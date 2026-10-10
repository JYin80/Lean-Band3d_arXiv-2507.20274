/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Topology.Instances.Matrix
import RBM3D.Green.EntryDom
import RBM3D.Green.FlucVanish
import RBM3D.Green.RowIndep

/-!
# Fluctuation averaging, averaging layer, and the large deviation inputs of `lem_GbEXP` for the
Gaussian flow, `d ≥ 3` (S1-18)

Ticket T2078.  Port of `RBM2D/Green/FlucAvg.lean` (546 lines) and `RBM2D/Green/LDE.lean` (818
lines) at commit `c9a24cf` (the portmap keeps 411 and 712 lines of them: the `#print axioms` lines
and the private `Checks` sections are not ported) to the fine lattice `Z_{WL}^d`, with the renaming
rules R1-R4 of `docs/tickets/ST1-COMMON.md` (item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L` and
`Idx L W` become `Zd d L` and `Idx d L W`, `W^2`, `W⁻²` and `(W L)^2` become `W^d`, `W^{-d}` and
`(W L)^d = sz.size n`, `BlockIndex L W` becomes the block-product index `Vtx d L W`, `Sblk2 L W`
(RBM2D's fixed profile) becomes the merged `RBM.Gauss.svar d L W (sz.lam n)`, `spectralZ` and
`spectralM` become `zt` and `mE`, and RBM2D's fine-lattice `svar L W` becomes
`svarF d L W (sz.lam n)`.  The paper (arXiv:2507.20274) does not state these lemmas:
`paper/tex/3_5_Loop_Hierarchy.tex:37` says that the estimates of `lem_GbEXP` (among them
`(GavLGEX)`, `3_5:33`) have been proven as Lemma 4.1 of `[YY_25]` for 1D random band matrices and
that their proofs are dimension-independent (resolvent identities and large deviation estimates).

## Contents

* FlucAvg (`RBM2D/Green/FlucAvg.lean`): measurability of `G_{ij}`, `G^{(κ)}_{ab}`, `E_k[X]`,
  `Z_k` (`measurable_*`), the deterministic envelopes `|G_{ij}| ≤ η⁻¹` (`norm_green_apply_le_etaT`,
  ..., `rowIntegrable_*`), the pointwise parameters `FlucBound` and `flucBound_env`
  (`B = 2(η⁻¹ + 1)`, `ε = 4η⁻¹`), the bounds on `flucAvg` (`norm_flucAvg_le`,
  `integrable_norm_flucAvg_pow`), `condExpDiag`, the counting facts (`card_blockAvg_support`,
  `card_Sblk_support`, `flucAvg_card_Idx_eq_size`, `flucAvg_card_Z2_le_size`), and `tendsto_W`,
  `eventually_le_W` (`W(n) → ∞` from `SizeTendsto` and `Bandwidth`, `∀ᶠ n, p ≤ W n`).
* LDE (`RBM2D/Green/LDE.lean`): the Ward identity and `G_{ii} ≠ 0` (`im_green_diag`,
  `green_diag_ne_zero`), the side conditions of the minor formula for every `ω`
  (`isUnit_det_Hflow_sub`, `green_Hflow_diag_ne_zero`), the column sum as the conjugate of a row sum
  (`minorRowConj_eq_greenMinor`, `ldeColLHS_eq`, `rowVarSum_minorRowConj_eq`), the relabelling
  `Idx ≃ Vtx` of the row sums, the bridge from the normalised row sum to `PerTimeDomAt` at a time
  sequence, **`stochDom_ldeRow`, `stochDom_ldeCol`** (the hypotheses `hLrow`, `hLcol` of
  `entry_bound_stochDom` of `Green/EntryDom.lean`), and the diagonal `|H_xx|² ≺ S_xx`:
  **`stochDom_normSq_Hflow_diag`** (the hypothesis `hLdiag` of `diag_bound_stochDom`).

* T2389 (BA-G2): the same inputs for a deterministic Hermitian shift `D` (`green (D + seqHflow …) z`, any `z` with
  `Im z ≠ 0`): `LDE_stochDom_ldeRow_shift`, `LDE_stochDom_ldeCol_shift` (the band `stochDom_ldeRow`,
  `stochDom_ldeCol` are their corollaries at `D = 0`), and the twins of the fluctuation layer
  (`LDE_greenMinorMatD`, …, `LDE_FlucBoundD`, `LDE_flucBound_envD`, `LDE_integrable_norm_flucAvg_powD`; `LDE_shift_zero`
  is the bridge to the band at `D = 0`).

* Instances (`RBM.Green.LDEInst`, at the end): compiled nonempty applications of the targets at the
  preflight sequence `sz0` (`d = 3`, `E ≡ 0`, `t ≡ 1/2`), among them `eventually_le_W_sz0`,
  `stochDom_normSq_Hflow_diag_sz0`, `stochDom_ldeRow_sz0`, `stochDom_ldeCol_sz0`, and an `example`
  that feeds the three large deviation inputs into `entry_bound_stochDom` and `diag_bound_stochDom`
  (only `hLquad`, the quadratic-form input of the tickets S1-12 - S1-19, stays a hypothesis).

## Differences from RBM2D (residual, after the renaming)

* **No `UniformWeight` is used in these two sources.**  RBM2D's `FlucAvg.lean` mentions
  `uniformWeight_blockAvg2`, `uniformWeight_svar` only in docstrings.  The row `j ↦ S_{ij}` is a
  `BoundedWeight` (DECISIONS §30, T2061: `boundedWeight_svarF`, `c = W^{-d}`, `#A = (2d + 1) W^d`),
  not a uniform weight (`not_uniformWeight_svarF`); `norm_flucAvg_le` takes an arbitrary weight `T`
  and `LDE_norm_flucAvg_le_of_boundedWeight` is its reading for a bounded weight (only `∑ t ≤ 1`
  is used, never `t = c`).
* `card_Sblk_support` (`T2078a`): the support is oriented `blk j - blk i ∈ flucVanish_sbSupport`
  as in the merged `boundedWeight_svarF` (RBM2D: `blk i - blk j ∈ sbSupport`; the set is the same,
  `sbSupport` is symmetric), and the constant `5` is `2 d + 1` (`flucVanish_card_svarSupport_eq`).
* `Sblk2_diag_eq` (`T2078b`): `svar d L W g i i = W^{-d} (1 + 2 d g²)⁻¹` (RBM2D: `1 / (5 W²)`
  with no coupling); `Sblk_diag_pos` holds for every real `g`.
* `Sblk_diag_pos`, `Sblk2_diag_eq`, `eventually_card_Idx_le` keep their RBM2D names; the first two
  are stated for `svar` (RBM2D `Sblk2`).
* The private `Checks` sections are replaced by the instances at the end of the file (`sz0` of
  `Defs/Sizes.lean`).
-/

set_option linter.style.longLine false

namespace RBM.Green

section FlucAvgPart

open MeasureTheory ProbabilityTheory Filter Matrix Finset RBM.Gauss

/-! ### Measurability of the matrix inverse (private port of RBM1D `Defs/MatrixMeasurable.lean`,
theorem `measurable_matrix_inv_apply`) -/

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A`. -/
private theorem flucAvg_measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ} (hM : Measurable M)
    (i j : ν) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

end MatrixMeasurable

/-! ### Measurability

The last obstruction to the hypotheses of the moment bound: the entries of the Green function,
the minor Green function and the conditional expectation `E_k` are measurable. -/

/-- `ω ↦ H_u(ω) - z` is measurable as a matrix-valued map. -/
theorem measurable_Hflow_sub {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) :
    Measurable fun ω : Sizes.SeqΩ sz =>
      Sizes.seqHflow sz n u ω
        - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
  refine Matrix.measurable_iff.2 fun a b => ?_
  have h : (fun ω : Sizes.SeqΩ sz => (Sizes.seqHflow sz n u ω
        - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) a b)
      = fun ω => Sizes.seqHflow sz n u ω a b
        - z * (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) a b := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (Sizes.measurable_seqHflow_entry sz n u a b).sub measurable_const

/-- **`ω ↦ G_{ij}(ω)` is measurable.** -/
theorem measurable_green_apply {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (i j : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω => green (Sizes.seqHflow sz n u ω) z i j :=
  flucAvg_measurable_matrix_inv_apply (measurable_Hflow_sub sz n u z) i j

/-- The same for the minor resolvent `G^{(κ)}`. -/
theorem measurable_greenMinorMat_apply {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (a b : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Measurable fun ω => greenMinorMat sz n u z κ ω a b := by
  refine flucAvg_measurable_matrix_inv_apply (M := fun ω : Sizes.SeqΩ sz =>
    (Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} ℂ)) ?_ a b
  refine Matrix.measurable_iff.2 fun p q => ?_
  have h : (fun ω : Sizes.SeqΩ sz =>
      ((Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
        - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}
          {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} ℂ)) p q)
      = fun ω => Sizes.seqHflow sz n u ω p.1 q.1
          - z * (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}
            {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} ℂ) p q := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (Sizes.measurable_seqHflow_entry sz n u p.1 q.1).sub measurable_const

/-- **`ω ↦ E_k[X](ω)` is measurable** for measurable `X`: `E_k` is an integral over the second
factor of `Ω × Ω`, and `rowSplit` is jointly measurable (`measurable_rowSplit`), so
`MeasureTheory.StronglyMeasurable.integral_prod_right'` applies. -/
theorem measurable_condRow {d : ℕ} (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    {X : Sizes.SeqΩ sz → ℂ} (hX : Measurable X) :
    Measurable (condRow sz n k X) := by
  have hjoint : StronglyMeasurable fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz =>
      X (rowSplit sz n k p.1 p.2) :=
    (hX.comp (measurable_rowSplit sz n k)).stronglyMeasurable
  exact hjoint.integral_prod_right'.measurable

theorem measurable_greenDiagCentered {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) :
    Measurable (greenDiagCentered sz n u z m k) :=
  (measurable_green_apply sz n u z k k).sub measurable_const

theorem measurable_greenMinorDiagCentered {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Measurable (greenMinorDiagCentered sz n u z m κ k) :=
  (measurable_greenMinorMat_apply sz n u z κ k k).sub measurable_const

/-- Measurability of `Z_k = (1 - E_k)(G_{kk} - m)`. -/
theorem measurable_flucDiag {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) :
    Measurable (flucDiag sz n u z m k) :=
  (measurable_greenDiagCentered sz n u z m k).sub
    (measurable_condRow sz n k (measurable_greenDiagCentered sz n u z m k))

/-! ### The deterministic envelope, entrywise

`Im z_t = η_t = (1 - t) Im m(E) > 0` for `|E| < 2`, `t < 1`, so `‖G_t‖_op ≤ η_t⁻¹`
(`RBM.Gauss.norm_Gsig_le_inv_eta`) for *every* `ω`, and the same for every minor `G^{(κ)}_t`, a
resolvent of the Hermitian matrix `H^{(κ)}`.  The bound is written with `η_t = (zt E t).im`
(RBM2D: `(spectralZ E t).im`). -/

section Envelope

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E t : ℝ}

/-- For `|E| < 2` and `t < 1`, `η_t = Im z_t > 0`. -/
private theorem flucAvg_zt_im_pos (hE : |E| < 2) (ht : t < 1) :
    0 < (zt E t).im := by
  rw [zt_im]
  exact mul_pos (by linarith) (mE_im_pos hE)

/-- The merged `Gres H z +` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`. -/
private theorem flucAvg_Gres_true_eq_green {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- The Green function of a Hermitian matrix at `z_t` has operator norm at most `η_t⁻¹`
(RBM2D `norm_green_le`, `Gauss/Envelope.lean:116`, read through `norm_Gsig_le_inv_eta`). -/
private theorem flucAvg_norm_green_zt_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (hE : |E| < 2) (ht : t < 1) :
    ‖green H (zt E t)‖ ≤ ((zt E t).im)⁻¹ := by
  have hη := flucAvg_zt_im_pos hE ht
  have h := norm_Gsig_le_inv_eta hH hη (le_of_eq (abs_of_pos hη).symm) true
  rwa [flucAvg_Gres_true_eq_green] at h

/-- `|G_{ij}| ≤ η_t⁻¹` for every `ω`. -/
theorem norm_green_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ‖green (Sizes.seqHflow sz n u ω) (zt E t) i j‖ ≤ ((zt E t).im)⁻¹ :=
  le_trans (norm_matrix_entry_le_opNorm _ i j)
    (flucAvg_norm_green_zt_le (Sizes.seqHflow_isHermitian sz n u ω) hE ht)

/-- `G^{(κ)}` is the resolvent of the minor `H^{(κ)}`, which is Hermitian. -/
theorem greenMinorMat_eq_green_submatrix {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    greenMinorMat sz n u z κ ω
      = green ((Sizes.seqHflow sz n u ω).submatrix
          (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
          (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))) z :=
  rfl

/-- `|G^{(κ)}_{ab}| ≤ η_t⁻¹` for every `ω`: the minor of a Hermitian matrix is Hermitian, so the
same envelope applies. -/
theorem norm_greenMinorMat_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {κ : Idx d (sz.L n) (sz.W n)} (a b : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ sz) :
    ‖greenMinorMat sz n u (zt E t) κ ω a b‖ ≤ ((zt E t).im)⁻¹ := by
  rw [greenMinorMat_eq_green_submatrix]
  exact le_trans (norm_matrix_entry_le_opNorm _ a b)
    (flucAvg_norm_green_zt_le ((Sizes.seqHflow_isHermitian sz n u ω).submatrix _) hE ht)

/-- `|G_{kk} - m| ≤ η_t⁻¹ + 1` for every `ω` (`‖m^{(E)}‖ = 1`). -/
theorem norm_greenDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ‖greenDiagCentered sz n u (zt E t) (mE E) k ω‖
      ≤ ((zt E t).im)⁻¹ + 1 := by
  refine le_trans (norm_sub_le _ _) (add_le_add (norm_green_apply_le_etaT hE ht u k k ω) ?_)
  exact le_of_eq (norm_mE hE.le)

theorem norm_greenMinorDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {κ : Idx d (sz.L n) (sz.W n)} (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ sz) :
    ‖greenMinorDiagCentered sz n u (zt E t) (mE E) κ k ω‖
      ≤ ((zt E t).im)⁻¹ + 1 := by
  refine le_trans (norm_sub_le _ _)
    (add_le_add (norm_greenMinorMat_apply_le_etaT hE ht u k k ω) ?_)
  exact le_of_eq (norm_mE hE.le)

/-- `RowIntegrable` for `G_{kk} - m`: the hypothesis `hrow` of the moment bound, now a theorem. -/
theorem rowIntegrable_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) :
    RowIntegrable sz n k (greenDiagCentered sz n u (zt E t) (mE E) k) :=
  rowIntegrable_of_measurable_of_bound
    (measurable_greenDiagCentered sz n u (zt E t) (mE E) k)
    (norm_greenDiagCentered_le_env hE ht u k)

theorem rowIntegrable_greenMinorDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {κ : Idx d (sz.L n) (sz.W n)} (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ})
    (j : Idx d (sz.L n) (sz.W n)) :
    RowIntegrable sz n j (greenMinorDiagCentered sz n u (zt E t) (mE E) κ k) :=
  rowIntegrable_of_measurable_of_bound
    (measurable_greenMinorDiagCentered sz n u (zt E t) (mE E) κ k)
    (norm_greenMinorDiagCentered_le_env hE ht u k)

end Envelope

/-! ### The pointwise parameters `B` and `ε`

The moment bound is stated for *pointwise-uniform* parameters `B` (a bound on every factor `Z_k`
and every replaced factor `Z^{(κ)}_k`) and `ε` (a bound on the replacement error).
`FlucBound` packages them; the unconditional instance is the deterministic envelope one,
`flucBound_env`. -/

/-- The three uniform bounds the moment bound consumes, packaged. -/
structure FlucBound {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (B ε : ℝ) : Prop where
  /-- `B` is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- `ε` is nonnegative. -/
  eps_nonneg : 0 ≤ ε
  /-- Every factor `Z_k` is bounded by `B`, for every `ω`. -/
  flucDiag_le : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
    ‖flucDiag sz n u z m k ω‖ ≤ B
  /-- Every replaced factor `Z^{(κ)}_k` is bounded by `B`, for every `ω`. -/
  flucDiagMinor_le : ∀ (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ sz), ‖flucDiagMinor sz n u z m κ k ω‖ ≤ B
  /-- The replacement `Z_k ↦ Z^{(κ)}_k` costs at most `ε`, for every `ω`. -/
  repl_le : ∀ (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ sz), ‖flucDiag sz n u z m k.1 ω - flucDiagMinor sz n u z m κ k ω‖ ≤ ε

section EnvParams

open scoped Matrix.Norms.L2Operator

variable {E t : ℝ}

/-- **The pointwise parameters exist, unconditionally.**  The deterministic envelope
`‖G_t‖ ≤ η_t⁻¹` holds for *every* `ω`, with no exceptional set, and it survives the `(1 - E_k)`
(factor `2`, `norm_sub_condRow_le`) and the minor replacement (`G` and `G^{(κ)}` are resolvents
of two Hermitian matrices, so their difference is at most `2 η_t⁻¹`).

The parameters are `B = 2(η_t⁻¹ + 1)` and `ε = 4 η_t⁻¹`: finite and explicit, of size `η_t⁻¹`. -/
theorem flucBound_env (hE : |E| < 2) (ht : t < 1) {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) :
    FlucBound sz n u (zt E t) (mE E)
      (2 * (((zt E t).im)⁻¹ + 1)) (4 * ((zt E t).im)⁻¹) := by
  have hη : 0 < (zt E t).im := flucAvg_zt_im_pos hE ht
  refine ⟨by positivity, by positivity, fun k ω => ?_, fun κ k ω => ?_, fun κ k ω => ?_⟩
  · exact norm_flucDiag_le (norm_greenDiagCentered_le_env hE ht u k) ω
  · exact norm_flucDiagMinor_le (norm_greenMinorDiagCentered_le_env hE ht u k) ω
  · have he : ∀ ω' : Sizes.SeqΩ sz,
        ‖green (Sizes.seqHflow sz n u ω') (zt E t) k.1 k.1
          - greenMinorMat sz n u (zt E t) κ ω' k k‖ ≤ 2 * ((zt E t).im)⁻¹ := by
      intro ω'
      refine le_trans (norm_sub_le _ _) ?_
      have h1 := norm_green_apply_le_etaT hE ht u k.1 k.1 ω'
      have h2 := norm_greenMinorMat_apply_le_etaT hE ht u k k ω'
      linarith
    have := norm_flucDiag_sub_flucDiagMinor_le (u := u) (z := zt E t)
      (m := mE E) (κ := κ) (k := k) (rowIntegrable_greenDiagCentered hE ht u k.1)
      (rowIntegrable_greenMinorDiagCentered hE ht u k k.1) he ω
    linarith

end EnvParams

/-! ### The moment bound in the assembled form -/

section Moment

/-- Measurability of the weighted fluctuation average `∑_k t_k Z_k`. -/
theorem measurable_flucAvg {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (T : Idx d (sz.L n) (sz.W n) → ℝ) :
    Measurable (flucAvg sz n u z m T) :=
  Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_flucDiag sz n u z m k)

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u : ℝ} {z m : ℂ} {T : Idx d (sz.L n) (sz.W n) → ℝ}

/-- `‖∑_k t_k Z_k‖ ≤ (∑_k |t_k|) B`. -/
theorem norm_flucAvg_le {B : ℝ}
    (hB : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), ‖flucDiag sz n u z m k ω‖ ≤ B)
    (ω : Sizes.SeqΩ sz) : ‖flucAvg sz n u z m T ω‖ ≤ (∑ k, |T k|) * B := by
  calc ‖flucAvg sz n u z m T ω‖
      ≤ ∑ k, ‖(T k : ℂ) * flucDiag sz n u z m k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, |T k| * B := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB k ω) (abs_nonneg _)
    _ = (∑ k, |T k|) * B := by rw [Finset.sum_mul]

/-- **A bounded weight** (`0 ≤ t ≤ c` on `A`, `0` off `A`, `∑ t ≤ 1`; DECISIONS §30, T2061) gives
`‖∑_k t_k Z_k‖ ≤ B`: only the mass `∑ t ≤ 1` enters, never `t = c`.  The rows `j ↦ S_{ij}`
(`boundedWeight_svarF`) are bounded weights; the block averages are uniform weights, hence bounded
(`UniformWeight.toBoundedWeight`). -/
theorem LDE_norm_flucAvg_le_of_boundedWeight {B c : ℝ} {A : Finset (Idx d (sz.L n) (sz.W n))}
    (hT : BoundedWeight T c A)
    (hB : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), ‖flucDiag sz n u z m k ω‖ ≤ B)
    (ω : Sizes.SeqΩ sz) : ‖flucAvg sz n u z m T ω‖ ≤ B := by
  have h0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ω)
  have hsum : ∑ k, |T k| ≤ 1 := by
    have : ∑ k, |T k| = ∑ k, T k :=
      Finset.sum_congr rfl fun k _ => abs_of_nonneg (hT.nonneg k)
    rw [this]
    exact hT.sum_le
  calc ‖flucAvg sz n u z m T ω‖ ≤ (∑ k, |T k|) * B := norm_flucAvg_le hB ω
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hsum h0
    _ = B := one_mul B

/-- The `2p`-th power of `|∑_k t_k Z_k|` is integrable under a uniform bound on the `Z_k`. -/
theorem integrable_norm_flucAvg_pow {B : ℝ}
    (hB : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), ‖flucDiag sz n u z m k ω‖ ≤ B)
    (p : ℕ) :
    Integrable (fun ω => |‖flucAvg sz n u z m T ω‖| ^ (2 * p)) (Sizes.seqP sz) := by
  have hrw : (fun ω => |‖flucAvg sz n u z m T ω‖| ^ (2 * p))
      = fun ω => ‖flucAvg sz n u z m T ω‖ ^ (2 * p) := by
    funext ω; rw [abs_norm]
  rw [hrw]
  refine Integrable.mono' (integrable_const (((∑ k, |T k|) * B) ^ (2 * p)))
    (((measurable_flucAvg sz n u z m T).norm.pow_const (2 * p)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : (0 : ℝ) ≤ ∑ k, |T k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_flucAvg_le hB ω) _

end Moment

/-! ### The conditional diagonal -/

/-- `E_k(G_{kk} - m)`, the fine-index conditional diagonal (the quantity `x` of the entry-block
estimate). -/
noncomputable def condExpDiag {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) : Sizes.SeqΩ sz → ℂ :=
  condRow sz n k (greenDiagCentered sz n u z m k)

/-! ### The counting facts at `d ≥ 3`

`t_k = W^{-d} 1(k ∈ 𝓘_a)` (`uniformWeight_blockAvg2`) is a uniform weight and `t_k = S_{ik}` is a
bounded weight (`boundedWeight_svarF`, DECISIONS §30); here the index sets are counted at slice `n`
(`W^d` and `(2d + 1) W^d` sites), the index set is counted (`#Idx = size n = (W L)^d`), and
`W → ∞` is derived from `SizeTendsto` and `Bandwidth`. -/

section Families

/-- The block average of (4.12) is a uniform weight on a set of `W^d` elements (RBM2D
`card_blockAvg_support`: `W²`); the merged `flucVanish_card_blockSupport` at `(sz.L n, sz.W n)`. -/
theorem card_blockAvg_support {d : ℕ} (sz : Sizes d) (n : ℕ) (a : Zd d (sz.L n)) :
    ((univ : Finset (Idx d (sz.L n) (sz.W n))).filter fun k =>
      (split d (sz.L n) (sz.W n) k).1 = a).card = sz.W n ^ d :=
  flucVanish_card_blockSupport d (sz.L n) (sz.W n) a

/-- The variance-profile row `t_j = S_{ij}` of (4.12) is a bounded weight on a set of
`(2d + 1) W^d` elements (RBM2D `card_Sblk_support`: `5 W²`, and `blk i - blk j ∈ sbSupport`; here
`blk j - blk i ∈ flucVanish_sbSupport`, paper-delta candidate `T2078a`); the merged
`flucVanish_card_svarSupport_eq` at `(sz.L n, sz.W n)` with `3 ≤ sz.L n`. -/
theorem card_Sblk_support {d : ℕ} (sz : Sizes d) (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) :
    ((univ : Finset (Idx d (sz.L n) (sz.W n))).filter fun j =>
      (split d (sz.L n) (sz.W n) j).1 - (split d (sz.L n) (sz.W n) i).1
        ∈ flucVanish_sbSupport d (sz.L n)).card
      = (2 * d + 1) * sz.W n ^ d :=
  flucVanish_card_svarSupport_eq d (sz.L n) (sz.W n) (sz.three_le_L n) i

/-- **`#Idx = size`**, exactly: `#(Zd d (W L)) = (W L)^d = N` (RBM2D `flucAvg_card_Idx_eq_size`:
`(W L)²`); the merged `Sizes.card_Idx`. -/
theorem flucAvg_card_Idx_eq_size {d : ℕ} (sz : Sizes d) (n : ℕ) :
    Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n :=
  Sizes.card_Idx sz n

/-- `#Zd d L ≤ size` (RBM2D `flucAvg_card_Z2_le_size`: `L² ≤ (W L)²`): `L^d ≤ (W L)^d` since
`W ≥ 1`. -/
theorem flucAvg_card_Z2_le_size {d : ℕ} (sz : Sizes d) (n : ℕ) :
    Fintype.card (Zd d (sz.L n)) ≤ sz.size n := by
  have hLW : sz.L n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_left _ (sz.W_pos n)
  have h : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by
    simp [Zd, ZMod.card]
  rw [h, Sizes.size]
  exact Nat.pow_le_pow_left hLW d

/-- **`W(n) → ∞`**, from `N → ∞` (`SizeTendsto`) and `W ≥ N^𝔠` (`Bandwidth`, `Main_DEL_COND`,
`1_2:359`) with `𝔠 > 0` (RBM2D `tendsto_W`). -/
theorem tendsto_W {d : ℕ} (sz : Sizes d) {c : ℝ} (hc : 0 < c) (hsz : sz.SizeTendsto)
    (hbw : sz.Bandwidth c) :
    Tendsto (fun n => (sz.W n : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop hbw ((tendsto_rpow_atTop hc).comp hsz)

/-- Every `p` is eventually below `W(n)`. -/
theorem eventually_le_W {d : ℕ} (sz : Sizes d) {c : ℝ} (hc : 0 < c) (hsz : sz.SizeTendsto)
    (hbw : sz.Bandwidth c) (p : ℕ) : ∀ᶠ n : ℕ in atTop, p ≤ sz.W n := by
  filter_upwards [(tendsto_W sz hc hsz hbw).eventually_ge_atTop (p : ℝ)] with n hn
  exact_mod_cast hn

end Families

/-! ### The fluctuation layer for a deterministic Hermitian shift (T2389, BA-G2)

The block Anderson resolvent is `G = (D + X - z)⁻¹` with `D = g₀ Ψ` deterministic and Hermitian and `X = seqHflow`
the Gaussian part.  The declarations of `FlucVanish` (`greenMinorMat`, `greenDiagCentered`, `flucDiag`,
`flucDiagMinor`, `flucAvg`; group B, not writable by this ticket) read `green (seqHflow …) z`; the twins below
read `green (D + seqHflow …) z`, and `D = 0` is the band (`LDE_shift_zero`).  The proofs use only `D + X` Hermitian,
`Im z ≠ 0` and, for the envelopes of the centred diagonals, `‖m‖ ≤ 1`: `D` is a constant of every conditional
expectation `E_k`, which only resamples row `k` of `X`.  The band declarations stay as they are. -/

section FlucShift

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- The minor resolvent `G^{(κ)} = ((D + X)^{(κ)} - z)⁻¹` as a total function of `ω`. -/
noncomputable def LDE_greenMinorMatD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} ℂ :=
  ((D + Sizes.seqHflow sz n u ω).submatrix
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} ℂ))⁻¹

/-- `G_{kk} - m` for the resolvent of `D + X`. -/
noncomputable def LDE_greenDiagCenteredD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) : Sizes.SeqΩ sz → ℂ :=
  fun ω => green (D + Sizes.seqHflow sz n u ω) z k k - m

/-- `G^{(κ)}_{kk} - m` for the minor of `D + X`. -/
noncomputable def LDE_greenMinorDiagCenteredD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z m : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Sizes.SeqΩ sz → ℂ :=
  fun ω => LDE_greenMinorMatD sz n D u z κ ω k k - m

/-- `Z_k = (1 - E_k)(G_{kk} - m)` for `D + X`. -/
noncomputable def LDE_flucDiagD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) : Sizes.SeqΩ sz → ℂ :=
  fun ω => LDE_greenDiagCenteredD sz n D u z m k ω - condRow sz n k (LDE_greenDiagCenteredD sz n D u z m k) ω

/-- `Z^{(κ)}_k = (1 - E_k)(G^{(κ)}_{kk} - m)` for `D + X`. -/
noncomputable def LDE_flucDiagMinorD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z m : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Sizes.SeqΩ sz → ℂ :=
  fun ω => LDE_greenMinorDiagCenteredD sz n D u z m κ k ω
    - condRow sz n k.1 (LDE_greenMinorDiagCenteredD sz n D u z m κ k) ω

/-- `∑_k t_k Z_k` for `D + X`. -/
noncomputable def LDE_flucAvgD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z m : ℂ)
    (T : Idx d (sz.L n) (sz.W n) → ℝ) : Sizes.SeqΩ sz → ℂ :=
  fun ω => ∑ k, (T k : ℂ) * LDE_flucDiagD sz n D u z m k ω

/-- `E_k(G_{kk} - m)` for `D + X`. -/
noncomputable def LDE_condExpDiagD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) : Sizes.SeqΩ sz → ℂ :=
  condRow sz n k (LDE_greenDiagCenteredD sz n D u z m k)

/-- At `D = 0` the twins are the band declarations of `FlucVanish` and `condExpDiag`. -/
theorem LDE_shift_zero (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (k : Idx d (sz.L n) (sz.W n))
    (κ : Idx d (sz.L n) (sz.W n)) (T : Idx d (sz.L n) (sz.W n) → ℝ)
    (k' : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    LDE_greenMinorMatD sz n 0 u z κ = greenMinorMat sz n u z κ ∧
    LDE_greenDiagCenteredD sz n 0 u z m k = greenDiagCentered sz n u z m k ∧
    LDE_greenMinorDiagCenteredD sz n 0 u z m κ k' = greenMinorDiagCentered sz n u z m κ k' ∧
    LDE_flucDiagD sz n 0 u z m k = flucDiag sz n u z m k ∧
    LDE_flucDiagMinorD sz n 0 u z m κ k' = flucDiagMinor sz n u z m κ k' ∧
    LDE_flucAvgD sz n 0 u z m T = flucAvg sz n u z m T ∧
    LDE_condExpDiagD sz n 0 u z m k = condExpDiag sz n u z m k := by
  have h1 : LDE_greenMinorMatD sz n 0 u z κ = greenMinorMat sz n u z κ := by
    funext ω; simp [LDE_greenMinorMatD, greenMinorMat]
  have h2 : ∀ k, LDE_greenDiagCenteredD sz n 0 u z m k = greenDiagCentered sz n u z m k := by
    intro k; funext ω; simp [LDE_greenDiagCenteredD, greenDiagCentered]
  have h3 : LDE_greenMinorDiagCenteredD sz n 0 u z m κ k' = greenMinorDiagCentered sz n u z m κ k' := by
    funext ω; simp [LDE_greenMinorDiagCenteredD, greenMinorDiagCentered, h1]
  have h4 : ∀ k, LDE_flucDiagD sz n 0 u z m k = flucDiag sz n u z m k := by
    intro k; funext ω; simp [LDE_flucDiagD, flucDiag, h2]
  refine ⟨h1, h2 k, h3, h4 k, ?_, ?_, ?_⟩
  · funext ω; simp [LDE_flucDiagMinorD, flucDiagMinor, h3]
  · funext ω; simp [LDE_flucAvgD, flucAvg, h4]
  · simp [LDE_condExpDiagD, condExpDiag, h2]

variable (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- Every entry of `D + X - z` is measurable in `ω`. -/
theorem LDE_measurable_HflowD_sub (u : ℝ) (z : ℂ) :
    Measurable fun ω : Sizes.SeqΩ sz =>
      D + Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
  refine Matrix.measurable_iff.2 fun a b => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  exact (measurable_const.add (Sizes.measurable_seqHflow_entry sz n u a b)).sub measurable_const

/-- **`ω ↦ G_{ij}(ω)` is measurable** for the resolvent of `D + X`. -/
theorem LDE_measurable_green_applyD (u : ℝ) (z : ℂ) (i j : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω : Sizes.SeqΩ sz => green (D + Sizes.seqHflow sz n u ω) z i j :=
  flucAvg_measurable_matrix_inv_apply (LDE_measurable_HflowD_sub D u z) i j

/-- The same for the minor resolvent `G^{(κ)}` of `D + X`. -/
theorem LDE_measurable_greenMinorMat_applyD (u : ℝ) (z : ℂ) (κ : Idx d (sz.L n) (sz.W n))
    (a b : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Measurable fun ω : Sizes.SeqΩ sz => LDE_greenMinorMatD sz n D u z κ ω a b := by
  refine flucAvg_measurable_matrix_inv_apply (M := fun ω : Sizes.SeqΩ sz =>
    (D + Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n))
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} ℂ)) ?_ a b
  refine Matrix.measurable_iff.2 fun p q => ?_
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply]
  exact (measurable_const.add (Sizes.measurable_seqHflow_entry sz n u p.1 q.1)).sub measurable_const

theorem LDE_measurable_greenDiagCenteredD (u : ℝ) (z m : ℂ) (k : Idx d (sz.L n) (sz.W n)) :
    Measurable (LDE_greenDiagCenteredD sz n D u z m k) :=
  (LDE_measurable_green_applyD D u z k k).sub measurable_const

theorem LDE_measurable_greenMinorDiagCenteredD (u : ℝ) (z m : ℂ) (κ : Idx d (sz.L n) (sz.W n))
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Measurable (LDE_greenMinorDiagCenteredD sz n D u z m κ k) :=
  (LDE_measurable_greenMinorMat_applyD D u z κ k k).sub measurable_const

/-- Measurability of `Z_k = (1 - E_k)(G_{kk} - m)` for `D + X`. -/
theorem LDE_measurable_flucDiagD (u : ℝ) (z m : ℂ) (k : Idx d (sz.L n) (sz.W n)) :
    Measurable (LDE_flucDiagD sz n D u z m k) :=
  (LDE_measurable_greenDiagCenteredD D u z m k).sub
    (measurable_condRow sz n k (LDE_measurable_greenDiagCenteredD D u z m k))

/-- Measurability of the weighted fluctuation average for `D + X`. -/
theorem LDE_measurable_flucAvgD (u : ℝ) (z m : ℂ) (T : Idx d (sz.L n) (sz.W n) → ℝ) :
    Measurable (LDE_flucAvgD sz n D u z m T) :=
  Finset.measurable_sum _ fun k _ => measurable_const.mul (LDE_measurable_flucDiagD D u z m k)

section EnvelopeD

open scoped Matrix.Norms.L2Operator

/-- **The envelope for `D + X`:** `|G_{ij}| ≤ |Im z|⁻¹` for every `ω`, `D + X` being Hermitian (no spectral
bound on `D` or on `X`; `z_t` of the band has `|Im z_t| = η_t`). -/
theorem LDE_norm_green_apply_leD (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u : ℝ)
    (i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ‖green (D + Sizes.seqHflow sz n u ω) z i j‖ ≤ |z.im|⁻¹ := by
  have h := norm_Gsig_le_inv_eta (hD.add (Sizes.seqHflow_isHermitian sz n u ω)) (abs_pos.2 hz) le_rfl true
  rw [flucAvg_Gres_true_eq_green] at h
  exact (norm_matrix_entry_le_opNorm _ i j).trans h

/-- `|G^{(κ)}_{ab}| ≤ |Im z|⁻¹` for every `ω`: the minor of a Hermitian matrix is Hermitian. -/
theorem LDE_norm_greenMinorMat_apply_leD (hD : D.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u : ℝ)
    {κ : Idx d (sz.L n) (sz.W n)} (a b : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) (ω : Sizes.SeqΩ sz) :
    ‖LDE_greenMinorMatD sz n D u z κ ω a b‖ ≤ |z.im|⁻¹ := by
  have h := norm_Gsig_le_inv_eta
    ((hD.add (Sizes.seqHflow_isHermitian sz n u ω)).submatrix
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ} → Idx d (sz.L n) (sz.W n)))
    (abs_pos.2 hz) le_rfl true
  rw [flucAvg_Gres_true_eq_green] at h
  exact (norm_matrix_entry_le_opNorm _ a b).trans h

/-- `|G_{kk} - m| ≤ |Im z|⁻¹ + 1` for every `ω` (`‖m‖ ≤ 1`). -/
theorem LDE_norm_greenDiagCentered_le_envD (hD : D.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : ‖m‖ ≤ 1)
    (u : ℝ) (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ‖LDE_greenDiagCenteredD sz n D u z m k ω‖ ≤ |z.im|⁻¹ + 1 :=
  (norm_sub_le _ _).trans (add_le_add (LDE_norm_green_apply_leD D hD hz u k k ω) hm)

theorem LDE_norm_greenMinorDiagCentered_le_envD (hD : D.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : ‖m‖ ≤ 1)
    (u : ℝ) {κ : Idx d (sz.L n) (sz.W n)} (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) (ω : Sizes.SeqΩ sz) :
    ‖LDE_greenMinorDiagCenteredD sz n D u z m κ k ω‖ ≤ |z.im|⁻¹ + 1 :=
  (norm_sub_le _ _).trans (add_le_add (LDE_norm_greenMinorMat_apply_leD D hD hz u k k ω) hm)

end EnvelopeD

/-- The three uniform bounds the moment bound consumes, packaged, for `D + X` (`FlucBound` of the band). -/
structure LDE_FlucBoundD (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z m : ℂ) (B ε : ℝ) : Prop where
  /-- `B` is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- `ε` is nonnegative. -/
  eps_nonneg : 0 ≤ ε
  /-- Every factor `Z_k` is bounded by `B`, for every `ω`. -/
  flucDiag_le : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
    ‖LDE_flucDiagD sz n D u z m k ω‖ ≤ B
  /-- Every replaced factor `Z^{(κ)}_k` is bounded by `B`, for every `ω`. -/
  flucDiagMinor_le : ∀ (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ sz), ‖LDE_flucDiagMinorD sz n D u z m κ k ω‖ ≤ B
  /-- The replacement `Z_k ↦ Z^{(κ)}_k` costs at most `ε`, for every `ω`. -/
  repl_le : ∀ (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ})
    (ω : Sizes.SeqΩ sz), ‖LDE_flucDiagD sz n D u z m k.1 ω - LDE_flucDiagMinorD sz n D u z m κ k ω‖ ≤ ε

/-- **The replacement error of a factor** (`norm_flucDiag_sub_flucDiagMinor_le` of `FlucVanish` for `D + X`): from a
uniform bound `e` on `G_{kk} - G^{(κ)}_{kk}` and row integrability, `‖Z_k - Z^{(κ)}_k‖ ≤ 2e`. -/
theorem LDE_norm_flucDiag_sub_flucDiagMinor_leD {u : ℝ} {z m : ℂ} {κ : Idx d (sz.L n) (sz.W n)}
    {k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}} {e : ℝ}
    (hrow : RowIntegrable sz n k.1 (LDE_greenDiagCenteredD sz n D u z m k.1))
    (hrow' : RowIntegrable sz n k.1 (LDE_greenMinorDiagCenteredD sz n D u z m κ k))
    (he : ∀ ω, ‖green (D + Sizes.seqHflow sz n u ω) z k.1 k.1 - LDE_greenMinorMatD sz n D u z κ ω k k‖ ≤ e)
    (ω : Sizes.SeqΩ sz) :
    ‖LDE_flucDiagD sz n D u z m k.1 ω - LDE_flucDiagMinorD sz n D u z m κ k ω‖ ≤ 2 * e := by
  have hD' : ∀ ω' : Sizes.SeqΩ sz, LDE_greenDiagCenteredD sz n D u z m k.1 ω'
      - LDE_greenMinorDiagCenteredD sz n D u z m κ k ω'
      = green (D + Sizes.seqHflow sz n u ω') z k.1 k.1 - LDE_greenMinorMatD sz n D u z κ ω' k k := by
    intro ω'
    simp only [LDE_greenDiagCenteredD, LDE_greenMinorDiagCenteredD]
    ring
  have hcondpt : condRow sz n k.1 (LDE_greenDiagCenteredD sz n D u z m k.1) ω
      - condRow sz n k.1 (LDE_greenMinorDiagCenteredD sz n D u z m κ k) ω
      = condRow sz n k.1 (fun ω' => green (D + Sizes.seqHflow sz n u ω') z k.1 k.1
          - LDE_greenMinorMatD sz n D u z κ ω' k k) ω := by
    have := congrFun (condRow_sub k.1 hrow hrow') ω
    rw [← this]
    simp only [condRow_apply, hD']
  have hbound : ‖condRow sz n k.1 (fun ω' => green (D + Sizes.seqHflow sz n u ω') z k.1 k.1
      - LDE_greenMinorMatD sz n D u z κ ω' k k) ω‖ ≤ e := by
    rw [condRow_apply]
    simpa using norm_integral_le_of_norm_le_const (μ := Sizes.seqP sz)
      (f := fun ω' => green (D + Sizes.seqHflow sz n u (rowSplit sz n k.1 ω ω')) z k.1 k.1
        - LDE_greenMinorMatD sz n D u z κ (rowSplit sz n k.1 ω ω') k k)
      (C := e) (Filter.Eventually.of_forall fun ω' => he _)
  have hsplit : LDE_flucDiagD sz n D u z m k.1 ω - LDE_flucDiagMinorD sz n D u z m κ k ω
      = (green (D + Sizes.seqHflow sz n u ω) z k.1 k.1 - LDE_greenMinorMatD sz n D u z κ ω k k)
        - condRow sz n k.1 (fun ω' => green (D + Sizes.seqHflow sz n u ω') z k.1 k.1
            - LDE_greenMinorMatD sz n D u z κ ω' k k) ω := by
    rw [← hcondpt, ← hD' ω]
    simp only [LDE_flucDiagD, LDE_flucDiagMinorD]
    ring
  rw [hsplit]
  calc _ ≤ ‖green (D + Sizes.seqHflow sz n u ω) z k.1 k.1 - LDE_greenMinorMatD sz n D u z κ ω k k‖
        + ‖condRow sz n k.1 (fun ω' => green (D + Sizes.seqHflow sz n u ω') z k.1 k.1
            - LDE_greenMinorMatD sz n D u z κ ω' k k) ω‖ := norm_sub_le _ _
    _ ≤ e + e := add_le_add (he ω) hbound
    _ = 2 * e := by ring

/-- **The pointwise parameters exist, unconditionally, for `D + X`:** `B = 2(|Im z|⁻¹ + 1)`, `ε = 4 |Im z|⁻¹`
(`flucBound_env` of the band, with `|Im z_t| = η_t`; `‖m‖ ≤ 1`). -/
theorem LDE_flucBound_envD (hD : D.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hm : ‖m‖ ≤ 1) (u : ℝ) :
    LDE_FlucBoundD sz n D u z m (2 * (|z.im|⁻¹ + 1)) (4 * |z.im|⁻¹) := by
  have hη : 0 < |z.im|⁻¹ := inv_pos.2 (abs_pos.2 hz)
  refine ⟨by positivity, by positivity, fun k ω => ?_, fun κ k ω => ?_, fun κ k ω => ?_⟩
  · exact norm_sub_condRow_le (LDE_norm_greenDiagCentered_le_envD D hD hz hm u k) ω
  · exact norm_sub_condRow_le (LDE_norm_greenMinorDiagCentered_le_envD D hD hz hm u k) ω
  · have he : ∀ ω' : Sizes.SeqΩ sz,
        ‖green (D + Sizes.seqHflow sz n u ω') z k.1 k.1 - LDE_greenMinorMatD sz n D u z κ ω' k k‖
          ≤ 2 * |z.im|⁻¹ := by
      intro ω'
      have h1 := LDE_norm_green_apply_leD D hD hz u k.1 k.1 ω'
      have h2 := LDE_norm_greenMinorMat_apply_leD D hD hz u k k ω'
      linarith [norm_sub_le (green (D + Sizes.seqHflow sz n u ω') z k.1 k.1)
        (LDE_greenMinorMatD sz n D u z κ ω' k k)]
    have := LDE_norm_flucDiag_sub_flucDiagMinor_leD D (u := u) (z := z) (m := m) (κ := κ) (k := k)
      (rowIntegrable_of_measurable_of_bound (LDE_measurable_greenDiagCenteredD D u z m k.1)
        (LDE_norm_greenDiagCentered_le_envD D hD hz hm u k.1))
      (rowIntegrable_of_measurable_of_bound (LDE_measurable_greenMinorDiagCenteredD D u z m κ k)
        (LDE_norm_greenMinorDiagCentered_le_envD D hD hz hm u k)) he ω
    linarith

/-- `‖∑_k t_k Z_k‖ ≤ (∑_k |t_k|) B` for `D + X`. -/
theorem LDE_norm_flucAvg_leD {u : ℝ} {z m : ℂ} {T : Idx d (sz.L n) (sz.W n) → ℝ} {B : ℝ}
    (hB : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), ‖LDE_flucDiagD sz n D u z m k ω‖ ≤ B)
    (ω : Sizes.SeqΩ sz) : ‖LDE_flucAvgD sz n D u z m T ω‖ ≤ (∑ k, |T k|) * B := by
  calc ‖LDE_flucAvgD sz n D u z m T ω‖
      ≤ ∑ k, ‖(T k : ℂ) * LDE_flucDiagD sz n D u z m k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, |T k| * B := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB k ω) (abs_nonneg _)
    _ = (∑ k, |T k|) * B := by rw [Finset.sum_mul]

/-- A bounded weight gives `‖∑_k t_k Z_k‖ ≤ B` for `D + X` (`LDE_norm_flucAvg_le_of_boundedWeight`). -/
theorem LDE_norm_flucAvg_le_of_boundedWeightD {u : ℝ} {z m : ℂ} {T : Idx d (sz.L n) (sz.W n) → ℝ}
    {B c : ℝ} {A : Finset (Idx d (sz.L n) (sz.W n))} (hT : BoundedWeight T c A)
    (hB : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), ‖LDE_flucDiagD sz n D u z m k ω‖ ≤ B)
    (ω : Sizes.SeqΩ sz) : ‖LDE_flucAvgD sz n D u z m T ω‖ ≤ B := by
  have h0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ω)
  have hsum : ∑ k, |T k| ≤ 1 := by
    rw [Finset.sum_congr rfl fun k _ => abs_of_nonneg (hT.nonneg k)]
    exact hT.sum_le
  calc ‖LDE_flucAvgD sz n D u z m T ω‖ ≤ (∑ k, |T k|) * B := LDE_norm_flucAvg_leD D hB ω
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hsum h0
    _ = B := one_mul B

/-- The `2p`-th power of `|∑_k t_k Z_k|` is integrable under a uniform bound on the `Z_k`, for `D + X`. -/
theorem LDE_integrable_norm_flucAvg_powD {u : ℝ} {z m : ℂ} {T : Idx d (sz.L n) (sz.W n) → ℝ} {B : ℝ}
    (hB : ∀ (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), ‖LDE_flucDiagD sz n D u z m k ω‖ ≤ B)
    (p : ℕ) :
    Integrable (fun ω => |‖LDE_flucAvgD sz n D u z m T ω‖| ^ (2 * p)) (Sizes.seqP sz) := by
  have hrw : (fun ω => |‖LDE_flucAvgD sz n D u z m T ω‖| ^ (2 * p))
      = fun ω => ‖LDE_flucAvgD sz n D u z m T ω‖ ^ (2 * p) := by
    funext ω; rw [abs_norm]
  rw [hrw]
  refine Integrable.mono' (integrable_const (((∑ k, |T k|) * B) ^ (2 * p)))
    (((LDE_measurable_flucAvgD D u z m T).norm.pow_const (2 * p)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : (0 : ℝ) ≤ ∑ k, |T k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (LDE_norm_flucAvg_leD D hB ω) _

end FlucShift

end FlucAvgPart

section LDEPart

open MeasureTheory ProbabilityTheory Matrix Finset RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
open scoped ComplexOrder NNReal ENNReal

/-! ### The diagonal Green function never vanishes off the real axis -/

section GreenDiag

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

private theorem LDE_isUnit_det {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (H - z • (1 : Matrix ν ν ℂ)).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (RBM.isUnit_sub_smul_of_isHermitian hH hz)

/-- **The Ward identity at one site.**  For Hermitian `H` and `Im z ≠ 0`, writing
`v = G e_i`, we have `Im G_{ii} = Im z · ‖v‖²`. -/
theorem im_green_diag {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : ν) :
    (green H z i i).im
      = z.im * (star (green H z *ᵥ Pi.single i 1) ⬝ᵥ (green H z *ᵥ Pi.single i 1)).re := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := LDE_isUnit_det hH hz
  set v : ν → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hvi : v i = green H z i i := by
    rw [hv]; simp
  have hMv : (H - z • (1 : Matrix ν ν ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hsplit : star v ⬝ᵥ ((H - z • (1 : Matrix ν ν ℂ)) *ᵥ v)
      = star v ⬝ᵥ (H *ᵥ v) - z * (star v ⬝ᵥ v) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  rw [hMv, dotProduct_single_one] at hsplit
  have hHim : (star v ⬝ᵥ H *ᵥ v).im = 0 := by
    simpa [RCLike.im_to_complex] using hH.im_star_dotProduct_mulVec_self v
  have hself : (star v ⬝ᵥ v).im = 0 := by
    have := dotProduct_star_self_nonneg v
    rw [Complex.le_def] at this
    exact this.2.symm
  have := congrArg Complex.im hsplit
  rw [Complex.sub_im, hHim, Complex.mul_im, hself] at this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_im, hvi] at this
  linarith [this]

/-- **`G_{ii} ≠ 0`.**  For Hermitian `H` and `Im z ≠ 0` the diagonal Green function is never
zero. -/
theorem green_diag_ne_zero {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : ν) : green H z i i ≠ 0 := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := LDE_isUnit_det hH hz
  set v : ν → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hMv : (H - z • (1 : Matrix ν ν ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hMv
    have h1 := congrFun hMv i
    simp at h1
  have hpos : (0 : ℂ) < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hvne
  rw [Complex.lt_def] at hpos
  have hre : (0 : ℝ) < (star v ⬝ᵥ v).re := by simpa using hpos.1
  intro hzero
  have him := im_green_diag hH hz i
  rw [hzero] at him
  simp only [Complex.zero_im] at him
  have : z.im = 0 := by
    rcases mul_eq_zero.1 him.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hre)
  exact hz this

end GreenDiag

section SideConditions

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u : ℝ} {z : ℂ}

/-! ### The side conditions hold for every `ω` -/

theorem isUnit_det_Hflow_sub {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (hz : z.im ≠ 0) :
    IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det :=
  LDE_isUnit_det (Sizes.seqHflow_isHermitian sz n u ω) hz

theorem green_Hflow_diag_ne_zero {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (hz : z.im ≠ 0) (x : Idx d (sz.L n) (sz.W n)) :
    green (Sizes.seqHflow sz n u ω) z x x ≠ 0 :=
  green_diag_ne_zero (Sizes.seqHflow_isHermitian sz n u ω) hz x

/-! ### The column LDE: the conjugated minor row -/

/-- Where the resolvent exists, the coefficients `minorRowConj` are the conjugated entries of
`G^{(j)}`. -/
theorem minorRowConj_eq_greenMinor (u : ℝ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGjj : green (Sizes.seqHflow sz n u ω) z j j ≠ 0) {l : Idx d (sz.L n) (sz.W n)} (hl : l ≠ j) :
    minorRowConj sz n u z j k ω l
      = (starRingEnd ℂ) (greenMinor (green (Sizes.seqHflow sz n u ω) z) j k.1 l) := by
  unfold minorRowConj
  rw [dite_eq_left_of_eq_true (by simpa using hl), inv_minor_resolvent hdet j hGjj]
  rfl

/-- **The left-hand side of the column LDE** is the row sum with the conjugated minor row. -/
theorem ldeColLHS_eq (u : ℝ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGjj : green (Sizes.seqHflow sz n u ω) z j j ≠ 0) :
    ldeColLHS (Sizes.seqHflow sz n u ω) (green (Sizes.seqHflow sz n u ω) z) k.1 j
      = ‖rowSum sz n u j (minorRowConj sz n u z j k) ω‖ ^ 2 := by
  have key : rowSum sz n u j (minorRowConj sz n u z j k) ω
      = (starRingEnd ℂ) (∑ l ∈ Finset.univ.erase j,
          greenMinor (green (Sizes.seqHflow sz n u ω) z) j k.1 l * Sizes.seqHflow sz n u ω l j) := by
    unfold rowSum
    rw [map_sum, Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
      (fun l => by simp [Finset.mem_erase]) _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [minorRowConj_eq_greenMinor u k hdet hGjj l.2, map_mul,
      show (starRingEnd ℂ) (Sizes.seqHflow sz n u ω l.1 j) = Sizes.seqHflow sz n u ω j l.1 from
        (Sizes.seqHflow_isHermitian sz n u ω).apply j l.1]
    ring
  rw [key, Complex.norm_conj, ldeColLHS]

/-- **The right-hand side of the column LDE** is the variance of that row sum, up to the factor
`u` (using `svarF_comm`). -/
theorem rowVarSum_minorRowConj_eq (u : ℝ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGjj : green (Sizes.seqHflow sz n u ω) z j j ≠ 0) :
    rowVarSum sz n u j (minorRowConj sz n u z j k) ω
      = u * ldeColRHS (svarF d (sz.L n) (sz.W n) (sz.lam n))
          (green (Sizes.seqHflow sz n u ω) z) k.1 j := by
  unfold rowVarSum ldeColRHS
  congr 1
  rw [Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
    (fun l => by simp [Finset.mem_erase]) _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [minorRowConj_eq_greenMinor u k hdet hGjj l.2, Complex.norm_conj,
    svarF_comm d (sz.L n) (sz.W n) (sz.lam n) j l.1]
  ring

end SideConditions

/-! ### Relabelling from the fine lattice `Idx` to the block-product index `Vtx`

Dimension `d` has two index types for the same lattice: the statements of `Green/EntryDom.lean`
(`hLrow`, `hLcol`, `hLdiag`) are on `Vtx d L W` through `blockMat`, `greenBlk`, `svar`, whereas the
row-sum results of `Green/RowIndep.lean` are on `Idx d L W`; the two are joined by `splitEquiv`. -/

section Relabel

variable {m ν : Type*} [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν]

omit [Fintype m] [Fintype ν] [DecidableEq m] [DecidableEq ν] in
private theorem LDE_greenMinor_submatrix (e : m ≃ ν) (G : Matrix ν ν ℂ) (a k l : m) :
    greenMinor (G.submatrix e e) a k l = greenMinor G (e a) (e k) (e l) := by
  simp [greenMinor]

private theorem LDE_ldeRowLHS_submatrix (e : m ≃ ν) (H G : Matrix ν ν ℂ) (a b : m) :
    ldeRowLHS (H.submatrix e e) (G.submatrix e e) a b = ldeRowLHS H G (e a) (e b) := by
  unfold ldeRowLHS
  congr 2
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

private theorem LDE_ldeRowRHS_submatrix (e : m ≃ ν) (S : ν → ν → ℝ) (G : Matrix ν ν ℂ)
    (a b : m) :
    ldeRowRHS (fun p q => S (e p) (e q)) (G.submatrix e e) a b = ldeRowRHS S G (e a) (e b) := by
  unfold ldeRowRHS
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

private theorem LDE_ldeColLHS_submatrix (e : m ≃ ν) (H G : Matrix ν ν ℂ) (a b : m) :
    ldeColLHS (H.submatrix e e) (G.submatrix e e) a b = ldeColLHS H G (e a) (e b) := by
  unfold ldeColLHS
  congr 2
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

private theorem LDE_ldeColRHS_submatrix (e : m ≃ ν) (S : ν → ν → ℝ) (G : Matrix ν ν ℂ)
    (a b : m) :
    ldeColRHS (fun p q => S (e p) (e q)) (G.submatrix e e) a b = ldeColRHS S G (e a) (e b) := by
  unfold ldeColRHS
  refine Finset.sum_equiv e (fun k => by simp [Finset.mem_erase]) (fun k _ => ?_)
  simp [LDE_greenMinor_submatrix]

end Relabel

section RelabelBlock

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The block resolvent is the fine-lattice resolvent, relabelled by `splitEquiv`. -/
private theorem LDE_greenBlk_true (E t : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    greenBlk d L W E t M true
      = (green M (zt E t)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  have h0 : greenBlk d L W E t M true = green (blockMat d L W M) (zt E t) := by
    simp only [greenBlk, Gres, green, ite_true]
    exact (Matrix.nonsing_inv_eq_ringInverse _).symm
  rw [h0]
  unfold green blockMat
  have h : (M - zt E t • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix
      (splitEquiv d L W).symm (splitEquiv d L W).symm
      = M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm
        - zt E t • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, (splitEquiv d L W).symm.injective.eq_iff]
  rw [← h, Matrix.inv_submatrix_equiv]

/-- The block profile `svar` is the fine-lattice profile `svarF` read through `splitEquiv`
(RBM2D `Sblk2_eq_svar`). -/
private theorem LDE_svar_eq_svarF (g : ℝ) (a b : Vtx d L W) :
    svar d L W g a b
      = svarF d L W g ((splitEquiv d L W).symm a) ((splitEquiv d L W).symm b) := by
  rw [svarF_eq_svar]
  have h1 : split d L W ((splitEquiv d L W).symm a) = a :=
    (splitEquiv d L W).apply_symm_apply a
  have h2 : split d L W ((splitEquiv d L W).symm b) = b :=
    (splitEquiv d L W).apply_symm_apply b
  rw [h1, h2]

private theorem LDE_svar_funext (g : ℝ) :
    svar d L W g
      = fun p q => svarF d L W g ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) := by
  funext p q; exact LDE_svar_eq_svarF g p q

private theorem LDE_blk_rowLHS (M G : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Vtx d L W) :
    ldeRowLHS (blockMat d L W M) (blockMat d L W G) a b
      = ldeRowLHS M G ((splitEquiv d L W).symm a) ((splitEquiv d L W).symm b) :=
  LDE_ldeRowLHS_submatrix (splitEquiv d L W).symm M G a b

private theorem LDE_blk_rowRHS (G : Matrix (Idx d L W) (Idx d L W) ℂ) (g : ℝ) (a b : Vtx d L W) :
    ldeRowRHS (svar d L W g) (blockMat d L W G) a b
      = ldeRowRHS (svarF d L W g) G ((splitEquiv d L W).symm a) ((splitEquiv d L W).symm b) := by
  rw [LDE_svar_funext g]
  exact LDE_ldeRowRHS_submatrix (splitEquiv d L W).symm (svarF d L W g) G a b

private theorem LDE_blk_colLHS (M G : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Vtx d L W) :
    ldeColLHS (blockMat d L W M) (blockMat d L W G) a b
      = ldeColLHS M G ((splitEquiv d L W).symm a) ((splitEquiv d L W).symm b) :=
  LDE_ldeColLHS_submatrix (splitEquiv d L W).symm M G a b

private theorem LDE_blk_colRHS (G : Matrix (Idx d L W) (Idx d L W) ℂ) (g : ℝ) (a b : Vtx d L W) :
    ldeColRHS (svar d L W g) (blockMat d L W G) a b
      = ldeColRHS (svarF d L W g) G ((splitEquiv d L W).symm a) ((splitEquiv d L W).symm b) := by
  rw [LDE_svar_funext g]
  exact LDE_ldeColRHS_submatrix (splitEquiv d L W).symm (svarF d L W g) G a b

end RelabelBlock

/-! ### The bridge from the normalised row sum to `PerTimeDomAt`, with a time sequence

RBM1D `stochDom_sq_of_rowSum` (`86573b9:Gauss/LDEHyp.lean:179`) used the fixed-`u` lemma
`highProb_norm_rowSum_sq_le`; here the time is a sequence `tim n ∈ [0, 1]`, so the degenerate
fibre argument is redone per `n` on top of the merged `stochDom_rowSum_generalTime`.  The
conclusion is the per-time form `PerTimeDomAt` (no union bound is needed for it). -/

section Bridge

variable {d : ℕ} {sz : Sizes d}

/-- **From `‖Z‖ / √V ≺ 1` to `‖Z‖² ≺ B`, uniformly in a time sequence.**  If `A = ‖Z‖²` and the
conditional variance is `tim n · B` with `0 ≤ tim n ≤ 1` and `B ≥ 0`, then `A ≺ B` in the
per-time form. -/
private theorem LDE_perTime_sq_of_rowSum (hsize : Filter.Tendsto sz.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (sz.size n : ℝ) ^ Ccard)
    (tim : ℕ → ℝ) (h0 : ∀ n, 0 ≤ tim n) (h1 : ∀ n, tim n ≤ 1)
    (row : ∀ n, U n → Idx d (sz.L n) (sz.W n))
    (C : ∀ n, U n → Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ sz),
      (∀ c ∈ offRowCoord sz n (row n q), ω c = ω' c) → C n q ω = C n q ω')
    {V : ℕ → Type*} (f : ∀ n, V n → U n) (A B : ∀ n, V n → Sizes.SeqΩ sz → ℝ)
    (hB : ∀ n v ω, 0 ≤ B n v ω)
    (hA : ∀ n v ω, A n v ω = ‖rowSum sz n (tim n) (row n (f n v)) (C n (f n v)) ω‖ ^ 2)
    (hVar : ∀ n v ω,
      rowVarSum sz n (tim n) (row n (f n v)) (C n (f n v)) ω = tim n * B n v ω) :
    PerTimeDomAt (Sizes.seqP sz) sz.size A B := by
  classical
  intro τ hτ D hD
  have hgood := stochDom_rowSum_generalTime (sz := sz) hsize hcard (fun n _ => tim n)
    (fun n _ => h0 n) row C hCmeas hC
  filter_upwards [hgood (τ / 2) (by linarith) D hD, hsize.eventually_ge_atTop 1] with n hn hn1
  intro v
  have hpos : (0 : ℝ) < (sz.size n : ℝ) := by exact_mod_cast hn1
  set q := f n v with hq
  have hnull : (Sizes.seqP sz) {ω | ¬ (rowVarSum sz n (tim n) (row n q) (C n q) ω = 0 →
      rowSum sz n (tim n) (row n q) (C n q) ω = 0)} = 0 := by
    have hae := rowSum_ae_eq_zero_of_varSum_eq_zero (sz := sz) (n := n) (i := row n q)
      (h0 n) (C n q) (hCmeas n q) (hC n q)
    simpa [MeasureTheory.ae_iff] using hae
  have hsub : {ω | (sz.size n : ℝ) ^ τ * B n v ω < A n v ω}
      ⊆ badSetAt sz.size (fun n q ω =>
          ‖rowSum sz n (tim n) (row n q) (rowCoeffNorm sz n (tim n) (row n q) (C n q)) ω‖)
          (fun _ _ _ => (1 : ℝ)) (τ / 2) n
        ∪ {ω | ¬ (rowVarSum sz n (tim n) (row n q) (C n q) ω = 0 →
            rowSum sz n (tim n) (row n q) (C n q) ω = 0)} := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1', h2'⟩ := hcon
    have h1'' : ‖rowSum sz n (tim n) (row n q)
        (rowCoeffNorm sz n (tim n) (row n q) (C n q)) ω‖ ≤ (sz.size n : ℝ) ^ (τ / 2) * 1 := by
      by_contra hlt
      exact h1' ⟨q, not_le.1 hlt⟩
    have h2'' : rowVarSum sz n (tim n) (row n q) (C n q) ω = 0 →
        rowSum sz n (tim n) (row n q) (C n q) ω = 0 := by
      by_contra hne
      exact h2' hne
    have hω' : (sz.size n : ℝ) ^ τ * B n v ω
        < ‖rowSum sz n (tim n) (row n q) (C n q) ω‖ ^ 2 := by
      have h := hω
      rw [Set.mem_ofPred_eq (p := fun ω => (sz.size n : ℝ) ^ τ * B n v ω < A n v ω)] at h
      rwa [hA n v ω] at h
    have hNB : 0 ≤ (sz.size n : ℝ) ^ τ * B n v ω :=
      mul_nonneg (Real.rpow_nonneg hpos.le τ) (hB n v ω)
    have hV0 : 0 ≤ rowVarSum sz n (tim n) (row n q) (C n q) ω := by
      rw [hVar n v ω]; exact mul_nonneg (h0 n) (hB n v ω)
    rcases eq_or_lt_of_le hV0 with hV | hV
    · rw [h2'' hV.symm] at hω'
      simp at hω'
      linarith
    · have hs : (0 : ℝ) < Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω) :=
        Real.sqrt_pos.2 hV
      rw [rowSum_rowCoeffNorm (C n q) hV, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs.le, mul_one] at h1''
      have hle : ‖rowSum sz n (tim n) (row n q) (C n q) ω‖
          ≤ (sz.size n : ℝ) ^ (τ / 2)
            * Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω) := by
        rw [inv_mul_le_iff₀ hs] at h1''
        linarith [h1'']
      have hnn : (0 : ℝ) ≤ ‖rowSum sz n (tim n) (row n q) (C n q) ω‖ := norm_nonneg _
      have hrhs : (0 : ℝ) ≤ (sz.size n : ℝ) ^ (τ / 2)
          * Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω) := by
        have : (0 : ℝ) ≤ (sz.size n : ℝ) ^ (τ / 2) := Real.rpow_nonneg hpos.le _
        positivity
      have hsq := mul_le_mul hle hle hnn hrhs
      have hsqrt : Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω) *
          Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω)
          = rowVarSum sz n (tim n) (row n q) (C n q) ω := Real.mul_self_sqrt hV0
      have hNpow : (sz.size n : ℝ) ^ (τ / 2) * (sz.size n : ℝ) ^ (τ / 2) = (sz.size n : ℝ) ^ τ := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      have hchain : ‖rowSum sz n (tim n) (row n q) (C n q) ω‖ ^ 2
          ≤ (sz.size n : ℝ) ^ τ * rowVarSum sz n (tim n) (row n q) (C n q) ω := by
        calc ‖rowSum sz n (tim n) (row n q) (C n q) ω‖ ^ 2
            = ‖rowSum sz n (tim n) (row n q) (C n q) ω‖
              * ‖rowSum sz n (tim n) (row n q) (C n q) ω‖ := by ring
          _ ≤ ((sz.size n : ℝ) ^ (τ / 2)
                * Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω)) *
              ((sz.size n : ℝ) ^ (τ / 2)
                * Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω)) := hsq
          _ = ((sz.size n : ℝ) ^ (τ / 2) * (sz.size n : ℝ) ^ (τ / 2)) *
              (Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω) *
                Real.sqrt (rowVarSum sz n (tim n) (row n q) (C n q) ω)) := by ring
          _ = (sz.size n : ℝ) ^ τ * rowVarSum sz n (tim n) (row n q) (C n q) ω := by
              rw [hNpow, hsqrt]
      have hvarle : rowVarSum sz n (tim n) (row n q) (C n q) ω ≤ B n v ω := by
        rw [hVar n v ω]
        nlinarith [hB n v ω, h1 n, h0 n]
      have hmul : (sz.size n : ℝ) ^ τ * rowVarSum sz n (tim n) (row n q) (C n q) ω
          ≤ (sz.size n : ℝ) ^ τ * B n v ω :=
        mul_le_mul_of_nonneg_left hvarle (Real.rpow_nonneg hpos.le τ)
      linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  exact hn

end Bridge

/-! ### The two hypotheses `hLrow`, `hLcol` of `entry_bound_stochDom` -/

section RowCol

variable {d : ℕ} (sz : Sizes d)

/-- **The row large deviation input `hLrow` for the flow `D + X` with a deterministic Hermitian shift**
(`D n` Hermitian, `Im z n ≠ 0`, `0 ≤ t n ≤ 1`; `X = H_{t_n}` of `sz` is the row, the resolvent
`G = (D + X - z)⁻¹` supplies the minors): `|∑_{k≠i} X_{ik} G^{(i)}_{kj}|² ≺ ∑_{k≠i} S_{ik} |G^{(i)}_{kj}|²`, uniformly in
`i ≠ j`, per time `t n`.  Only `D + X` Hermitian and `Im z ≠ 0` are used: `D` is a constant of the minor
(`RowIndep_minorColD`).  `D = 0`, `z = z_t` is `stochDom_ldeRow`. -/
theorem LDE_stochDom_ldeRow_shift (hsz : sz.SizeTendsto)
    (D : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hD : ∀ n, (D n).IsHermitian) {z : ℕ → ℂ} (hz : ∀ n, (z n).im ≠ 0)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1) :
    sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2) := by
  have hsz' : Filter.Tendsto sz.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  have hH : ∀ n ω, (D n + sz.seqHflow n (t n) ω).IsHermitian := fun n ω =>
    (hD n).add (Sizes.seqHflow_isHermitian sz n (t n) ω)
  have hdet : ∀ n ω, IsUnit (D n + sz.seqHflow n (t n) ω - z n • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det := fun n ω =>
    LDE_isUnit_det (hH n ω) (hz n)
  refine LDE_perTime_sq_of_rowSum (sz := sz) hsz' (eventually_card_LdeIdx_le sz) t ht0 ht1
    (fun n q => q.1)
    (fun n q => RowIndep_minorColD sz n (D n) (t n) (z n) q.1 q.2)
    (fun n q => RowIndep_measurable_minorColD (D n) (t n) _ q.1 q.2)
    (fun n q ω ω' h => RowIndep_minorColD_congr (D n) (t n) _ q.2 h)
    (V := fun n => OffPair d (sz.L n) (sz.W n))
    (fun n p => (⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.1,
      ⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.2,
        (splitEquiv d (sz.L n) (sz.W n)).symm.injective.ne (Ne.symm p.2)⟩⟩ : LdeIdx sz n)) _ _
    ?_ ?_ ?_
  · intro n p ω
    exact Finset.sum_nonneg fun k _ => mul_nonneg (svar_nonneg _ _ _ _ _ _) (by positivity)
  · intro n p ω
    rw [LDE_blk_rowLHS]
    exact RowIndep_ldeRowLHS_eqD (D n) (t n)
      ⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.2,
        (splitEquiv d (sz.L n) (sz.W n)).symm.injective.ne (Ne.symm p.2)⟩
      (hdet n ω) (green_diag_ne_zero (hH n ω) (hz n) _)
  · intro n p ω
    rw [LDE_blk_rowRHS]
    exact RowIndep_rowVarSum_eqD (D n) (t n)
      ⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.2,
        (splitEquiv d (sz.L n) (sz.W n)).symm.injective.ne (Ne.symm p.2)⟩
      (hdet n ω) (green_diag_ne_zero (hH n ω) (hz n) _)

/-- **The column large deviation input `hLcol` for the flow `D + X` with a deterministic Hermitian shift**
(hypotheses as in `LDE_stochDom_ldeRow_shift`): `|∑_{l≠j} G^{(j)}_{kl} X_{lj}|² ≺ ∑_{l≠j} |G^{(j)}_{kl}|² S_{lj}`,
uniformly in `k ≠ j`.  `D = 0`, `z = z_t` is `stochDom_ldeCol`. -/
theorem LDE_stochDom_ldeCol_shift (hsz : sz.SizeTendsto)
    (D : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hD : ∀ n, (D n).IsHermitian) {z : ℕ → ℂ} (hz : ∀ n, (z n).im ≠ 0)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1) :
    sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2) := by
  have hsz' : Filter.Tendsto sz.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  have hH : ∀ n ω, (D n + sz.seqHflow n (t n) ω).IsHermitian := fun n ω =>
    (hD n).add (Sizes.seqHflow_isHermitian sz n (t n) ω)
  have hdet : ∀ n ω, IsUnit (D n + sz.seqHflow n (t n) ω - z n • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det := fun n ω =>
    LDE_isUnit_det (hH n ω) (hz n)
  refine LDE_perTime_sq_of_rowSum (sz := sz) hsz' (eventually_card_LdeIdx_le sz) t ht0 ht1
    (fun n q => q.1)
    (fun n q => RowIndep_minorRowConjD sz n (D n) (t n) (z n) q.1 q.2)
    (fun n q => RowIndep_measurable_minorRowConjD (D n) (t n) _ q.1 q.2)
    (fun n q ω ω' h => RowIndep_minorRowConjD_congr (D n) (t n) _ q.2 h)
    (V := fun n => OffPair d (sz.L n) (sz.W n))
    (fun n p => (⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.2,
      ⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.1,
        (splitEquiv d (sz.L n) (sz.W n)).symm.injective.ne p.2⟩⟩ : LdeIdx sz n)) _ _ ?_ ?_ ?_
  · intro n p ω
    exact Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (svar_nonneg _ _ _ _ _ _)
  · intro n p ω
    rw [LDE_blk_colLHS]
    exact RowIndep_ldeColLHS_eqD (D n) (t n)
      ⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.1,
        (splitEquiv d (sz.L n) (sz.W n)).symm.injective.ne p.2⟩
      (hdet n ω) (green_diag_ne_zero (hH n ω) (hz n) _)
  · intro n p ω
    rw [LDE_blk_colRHS]
    exact RowIndep_rowVarSum_minorRowConjD_eq (D n) (t n)
      ⟨(splitEquiv d (sz.L n) (sz.W n)).symm p.1.1,
        (splitEquiv d (sz.L n) (sz.W n)).symm.injective.ne p.2⟩
      (hdet n ω) (green_diag_ne_zero (hH n ω) (hz n) _)

/-- **The row large deviation input `hLrow` of `entry_bound_stochDom`,** for the Gaussian flow
`H_{t_n}`: `|∑_{k≠i} H_{ik} G^{(i)}_{kj}|² ≺ ∑_{k≠i} S_{ik} |G^{(i)}_{kj}|²`, uniformly in
`i ≠ j`, per time `t n` (the conclusion is the text of `hLrow`, over the block-product index;
RBM1D `stochDom_ldeRow`, `86573b9:Gauss/LDEHyp.lean:221`; RBM2D `Green/LDE.lean:410`).  The band
statement is the corollary of `LDE_stochDom_ldeRow_shift` at `D = 0`, `z = z_t`. -/
theorem stochDom_ldeRow {κ : ℝ} (hκ : 0 < κ) (hsz : sz.SizeTendsto) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2) := by
  have h := LDE_stochDom_ldeRow_shift sz hsz (fun _ => 0) (fun _ => Matrix.isHermitian_zero)
    (z := fun n => zt (E n) (t n)) (fun n => zt_im_ne_zero hκ (hE n) (ht1 n)) ht0 fun n => (ht1 n).le
  simpa only [zero_add, LDE_greenBlk_true, blockMat] using h

/-- **The column large deviation input `hLcol` of `entry_bound_stochDom`,** for the Gaussian flow
`H_{t_n}`: `|∑_{l≠j} G^{(j)}_{kl} H_{lj}|² ≺ ∑_{l≠j} |G^{(j)}_{kl}|² S_{lj}`, uniformly in
`k ≠ j` (RBM1D `stochDom_ldeCol`, `86573b9:Gauss/LDEHyp.lean:246`; RBM2D `Green/LDE.lean:451`).  The
band statement is the corollary of `LDE_stochDom_ldeCol_shift` at `D = 0`, `z = z_t`. -/
theorem stochDom_ldeCol {κ : ℝ} (hκ : 0 < κ) (hsz : sz.SizeTendsto) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2) := by
  have h := LDE_stochDom_ldeCol_shift sz hsz (fun _ => 0) (fun _ => Matrix.isHermitian_zero)
    (z := fun n => zt (E n) (t n)) (fun n => zt_im_ne_zero hκ (hE n) (ht1 n)) ht0 fun n => (ht1 n).le
  simpa only [zero_add, LDE_greenBlk_true, blockMat] using h

end RowCol

/-! ### The diagonal input `hLdiag`

The diagonal entry `H_xx = √u · ω⟨n,x,x,tt⟩` is a real centred Gaussian of variance
`u · svarF_xx = u W^{-d} (1 + 2 d g²)⁻¹` (`g = sz.lam n`); the Gaussian moments below are re-ported
privately from `RowIndep.lean:89-160` (which is itself a private port of RBM1D
`Gauss/Moments.lean`). -/

section DiagMoments

private theorem LDE_integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

private theorem LDE_integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

private theorem LDE_integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := LDE_integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((LDE_integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    LDE_integrable_mul_gaussianPDFReal hv
      ((LDE_integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    LDE_integrable_mul_gaussianPDFReal hv (LDE_integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- **The even moments of a centred real Gaussian**: `E[X^{2p}] = (2p-1)!!·v^p`. -/
private theorem LDE_integral_pow_gaussianReal (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) = RowIndep_dfac p * (v : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 from by ring, LDE_integral_pow_gaussianReal_succ, ih,
      RowIndep_dfac_succ]
    ring

end DiagMoments

section Diag

/-- The diagonal of the block variance profile is `W^{-d} (1 + 2 d g²)⁻¹` (RBM2D
`Sblk2_diag_eq`: `1 / (5 W²)`, with no coupling; paper-delta candidate `T2078b`).  `svar` is the
merged `RBM.Gauss.svar` (RBM2D `Sblk2`). -/
theorem Sblk2_diag_eq {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W] (i : Vtx d L W) :
    svar d L W g i i = ((W : ℝ) ^ d)⁻¹ * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by
  simp [svar, SBR, sbKernelR]

/-- The diagonal of the variance profile is positive, for every real coupling `g`
(RBM2D `Sblk_diag_pos`: `1 / (5 W²) > 0`, RBM1D `86573b9:Gauss/LDEDiag.lean:37`). -/
theorem Sblk_diag_pos {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W] (i : Vtx d L W) :
    0 < svar d L W g i i := by
  have hW : (0 : ℝ) < W := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  rw [Sblk2_diag_eq]
  have : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  positivity

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u : ℝ}

/-! #### One coordinate -/

/-- Moments of a single coordinate, pushed through `Sizes.seqP_map_eval`. -/
theorem integral_pow_coord {d : ℕ} (sz : Sizes d) (c : Sizes.SeqCoord sz) (k : ℕ) :
    ∫ ω, (ω c) ^ k ∂(Sizes.seqP sz) = ∫ x : ℝ, x ^ k ∂(gaussianReal 0 (Sizes.seqGvar sz c)) := by
  have hf : AEMeasurable (fun ω : Sizes.SeqΩ sz => ω c) (Sizes.seqP sz) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ k) ((Sizes.seqP sz).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, Sizes.seqP_map_eval]

theorem integrable_pow_coord {d : ℕ} (sz : Sizes d) (c : Sizes.SeqCoord sz) (k : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ sz => (ω c) ^ k) (Sizes.seqP sz) := by
  have hf : AEMeasurable (fun ω : Sizes.SeqΩ sz => ω c) (Sizes.seqP sz) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ k) ((Sizes.seqP sz).map fun ω => ω c) := by
    fun_prop
  refine (integrable_map_measure hg hf).1 ?_
  rw [Sizes.seqP_map_eval]
  exact LDE_integrable_pow_gaussianReal _ k

/-! #### The diagonal entry of the flow -/

/-- The diagonal entry is real: `|H_{xx}|² = u · ω⟨n,x,x,tt⟩²`. -/
theorem normSq_Hflow_diag (hu : 0 ≤ u) (ω : Sizes.SeqΩ sz) (x : Idx d (sz.L n) (sz.W n)) :
    ‖Sizes.seqHflow sz n u ω x x‖ ^ 2 = u * (ω ⟨n, (x, x, true)⟩) ^ 2 := by
  have hX : Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) x x
      = ((ω ⟨n, (x, x, true)⟩ : ℝ) : ℂ) := by
    rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
    rfl
  have hH : Sizes.seqHflow sz n u ω x x
      = (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) x x := rfl
  rw [hH, hX, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u), mul_pow, Real.sq_sqrt hu, sq_abs]

/-- **All even moments of the diagonal entry**: `E|H_{xx}|^{2p} = u^p (2p-1)!! S_{xx}^p`. -/
theorem integral_norm_Hflow_diag_pow (hu : 0 ≤ u) (x : Idx d (sz.L n) (sz.W n)) (p : ℕ) :
    ∫ ω, ‖Sizes.seqHflow sz n u ω x x‖ ^ (2 * p) ∂(Sizes.seqP sz)
      = u ^ p * (RowIndep_dfac p * svarF d (sz.L n) (sz.W n) (sz.lam n) x x ^ p) := by
  have hpow : ∀ ω : Sizes.SeqΩ sz, ‖Sizes.seqHflow sz n u ω x x‖ ^ (2 * p)
      = u ^ p * (ω ⟨n, (x, x, true)⟩) ^ (2 * p) := by
    intro ω
    rw [pow_mul, normSq_Hflow_diag hu ω x, mul_pow, ← pow_mul, mul_comm 2 p]
  simp only [hpow]
  rw [integral_const_mul, integral_pow_coord, LDE_integral_pow_gaussianReal]
  have : ((Sizes.seqGvar sz ⟨n, (x, x, true)⟩ : ℝ≥0) : ℝ)
      = svarF d (sz.L n) (sz.W n) (sz.lam n) x x := by
    simp only [Sizes.seqGvar, gvarF, ite_true]
    rfl
  rw [this]

theorem integrable_norm_Hflow_diag_pow (hu : 0 ≤ u) (x : Idx d (sz.L n) (sz.W n)) (k : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ sz => ‖Sizes.seqHflow sz n u ω x x‖ ^ (2 * k))
      (Sizes.seqP sz) := by
  have hpow : ∀ ω : Sizes.SeqΩ sz, ‖Sizes.seqHflow sz n u ω x x‖ ^ (2 * k)
      = u ^ k * (ω ⟨n, (x, x, true)⟩) ^ (2 * k) := by
    intro ω
    rw [pow_mul, normSq_Hflow_diag hu ω x, mul_pow, ← pow_mul, mul_comm 2 k]
  simp only [hpow]
  exact (integrable_pow_coord sz _ (2 * k)).const_mul _

/-! #### The union bound -/

/-- The block-product index set has exactly `sz.size n = (W L)^d` elements (RBM2D
`eventually_card_Idx_le`: `(W L)²`; RBM1D `86573b9:Gauss/LDEDiag.lean:101`). -/
theorem eventually_card_Idx_le {d : ℕ} (sz : Sizes d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) ≤ (sz.size n : ℝ) ^ (1 : ℝ) := by
  refine Filter.Eventually.of_forall fun n => ?_
  rw [card_BlockIndex, Real.rpow_one, Sizes.size, mul_comm (sz.W n)]

/-- **The input `hLdiag` of `diag_bound_stochDom`**, for the Gaussian flow: `|H_{ii}|² ≺ S_{ii}`,
uniformly in `i`, per time `t n` with `0 ≤ t n < 1` (RBM1D `stochDom_normSq_Hflow_diag`,
`86573b9:Gauss/LDEDiag.lean:116`, for a fixed time; here the constant is uniform in the time
because `t n ≤ 1`; RBM2D `Green/LDE.lean:659`).  The constant is `(4p - 1)!! + 1`, independent of
`d`, `W`, `L`, `sz.lam n` and `n`: `E ‖H_xx‖^{4p} = u^{2p} (4p-1)!! S_xx^{2p}`. -/
theorem stochDom_normSq_Hflow_diag {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (fun n i _ => svar d (sz.L n) (sz.W n) (sz.lam n) i i) := by
  have hsz' : Filter.Tendsto sz.size Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hsz
  have hsd : StochDomAt (Sizes.seqP sz) sz.size
      (fun n (i : Vtx d (sz.L n) (sz.W n)) ω =>
        ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (fun n (i : Vtx d (sz.L n) (sz.W n)) _ => svar d (sz.L n) (sz.W n) (sz.lam n) i i) := by
    refine stochDomAt_of_momentDomAt (P := Sizes.seqP sz) sz.size hsz'
      (U := fun n => Vtx d (sz.L n) (sz.W n)) (Ccard := 1) (eventually_card_Idx_le sz)
      (Y := fun n (i : Vtx d (sz.L n) (sz.W n)) ω =>
        ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (Φ := fun n (i : Vtx d (sz.L n) (sz.W n)) => svar d (sz.L n) (sz.W n) (sz.lam n) i i)
      (fun n i => Sblk_diag_pos (sz.lam n) i) ?_ ?_
    · intro p n i
      have habs : ∀ ω : Sizes.SeqΩ sz,
          |‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2| ^ (2 * p)
            = ‖Sizes.seqHflow sz n (t n) ω ((splitEquiv d (sz.L n) (sz.W n)).symm i)
                ((splitEquiv d (sz.L n) (sz.W n)).symm i)‖ ^ (2 * (2 * p)) := fun ω => by
        rw [abs_of_nonneg (by positivity), ← pow_mul]
        rfl
      simp only [habs]
      exact integrable_norm_Hflow_diag_pow (ht0 n) _ (2 * p)
    · intro ε hε p
      have hd0 : (0 : ℝ) ≤ RowIndep_dfac (2 * p) := by unfold RowIndep_dfac; positivity
      refine ⟨RowIndep_dfac (2 * p) + 1, by linarith, ?_⟩
      filter_upwards [hsz'.eventually_ge_atTop 1] with n hn1 i
      have hN1' : (1 : ℝ) ≤ (sz.size n : ℝ) := by exact_mod_cast hn1
      have hS : (0 : ℝ) < svar d (sz.L n) (sz.W n) (sz.lam n) i i := Sblk_diag_pos (sz.lam n) i
      have hpt : ∀ ω : Sizes.SeqΩ sz,
          |‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2| ^ (2 * p)
            = ‖Sizes.seqHflow sz n (t n) ω ((splitEquiv d (sz.L n) (sz.W n)).symm i)
                ((splitEquiv d (sz.L n) (sz.W n)).symm i)‖ ^ (2 * (2 * p)) := fun ω => by
        rw [abs_of_nonneg (by positivity), ← pow_mul]
        rfl
      simp only [hpt]
      rw [integral_norm_Hflow_diag_pow (ht0 n), ← LDE_svar_eq_svarF]
      have hpow : (1 : ℝ) ≤ (sz.size n : ℝ) ^ (ε * p) := Real.one_le_rpow hN1' (by positivity)
      have hu : (t n) ^ (2 * p) ≤ 1 := pow_le_one₀ (ht0 n) (ht1 n).le
      set A : ℝ := svar d (sz.L n) (sz.W n) (sz.lam n) i i ^ (2 * p) with hAdef
      have hA0 : 0 < A := by rw [hAdef]; positivity
      calc (t n) ^ (2 * p) * (RowIndep_dfac (2 * p) * A)
          ≤ 1 * (RowIndep_dfac (2 * p) * A) :=
            mul_le_mul_of_nonneg_right hu (by positivity)
        _ = RowIndep_dfac (2 * p) * A := one_mul _
        _ ≤ (RowIndep_dfac (2 * p) + 1) * A := by nlinarith
        _ ≤ (RowIndep_dfac (2 * p) + 1) * ((sz.size n : ℝ) ^ (ε * p) * A) := by
            have h1 : A ≤ (sz.size n : ℝ) ^ (ε * p) * A := le_mul_of_one_le_left hA0.le hpow
            exact mul_le_mul_of_nonneg_left h1 (by linarith)
  exact perTimeOfStochDomAt _ _ _ _ hsd

end Diag

end LDEPart

namespace LDEInst

/-! ### Compiled nonempty instances at the preflight sequence `sz0` (`d = 3`)

`SizesInst.sz0` (`RBM3D/Defs/Sizes.lean:260`): `L n = 4 (n + 1)`, `W n = (2 (n + 1))^5`,
`lam n = (2 (n + 1))^{-6}`, `d = 3`; at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`,
`N = (W L)^3 = 2097152`.  The external hypotheses are `SizeTendsto` and `Bandwidth`, computed at
`sz0` (`sz0_tendsto`, `sz0_bandwidth`, `W/L → ∞`, `N^{1/6}/W = √(L/W) → 0`); every other
hypothesis is deterministic and discharged.  The energy is `E ≡ 0` (`|E| ≤ 2 - κ` with `κ = 1`),
the time `t ≡ 1/2` (`0 ≤ t < 1`, `Im z_t = 1/2`).  The only hypothesis left is `hLquad` of
`diag_bound_stochDom`, the quadratic-form large deviation of the tickets S1-12 - S1-19. -/

open RBM.Gauss RBM.Gauss.SizesInst
open scoped Matrix.Norms.L2Operator

private theorem inst_zt_im_ne_zero : (zt 0 (1 / 2)).im ≠ 0 :=
  zt_im_ne_zero (κ := 1) one_pos (by norm_num) (by norm_num)

/-! #### Target `eventually_le_W` and `tendsto_W` -/

/-- **Instance of `tendsto_W`** at `sz0`, `𝔠 = 1/6`: `W n → ∞`. -/
theorem tendsto_W_sz0 : Filter.Tendsto (fun n => (sz0.W n : ℝ)) Filter.atTop Filter.atTop :=
  tendsto_W sz0 (c := 1 / 6) (by norm_num) sz0_tendsto sz0_bandwidth

/-- **Instance of `eventually_le_W`** at `sz0`, `𝔠 = 1/6`, every `p`: both external hypotheses
(`SizeTendsto`, `Bandwidth`) hold at `sz0`; the threshold depends on `sz0` and `p` only. -/
theorem eventually_le_W_sz0 (p : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, p ≤ sz0.W n :=
  eventually_le_W sz0 (c := 1 / 6) (by norm_num) sz0_tendsto sz0_bandwidth p

/-- Nondegenerate: `p = 10^6` (the first `n` with `10^6 ≤ W n` is `n = 7`, `W 7 = 1048576`). -/
theorem eventually_le_W_sz0_million : ∀ᶠ n : ℕ in Filter.atTop, 1000000 ≤ sz0.W n :=
  eventually_le_W_sz0 1000000

/-! #### Target `stochDom_normSq_Hflow_diag` -/

/-- **Instance of `stochDom_normSq_Hflow_diag`** (the hypothesis `hLdiag` of
`diag_bound_stochDom`) at `sz0`, `t ≡ 1/2`: only `SizeTendsto` (computed at `sz0`) and the
deterministic `0 ≤ t < 1`. -/
theorem stochDom_normSq_Hflow_diag_sz0 :
    sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ‖blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω) i i‖ ^ 2)
      (fun n i _ => svar 3 (sz0.L n) (sz0.W n) (sz0.lam n) i i) :=
  stochDom_normSq_Hflow_diag sz0 sz0_tendsto (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num)

/-- The diagonal variance at `sz0`, `n = 0`, is `W^{-d} (1 + 2 d g²)⁻¹ = 32768⁻¹ (1 + 6/4096)⁻¹`
and positive (`Sblk2_diag_eq`, `Sblk_diag_pos`): the domination `‖H_ii‖² ≺ S_ii` is not
degenerate. -/
theorem diag_variance_sz0 (i : Vtx 3 (sz0.L 0) (sz0.W 0)) :
    svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i i
      = ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * (3 : ℝ) * (1 / 64) ^ 2)⁻¹ ∧
    0 < svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i i := by
  refine ⟨?_, Sblk_diag_pos _ i⟩
  rw [Sblk2_diag_eq]
  have hW : (sz0.W 0 : ℝ) = 32 := by exact_mod_cast sz0_values.2.1
  have hl : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  rw [hW, hl]
  norm_num

/-- The sizes of the numeric check of the preflight, `d = 3`, `L = 3`, `W = 2`, `g = 1/2`
(constant sequences; no limit statement is claimed at them). -/
private noncomputable def szT : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

/-- **Instance of `integral_norm_Hflow_diag_pow`**, the moment behind the constant of
`stochDom_normSq_Hflow_diag`, at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `u = 1/2`: `S_xx = 1/20`,
`E |H_xx|^4 = u² · 3 · S_xx² = 3/1600`. -/
theorem integral_norm_Hflow_diag_pow_szT (x : Idx 3 (szT.L 0) (szT.W 0)) :
    ∫ ω, ‖szT.seqHflow 0 (1 / 2) ω x x‖ ^ (2 * 2) ∂(Sizes.seqP szT) = 3 / 1600 := by
  rw [integral_norm_Hflow_diag_pow (by norm_num)]
  have hS : svarF 3 (szT.L 0) (szT.W 0) (szT.lam 0) x x = 1 / 20 := by
    rw [svarF_diag]
    norm_num [szT]
  rw [hS]
  simp only [RowIndep_dfac, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num

/-! #### Targets `stochDom_ldeRow`, `stochDom_ldeCol` and their use in `(GijGEX)`, `(GiiGEX)` -/

/-- **Instance of `stochDom_ldeRow`** (the hypothesis `hLrow` of `entry_bound_stochDom`) at
`sz0`, `E ≡ 0`, `κ = 1`, `t ≡ 1/2`. -/
theorem stochDom_ldeRow_sz0 :
    sz0.PrecPT (U := fun n => OffPair 3 (sz0.L n) (sz0.W n))
      (fun n u ω => ldeRowLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2) :=
  stochDom_ldeRow sz0 (κ := 1) one_pos sz0_tendsto (E := fun _ => 0) (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)

/-- **Instance of `stochDom_ldeCol`** (the hypothesis `hLcol` of `entry_bound_stochDom`) at the
same data. -/
theorem stochDom_ldeCol_sz0 :
    sz0.PrecPT (U := fun n => OffPair 3 (sz0.L n) (sz0.W n))
      (fun n u ω => ldeColLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2) :=
  stochDom_ldeCol sz0 (κ := 1) one_pos sz0_tendsto (E := fun _ => 0) (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)

/-- A nonzero Hermitian shift for the instances of the `D`-versions (T2389): `D = (1/2) I` at `sz0`, every `n`
(`D = 0` is the band, `D = g₀ Ψ` the block Anderson model). -/
noncomputable def LDE_shiftD_sz0 (n : ℕ) :
    Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)

theorem LDE_shiftD_sz0_isHermitian (n : ℕ) : (LDE_shiftD_sz0 n).IsHermitian :=
  Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])

/-- **Instances of `LDE_stochDom_ldeRow_shift` and `LDE_stochDom_ldeCol_shift`** at `sz0`, `t ≡ 1/2`,
`z ≡ z_{1/2}` and the nonzero shift `D = (1/2) I`: every deterministic hypothesis is discharged (`SizeTendsto`
is computed at `sz0`). -/
example := LDE_stochDom_ldeRow_shift sz0 sz0_tendsto LDE_shiftD_sz0 LDE_shiftD_sz0_isHermitian
  (z := fun _ => zt 0 (1 / 2)) (fun _ => inst_zt_im_ne_zero) (t := fun _ => 1 / 2)
  (fun _ => by norm_num) (fun _ => by norm_num)

example := LDE_stochDom_ldeCol_shift sz0 sz0_tendsto LDE_shiftD_sz0 LDE_shiftD_sz0_isHermitian
  (z := fun _ => zt 0 (1 / 2)) (fun _ => inst_zt_im_ne_zero) (t := fun _ => 1 / 2)
  (fun _ => by norm_num) (fun _ => by norm_num)

/-- **Instance of the `D`-envelopes** at `sz0`, the shift `D = (1/2) I`, `z = z_{1/2}`, `m = m(0)` (`‖m‖ = 1`):
`B = 2(|Im z|⁻¹ + 1)` and `ε = 4 |Im z|⁻¹` bound the fluctuation layer of `D + X`, for every `u`. -/
example (u : ℝ) : LDE_FlucBoundD sz0 0 (LDE_shiftD_sz0 0) u (zt 0 (1 / 2)) (mE 0)
    (2 * (|(zt 0 (1 / 2)).im|⁻¹ + 1)) (4 * |(zt 0 (1 / 2)).im|⁻¹) :=
  LDE_flucBound_envD (LDE_shiftD_sz0 0) (LDE_shiftD_sz0_isHermitian 0) inst_zt_im_ne_zero
    (norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)).le u

/-- **Instances of the other `D`-twins of the averaging layer** at `sz0`, `n = 0`, the shift `D = (1/2) I`,
`z = z_{1/2}`, `m = m(0)` (`‖m‖ = 1`), `u = 1/2`: the envelope of the centred diagonal and of the minor, the bounded
weight `j ↦ S_{0j}` (not a uniform weight), integrability of `|∑_j S_{0j} Z_j|⁴`, measurability, and the bridge
`LDE_shift_zero` to the band `FlucVanish` objects. -/
example (k : Idx 3 (sz0.L 0) (sz0.W 0)) (ω : Sizes.SeqΩ sz0) :
    ‖LDE_greenDiagCenteredD sz0 0 (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0) k ω‖
      ≤ |(zt 0 (1 / 2)).im|⁻¹ + 1 :=
  LDE_norm_greenDiagCentered_le_envD (LDE_shiftD_sz0 0) (LDE_shiftD_sz0_isHermitian 0) inst_zt_im_ne_zero
    (norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)).le (1 / 2) k ω

example (κ : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : {a : Idx 3 (sz0.L 0) (sz0.W 0) // a ≠ κ}) (ω : Sizes.SeqΩ sz0) :
    ‖LDE_greenMinorMatD sz0 0 (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) κ ω a b‖ ≤ |(zt 0 (1 / 2)).im|⁻¹ :=
  LDE_norm_greenMinorMat_apply_leD (LDE_shiftD_sz0 0) (LDE_shiftD_sz0_isHermitian 0) inst_zt_im_ne_zero (1 / 2) a b ω

example (ω : Sizes.SeqΩ sz0) :
    ‖LDE_flucAvgD sz0 0 (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0)
      (fun j : Idx 3 (sz0.L 0) (sz0.W 0) => svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j) ω‖
      ≤ 2 * (|(zt 0 (1 / 2)).im|⁻¹ + 1) :=
  LDE_norm_flucAvg_le_of_boundedWeightD (LDE_shiftD_sz0 0)
    (boundedWeight_svarF 3 (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (sz0.lam 0) 0)
    (LDE_flucBound_envD (LDE_shiftD_sz0 0) (LDE_shiftD_sz0_isHermitian 0) inst_zt_im_ne_zero
      (norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)).le (1 / 2)).flucDiag_le ω

example : MeasureTheory.Integrable
    (fun ω => |‖LDE_flucAvgD sz0 0 (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0)
      (fun j : Idx 3 (sz0.L 0) (sz0.W 0) => svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j) ω‖| ^ (2 * 2))
    (Sizes.seqP sz0) :=
  LDE_integrable_norm_flucAvg_powD (LDE_shiftD_sz0 0)
    (LDE_flucBound_envD (LDE_shiftD_sz0 0) (LDE_shiftD_sz0_isHermitian 0) inst_zt_im_ne_zero
      (norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)).le (1 / 2)).flucDiag_le 2

example (κ : Idx 3 (sz0.L 0) (sz0.W 0)) (k : {a : Idx 3 (sz0.L 0) (sz0.W 0) // a ≠ κ}) :
    Measurable (LDE_greenMinorDiagCenteredD sz0 0 (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0) κ k) :=
  LDE_measurable_greenMinorDiagCenteredD (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0) κ k

example (k : Idx 3 (sz0.L 0) (sz0.W 0)) (T : Idx 3 (sz0.L 0) (sz0.W 0) → ℝ) :
    Measurable (LDE_flucDiagD sz0 0 (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0) k) ∧
      Measurable (LDE_flucAvgD sz0 0 (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0) T) :=
  ⟨LDE_measurable_flucDiagD (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0) k,
    LDE_measurable_flucAvgD (LDE_shiftD_sz0 0) (1 / 2) (zt 0 (1 / 2)) (mE 0) T⟩

example (κ k : Idx 3 (sz0.L 0) (sz0.W 0)) (T : Idx 3 (sz0.L 0) (sz0.W 0) → ℝ)
    (k' : {a : Idx 3 (sz0.L 0) (sz0.W 0) // a ≠ κ}) :=
  LDE_shift_zero sz0 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) k κ T k'

/-- **The band is recovered at `D = 0`** (two of the `D`-versions): `measurable_green_apply` and
`norm_green_apply_le_etaT` from `LDE_measurable_green_applyD` and `LDE_norm_green_apply_leD`. -/
example {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (i j : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω => green (Sizes.seqHflow sz n u ω) z i j := by
  simpa using LDE_measurable_green_applyD (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) u z i j

example {d : ℕ} {sz : Sizes d} {n : ℕ} {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ‖green (Sizes.seqHflow sz n u ω) (zt E t) i j‖ ≤ ((zt E t).im)⁻¹ := by
  have hη := flucAvg_zt_im_pos hE ht
  simpa [abs_of_pos hη] using LDE_norm_green_apply_leD
    (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) Matrix.isHermitian_zero hη.ne' u i j ω

/-- **`(GijGEX)`, `3_5:24`, with no large deviation hypothesis left**: `GijOmegaSeq` at `sz0`, `E ≡ 0`, `t ≡ 1/2`,
`κ = 1`, `𝔠 = 1/6`, `𝔡 = 1/10`, `c = 1`, from the two proved inputs. -/
example : GijOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
  entry_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) one_pos sz0_admissible
    (E := fun _ => 0) (t := fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) one_pos
    stochDom_ldeRow_sz0 stochDom_ldeCol_sz0

section AtHalf

variable
  (hLquad : sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
    (fun n i ω => ldeQuadLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true)
      (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n)) (1 / 2) i)
    (fun n i ω => ldeQuadRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) i))

include hLquad in
/-- **`(GiiGEX)`, `3_5:21`**: `GiiOmegaSeq` at the same data, with the quadratic-form input `hLquad` (not this
ticket's) left as a variable and the other three inputs (`hLrow`, `hLcol`, `hLdiag`) proved. -/
example : GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
  diag_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) one_pos stochDom_ldeRow_sz0
    stochDom_ldeCol_sz0 hLquad stochDom_normSq_Hflow_diag_sz0

end AtHalf

/-! #### The Ward identity, the minor formula and the column sum -/

/-- **Instance of `green_Hflow_diag_ne_zero` and `isUnit_det_Hflow_sub`** at `sz0`, every sample
point and every site. -/
theorem green_diag_ne_zero_sz0 (ω : Sizes.SeqΩ sz0) (x : Idx 3 (sz0.L 0) (sz0.W 0)) :
    IsUnit (sz0.seqHflow 0 (1 / 2) ω - zt 0 (1 / 2) •
      (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)).det ∧
    green (sz0.seqHflow 0 (1 / 2) ω) (zt 0 (1 / 2)) x x ≠ 0 :=
  ⟨isUnit_det_Hflow_sub sz0 0 (1 / 2) ω inst_zt_im_ne_zero,
    green_Hflow_diag_ne_zero sz0 0 (1 / 2) ω inst_zt_im_ne_zero x⟩

/-- **Instance of `ldeColLHS_eq`** at `sz0`: the column sum is the norm of a row sum, at every
sample point. -/
theorem ldeColLHS_eq_sz0 (ω : Sizes.SeqΩ sz0) (j : Idx 3 (sz0.L 0) (sz0.W 0))
    (k : {a : Idx 3 (sz0.L 0) (sz0.W 0) // a ≠ j}) :
    ldeColLHS (sz0.seqHflow 0 (1 / 2) ω) (green (sz0.seqHflow 0 (1 / 2) ω) (zt 0 (1 / 2))) k.1 j
      = ‖rowSum sz0 0 (1 / 2) j (minorRowConj sz0 0 (1 / 2) (zt 0 (1 / 2)) j k) ω‖ ^ 2 :=
  ldeColLHS_eq (1 / 2) k (isUnit_det_Hflow_sub sz0 0 (1 / 2) ω inst_zt_im_ne_zero)
    (green_Hflow_diag_ne_zero sz0 0 (1 / 2) ω inst_zt_im_ne_zero j)

/-- **Instance of `rowVarSum_minorRowConj_eq`** at `sz0`, at every sample point. -/
theorem rowVarSum_minorRowConj_eq_sz0 (ω : Sizes.SeqΩ sz0) (j : Idx 3 (sz0.L 0) (sz0.W 0))
    (k : {a : Idx 3 (sz0.L 0) (sz0.W 0) // a ≠ j}) :
    rowVarSum sz0 0 (1 / 2) j (minorRowConj sz0 0 (1 / 2) (zt 0 (1 / 2)) j k) ω
      = (1 / 2) * ldeColRHS (svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0))
          (green (sz0.seqHflow 0 (1 / 2) ω) (zt 0 (1 / 2))) k.1 j :=
  rowVarSum_minorRowConj_eq (1 / 2) k (isUnit_det_Hflow_sub sz0 0 (1 / 2) ω inst_zt_im_ne_zero)
    (green_Hflow_diag_ne_zero sz0 0 (1 / 2) ω inst_zt_im_ne_zero j)

/-- **Instance of `minorRowConj_eq_greenMinor`** at `sz0`, at every sample point (`l ≠ j`). -/
theorem minorRowConj_eq_greenMinor_sz0 (ω : Sizes.SeqΩ sz0) (j : Idx 3 (sz0.L 0) (sz0.W 0))
    (k : {a : Idx 3 (sz0.L 0) (sz0.W 0) // a ≠ j}) {l : Idx 3 (sz0.L 0) (sz0.W 0)} (hl : l ≠ j) :
    minorRowConj sz0 0 (1 / 2) (zt 0 (1 / 2)) j k ω l
      = (starRingEnd ℂ) (greenMinor (green (sz0.seqHflow 0 (1 / 2) ω) (zt 0 (1 / 2))) j k.1 l) :=
  minorRowConj_eq_greenMinor (1 / 2) k (isUnit_det_Hflow_sub sz0 0 (1 / 2) ω inst_zt_im_ne_zero)
    (green_Hflow_diag_ne_zero sz0 0 (1 / 2) ω inst_zt_im_ne_zero j) hl

/-! #### The averaging layer: envelopes, `FlucBound`, the bounded weight -/

/-- `Im z_0 = 1` at `E = 0` (`m(0) = i`), so the envelope parameters are `B = ε = 4`. -/
private theorem inst_zt_zero_im : (zt 0 0).im = 1 := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [zt_im, mE_im]
  simp [hs]

/-- **Instance of `flucBound_env`** at `sz0`, `n = 0`, `E = 0`, `t = 0`: `B = ε = 4`. -/
theorem flucBound_env_sz0 (u : ℝ) : FlucBound sz0 0 u (zt 0 0) (mE 0) 4 4 := by
  have h := flucBound_env (E := 0) (t := 0) (by norm_num) (by norm_num) sz0 0 u
  rw [inst_zt_zero_im] at h
  norm_num at h
  exact h

/-- **Instance of the envelope** `norm_green_apply_le_etaT` at `sz0`, `t = 1/2`: `Im z_t = 1/2`,
`|G_{ij}| ≤ 2` for every `ω`. -/
theorem norm_green_apply_le_etaT_sz0 (ω : Sizes.SeqΩ sz0) (i j : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ‖green (sz0.seqHflow 0 (1 / 2) ω) (zt 0 (1 / 2)) i j‖ ≤ ((zt 0 (1 / 2)).im)⁻¹ :=
  norm_green_apply_le_etaT (E := 0) (t := 1 / 2) (by norm_num) (by norm_num) (1 / 2) i j ω

/-- **Instance of `LDE_norm_flucAvg_le_of_boundedWeight`** at `sz0`, `n = 0`, `E = 0`, `t = 1/2`:
the row weight `j ↦ S_{0j}` (`boundedWeight_svarF`, `c = W^{-d}`, `(2d + 1) W^d` sites; not a
uniform weight) gives `|∑_j S_{0j} Z_j| ≤ 2 (η⁻¹ + 1)`, at every sample point. -/
theorem norm_flucAvg_le_boundedWeight_sz0 (ω : Sizes.SeqΩ sz0) :
    ‖flucAvg sz0 0 (1 / 2) (zt 0 (1 / 2)) (mE 0)
      (fun j : Idx 3 (sz0.L 0) (sz0.W 0) => svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j) ω‖
      ≤ 2 * (((zt 0 (1 / 2)).im)⁻¹ + 1) :=
  LDE_norm_flucAvg_le_of_boundedWeight
    (boundedWeight_svarF 3 (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (sz0.lam 0) 0)
    (flucBound_env (E := 0) (t := 1 / 2) (by norm_num) (by norm_num) sz0 0 (1 / 2)).flucDiag_le ω

/-- **Instance of `norm_flucAvg_le`**: the same average with the weight `|T|` summed directly. -/
theorem norm_flucAvg_le_sz0 (ω : Sizes.SeqΩ sz0) :
    ‖flucAvg sz0 0 (1 / 2) (zt 0 (1 / 2)) (mE 0)
      (fun j : Idx 3 (sz0.L 0) (sz0.W 0) => svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j) ω‖
      ≤ (∑ j : Idx 3 (sz0.L 0) (sz0.W 0), |svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j|)
        * (2 * (((zt 0 (1 / 2)).im)⁻¹ + 1)) :=
  norm_flucAvg_le
    (flucBound_env (E := 0) (t := 1 / 2) (by norm_num) (by norm_num) sz0 0 (1 / 2)).flucDiag_le ω

/-! #### The counting facts -/

/-- **Instance of `card_blockAvg_support`**: a block has `W^d = 32768` sites at `sz0`, `n = 0`. -/
theorem card_blockAvg_support_sz0 (a : Zd 3 (sz0.L 0)) :
    ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun k =>
      (split 3 (sz0.L 0) (sz0.W 0) k).1 = a).card = 32768 := by
  rw [card_blockAvg_support]
  have hW : sz0.W 0 = 32 := sz0_values.2.1
  rw [hW]
  norm_num

/-- **Instance of `card_Sblk_support`**: the row support has `(2d + 1) W^d = 229376` sites. -/
theorem card_Sblk_support_sz0 (i : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun j =>
      (split 3 (sz0.L 0) (sz0.W 0) j).1 - (split 3 (sz0.L 0) (sz0.W 0) i).1
        ∈ flucVanish_sbSupport 3 (sz0.L 0)).card = 229376 := by
  rw [card_Sblk_support]
  have hW : sz0.W 0 = 32 := sz0_values.2.1
  rw [hW]
  norm_num

/-- **Instance of `flucAvg_card_Idx_eq_size` and `flucAvg_card_Z2_le_size`**: `#Idx = N =
2097152` and `#Zd 3 4 = 64 ≤ N`. -/
theorem flucAvg_card_sz0 :
    Fintype.card (Idx 3 (sz0.L 0) (sz0.W 0)) = 2097152 ∧
      Fintype.card (Zd 3 (sz0.L 0)) = 64 ∧
      Fintype.card (Zd 3 (sz0.L 0)) ≤ sz0.size 0 := by
  refine ⟨?_, ?_, flucAvg_card_Z2_le_size sz0 0⟩
  · rw [flucAvg_card_Idx_eq_size]; exact sz0_values.2.2.1
  · have hL : sz0.L 0 = 4 := sz0_values.1
    simp [Zd, ZMod.card, hL]

end LDEInst

end RBM.Green
