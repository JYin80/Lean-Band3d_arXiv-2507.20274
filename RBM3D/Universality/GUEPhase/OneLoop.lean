/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Gauss.SteinMatrix
import RBM3D.Green.Stability
import RBM3D.Hierarchy.ContractionSecondLoop
import RBM3D.Gauss.LoopFlowStein
import RBM3D.Loop.KLSumZero

/-!
# Lemma 5.15 for the GUE-phase grid: the `1`-loop expectation bound, `d ≥ 3`

Ticket T2353 (UN-45/46).  Port of RBM2D `Universality/GUEPhase/OneLoop.lean` (1729 lines, RBM2D
commit `9e0f275`; cited `OL:<line>`) at `d ≥ 3`.  Paper: arXiv:2507.20274, the GUE phase of Thm 2.4
(`paper/tex/1_2_Intro_model_result.tex:566-570`: "essentially identical to that used for
one-dimensional [YY_25, Theorem 2.6] and two-dimensional [DYYY25, Theorem 2.6]").  The band-flow
form of the lemma is `lem:improve_exp_aver` (`paper/tex/6_Step6_two_loop.tex:12-21`,
`max_a |𝔼 tr((G_u - M) E_a)| ≺ (W^{-d} B_{u,0})²`, whose proof "is the same as that of
[YY_25, Lemma 5.15]"); this file is the GUE-phase-grid form `N^ε (N η_u)^{-2}` of the RBM2D port.

**Result.**  `gueGrid_expect_oneLoop`: the pathwise `1`-loop bound
`‖⟨(G - m)E_a⟩‖ ≺ (N η_u)^{-1}` (`StochDomAt (Pgue sz) sz.size`, uniformly in the grid time and
the block label) implies `‖𝔼⟨(G - m)E_a⟩‖ ≤ N^ε (N η_u)^{-2}` eventually, for every `ε > 0`.

**Proof.**
* The one-time law of grid step `k` (`olComb`, `olVar`, `ol_map_comb`, `ol_map_comb_slice`,
  `ol_gueH_eq`): `gueH` at step `k` is `Xmat` of the size-`n` slice of
  `√t₁ ω₀ + √(Δ/N) Σ_{i≤k} ω_i`, which has the product Gaussian law with variances
  `t₁ seqGvar_c + k (Δ/N) gueUnitVar_c`.
* Stein's identity for that product Gaussian applied to `tr(B_c G E_a)`, with the contraction of
  the mixed variances: the `t₁` part is `sum_coordinateBlock_trace_pair`, the unit-GUE part is
  `OneLoop_sum_gue_block`, `Σ_c w_c tr(A B_c C B_c) = tr A tr C`.  Result:
  `𝔼 tr(H G E_a) = -Σ_p Ŝ_{pa} 𝔼[g_p g_a]`, `Ŝ = t₁ S^{(B)} + ((u - t₁)/L^d) J` (row sums `u`),
  and with `m z_u + u m² = -1` the block identity `OneLoop_selfcons`.
* Stability of `1 - m² Ŝ` in `max → max` (`OneLoop_stable`): the zero mode through
  `|1 - u m²| ≥ gapK κ`, the rest through the proved `d ≥ 3` stability constant
  `Kstab3 d Λ κ` of `Green/Stability.lean` (`stable_svar_bulk_vtx`).
* The bound at one grid time from the pathwise input on its good event and the envelope
  `‖G‖ ≤ η⁻¹` on the bad event (`OneLoop_expect_core`, `OneLoop_expect_bound`), and
  `gueGrid_expect_oneLoop`; the constant `Kstab3 d Λ κ (1 + 1/gapK κ)` does not depend on `n`
  or `L`, and is absorbed by the `N^ε` factor.

## What changes from `d = 2` (translation table; cited `OL:` = the RBM2D file)

`d : Sizes` is `sz : Sizes d`; `d.L n`, `d.W n`, `d.size n` are `sz.L n`, `sz.W n`, `sz.size n`
(`= (W L)^d`); `Idx L W` is `Idx d L W`; `Z2 L` is `Zd d L`; `BlockIndex L W` is `Vtx d L W`;
`Coord L W` is `CoordF d L W`; `gvar L W c` is `gvarF d L W g c` (the one-size law carries the
real parameter `g`, here `g = sz.lam n`:
`seqGvar sz ⟨n, c⟩ = gvarF d (sz.L n) (sz.W n) (sz.lam n) c` by `rfl`); `SB L` is `SB d L g`;
`Theta L ξ` is `Theta d L g ξ`; `spectralZ`, `spectralM` are `zt`, `mE`;
`gloop L W (blockMat M) z ⟨[true], [b]⟩` is `loopL d L W (blockMat d L W M) z ⟨[true], [b]⟩`;
`green H z` is `Gres H z true`; `Gsig` is `Gres`; `(W⁻¹)^2`, `W^2`, `(L W)^2`, `L^2` are
`(W⁻¹)^d`, `W^d`, `(L W)^d`, `L^d`; `etaT` is `RBM.Gauss.etaT`.

**Statement change of `gueGrid_expect_oneLoop` (paper-delta candidates `T2353a`, `T2353b`).**  The
`d = 2` constant `1 + cShortRow κ (1 + log L)` (the row sum of `Θ_{t m²}`, `OL:1133-1166`, built
on `xiRowBoundShort`, `xiMat`, `cShortRow`, `cProp5`) has the `log L` of the `d = 2` lattice sum;
at `d ≥ 3` it is the proved `Kstab3 d Λ κ` (`Green/Stability.lean`), uniform in `L`, valid for the
coupling window `0 < g ≤ Λ` of the proved pin 5s (`prop5Short_holds`).  Hence the added
hypotheses `3 ≤ d` and `0 < sz.lam n ≤ Λ` eventually (`(eq:WO)` gives it with `Λ = 𝔡⁻¹`), and the
`log L` absorption `OneLoop_log_absorb` (`OL:1606-1632`) and the `cShortRow`/`cProp5` lines
(`OL:1664-1668`, `1699-1711`) are deleted: the constant `8 Kstab3 (1 + 1/gapK) + 1` is absorbed by
`N^{ε/2}` directly.

The mixed-grid carrier (`OL:70-389`: `OneLoop_Pgue_eq_mixed`, `OneLoop_map_combined_eq_mixed`,
`OneLoop_map_slice_infinitePi`, `OneLoop_seqXmat_*`) is not re-ported: it is the public part of
`Grid.lean` (`GUEPhaseGrid_*`).  Compiled nonempty instances: namespace
`RBM.Univ.GUEPhase.OneLoopInst` (last section).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.GaussianProduct
  RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### The one-time law of grid step `k` -/

/-- The real-coordinate combination read by grid step `k`: `a ω₀ + b ∑_{i=1}^k ω_i`
(`OL:393`). -/
def olComb (a b : ℝ) (k : ℕ) (ω : PathΩ sz) : Sizes.SeqΩ sz :=
  a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i

theorem olComb_measurable (a b : ℝ) (k : ℕ) : Measurable (olComb sz a b k) := by
  have h1 : Measurable (fun ω : PathΩ sz => ω 0) := measurable_pi_apply 0
  have h2 : Measurable (fun ω : PathΩ sz => ∑ i ∈ Finset.Icc 1 k, ω i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (h1.const_smul a).add (h2.const_smul b)

/-- The coordinate variances of step `k`: `a² seqGvar_c + k b² gueUnitVar_c` (`OL:404`). -/
def olVar (a b : ℝ) (k : ℕ) : Sizes.SeqCoord sz → ℝ≥0 := fun c =>
  NNReal.mk (a ^ 2) (sq_nonneg a) * Sizes.seqGvar sz c
    + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * gueUnitVar sz c)

/-- **The one-time law of step `k`** (the D1 coordinate description): the combination has the
product Gaussian law with variances `olVar` (`OL:410`). -/
theorem ol_map_comb (a b : ℝ) (k : ℕ) :
    (Pgue sz).map (olComb sz a b k)
      = Measure.infinitePi (fun c : Sizes.SeqCoord sz => gaussianReal 0 (olVar sz a b k c)) := by
  rw [GUEPhaseGrid_Pgue_eq_mixed]
  exact GUEPhaseGrid_map_combined_eq_mixed (Sizes.seqGvar sz) (gueUnitVar sz) a b k

/-- The size-`n` slice of the combination has the product Gaussian law `GaussianProduct.law`
(`OL:417`). -/
theorem ol_map_comb_slice (a b : ℝ) (k n : ℕ) :
    (Pgue sz).map (fun ω => Sizes.slice sz n (olComb sz a b k ω))
      = GaussianProduct.law (fun c : CoordF d (sz.L n) (sz.W n) => olVar sz a b k ⟨n, c⟩) := by
  have hm : Measurable (Sizes.slice sz n) := Sizes.measurable_slice sz n
  rw [show (fun ω => Sizes.slice sz n (olComb sz a b k ω)) = Sizes.slice sz n ∘ olComb sz a b k
      from rfl,
    ← Measure.map_map hm (olComb_measurable sz a b k), ol_map_comb]
  exact GUEPhaseGrid_map_slice_infinitePi (sz := sz) (olVar sz a b k) n

/-- `gueH` at step `k` is `Xmat` of the size-`n` slice of the combination (`OL:426`). -/
theorem ol_gueH_eq (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    gueH sz t1 t0 K n k ω
      = Xmat d (sz.L n) (sz.W n) (Sizes.slice sz n (olComb sz (Real.sqrt (t1 n))
          (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ))) k ω)) := by
  change _ = Sizes.seqXmat sz n _
  unfold gueH olComb
  rw [GUEPhaseGrid_seqXmat_add, GUEPhaseGrid_seqXmat_smul, GUEPhaseGrid_seqXmat_smul,
    GUEPhaseGrid_seqXmat_sum, GUEPhaseGrid_real_smul_matrix, GUEPhaseGrid_real_smul_matrix]

/-! ## Fixed size: contraction of the step-`k` coordinate variances

`OneLoop_sum_orderedPairs_from_upper` is a copy of the private `contraction_sum_orderedPairs_from_upper`
(`Hierarchy/ContractionBasic.lean:321`; `OL:446`). -/

section OrderedPairs

/-- An upper-triangular sum, with its transposed term, plus the diagonal is the full ordered-pair
sum.  The key is injective, so its order chooses exactly one orientation of every distinct pair. -/
private theorem OneLoop_sum_orderedPairs_from_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (key : ι → ℕ) (hkey : Function.Injective key)
    (S : ι → ι → ℂ) (hS : ∀ i j, S i j = S j i)
    (f : ι → ι → ℂ) :
    ∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0) =
      ∑ i : ι, ∑ j : ι, S i j * f i j := by
  classical
  have point (i j : ι) : S i j * f i j =
      (if key i < key j then S i j * f i j else 0) +
      (if i = j then S i i * f i i else 0) +
      (if key j < key i then S i j * f i j else 0) := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
    · have hij : i = j := hkey h
      subst j
      simp
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
  have hswap :
      (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) =
      (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hS]
  calc
    (∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0)) =
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) := by
          simp_rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : key i < key j
          · have hne : i ≠ j := by
              intro he
              subst j
              exact (lt_irrefl _) hij
            simp [hij, hne, mul_add]
          · simp [hij]
    _ = (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
          rw [hswap]
    _ = ∑ i : ι, ∑ j : ι, S i j * f i j := by
          symm
          calc
            (∑ i : ι, ∑ j : ι, S i j * f i j) =
                ∑ i : ι, ∑ j : ι,
                  ((if key i < key j then S i j * f i j else 0) +
                   (if i = j then S i i * f i i else 0) +
                   (if key j < key i then S i j * f i j else 0)) := by
                    refine Finset.sum_congr rfl fun i _ =>
                      Finset.sum_congr rfl fun j _ => point i j
            _ = _ := by simp only [Finset.sum_add_distrib]

end OrderedPairs

section GUEContraction

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- **The unit-GUE coordinate contraction** on the physical lattice (`OL:521`):
`∑_c w_c tr(A X_c C X_c) = tr A · tr C`, `w_c = 1` on the diagonal and `1/2` off it. -/
private theorem OneLoop_sum_gue_fine (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c : CoordF d L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c) =
      Matrix.trace A * Matrix.trace C := by
  classical
  have splitCoord (f : CoordF d L W → ℂ) :
      ∑ c : CoordF d L W, f c = ∑ i : Idx d L W, ∑ j : Idx d L W, ∑ b : Bool, f (i, j, b) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_prod_type (fun jb : Idx d L W × Bool => f (i, jb))
  rw [splitCoord]
  have hpair : ∀ i j : Idx d L W, ∑ b : Bool,
      (if (i, j, b).1 = (i, j, b).2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (A * coordinateMatrix d L W (i, j, b) * C *
          coordinateMatrix d L W (i, j, b)) =
      (if idxKey d L W i < idxKey d L W j then (fun _ _ : Idx d L W => (1 : ℂ)) i j *
          ((fun i j : Idx d L W => A i i * C j j) i j + (fun i j : Idx d L W => A i i * C j j) j i)
        else if i = j then (fun _ _ : Idx d L W => (1 : ℂ)) i i *
          (fun i j : Idx d L W => A i i * C j j) i i else 0) := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
    · have hne : i ≠ j := fun he => by subst he; exact lt_irrefl _ h
      simp only [h, ite_true, Fintype.sum_bool, hne, ite_false]
      rw [trace_coordinate_real d L W A C h, trace_coordinate_imag d L W A C h]
      ring
    · subst h
      simp only [lt_irrefl, ite_false, ite_true, Fintype.sum_bool]
      rw [coordinateMatrix_diag_imag_zero]
      simp [trace_coordinate_diag d L W A C i]
    · have hne : i ≠ j := fun he => by subst he; exact lt_irrefl _ h
      have hrev : ¬ idxKey d L W i < idxKey d L W j := not_lt_of_ge (le_of_lt h)
      simp [hrev, hne, coordinateMatrix_lower_zero d L W h]
  simp_rw [hpair]
  rw [OneLoop_sum_orderedPairs_from_upper (idxKey d L W) (idxKey_injective d L W)
    (fun _ _ => (1 : ℂ)) (fun _ _ => rfl) (fun i j => A i i * C j j)]
  simp only [one_mul, Matrix.trace, Matrix.diag, Finset.sum_mul_sum]

private theorem OneLoop_trace_blockRelabel (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix.trace (blockRelabel d L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, blockRelabel]
  exact (Equiv.sum_comp (splitEquiv d L W).symm (fun i => M i i))

private theorem OneLoop_blockRelabel_mul (M N : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockRelabel d L W (M * N) = blockRelabel d L W M * blockRelabel d L W N :=
  (Matrix.submatrix_mul_equiv M N (splitEquiv d L W).symm (splitEquiv d L W).symm
    (splitEquiv d L W).symm).symm

private theorem OneLoop_trace_coordinateBlock_pair
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) (γ : CoordF d L W) :
    Matrix.trace (A * coordinateBlock d L W γ * C * coordinateBlock d L W γ) =
    Matrix.trace (A.submatrix (split d L W) (split d L W) * coordinateMatrix d L W γ *
      C.submatrix (split d L W) (split d L W) * coordinateMatrix d L W γ) := by
  let P := A.submatrix (split d L W) (split d L W)
  let Q := C.submatrix (split d L W) (split d L W)
  have hA : blockRelabel d L W P = A := blockRelabel_submatrix_split d L W A
  have hC : blockRelabel d L W Q = C := blockRelabel_submatrix_split d L W C
  change Matrix.trace (A * blockRelabel d L W (coordinateMatrix d L W γ) *
    C * blockRelabel d L W (coordinateMatrix d L W γ)) =
    Matrix.trace (P * coordinateMatrix d L W γ * Q * coordinateMatrix d L W γ)
  rw [← hA, ← hC, ← OneLoop_blockRelabel_mul d L W, ← OneLoop_blockRelabel_mul d L W,
    ← OneLoop_blockRelabel_mul d L W]
  exact OneLoop_trace_blockRelabel d L W _

/-- The unit-GUE coordinate contraction in block coordinates (`OL:585`). -/
private theorem OneLoop_sum_gue_block (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (A * coordinateBlock d L W c * C * coordinateBlock d L W c) =
      Matrix.trace A * Matrix.trace C := by
  simp_rw [OneLoop_trace_coordinateBlock_pair d L W]
  rw [OneLoop_sum_gue_fine d L W]
  have h1 : Matrix.trace (A.submatrix (split d L W) (split d L W)) = Matrix.trace A := by
    rw [← OneLoop_trace_blockRelabel d L W, blockRelabel_submatrix_split d L W A]
  have h2 : Matrix.trace (C.submatrix (split d L W) (split d L W)) = Matrix.trace C := by
    rw [← OneLoop_trace_blockRelabel d L W, blockRelabel_submatrix_split d L W C]
  rw [h1, h2]

end GUEContraction

section FixedSize

open scoped Matrix.Norms.L2Operator

variable (d L W : ℕ) [NeZero L] [NeZero W]

private theorem OneLoop_sub_mul_green {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Gres H z true = 1 := by
  simp only [Gres, ↓reduceIte]
  exact Ring.mul_inverse_cancel _ (isUnit_sub_smul_of_isHermitian hH hz)

private theorem OneLoop_gloop_one (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (b : Zd d L) :
    loopL d L W H z ⟨[true], [b]⟩ = Matrix.trace (Gres H z true * Eblk d L W b) := by
  simp [loopL]

/-- Resolvent identity at a single sample: `tr(H G E_a) = 1 + z tr(G E_a)`
(`OL:618`; RBM2D `Evolution/Step61.lean`, `step61_trace_HGE`). -/
private theorem OneLoop_trace_HGE (u : ℝ) (ω : Ω d L W) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) :
    Matrix.trace (HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true * Eblk d L W a) =
      1 + z * loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩ := by
  have h := OneLoop_sub_mul_green d L W (HflowBlock_isHermitian d L W u ω) hz
  have hHG : HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true =
      1 + z • Gres (HflowBlock d L W u ω) z true := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  rw [hHG, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.one_mul, trace_Eblk, OneLoop_gloop_one, smul_eq_mul]

private theorem OneLoop_norm_trace_mul3_le
    (A M C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ‖Matrix.trace (A * M * C)‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * (‖A‖ * ‖M‖ * ‖C‖) := by
  have h := norm_matrix_trace_le_card_mul (A * M * C)
  rw [card_BlockIndex] at h
  refine h.trans ?_
  gcongr
  exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)

/-- A Gaussian coordinate times a bounded measurable complex observable is integrable under any
product Gaussian law (`OL:640`). -/
private theorem OneLoop_integrable_coord_smul (v : CoordF d L W → ℝ≥0) (c : CoordF d L W)
    (g : Ω d L W → ℂ) (hgm : Measurable g) {C : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω : Ω d L W => ω c • g ω) (GaussianProduct.law v) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (GaussianProduct.law v) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((GaussianProduct.law v).map fun ω => ω c) := by
    have hmap : (GaussianProduct.law v).map (fun ω : Ω d L W => ω c) = gaussianReal 0 (v c) :=
      Measure.infinitePi_map_eval _ c
    rw [hmap]
    exact RBM.integrable_id_gaussianReal (var := v c)
  have hcoord : Integrable (fun ω : Ω d L W => ω c) (GaussianProduct.law v) :=
    (integrable_map_measure hg.aestronglyMeasurable hf).1 hg
  have h := hcoord.ofReal.bdd_mul hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  simpa [Complex.real_smul, mul_comm] using h

private theorem OneLoop_integrable_of_cont_bdd (v : CoordF d L W → ℝ≥0) {f : Ω d L W → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f (GaussianProduct.law v) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

private theorem OneLoop_green_norm_le (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (ω : Ω d L W) :
    ‖Gres (HflowBlock d L W u ω) z true‖ ≤ (|z.im|)⁻¹ :=
  norm_Gsig_le_inv_eta (HflowBlock_isHermitian d L W u ω) (abs_pos.mpr hz) le_rfl true

private theorem OneLoop_g_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) (c : CoordF d L W) :
    Continuous fun ω : Ω d L W => Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a) :=
  (continuous_matrixTrace d L W).comp
    ((continuous_const.mul (continuous_green_HflowBlock_sample d L W u hz)).mul continuous_const)

private theorem OneLoop_g'_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L)
    (c : CoordF d L W) :
    Continuous fun ω : Ω d L W => Matrix.trace
      (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a) := by
  have hGc := continuous_green_HflowBlock_sample d L W u hz
  exact (continuous_matrixTrace d L W).comp
    ((continuous_const.mul (((hGc.mul continuous_const).mul hGc).neg)).mul continuous_const)

private theorem OneLoop_g_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) (c : CoordF d L W) :
    ∃ C : ℝ, ∀ ω : Ω d L W, ‖Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ d : ℕ) : ℝ) *
    (‖coordinateBlock d L W c‖ * (|z.im|)⁻¹ * ‖Eblk d L W a‖), fun ω => ?_⟩
  refine (OneLoop_norm_trace_mul3_le d L W _ _ _).trans ?_
  gcongr
  exact OneLoop_green_norm_le d L W u hz ω

private theorem OneLoop_g'_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L)
    (c : CoordF d L W) :
    ∃ C : ℝ, ∀ ω : Ω d L W, ‖Matrix.trace
      (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a)‖ ≤ C := by
  refine ⟨(((L * W) ^ d : ℕ) : ℝ) *
    (‖coordinateBlock d L W c‖ * ((|z.im|)⁻¹ * ‖Real.sqrt u • coordinateBlock d L W c‖ *
      (|z.im|)⁻¹) * ‖Eblk d L W a‖), fun ω => ?_⟩
  refine (OneLoop_norm_trace_mul3_le d L W _ _ _).trans ?_
  gcongr
  rw [norm_neg]
  refine (norm_mul_le _ _).trans ?_
  gcongr
  · exact (norm_mul_le _ _).trans (by gcongr; exact OneLoop_green_norm_le d L W u hz ω)
  · exact OneLoop_green_norm_le d L W u hz ω

/-- One-coordinate Stein identity for `tr(B_c G E_a)` under an arbitrary product Gaussian law
(`OL:706`). -/
private theorem OneLoop_stein_coord (v : CoordF d L W → ℝ≥0) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (a : Zd d L) (c : CoordF d L W) :
    ∫ ω : Ω d L W, ω c • Matrix.trace
        (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a)
        ∂(GaussianProduct.law v) =
      (v c : ℝ) • ∫ ω : Ω d L W, Matrix.trace
        (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
          (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
          Eblk d L W a) ∂(GaussianProduct.law v) := by
  set B := coordinateBlock d L W c with hB
  set E := Eblk d L W a with hE
  let g : Ω d L W → ℂ := fun ω => Matrix.trace (B * Gres (HflowBlock d L W u ω) z true * E)
  let g' : Ω d L W → ℂ := fun ω => Matrix.trace (B * (-(Gres (HflowBlock d L W u ω) z true *
    (Real.sqrt u • B) * Gres (HflowBlock d L W u ω) z true)) * E)
  have hgc : Continuous g := OneLoop_g_cont d L W u hz a c
  have hg'c : Continuous g' := OneLoop_g'_cont d L W u hz a c
  have hderiv : ∀ ω : Ω d L W,
      HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c) := by
    intro ω
    set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h1 := hasDerivAt_green_HflowBlock_update d L W u ω c hz
    have h2 := ((hasDerivAt_const (ω c) B).mul h1).mul_const E
    have h3 := T.hasFDerivAt.comp_hasDerivAt (ω c) h2
    refine h3.congr_deriv ?_
    simp only [hT, g', zero_mul, zero_add, hB]
  have hgb : ∃ C : ℝ, ∀ ω : Ω d L W, ‖g ω‖ ≤ C := OneLoop_g_bdd d L W u hz a c
  have hg'b : ∃ C : ℝ, ∀ ω : Ω d L W, ‖g' ω‖ ≤ C := OneLoop_g'_bdd d L W u hz a c
  exact GaussianProduct.stein v c g g' hgc hg'c hderiv hgb hg'b

private theorem OneLoop_HflowBlock_eq (u : ℝ) (ω : Ω d L W) :
    HflowBlock d L W u ω =
      (Real.sqrt u : ℂ) • ∑ c : CoordF d L W, ω c • coordinateBlock d L W c := by
  rw [← Xblock_eq_sum_coordinates]
  ext i j
  simp [HflowBlock, Hflow, blockMat, Matrix.submatrix_apply]

end FixedSize

section FixedSize2

open scoped Matrix.Norms.L2Operator

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem OneLoop_Eblk_mul_Eblk (a b : Zd d L) :
    Eblk d L W a * Eblk d L W b =
      if a = b then (((W : ℂ) ^ d)⁻¹) • Eblk d L W a else 0 := by
  unfold Eblk
  rw [diagonal_mul_diagonal]
  ext p q
  by_cases hab : a = b
  · subst hab
    simp only [ite_true, diagonal_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp_all
  · simp only [hab, ite_false, diagonal_apply, Matrix.zero_apply]
    split_ifs <;> simp_all

omit [NeZero W] in
/-- The blocks partition the identity with factor `W^{-d}` (`OL`: `sum_Eblk`, RBM2D `Defs/Model.lean:83`;
copy of the private `contraction_sum_Eblk`, `Hierarchy/ContractionBasic.lean:755`). -/
private theorem OneLoop_sum_Eblk :
    ∑ a, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- **The mixed-profile contraction**: with coordinate variances `v_c = t₁ gvar_c + c₀ w_c`
(`w_c = 1` on the diagonal, `1/2` off it), the Stein sum collapses to the block profile
`Ŝ_{pa} = t₁ S^{(B)}_{pa} + c₀ W^d`:
`∑_c (√u v_c) tr(B_c (-(G √u B_c G)) E_a) = -u ∑_p Ŝ_{pa} tr(G E_p) tr(G E_a)`.
The `t₁` part is `sum_coordinateBlock_trace_pair`; the `c₀` part is the unit-GUE contraction
`OneLoop_sum_gue_block` (`tr A tr C`, with `tr G = W^d ∑_p tr(G E_p)`) (`OL:759`). -/
private theorem OneLoop_contraction (v : CoordF d L W → ℝ≥0) {t1 c0 : ℝ}
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W g c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (u : ℝ) (hu : 0 ≤ u) (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) :
    ∑ c : CoordF d L W, ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock d L W c *
        (-(G * (Real.sqrt u • coordinateBlock d L W c) * G)) * Eblk d L W a) =
    -(u : ℂ) * ∑ p : Zd d L, ((t1 : ℂ) * SB d L g p a + ((c0 * (W : ℝ) ^ d : ℝ) : ℂ)) *
      (Matrix.trace (G * Eblk d L W p) * Matrix.trace (G * Eblk d L W a)) := by
  have hterm : ∀ c : CoordF d L W,
      ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock d L W c *
        (-(G * (Real.sqrt u • coordinateBlock d L W c) * G)) * Eblk d L W a) =
      -(u : ℂ) * (((v c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock d L W c * (G * Eblk d L W a) *
          coordinateBlock d L W c)) := by
    intro c
    set B := coordinateBlock d L W c
    have h1 : B * (-(G * (Real.sqrt u • B) * G)) * Eblk d L W a =
        -(Real.sqrt u • (B * (G * B * (G * Eblk d L W a)))) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
    have h2 : Matrix.trace (B * (G * B * (G * Eblk d L W a))) =
        Matrix.trace (G * B * (G * Eblk d L W a) * B) :=
      Matrix.trace_mul_comm _ _
    rw [h1, Matrix.trace_neg, Matrix.trace_smul, h2, Complex.real_smul]
    have h3 : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
    linear_combination
      (-(((v c : ℝ) : ℂ) * Matrix.trace (G * B * (G * Eblk d L W a) * B))) * h3
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  have hvC : ∀ c : CoordF d L W, ((v c : ℝ) : ℂ) =
      (t1 : ℂ) * ((gvarF d L W g c : ℝ) : ℂ) +
        (c0 : ℂ) * (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) := by
    intro c
    rw [hv c]
    split_ifs <;> push_cast <;> ring
  have hsplit : ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock d L W c * (G * Eblk d L W a) *
          coordinateBlock d L W c) =
      (t1 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        Matrix.trace (G * coordinateBlock d L W c * (G * Eblk d L W a) *
          coordinateBlock d L W c) +
      (c0 : ℂ) * ∑ c : CoordF d L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (G * coordinateBlock d L W c * (G * Eblk d L W a) *
          coordinateBlock d L W c) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hvC c]
    ring
  rw [hsplit, sum_coordinateBlock_trace_pair d L W g G (G * Eblk d L W a),
    OneLoop_sum_gue_block d L W G (G * Eblk d L W a)]
  have hq : ∀ q : Zd d L, Matrix.trace (G * Eblk d L W a * Eblk d L W q) =
      if a = q then (W : ℂ)⁻¹ ^ d * Matrix.trace (G * Eblk d L W a) else 0 := by
    intro q
    rw [Matrix.mul_assoc, OneLoop_Eblk_mul_Eblk d L W]
    split_ifs
    · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, inv_pow]
    · simp
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have htr : Matrix.trace G = (W : ℂ) ^ d * ∑ p : Zd d L, Matrix.trace (G * Eblk d L W p) := by
    have h := congrArg (fun M => Matrix.trace (G * M)) (OneLoop_sum_Eblk d L W)
    simp only [Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.mul_one, smul_eq_mul] at h
    rw [h]
    field_simp
  simp_rw [hq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [htr]
  have e1 : (t1 : ℂ) * ((W : ℂ) ^ d * ∑ x : Zd d L, Matrix.trace (G * Eblk d L W x) *
      SB d L g x a * ((W : ℂ)⁻¹ ^ d * Matrix.trace (G * Eblk d L W a))) =
      ∑ x : Zd d L, (t1 : ℂ) * ((W : ℂ) ^ d * (Matrix.trace (G * Eblk d L W x) * SB d L g x a *
        ((W : ℂ)⁻¹ ^ d * Matrix.trace (G * Eblk d L W a)))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  have e2 : (c0 : ℂ) * (((W : ℂ) ^ d * ∑ p : Zd d L, Matrix.trace (G * Eblk d L W p)) *
      Matrix.trace (G * Eblk d L W a)) =
      ∑ p : Zd d L, (c0 : ℂ) * ((W : ℂ) ^ d * Matrix.trace (G * Eblk d L W p) *
        Matrix.trace (G * Eblk d L W a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  have hlhs : ∀ p : Zd d L, (t1 : ℂ) * ((W : ℂ) ^ d * (Matrix.trace (G * Eblk d L W p) *
      SB d L g p a * ((W : ℂ)⁻¹ ^ d * Matrix.trace (G * Eblk d L W a)))) +
      (c0 : ℂ) * ((W : ℂ) ^ d * Matrix.trace (G * Eblk d L W p) *
        Matrix.trace (G * Eblk d L W a)) =
      ((t1 : ℂ) * SB d L g p a + ((c0 * (W : ℝ) ^ d : ℝ) : ℂ)) *
        (Matrix.trace (G * Eblk d L W p) * Matrix.trace (G * Eblk d L W a)) := by
    intro p
    have hWd : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ hW
    push_cast
    rw [inv_pow]
    field_simp
  rw [e1, e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => hlhs p

end FixedSize2

section FixedSize3

open scoped Matrix.Norms.L2Operator

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

private theorem OneLoop_gloop_bdd (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Zd d L)
    (ω : Ω d L W) :
    ‖loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * ((|z.im|)⁻¹ * (((W : ℝ) ^ d)⁻¹)) := by
  have h := norm_gloop_le_crude d L W (HflowBlock_isHermitian d L W u ω)
    (abs_pos.mpr hz) le_rfl ⟨[true], [b]⟩ (by simp [Loop.LoopIdx.WF])
  simpa using h

private theorem OneLoop_gloop_cont (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (b : Zd d L) :
    Continuous fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩ :=
  continuous_gloop_HflowBlock_sample d L W u hz _ (by simp [Loop.LoopIdx.WF])

private theorem OneLoop_integrable_gloop (v : CoordF d L W → ℝ≥0) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (b : Zd d L) :
    Integrable (fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩)
      (GaussianProduct.law v) :=
  OneLoop_integrable_of_cont_bdd d L W v (OneLoop_gloop_cont d L W u hz b)
    (OneLoop_gloop_bdd d L W u hz b)

private theorem OneLoop_integrable_gloop_mul (v : CoordF d L W → ℝ≥0) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (b a : Zd d L) :
    Integrable (fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z ⟨[true], [b]⟩ *
      loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩) (GaussianProduct.law v) := by
  refine OneLoop_integrable_of_cont_bdd d L W v
    ((OneLoop_gloop_cont d L W u hz b).mul (OneLoop_gloop_cont d L W u hz a))
    (C := ((((L * W) ^ d : ℕ) : ℝ) * ((|z.im|)⁻¹ * (((W : ℝ) ^ d)⁻¹))) *
      ((((L * W) ^ d : ℕ) : ℝ) * ((|z.im|)⁻¹ * (((W : ℝ) ^ d)⁻¹)))) (fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul (OneLoop_gloop_bdd d L W u hz b ω) (OneLoop_gloop_bdd d L W u hz a ω)
    (norm_nonneg _) ((norm_nonneg _).trans (OneLoop_gloop_bdd d L W u hz b ω))

/-- **Stein step** under the product Gaussian `law v` of the step-`k` coordinate variances:
`𝔼 tr(H G E_a) = -u ∑_p Ŝ_{pa} 𝔼[g_p g_a]`, `g_b = tr(G E_b)`, `Ŝ = t₁ S^{(B)} + c₀ W^d`
(`OL:888`). -/
private theorem OneLoop_stein (v : CoordF d L W → ℝ≥0) {t1 c0 : ℝ}
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W g c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (u : ℝ) (hu : 0 ≤ u) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) :
    ∫ ω : Ω d L W, Matrix.trace (HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true *
        Eblk d L W a) ∂(GaussianProduct.law v) =
      -(u : ℂ) * ∑ p : Zd d L, ((t1 : ℂ) * SB d L g p a + ((c0 * (W : ℝ) ^ d : ℝ) : ℂ)) *
        ∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) z ⟨[true], [p]⟩ *
          loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩ ∂(GaussianProduct.law v) := by
  classical
  have hI1 : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => ω c • Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a))
      (GaussianProduct.law v) := by
    intro c
    obtain ⟨C, hC⟩ := OneLoop_g_bdd d L W u hz a c
    exact OneLoop_integrable_coord_smul d L W v c _ (OneLoop_g_cont d L W u hz a c).measurable hC
  have hI2 : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => Matrix.trace
      (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a)) (GaussianProduct.law v) := by
    intro c
    obtain ⟨C, hC⟩ := OneLoop_g'_bdd d L W u hz a c
    exact OneLoop_integrable_of_cont_bdd d L W v (OneLoop_g'_cont d L W u hz a c) hC
  have hexp : ∀ ω : Ω d L W, Matrix.trace (HflowBlock d L W u ω *
      Gres (HflowBlock d L W u ω) z true * Eblk d L W a) =
      ∑ c : CoordF d L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
        (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a)) := by
    intro ω
    generalize Gres (HflowBlock d L W u ω) z true = G
    rw [OneLoop_HflowBlock_eq d L W u ω]
    simp only [Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
      Complex.real_smul, smul_eq_mul, Finset.mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun c _ => (hI1 c).const_mul _)]
  have hstein : ∀ c : CoordF d L W, ∫ ω : Ω d L W, (Real.sqrt u : ℂ) * (ω c • Matrix.trace
      (coordinateBlock d L W c * Gres (HflowBlock d L W u ω) z true * Eblk d L W a))
        ∂(GaussianProduct.law v) =
      ∫ ω : Ω d L W, ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) * Matrix.trace
        (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
          (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
          Eblk d L W a) ∂(GaussianProduct.law v) := by
    intro c
    rw [integral_const_mul, OneLoop_stein_coord d L W v u hz a c, integral_const_mul,
      Complex.real_smul, mul_assoc]
  simp_rw [hstein]
  rw [← integral_finsetSum _ (fun c _ => (hI2 c).const_mul _)]
  have hpt : ∀ ω : Ω d L W, ∑ c : CoordF d L W, ((Real.sqrt u : ℂ) * ((v c : ℝ) : ℂ)) *
      Matrix.trace (coordinateBlock d L W c * (-(Gres (HflowBlock d L W u ω) z true *
        (Real.sqrt u • coordinateBlock d L W c) * Gres (HflowBlock d L W u ω) z true)) *
        Eblk d L W a) =
      -(u : ℂ) * ∑ p : Zd d L, ((t1 : ℂ) * SB d L g p a + ((c0 * (W : ℝ) ^ d : ℝ) : ℂ)) *
        (loopL d L W (HflowBlock d L W u ω) z ⟨[true], [p]⟩ *
        loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩) := by
    intro ω
    rw [OneLoop_contraction d L W g v hv u hu]
    simp only [OneLoop_gloop_one]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _
    (fun p _ => (OneLoop_integrable_gloop_mul d L W v u hz p a).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]

private theorem OneLoop_SB_symm (a b : Zd d L) : SB d L g b a = SB d L g a b :=
  congrFun (congrFun (SB_transpose d L g) a) b

omit [NeZero W] in
private theorem OneLoop_sum_SB_col (hL : 3 ≤ L) (a : Zd d L) :
    ∑ b : Zd d L, SB d L g b a = 1 := by
  simp_rw [OneLoop_SB_symm d L g a]
  exact sum_SB_row d L g hL a

omit [NeZero W] in
private theorem OneLoop_card_Zd : (Fintype.card (Zd d L) : ℕ) = L ^ d := by
  simp [Zd, ZMod.card]

/-- **The block identity before inversion** for the step-`k` law: with `x_b = 𝔼 g_b - m`,
`Z_b = g_b - m`, `Ŝ = t₁ S^{(B)} + c₀ W^d` (row sums `u = t₁ + L^d c₀ W^d`),
`x_a = m² ∑_b Ŝ_{ba} x_b + m ∑_b Ŝ_{ba} 𝔼[Z_b Z_a]` (`OL:961`). -/
private theorem OneLoop_selfcons (hL : 3 ≤ L) (v : CoordF d L W → ℝ≥0) {t1 c0 E u : ℝ}
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W g c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (hsum : t1 + (L : ℝ) ^ d * (c0 * (W : ℝ) ^ d) = u) (hE : |E| < 2) (hu1 : u < 1)
    (a : Zd d L) :
    (∫ ω : Ω d L W, loopL d L W (HflowBlock d L W 1 ω) (zt E u) ⟨[true], [a]⟩
        ∂(GaussianProduct.law v)) - mE E =
      mE E ^ 2 * ∑ b : Zd d L, ((t1 : ℂ) * SB d L g b a + ((c0 * (W : ℝ) ^ d : ℝ) : ℂ)) *
        ((∫ ω : Ω d L W, loopL d L W (HflowBlock d L W 1 ω) (zt E u) ⟨[true], [b]⟩
          ∂(GaussianProduct.law v)) - mE E) +
      mE E * ∑ b : Zd d L, ((t1 : ℂ) * SB d L g b a + ((c0 * (W : ℝ) ^ d : ℝ) : ℂ)) *
        ∫ ω : Ω d L W,
        (loopL d L W (HflowBlock d L W 1 ω) (zt E u) ⟨[true], [b]⟩ - mE E) *
          (loopL d L W (HflowBlock d L W 1 ω) (zt E u) ⟨[true], [a]⟩ - mE E)
          ∂(GaussianProduct.law v) := by
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE))
  set z := zt E u with hzdef
  set m := mE E with hm
  set Q := GaussianProduct.law v with hQ
  set Sh : Zd d L → ℂ := fun b => (t1 : ℂ) * SB d L g b a + ((c0 * (W : ℝ) ^ d : ℝ) : ℂ)
    with hSh
  set g' : Zd d L → Ω d L W → ℂ := fun b ω => loopL d L W (HflowBlock d L W 1 ω) z ⟨[true], [b]⟩
    with hg'
  have hgI : ∀ b, Integrable (g' b) Q := fun b => OneLoop_integrable_gloop d L W v 1 hz b
  have hgg : ∀ b, Integrable (fun ω => g' b ω * g' a ω) Q :=
    fun b => OneLoop_integrable_gloop_mul d L W v 1 hz b a
  -- the Stein identity, integrated resolvent identity
  have hres : ∫ ω : Ω d L W, Matrix.trace (HflowBlock d L W 1 ω *
      Gres (HflowBlock d L W 1 ω) z true * Eblk d L W a) ∂Q = 1 + z * ∫ ω, g' a ω ∂Q := by
    simp_rw [OneLoop_trace_HGE d L W 1 _ hz a]
    rw [integral_add (integrable_const _) ((hgI a).const_mul z), integral_const_mul,
      integral_const]
    simp
  have hst : 1 + z * ∫ ω, g' a ω ∂Q = -∑ p : Zd d L, Sh p * ∫ ω, g' p ω * g' a ω ∂Q := by
    have h := OneLoop_stein d L W g v hv 1 zero_le_one hz a
    rw [hres] at h
    rw [h]
    simp only [Complex.ofReal_one, neg_mul, one_mul]
    rfl
  -- `m z + u m² = -1`
  have hmz : m * z + (u : ℂ) * m ^ 2 = -1 := by
    have hq := spectralM_quadratic (E := E) hE.le
    simp only [hzdef, zt]
    linear_combination hq
  have hSum1 : ∑ b : Zd d L, Sh b = (u : ℂ) := by
    simp only [hSh, Finset.sum_add_distrib, ← Finset.mul_sum, OneLoop_sum_SB_col d L g hL a,
      Finset.sum_const, Finset.card_univ]
    rw [OneLoop_card_Zd d L, nsmul_eq_mul]
    rw [← hsum]
    push_cast
    ring
  change (∫ ω, g' a ω ∂Q) - m =
    m ^ 2 * ∑ b : Zd d L, Sh b * ((∫ ω, g' b ω ∂Q) - m) +
      m * ∑ b : Zd d L, Sh b * ∫ ω, (g' b ω - m) * (g' a ω - m) ∂Q
  -- centred product integrals
  have hZ : ∀ b, ∫ ω : Ω d L W, (g' b ω - m) * (g' a ω - m) ∂Q =
      (∫ ω, g' b ω * g' a ω ∂Q) - m * (∫ ω, g' b ω ∂Q) -
        m * (∫ ω, g' a ω ∂Q) + m ^ 2 := by
    intro b
    have i1 : Integrable (fun ω : Ω d L W => g' b ω * g' a ω) Q := hgg b
    have i2 : Integrable (fun ω : Ω d L W => m * g' b ω) Q := (hgI b).const_mul m
    have i3 : Integrable (fun ω : Ω d L W => m * g' a ω) Q := (hgI a).const_mul m
    have hfun : (fun ω : Ω d L W => (g' b ω - m) * (g' a ω - m)) =
        fun ω => g' b ω * g' a ω - m * g' b ω - m * g' a ω + m ^ 2 := by
      funext ω; ring
    have i12 : Integrable (fun ω : Ω d L W => g' b ω * g' a ω - m * g' b ω) Q := i1.sub i2
    have i123 : Integrable (fun ω : Ω d L W => g' b ω * g' a ω - m * g' b ω - m * g' a ω) Q :=
      i12.sub i3
    rw [hfun, integral_add i123 (integrable_const _), integral_sub i12 i3, integral_sub i1 i2,
      integral_const_mul, integral_const_mul, integral_const]
    simp
  simp_rw [hZ]
  set Ia := ∫ ω, g' a ω ∂Q with hIa
  have e1 : ∑ b : Zd d L, Sh b * ((∫ ω, g' b ω ∂Q) - m) =
      (∑ b : Zd d L, Sh b * ∫ ω, g' b ω ∂Q) - (u : ℂ) * m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hSum1]
  have e2 : ∑ b : Zd d L, Sh b * ((∫ ω, g' b ω * g' a ω ∂Q) -
      m * (∫ ω, g' b ω ∂Q) - m * Ia + m ^ 2) =
      (∑ b : Zd d L, Sh b * ∫ ω, g' b ω * g' a ω ∂Q) -
        m * (∑ b : Zd d L, Sh b * ∫ ω, g' b ω ∂Q) - (u : ℂ) * (m * Ia - m ^ 2) := by
    have hb : ∀ b : Zd d L, Sh b * ((∫ ω, g' b ω * g' a ω ∂Q) -
        m * (∫ ω, g' b ω ∂Q) - m * Ia + m ^ 2) =
        Sh b * (∫ ω, g' b ω * g' a ω ∂Q) -
          m * (Sh b * ∫ ω, g' b ω ∂Q) + Sh b * (m ^ 2 - m * Ia) :=
      fun b => by ring
    simp_rw [hb]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hSum1]
    ring
  rw [e1, e2]
  set T1 := ∑ b : Zd d L, Sh b * ∫ ω, g' b ω ∂Q
  set T2 := ∑ b : Zd d L, Sh b * ∫ ω, g' b ω * g' a ω ∂Q
  linear_combination (-m) * hst + Ia * hmz

end FixedSize3

/-! ## Deterministic inversion of `x = m² Ŝ x + y` in `max → max`

The `d = 2` solution `x = Θ_{t₁ m²} r` with the row sum `1 + cShortRow κ (1 + log L)`
(`OL:1112-1166`: `OneLoop_theta_solve`, `OneLoop_theta_row_sum`, built on `xiRowBoundShort`, `xiMat`,
`cShortRow`, `cProp5`) is replaced by the proved `d ≥ 3` stability `Green.Stable (svar d L W g)`
with the constant `Green.Kstab3 d Λ κ` of `Green/Stability.lean` (`stable_svar_bulk_vtx`; the
row sums of `Θ_{t m²}` are bounded through the proved pin 5s and the exponential lattice sum,
uniformly in `L`).  No `log L` occurs. -/

section Stability

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

private theorem OneLoop_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < Loop.gapK κ := by
  unfold Loop.gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

/-- The bulk gap `c_κ ≤ |1 - t m²|` for `t ≥ 0`, `|E| ≤ 2 - κ` (`OL:1084`): the merged
`Loop.gapK_le_norm` at `s = +` (`mSigma E true = mE E`). -/
private theorem OneLoop_gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht0 : 0 ≤ t) : Loop.gapK κ ≤ ‖1 - (t : ℂ) * mE E ^ 2‖ := by
  have h := Loop.gapK_le_norm hκ hE ht0 true
  simpa [mSigma, sq] using h

omit [NeZero L] [NeZero W] in
/-- `S_{(a,α),(b,β)} = W^{-d} S^(B)_{ab}` entrywise in `ℂ` (copy of the private
`stability_svar_cast`, `Green/Stability.lean:70`). -/
private theorem OneLoop_svar_cast (a b : Zd d L) (α β : Fin (W ^ d)) :
    ((svar d L W g (a, α) (b, β) : ℝ) : ℂ) = ((W : ℂ) ^ d)⁻¹ * SB d L g a b := by
  rw [SB_eq_map_SBR]
  simp [RBM.Gauss.svar]

/-- `Stable` of the block-product profile `svar` read on functions of the block label only: if
`‖x_a - ξ ∑_b S^(B)_{ab} x_b‖ ≤ B` for all `a` then `‖x_a‖ ≤ K B`.  (`v (a, α) = x_a`; the
fibre sum `∑_β W^{-d} = 1`; the lift of `stable_svar_vtx`, `Green/Stability.lean:80`.) -/
private theorem OneLoop_stable_SB {ξ : ℂ} {K : ℝ} (hK : Green.Stable (svar d L W g) ξ K)
    {x : Zd d L → ℂ} {B : ℝ}
    (hB : ∀ a, ‖x a - ξ * ∑ b, SB d L g a b * x b‖ ≤ B) (a : Zd d L) :
    ‖x a‖ ≤ K * B := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have : NeZero (W ^ d) := ⟨pow_ne_zero _ (NeZero.ne W)⟩
  have hS : ∀ (a : Zd d L) (α : Fin (W ^ d)),
      ∑ k : Vtx d L W, (svar d L W g (a, α) k : ℂ) * x k.1 = ∑ b, SB d L g a b * x b := by
    intro a α
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [OneLoop_svar_cast d L W g, ← Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hWd : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ hW
    push_cast
    field_simp
  have h := hK (fun i => x i.1) B (fun i => by simpa only [hS i.1 i.2] using hB i.1) (a, 0)
  simpa using h

/-- **Stability of `1 - m² Ŝ` in `max → max`** (`OL:1172`): `Ŝ = t₁ S^{(B)} + σ J` on `Z_L^d` with
row sums `u = t₁ + L^d σ < 1`.  The average is recovered through `1 - u m²`,
`|1 - u m²| ≥ c_κ = gapK κ`; the rest is `1 - t₁ m² S^{(B)}`, stable with the constant `K`
(`Green.Kstab3 d Λ κ` by `stable_svar_bulk_vtx`; `d = 2`: `1 + cShortRow κ (1 + log L)`). -/
private theorem OneLoop_stable (hL : 3 ≤ L) {κ E t1 σ u K : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ)
    (hu : t1 + (L : ℝ) ^ d * σ = u) (hu1 : u < 1)
    (hK : Green.Stable (svar d L W g) ((t1 : ℂ) * mE E ^ 2) K) {x y : Zd d L → ℂ}
    (h : ∀ a, x a = mE E ^ 2 * ∑ b, ((t1 : ℂ) * SB d L g b a + (σ : ℂ)) * x b + y a)
    {B : ℝ} (hB : ∀ a, ‖y a‖ ≤ B) (a : Zd d L) :
    ‖x a‖ ≤ K * (1 + 1 / Loop.gapK κ) * B := by
  classical
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  set m := mE E with hm
  have hm1 : ‖m‖ = 1 := norm_spectralM hE2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a)
  have hgpos : 0 < Loop.gapK κ := OneLoop_gapK_pos hκ hκ2
  set gk := Loop.gapK κ with hgk
  have hLσ : (L : ℝ) ^ d * σ ≤ 1 := by linarith
  have hu0 : 0 ≤ u := by rw [← hu]; positivity
  have hc : (Fintype.card (Zd d L) : ℕ) = L ^ d := OneLoop_card_Zd d L
  set S := ∑ b, x b with hS
  -- the row sums of the profile
  have hrow : ∀ b : Zd d L, ∑ a : Zd d L, ((t1 : ℂ) * SB d L g b a + (σ : ℂ)) = (u : ℂ) := by
    intro b
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_SB_row d L g hL b, Finset.sum_const,
      Finset.card_univ, hc, nsmul_eq_mul]
    rw [← hu]
    push_cast
    ring
  -- the average: `(1 - u m²) ∑ x = ∑ y`
  have hsum : (1 - (u : ℂ) * m ^ 2) * S = ∑ a, y a := by
    have e1 : ∑ a : Zd d L, ∑ b : Zd d L, ((t1 : ℂ) * SB d L g b a + (σ : ℂ)) * x b =
        (u : ℂ) * S := by
      rw [Finset.sum_comm, hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, hrow b]
    have h1 : S = m ^ 2 * ((u : ℂ) * S) + ∑ a, y a := by
      conv_lhs => rw [hS, Finset.sum_congr rfl fun a _ => h a]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1]
    linear_combination h1
  have hden : gk ≤ ‖1 - (u : ℂ) * m ^ 2‖ := OneLoop_gapK_le_norm hκ hE hu0
  have hY : ‖∑ a, y a‖ ≤ (L : ℝ) ^ d * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖y a‖ ≤ ∑ _a : Zd d L, B := Finset.sum_le_sum fun a _ => hB a
      _ = (L : ℝ) ^ d * B := by
        rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]; push_cast; ring
  have hSle : ‖S‖ ≤ (L : ℝ) ^ d * B / gk := by
    rw [le_div_iff₀ hgpos]
    calc ‖S‖ * gk ≤ ‖S‖ * ‖1 - (u : ℂ) * m ^ 2‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = ‖∑ a, y a‖ := by rw [← hsum, norm_mul, mul_comm]
      _ ≤ (L : ℝ) ^ d * B := hY
  -- the remainder `r = y + m² σ ∑ x`
  set r : Zd d L → ℂ := fun a => y a + m ^ 2 * (σ : ℂ) * S with hr
  have hrle : ∀ a, ‖r a‖ ≤ (1 + 1 / gk) * B := by
    intro a
    calc ‖r a‖ ≤ ‖y a‖ + ‖m ^ 2 * (σ : ℂ) * S‖ := norm_add_le _ _
      _ ≤ B + σ * ((L : ℝ) ^ d * B / gk) := by
          gcongr
          · exact hB a
          · rw [norm_mul, norm_mul, norm_pow, hm1, one_pow, one_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hσ]
            exact mul_le_mul_of_nonneg_left hSle hσ
      _ = B + ((L : ℝ) ^ d * σ) * B / gk := by ring
      _ ≤ B + 1 * B / gk := by gcongr
      _ = (1 + 1 / gk) * B := by ring
  -- `x - t₁ m² S^{(B)} x = r`
  have hxr : ∀ a, ‖x a - ((t1 : ℂ) * m ^ 2) * ∑ b, SB d L g a b * x b‖ ≤ (1 + 1 / gk) * B := by
    intro a
    have h2 : ∑ b : Zd d L, ((t1 : ℂ) * SB d L g b a + (σ : ℂ)) * x b =
        (t1 : ℂ) * ∑ b : Zd d L, SB d L g a b * x b + (σ : ℂ) * S := by
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hS,
        OneLoop_SB_symm d L g a]
    have h3 : x a - ((t1 : ℂ) * m ^ 2) * ∑ b, SB d L g a b * x b = r a := by
      rw [h a, h2]
      simp only [hr]
      ring
    rw [h3]
    exact hrle a
  have := OneLoop_stable_SB d L W g hK hxr a
  calc ‖x a‖ ≤ K * ((1 + 1 / gk) * B) := this
    _ = K * (1 + 1 / gk) * B := by ring

end Stability

/-! ## From the pathwise input to the expectation bound at one grid time -/

section Core

open scoped Matrix.Norms.L2Operator

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- **The core of the bound at one grid time** (`OL:1275`): given a measurable exceptional set
`T`, `μ.real T ≤ δ`, off which every `1`-loop is `≤ ρ Λu`, and a global envelope `Env` with
`δ Env² ≤ 4 Λu²`, then
`‖𝔼 g_a - m‖ ≤ Kstab3 d Λ κ (1 + 1/c_κ)(ρ² + 4) Λu²` (`d = 2`:
`(1 + cShortRow κ (1 + log L))(1 + 1/c_κ)`), for the coupling `0 < g ≤ Λ` and `3 ≤ d`. -/
private theorem OneLoop_expect_core (hd : 3 ≤ d) (hL : 3 ≤ L) {Λ κ E t1 c0 u : ℝ}
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht1 : 0 ≤ t1) (hc0 : 0 ≤ c0)
    (hsum : t1 + (L : ℝ) ^ d * (c0 * (W : ℝ) ^ d) = u) (hu1 : u < 1)
    (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W g c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]
    (φ : Ω' → Ω d L W) (hφ : Measurable φ) (hmap : μ.map φ = GaussianProduct.law v)
    {Λu ρ Env δ : ℝ} (T : Set Ω') (hT : MeasurableSet T)
    (hEnv : ∀ (b : Zd d L) (ω' : Ω d L W),
      ‖loopL d L W (HflowBlock d L W 1 ω') (zt E u) ⟨[true], [b]⟩ - mE E‖ ≤ Env)
    (hTδ : μ.real T ≤ δ) (hbad : δ * Env ^ 2 ≤ 4 * Λu ^ 2)
    (hgood : ∀ ω ∉ T, ∀ b : Zd d L,
      ‖loopL d L W (HflowBlock d L W 1 (φ ω)) (zt E u) ⟨[true], [b]⟩ - mE E‖ ≤ ρ * Λu)
    (a : Zd d L) :
    ‖(∫ ω, loopL d L W (HflowBlock d L W 1 (φ ω)) (zt E u) ⟨[true], [a]⟩ ∂μ) - mE E‖ ≤
      Green.Kstab3 d Λ κ * (1 + 1 / Loop.gapK κ) * ((ρ ^ 2 + 4) * Λu ^ 2) := by
  classical
  have hE2 : |E| < 2 := by linarith
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE2))
  set z := zt E u with hzdef
  set m := mE E with hm
  have hm1 : ‖m‖ = 1 := norm_spectralM hE2.le
  set Q := GaussianProduct.law v with hQ
  set σ : ℝ := c0 * (W : ℝ) ^ d with hσdef
  have hσ0 : 0 ≤ σ := by positivity
  have hLσ0 : 0 ≤ (L : ℝ) ^ d * σ := by positivity
  have hu0 : 0 ≤ u := by rw [← hsum]; positivity
  have ht1' : t1 < 1 := by linarith
  have hc : (Fintype.card (Zd d L) : ℕ) = L ^ d := OneLoop_card_Zd d L
  set Φ : Zd d L → Ω d L W → ℂ := fun b ω' => loopL d L W (HflowBlock d L W 1 ω') z ⟨[true], [b]⟩ - m
    with hΦ
  have hΦc : ∀ b, Continuous (Φ b) :=
    fun b => (OneLoop_gloop_cont d L W 1 hz b).sub continuous_const
  have hΦm : ∀ b, Measurable (Φ b) := fun b => (hΦc b).measurable
  have hΦb : ∀ b ω', ‖Φ b ω'‖ ≤ Env := fun b ω' => hEnv b ω'
  have hEnv0 : 0 ≤ Env := (norm_nonneg _).trans (hΦb 0 0)
  -- transfer of integrals along `φ`
  have hint : ∀ {F : Ω d L W → ℂ}, Continuous F →
      ∫ ω, F (φ ω) ∂μ = ∫ ω', F ω' ∂Q := by
    intro F hF
    have h := integral_map hφ.aemeasurable (hF.aestronglyMeasurable (μ := μ.map φ))
    rw [hmap] at h
    exact h.symm
  -- the first moments and the self-consistent equation
  have hgI : ∀ b, Integrable (fun ω' => loopL d L W (HflowBlock d L W 1 ω') z ⟨[true], [b]⟩) Q :=
    fun b => OneLoop_integrable_gloop d L W v 1 hz b
  have hxg : ∀ b, ∫ ω', Φ b ω' ∂Q =
      (∫ ω', loopL d L W (HflowBlock d L W 1 ω') z ⟨[true], [b]⟩ ∂Q) - m := by
    intro b
    simp only [hΦ]
    rw [integral_sub (hgI b) (integrable_const _), integral_const]
    simp
  set Y : Zd d L → Zd d L → ℂ := fun b a' => ∫ ω', Φ b ω' * Φ a' ω' ∂Q with hY
  set x : Zd d L → ℂ := fun b => ∫ ω', Φ b ω' ∂Q with hx
  set y : Zd d L → ℂ := fun a' =>
    m * ∑ b : Zd d L, ((t1 : ℂ) * SB d L g b a' + (σ : ℂ)) * Y b a' with hy
  have hxy : ∀ a', x a' =
      m ^ 2 * ∑ b : Zd d L, ((t1 : ℂ) * SB d L g b a' + (σ : ℂ)) * x b + y a' := by
    intro a'
    have h := OneLoop_selfcons d L W g hL v hv hsum hE2 hu1 a'
    simp only [hx, hy, hY, hxg] at h ⊢
    exact h
  -- the pair bound from the pathwise input
  have hpair : ∀ b a', ‖Y b a'‖ ≤ (ρ * Λu) ^ 2 + 4 * Λu ^ 2 := by
    intro b a'
    have hYeq : Y b a' = ∫ ω, Φ b (φ ω) * Φ a' (φ ω) ∂μ := (hint ((hΦc b).mul (hΦc a'))).symm
    have hpt : ∀ ω, ‖Φ b (φ ω) * Φ a' (φ ω)‖ ≤
        (ρ * Λu) ^ 2 + T.indicator (fun _ => Env ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ T
      · rw [Set.indicator_of_mem hω, norm_mul]
        calc ‖Φ b (φ ω)‖ * ‖Φ a' (φ ω)‖ ≤ Env * Env :=
              mul_le_mul (hΦb b (φ ω)) (hΦb a' (φ ω)) (norm_nonneg _) hEnv0
          _ = Env ^ 2 := (sq Env).symm
          _ ≤ (ρ * Λu) ^ 2 + Env ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
      · rw [Set.indicator_of_notMem hω, add_zero, norm_mul]
        have h1 := hgood ω hω b
        have h2 := hgood ω hω a'
        calc ‖Φ b (φ ω)‖ * ‖Φ a' (φ ω)‖ ≤ (ρ * Λu) * (ρ * Λu) :=
              mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
          _ = (ρ * Λu) ^ 2 := (sq _).symm
    have hmeas : Measurable (fun ω => Φ b (φ ω) * Φ a' (φ ω)) :=
      ((hΦm b).comp hφ).mul ((hΦm a').comp hφ)
    have hint1 : Integrable (fun ω => ‖Φ b (φ ω) * Φ a' (φ ω)‖) μ := by
      refine Integrable.of_bound (C := Env * Env) hmeas.norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [norm_norm, norm_mul]
      exact mul_le_mul (hΦb b (φ ω)) (hΦb a' (φ ω)) (norm_nonneg _) hEnv0
    have hint2 : Integrable (fun ω => (ρ * Λu) ^ 2 + T.indicator (fun _ => Env ^ 2) ω) μ :=
      (integrable_const _).add ((integrable_const _).indicator hT)
    rw [hYeq]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono hint1 hint2 hpt).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hT), integral_const,
      integral_indicator_const _ hT]
    simp only [probReal_univ, smul_eq_mul]
    have : μ.real T * Env ^ 2 ≤ 4 * Λu ^ 2 :=
      (mul_le_mul_of_nonneg_right hTδ (sq_nonneg _)).trans hbad
    linarith
  -- the row norm of the profile
  have hrowS : ∀ a' : Zd d L, ∑ b : Zd d L, ‖(t1 : ℂ) * SB d L g b a' + (σ : ℂ)‖ ≤ u := by
    intro a'
    have hsb : ∑ b : Zd d L, ‖SB d L g b a'‖ = 1 := by
      simp_rw [OneLoop_SB_symm d L g a']
      have h := congrArg (fun r : NNReal => (r : ℝ)) (sum_nnnorm_SB_row d L g hL a')
      simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] using h
    calc ∑ b : Zd d L, ‖(t1 : ℂ) * SB d L g b a' + (σ : ℂ)‖
        ≤ ∑ b : Zd d L, (t1 * ‖SB d L g b a'‖ + σ) := Finset.sum_le_sum fun b _ => by
          calc ‖(t1 : ℂ) * SB d L g b a' + (σ : ℂ)‖ ≤ ‖(t1 : ℂ) * SB d L g b a'‖ + ‖(σ : ℂ)‖ :=
                norm_add_le _ _
            _ = t1 * ‖SB d L g b a'‖ + σ := by
                rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                  Real.norm_eq_abs, abs_of_nonneg ht1, abs_of_nonneg hσ0]
      _ = t1 + (L : ℝ) ^ d * σ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsb, Finset.sum_const, Finset.card_univ,
            hc, nsmul_eq_mul]
          push_cast
          ring
      _ = u := by rw [hσdef]; exact hsum
  have hyle : ∀ a', ‖y a'‖ ≤ (ρ * Λu) ^ 2 + 4 * Λu ^ 2 := by
    intro a'
    have hK0 : 0 ≤ (ρ * Λu) ^ 2 + 4 * Λu ^ 2 := by positivity
    calc ‖y a'‖ = ‖m‖ * ‖∑ b : Zd d L, ((t1 : ℂ) * SB d L g b a' + (σ : ℂ)) * Y b a'‖ := by
          rw [hy]; exact norm_mul _ _
      _ ≤ 1 * (∑ b : Zd d L, ‖(t1 : ℂ) * SB d L g b a' + (σ : ℂ)‖ *
            ((ρ * Λu) ^ 2 + 4 * Λu ^ 2)) := by
          rw [hm1]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b _ => ?_)) zero_le_one
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hpair b a') (norm_nonneg _)
      _ = (∑ b : Zd d L, ‖(t1 : ℂ) * SB d L g b a' + (σ : ℂ)‖) *
            ((ρ * Λu) ^ 2 + 4 * Λu ^ 2) := by
          rw [one_mul, Finset.sum_mul]
      _ ≤ u * ((ρ * Λu) ^ 2 + 4 * Λu ^ 2) := mul_le_mul_of_nonneg_right (hrowS a') hK0
      _ ≤ 1 * ((ρ * Λu) ^ 2 + 4 * Λu ^ 2) := mul_le_mul_of_nonneg_right hu1.le hK0
      _ = (ρ * Λu) ^ 2 + 4 * Λu ^ 2 := one_mul _
  -- stability, with the proved `d ≥ 3` constant
  have hK : Green.Stable (svar d L W g) ((t1 : ℂ) * mE E ^ 2) (Green.Kstab3 d Λ κ) :=
    Green.stable_svar_bulk_vtx hd hL hg hgΛ hκ hE ht1 ht1'
  have hxa := OneLoop_stable d L W g hL hκ hE ht1 hσ0 hsum hu1 hK (x := x) (y := y)
    (fun a' => hxy a') hyle a
  have hconc : (∫ ω, loopL d L W (HflowBlock d L W 1 (φ ω)) z ⟨[true], [a]⟩ ∂μ) - m = x a := by
    rw [hint (OneLoop_gloop_cont d L W 1 hz a), hx]
    simp only
    rw [hxg a]
  rw [hconc]
  calc ‖x a‖ ≤ Green.Kstab3 d Λ κ * (1 + 1 / Loop.gapK κ) *
        ((ρ * Λu) ^ 2 + 4 * Λu ^ 2) := hxa
    _ = Green.Kstab3 d Λ κ * (1 + 1 / Loop.gapK κ) *
        ((ρ ^ 2 + 4) * Λu ^ 2) := by ring

end Core

section Wrapper

open scoped Matrix.Norms.L2Operator

/-- `blockMat (Xmat ω) = HflowBlock 1 ω` (`OL:1431`). -/
private theorem OneLoop_blockMat_Xmat (d L W : ℕ) [NeZero L] [NeZero W] (ω : Ω d L W) :
    blockMat d L W (Xmat d L W ω) = HflowBlock d L W 1 ω := by
  unfold HflowBlock Hflow blockMat
  simp

/-- **The bound at one grid time** (`OL:1441`): for a set `Bset` of probability `≤ N^{-5}` off which
every `1`-loop of step `k` is `≤ ρ Λu`, `Λu = (N η_u)^{-1}`:
`‖𝔼⟨(G-m)E_a⟩‖ ≤ Kstab3 d Λ κ (1 + 1/c_κ) (ρ² + 4) Λu²`, for `0 < sz.lam n ≤ Λ`, `3 ≤ d`.
(`D = 5`: the envelope of a `1`-loop is `L^d η⁻¹ ≤ N² Λu`.) -/
private theorem OneLoop_expect_bound (hd : 3 ≤ d) {Λ κ : ℝ} (hκ : 0 < κ) (n : ℕ)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ)
    {E t1 t0 : ℕ → ℝ} (hE : |E n| ≤ 2 - κ) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n)
    (ht0 : t0 n < 1) (K : ℕ → ℕ) (hK : K n ≠ 0) (k : ℕ) (hkK : k ≤ K n)
    {ρ : ℝ} (Bset : Set (PathΩ sz))
    (hPB : Pgue sz Bset ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(5 : ℝ))))
    (hgood : ∀ ω ∉ Bset, ∀ b : Zd d (sz.L n),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
          (zt (E n) (gridTime t1 t0 K n k)) ⟨[true], [b]⟩ - mE (E n)‖
        ≤ ρ * (gueScale sz E n (gridTime t1 t0 K n k))⁻¹)
    (a : Zd d (sz.L n)) :
    ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
          (zt (E n) (gridTime t1 t0 K n k)) ⟨[true], [a]⟩ ∂(Pgue sz)) - mE (E n)‖
      ≤ Green.Kstab3 d Λ κ * (1 + 1 / Loop.gapK κ) *
        ((ρ ^ 2 + 4) * (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ 2) := by
  classical
  have hL3 := sz.three_le_L n
  have hW0 := sz.W_pos n
  have hLpos : (0 : ℝ) < sz.L n := by exact_mod_cast (show 0 < sz.L n by omega)
  have hWpos : (0 : ℝ) < sz.W n := by exact_mod_cast hW0
  have hNeq : ((sz.size n : ℕ) : ℝ) = (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNeq]; positivity
  have hN1 : 1 ≤ N := by
    have h1 : 1 ≤ sz.size n := sz.one_le_size n
    rw [hNdef]
    exact_mod_cast h1
  -- the grid time
  set Δ := gridStep t1 t0 K n with hΔdef
  set u := gridTime t1 t0 K n k with hudef
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hKpos.le
  have hkK' : (k : ℝ) ≤ K n := by exact_mod_cast hkK
  have hkΔ : (k : ℝ) * Δ ≤ t0 n - t1 n := by
    calc (k : ℝ) * Δ ≤ K n * Δ := mul_le_mul_of_nonneg_right hkK' hΔ0
      _ = t0 n - t1 n := by rw [hΔdef, gridStep]; field_simp
  have hu_eq : u = t1 n + (k : ℝ) * Δ := rfl
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg _) hΔ0
  have hu0 : 0 ≤ u := by rw [hu_eq]; linarith
  have hu1 : u < 1 := by rw [hu_eq]; linarith
  have hE2 : |E n| < 2 := by linarith
  have hm1 : ‖mE (E n)‖ = 1 := norm_spectralM hE2.le
  set η := etaT (E n) u with hηdef
  have hηpos : 0 < η := etaT_pos hE2 hu1
  have hηle : η ≤ 1 := by
    have him : (mE (E n)).im ≤ 1 := by
      have h := Complex.abs_im_le_norm (mE (E n))
      rw [hm1] at h
      exact (le_abs_self _).trans h
    have him0 := spectralM_im_pos hE2
    rw [hηdef, etaT]
    nlinarith
  set Λu := (gueScale sz E n u)⁻¹ with hΛdef
  have hscale : gueScale sz E n u = N * η := rfl
  have hΛ : Λu = (N * η)⁻¹ := by rw [hΛdef, hscale]
  have hΛ0 : 0 ≤ Λu := by rw [hΛ]; positivity
  have hηinv : η⁻¹ = N * Λu := by rw [hΛ]; field_simp
  -- the one-time law of step `k`
  set aa := Real.sqrt (t1 n) with haa
  set bb := Real.sqrt (Δ / N) with hbb
  have haa2 : aa ^ 2 = t1 n := Real.sq_sqrt ht1
  have hbb2 : bb ^ 2 = Δ / N := Real.sq_sqrt (div_nonneg hΔ0 hNpos.le)
  set c0 : ℝ := (k : ℝ) * bb ^ 2 with hc0
  have hc00 : 0 ≤ c0 := by rw [hc0]; positivity
  have hsum : t1 n + (sz.L n : ℝ) ^ d * (c0 * (sz.W n : ℝ) ^ d) = u := by
    rw [hc0, hbb2, hu_eq, hNeq]
    field_simp
  have hv : ∀ c : CoordF d (sz.L n) (sz.W n), (olVar sz aa bb k ⟨n, c⟩ : ℝ) =
      t1 n * (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) +
        c0 * (if c.1 = c.2.1 then 1 else 1 / 2) := by
    intro c
    have hg' : ((Sizes.seqGvar sz ⟨n, c⟩ : ℝ≥0) : ℝ) =
        (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) := rfl
    simp only [olVar, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul, hg', haa2]
    by_cases hc : c.1 = c.2.1
    · simp [gueUnitVar, hc, hc0]
    · simp [gueUnitVar, hc, hc0]
      ring
  have hmap := ol_map_comb_slice sz aa bb k n
  have hφ : Measurable (fun ω : PathΩ sz => Sizes.slice sz n (olComb sz aa bb k ω)) :=
    (Sizes.measurable_slice sz n).comp (olComb_measurable sz aa bb k)
  have hblock : ∀ ω : PathΩ sz, blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω) =
      HflowBlock d (sz.L n) (sz.W n) 1 (Sizes.slice sz n (olComb sz aa bb k ω)) := by
    intro ω
    rw [ol_gueH_eq]
    exact OneLoop_blockMat_Xmat d _ _ _
  -- the measurable exceptional set
  set T := toMeasurable (Pgue sz) Bset with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hBT : Bset ⊆ T := subset_toMeasurable _ _
  have hTδ : (Pgue sz).real T ≤ N ^ (-(5 : ℝ)) := by
    rw [measureReal_def, hT, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _) hPB
  -- the global envelope
  have hz : (zt (E n) u).im ≠ 0 := by
    rw [spectralZ_im]
    exact ne_of_gt (mul_pos (by linarith) (spectralM_im_pos hE2))
  have hzη : η ≤ |(zt (E n) u).im| := by
    rw [spectralZ_im, abs_of_pos (mul_pos (by linarith) (spectralM_im_pos hE2))]
    exact le_rfl
  have hgl : ∀ (b : Zd d (sz.L n)) (ω' : Ω d (sz.L n) (sz.W n)),
      ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) 1 ω') (zt (E n) u)
        ⟨[true], [b]⟩‖ ≤ (sz.L n : ℝ) ^ d * η⁻¹ := by
    intro b ω'
    have h := norm_gloop_le_crude d (sz.L n) (sz.W n)
      (HflowBlock_isHermitian d (sz.L n) (sz.W n) 1 ω') hηpos hzη ⟨[true], [b]⟩
      (by simp [Loop.LoopIdx.WF])
    refine h.trans (le_of_eq ?_)
    have hW : (sz.W n : ℝ) ^ d ≠ 0 := (pow_pos hWpos d).ne'
    simp only [List.length_singleton, pow_one]
    push_cast
    rw [mul_pow]
    field_simp
  have hL2N : (sz.L n : ℝ) ^ d ≤ N := by
    rw [hNeq]
    have hW2 : (1 : ℝ) ≤ (sz.W n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW0)
    nlinarith [pow_nonneg hLpos.le d]
  have hEnv : ∀ (b : Zd d (sz.L n)) (ω' : Ω d (sz.L n) (sz.W n)),
      ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) 1 ω') (zt (E n) u)
        ⟨[true], [b]⟩ - mE (E n)‖ ≤ 2 * N ^ 2 * Λu := by
    intro b ω'
    have h1 : 1 ≤ η⁻¹ := by rw [le_inv_comm₀ one_pos hηpos, inv_one]; exact hηle
    have hη0 : 0 ≤ η⁻¹ := (inv_pos.2 hηpos).le
    calc ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) 1 ω') (zt (E n) u)
          ⟨[true], [b]⟩ - mE (E n)‖
        ≤ ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) 1 ω') (zt (E n) u)
          ⟨[true], [b]⟩‖ + ‖mE (E n)‖ := norm_sub_le _ _
      _ ≤ (sz.L n : ℝ) ^ d * η⁻¹ + (sz.L n : ℝ) ^ d * η⁻¹ := by
          rw [hm1]
          refine add_le_add (hgl b ω') ?_
          have hL1 : (1 : ℝ) ≤ (sz.L n : ℝ) ^ d :=
            one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ sz.L n))
          exact one_le_mul_of_one_le_of_one_le hL1 h1
      _ ≤ N * η⁻¹ + N * η⁻¹ := by gcongr
      _ = 2 * N ^ 2 * Λu := by rw [hηinv]; ring
  have hbad : N ^ (-(5 : ℝ)) * (2 * N ^ 2 * Λu) ^ 2 ≤ 4 * Λu ^ 2 := by
    have h5 : N ^ (-(5 : ℝ)) = (N ^ 5)⁻¹ := by
      rw [Real.rpow_neg hNpos.le]; norm_cast
    calc N ^ (-(5 : ℝ)) * (2 * N ^ 2 * Λu) ^ 2 = 4 * Λu ^ 2 / N := by
          rw [h5]; field_simp; ring
      _ ≤ 4 * Λu ^ 2 := by
          rw [div_le_iff₀ hNpos]
          have h4 : 0 ≤ 4 * Λu ^ 2 := by positivity
          calc 4 * Λu ^ 2 = 4 * Λu ^ 2 * 1 := (mul_one _).symm
            _ ≤ 4 * Λu ^ 2 * N := mul_le_mul_of_nonneg_left hN1 h4
  have hgood' : ∀ ω ∉ T, ∀ b : Zd d (sz.L n),
      ‖loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) 1
          (Sizes.slice sz n (olComb sz aa bb k ω))) (zt (E n) u) ⟨[true], [b]⟩ -
        mE (E n)‖ ≤ ρ * Λu := by
    intro ω hω b
    have h := hgood ω (fun h => hω (hBT h)) b
    rwa [hblock ω] at h
  have key := OneLoop_expect_core d (sz.L n) (sz.W n) (sz.lam n) hd hL3 hg hgΛ hκ hE ht1 hc00
    hsum hu1 (fun c => olVar sz aa bb k ⟨n, c⟩) hv (Pgue sz)
    (fun ω : PathΩ sz => Sizes.slice sz n (olComb sz aa bb k ω)) hφ hmap T hTm hEnv hTδ hbad
    hgood' a
  have hfun : (fun ω : PathΩ sz => loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
      (zt (E n) u) ⟨[true], [a]⟩) = fun ω : PathΩ sz => loopL d (sz.L n) (sz.W n)
        (HflowBlock d (sz.L n) (sz.W n) 1 (Sizes.slice sz n (olComb sz aa bb k ω)))
        (zt (E n) u) ⟨[true], [a]⟩ := funext fun ω => by rw [hblock ω]
  rw [hfun]
  exact key

end Wrapper

section Main

open scoped Matrix.Norms.L2Operator

/-- **Lemma 5.15 for the GUE-phase grid** (`OL:1642`): given the pathwise `1`-loop bound
`‖⟨(G - m)E_a⟩‖ ≺ (N η_u)^{-1}` at every grid time of the GUE-phase path, the `1`-loop expectation
satisfies `‖𝔼⟨(G - m)E_a⟩‖ ≤ N^ε (N η_u)^{-2}` eventually, for every `ε > 0`, uniformly in the grid
time and the block label.  Proof: the one-time law of grid step `k` (`ol_map_comb_slice`), Stein's
identity for that product Gaussian with the mixed block profile
`Ŝ = t₁ S^{(B)} + ((u - t₁)/L^d) J` (`OneLoop_selfcons`), stability of `1 - m² Ŝ` through
`|1 - u m²| ≥ gapK κ` and the `d ≥ 3` constant `Kstab3 d Λ κ` of `Green/Stability.lean`
(`OneLoop_stable`), and the pathwise input on its good event with the envelope `‖G‖ ≤ η⁻¹` on the
bad event (`OneLoop_expect_bound`, `D = 5`).  The constant does not depend on `n` or `L`: it is
absorbed by `N^{ε/2}` as soon as `N^{ε/2} ≥ 8 Kstab3 d Λ κ (1 + 1/gapK κ) + 1`.  The hypotheses
`3 ≤ d` and `0 < sz.lam n ≤ Λ` eventually (the coupling window of the proved pin 5s of
`lem_propTH`; `(eq:WO)` gives it with `Λ = 𝔡⁻¹`) are the difference to the `d = 2` statement. -/
theorem gueGrid_expect_oneLoop (hd : 3 ≤ d) {Λ κ : ℝ} (hκ : 0 < κ) {E t1 t0 : ℕ → ℝ}
    {K : ℕ → ℕ}
    (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hK : ∀ n, K n ≠ 0)
    (h1 : StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (K n + 1) × Zd d (sz.L n)) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n p.1 ω))
            (zt (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ - mE (E n)‖)
      (fun n p _ => (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (K n + 1) × Zd d (sz.L n),
      ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n p.1 ω))
          (zt (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue sz)) - mE (E n)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ 2 := by
  intro ε hε
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hsize
  have hκ2 : κ ≤ 2 := by
    have := hE 0
    linarith [abs_nonneg (E 0)]
  have hgpos : 0 < Loop.gapK κ := OneLoop_gapK_pos hκ hκ2
  set gk := Loop.gapK κ with hg
  set K' : ℝ := Green.Kstab3 d Λ κ * (1 + 1 / gk) with hK'
  have hK'0 : 0 ≤ K' := by
    have := Green.one_le_Kstab3 d Λ κ
    have : 0 ≤ 1 + 1 / gk := by positivity
    positivity
  have hbad := h1 (ε / 4) (by positivity) 5 (by norm_num)
  have habs : ∀ᶠ n : ℕ in atTop, 8 * K' + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp hsz).eventually (eventually_ge_atTop (8 * K' + 1))
  filter_upwards [hbad, habs, hlam, hsz.eventually (eventually_ge_atTop 1)] with n hPn hn hlamn hN1r
  rintro ⟨k, a⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hbound := OneLoop_expect_bound sz hd hκ n hlamn.1 hlamn.2 (hE n) (ht1 n) (ht10 n) (ht0 n) K
    (hK n) k (Nat.lt_succ_iff.1 k.isLt) (ρ := N ^ (ε / 4)) _ hPn
    (fun ω hω b => by
      by_contra hc
      exact hω ⟨(k, b), lt_of_not_ge hc⟩) a
  -- the constants
  set Λ2 := (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ 2 with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by rw [hΛ2]; exact sq_nonneg _
  set X := N ^ (ε / 2) with hX
  have hρ : (N ^ (ε / 4)) ^ 2 = X := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hNε : N ^ ε = X * X := by
    rw [hX, ← Real.rpow_add hN0]; ring_nf
  have hX1 : 1 ≤ X := by nlinarith
  have hXC : K' * (X + 4) ≤ X * X := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (by linarith : (0 : ℝ) ≤ X - 8 * K' - 1),
      mul_nonneg hK'0 (by linarith : (0 : ℝ) ≤ X - 1)]
  rw [hρ] at hbound
  calc _ ≤ K' * ((X + 4) * Λ2) := hbound
    _ = (K' * (X + 4)) * Λ2 := by ring
    _ ≤ (X * X) * Λ2 := mul_le_mul_of_nonneg_right hXC hΛ20
    _ = N ^ ε * Λ2 := by rw [hNε]

end Main

end RBM.Univ.GUEPhase

/-! ## Compiled instances

The preflight sizes `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`, `N 0 = 2097152`,
`lam n = (2 (n + 1))^{-6}`), the grid data of `Grid.lean` §`GridCheck`: `t₀ = 9/10`,
`t₁ = (1 - ζ(1/20)) · 9/10 = e^{-1/20} · 9/10`, `K = 4`, and `E = 1` (`|E| = 1 ≤ 3/2`, `κ = 1/2`).
The pathwise one-loop input `h1` (the `StochDomAt` output of the §7.2 random layer, another gate's
pin) stays a hypothesis of the main instance; every deterministic hypothesis is discharged. -/

namespace RBM.Univ.GUEPhase.OneLoopInst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
  RBM.Univ.GUEPhase RBM.Gauss.SizesInst

/-- The grid data `t₁ = (1 - ζ(1/20)) · 9/10`, `t₀ = 9/10`, `K = 4`, `E = 1`. -/
private abbrev OneLoopInst_t1 : ℕ → ℝ := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)
private abbrev OneLoopInst_t0 : ℕ → ℝ := fun _ => 9 / 10
private abbrev OneLoopInst_K : ℕ → ℕ := fun _ => 4
private abbrev OneLoopInst_E : ℕ → ℝ := fun _ => 1

private theorem OneLoopInst_ouZeta_nonneg : 0 ≤ ouZeta (1 / 20) := by
  unfold ouZeta
  have := Real.exp_le_one_iff.2 (neg_nonpos.2 (by norm_num : (0 : ℝ) ≤ 1 / 20))
  linarith

private theorem OneLoopInst_t1_nonneg (n : ℕ) : 0 ≤ OneLoopInst_t1 n := by
  have hz : ouZeta (1 / 20) ≤ 1 := by
    unfold ouZeta
    have := (Real.exp_pos (-(1 / 20 : ℝ))).le
    linarith
  change 0 ≤ (1 - ouZeta (1 / 20)) * (9 / 10)
  nlinarith

private theorem OneLoopInst_t1_le_t0 (n : ℕ) : OneLoopInst_t1 n ≤ OneLoopInst_t0 n := by
  change (1 - ouZeta (1 / 20)) * (9 / 10) ≤ 9 / 10
  nlinarith [OneLoopInst_ouZeta_nonneg]

/-- `olComb` at `k = 0` is the scaled first draw; at `k = 4` it has the extra grid sum (a concrete
evaluation of the definition). -/
example (ω : PathΩ sz0) : olComb sz0 (1 / 2) (1 / 3) 0 ω = (1 / 2 : ℝ) • ω 0 := by
  simp [olComb]

example (ω : PathΩ sz0) :
    olComb sz0 (1 / 2) (1 / 3) 4 ω = (1 / 2 : ℝ) • ω 0 + (1 / 3 : ℝ) • ∑ i ∈ Finset.Icc 1 4, ω i :=
  rfl

/-- `olComb_measurable` at `a = 1/2`, `b = 1/3`, `k = 4`. -/
example : Measurable (olComb sz0 (1 / 2) (1 / 3) 4) := olComb_measurable sz0 _ _ _

/-- `olVar` at a diagonal coordinate of size `n = 0` (`gueUnitVar = 1`): `a² S_ii + k b²`; and at an
off-diagonal one (`gueUnitVar = 1/2`): `a² S_ij/2 + k b²/2`; both positive. -/
example (i : Idx 3 (sz0.L 0) (sz0.W 0)) :
    (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, i, true)⟩ : ℝ) =
      (1 / 2) ^ 2 * (Sizes.seqGvar sz0 ⟨0, (i, i, true)⟩ : ℝ) + 4 * ((1 / 3) ^ 2 * 1) := by
  simp [olVar, gueUnitVar]

example (i j : Idx 3 (sz0.L 0) (sz0.W 0)) (hij : i ≠ j) :
    (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, j, true)⟩ : ℝ) =
      (1 / 2) ^ 2 * (Sizes.seqGvar sz0 ⟨0, (i, j, true)⟩ : ℝ) + 4 * ((1 / 3) ^ 2 * (1 / 2)) := by
  simp [olVar, gueUnitVar, hij]

example (i : Idx 3 (sz0.L 0) (sz0.W 0)) :
    0 < (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, i, true)⟩ : ℝ) := by
  have : (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, i, true)⟩ : ℝ) =
      (1 / 2) ^ 2 * (Sizes.seqGvar sz0 ⟨0, (i, i, true)⟩ : ℝ) + 4 * ((1 / 3) ^ 2 * 1) := by
    simp [olVar, gueUnitVar]
  rw [this]
  have h0 : (0 : ℝ) ≤ (Sizes.seqGvar sz0 ⟨0, (i, i, true)⟩ : ℝ) := NNReal.coe_nonneg _
  nlinarith

/-- `ol_map_comb` at `a = 1/2`, `b = 1/3`, `k = 4`: the combination has the product Gaussian law
with variances `olVar`. -/
example :
    (Pgue sz0).map (olComb sz0 (1 / 2) (1 / 3) 4)
      = Measure.infinitePi
          (fun c : Sizes.SeqCoord sz0 => gaussianReal 0 (olVar sz0 (1 / 2) (1 / 3) 4 c)) :=
  ol_map_comb sz0 _ _ _

/-- `ol_map_comb_slice` at the same data and `n = 0` (`L = 4`, `W = 32`). -/
example :
    (Pgue sz0).map (fun ω => Sizes.slice sz0 0 (olComb sz0 (1 / 2) (1 / 3) 4 ω))
      = GaussianProduct.law (fun c : CoordF 3 (sz0.L 0) (sz0.W 0) =>
          olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, c⟩) :=
  ol_map_comb_slice sz0 _ _ _ 0

/-- `ol_gueH_eq` at the grid data, `n = 0`, `k = 4 = K`, every sample point. -/
example (ω : PathΩ sz0) :
    gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K 0 4 ω
      = Xmat 3 (sz0.L 0) (sz0.W 0) (Sizes.slice sz0 0 (olComb sz0 (Real.sqrt (OneLoopInst_t1 0))
          (Real.sqrt (gridStep OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K 0 /
            ((sz0.size 0 : ℕ) : ℝ))) 4 ω)) :=
  ol_gueH_eq sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K 0 4 ω

/-- `ol_gueH_eq` at every size index and every grid step. -/
example (n k : ℕ) (ω : PathΩ sz0) :
    gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n k ω
      = Xmat 3 (sz0.L n) (sz0.W n) (Sizes.slice sz0 n (olComb sz0 (Real.sqrt (OneLoopInst_t1 n))
          (Real.sqrt (gridStep OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n /
            ((sz0.size n : ℕ) : ℝ))) k ω)) :=
  ol_gueH_eq sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n k ω

/-- The coupling window: `0 < sz0.lam n ≤ 10` for every `n` (`lam n = (2 (n + 1))^{-6} ≤ 1`). -/
private theorem OneLoopInst_lam_window : ∀ᶠ n : ℕ in atTop, 0 < sz0.lam n ∧ sz0.lam n ≤ 10 := by
  refine Eventually.of_forall fun n => ?_
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  refine ⟨by rw [hlam]; positivity, ?_⟩
  rw [hlam]
  exact (inv_le_one_of_one_le₀ (one_le_pow₀ hx1)).trans (by norm_num)

/-- **`gueGrid_expect_oneLoop` at the preflight sizes** (`d = 3`, `κ = 1/2`, `E = 1`, the grid data
above, `Λ = 10`): every deterministic hypothesis is discharged (`3 ≤ 3`, `0 < 1/2`, `N_n → ∞`,
`0 < lam n ≤ 10`, `|1| ≤ 2 - 1/2`, `0 ≤ t₁ ≤ t₀ = 9/10 < 1`, `K = 4 ≠ 0`); only the pathwise
`1`-loop input `h1` (the output of the §7.2 layer, another gate's pin) is a hypothesis. -/
private theorem OneLoopInst_main
    (h1 : StochDomAt (Pgue sz0) sz0.size
      (fun n (p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n)) ω =>
        ‖loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
              (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω))
            (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))
              ⟨[true], [p.2]⟩ - mE (OneLoopInst_E n)‖)
      (fun n p _ => (gueScale sz0 OneLoopInst_E n
        (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n),
      ‖(∫ ω, loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
            (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω))
          (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))
            ⟨[true], [p.2]⟩ ∂(Pgue sz0)) - mE (OneLoopInst_E n)‖ ≤
        ((sz0.size n : ℕ) : ℝ) ^ ε * (gueScale sz0 OneLoopInst_E n
          (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹ ^ 2 :=
  gueGrid_expect_oneLoop sz0 (by norm_num) (Λ := 10) (κ := 1 / 2) (by norm_num)
    (E := OneLoopInst_E) (t1 := OneLoopInst_t1) (t0 := OneLoopInst_t0) (K := OneLoopInst_K)
    (tendsto_natCast_atTop_iff.mp sz0_tendsto) OneLoopInst_lam_window
    (fun _ => by norm_num [OneLoopInst_E]) OneLoopInst_t1_nonneg OneLoopInst_t1_le_t0
    (fun _ => by norm_num [OneLoopInst_t0]) (fun _ => by norm_num [OneLoopInst_K]) h1

/-- The eventual conclusion at the instance is nonempty: for `ε = 1/2` the statement `∀ᶠ n`
produces an index `n` (a size at which the bound is asserted), given `h1`. -/
example
    (h1 : StochDomAt (Pgue sz0) sz0.size
      (fun n (p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n)) ω =>
        ‖loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
              (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω))
            (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))
              ⟨[true], [p.2]⟩ - mE (OneLoopInst_E n)‖)
      (fun n p _ => (gueScale sz0 OneLoopInst_E n
        (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹)) :
    ∃ n : ℕ, ∀ p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n),
      ‖(∫ ω, loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
            (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω))
          (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))
            ⟨[true], [p.2]⟩ ∂(Pgue sz0)) - mE (OneLoopInst_E n)‖ ≤
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * (gueScale sz0 OneLoopInst_E n
          (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹ ^ 2 :=
  (OneLoopInst_main h1 (1 / 2) (by norm_num)).exists

end RBM.Univ.GUEPhase.OneLoopInst

end
