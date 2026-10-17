/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.StepDecomp
import RBM3D.Green.Pins
import RBM3D.Gauss.FlowCalculus
import RBM3D.Induction.ConArgDet

/-!
# The quadratic-variation form and the quadratic-variation identities of Step 2 (`d ≥ 3`)

Ticket T2084 (ST2-23).  Port of RBM2D `RBM2D/Path/QVForm.lean` (325 lines) and
`RBM2D/Path/QVIdentity.lean` (844 lines) at `c9a24cf` (RBM1D `Gauss/GridQVForm.lean`, commit
`86573b9`, for the first) to the merged MD layer, in one file.  Paper: arXiv:2507.20274,
`(defEOTE)` and `(def_diffakn_k)` (`3_5:176-190`), the six-loop `Eq:defGLoop` (`1_2:824`).

* **Part 1 (`QVForm`)**: the symmetric covariance form `vB` of `linTrVar`, `vB_self`,
  `vB_nonneg_diag`, `v_sum_eq`, `abs_vB_le`, and **`v_gradMat_eq_quadVar`**: for `Φ` differentiable
  at the Hermitian `M` and real on Hermitian matrices, `linTrVar n (gradMat Φ M)` is the quadratic
  variation `Σ_c gvarF_c ‖fderiv ℝ Φ M (coordinateMatrix c)‖²` over all `CoordF d L W`
  (`gvarF d L W (sz.lam n)`, the variance of the sequence `sz`).  Imports `Path/StepDecomp.lean`
  (`gradMat`, `lin_eq_fderiv`) and `Path/Markov.lean` (`linTr`, `linTrVar`, `coordFinset`).
* **Part 2 (`QVIdentity`)**: the pins `EECutIdentity`, `QVPropagated`, `EEShift` and their proofs
  `eeCutIdentity`, `qvPropagated`, `eeShift`, over the vocabulary `loop6`, `EE`, `cutDeriv1`,
  `cutDeriv2`, `loopDeriv` (RBM2D `Path/Step2Vocab.lean:87-109`; they do not exist in the merged
  `Induction/Step2Defs.lean`, whose `STEEM`/`STEEkM` are the diagonal case `a = a'` with `σ` as
  argument).  `loopPM`, `greenBlk` are the merged `Green/Pins.lean` ones.

Renaming (`docs/tickets/ST1-COMMON.md` items 2-3): `Z2 L` becomes `Zd d L`, `Idx L W` becomes
`Idx d L W`, `BlockIndex L W` becomes `Vtx d L W`, `Coord/svar/gvar` become `CoordF/svarF/gvarF`,
`d : Sizes` becomes `{d : ℕ} (sz : Sizes d)`, `Gsig` becomes `Gres`, `spectralZ` becomes `zt`,
`green` words are the merged `Gres`, `blockMat X` is `blockMat d L W X`.

`d ≥ 3` changes (CLAUDE.md §5.2):

* **`W^2 → W^d`** (`QVIdentity_svar_sum`, `EE`, `eeShift`): `svarF = W^{-d} S^{(B)}(g)`, the
  entries of `E_b` are `W^{-d}`, `‖E_b‖ ≤ W^{-d}`; `W^d (W^{-d})² = W^{-d}` is the collapse of the
  two block sums.
* **The coupling `g`**: `S^{(B)}(g)` carries `g` (rows still sum to `1` for every real `g`, `3 ≤ L`,
  `sum_norm_SB_row`).  `g : ℝ` is a new parameter of `EE`, of the three pins and of the proofs;
  `gvarF d L W g` is the coordinate variance of the same `g` (paper-delta candidate `T2084a`).
  RBM2D has no coupling.
* **`L^2 → L^d`, `(W L)^2 → (W L)^d`** (`eeShift`): `Σ_b 1 = L^d`, `card (Vtx d L W) = (L W)^d`
  (`card_BlockIndex`); the bound is `12 L^d N W^{-5d} η⁻⁷ Δ ≤ 16 N² η⁻⁷ Δ`, `N = (W L)^d`, using
  `L^d ≤ N` and `W^{-5d} ≤ 1`: the constants `12`, `16` contain no `d`.
* **The exponents of `η`**: `7 = 2 + 5` (one resolvent difference and the other five `G` of the
  six-loop) is the loop length, not the dimension.

The telescoping lemmas are ports of RBM1D `norm_prodList_sub_le` / `norm_prodList_le_pow`
(`RBM1D/Gauss/GridQVStep.lean` at `86573b9`).  Every unpinned helper is `private` and carries the
prefix `QVForm_` or `QVIdentity_`.  The last section compiles every target at the merged `sz0`
(`d = 3`, `L = 4`, `W = 32`, `g = 1/64`).
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Green
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

section QVForm

variable {d : ℕ} {sz : Sizes d}

/-! ### (T1) : `vB`, the linear identity, and its Cauchy–Schwarz bound -/

/-- **`vB`** (RBM1D `vB`, `Gauss/GridQVForm.lean`, commit `86573b9`): the symmetric bilinear
covariance form underlying `linTrVar`. -/
noncomputable def vB (n : ℕ) (A A' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  ∑ c ∈ coordFinset n, (Sizes.seqGvar sz c : ℝ) * linTr n A (Sizes.seqXmat sz n (Pi.single c 1))
      * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1))

/-- `linTrVar` as a real sum (the private `linTrVar_eq_sum` of `Path/Markov.lean`, re-proved). -/
private theorem QVForm_linTrVar_eq_sum (n : ℕ)
    (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTrVar n A = ∑ c ∈ coordFinset n, (Sizes.seqGvar sz c : ℝ)
      * (linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 := by
  unfold linTrVar linVar
  push_cast [NNReal.coe_mk]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **`vB` on the diagonal is `linTrVar`.** -/
theorem vB_self (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    vB n A A = linTrVar n A := by
  rw [QVForm_linTrVar_eq_sum]
  unfold vB
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end QVForm

/-! ### (T2) : `linTrVar n (gradMat Φ M)` is the quadratic variation -/

/-! ### Check on the elementary member `A ↦ sin (Re tr A)` -/

/-! ## The loop vocabulary of Step 2 at `n = 2` (RBM2D `Path/Step2Vocab.lean:87-109`)

`loopPM`, `greenBlk` are the merged `RBM3D/Green/Pins.lean` ones; `loop6`, `EE`, `cutDeriv1`,
`cutDeriv2`, `loopDeriv` are RBM2D's definitions with `Z2 L → Zd d L`, `W^2 → W^d`, `SB L → SB d L g`
(R2, R3, and the coupling `g` of `(eq:variancematrix)`), the six-loop being the merged `loopFine`. -/

/-! ## The pinned statements (RBM2D `Path/QVIdentity.lean:345-372`, with `d`, `g`) -/

/-! ## Coordinate algebra and the cut pairings -/

section CoordAlgebra

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem QVIdentity_cm_apply (c : CoordF d L W) (k l : Idx d L W) :
    coordinateMatrix d L W c k l = Xentry d L W (Pi.single c 1) k l := rfl

private theorem QVIdentity_cm_lt {i j : Idx d L W} (h : idxKey d L W i < idxKey d L W j)
    (b : Bool) :
    coordinateMatrix d L W (i, j, b) =
      Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [QVIdentity_cm_apply, Xentry, Matrix.add_apply, Matrix.single_apply,
    Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVIdentity_cm_diag_true (i : Idx d L W) :
    coordinateMatrix d L W (i, i, true) = Matrix.single i i (1 : ℂ) := by
  ext k l
  simp only [QVIdentity_cm_apply, Xentry, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVIdentity_cm_diag_false (i : Idx d L W) :
    coordinateMatrix d L W (i, i, false) = 0 := by
  ext k l
  simp only [QVIdentity_cm_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVIdentity_cm_gt {i j : Idx d L W} (h : idxKey d L W j < idxKey d L W i)
    (b : Bool) :
    coordinateMatrix d L W (i, j, b) = 0 := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [QVIdentity_cm_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

/-- The diagonal coordinate variance is `S_ii` (the private `fineModel_gvarF_diag` of
`Gauss/FineModel.lean:233`, re-proved). -/
private theorem QVIdentity_gvar_diag (g : ℝ) (i : Idx d L W) (b : Bool) :
    (gvarF d L W g (i, i, b) : ℝ) = svarF d L W g i i := by
  change (if i = i then svarF d L W g i i else svarF d L W g i i / 2) = _
  simp

/-- The off-diagonal coordinate variance is `S_ij / 2` (the private `fineModel_gvarF_offDiag` of
`Gauss/FineModel.lean:241`, re-proved). -/
private theorem QVIdentity_gvar_offDiag (g : ℝ) (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- The pairing `Σ_{k,l} X_{kl} f_{lk}` (the trace `tr(X F)` with `F_{lk} = f l k`). -/
private def QVIdentity_pair (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (f : Idx d L W → Idx d L W → ℂ) : ℂ :=
  ∑ k, ∑ l, X k l * f l k

private theorem QVIdentity_pair_single (i j : Idx d L W) (x : ℂ)
    (f : Idx d L W → Idx d L W → ℂ) :
    QVIdentity_pair (Matrix.single i j x) f = x * f j i := by
  simp only [QVIdentity_pair, Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

private theorem QVIdentity_pair_add (X Y : Matrix (Idx d L W) (Idx d L W) ℂ)
    (f : Idx d L W → Idx d L W → ℂ) :
    QVIdentity_pair (X + Y) f = QVIdentity_pair X f + QVIdentity_pair Y f := by
  simp only [QVIdentity_pair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem QVIdentity_pair_zero (f : Idx d L W → Idx d L W → ℂ) :
    QVIdentity_pair (0 : Matrix (Idx d L W) (Idx d L W) ℂ) f = 0 := by
  simp [QVIdentity_pair]

/-- Sum of an ordered-pair function over the three cases of `idxKey`. -/
private theorem QVIdentity_sum_tri (T : Idx d L W → Idx d L W → ℂ) :
    (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j + T j i
      else if i = j then T i i else 0) = ∑ i, ∑ j, T i j := by
  have hpt : ∀ i j, (if idxKey d L W i < idxKey d L W j then T i j + T j i
      else if i = j then T i i else 0) =
      ((if idxKey d L W i < idxKey d L W j then T i j else 0) +
        (if idxKey d L W i < idxKey d L W j then T j i else 0)) +
        (if i = j then T i j else 0) := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [h, hij]
    · subst h; simp
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [not_lt.mpr h.le, hij]
  have hswap : (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T j i else 0) =
      ∑ i, ∑ j, if idxKey d L W j < idxKey d L W i then T i j else 0 := Finset.sum_comm
  calc (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j + T j i
        else if i = j then T i i else 0)
      = (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T j i else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by
        simp only [hpt, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey d L W j < idxKey d L W i then T i j else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by rw [hswap]
    _ = ∑ i, ∑ j, (((if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (if idxKey d L W j < idxKey d L W i then T i j else 0)) +
          (if i = j then T i j else 0)) := by simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, T i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]
        · subst h; simp
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]

/-- **Coordinate sum of a sesquilinear pairing.**  For every pair of kernels `f, f'`,
`Σ_c gvar_c ⟨X_c, f⟩ conj ⟨X_c, f'⟩ = Σ_{k,l} svar_{kl} f_{lk} conj f'_{lk}`. -/
private theorem QVIdentity_coord_sum (g : ℝ) (f f' : Idx d L W → Idx d L W → ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (QVIdentity_pair (coordinateMatrix d L W c) f *
          (starRingEnd ℂ) (QVIdentity_pair (coordinateMatrix d L W c) f')) =
      ∑ k, ∑ l, (svarF d L W g k l : ℂ) * (f l k * (starRingEnd ℂ) (f' l k)) := by
  have hc : ∀ F : CoordF d L W → ℂ,
      ∑ c : CoordF d L W, F c =
        ∑ i : Idx d L W, ∑ j : Idx d L W, (F (i, j, true) + F (i, j, false)) := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => Fintype.sum_bool _
  rw [← QVIdentity_sum_tri, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_left h, QVIdentity_cm_lt h, QVIdentity_cm_lt h,
      QVIdentity_gvar_offDiag g i j true hij,
      QVIdentity_gvar_offDiag g i j false hij, svarF_comm d L W g j i]
    simp only [QVIdentity_pair_add, QVIdentity_pair_single, ite_true, Bool.false_eq_true,
      ite_false, map_add, map_mul, map_neg, map_one, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · subst h
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, QVIdentity_cm_diag_true,
      QVIdentity_cm_diag_false, QVIdentity_gvar_diag, QVIdentity_gvar_diag]
    simp [QVIdentity_pair_single, QVIdentity_pair_zero]
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_right (not_lt.mpr h.le), ite_eq_right hij, QVIdentity_cm_gt h, QVIdentity_cm_gt h]
    simp [QVIdentity_pair_zero]

/-- Reordering four finite sums. -/
private theorem QVIdentity_sum_swap4 {α β : Type*} [Fintype α] [Fintype β]
    (F : α → α → β → β → ℂ) :
    ∑ b, ∑ b', ∑ q, ∑ p, F b b' q p = ∑ q, ∑ p, ∑ b, ∑ b', F b b' q p := by
  calc ∑ b, ∑ b', ∑ q, ∑ p, F b b' q p = ∑ b, ∑ q, ∑ p, ∑ b', F b b' q p := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ p, ∑ b, ∑ b', F b b' q p := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm

/-- `S_{xy}` of the fine lattice as `W^{-d} S^{(B)}_{[x][y]}`, in `ℂ`. -/
private theorem QVIdentity_svarF_cast (g : ℝ) (p q : Vtx d L W) :
    (svarF d L W g ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) : ℂ) =
      SB d L g p.1 q.1 * ((W : ℂ) ^ d)⁻¹ := by
  have h1 : svarF d L W g ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) =
      ((W : ℝ) ^ d)⁻¹ * SBR d L g p.1 q.1 := by
    rw [svarF_eq_svar]
    have e1 : split d L W ((splitEquiv d L W).symm p) = p :=
      (splitEquiv d L W).apply_symm_apply p
    have e2 : split d L W ((splitEquiv d L W).symm q) = q :=
      (splitEquiv d L W).apply_symm_apply q
    rw [e1, e2]
    rfl
  have h2 : SB d L g p.1 q.1 = ((SBR d L g p.1 q.1 : ℝ) : ℂ) := by
    rw [SB_eq_map_SBR]; rfl
  rw [h1, h2]
  push_cast
  ring

end CoordAlgebra

/-! ## `EECutIdentity` -/

/-! ## `QVPropagated` -/

/-! ## `EEShift` -/

/-! ## Compiled nonempty instances at `d = 3` (the merged `sz0`: `L = 4`, `W = 32`, `g = 1/64`)

`M = 1` is Hermitian; `E = 1`, `u = 1/2`, `Δ = 1/1000`; the labels `(0, 1)` and `(1, 0)` are
two different two-loop labels in `Z_4^3` (constant functions); `κ ≡ 1`.  The cases `u = 0` and
`u + Δ = 999/1000` of `eeShift` exercise the ends of the time window (`0 ≤ u`, `u + Δ < 1`). -/

end RBM.Path

end
