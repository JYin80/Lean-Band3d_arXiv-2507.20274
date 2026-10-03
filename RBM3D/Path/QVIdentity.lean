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

theorem vB_nonneg_diag (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    0 ≤ vB n A A := by
  rw [vB_self]; exact linTrVar_nonneg n A

/-- `linTr` is real-linear in the direction argument, for a finite real-weighted sum of
directions (RBM1D `lin_sum_smul`). -/
private theorem QVForm_linTr_sum_smul {ι : Type*} [Fintype ι] (n : ℕ) (r : ι → ℝ)
    (A : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n (∑ i : ι, (r i : ℂ) • A i) X = ∑ i : ι, r i * linTr n (A i) X := by
  unfold linTr
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ i : ι, Matrix.trace ((r i : ℂ) • A i * X)
      = (r i : ℂ) * Matrix.trace (A i * X) := by
    intro i
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hstep i, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **`v_sum_eq`** (RBM1D `v_sum_eq`): `linTrVar` of a real-weighted sum of directions is the
associated `vB`-quadratic form. -/
theorem v_sum_eq {ι : Type*} [Fintype ι] (n : ℕ) (r : ι → ℝ)
    (A : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTrVar n (∑ i : ι, (r i : ℂ) • A i)
      = ∑ i : ι, ∑ i' : ι, r i * r i' * vB n (A i) (A i') := by
  classical
  have hv : linTrVar n (∑ i : ι, (r i : ℂ) • A i)
      = ∑ c ∈ coordFinset n, (Sizes.seqGvar sz c : ℝ) *
          (∑ i : ι, r i * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2 := by
    rw [QVForm_linTrVar_eq_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [QVForm_linTr_sum_smul]
  rw [hv]
  have hexpand : ∀ c : Sizes.SeqCoord sz, (Sizes.seqGvar sz c : ℝ) *
      (∑ i : ι, r i * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2
      = ∑ i : ι, ∑ i' : ι, (Sizes.seqGvar sz c : ℝ) * r i * r i'
          * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))
          * linTr n (A i') (Sizes.seqXmat sz n (Pi.single c 1)) := by
    intro c
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun c _ => hexpand c]
  rw [show (∑ c ∈ coordFinset n, ∑ i : ι, ∑ i' : ι, (Sizes.seqGvar sz c : ℝ) * r i * r i'
        * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))
        * linTr n (A i') (Sizes.seqXmat sz n (Pi.single c 1)))
      = ∑ i : ι, ∑ c ∈ coordFinset n, ∑ i' : ι, (Sizes.seqGvar sz c : ℝ) * r i * r i'
          * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))
          * linTr n (A i') (Sizes.seqXmat sz n (Pi.single c 1))
      from Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (∑ c ∈ coordFinset n, ∑ i' : ι, (Sizes.seqGvar sz c : ℝ) * r i * r i'
        * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))
        * linTr n (A i') (Sizes.seqXmat sz n (Pi.single c 1)))
      = ∑ i' : ι, ∑ c ∈ coordFinset n, (Sizes.seqGvar sz c : ℝ) * r i * r i'
          * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))
          * linTr n (A i') (Sizes.seqXmat sz n (Pi.single c 1))
      from Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  show (∑ c ∈ coordFinset n, (Sizes.seqGvar sz c : ℝ) * r i * r i'
      * linTr n (A i) (Sizes.seqXmat sz n (Pi.single c 1))
      * linTr n (A i') (Sizes.seqXmat sz n (Pi.single c 1)))
      = r i * r i' * vB n (A i) (A i')
  rw [vB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **The Cauchy–Schwarz bound on `vB`** (RBM1D `abs_vB_le`): `|vB A A'| ≤ √(linTrVar A)
√(linTrVar A')`. -/
theorem abs_vB_le (n : ℕ) (A A' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    |vB n A A'| ≤ Real.sqrt (linTrVar n A) * Real.sqrt (linTrVar n A') := by
  classical
  set f : Sizes.SeqCoord sz → ℝ := fun c =>
    Real.sqrt (Sizes.seqGvar sz c : ℝ) * linTr n A (Sizes.seqXmat sz n (Pi.single c 1))
    with hf_def
  set g : Sizes.SeqCoord sz → ℝ := fun c =>
    Real.sqrt (Sizes.seqGvar sz c : ℝ) * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1))
    with hg_def
  have hfg : ∀ c ∈ coordFinset n, f c * g c = (Sizes.seqGvar sz c : ℝ)
      * linTr n A (Sizes.seqXmat sz n (Pi.single c 1))
      * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1)) := by
    intro c _
    have hsq : Real.sqrt (Sizes.seqGvar sz c : ℝ) * Real.sqrt (Sizes.seqGvar sz c : ℝ)
        = (Sizes.seqGvar sz c : ℝ) := Real.mul_self_sqrt (Sizes.seqGvar sz c).2
    change Real.sqrt (Sizes.seqGvar sz c : ℝ) * linTr n A (Sizes.seqXmat sz n (Pi.single c 1))
        * (Real.sqrt (Sizes.seqGvar sz c : ℝ) * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1)))
        = (Sizes.seqGvar sz c : ℝ) * linTr n A (Sizes.seqXmat sz n (Pi.single c 1))
          * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1))
    conv_rhs => rw [← hsq]
    ring
  have hf2 : ∀ c ∈ coordFinset n,
      f c ^ 2 = (Sizes.seqGvar sz c : ℝ) * linTr n A (Sizes.seqXmat sz n (Pi.single c 1)) ^ 2 := by
    intro c _
    have hsq : Real.sqrt (Sizes.seqGvar sz c : ℝ) ^ 2 = (Sizes.seqGvar sz c : ℝ) :=
      Real.sq_sqrt (Sizes.seqGvar sz c).2
    change (Real.sqrt (Sizes.seqGvar sz c : ℝ) * linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2
        = (Sizes.seqGvar sz c : ℝ) * linTr n A (Sizes.seqXmat sz n (Pi.single c 1)) ^ 2
    conv_rhs => rw [← hsq]
    ring
  have hg2 : ∀ c ∈ coordFinset n,
      g c ^ 2 = (Sizes.seqGvar sz c : ℝ) * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1)) ^ 2 := by
    intro c _
    have hsq : Real.sqrt (Sizes.seqGvar sz c : ℝ) ^ 2 = (Sizes.seqGvar sz c : ℝ) :=
      Real.sq_sqrt (Sizes.seqGvar sz c).2
    change (Real.sqrt (Sizes.seqGvar sz c : ℝ) * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1))) ^ 2
        = (Sizes.seqGvar sz c : ℝ) * linTr n A' (Sizes.seqXmat sz n (Pi.single c 1)) ^ 2
    conv_rhs => rw [← hsq]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (coordFinset n) f g
  have hvBeq : vB n A A' = ∑ c ∈ coordFinset n, f c * g c :=
    (Finset.sum_congr rfl hfg).symm
  have hvAeq : linTrVar n A = ∑ c ∈ coordFinset n, f c ^ 2 := by
    rw [QVForm_linTrVar_eq_sum]
    exact Finset.sum_congr rfl fun c hc => (hf2 c hc).symm
  have hvA'eq : linTrVar n A' = ∑ c ∈ coordFinset n, g c ^ 2 := by
    rw [QVForm_linTrVar_eq_sum]
    exact Finset.sum_congr rfl fun c hc => (hg2 c hc).symm
  rw [← hvBeq, ← hvAeq, ← hvA'eq] at hCS
  have hstep : |vB n A A'| = Real.sqrt ((vB n A A') ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [hstep]
  calc Real.sqrt ((vB n A A') ^ 2) ≤ Real.sqrt (linTrVar n A * linTrVar n A') :=
        Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (linTrVar n A) * Real.sqrt (linTrVar n A') :=
        Real.sqrt_mul (linTrVar_nonneg n A) _


end QVForm

section QVForm2

variable {d : ℕ}

/-! ### (T2) : `linTrVar n (gradMat Φ M)` is the quadratic variation -/

/-- A real-valued-on-Hermitian function has a real derivative along a Hermitian direction
(RBM1D `fderiv_im_eq_zero_of_herm`; the private `StepDecomp_fderiv_im_eq_zero` of
`Path/StepDecomp.lean`, re-proved). -/
private theorem QVForm_fderiv_im_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} {M X : Matrix ι ι ℂ} (hd : DifferentiableAt ℝ Ψ M)
    (hReal : ∀ A, A.IsHermitian → (Ψ A).im = 0) (hM : M.IsHermitian) (hX : X.IsHermitian) :
    (fderiv ℝ Ψ M X).im = 0 := by
  have hadd : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => M + t' • X) X t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const X).const_add M
  have hherm : ∀ t : ℝ, (M + t • X).IsHermitian := fun t => by
    have hcast : M + t • X = M + (t : ℂ) • X := by rw [Complex.coe_smul]
    rw [hcast]
    exact hM.add (hX.smul (Complex.conj_ofReal t))
  have hp0 : HasDerivAt (fun t' : ℝ => Ψ (M + t' • X)) (fderiv ℝ Ψ M X) 0 := by
    have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) := by
      simpa using hd.hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (hadd 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  have hpath0 : ∀ t' : ℝ, (Ψ (M + t' • X)).im = 0 := fun t' => hReal _ (hherm t')
  have him0 : HasDerivAt (fun t' : ℝ => (Ψ (M + t' • X)).im) ((fderiv ℝ Ψ M X).im) 0 := by
    have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) Complex.imCLM.hasFDerivAt hp0
    simpa [Function.comp_def] using h1
  have hconst : (fun t' : ℝ => (Ψ (M + t' • X)).im) = fun _ : ℝ => (0 : ℝ) := funext hpath0
  rw [hconst] at him0
  exact him0.unique (hasDerivAt_const 0 0)

/-- The coordinate matrix of the slice is the coordinate matrix of the coordinate. -/
private theorem QVForm_seqXmat_single (sz : Sizes d) (n : ℕ) (c : CoordF d (sz.L n) (sz.W n)) :
    Sizes.seqXmat sz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) 1)
      = coordinateMatrix d (sz.L n) (sz.W n) c := by
  have hs : Sizes.slice sz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) 1)
      = Pi.single c 1 := by
    funext c'
    change (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) (1 : ℝ) : Sizes.SeqCoord sz → ℝ) ⟨n, c'⟩
      = (Pi.single c (1 : ℝ) : CoordF d (sz.L n) (sz.W n) → ℝ) c'
    by_cases h : c' = c
    · subst h; simp
    · have h' : (⟨n, c'⟩ : Sizes.SeqCoord sz) ≠ ⟨n, c⟩ := fun he =>
        h (eq_of_heq (Sigma.mk.inj he).2)
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
  unfold Sizes.seqXmat coordinateMatrix
  rw [hs]

/-- **`v_gradMat_eq_quadVar`** (RBM1D `v_gradMat_eq_quadVar`): for `Φ` differentiable at `M`,
real-valued on the Hermitian matrices, and `M` Hermitian, the conditional-variance proxy
`linTrVar n (gradMat Φ M)` is the quadratic variation
`Σ_c gvar_c ‖fderiv ℝ Φ M (coordinateMatrix c)‖²` over all coordinates. -/
theorem v_gradMat_eq_quadVar {d : ℕ} (sz : Sizes d) (n : ℕ)
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hd : DifferentiableAt ℝ Φ M) (hReal : ∀ A, A.IsHermitian → (Φ A).im = 0)
    (hM : M.IsHermitian) :
    linTrVar n (gradMat Φ M)
      = ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ)
          * ‖fderiv ℝ Φ M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 := by
  classical
  rw [QVForm_linTrVar_eq_sum]
  unfold coordFinset
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hX := coordinateMatrix_isHermitian d (sz.L n) (sz.W n) c
  change (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
      (linTr n (gradMat Φ M) (Sizes.seqXmat sz n (Pi.single (⟨n, c⟩ : Sizes.SeqCoord sz) 1))) ^ 2
    = _
  rw [QVForm_seqXmat_single sz, ← lin_eq_fderiv sz n M hX]
  have him := QVForm_fderiv_im_eq_zero hd hReal hM hX
  have hz : fderiv ℝ Φ M (coordinateMatrix d (sz.L n) (sz.W n) c)
      = ((fderiv ℝ Φ M (coordinateMatrix d (sz.L n) (sz.W n) c)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hnormsq : ‖fderiv ℝ Φ M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2
      = (fderiv ℝ Φ M (coordinateMatrix d (sz.L n) (sz.W n) c)).re ^ 2 := by
    conv_lhs => rw [hz]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnormsq]

/-! ### Check on the elementary member `A ↦ sin (Re tr A)` -/

/-- The continuous real-linear functional `Re tr`. -/
private def QVForm_g (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (Matrix.trace A).re
      map_add' := fun A B => by simp
      map_smul' := fun r A => by simp }

private theorem QVForm_check_differentiable {d : ℕ} (sz : Sizes d) (n : ℕ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    DifferentiableAt ℝ
      (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) M :=
  have h : ContDiff ℝ 1 (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_sin.comp (QVForm_g (Idx d (sz.L n) (sz.W n))).contDiff)
  h.contDiffAt.differentiableAt one_ne_zero

/-- `v_gradMat_eq_quadVar` on the elementary member `A ↦ sin (Re tr A)`, for every size and every
Hermitian `M`: all three hypotheses are discharged. -/
theorem QVForm_check_v_gradMat_eq_quadVar {d : ℕ} (sz : Sizes d) (n : ℕ)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    linTrVar n (gradMat
        (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
          (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) M)
      = ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ)
          * ‖fderiv ℝ (fun A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
              (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) M
              (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 :=
  v_gradMat_eq_quadVar sz n (QVForm_check_differentiable sz n M)
    (fun _ _ => Complex.ofReal_im _) hM

end QVForm2


/-! ## The loop vocabulary of Step 2 at `n = 2` (RBM2D `Path/Step2Vocab.lean:87-109`)

`loopPM`, `greenBlk` are the merged `RBM3D/Green/Pins.lean` ones; `loop6`, `EE`, `cutDeriv1`,
`cutDeriv2`, `loopDeriv` are RBM2D's definitions with `Z2 L → Zd d L`, `W^2 → W^d`, `SB L → SB d L g`
(R2, R3, and the coupling `g` of `(eq:variancematrix)`), the six-loop being the merged `loopFine`. -/

section Vocab

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- A six-loop `𝓛_{u,σ,a}` at `M` (RBM2D `Path/Step2Vocab.lean:87`). -/
def loop6 (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Fin 6 → Bool)
    (a : Fin 6 → Zd d L) : ℂ :=
  loopFine d L W M (zt E u) σ a

/-- `(𝓔 ⊗ 𝓔)_{u,(+,-),a,a'}` (`defEOTE`, `3_5:176-190`; RBM2D `Path/Step2Vocab.lean:93`), with the
coupling `g` of `S^{(B)}(g)` and the prefactor `W^d`. -/
def EE (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a a' : Zd d L × Zd d L) : ℂ :=
  (W : ℂ) ^ d * ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' *
    (loop6 d L W E u M ![true, false, true, false, true, false] ![a.1, a.2, b', a'.2, a'.1, b] +
      loop6 d L W E u M ![false, true, false, true, false, true] ![a.2, a.1, b', a'.1, a'.2, b])

/-- The derivative of `𝓛_{(+,-),a}` through the first edge `G(+)`, along a direction `X`
(RBM2D `Path/Step2Vocab.lean:99`). -/
def cutDeriv1 (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L × Zd d L) : ℂ :=
  -Matrix.trace (greenBlk d L W E u M true * blockMat d L W X * greenBlk d L W E u M true *
    Eblk d L W a.1 * greenBlk d L W E u M false * Eblk d L W a.2)

/-- The derivative of `𝓛_{(+,-),a}` through the second edge `G(-)`, along `X`
(RBM2D `Path/Step2Vocab.lean:104`). -/
def cutDeriv2 (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L × Zd d L) : ℂ :=
  -Matrix.trace (greenBlk d L W E u M true * Eblk d L W a.1 * greenBlk d L W E u M false *
    blockMat d L W X * greenBlk d L W E u M false * Eblk d L W a.2)

/-- The directional derivative of `𝓛_{u,(+,-),a}` at `M` along `X` (RBM2D
`Path/Step2Vocab.lean:109`). -/
def loopDeriv (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L × Zd d L) : ℂ :=
  deriv (fun y : ℝ => loopPM d L W E u (M + (y : ℂ) • X) a.1 a.2) 0

end Vocab

/-! ## The pinned statements (RBM2D `Path/QVIdentity.lean:345-372`, with `d`, `g`) -/

/-- **Pin E.6a (corrected paper-delta #22, per cut)**: `(𝓔⊗𝓔)_{a,a'}` is the sum over the two
edges `k` of `Σ_α S_α ∂^{(k)}_α 𝓛_a · conj(∂^{(k)}_α 𝓛_{a'})` (diagonal cuts only).  The
identity without the cut split, `Σ_α S_α ∂_α𝓛 conj ∂_α𝓛 = (𝓔⊗𝓔)`, is false (T2049e).  The
dimension `d` and the coupling `g` of `S^{(B)}(g)` are parameters. -/
def EECutIdentity : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ∀ a a' : Zd d L × Zd d L,
      EE d L W g E u M a a' = ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (cutDeriv1 d L W E u M (coordinateMatrix d L W c) a *
            (starRingEnd ℂ) (cutDeriv1 d L W E u M (coordinateMatrix d L W c) a') +
          cutDeriv2 d L W E u M (coordinateMatrix d L W c) a *
            (starRingEnd ℂ) (cutDeriv2 d L W E u M (coordinateMatrix d L W c) a'))

/-- **Pin E.6b (QV of a propagated increment)**: for any coefficients `κ` (the kernel of
`𝒰_{u_{j+1},v}` at the target `a`), `Σ_c gvar_c |Σ_b κ_b ∂_c 𝓛_b|² ≤ 2 Re Σ_{b,b'} κ_b κ̄_{b'}
(𝓔⊗𝓔)_{b,b'}` (Cauchy–Schwarz over the two cuts; the factor `2 = n`). -/
def QVPropagated : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ∀ κ : Zd d L × Zd d L → ℂ,
      ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) *
          ‖∑ b : Zd d L × Zd d L, κ b * loopDeriv d L W E u M (coordinateMatrix d L W c) b‖ ^ 2 ≤
        2 * (∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          κ b * (starRingEnd ℂ) (κ b') * EE d L W g E u M b b').re

/-- **Pin E.6c (one-step time shift of `𝓔⊗𝓔`)**: `‖(𝓔⊗𝓔)_{u+Δ}(M) - (𝓔⊗𝓔)_u(M)‖ ≤
16 N² η_{u+Δ}^{-7} Δ` for Hermitian `M`, `N = (W L)^d` (RBM1D `sqrt_quadVar_time_shift`,
`Gauss/GridQVStep.lean:566`). -/
def EEShift : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u Δ : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → 0 ≤ Δ →
    u + Δ < 1 → ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ a a' : Zd d L × Zd d L,
      ‖EE d L W g E (u + Δ) M a a' - EE d L W g E u M a a'‖ ≤
        16 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * (etaT E (u + Δ))⁻¹ ^ 7 * Δ

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

/-- `tr(blockMat X · A) = Σ_{k,l} X_{kl} A_{e l, e k}` with `e = splitEquiv`. -/
private theorem QVIdentity_trace_blockMat_mul (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (A : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (blockMat d L W X * A) =
      QVIdentity_pair X (fun l k => A (splitEquiv d L W l) (splitEquiv d L W k)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, blockMat, Matrix.submatrix_apply,
    QVIdentity_pair]
  rw [← (splitEquiv d L W).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (splitEquiv d L W).sum_comp]
  simp

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

/-- **From the fine variance to block insertions.**
`Σ_{k,l} svar_{kl} A_{e l,e k} conj B_{e l,e k} = W^d Σ_{b,b'} S^{(B)}_{bb'} tr(A E_b Bᴴ E_{b'})`. -/
private theorem QVIdentity_svar_sum (g : ℝ) (A B : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ k, ∑ l, (svarF d L W g k l : ℂ) *
        (A (splitEquiv d L W l) (splitEquiv d L W k) *
          (starRingEnd ℂ) (B (splitEquiv d L W l) (splitEquiv d L W k))) =
      (W : ℂ) ^ d * ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' *
        Matrix.trace (A * Eblk d L W b * Bᴴ * Eblk d L W b') := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  -- the left side over block indices
  have hL : ∑ k, ∑ l, (svarF d L W g k l : ℂ) *
        (A (splitEquiv d L W l) (splitEquiv d L W k) *
          (starRingEnd ℂ) (B (splitEquiv d L W l) (splitEquiv d L W k))) =
      ∑ p : Vtx d L W, ∑ q : Vtx d L W,
        SB d L g p.1 q.1 * ((W : ℂ) ^ d)⁻¹ * (A q p * (starRingEnd ℂ) (B q p)) := by
    rw [← (splitEquiv d L W).symm.sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← (splitEquiv d L W).symm.sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [QVIdentity_svarF_cast]
    simp only [Equiv.apply_symm_apply]
  have htr : ∀ b b' : Zd d L, Matrix.trace (A * Eblk d L W b * Bᴴ * Eblk d L W b') =
      ∑ q : Vtx d L W, ∑ p : Vtx d L W,
        (if p.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) * (if q.1 = b' then ((W : ℂ) ^ d)⁻¹ else 0) *
          (A q p * (starRingEnd ℂ) (B q p)) := by
    intro b b'
    simp only [Matrix.trace, Matrix.diag, Eblk, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.1 = b'
    · simp only [hq, ite_true]
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p.1 = b
      · simp only [hp, ite_true, RCLike.star_def]; ring
      · simp [hp]
    · simp [hq]
  have hcollapse : ∀ (x y : Vtx d L W) (C : ℂ),
      ∑ b : Zd d L, ∑ b' : Zd d L, (W : ℂ) ^ d * (SB d L g b b' *
        ((if x.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) * (if y.1 = b' then ((W : ℂ) ^ d)⁻¹ else 0) *
          C)) =
        (W : ℂ) ^ d * (SB d L g x.1 y.1 * (((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * C)) := by
    intro x y C
    rw [Finset.sum_eq_single x.1]
    · rw [Finset.sum_eq_single y.1]
      · simp
      · intro b' _ hb'; simp [Ne.symm hb']
      · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hL]
  simp only [htr, Finset.mul_sum]
  rw [QVIdentity_sum_swap4, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hcollapse]
  have hWd : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ hW
  field_simp

end CoordAlgebra

/-! ## `EECutIdentity` -/

section Cuts

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- `G(σ)^* = G(!σ)` (private copies exist in `Induction/Split.lean:250`,
`Induction/Contract.lean:224`, `Green/Pins.lean:367`; RBM2D `Hierarchy/Loops.lean`
`Gsig_conjTranspose`). -/
private theorem QVIdentity_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

private theorem QVIdentity_loop6_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (σ : Fin 6 → Bool) (x : Fin 6 → Zd d L) :
    loop6 d L W E u M σ x = Matrix.trace (greenBlk d L W E u M (σ 0) * Eblk d L W (x 0) *
      greenBlk d L W E u M (σ 1) * Eblk d L W (x 1) * greenBlk d L W E u M (σ 2) *
      Eblk d L W (x 2) * greenBlk d L W E u M (σ 3) * Eblk d L W (x 3) *
      greenBlk d L W E u M (σ 4) * Eblk d L W (x 4) * greenBlk d L W E u M (σ 5) *
      Eblk d L W (x 5)) := by
  simp only [loop6, loopFine, loopM, greenBlk, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, Matrix.mul_one, Matrix.mul_assoc]
  rfl

/-- The edge-1 derivative as a pairing: `∂^{(1)}_X 𝓛_a = -tr(X̂ · G₊E_{a₁}G₋E_{a₂}G₊)`. -/
private theorem QVIdentity_cut1_eq (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a : Zd d L × Zd d L) :
    cutDeriv1 d L W E u M X a = -Matrix.trace (blockMat d L W X * (greenBlk d L W E u M true *
      Eblk d L W a.1 * greenBlk d L W E u M false * Eblk d L W a.2 *
      greenBlk d L W E u M true)) := by
  rw [cutDeriv1]
  congr 1
  calc Matrix.trace (greenBlk d L W E u M true * blockMat d L W X * greenBlk d L W E u M true *
          Eblk d L W a.1 * greenBlk d L W E u M false * Eblk d L W a.2)
      = Matrix.trace (greenBlk d L W E u M true * (blockMat d L W X *
          greenBlk d L W E u M true *
          Eblk d L W a.1 * greenBlk d L W E u M false * Eblk d L W a.2)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((blockMat d L W X * greenBlk d L W E u M true *
          Eblk d L W a.1 * greenBlk d L W E u M false * Eblk d L W a.2) *
          greenBlk d L W E u M true) :=
        Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The edge-2 derivative as a pairing: `∂^{(2)}_X 𝓛_a = -tr(X̂ · G₋E_{a₂}G₊E_{a₁}G₋)`. -/
private theorem QVIdentity_cut2_eq (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a : Zd d L × Zd d L) :
    cutDeriv2 d L W E u M X a = -Matrix.trace (blockMat d L W X * (greenBlk d L W E u M false *
      Eblk d L W a.2 * greenBlk d L W E u M true * Eblk d L W a.1 *
      greenBlk d L W E u M false)) := by
  rw [cutDeriv2]
  congr 1
  calc Matrix.trace (greenBlk d L W E u M true * Eblk d L W a.1 * greenBlk d L W E u M false *
          blockMat d L W X * greenBlk d L W E u M false * Eblk d L W a.2)
      = Matrix.trace ((greenBlk d L W E u M true * Eblk d L W a.1 *
          greenBlk d L W E u M false) *
          (blockMat d L W X * greenBlk d L W E u M false * Eblk d L W a.2)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((blockMat d L W X * greenBlk d L W E u M false * Eblk d L W a.2) *
          (greenBlk d L W E u M true * Eblk d L W a.1 * greenBlk d L W E u M false)) :=
        Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- A coordinate sum of a cut pairing, in block form. -/
private theorem QVIdentity_cut_pair (g : ℝ)
    (A : Zd d L × Zd d L → Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (f : Matrix (Idx d L W) (Idx d L W) ℂ → Zd d L × Zd d L → ℂ)
    (hf : ∀ X a, f X a = -Matrix.trace (blockMat d L W X * A a)) (a a' : Zd d L × Zd d L) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (f (coordinateMatrix d L W c) a * (starRingEnd ℂ) (f (coordinateMatrix d L W c) a')) =
      (W : ℂ) ^ d * ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' *
        Matrix.trace (A a * Eblk d L W b * (A a')ᴴ * Eblk d L W b') := by
  simp only [hf, QVIdentity_trace_blockMat_mul, map_neg, neg_mul_neg]
  rw [QVIdentity_coord_sum, QVIdentity_svar_sum]

private theorem QVIdentity_greenBlk_conjTranspose (E u : ℝ) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (σ : Bool) :
    (greenBlk d L W E u M σ)ᴴ = greenBlk d L W E u M (!σ) :=
  QVIdentity_Gres_conjTranspose (hM.submatrix _) _ σ

/-- Swapping the summation labels of an `S^{(B)}`-weighted double sum. -/
private theorem QVIdentity_SB_swap (g : ℝ) (F : Zd d L → Zd d L → ℂ) :
    ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' * F b' b =
      ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' * F b b' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [show SB d L g b' b = SB d L g b b' from congrFun (congrFun (SB_transpose d L g) b) b']

end Cuts

/-- **`eeCutIdentity`**: the corrected, per-cut `(𝓔⊗𝓔)` identity (paper-delta #22, T2049e).
Each cut pairs through `svarF = W^{-d} S^{(B)}` into one of the two six-loops of `EE`
(RBM2D `Path/QVIdentity.lean:378`). -/
theorem eeCutIdentity : EECutIdentity := by
  intro d L W g _ _ E u _ _ _ _ M hM a a'
  have hG := QVIdentity_greenBlk_conjTranspose (d := d) (L := L) (W := W) E u hM
  have hE : ∀ b : Zd d L, (Eblk d L W b)ᴴ = Eblk d L W b := fun b => Eblk_isHermitian b
  have h1 : ∀ x y : Zd d L,
      loop6 d L W E u M ![true, false, true, false, true, false] ![a.1, a.2, x, a'.2, a'.1, y] =
        Matrix.trace ((greenBlk d L W E u M true * Eblk d L W a.1 * greenBlk d L W E u M false *
          Eblk d L W a.2 * greenBlk d L W E u M true) * Eblk d L W x *
          (greenBlk d L W E u M true * Eblk d L W a'.1 * greenBlk d L W E u M false *
            Eblk d L W a'.2 * greenBlk d L W E u M true)ᴴ * Eblk d L W y) := by
    intro x y
    rw [QVIdentity_loop6_eq]
    simp [Matrix.conjTranspose_mul, hG, hE, Matrix.mul_assoc]
  have h2 : ∀ x y : Zd d L,
      loop6 d L W E u M ![false, true, false, true, false, true] ![a.2, a.1, x, a'.1, a'.2, y] =
        Matrix.trace ((greenBlk d L W E u M false * Eblk d L W a.2 * greenBlk d L W E u M true *
          Eblk d L W a.1 * greenBlk d L W E u M false) * Eblk d L W x *
          (greenBlk d L W E u M false * Eblk d L W a'.2 * greenBlk d L W E u M true *
            Eblk d L W a'.1 * greenBlk d L W E u M false)ᴴ * Eblk d L W y) := by
    intro x y
    rw [QVIdentity_loop6_eq]
    simp [Matrix.conjTranspose_mul, hG, hE, Matrix.mul_assoc]
  rw [EE]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [QVIdentity_cut_pair g _ _ (QVIdentity_cut1_eq E u M) a a',
    QVIdentity_cut_pair g _ _ (QVIdentity_cut2_eq E u M) a a']
  simp only [h1, h2]
  exact congrArg₂ (· + ·) (congrArg ((W : ℂ) ^ d * ·) (QVIdentity_SB_swap g _))
    (congrArg ((W : ℂ) ^ d * ·) (QVIdentity_SB_swap g _))

/-! ## `QVPropagated` -/

section Deriv

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

set_option linter.unusedDecidableInType false in
/-- The trace of a differentiable matrix path (the `DecidableEq` instance is used by the
`L2Operator` norm). -/
private theorem QVIdentity_hasDerivAt_trace {n : Type*} [Fintype n] [DecidableEq n]
    {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The affine line `s ↦ M + s • A` has derivative `A` (RBM2D `Gauss/Envelope.lean:136`,
`hasDerivAt_line`; the merged copies are `private`). -/
private theorem QVIdentity_hasDerivAt_line {n : Type*} [Fintype n] [DecidableEq n]
    (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

/-- **`loopDeriv = cutDeriv1 + cutDeriv2`** along any direction `X`, at a Hermitian `M`, for
`|E| < 2` and `u < 1` (so `Im z_u ≠ 0`). -/
private theorem QVIdentity_loopDeriv_eq {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (X : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L × Zd d L) :
    loopDeriv d L W E u M X a = cutDeriv1 d L W E u M X a + cutDeriv2 d L W E u M X a := by
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hz : (zt E u).im ≠ 0 := by
    rw [zt_im]
    exact (mul_pos (by linarith) (mE_im_pos hE)).ne'
  set Hy : ℝ → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun y => blockMat d L W M + (y : ℂ) • blockMat d L W X with hHy
  have hH0 : Hy 0 = blockMat d L W M := by simp [hHy]
  have hline : HasDerivAt Hy (blockMat d L W X) 0 := QVIdentity_hasDerivAt_line _ _ 0
  have hG : ∀ σ : Bool, HasDerivAt (fun y => Gres (Hy y) (zt E u) σ)
      (-(greenBlk d L W E u M σ * blockMat d L W X * greenBlk d L W E u M σ)) 0 := by
    intro σ
    cases σ with
    | true =>
        have h := hasDerivAt_green_moving hline (hasDerivAt_const (0 : ℝ) (zt E u))
          (by rw [hH0]; exact hH) hz
        simpa [hH0, greenBlk] using h
    | false =>
        have hz' : ((starRingEnd ℂ) (zt E u)).im ≠ 0 := by simpa using hz
        have h := hasDerivAt_green_moving hline
          (hasDerivAt_const (0 : ℝ) ((starRingEnd ℂ) (zt E u))) (by rw [hH0]; exact hH) hz'
        simpa [hH0, greenBlk, Gres] using h
  have hfun : (fun y : ℝ => loopPM d L W E u (M + (y : ℂ) • X) a.1 a.2) =
      fun y => Matrix.trace (Gres (Hy y) (zt E u) true * Eblk d L W a.1 *
        (Gres (Hy y) (zt E u) false * Eblk d L W a.2)) := by
    funext y
    simp only [loopPM, loopFine, loopM, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, Matrix.mul_one, hHy, blockMat, Matrix.submatrix_add, Matrix.submatrix_smul]
    simp [Matrix.mul_assoc]
  have hD : HasDerivAt (fun y => Matrix.trace (Gres (Hy y) (zt E u) true * Eblk d L W a.1 *
        (Gres (Hy y) (zt E u) false * Eblk d L W a.2)))
      (Matrix.trace (-(greenBlk d L W E u M true * blockMat d L W X *
            greenBlk d L W E u M true) *
          Eblk d L W a.1 * (Gres (Hy 0) (zt E u) false * Eblk d L W a.2) +
        Gres (Hy 0) (zt E u) true * Eblk d L W a.1 *
          (-(greenBlk d L W E u M false * blockMat d L W X * greenBlk d L W E u M false) *
            Eblk d L W a.2))) 0 :=
    QVIdentity_hasDerivAt_trace
      (((hG true).mul_const (Eblk d L W a.1)).mul ((hG false).mul_const (Eblk d L W a.2)))
  rw [loopDeriv, hfun, hD.deriv, cutDeriv1, cutDeriv2, hH0]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_add, Matrix.trace_neg,
    Matrix.mul_assoc, greenBlk]

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
private theorem QVIdentity_norm_add_sq_le (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h0 := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- `‖x‖² = Re(x · conj x)`, as a complex identity. -/
private theorem QVIdentity_mul_conj (x : ℂ) : x * (starRingEnd ℂ) x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Deriv

/-- **`qvPropagated`**: Cauchy–Schwarz over the two cuts (factor `2 = n`), then
`eeCutIdentity` (RBM2D `Path/QVIdentity.lean:487`). -/
theorem qvPropagated : QVPropagated := by
  intro d L W g _ _ E u hL hE hu0 hu M hM κ
  set P : CoordF d L W → ℂ := fun c =>
    ∑ b : Zd d L × Zd d L, κ b * cutDeriv1 d L W E u M (coordinateMatrix d L W c) b with hP
  set Q : CoordF d L W → ℂ := fun c =>
    ∑ b : Zd d L × Zd d L, κ b * cutDeriv2 d L W E u M (coordinateMatrix d L W c) b with hQ
  have hsplit : ∀ c, ∑ b : Zd d L × Zd d L,
      κ b * loopDeriv d L W E u M (coordinateMatrix d L W c) b = P c + Q c := by
    intro c
    simp only [hP, hQ, QVIdentity_loopDeriv_eq hE hu hM, mul_add, Finset.sum_add_distrib]
  -- the complex identity
  have hkey : ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (P c * (starRingEnd ℂ) (P c) + Q c * (starRingEnd ℂ) (Q c)) =
      ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * EE d L W g E u M b b' := by
    have hPP : ∀ c, P c * (starRingEnd ℂ) (P c) + Q c * (starRingEnd ℂ) (Q c) =
        ∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L, κ b * (starRingEnd ℂ) (κ b') *
          (cutDeriv1 d L W E u M (coordinateMatrix d L W c) b *
              (starRingEnd ℂ) (cutDeriv1 d L W E u M (coordinateMatrix d L W c) b') +
            cutDeriv2 d L W E u M (coordinateMatrix d L W c) b *
              (starRingEnd ℂ) (cutDeriv2 d L W E u M (coordinateMatrix d L W c) b')) := by
      intro c
      simp only [hP, hQ, map_sum, map_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [hPP, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [eeCutIdentity d L W g E u hL hE hu0 hu M hM b b', Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hre : ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * (‖P c‖ ^ 2 + ‖Q c‖ ^ 2) =
      (∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * EE d L W g E u M b b').re := by
    rw [← hkey, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [QVIdentity_mul_conj, QVIdentity_mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  simp only [hsplit]
  rw [← hre, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hg : (0 : ℝ) ≤ (gvarF d L W g c : ℝ) := (gvarF d L W g c).2
  have := QVIdentity_norm_add_sq_le (P c) (Q c)
  nlinarith

/-! ## `EEShift` -/

section Shift

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- Product bound for a signed Green / block-insertion word (port of RBM1D
`norm_prodList_le_pow`, with separate bounds `K` for `G` and `w` for `E_b`). -/
private theorem QVIdentity_norm_foldr_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {K w : ℝ} (hK : 0 ≤ K) (hw : 0 ≤ w) (hG : ∀ σ, ‖Gres H z σ‖ ≤ K)
    (hE : ∀ b, ‖Eblk d L W b‖ ≤ w) (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖ ≤ (K * w) ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ']
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      exact mul_le_mul (mul_le_mul (hG p.1) (hE p.2) (norm_nonneg _) hK) ih (norm_nonneg _)
        (mul_nonneg hK hw)

/-- Telescoping bound for two signed Green / block-insertion words (port of RBM1D
`norm_prodList_sub_le`, `Gauss/GridQVStep.lean:180` at `86573b9`). -/
private theorem QVIdentity_norm_foldr_sub_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z₁ z₂ : ℂ} {K w δ : ℝ} (hK : 0 ≤ K) (hw : 0 ≤ w) (hδ : 0 ≤ δ)
    (hG₁ : ∀ σ, ‖Gres H z₁ σ‖ ≤ K) (hG₂ : ∀ σ, ‖Gres H z₂ σ‖ ≤ K)
    (hE : ∀ b, ‖Eblk d L W b‖ ≤ w) (hsub : ∀ σ, ‖Gres H z₁ σ - Gres H z₂ σ‖ ≤ δ)
    (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p M => Gres H z₁ p.1 * Eblk d L W p.2 * M)
          (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) -
        l.foldr (fun p M => Gres H z₂ p.1 * Eblk d L W p.2 * M) 1‖ ≤
      (l.length : ℝ) * δ * w * (K * w) ^ (l.length - 1) := by
  induction l with
  | nil => simp
  | cons p l ih =>
      set P₁ := l.foldr (fun p M => Gres H z₁ p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
      set P₂ := l.foldr (fun p M => Gres H z₂ p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
      have hP₁ : ‖P₁‖ ≤ (K * w) ^ l.length := QVIdentity_norm_foldr_le hK hw hG₁ hE l
      have hsplit : Gres H z₁ p.1 * Eblk d L W p.2 * P₁ - Gres H z₂ p.1 * Eblk d L W p.2 * P₂ =
          (Gres H z₁ p.1 - Gres H z₂ p.1) * Eblk d L W p.2 * P₁ +
            Gres H z₂ p.1 * Eblk d L W p.2 * (P₁ - P₂) := by noncomm_ring
      simp only [List.foldr_cons, List.length_cons]
      rw [hsplit]
      have hA : ‖(Gres H z₁ p.1 - Gres H z₂ p.1) * Eblk d L W p.2 * P₁‖ ≤
          δ * w * (K * w) ^ l.length := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        exact mul_le_mul (mul_le_mul (hsub p.1) (hE p.2) (norm_nonneg _) hδ) hP₁ (norm_nonneg _)
          (mul_nonneg hδ hw)
      have hB : ‖Gres H z₂ p.1 * Eblk d L W p.2 * (P₁ - P₂)‖ ≤
          K * w * ((l.length : ℝ) * δ * w * (K * w) ^ (l.length - 1)) := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        exact mul_le_mul (mul_le_mul (hG₂ p.1) (hE p.2) (norm_nonneg _) hK) ih (norm_nonneg _)
          (mul_nonneg hK hw)
      have hC : K * w * ((l.length : ℝ) * δ * w * (K * w) ^ (l.length - 1)) =
          (l.length : ℝ) * δ * w * (K * w) ^ l.length := by
        rcases Nat.eq_zero_or_pos l.length with h0 | hpos
        · rw [h0]; simp
        · obtain ⟨k, hk⟩ : ∃ k, l.length = k + 1 := ⟨l.length - 1, by omega⟩
          rw [hk, Nat.add_sub_cancel, pow_succ]
          push_cast
          ring
      refine (norm_add_le _ _).trans ?_
      rw [Nat.add_sub_cancel]
      push_cast
      nlinarith [hA, hB, hC]

/-- The `S^{(B)}` rows have total norm `1`. -/
private theorem QVIdentity_sum_norm_SB (g : ℝ) (hL : 3 ≤ L) (b : Zd d L) :
    ∑ b' : Zd d L, ‖SB d L g b b'‖ = 1 := sum_norm_SB_row d L g hL b

/-- The spectral parameter moves by `Δ` in norm: `‖z_{u+Δ} - z_u‖ = Δ` (`|m| = 1`). -/
private theorem QVIdentity_norm_zt_sub {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ) :
    ‖zt E (u + Δ) - zt E u‖ = Δ := by
  have h : zt E (u + Δ) - zt E u = (-(Δ : ℂ)) * mE E := by
    simp only [zt]; push_cast; ring
  rw [h, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ,
    norm_mE hE.le, mul_one]

/-- Resolvent bounds at the two times `u ≤ u + Δ`, with `η = η_{u+Δ}`. -/
private theorem QVIdentity_Gres_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {E u Δ : ℝ}
    (hE : |E| < 2) (hΔ : 0 ≤ Δ)
    (huΔ : u + Δ < 1) {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    (∀ σ, ‖Gres H (zt E u) σ‖ ≤ (etaT E (u + Δ))⁻¹) ∧
      (∀ σ, ‖Gres H (zt E (u + Δ)) σ‖ ≤ (etaT E (u + Δ))⁻¹) ∧
      (∀ σ, ‖Gres H (zt E (u + Δ)) σ - Gres H (zt E u) σ‖ ≤
        Δ * (etaT E (u + Δ))⁻¹ ^ 2) := by
  have hm := mE_im_pos hE
  have hη : 0 < etaT E (u + Δ) := etaT_pos hE huΔ
  have him1 : etaT E (u + Δ) ≤ |(zt E u).im| := by
    rw [zt_im, etaT]
    refine le_trans ?_ (le_abs_self _)
    nlinarith
  have him2 : etaT E (u + Δ) ≤ |(zt E (u + Δ)).im| := by
    rw [zt_im, etaT]
    exact le_abs_self _
  have hG1 : ∀ σ, ‖Gres H (zt E u) σ‖ ≤ (etaT E (u + Δ))⁻¹ :=
    norm_Gsig_le_inv_eta hH hη him1
  have hG2 : ∀ σ, ‖Gres H (zt E (u + Δ)) σ‖ ≤ (etaT E (u + Δ))⁻¹ :=
    norm_Gsig_le_inv_eta hH hη him2
  refine ⟨hG1, hG2, fun σ => ?_⟩
  have hne1 : (zt E u).im ≠ 0 := fun h => by
    rw [h, abs_zero] at him1; linarith
  have hne2 : (zt E (u + Δ)).im ≠ 0 := fun h => by
    rw [h, abs_zero] at him2; linarith
  have hU1 := Ind.isUnit_sub_zSig hH hne2 σ
  have hU2 := Ind.isUnit_sub_zSig hH hne1 σ
  have heq : Gres H (zt E (u + Δ)) σ - Gres H (zt E u) σ =
      (Ind.zSig (zt E (u + Δ)) σ - Ind.zSig (zt E u) σ) •
        (Gres H (zt E (u + Δ)) σ * Gres H (zt E u) σ) := by
    exact sub_eq_iff_eq_add'.mpr (Ind.Gres_eq_add_smul_mul hU1 hU2)
  rw [heq]
  refine (norm_smul_le _ _).trans ?_
  rw [Ind.norm_zSig_sub_zSig, QVIdentity_norm_zt_sub hE hΔ]
  calc Δ * ‖Gres H (zt E (u + Δ)) σ * Gres H (zt E u) σ‖
      ≤ Δ * ((etaT E (u + Δ))⁻¹ * (etaT E (u + Δ))⁻¹) :=
        mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
          (mul_le_mul (hG2 σ) (hG1 σ) (norm_nonneg _) (inv_nonneg.mpr hη.le))) hΔ
    _ = Δ * (etaT E (u + Δ))⁻¹ ^ 2 := by ring

/-- One six-loop moves by at most `N · 6 Δ η⁻² W^{-d} (η⁻¹ W^{-d})⁵` between `u` and `u + Δ`,
`N = (L W)^d`. -/
private theorem QVIdentity_loop6_shift {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ)
    (huΔ : u + Δ < 1) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (σ : Fin 6 → Bool) (x : Fin 6 → Zd d L) :
    ‖loop6 d L W E (u + Δ) M σ x - loop6 d L W E u M σ x‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) * (6 * (Δ * (etaT E (u + Δ))⁻¹ ^ 2) *
        ((W : ℝ) ^ d)⁻¹ * ((etaT E (u + Δ))⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ 5) := by
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hη : 0 < etaT E (u + Δ) := etaT_pos hE huΔ
  obtain ⟨hG1, hG2, hsub⟩ := QVIdentity_Gres_shift (E := E) (u := u) hE hΔ huΔ hH
  have hlen : ((loopOf σ x).σ.zip (loopOf σ x).a).length = 6 := by simp [loopOf]
  have h := QVIdentity_norm_foldr_sub_le (inv_nonneg.mpr hη.le) (by positivity)
    (mul_nonneg hΔ (by positivity)) hG2 hG1 (norm_Eblk_le_inv_W_sq d L W) hsub
    ((loopOf σ x).σ.zip (loopOf σ x).a)
  rw [hlen] at h
  rw [loop6, loop6, loopFine, loopFine, loopM_eq_loopL, loopM_eq_loopL, loopL, loopL,
    ← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine h.trans_eq ?_
  norm_num

/-- **`eeShift`**: the one-step time shift of `(𝓔⊗𝓔)`, `‖ΔEE‖ ≤ 16 N² η_{u+Δ}^{-7} Δ`,
`N = (W L)^d`.  Proof: six `E_b` factors give `w⁶`, `w = W^{-d}`; with the prefactor `W^d` and the
unit row sums of `S^{(B)}` the bound is `12 L^d N W^{-5d} η⁻⁷ Δ ≤ 16 N² η⁻⁷ Δ`
(RBM2D `Path/QVIdentity.lean:705`, with `W² → W^d`, `L² → L^d`). -/
theorem eeShift : EEShift := by
  intro d L W g _ _ E u Δ hL hE hu0 hΔ huΔ M hM a a'
  set η := etaT E (u + Δ) with hηdef
  have hη : 0 < η := etaT_pos hE huΔ
  set N : ℝ := (Fintype.card (Vtx d L W) : ℝ) with hNdef
  set w : ℝ := ((W : ℝ) ^ d)⁻¹ with hwdef
  set B : ℝ := N * (6 * (Δ * η⁻¹ ^ 2) * w * (η⁻¹ * w) ^ 5) with hBdef
  have hloop : ∀ σ x, ‖loop6 d L W E (u + Δ) M σ x - loop6 d L W E u M σ x‖ ≤ B :=
    fun σ x => QVIdentity_loop6_shift hE hΔ huΔ hM σ x
  have hB0 : 0 ≤ B := by positivity
  have hdiff : EE d L W g E (u + Δ) M a a' - EE d L W g E u M a a' =
      (W : ℂ) ^ d * ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' *
        ((loop6 d L W E (u + Δ) M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b] -
          loop6 d L W E u M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b]) +
         (loop6 d L W E (u + Δ) M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b] -
          loop6 d L W E u M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b])) := by
    rw [EE, EE, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  have hsum : ‖∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' *
        ((loop6 d L W E (u + Δ) M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b] -
          loop6 d L W E u M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b]) +
         (loop6 d L W E (u + Δ) M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b] -
          loop6 d L W E u M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b]))‖ ≤ (L : ℝ) ^ d * (2 * B) := by
    refine (norm_sum_le _ _).trans ?_
    have hrow : ∀ b : Zd d L, ‖∑ b' : Zd d L, SB d L g b b' *
        ((loop6 d L W E (u + Δ) M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b] -
          loop6 d L W E u M ![true, false, true, false, true, false]
            ![a.1, a.2, b', a'.2, a'.1, b]) +
         (loop6 d L W E (u + Δ) M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b] -
          loop6 d L W E u M ![false, true, false, true, false, true]
            ![a.2, a.1, b', a'.1, a'.2, b]))‖ ≤ 2 * B := by
      intro b
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b' : Zd d L, ‖SB d L g b b' *
          ((loop6 d L W E (u + Δ) M ![true, false, true, false, true, false]
              ![a.1, a.2, b', a'.2, a'.1, b] -
            loop6 d L W E u M ![true, false, true, false, true, false]
              ![a.1, a.2, b', a'.2, a'.1, b]) +
           (loop6 d L W E (u + Δ) M ![false, true, false, true, false, true]
              ![a.2, a.1, b', a'.1, a'.2, b] -
            loop6 d L W E u M ![false, true, false, true, false, true]
              ![a.2, a.1, b', a'.1, a'.2, b]))‖
          ≤ ∑ b' : Zd d L, ‖SB d L g b b'‖ * (2 * B) := by
            refine Finset.sum_le_sum fun b' _ => ?_
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (norm_add_le _ _).trans ?_
            linarith [hloop ![true, false, true, false, true, false]
              ![a.1, a.2, b', a'.2, a'.1, b],
              hloop ![false, true, false, true, false, true] ![a.2, a.1, b', a'.1, a'.2, b]]
        _ = 2 * B := by rw [← Finset.sum_mul, QVIdentity_sum_norm_SB g hL b, one_mul]
    calc ∑ b : Zd d L, _ ≤ ∑ _b : Zd d L, 2 * B := Finset.sum_le_sum fun b _ => hrow b
      _ = (L : ℝ) ^ d * (2 * B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [Zd, ZMod.card]
  -- the final arithmetic
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  have hW0 : (0 : ℝ) < W := by linarith
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hwdef]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have hWw : (W : ℝ) ^ d * w = 1 := by
    rw [hwdef, mul_inv_cancel₀ (by positivity)]
  have hNval : N = (((W * L) ^ d : ℕ) : ℝ) := by
    rw [hNdef, card_BlockIndex]
    push_cast
    ring
  have hLN : (L : ℝ) ^ d ≤ N := by
    rw [hNval]
    push_cast
    rw [mul_pow]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hW1)
  have hN0 : 0 ≤ N := by positivity
  have hι : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hw5 : w ^ 5 ≤ 1 := pow_le_one₀ hw0 hw1
  rw [hdiff, norm_mul, norm_pow, Complex.norm_natCast, ← hNval]
  calc (W : ℝ) ^ d * ‖_‖ ≤ (W : ℝ) ^ d * ((L : ℝ) ^ d * (2 * B)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 12 * ((W : ℝ) ^ d * w) * (L : ℝ) ^ d * N * w ^ 5 * η⁻¹ ^ 7 * Δ := by
        rw [hBdef]; ring
    _ = 12 * (L : ℝ) ^ d * N * w ^ 5 * η⁻¹ ^ 7 * Δ := by rw [hWw]; ring
    _ ≤ 12 * N * N * 1 * η⁻¹ ^ 7 * Δ := by
        have h7 : 0 ≤ η⁻¹ ^ 7 * Δ := mul_nonneg (pow_nonneg hι 7) hΔ
        have h1 : (L : ℝ) ^ d * N * w ^ 5 ≤ N * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hLN hN0) hw5 (pow_nonneg hw0 5)
            (mul_nonneg hN0 hN0)
        nlinarith
    _ ≤ 16 * N ^ 2 * η⁻¹ ^ 7 * Δ := by
        have h7 : 0 ≤ N ^ 2 * η⁻¹ ^ 7 * Δ := by positivity
        nlinarith

end Shift

/-! ## Compiled nonempty instances at `d = 3` (the merged `sz0`: `L = 4`, `W = 32`, `g = 1/64`)

`M = 1` is Hermitian; `E = 1`, `u = 1/2`, `Δ = 1/1000`; the labels `(0, 1)` and `(1, 0)` are
two different two-loop labels in `Z_4^3` (constant functions); `κ ≡ 1`.  The cases `u = 0` and
`u + Δ = 999/1000` of `eeShift` exercise the ends of the time window (`0 ≤ u`, `u + Δ < 1`). -/

section Instances

open RBM.Gauss.SizesInst

/-- `eeCutIdentity` at `d = 3`, `L = 4`, `W = 32`, `g = 1/64`, `M = 1`, `a ≠ a'`. -/
example : EE 3 4 32 (1 / 64) 1 (1 / 2) 1 (0, 1) (1, 0) =
    ∑ c : CoordF 3 4 32, ((gvarF 3 4 32 (1 / 64) c : ℝ) : ℂ) *
      (cutDeriv1 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (0, 1) *
          (starRingEnd ℂ) (cutDeriv1 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (1, 0)) +
        cutDeriv2 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (0, 1) *
          (starRingEnd ℂ) (cutDeriv2 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (1, 0))) :=
  eeCutIdentity 3 4 32 (1 / 64) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)

/-- `qvPropagated` at the same data with `κ ≡ 1`. -/
example : ∑ c : CoordF 3 4 32, (gvarF 3 4 32 (1 / 64) c : ℝ) *
      ‖∑ b : Zd 3 4 × Zd 3 4, (fun _ => (1 : ℂ)) b *
        loopDeriv 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) b‖ ^ 2 ≤
    2 * (∑ b : Zd 3 4 × Zd 3 4, ∑ b' : Zd 3 4 × Zd 3 4,
      (fun _ => (1 : ℂ)) b * (starRingEnd ℂ) ((fun _ => (1 : ℂ)) b') *
        EE 3 4 32 (1 / 64) 1 (1 / 2) 1 b b').re :=
  qvPropagated 3 4 32 (1 / 64) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 Matrix.isHermitian_one (fun _ => 1)

/-- `eeShift` at `u = 1/2`, `Δ = 1/1000`, `a ≠ a'`. -/
example : ‖EE 3 4 32 (1 / 64) 1 (1 / 2 + 1 / 1000) 1 (0, 1) (1, 0) -
      EE 3 4 32 (1 / 64) 1 (1 / 2) 1 (0, 1) (1, 0)‖ ≤
    16 * (((32 * 4) ^ 3 : ℕ) : ℝ) ^ 2 * (etaT 1 (1 / 2 + 1 / 1000))⁻¹ ^ 7 * (1 / 1000) :=
  eeShift 3 4 32 (1 / 64) 1 (1 / 2) (1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)

/-- `eeShift` at the lower end of the window, `u = 0`. -/
example : ‖EE 3 4 32 (1 / 64) 1 (0 + 1 / 1000) 1 (0, 1) (1, 0) -
      EE 3 4 32 (1 / 64) 1 0 1 (0, 1) (1, 0)‖ ≤
    16 * (((32 * 4) ^ 3 : ℕ) : ℝ) ^ 2 * (etaT 1 (0 + 1 / 1000))⁻¹ ^ 7 * (1 / 1000) :=
  eeShift 3 4 32 (1 / 64) 1 0 (1 / 1000) (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)

/-- `eeShift` at the upper end of the window, `u + Δ = 999/1000`. -/
example : ‖EE 3 4 32 (1 / 64) 1 (998 / 1000 + 1 / 1000) 1 (0, 1) (1, 0) -
      EE 3 4 32 (1 / 64) 1 (998 / 1000) 1 (0, 1) (1, 0)‖ ≤
    16 * (((32 * 4) ^ 3 : ℕ) : ℝ) ^ 2 * (etaT 1 (998 / 1000 + 1 / 1000))⁻¹ ^ 7 * (1 / 1000) :=
  eeShift 3 4 32 (1 / 64) 1 (998 / 1000) (1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)

/-- `v_gradMat_eq_quadVar` at `sz0`, size index `0`, on the elementary member
`A ↦ sin (Re tr A)` at the Hermitian matrix `1`: all three hypotheses discharged. -/
example : linTrVar (sz := sz0) 0 (gradMat
        (fun A : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
          (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) 1)
      = ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ)
          * ‖fderiv ℝ (fun A : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
              (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) 1
              (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c)‖ ^ 2 :=
  QVForm_check_v_gradMat_eq_quadVar sz0 0 Matrix.isHermitian_one

/-- `abs_vB_le` at `sz0`, size index `0`. -/
example : |vB (sz := sz0) 0 (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)|
    ≤ Real.sqrt (linTrVar (sz := sz0) 0
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) *
      Real.sqrt (linTrVar (sz := sz0) 0
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) :=
  abs_vB_le 0 1 1

/-- `v_sum_eq` at `sz0`, size index `0`, two directions `1`, `1` with weights `1`, `1`. -/
example : linTrVar (sz := sz0) 0 (∑ i : Fin 2, (((fun _ : Fin 2 => (1 : ℝ)) i : ℝ) : ℂ) •
        (fun _ : Fin 2 => (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) i)
      = ∑ i : Fin 2, ∑ i' : Fin 2, (fun _ : Fin 2 => (1 : ℝ)) i * (fun _ : Fin 2 => (1 : ℝ)) i' *
          vB (sz := sz0) 0 ((fun _ : Fin 2 =>
            (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) i)
            ((fun _ : Fin 2 =>
            (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) i') :=
  v_sum_eq 0 _ _

end Instances


end RBM.Path

end
