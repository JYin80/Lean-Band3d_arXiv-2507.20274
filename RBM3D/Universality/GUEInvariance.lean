/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Pins
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# GUE unitary invariance (T2175, UN-08)

Port of RBM2D `c9a24cf:RBM2D/Universality/GUEInvariance.lean` (itself a port of RBM1D
`c06b103:RBM1D/Flow/GUEUnitaryInvariance.lean`), adapted to the RBM3D coordinate space
`Ω d L W = CoordF d L W → ℝ`, `CoordF d L W = Idx d L W × Idx d L W × Bool`, `Idx d L W = Zd d (W L)`,
and to `gueVar`, `gueP`, `Xmat` (`N = (W L)^d`); the only dimension-dependent step is `card_Idx`.

## Route

Only the real coordinates `(i, j, b)` with `idxKey i < idxKey j` (both booleans) or `i = j`
(`b = true`) are read by `Xmat d L W`; they form the finite slot type `GUESlot d L W`.  The real-linear
reconstruction `GUEReconSlot` and its left inverse `GUEExtractSlot` identify `Xmat d L W` with
`GUEReconSlot` composed with the restriction of `ω` to the slots.  The key identity
(`GUEMainIdentity`) is `∑ (extr K)² / wt = N · Tr(K²)` for Hermitian `K` (`wt` the slot's Gaussian
variance `gueVar`, `N = (W L)^d` the matrix size); its right side is invariant under unitary
conjugation.  Standardizing each slot by `√wt` gives a linear isometry of
`EuclideanSpace ℝ (GUESlot d L W)`, to which `ProbabilityTheory.stdGaussian_map` applies; the slot
law of `gueP` is identified with a standardized `stdGaussian` by `map_pi_eq_stdGaussian`,
`Measure.pi_map_pi` and `gaussianReal_map_const_mul`.  The unused coordinates of `Coord d L W` (the
pairs with `idxKey j < idxKey i` and `(i, i, false)`) drop out through
`Measure.map_infinitePi_infinitePi_of_inj`.

The RBM1D theorem `gueMeasure_map_conj` states the invariance for `Uᴴ * X * U`; the RBM2D target
`gueP_map_unitary_conj` (the endpoint of RBM2D `GUEInvariance.lean:999`) states it for `U * X * star U`.  The
RBM1D direction is kept for the private ported proof (`GUE_map_conj`), and the target is its
instance at `star U`.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory WithLp
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped ComplexConjugate NNReal ENNReal

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

variable (d d L W : ℕ) [NeZero L] [NeZero W]

/-! ### The real-coordinate slot type at fixed matrix size `N` -/

/-- Which triples `(i, j, b)` carry a real coordinate read by `Xmat d L W`: either
`idxKey i < idxKey j` (either boolean), or `i = j` (only `b = true`).  Unpinned, file-local
(CLAUDE.md §3 (E)). -/
private def GUESlotPred (q : Idx d L W × Idx d L W × Bool) : Prop :=
  idxKey d L W q.1 < idxKey d L W q.2.1 ∨ (q.1 = q.2.1 ∧ q.2.2 = true)

private instance instDecidablePredGUESlotPred :
    DecidablePred (GUESlotPred d L W) := fun q => by unfold GUESlotPred; infer_instance

/-- The finite index set of real coordinates read by `Xmat d L W`. -/
private def GUESlot : Type :=
  {q : Idx d L W × Idx d L W × Bool // GUESlotPred d L W q}

private instance instFintypeGUESlot : Fintype (GUESlot d L W) :=
  Subtype.fintype _

/-! ### The Gaussian variance of a slot (total function, matches `gueVar`) -/

private theorem GUE_card_idx :
    Fintype.card (Idx d L W) = (W * L) ^ d := by
  simp [Idx, Zd, ZMod.card]

private noncomputable def GUEWt (q : Idx d L W × Idx d L W × Bool) : ℝ :=
  (gueVar d L W q : ℝ)

private theorem GUEWt_diag (i : Idx d L W) (b : Bool) :
    GUEWt d L W (i, i, b) = 1 / (Fintype.card (Idx d L W) : ℝ) := by
  rw [GUE_card_idx]
  unfold GUEWt gueVar
  simp

private theorem GUEWt_offDiag (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    GUEWt d L W (i, j, b) = 1 / (2 * (Fintype.card (Idx d L W) : ℝ)) := by
  rw [GUE_card_idx]
  unfold GUEWt gueVar
  simp [hij]

private theorem GUEWt_pos (q : Idx d L W × Idx d L W × Bool) :
    0 < GUEWt d L W q := by
  have hc : (0 : ℝ) < (Fintype.card (Idx d L W) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rcases q with ⟨i, j, b⟩
  by_cases h : i = j
  · subst h
    rw [GUEWt_diag]
    positivity
  · rw [GUEWt_offDiag d L W i j b h]
    positivity

/-! ### Reconstruction and extraction (total functions on all triples) -/

/-- Rebuild a Hermitian matrix from a total assignment of real values to triples
`(i, j, b)`, using only the values at slots (mirrors `RBM.Gauss.Xentry`). -/
private noncomputable def GUERe (x : Idx d L W × Idx d L W × Bool → ℝ) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun i j =>
    if idxKey d L W i < idxKey d L W j then
      (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ)
    else if idxKey d L W j < idxKey d L W i then
      (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ)
    else
      (x (i, i, true) : ℂ)

/-- Extract the real value of a matrix entry at a triple `(i, j, b)` (mirrors the inverse of
`Xentry`; well-behaved only at slots, but total). -/
private noncomputable def GUEEx (K : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Idx d L W × Idx d L W × Bool → ℝ :=
  fun q => if q.1 = q.2.1 ∨ q.2.2 = true then (K q.1 q.2.1).re else (K q.1 q.2.1).im

private theorem GUERe_apply_lt (x : Idx d L W × Idx d L W × Bool → ℝ)
    {i j : Idx d L W} (h : idxKey d L W i < idxKey d L W j) :
    GUERe d L W x i j = (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ) := by
  simp only [GUERe, Matrix.of_apply, ite_eq_left h]

private theorem GUERe_apply_gt (x : Idx d L W × Idx d L W × Bool → ℝ)
    {i j : Idx d L W} (h : idxKey d L W j < idxKey d L W i) :
    GUERe d L W x i j = (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ) := by
  have hne : ¬ idxKey d L W i < idxKey d L W j := asymm h
  simp only [GUERe, Matrix.of_apply, ite_eq_right hne, ite_eq_left h]

private theorem GUERe_apply_diag (x : Idx d L W × Idx d L W × Bool → ℝ)
    (i : Idx d L W) :
    GUERe d L W x i i = (x (i, i, true) : ℂ) := by
  simp only [GUERe, Matrix.of_apply, ite_eq_right (lt_irrefl (idxKey d L W i))]

/-- **Hermitian-ness of `GUERe`**, for any real coordinate assignment. -/
private theorem GUERe_isHermitian (x : Idx d L W × Idx d L W × Bool → ℝ) :
    (GUERe d L W x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · rw [GUERe_apply_lt d L W x h, GUERe_apply_gt d L W x h, hstar]
    apply Complex.ext <;> simp
  · subst h
    rw [GUERe_apply_diag d L W x i, hstar]
    apply Complex.ext <;> simp
  · rw [GUERe_apply_gt d L W x h, GUERe_apply_lt d L W x h, hstar]
    apply Complex.ext <;> simp

/-- **Extraction after reconstruction recovers a slot's value.** -/
private theorem GUEEx_GUERe (x : Idx d L W × Idx d L W × Bool → ℝ)
    {q : Idx d L W × Idx d L W × Bool} (hq : GUESlotPred d L W q) :
    GUEEx d L W (GUERe d L W x) q = x q := by
  rcases q with ⟨i, j, b⟩
  rcases hq with h | ⟨hij, hb⟩
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    have hval : GUERe d L W x i j = (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ) :=
      GUERe_apply_lt d L W x h
    cases b
    · have e : GUEEx d L W (GUERe d L W x) (i, j, false) = (GUERe d L W x i j).im := by
        simp [GUEEx, hne]
      rw [e, hval]
      simp
    · have e : GUEEx d L W (GUERe d L W x) (i, j, true) = (GUERe d L W x i j).re := by
        simp [GUEEx]
      rw [e, hval]
      simp
  · dsimp only at hij hb
    subst hij
    subst hb
    have e : GUEEx d L W (GUERe d L W x) (i, i, true) = (GUERe d L W x i i).re := by
      simp [GUEEx]
    rw [e, GUERe_apply_diag d L W x i]
    simp

/-- **Reconstruction after extraction recovers a Hermitian matrix.** -/
private theorem GUERe_GUEEx {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hK : K.IsHermitian) : GUERe d L W (GUEEx d L W K) = K := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    rw [GUERe_apply_lt d L W (GUEEx d L W K) h]
    have e1 : GUEEx d L W K (i, j, true) = (K i j).re := by simp [GUEEx]
    have e2 : GUEEx d L W K (i, j, false) = (K i j).im := by simp [GUEEx, hne]
    rw [e1, e2, mul_comm]
    exact Complex.re_add_im (K i j)
  · subst h
    rw [GUERe_apply_diag d L W (GUEEx d L W K) i]
    have e : GUEEx d L W K (i, i, true) = (K i i).re := by simp [GUEEx]
    rw [e]
    have him : (K i i).im = 0 := by
      have hKii : star (K i i) = K i i := hK.apply i i
      have hcong := congrArg Complex.im hKii
      simp only [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl,
        Complex.conj_im] at hcong
      linarith
    apply Complex.ext
    · simp
    · simp [him]
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    rw [GUERe_apply_gt d L W (GUEEx d L W K) h]
    have e1 : GUEEx d L W K (j, i, true) = (K j i).re := by simp [GUEEx]
    have e2 : GUEEx d L W K (j, i, false) = (K j i).im := by simp [GUEEx, Ne.symm hne]
    rw [e1, e2]
    have hKij : star (K i j) = K j i := hK.apply j i
    have hcong : K i j = star (K j i) := by rw [← hKij, star_star]
    rw [hcong]
    apply Complex.ext <;> simp

/-! ### `GUERe`, `GUEEx` are real-linear -/

private theorem GUE_real_smul (c : ℝ) (z : ℂ) : c • z = (c : ℂ) * z := rfl

private theorem GUERe_add (x y : Idx d L W × Idx d L W × Bool → ℝ) :
    GUERe d L W (x + y) = GUERe d L W x + GUERe d L W y := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · rw [Matrix.add_apply, GUERe_apply_lt d L W x h, GUERe_apply_lt d L W y h,
      GUERe_apply_lt d L W (x + y) h]
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring
  · subst h
    rw [Matrix.add_apply, GUERe_apply_diag d L W x i, GUERe_apply_diag d L W y i,
      GUERe_apply_diag d L W (x + y) i]
    simp only [Pi.add_apply, Complex.ofReal_add]
  · rw [Matrix.add_apply, GUERe_apply_gt d L W x h, GUERe_apply_gt d L W y h,
      GUERe_apply_gt d L W (x + y) h]
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring

private theorem GUERe_smul (c : ℝ) (x : Idx d L W × Idx d L W × Bool → ℝ) :
    GUERe d L W (c • x) = c • GUERe d L W x := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · rw [Matrix.smul_apply, GUERe_apply_lt d L W x h, GUERe_apply_lt d L W (c • x) h]
    simp only [Pi.smul_apply, smul_eq_mul, GUE_real_smul, Complex.ofReal_mul]
    ring
  · subst h
    rw [Matrix.smul_apply, GUERe_apply_diag d L W x i, GUERe_apply_diag d L W (c • x) i]
    simp only [Pi.smul_apply, smul_eq_mul, GUE_real_smul, Complex.ofReal_mul]
  · rw [Matrix.smul_apply, GUERe_apply_gt d L W x h, GUERe_apply_gt d L W (c • x) h]
    simp only [Pi.smul_apply, smul_eq_mul, GUE_real_smul, Complex.ofReal_mul]
    ring

private theorem GUEEx_add (K K' : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEEx d L W (K + K') = GUEEx d L W K + GUEEx d L W K' := by
  funext q
  unfold GUEEx
  by_cases hc : q.1 = q.2.1 ∨ q.2.2 = true
  · simp [hc]
  · simp [hc]

private theorem GUEEx_smul (c : ℝ) (K : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEEx d L W (c • K) = c • GUEEx d L W K := by
  funext q
  unfold GUEEx
  by_cases hc : q.1 = q.2.1 ∨ q.2.2 = true
  · simp only [hc, Matrix.smul_apply, Complex.smul_re, smul_eq_mul, Pi.smul_apply,
      ite_eq_left]
  · simp only [hc, Matrix.smul_apply, Complex.smul_im, smul_eq_mul, Pi.smul_apply,
      ite_eq_right, not_false_eq_true]

/-! ### The fixed conjugation `H ↦ Uᴴ H U`, and its interaction with `GUERe`/`GUEEx` -/

private noncomputable def GUEConj (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Uᴴ * H * U

private theorem GUEConj_isHermitian (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) :
    (GUEConj d L W U H).IsHermitian := by
  change (Uᴴ * H * U)ᴴ = Uᴴ * H * U
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
    Matrix.mul_assoc]

private theorem GUEConj_add (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (H1 H2 : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEConj d L W U (H1 + H2) = GUEConj d L W U H1 + GUEConj d L W U H2 := by
  change Uᴴ * (H1 + H2) * U = Uᴴ * H1 * U + Uᴴ * H2 * U
  rw [Matrix.mul_add, Matrix.add_mul]

private theorem GUEConj_smul (U : Matrix (Idx d L W) (Idx d L W) ℂ) (c : ℝ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEConj d L W U (c • H) = c • GUEConj d L W U H := by
  change Uᴴ * (c • H) * U = c • (Uᴴ * H * U)
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `Uᴴ * (Uᴴ H U) * U`-type cancellation: conjugating by `U` then by `Uᴴ` is the identity, for
any unitary `U`. -/
private theorem GUEConj_conj_left {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEConj d L W Uᴴ (GUEConj d L W U H) = H := by
  change Uᴴᴴ * (Uᴴ * H * U) * Uᴴ = H
  rw [Matrix.conjTranspose_conjTranspose]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc U * (Uᴴ * H * U) * Uᴴ = (U * Uᴴ) * H * (U * Uᴴ) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc U Uᴴ H, ← Matrix.mul_assoc U,
          Matrix.mul_assoc]
    _ = H := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem GUEConj_conj_right {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEConj d L W U (GUEConj d L W Uᴴ H) = H := by
  have hU' : Uᴴ ∈ Matrix.unitaryGroup (Idx d L W) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have := GUEConj_conj_left d L W hU' H
  rwa [Matrix.conjTranspose_conjTranspose] at this

/-! ### The algebraic core: `∑ (extraction)²/(variance) = M · Tr(K²)` and unitary invariance -/

private theorem GUE_re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s' hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, Complex.add_re, ih]

private theorem GUE_normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.normSq_conj]

/-- **Step 1 of the main identity**: `Tr(K²).re` as a double sum of `normSq`, using only that
`K` is Hermitian. -/
private theorem GUE_trace_sq_re {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hK : K.IsHermitian) :
    (Matrix.trace (K * K)).re = ∑ i, ∑ j, Complex.normSq (K i j) := by
  have htr : Matrix.trace (K * K) = ∑ i, ∑ j, K i j * K j i := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [htr, GUE_re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [GUE_re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hji : K j i = star (K i j) := (hK.apply j i).symm
  have heq : K i j * K j i = ((Complex.normSq (K i j) : ℝ) : ℂ) := by
    rw [hji, show star (K i j) = (starRingEnd ℂ) (K i j) from rfl, Complex.mul_conj]
  rw [heq]
  simp

/-- **Step 2 of the main identity**: the sum of the two boolean slots at a fixed `(i, j)`. -/
private theorem GUE_bool_sum {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hK : K.IsHermitian) (i j : Idx d L W) :
    (∑ b : Bool, if GUESlotPred d L W (i, j, b) then
        (GUEEx d L W K (i, j, b)) ^ 2 / GUEWt d L W (i, j, b) else 0) =
      if i = j then (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j)
      else if idxKey d L W i < idxKey d L W j then
        2 * (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j)
      else 0 := by
  rw [Fintype.sum_bool]
  by_cases hij : i = j
  · subst hij
    have hSPt : GUESlotPred d L W (i, i, true) := Or.inr ⟨rfl, rfl⟩
    have hSPf : ¬ GUESlotPred d L W (i, i, false) := by
      simp [GUESlotPred]
    rw [ite_eq_left rfl, ite_eq_left hSPt, ite_eq_right hSPf]
    have e : GUEEx d L W K (i, i, true) = (K i i).re := by simp [GUEEx]
    have hw : GUEWt d L W (i, i, true) = 1 / (Fintype.card (Idx d L W) : ℝ) :=
      GUEWt_diag d L W i true
    rw [e, add_zero, hw]
    have him : (K i i).im = 0 := by
      have hKii : star (K i i) = K i i := hK.apply i i
      have hcong := congrArg Complex.im hKii
      simp only [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl,
        Complex.conj_im] at hcong
      linarith
    rw [Complex.normSq_apply, him]
    field_simp
    ring
  · rw [ite_eq_right hij]
    by_cases hlt : idxKey d L W i < idxKey d L W j
    · have hSPt : GUESlotPred d L W (i, j, true) := Or.inl hlt
      have hSPf : GUESlotPred d L W (i, j, false) := Or.inl hlt
      rw [ite_eq_left hlt, ite_eq_left hSPt, ite_eq_left hSPf]
      have e1 : GUEEx d L W K (i, j, true) = (K i j).re := by simp [GUEEx]
      have e2 : GUEEx d L W K (i, j, false) = (K i j).im := by simp [GUEEx, hij]
      have hw1 : GUEWt d L W (i, j, true) = 1 / (2 * (Fintype.card (Idx d L W) : ℝ)) :=
        GUEWt_offDiag d L W i j true hij
      have hw2 : GUEWt d L W (i, j, false) = 1 / (2 * (Fintype.card (Idx d L W) : ℝ)) :=
        GUEWt_offDiag d L W i j false hij
      rw [e1, e2, hw1, hw2, Complex.normSq_apply]
      field_simp
    · have hSPt : ¬ GUESlotPred d L W (i, j, true) := by
        simp [GUESlotPred, hlt, hij]
      have hSPf : ¬ GUESlotPred d L W (i, j, false) := by
        simp [GUESlotPred, hlt, hij]
      rw [ite_eq_right hlt, ite_eq_right hSPt, ite_eq_right hSPf]
      ring

/-- **Step 3 of the main identity**: the off-diagonal contribution is symmetric under swapping
`i` and `j` (uses `K`'s Hermitian symmetry). -/
private theorem GUE_swap_sum {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hK : K.IsHermitian) (c : ℝ) :
    ∑ i : Idx d L W, ∑ j : Idx d L W,
        (if idxKey d L W j < idxKey d L W i then c * Complex.normSq (K i j) else 0) =
      ∑ i : Idx d L W, ∑ j : Idx d L W,
        (if idxKey d L W i < idxKey d L W j then c * Complex.normSq (K i j) else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hab : idxKey d L W a < idxKey d L W b
  · rw [ite_eq_left hab, ite_eq_left hab]
    have hsymm : Complex.normSq (K b a) = Complex.normSq (K a b) := by
      have hba : K b a = star (K a b) := (hK.apply b a).symm
      rw [hba, GUE_normSq_star]
    rw [hsymm]
  · rw [ite_eq_right hab, ite_eq_right hab]

/-- **Main identity**: the weighted sum of squared slot values equals `M · Tr(K²).re`, for
Hermitian `K`. -/
private theorem GUEMainIdentity {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hK : K.IsHermitian) :
    ∑ q : GUESlot d L W, (GUEEx d L W K q.1) ^ 2 / GUEWt d L W q.1 =
      (Fintype.card (Idx d L W) : ℝ) * (Matrix.trace (K * K)).re := by
  have hconv : (∑ q ∈ (Finset.univ : Finset (Idx d L W × Idx d L W × Bool)).filter (GUESlotPred d L W),
      (GUEEx d L W K q) ^ 2 / GUEWt d L W q) =
      ∑ q : GUESlot d L W, (GUEEx d L W K q.1) ^ 2 / GUEWt d L W q.1 :=
    Finset.sum_subtype _ (fun x => by simp) _
  rw [← hconv, Finset.sum_filter]
  have hsplit : (∑ q : Idx d L W × Idx d L W × Bool,
      if GUESlotPred d L W q then (GUEEx d L W K q) ^ 2 / GUEWt d L W q else 0) =
      ∑ i : Idx d L W, ∑ j : Idx d L W, ∑ b : Bool,
        if GUESlotPred d L W (i, j, b) then (GUEEx d L W K (i, j, b)) ^ 2 / GUEWt d L W (i, j, b)
        else 0 := by
    rw [Fintype.sum_prod_type (α₁ := Idx d L W) (α₂ := Idx d L W × Bool)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Fintype.sum_prod_type (α₁ := Idx d L W) (α₂ := Bool)
      (f := fun y => if GUESlotPred d L W (i, y) then
        (GUEEx d L W K (i, y)) ^ 2 / GUEWt d L W (i, y) else 0)
  rw [hsplit]
  simp_rw [GUE_bool_sum d L W hK]
  rw [GUE_trace_sq_re d L W hK]
  have hsep : ∀ i j : Idx d L W,
      (if i = j then (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j)
        else if idxKey d L W i < idxKey d L W j then
          2 * (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j) else 0) =
      (if i = j then (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j) else 0) +
        (if idxKey d L W i < idxKey d L W j then
          2 * (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j) else 0) := by
    intro i j
    by_cases hij : i = j
    · have hnlt : ¬ idxKey d L W i < idxKey d L W j := by rw [hij]; exact lt_irrefl _
      rw [ite_eq_left hij, ite_eq_left hij, ite_eq_right hnlt, add_zero]
    · rw [ite_eq_right hij, ite_eq_right hij, zero_add]
  simp_rw [hsep, Finset.sum_add_distrib]
  have hA : ∑ i : Idx d L W, ∑ j : Idx d L W,
      (if i = j then (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j) else 0) =
      (Fintype.card (Idx d L W) : ℝ) * ∑ i : Idx d L W, Complex.normSq (K i i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  have hB : ∑ i : Idx d L W, ∑ j : Idx d L W,
      (if idxKey d L W i < idxKey d L W j then
        2 * (Fintype.card (Idx d L W) : ℝ) * Complex.normSq (K i j) else 0) =
      2 * (Fintype.card (Idx d L W) : ℝ) * ∑ i : Idx d L W, ∑ j : Idx d L W,
        (if idxKey d L W i < idxKey d L W j then Complex.normSq (K i j) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  rw [hA, hB]
  have hC : ∑ i : Idx d L W, ∑ j : Idx d L W, Complex.normSq (K i j) =
      (∑ i : Idx d L W, Complex.normSq (K i i)) +
      2 * (∑ i : Idx d L W, ∑ j : Idx d L W,
        (if idxKey d L W i < idxKey d L W j then Complex.normSq (K i j) else 0)) := by
    have hdecomp : ∀ i j : Idx d L W, Complex.normSq (K i j) =
        (if i = j then Complex.normSq (K i j) else 0) +
        ((if idxKey d L W i < idxKey d L W j then Complex.normSq (K i j) else 0) +
          (if idxKey d L W j < idxKey d L W i then Complex.normSq (K i j) else 0)) := by
      intro i j
      rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
      · rw [ite_eq_right (fun he : i = j => absurd h (he ▸ lt_irrefl _)), ite_eq_left h,
          ite_eq_right (asymm h)]
        ring
      · subst h
        rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _)]
        ring
      · rw [ite_eq_right (fun he : i = j => absurd h (he ▸ lt_irrefl _)), ite_eq_right (asymm h),
          ite_eq_left h]
        ring
    rw [show (∑ i : Idx d L W, ∑ j : Idx d L W, Complex.normSq (K i j)) =
        ∑ i : Idx d L W, ∑ j : Idx d L W, ((if i = j then Complex.normSq (K i j) else 0) +
          ((if idxKey d L W i < idxKey d L W j then Complex.normSq (K i j) else 0) +
            (if idxKey d L W j < idxKey d L W i then Complex.normSq (K i j) else 0))) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hdecomp i j))]
    simp_rw [Finset.sum_add_distrib]
    have hdiagsum : (∑ i : Idx d L W, ∑ j : Idx d L W,
        (if i = j then Complex.normSq (K i j) else 0)) =
        ∑ i : Idx d L W, Complex.normSq (K i i) :=
      Finset.sum_congr rfl (fun i _ => by simp)
    have hswap1 : (∑ i : Idx d L W, ∑ j : Idx d L W,
        (if idxKey d L W j < idxKey d L W i then Complex.normSq (K i j) else 0)) =
        ∑ i : Idx d L W, ∑ j : Idx d L W,
          (if idxKey d L W i < idxKey d L W j then Complex.normSq (K i j) else 0) := by
      simpa using GUE_swap_sum d L W hK 1
    rw [hdiagsum, hswap1]
    ring
  rw [hC]
  ring

/-! ### The subtype-indexed reconstruction/extraction, and the conjugation action on slots -/

private noncomputable def GUEExtend (x : GUESlot d L W → ℝ) :
    Idx d L W × Idx d L W × Bool → ℝ :=
  fun q => if h : GUESlotPred d L W q then x ⟨q, h⟩ else 0

private theorem GUEExtend_add (x y : GUESlot d L W → ℝ) :
    GUEExtend d L W (x + y) = GUEExtend d L W x + GUEExtend d L W y := by
  funext q
  change GUEExtend d L W (x + y) q = GUEExtend d L W x q + GUEExtend d L W y q
  unfold GUEExtend
  by_cases h : GUESlotPred d L W q
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h, add_zero]

private theorem GUEExtend_smul (c : ℝ) (x : GUESlot d L W → ℝ) :
    GUEExtend d L W (c • x) = c • GUEExtend d L W x := by
  funext q
  change GUEExtend d L W (c • x) q = c • GUEExtend d L W x q
  unfold GUEExtend
  by_cases h : GUESlotPred d L W q
  · rw [dite_eq_left h, dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h, smul_zero]

private noncomputable def GUEReconSlot (x : GUESlot d L W → ℝ) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  GUERe d L W (GUEExtend d L W x)

private noncomputable def GUEExtractSlot (K : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUESlot d L W → ℝ :=
  fun p => GUEEx d L W K p.1

private theorem GUEReconSlot_add (x y : GUESlot d L W → ℝ) :
    GUEReconSlot d L W (x + y) = GUEReconSlot d L W x + GUEReconSlot d L W y := by
  unfold GUEReconSlot
  rw [GUEExtend_add, GUERe_add]

private theorem GUEReconSlot_smul (c : ℝ) (x : GUESlot d L W → ℝ) :
    GUEReconSlot d L W (c • x) = c • GUEReconSlot d L W x := by
  unfold GUEReconSlot
  rw [GUEExtend_smul, GUERe_smul]

private theorem GUEReconSlot_isHermitian (x : GUESlot d L W → ℝ) :
    (GUEReconSlot d L W x).IsHermitian :=
  GUERe_isHermitian d L W (GUEExtend d L W x)

private theorem GUEExtractSlot_add (K K' : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEExtractSlot d L W (K + K') = GUEExtractSlot d L W K + GUEExtractSlot d L W K' := by
  funext p
  exact congrFun (GUEEx_add d L W K K') p.1

private theorem GUEExtractSlot_smul (c : ℝ)
    (K : Matrix (Idx d L W) (Idx d L W) ℂ) :
    GUEExtractSlot d L W (c • K) = c • GUEExtractSlot d L W K := by
  funext p
  exact congrFun (GUEEx_smul d L W c K) p.1

private theorem GUEExtractSlot_GUEReconSlot (x : GUESlot d L W → ℝ) :
    GUEExtractSlot d L W (GUEReconSlot d L W x) = x := by
  funext p
  change GUEEx d L W (GUERe d L W (GUEExtend d L W x)) p.1 = x p
  rw [GUEEx_GUERe d L W (GUEExtend d L W x) p.2]
  unfold GUEExtend
  rw [dite_eq_left p.2]
  rfl

private theorem GUERe_congr_slots {x y : Idx d L W × Idx d L W × Bool → ℝ}
    (h : ∀ q, GUESlotPred d L W q → x q = y q) : GUERe d L W x = GUERe d L W y := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d L W i j with hlt | heq | hgt
  · rw [GUERe_apply_lt d L W x hlt, GUERe_apply_lt d L W y hlt, h _ (Or.inl hlt), h _ (Or.inl hlt)]
  · subst heq
    rw [GUERe_apply_diag d L W x i, GUERe_apply_diag d L W y i, h _ (Or.inr ⟨rfl, rfl⟩)]
  · rw [GUERe_apply_gt d L W x hgt, GUERe_apply_gt d L W y hgt, h _ (Or.inl hgt), h _ (Or.inl hgt)]

private theorem GUEReconSlot_GUEExtractSlot
    {K : Matrix (Idx d L W) (Idx d L W) ℂ} (hK : K.IsHermitian) :
    GUEReconSlot d L W (GUEExtractSlot d L W K) = K := by
  change GUERe d L W (GUEExtend d L W (GUEExtractSlot d L W K)) = K
  rw [GUERe_congr_slots d L W (x := GUEExtend d L W (GUEExtractSlot d L W K)) (y := GUEEx d L W K)
    (fun q hq => by unfold GUEExtend GUEExtractSlot; rw [dite_eq_left hq])]
  exact GUERe_GUEEx d L W hK

/-- The conjugation action on real slot values, `x ↦ extract (Uᴴ · reconstruct(x) · U)`. -/
private noncomputable def GUE_T (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (x : GUESlot d L W → ℝ) : GUESlot d L W → ℝ :=
  GUEExtractSlot d L W (GUEConj d L W U (GUEReconSlot d L W x))

private theorem GUE_T_add (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (x y : GUESlot d L W → ℝ) : GUE_T d L W U (x + y) = GUE_T d L W U x + GUE_T d L W U y := by
  unfold GUE_T
  rw [GUEReconSlot_add, GUEConj_add, GUEExtractSlot_add]

private theorem GUE_T_smul (U : Matrix (Idx d L W) (Idx d L W) ℂ) (c : ℝ)
    (x : GUESlot d L W → ℝ) : GUE_T d L W U (c • x) = c • GUE_T d L W U x := by
  unfold GUE_T
  rw [GUEReconSlot_smul, GUEConj_smul, GUEExtractSlot_smul]

private theorem GUE_T_left_inv {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (x : GUESlot d L W → ℝ) :
    GUE_T d L W Uᴴ (GUE_T d L W U x) = x := by
  unfold GUE_T
  rw [GUEReconSlot_GUEExtractSlot d L W
    (GUEConj_isHermitian d L W U (GUEReconSlot_isHermitian d L W x)),
    GUEConj_conj_left d L W hU, GUEExtractSlot_GUEReconSlot]

private theorem GUE_T_right_inv {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (x : GUESlot d L W → ℝ) :
    GUE_T d L W U (GUE_T d L W Uᴴ x) = x := by
  unfold GUE_T
  rw [GUEReconSlot_GUEExtractSlot d L W
    (GUEConj_isHermitian d L W Uᴴ (GUEReconSlot_isHermitian d L W x)),
    GUEConj_conj_right d L W hU, GUEExtractSlot_GUEReconSlot]

/-- **Conjugation-invariance of `Tr(K²)`**, the algebraic core of unitary invariance. -/
private theorem GUE_trace_conj_inv {U K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    Matrix.trace ((Uᴴ * K * U) * (Uᴴ * K * U)) = Matrix.trace (K * K) := by
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have heq : Uᴴ * K * U * (Uᴴ * K * U) = Uᴴ * (K * K) * U := by
    rw [show Uᴴ * K * U * (Uᴴ * K * U) = Uᴴ * K * (U * Uᴴ) * K * U by
      simp only [Matrix.mul_assoc], h1]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **The `Q`-invariance of `GUE_T`**: the weighted sum of squares is preserved by conjugation. -/
private theorem GUE_T_Q_inv {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (x : GUESlot d L W → ℝ) :
    ∑ p : GUESlot d L W, (GUE_T d L W U x p) ^ 2 / GUEWt d L W p.1 =
      ∑ p : GUESlot d L W, (x p) ^ 2 / GUEWt d L W p.1 := by
  have hK : (GUEReconSlot d L W x).IsHermitian := GUEReconSlot_isHermitian d L W x
  have hK' : (GUEConj d L W U (GUEReconSlot d L W x)).IsHermitian := GUEConj_isHermitian d L W U hK
  have e1 : (∑ p : GUESlot d L W, (GUE_T d L W U x p) ^ 2 / GUEWt d L W p.1) =
      (Fintype.card (Idx d L W) : ℝ) * (Matrix.trace (GUEConj d L W U (GUEReconSlot d L W x) *
        GUEConj d L W U (GUEReconSlot d L W x))).re :=
    GUEMainIdentity d L W hK'
  have e2 : (∑ p : GUESlot d L W, (x p) ^ 2 / GUEWt d L W p.1) =
      (Fintype.card (Idx d L W) : ℝ) *
        (Matrix.trace (GUEReconSlot d L W x * GUEReconSlot d L W x)).re := by
    rw [← GUEMainIdentity d L W hK]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [show GUEEx d L W (GUEReconSlot d L W x) p.1 =
        GUEExtractSlot d L W (GUEReconSlot d L W x) p from rfl,
      GUEExtractSlot_GUEReconSlot]
  rw [e1, e2, show GUEConj d L W U (GUEReconSlot d L W x) = Uᴴ * GUEReconSlot d L W x * U from rfl,
    GUE_trace_conj_inv d L W hU]

/-! ### Standardization by the square root of the variance, and the resulting isometry -/

private noncomputable def GUEDv (x : GUESlot d L W → ℝ) : GUESlot d L W → ℝ :=
  fun p => Real.sqrt (GUEWt d L W p.1) * x p

private noncomputable def GUEDvInv (x : GUESlot d L W → ℝ) : GUESlot d L W → ℝ :=
  fun p => x p / Real.sqrt (GUEWt d L W p.1)

private theorem GUEDv_add (x y : GUESlot d L W → ℝ) :
    GUEDv d L W (x + y) = GUEDv d L W x + GUEDv d L W y := by
  funext p
  change GUEDv d L W (x + y) p = GUEDv d L W x p + GUEDv d L W y p
  unfold GUEDv
  change Real.sqrt (GUEWt d L W p.1) * (x p + y p) = _
  ring

private theorem GUEDv_smul (c : ℝ) (x : GUESlot d L W → ℝ) :
    GUEDv d L W (c • x) = c • GUEDv d L W x := by
  funext p
  change GUEDv d L W (c • x) p = c • GUEDv d L W x p
  unfold GUEDv
  change Real.sqrt (GUEWt d L W p.1) * (c * x p) = c * (Real.sqrt (GUEWt d L W p.1) * x p)
  ring

private theorem GUEDvInv_add (x y : GUESlot d L W → ℝ) :
    GUEDvInv d L W (x + y) = GUEDvInv d L W x + GUEDvInv d L W y := by
  funext p
  change GUEDvInv d L W (x + y) p = GUEDvInv d L W x p + GUEDvInv d L W y p
  unfold GUEDvInv
  change (x p + y p) / Real.sqrt (GUEWt d L W p.1) = _
  ring

private theorem GUEDvInv_smul (c : ℝ) (x : GUESlot d L W → ℝ) :
    GUEDvInv d L W (c • x) = c • GUEDvInv d L W x := by
  funext p
  change GUEDvInv d L W (c • x) p = c • GUEDvInv d L W x p
  unfold GUEDvInv
  change (c * x p) / Real.sqrt (GUEWt d L W p.1) = c * (x p / Real.sqrt (GUEWt d L W p.1))
  ring

private theorem GUE_sqrt_ne_zero (q : Idx d L W × Idx d L W × Bool) :
    Real.sqrt (GUEWt d L W q) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (GUEWt_pos d L W q))

private theorem GUEDv_GUEDvInv (x : GUESlot d L W → ℝ) :
    GUEDv d L W (GUEDvInv d L W x) = x := by
  funext p
  change Real.sqrt (GUEWt d L W p.1) * (x p / Real.sqrt (GUEWt d L W p.1)) = x p
  field_simp [GUE_sqrt_ne_zero d L W p.1]

private theorem GUEDvInv_GUEDv (x : GUESlot d L W → ℝ) :
    GUEDvInv d L W (GUEDv d L W x) = x := by
  funext p
  change Real.sqrt (GUEWt d L W p.1) * x p / Real.sqrt (GUEWt d L W p.1) = x p
  field_simp [GUE_sqrt_ne_zero d L W p.1]

/-- The composite `extract ∘ (Uᴴ · ·  · U) ∘ reconstruct`, standardized by the square root of the
slot's variance: the map whose invariance under the pointwise Euclidean quadratic form is
established by `GUE_Tpp_Q`. -/
private noncomputable def GUE_Tpp (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (x : GUESlot d L W → ℝ) : GUESlot d L W → ℝ :=
  GUEDvInv d L W (GUE_T d L W U (GUEDv d L W x))

private theorem GUE_Tpp_add (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (x y : GUESlot d L W → ℝ) : GUE_Tpp d L W U (x + y) = GUE_Tpp d L W U x + GUE_Tpp d L W U y := by
  unfold GUE_Tpp
  rw [GUEDv_add, GUE_T_add, GUEDvInv_add]

private theorem GUE_Tpp_smul (U : Matrix (Idx d L W) (Idx d L W) ℂ) (c : ℝ)
    (x : GUESlot d L W → ℝ) : GUE_Tpp d L W U (c • x) = c • GUE_Tpp d L W U x := by
  unfold GUE_Tpp
  rw [GUEDv_smul, GUE_T_smul, GUEDvInv_smul]

private theorem GUE_Tpp_left_inv {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (x : GUESlot d L W → ℝ) :
    GUE_Tpp d L W Uᴴ (GUE_Tpp d L W U x) = x := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUE_T_left_inv d L W hU, GUEDvInv_GUEDv]

private theorem GUE_Tpp_right_inv {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (x : GUESlot d L W → ℝ) :
    GUE_Tpp d L W U (GUE_Tpp d L W Uᴴ x) = x := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUE_T_right_inv d L W hU, GUEDvInv_GUEDv]

/-- **The pointwise sum of squares is preserved by `GUE_Tpp`.** -/
private theorem GUE_Tpp_Q {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (x : GUESlot d L W → ℝ) :
    ∑ p : GUESlot d L W, (GUE_Tpp d L W U x p) ^ 2 = ∑ p : GUESlot d L W, (x p) ^ 2 := by
  have key := GUE_T_Q_inv d L W hU (GUEDv d L W x)
  have hlhs : ∀ p : GUESlot d L W, (GUE_Tpp d L W U x p) ^ 2 =
      (GUE_T d L W U (GUEDv d L W x) p) ^ 2 / GUEWt d L W p.1 := by
    intro p
    change (GUE_T d L W U (GUEDv d L W x) p / Real.sqrt (GUEWt d L W p.1)) ^ 2 = _
    rw [div_pow, Real.sq_sqrt (GUEWt_pos d L W p.1).le]
  have hrhs : ∀ p : GUESlot d L W, (GUEDv d L W x p) ^ 2 / GUEWt d L W p.1 = (x p) ^ 2 := by
    intro p
    change (Real.sqrt (GUEWt d L W p.1) * x p) ^ 2 / GUEWt d L W p.1 = (x p) ^ 2
    rw [mul_pow, Real.sq_sqrt (GUEWt_pos d L W p.1).le]
    field_simp [ne_of_gt (GUEWt_pos d L W p.1)]
  simp_rw [hlhs]
  rw [key]
  simp_rw [hrhs]

/-! ### The `EuclideanSpace` isometry, and its relation to `GUE_T` -/

private noncomputable def GUE_Tpp_lin (U : Matrix (Idx d L W) (Idx d L W) ℂ) :
    (GUESlot d L W → ℝ) →ₗ[ℝ] (GUESlot d L W → ℝ) where
  toFun := GUE_Tpp d L W U
  map_add' := GUE_Tpp_add d L W U
  map_smul' := GUE_Tpp_smul d L W U

private noncomputable def GUE_Tpp_linEquiv {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    (GUESlot d L W → ℝ) ≃ₗ[ℝ] (GUESlot d L W → ℝ) :=
  LinearEquiv.ofLinearMap (GUE_Tpp_lin d L W U) (GUE_Tpp_lin d L W Uᴴ)
    (LinearMap.ext (fun x => GUE_Tpp_right_inv d L W hU x))
    (LinearMap.ext (fun x => GUE_Tpp_left_inv d L W hU x))

private noncomputable def GUE_Tpp_eucl {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    EuclideanSpace ℝ (GUESlot d L W) ≃ₗ[ℝ] EuclideanSpace ℝ (GUESlot d L W) :=
  (WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ)).trans
    ((GUE_Tpp_linEquiv d L W hU).trans (WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ)).symm)

private theorem GUE_Tpp_eucl_apply {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (z : EuclideanSpace ℝ (GUESlot d L W))
    (p : GUESlot d L W) :
    (GUE_Tpp_eucl d L W hU z) p = GUE_Tpp d L W U (fun q => z q) p := rfl

private theorem GUE_Tpp_eucl_norm_sq {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (z : EuclideanSpace ℝ (GUESlot d L W)) :
    ‖GUE_Tpp_eucl d L W hU z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [GUE_Tpp_eucl_apply d L W hU]
  exact GUE_Tpp_Q d L W hU (fun q => z q)

private theorem GUE_Tpp_eucl_norm {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) (z : EuclideanSpace ℝ (GUESlot d L W)) :
    ‖GUE_Tpp_eucl d L W hU z‖ = ‖z‖ := by
  have h := congrArg Real.sqrt (GUE_Tpp_eucl_norm_sq d L W hU z)
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

private noncomputable def GUE_Tpp_isometry {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    EuclideanSpace ℝ (GUESlot d L W) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (GUESlot d L W) :=
  { GUE_Tpp_eucl d L W hU with norm_map' := GUE_Tpp_eucl_norm d L W hU }

/-- **`GUE_T` factors through `GUE_Tpp` via the standardizing scale.** -/
private theorem GUE_T_eq_Tpp (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (y : GUESlot d L W → ℝ) :
    GUE_T d L W U y = GUEDv d L W (GUE_Tpp d L W U (GUEDvInv d L W y)) := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUEDv_GUEDvInv]

/-- **The intertwining identity**: reconstructing after `GUE_T` matches conjugating after
reconstructing, for *any* slot values (no Hermitian hypothesis needed: `GUEReconSlot`'s output is
always Hermitian). -/
private theorem GUE_T_intertwine (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (x : GUESlot d L W → ℝ) :
    GUEReconSlot d L W (GUE_T d L W U x) = GUEConj d L W U (GUEReconSlot d L W x) := by
  unfold GUE_T
  exact GUEReconSlot_GUEExtractSlot d L W
    (GUEConj_isHermitian d L W U (GUEReconSlot_isHermitian d L W x))

/-! ### The coordinate-restriction map and its law under `gueP` -/

private theorem GUE_f_injective :
    Function.Injective (fun p : GUESlot d L W => p.1) := by
  intro p q h
  exact Subtype.ext h

private theorem GUE_Xmat_apply (ω : Ω d L W) (i j : Idx d L W) :
    Xmat d L W ω i j = Xentry d L W ω i j := rfl

private theorem Xmat_eq_GUERe_raw (ω : Ω d L W) :
    Xmat d L W ω = GUERe d L W (fun q => ω q) := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · rw [GUERe_apply_lt d L W _ h]
    simp [GUE_Xmat_apply, Xentry, h]
  · subst h
    rw [GUERe_apply_diag d L W _ i]
    simp [GUE_Xmat_apply, Xentry]
  · rw [GUERe_apply_gt d L W _ h]
    simp [GUE_Xmat_apply, Xentry, h, asymm h]

private theorem Xmat_eq_GUEReconSlot (ω : Ω d L W) :
    Xmat d L W ω =
      GUEReconSlot d L W (fun p : GUESlot d L W => ω p.1) := by
  rw [Xmat_eq_GUERe_raw]
  refine GUERe_congr_slots d L W (fun q hq => ?_)
  unfold GUEExtend
  rw [dite_eq_left hq]

/-! ### Measurability of the finite-dimensional maps -/

private theorem measurable_GUERe :
    Measurable (GUERe d L W) := by
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  simp only [GUERe, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem measurable_GUEExtend :
    Measurable (GUEExtend d L W) := by
  apply measurable_pi_iff.mpr; intro q
  unfold GUEExtend
  split_ifs <;> fun_prop

private theorem measurable_GUEReconSlot :
    Measurable (GUEReconSlot d L W) :=
  (measurable_GUERe d L W).comp (measurable_GUEExtend d L W)

private theorem measurable_GUEConj (U : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Measurable (GUEConj d L W U) := by
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  unfold GUEConj
  fun_prop

private theorem measurable_GUEExtractSlot :
    Measurable (GUEExtractSlot d L W) := by
  apply measurable_pi_iff.mpr; intro p
  unfold GUEExtractSlot GUEEx
  split_ifs <;> fun_prop

private theorem measurable_GUE_T (U : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Measurable (GUE_T d L W U) :=
  (measurable_GUEExtractSlot d L W).comp
    ((measurable_GUEConj d L W U).comp (measurable_GUEReconSlot d L W))

/-! ### The law of the coordinate-restriction map, identified with a standardized `stdGaussian` -/

private theorem measurable_GUEDv : Measurable (GUEDv d L W) := by
  apply measurable_pi_iff.mpr; intro p
  unfold GUEDv
  fun_prop

private theorem continuous_WithLp_linearEquiv :
    Continuous (⇑(WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ))) :=
  (WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ)).toLinearMap.continuous_of_finiteDimensional

private theorem continuous_WithLp_toLp :
    Continuous (WithLp.toLp 2 : (GUESlot d L W → ℝ) → EuclideanSpace ℝ (GUESlot d L W)) := by
  rw [← WithLp.coe_symm_linearEquiv (K := ℝ)]
  exact (WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ)).symm.toLinearMap.continuous_of_finiteDimensional

private theorem GUE_gaussianReal_eq (p : GUESlot d L W) :
    (gaussianReal 0 1).map (fun t => Real.sqrt (GUEWt d L W p.1) * t) =
      gaussianReal 0 (gueVar d L W p.1) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.eq
    change (Real.sqrt (GUEWt d L W p.1)) ^ 2 * 1 = (gueVar d L W p.1 : ℝ)
    rw [Real.sq_sqrt (GUEWt_pos d L W p.1).le, mul_one]
    rfl

private theorem GUE_muI_eq :
    (gueP d L W).map (fun ω => fun p : GUESlot d L W => ω p.1) =
      Measure.pi (fun p : GUESlot d L W => gaussianReal 0 (gueVar d L W p.1)) := by
  unfold gueP
  rw [Measure.map_infinitePi_infinitePi_of_inj (GUE_f_injective d L W), Measure.infinitePi_eq_pi]

private theorem GUE_muI_eq_stdGaussian_map :
    Measure.pi (fun p : GUESlot d L W => gaussianReal 0 (gueVar d L W p.1)) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot d L W))).map
        (GUEDv d L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ))) := by
  have hpi : (Measure.pi fun _ : GUESlot d L W => gaussianReal 0 1).map (GUEDv d L W) =
      Measure.pi (fun p : GUESlot d L W => gaussianReal 0 (gueVar d L W p.1)) := by
    rw [show (GUEDv d L W) = (fun x p => Real.sqrt (GUEWt d L W p.1) * x p) from rfl,
      Measure.pi_map_pi (fun p => Measurable.aemeasurable (by fun_prop))]
    exact congrArg Measure.pi (funext fun p => GUE_gaussianReal_eq d L W p)
  have hstd : (Measure.pi fun _ : GUESlot d L W => gaussianReal 0 1) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot d L W))).map
        (⇑(WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ))) := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (continuous_WithLp_linearEquiv d L W).measurable
      (continuous_WithLp_toLp d L W).measurable]
    have hid : (⇑(WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ)) ∘ WithLp.toLp 2) =
        (id : (GUESlot d L W → ℝ) → GUESlot d L W → ℝ) := by
      funext x
      change WithLp.ofLp (WithLp.toLp 2 x) = x
      rfl
    rw [hid, Measure.map_id]
  rw [← hpi, hstd, Measure.map_map (measurable_GUEDv d L W)
    (continuous_WithLp_linearEquiv d L W).measurable]

private theorem GUE_muI_eq_final :
    (gueP d L W).map (fun ω => fun p : GUESlot d L W => ω p.1) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot d L W))).map
        (GUEDv d L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ))) := by
  rw [GUE_muI_eq, GUE_muI_eq_stdGaussian_map]

/-- **Invariance of the coordinate law under `GUE_T`.** -/
private theorem GUE_muI_invariant {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    ((gueP d L W).map (fun ω => fun p : GUESlot d L W => ω p.1)).map
        (GUE_T d L W U) =
      (gueP d L W).map (fun ω => fun p : GUESlot d L W => ω p.1) := by
  rw [GUE_muI_eq_final]
  rw [Measure.map_map (measurable_GUE_T d L W U)
    ((measurable_GUEDv d L W).comp (continuous_WithLp_linearEquiv d L W).measurable)]
  have hfun : GUE_T d L W U ∘ (GUEDv d L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ))) =
      (GUEDv d L W ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ))) ∘ (GUE_Tpp_isometry d L W hU) := by
    funext z
    change GUE_T d L W U (GUEDv d L W ((WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ)) z)) =
      GUEDv d L W ((WithLp.linearEquiv 2 ℝ (GUESlot d L W → ℝ)) (GUE_Tpp_isometry d L W hU z))
    rw [GUE_T_eq_Tpp, GUEDvInv_GUEDv]
    rfl
  rw [hfun, ← Measure.map_map
    ((measurable_GUEDv d L W).comp (continuous_WithLp_linearEquiv d L W).measurable)
    (LinearIsometryEquiv.continuous _).measurable, stdGaussian_map (GUE_Tpp_isometry d L W hU)]

/-! ### The invariance statements -/

/-- Port of RBM1D `gueMeasure_map_conj` (`c06b103:RBM1D/Flow/GUEUnitaryInvariance.lean:962`), in the
RBM1D direction `Uᴴ * X * U`. -/
private theorem GUE_map_conj {U : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    (gueP d L W).map (fun ω => Uᴴ * Xmat d L W ω * U) = (gueP d L W).map (Xmat d L W) := by
  have hr_meas : Measurable (fun ω : Ω d L W => fun p : GUESlot d L W => ω p.1) := by
    apply measurable_pi_iff.mpr; intro p; exact measurable_pi_apply _
  have key1 : (fun ω => Uᴴ * Xmat d L W ω * U) =
      (GUEConj d L W U ∘ GUEReconSlot d L W) ∘
        (fun ω : Ω d L W => fun p : GUESlot d L W => ω p.1) := by
    funext ω
    change Uᴴ * Xmat d L W ω * U =
      GUEConj d L W U (GUEReconSlot d L W (fun p : GUESlot d L W => ω p.1))
    rw [Xmat_eq_GUEReconSlot d L W ω]
    rfl
  have key2 : Xmat d L W =
      GUEReconSlot d L W ∘ (fun ω : Ω d L W => fun p : GUESlot d L W => ω p.1) :=
    funext (Xmat_eq_GUEReconSlot d L W)
  rw [key1, key2,
    ← Measure.map_map ((measurable_GUEConj d L W U).comp (measurable_GUEReconSlot d L W)) hr_meas,
    ← Measure.map_map (measurable_GUEReconSlot d L W) hr_meas,
    show GUEConj d L W U ∘ GUEReconSlot d L W = GUEReconSlot d L W ∘ GUE_T d L W U from
      funext (fun x => (GUE_T_intertwine d L W U x).symm),
    ← Measure.map_map (measurable_GUEReconSlot d L W) (measurable_GUE_T d L W U)]
  congr 1
  exact GUE_muI_invariant d L W hU

/-- **Unitary invariance of the GUE law** (T2175 endpoint; restatement of RBM1D
`gueMeasure_map_conj` for `gueP`, `Xmat`): the law of the GUE matrix `Xmat d L W` under `gueP d L W` is
invariant under conjugation by any fixed unitary matrix. -/
theorem gueP_map_unitary_conj (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    (gueP d L W).map (fun ω => U * Xmat d L W ω * star U) = (gueP d L W).map (Xmat d L W) := by
  have hV : star U ∈ Matrix.unitaryGroup (Idx d L W) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h := GUE_map_conj d L W hV
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h

/-! ### Compiled nonempty instances (CLAUDE.md §4 step 2) -/

namespace GUEInvarianceCheck

/-- A diagonal matrix of unit phases `e^{i φ_k}`. -/
def phaseU (φ : Idx 3 3 1 → ℝ) : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ :=
  Matrix.diagonal fun k => Complex.exp ((φ k : ℂ) * Complex.I)

theorem phaseU_mem (φ : Idx 3 3 1 → ℝ) : phaseU φ ∈ Matrix.unitaryGroup (Idx 3 3 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseU,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  rw [Pi.star_apply, show star (Complex.exp ((φ k : ℂ) * Complex.I)) =
      Complex.exp (-((φ k : ℂ) * Complex.I)) from by
    rw [show star (Complex.exp ((φ k : ℂ) * Complex.I)) =
        (starRingEnd ℂ) (Complex.exp ((φ k : ℂ) * Complex.I)) from rfl, ← Complex.exp_conj]
    simp, ← Complex.exp_add]
  simp

/-- The unitary with phases `e^{i k}`, `k = idxKey`, is not a scalar matrix: its entries at the
indices of keys `0` and `1` are `1` and `e^{i} ≠ 1`. -/
theorem phaseU_not_scalar (c : ℂ) :
    phaseU (fun k => ((idxKey 3 3 1 k : ℕ) : ℝ)) ≠ c • (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) := by
  intro h
  have ha := congrFun (congrFun h ((Fintype.equivFin (Idx 3 3 1)).symm ⟨0, by simp [Idx, Zd, ZMod.card]⟩))
    ((Fintype.equivFin (Idx 3 3 1)).symm ⟨0, by simp [Idx, Zd, ZMod.card]⟩)
  have hb := congrFun (congrFun h ((Fintype.equivFin (Idx 3 3 1)).symm ⟨1, by simp [Idx, Zd, ZMod.card]⟩))
    ((Fintype.equivFin (Idx 3 3 1)).symm ⟨1, by simp [Idx, Zd, ZMod.card]⟩)
  simp only [phaseU, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, idxKey, Equiv.apply_symm_apply] at ha hb
  have hc : c = 1 := by simpa using ha.symm
  have hd : Complex.exp Complex.I = c := by simpa using hb
  have h1 : Complex.exp Complex.I = 1 := hd.trans hc
  rw [Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have him := congrArg Complex.im hn
  simp at him
  rcases lt_trichotomy n 0 with hn' | hn' | hn'
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith [Real.pi_gt_three]
  · subst hn'; simp at him
  · have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : (1 : ℤ) ≤ n)
    nlinarith [Real.pi_gt_three]

-- endpoint at `d = 3`, `L = 3`, `W = 1` (`N = 27`) and `U = 1`
theorem gueP_map_unitary_conj_one : (gueP 3 3 1).map (fun ω =>
    (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) * Xmat 3 3 1 ω * star (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ)) =
    (gueP 3 3 1).map (Xmat 3 3 1) :=
  gueP_map_unitary_conj 3 3 1 1 (one_mem _)

-- endpoint at `d = 3`, `L = 3`, `W = 1` and the non-scalar diagonal unitary `phaseU idxKey`
-- (phases `e^{i k}`, `k = idxKey`; `phaseU_mem`, `phaseU_not_scalar`)
theorem gueP_map_unitary_conj_phase : (gueP 3 3 1).map (fun ω =>
    phaseU (fun k => ((idxKey 3 3 1 k : ℕ) : ℝ)) * Xmat 3 3 1 ω *
      star (phaseU (fun k => ((idxKey 3 3 1 k : ℕ) : ℝ)))) = (gueP 3 3 1).map (Xmat 3 3 1) :=
  gueP_map_unitary_conj 3 3 1 _ (phaseU_mem _)

-- the common law in the statement is a probability measure
theorem isProbabilityMeasure_map_Xmat : IsProbabilityMeasure ((gueP 3 3 1).map (Xmat 3 3 1)) := by
  have : IsProbabilityMeasure (gueP 3 3 1) := by unfold gueP; infer_instance
  infer_instance

#print axioms RBM.Univ.gueP_map_unitary_conj
#print axioms RBM.Univ.GUEInvarianceCheck.phaseU_mem
#print axioms RBM.Univ.GUEInvarianceCheck.phaseU_not_scalar
#print axioms RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_one
#print axioms RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_phase
#print axioms RBM.Univ.GUEInvarianceCheck.isProbabilityMeasure_map_Xmat

end GUEInvarianceCheck

end RBM.Univ

end
