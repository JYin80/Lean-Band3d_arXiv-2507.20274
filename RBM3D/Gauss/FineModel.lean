/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.Sizes
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Gaussian band model on the fine lattice `Z_{WL}^d`, at one size and along a sequence

Paper: arXiv:2507.20274, `(bandcw0)`, `(eq:variancematrix)`, `(MBM)`.

* The variance profile `svarF` (`S_xy = W^{-d} S^{(B)}_{ab}(g)`), the coordinates `CoordF`, the
  one-size law `PF`, the matrix `Xmat`, the common sample space `SeqΩ` for all sizes with the
  law `seqP`, the size projection `slice`, `seqXmat` and the single-time flow
  `seqHflow = √u • seqXmat`.
* The properties of the model used downstream: the marginal laws of the coordinates,
  measurability and continuity of the matrix, its decomposition along the coordinates
  (`coordinateMatrix`), the second moments `E|X_ij|² = S_ij`, and the corresponding statements
  for the flows `Hflow` and `seqHflow` (`H_u = √u X`).

The variance at size `n` carries the coupling `sz.lam n`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

/-! ## The Gaussian model on the fine lattice (fixed size) -/

section Model

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- **`(eq:variancematrix)`** on the fine lattice: `S_xy = W^{-d} S^(B)_{ab}(g)` for `x ∈ [a]`,
`y ∈ [b]`.  The function `svar` of `RBM3D/Gauss/Model.lean` is the same function on `Vtx`; this
one is on `Z_{WL}^d`. -/
def svarF (i j : Idx d L W) : ℝ :=
  ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1

omit [NeZero L] in
theorem svarF_nonneg (i j : Idx d L W) : 0 ≤ svarF d L W g i j :=
  mul_nonneg (by positivity) (sbKernelR_nonneg d L g _)

theorem svarF_comm (i j : Idx d L W) : svarF d L W g i j = svarF d L W g j i := by
  simp only [svarF, SBR, Matrix.of_apply]
  rw [show (split d L W j).1 - (split d L W i).1 = -((split d L W i).1 - (split d L W j).1) by
    ring, sbKernelR_neg]

omit [NeZero L] in
/-- The diagonal entry variance `S_xx = W^{-d} (1 + 2 d g²)⁻¹`. -/
theorem svarF_diag (i : Idx d L W) :
    svarF d L W g i i = ((W : ℝ) ^ d)⁻¹ * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by
  simp [svarF, SBR, sbKernelR]

omit [NeZero L] in
/-- The fine-lattice variance profile is `svar` read through the bridge `split`:
the fine-lattice model and the block-product model carry the same `(eq:variancematrix)`. -/
theorem svarF_eq_svar (i j : Idx d L W) :
    svarF d L W g i j = svar d L W g (split d L W i) (split d L W j) := rfl

/-- A finite injective key, used only to orient independent off-diagonal entries (independence up to
`H_xy = conj H_yx`, `(bandcw0)`). -/
def idxKey (i : Idx d L W) : ℕ := (Fintype.equivFin (Idx d L W) i).val

theorem idxKey_injective : Function.Injective (idxKey d L W) := fun _ _ h =>
  (Fintype.equivFin (Idx d L W)).injective (Fin.val_injective h)

/-- Two real coordinates per oriented pair of lattice points (`(bandcw0)`). -/
abbrev CoordF : Type := Idx d L W × Idx d L W × Bool

/-- The finite product sample space of one size (`(bandcw0)`). -/
abbrev Ω : Type := CoordF d L W → ℝ

/-- Variance of one real coordinate: `S_ii` on the diagonal (one real Gaussian), `S_ij/2` off it
(two real Gaussians), so that `E|X_ij|² = S_ij` (`(bandcw0)`). -/
def gvarF (c : CoordF d L W) : ℝ≥0 :=
  ⟨if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2, by
    split_ifs
    · exact svarF_nonneg d L W g _ _
    · exact div_nonneg (svarF_nonneg d L W g _ _) (by norm_num)⟩

/-- **The one-size Gaussian law** (`(bandcw0)`): independent centred real Gaussians,
one per coordinate. -/
def PF : Measure (Ω d L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (gvarF d L W g c)

instance isProbabilityMeasure_PF : IsProbabilityMeasure (PF d L W g) := by
  unfold PF; infer_instance

/-- The entry `X_ij` of the Hermitian matrix, oriented by `idxKey`; real on the diagonal
(`(bandcw0)`: `N_ℝ` on the diagonal, `N_ℂ` off it). -/
def Xentry (ω : Ω d L W) (i j : Idx d L W) : ℂ :=
  if idxKey d L W i < idxKey d L W j then
    (ω (i, j, true) : ℂ) + Complex.I * (ω (i, j, false) : ℂ)
  else if idxKey d L W j < idxKey d L W i then
    (ω (j, i, true) : ℂ) - Complex.I * (ω (j, i, false) : ℂ)
  else (ω (i, j, true) : ℂ)

/-- **`H` of `(bandcw0)`** at one size. -/
def Xmat (ω : Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun i j => Xentry d L W ω i j

theorem idxKey_lt_or_eq_or_lt (i j : Idx d L W) :
    idxKey d L W i < idxKey d L W j ∨ i = j ∨ idxKey d L W j < idxKey d L W i := by
  rcases lt_trichotomy (idxKey d L W i) (idxKey d L W j) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (idxKey_injective d L W h))
  · exact Or.inr (Or.inr h)

theorem Xentry_swap (ω : Ω d L W) (i j : Idx d L W) :
    Xentry d L W ω j i = (starRingEnd ℂ) (Xentry d L W ω i j) := by
  unfold Xentry
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' (not_lt.mpr h.le)),
      ite_eq_left_iff.mpr (fun h' => absurd h h'), ite_eq_left_iff.mpr (fun h' => absurd h h')]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · subst h
    rw [ite_eq_right_iff.mpr (fun h' => absurd h' (lt_irrefl _)),
      ite_eq_right_iff.mpr (fun h' => absurd h' (lt_irrefl _))]
    simp only [Complex.conj_ofReal]
  · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'),
      ite_eq_right_iff.mpr (fun h' => absurd h' (not_lt.mpr h.le)),
      ite_eq_left_iff.mpr (fun h' => absurd h h')]
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

/-- `H` is Hermitian at every sample point. -/
theorem Xmat_isHermitian (ω : Ω d L W) : (Xmat d L W ω).IsHermitian := by
  ext i j
  exact (Xentry_swap d L W ω j i).symm

end Model

/-! ## The sequence-level model and the single-time flow -/

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- A coordinate records its size index as well as the entry and the real/imaginary tag
(`(bandcw0)`). -/
abbrev SeqCoord : Type := Σ n : ℕ, CoordF d (sz.L n) (sz.W n)

/-- One common sample space for all sizes (`(bandcw0)`; the `≺` of `(stoch_domination)` along
the sequence is one statement on one space). -/
abbrev SeqΩ : Type := SeqCoord sz → ℝ

/-- Coordinate variance at size `n`, with the coupling `sz.lam n` (`(eq:variancematrix)`). -/
def seqGvar (c : SeqCoord sz) : ℝ≥0 := gvarF d (sz.L c.1) (sz.W c.1) (sz.lam c.1) c.2

/-- **The model measure** (`(bandcw0)`, `(eq:variancematrix)`): independent
Gaussian coordinates for every size in one countable product.
Every size projection has the one-size law `PF` (`seqP_map_slice`). -/
def seqP : Measure (SeqΩ sz) := Measure.infinitePi fun c => gaussianReal 0 (seqGvar sz c)

instance isProbabilityMeasure_seqP : IsProbabilityMeasure (seqP sz) := by
  unfold seqP; infer_instance

/-- The coordinate vector at size `n`, extracted from the common product (`(bandcw0)`). -/
def slice (n : ℕ) (ω : SeqΩ sz) : Ω d (sz.L n) (sz.W n) := fun c => ω ⟨n, c⟩

theorem measurable_slice (n : ℕ) : Measurable (slice sz n) :=
  Measurable.of_eval fun (c : CoordF d (sz.L n) (sz.W n)) =>
    measurable_pi_apply (⟨n, c⟩ : SeqCoord sz)

/-- Every size projection of the common product has exactly the one-size Gaussian law. -/
theorem seqP_map_slice (n : ℕ) :
    (seqP sz).map (slice sz n) = PF d (sz.L n) (sz.W n) (sz.lam n) := by
  classical
  change _ = Measure.infinitePi _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  let e : CoordF d (sz.L n) (sz.W n) → SeqCoord sz := fun c => ⟨n, c⟩
  have he : Function.Injective e := by
    intro c c' h
    simpa [e] using h
  let t' : SeqCoord sz → Set ℝ := fun c =>
    if h : c.1 = n then t (h ▸ c.2) else Set.univ
  have hpre : slice sz n ⁻¹' Set.pi (↑s) t = Set.pi (↑(s.image e)) t' := by
    ext ω
    constructor
    · intro h c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      simpa [t', e, slice] using h a ha
    · intro h a ha
      have hc : e a ∈ s.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [t', e, slice] using h (e a) hc
  have ht' : ∀ c ∈ s.image e, MeasurableSet (t' c) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    simpa [t', e] using ht a
  rw [Measure.map_apply (measurable_slice sz n)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)),
    hpre, seqP, Measure.infinitePi_pi _ ht']
  rw [Finset.prod_image he.injOn]
  apply Finset.prod_congr rfl
  intro a ha
  simp [t', e, seqGvar]

/-- **`H` of `(bandcw0)` on the common probability space** at size index `n`. -/
def seqXmat (n : ℕ) (ω : SeqΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Xmat d (sz.L n) (sz.W n) (slice sz n ω)

/-- **The single-time flow** `H_u = √u X` (`(MBM)`, at one time): it has the law of the
matrix Brownian motion at time `u`, and is a deterministic coupling across times, not a matrix
Brownian motion.  It is used wherever the paper uses no stopping time. -/
def seqHflow (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (Real.sqrt u : ℂ) • seqXmat sz n ω

theorem seqXmat_isHermitian (n : ℕ) (ω : SeqΩ sz) : (seqXmat sz n ω).IsHermitian :=
  Xmat_isHermitian _ _ _ _

end Sizes

/-! ## Properties of the model: moments, coordinate decomposition, continuity

The lemmas of this section carry the dimension `d` and the coupling `g` as arguments; the
proofs follow the two-dimensional formalization.  The private `fineModel_*` lemmas are
elementary helpers for `gvarF`, `Xmat` and `Hflow`. -/

section ModelLemmas

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

omit [NeZero L] in
/-- The diagonal coordinate variance is `S_ii`. -/
private theorem fineModel_gvarF_diag (i : Idx d L W) (b : Bool) :
    (gvarF d L W g (i, i, b) : ℝ) = svarF d L W g i i := by
  change (if i = i then svarF d L W g i i else svarF d L W g i i / 2) = _
  simp

omit [NeZero L] in
/-- The off-diagonal coordinate variance is `S_ij / 2`. -/
private theorem fineModel_gvarF_offDiag (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- The entries of `Xmat` are the entries `Xentry`. -/
private theorem fineModel_Xmat_apply (ω : Ω d L W) (i j : Idx d L W) :
    Xmat d L W ω i j = Xentry d L W ω i j := rfl

omit [NeZero L] in
/-- Marginal law of one independent real coordinate. -/
theorem P_map_eval (c : CoordF d L W) :
    (PF d L W g).map (fun ω => ω c) = gaussianReal 0 (gvarF d L W g c) :=
  Measure.infinitePi_map_eval _ c

/-- Each entry `X_ij` is a measurable function of the coordinates. -/
theorem measurable_Xentry (i j : Idx d L W) :
    Measurable fun ω : Ω d L W => Xentry d L W ω i j := by
  unfold Xentry
  split_ifs <;> exact by fun_prop

/-! ### The defining entry covariance -/

omit [NeZero L] in
/-- Every coordinate is square-integrable. -/
theorem integrable_sq_coord (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => (ω c) ^ 2) (PF d L W g) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 2) ((PF d L W g).map fun ω => ω c) := by
    rw [P_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gvarF d L W g c) 2).integrable_sq
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

omit [NeZero L] in
/-- The second moment of a coordinate is its variance. -/
theorem integral_sq_coord (c : CoordF d L W) :
    ∫ ω, (ω c) ^ 2 ∂(PF d L W g) = (gvarF d L W g c : ℝ) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) :=
    (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((PF d L W g).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := gvarF d L W g c)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- `E |X_ij|² = S_ij`, including the real diagonal convention. -/
theorem integral_normSq_Xentry (i j : Idx d L W) :
    ∫ ω, ‖Xentry d L W ω i j‖ ^ 2 ∂(PF d L W g) = svarF d L W g i j := by
  have key : ∀ (p q : CoordF d L W) (S : ℝ), (gvarF d L W g p : ℝ) = S / 2 →
      (gvarF d L W g q : ℝ) = S / 2 →
      (∫ ω, ((ω p) ^ 2 + (ω q) ^ 2) ∂(PF d L W g)) = S := by
    intro p q S hp hq
    rw [integral_add (integrable_sq_coord d L W g p) (integrable_sq_coord d L W g q),
      integral_sq_coord, integral_sq_coord, hp, hq]
    ring
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hX : ∀ ω : Ω d L W, ‖Xentry d L W ω i j‖ ^ 2 =
        (ω (i, j, true)) ^ 2 + (ω (i, j, false)) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    simp only [hX]
    exact key _ _ _ (fineModel_gvarF_offDiag d L W g i j true hij)
      (fineModel_gvarF_offDiag d L W g i j false hij)
  · subst h
    have hX : ∀ ω : Ω d L W, ‖Xentry d L W ω i i‖ ^ 2 = (ω (i, i, true)) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    simp only [hX]
    rw [integral_sq_coord, fineModel_gvarF_diag]
  · have hij : j ≠ i := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hX : ∀ ω : Ω d L W, ‖Xentry d L W ω i j‖ ^ 2 =
        (ω (j, i, true)) ^ 2 + (ω (j, i, false)) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_right (asymm h), ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    simp only [hX]
    rw [key _ _ (svarF d L W g j i) (fineModel_gvarF_offDiag d L W g j i true hij)
      (fineModel_gvarF_offDiag d L W g j i false hij)]
    exact (svarF_comm d L W g i j).symm

/-! ### Linear decomposition into independent real coordinates -/

/-- The matrix depends additively on its real Gaussian coordinates. -/
theorem Xmat_add (ω ν : Ω d L W) :
    Xmat d L W (ω + ν) = Xmat d L W ω + Xmat d L W ν := by
  ext i j
  simp only [fineModel_Xmat_apply, Matrix.add_apply]
  unfold Xentry
  split_ifs <;> simp only [Pi.add_apply, Complex.ofReal_add] <;> ring

/-- Real scaling of every coordinate scales the entire matrix. -/
theorem Xmat_smul (t : ℝ) (ω : Ω d L W) :
    Xmat d L W (t • ω) = t • Xmat d L W ω := by
  ext i j
  simp only [fineModel_Xmat_apply, Matrix.smul_apply]
  unfold Xentry
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Algebra.smul_def, Complex.coe_algebraMap] <;> ring

/-- The real-linear map from independent coordinates to the Hermitian matrix. -/
noncomputable def Xlinear : Ω d L W →ₗ[ℝ] Matrix (Idx d L W) (Idx d L W) ℂ where
  toFun := Xmat d L W
  map_add' := Xmat_add d L W
  map_smul' := Xmat_smul d L W

/-- The matrix direction attached to one independent real coordinate.  Unused coordinates
give the zero matrix. -/
noncomputable def coordinateMatrix (c : CoordF d L W) :
    Matrix (Idx d L W) (Idx d L W) ℂ := Xmat d L W (Pi.single c 1)

/-- The matrix direction of a coordinate is Hermitian. -/
theorem coordinateMatrix_isHermitian (c : CoordF d L W) :
    (coordinateMatrix d L W c).IsHermitian := Xmat_isHermitian d L W _

/-- Replacing one real coordinate moves the matrix in its coordinate direction. -/
theorem Xmat_update (ω : Ω d L W) (c : CoordF d L W) (t : ℝ) :
    Xmat d L W (Function.update ω c t) =
      Xmat d L W ω + (t - ω c) • coordinateMatrix d L W c := by
  have hupdate : Function.update ω c t = ω + (t - ω c) • Pi.single c (1 : ℝ) := by
    funext e
    by_cases h : e = c
    · subst h
      simp [Function.update_self, Pi.single_eq_same, Pi.add_apply, Pi.smul_apply]
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h, Pi.add_apply, Pi.smul_apply]
  rw [hupdate, Xmat_add, Xmat_smul]
  rfl

/-- Exact finite coordinate decomposition of the one-time Gaussian matrix. -/
theorem Xmat_eq_sum_coordinates (ω : Ω d L W) :
    Xmat d L W ω = ∑ c : CoordF d L W, (ω c) • coordinateMatrix d L W c := by
  calc
    Xmat d L W ω = Xlinear d L W ω := rfl
    _ = Xlinear d L W (∑ c : CoordF d L W, Pi.single c (ω c)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ c : CoordF d L W, (ω c) • coordinateMatrix d L W c := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro c _
      have hsingle : Pi.single c (ω c) = (ω c) • (Pi.single c (1 : ℝ)) := by
        ext e
        by_cases h : e = c
        · subst h; simp
        · simp [h, Pi.smul_apply]
      rw [hsingle, map_smul]
      rfl

/-- The matrix is continuous as a function of the Gaussian coordinate vector. -/
theorem continuous_Xmat : Continuous (Xmat d L W) := by
  have h : Xmat d L W = fun ω : Ω d L W =>
      ∑ c : CoordF d L W, (ω c) • coordinateMatrix d L W c :=
    funext (Xmat_eq_sum_coordinates d L W)
  rw [h]
  exact continuous_finsetSum _ fun c _ => (continuous_apply c).smul continuous_const

/-- The one-time replacement for the paper's matrix Brownian flow (`(MBM)`, at one
time): `H_u = √u X`.  The sequence-level `seqHflow` is this map composed with `slice`
(`rfl`). -/
noncomputable def Hflow (u : ℝ) (ω : Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  (Real.sqrt u : ℂ) • Xmat d L W ω

/-- The entries of `Hflow` are `√u` times the entries `Xentry`. -/
private theorem fineModel_Hflow_apply (u : ℝ) (ω : Ω d L W) (i j : Idx d L W) :
    Hflow d L W u ω i j = (Real.sqrt u : ℂ) * Xentry d L W ω i j := rfl

/-- The same flow written with the real scalar action used by differentiation. -/
theorem Hflow_eq_realSmul (u : ℝ) (ω : Ω d L W) :
    Hflow d L W u ω = Real.sqrt u • Xmat d L W ω := by
  ext i j
  change (Real.sqrt u : ℂ) * Xentry d L W ω i j =
    Real.sqrt u • Xentry d L W ω i j
  rw [Complex.real_smul]

/-- The flow is continuous in the coordinate vector. -/
theorem continuous_Hflow (u : ℝ) : Continuous (Hflow d L W u) := by
  have h : Hflow d L W u = fun ω : Ω d L W => Real.sqrt u • Xmat d L W ω :=
    funext (Hflow_eq_realSmul d L W u)
  rw [h]
  exact (continuous_Xmat d L W).const_smul (Real.sqrt u)

/-- The flow is Hermitian. -/
theorem Hflow_isHermitian (u : ℝ) (ω : Ω d L W) :
    (Hflow d L W u ω).IsHermitian := by
  ext i j
  change (starRingEnd ℂ) ((Real.sqrt u : ℂ) * Xentry d L W ω j i) =
    (Real.sqrt u : ℂ) * Xentry d L W ω i j
  rw [map_mul, Complex.conj_ofReal, ← Xentry_swap]

/-- Each entry of the flow is a measurable function of the coordinates. -/
theorem measurable_Hflow (u : ℝ) (i j : Idx d L W) :
    Measurable fun ω : Ω d L W => Hflow d L W u ω i j := by
  simp only [fineModel_Hflow_apply]
  exact (measurable_Xentry d L W i j).const_mul _

/-- The entire time dependence is one scalar. -/
theorem Hflow_sub (u v : ℝ) (ω : Ω d L W) :
    Hflow d L W u ω - Hflow d L W v ω =
      ((Real.sqrt u - Real.sqrt v : ℝ) : ℂ) • Xmat d L W ω := by
  simp only [Hflow, Complex.ofReal_sub, sub_smul]

/-- Entrywise coordinate decomposition of the time increment. -/
theorem Hflow_sub_apply (u v : ℝ) (ω : Ω d L W) (i j : Idx d L W) :
    (Hflow d L W u ω - Hflow d L W v ω) i j =
      ((Real.sqrt u - Real.sqrt v : ℝ) : ℂ) * Xentry d L W ω i j := by
  rw [Hflow_sub]
  rfl

/-- The flow's entry variance is `u S_ij` for nonnegative time. -/
theorem integral_normSq_Hflow (u : ℝ) (hu : 0 ≤ u) (i j : Idx d L W) :
    ∫ ω, ‖Hflow d L W u ω i j‖ ^ 2 ∂(PF d L W g) = u * svarF d L W g i j := by
  simp only [fineModel_Hflow_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u), mul_pow]
  rw [integral_const_mul, integral_normSq_Xentry, Real.sq_sqrt hu]

end ModelLemmas

/-! ### The sequence-level lemmas -/

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- The marginal law of one coordinate under the common-space model measure. -/
theorem seqP_map_eval (c : SeqCoord sz) :
    (seqP sz).map (fun ω => ω c) = gaussianReal 0 (seqGvar sz c) :=
  Measure.infinitePi_map_eval _ c

/-- `seqHflow` is defined as `√u • seqXmat`, so this lemma is the definition. -/
theorem seqHflow_eq_smul (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    seqHflow sz n u ω = (Real.sqrt u : ℂ) • seqXmat sz n ω := rfl

/-- The common-space flow is Hermitian. -/
theorem seqHflow_isHermitian (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    (seqHflow sz n u ω).IsHermitian :=
  Hflow_isHermitian d (sz.L n) (sz.W n) u (slice sz n ω)

/-- Each entry of the common-space flow is a measurable function of the coordinates. -/
theorem measurable_seqHflow_entry (n : ℕ) (u : ℝ)
    (i j : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω : SeqΩ sz => seqHflow sz n u ω i j :=
  (measurable_Hflow d (sz.L n) (sz.W n) u i j).comp (measurable_slice sz n)

/-- The common-space flow has entry variance `u S_ij` at nonnegative time. -/
theorem integral_normSq_seqHflow (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (i j : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, ‖seqHflow sz n u ω i j‖ ^ 2 ∂(seqP sz) =
      u * svarF d (sz.L n) (sz.W n) (sz.lam n) i j := by
  change ∫ ω, ‖Hflow d (sz.L n) (sz.W n) u (slice sz n ω) i j‖ ^ 2 ∂(seqP sz) = _
  have hf : AEMeasurable (slice sz n) (seqP sz) := (measurable_slice sz n).aemeasurable
  have hg : AEStronglyMeasurable
      (fun v : Ω d (sz.L n) (sz.W n) => ‖Hflow d (sz.L n) (sz.W n) u v i j‖ ^ 2)
      ((seqP sz).map (slice sz n)) := by
    exact ((measurable_Hflow d (sz.L n) (sz.W n) u i j).norm.pow_const 2).aestronglyMeasurable
  rw [← integral_map hf hg, seqP_map_slice]
  exact integral_normSq_Hflow _ _ _ _ _ hu _ _

/-- Exact coordinate decomposition at every size on the common space. -/
theorem seqXmat_eq_sum_coordinates (n : ℕ) (ω : SeqΩ sz) :
    seqXmat sz n ω = ∑ c : CoordF d (sz.L n) (sz.W n),
      (ω ⟨n, c⟩) • coordinateMatrix d (sz.L n) (sz.W n) c :=
  Xmat_eq_sum_coordinates _ _ _ _

/-- Updating one common-space coordinate updates only its matrix direction at this size. -/
theorem seqXmat_update (n : ℕ) (ω : SeqΩ sz)
    (c : CoordF d (sz.L n) (sz.W n)) (t : ℝ) :
    seqXmat sz n (Function.update ω ⟨n, c⟩ t) =
      seqXmat sz n ω + (t - ω ⟨n, c⟩) • coordinateMatrix d (sz.L n) (sz.W n) c := by
  have hslice : slice sz n (Function.update ω ⟨n, c⟩ t) =
      Function.update (slice sz n ω) c t := by
    funext a
    by_cases h : a = c
    · subst h; simp [slice]
    · have hne : (⟨n, a⟩ : SeqCoord sz) ≠ ⟨n, c⟩ := fun he => h (by cases he; rfl)
      simp [slice, Function.update_of_ne h, Function.update_of_ne hne]
  change Xmat d (sz.L n) (sz.W n) (slice sz n (Function.update ω ⟨n, c⟩ t)) = _
  rw [hslice, Xmat_update]
  rfl

end Sizes

end RBM.Gauss
