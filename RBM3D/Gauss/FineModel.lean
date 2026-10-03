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

Ticket T2006 (MD-1).  Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex`
(cited `1_2:line`): `(bandcw0)` `1_2:296`, `(eq:variancematrix)` `1_2:304`, `(MBM)` `1_2:686`.

* Sections 3 and 4 of the compiled T2002 probe (`RBM3D/Probe/T2002Vocab.lean` at `5d2a4a8` on
  branch `t/T2002`, never merged), copied with their docstrings and proofs: the variance profile
  `svarF` (`S_xy = W^{-d} S^{(B)}_{ab}(g)`), the coordinates `CoordF`, the one-size law `PF`,
  the matrix `Xmat`, the common sample space `Sizes.SeqΩ` for all sizes with the law
  `Sizes.seqP`, the size projection `Sizes.slice`, `Sizes.seqXmat` and the single-time flow
  `Sizes.seqHflow = √u • seqXmat`.
* Section 5: the lemmas of `RBM2D/Gauss/Model.lean` (commit `c9a24cf`) ported to `d`
  dimensions with the renaming rules R1-R4 of `docs/reports/T2002-prove.md` (b.9): `d : Sizes`
  becomes `sz : Sizes d`, `Z2` becomes `Zd d`, `W^2` and `(W L)^2` become `W^d` and `(W L)^d`,
  and `Coord`, `svar`, `gvar`, `P` become `CoordF`, `svarF`, `gvarF`, `PF`.  The variance at
  size `n` carries the coupling `sz.lam n`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

/-! ## 3. The Gaussian model on the fine lattice (fixed size) -/

section Model

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- **`(eq:variancematrix)`** on the fine lattice: `S_xy = W^{-d} S^(B)_{ab}(g)` for `x ∈ [a]`,
`y ∈ [b]` (`1_2:304`).  The merged `Gauss.svar` is the same function on `Vtx`; this one is on
`Z_{WL}^d` (rule R4: RBM2D's `svar` is renamed `svarF` because `RBM.Gauss.svar` exists).
`RBM2D/Gauss/Model.lean:42` (`svar`), where `S^(B)` is the fixed five-point profile; rule R3. -/
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
/-- The fine-lattice variance profile is the merged `Gauss.svar` read through the bridge `split`:
the fine-lattice model and the merged block-product model carry the same `(eq:variancematrix)`. -/
theorem svarF_eq_svar (i j : Idx d L W) :
    svarF d L W g i j = svar d L W g (split d L W i) (split d L W j) := rfl

/-- A finite injective key, used only to orient independent off-diagonal entries (independence up to
`H_xy = conj H_yx`, `(bandcw0)`, `1_2:296`).  `RBM2D/Gauss/Model.lean:88`. -/
def idxKey (i : Idx d L W) : ℕ := (Fintype.equivFin (Idx d L W) i).val

theorem idxKey_injective : Function.Injective (idxKey d L W) := fun _ _ h =>
  (Fintype.equivFin (Idx d L W)).injective (Fin.val_injective h)

/-- Two real coordinates per oriented pair of lattice points (`(bandcw0)`, `1_2:296`; rule R4:
`RBM2D`'s `Coord`).  `RBM2D/Gauss/Model.lean:102`. -/
abbrev CoordF : Type := Idx d L W × Idx d L W × Bool

/-- The finite product sample space of one size (`(bandcw0)`, `1_2:296`):
`RBM2D/Gauss/Model.lean:105`. -/
abbrev Ω : Type := CoordF d L W → ℝ

/-- Variance of one real coordinate: `S_ii` on the diagonal (one real Gaussian), `S_ij/2` off it
(two real Gaussians), so that `E|X_ij|² = S_ij` (`(bandcw0)`, `1_2:296`).
`RBM2D/Gauss/Model.lean:108` (`gvar`), rule R4. -/
def gvarF (c : CoordF d L W) : ℝ≥0 :=
  ⟨if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2, by
    split_ifs
    · exact svarF_nonneg d L W g _ _
    · exact div_nonneg (svarF_nonneg d L W g _ _) (by norm_num)⟩

/-- **The one-size Gaussian law** (`(bandcw0)`, `1_2:296`): independent centred real Gaussians,
one per coordinate.  `RBM2D/Gauss/Model.lean:127` (`P`), rule R4. -/
def PF : Measure (Ω d L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (gvarF d L W g c)

instance isProbabilityMeasure_PF : IsProbabilityMeasure (PF d L W g) := by
  unfold PF; infer_instance

/-- The entry `X_ij` of the Hermitian matrix, oriented by `idxKey`; real on the diagonal
(`(bandcw0)`, `1_2:296`: `N_ℝ` on the diagonal, `N_ℂ` off it).  `RBM2D/Gauss/Model.lean:147`. -/
def Xentry (ω : Ω d L W) (i j : Idx d L W) : ℂ :=
  if idxKey d L W i < idxKey d L W j then
    (ω (i, j, true) : ℂ) + Complex.I * (ω (i, j, false) : ℂ)
  else if idxKey d L W j < idxKey d L W i then
    (ω (j, i, true) : ℂ) - Complex.I * (ω (j, i, false) : ℂ)
  else (ω (i, j, true) : ℂ)

/-- **`H` of `(bandcw0)`** (`1_2:296`) at one size: `RBM2D/Gauss/Model.lean:155` (`Xmat`). -/
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

/-! ## 4. The sequence-level model and the single-time flow -/

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- A coordinate records its size index as well as the entry and the real/imaginary tag
(`(bandcw0)`, `1_2:296`).  `RBM2D/Gauss/Model.lean:425`. -/
abbrev SeqCoord : Type := Σ n : ℕ, CoordF d (sz.L n) (sz.W n)

/-- One common sample space for all sizes (`(bandcw0)`, `1_2:296`; the `≺` of `1_2:227–231` along
the sequence is one statement on one space): `RBM2D/Gauss/Model.lean:428`. -/
abbrev SeqΩ : Type := SeqCoord sz → ℝ

/-- Coordinate variance at size `n`, with the coupling `sz.lam n` (`(eq:variancematrix)`,
`1_2:304`). -/
def seqGvar (c : SeqCoord sz) : ℝ≥0 := gvarF d (sz.L c.1) (sz.W c.1) (sz.lam c.1) c.2

/-- **The model measure** (`(bandcw0)`, `1_2:296`; `(eq:variancematrix)`, `1_2:304`): independent
Gaussian coordinates for every size in one countable product; `RBM2D/Gauss/Model.lean:434` (`seqP`).
Every size projection has the one-size law `PF` (`seqP_map_slice`). -/
def seqP : Measure (SeqΩ sz) := Measure.infinitePi fun c => gaussianReal 0 (seqGvar sz c)

instance isProbabilityMeasure_seqP : IsProbabilityMeasure (seqP sz) := by
  unfold seqP; infer_instance

/-- The coordinate vector at size `n`, extracted from the common product (`(bandcw0)`,
`1_2:296`). -/
def slice (n : ℕ) (ω : SeqΩ sz) : Ω d (sz.L n) (sz.W n) := fun c => ω ⟨n, c⟩

theorem measurable_slice (n : ℕ) : Measurable (slice sz n) :=
  Measurable.of_eval fun (c : CoordF d (sz.L n) (sz.W n)) =>
    measurable_pi_apply (⟨n, c⟩ : SeqCoord sz)

/-- Every size projection of the common product has exactly the one-size Gaussian law
(`RBM2D/Gauss/Model.lean:457`, proof ported verbatim). -/
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

/-- **`H` of `(bandcw0)` on the common probability space** (`1_2:296`) at size index `n`:
`RBM2D/Gauss/Model.lean:490` (`seqXmat`). -/
def seqXmat (n : ℕ) (ω : SeqΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Xmat d (sz.L n) (sz.W n) (slice sz n ω)

/-- **The single-time flow** `H_u = √u X` (`(MBM)`, `1_2:686`, at one time): it has the law of the
matrix Brownian motion at time `u`, and is a deterministic coupling across times, not a matrix
Brownian motion.  `RBM2D/Gauss/Model.lean:495` (`seqHflow`); DECISIONS §7: used wherever the
paper uses no stopping time. -/
def seqHflow (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (Real.sqrt u : ℂ) • seqXmat sz n ω

theorem seqXmat_isHermitian (n : ℕ) (ω : SeqΩ sz) : (seqXmat sz n ω).IsHermitian :=
  Xmat_isHermitian _ _ _ _

end Sizes

/-! ## 5. The lemmas of `RBM2D/Gauss/Model.lean`, ported to `d` dimensions

Source: `RBM2D/Gauss/Model.lean` at commit `c9a24cf` (the line of each lemma is cited).  Renaming:
R1 `d : Sizes` becomes `sz : Sizes d`, R2 `Z2` becomes `Zd d`, R3 `W^2`, `(W L)^2` become `W^d`,
`(W L)^d` and the profile `S^(B)` carries the coupling `g` (`sz.lam n` along the sequence), R4
`Coord`, `svar`, `gvar`, `P` become `CoordF`, `svarF`, `gvarF`, `PF`.  The proofs are RBM2D's with
the arguments `d` (and `g`) inserted and RBM2D's `@[simp]` lemmas `gvar_diag`, `gvar_offDiag`,
`Xmat_apply`, `Hflow_apply`, which the proofs use and the ticket does not list, replaced by the
private `fineModel_*` copies below. -/

section ModelLemmas

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

omit [NeZero L] in
/-- The diagonal coordinate variance is `S_ii`.  (Helper: `RBM2D/Gauss/Model.lean:115`,
`gvar_diag`; not part of the ticket's list, hence private.) -/
private theorem fineModel_gvarF_diag (i : Idx d L W) (b : Bool) :
    (gvarF d L W g (i, i, b) : ℝ) = svarF d L W g i i := by
  change (if i = i then svarF d L W g i i else svarF d L W g i i / 2) = _
  simp

omit [NeZero L] in
/-- The off-diagonal coordinate variance is `S_ij / 2`.  (Helper: `RBM2D/Gauss/Model.lean:121`,
`gvar_offDiag`; private.) -/
private theorem fineModel_gvarF_offDiag (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- (Helper: `RBM2D/Gauss/Model.lean:158`, `Xmat_apply`; private.) -/
private theorem fineModel_Xmat_apply (ω : Ω d L W) (i j : Idx d L W) :
    Xmat d L W ω i j = Xentry d L W ω i j := rfl

omit [NeZero L] in
/-- Marginal law of one independent real coordinate.  `RBM2D/Gauss/Model.lean:136`. -/
theorem P_map_eval (c : CoordF d L W) :
    (PF d L W g).map (fun ω => ω c) = gaussianReal 0 (gvarF d L W g c) :=
  Measure.infinitePi_map_eval _ c

omit [NeZero L] in
/-- Every finite collection of coordinates has its independent product law.
`RBM2D/Gauss/Model.lean:142`. -/
theorem P_map_restrict (I : Finset (CoordF d L W)) :
    (PF d L W g).map I.restrict = Measure.pi fun c : I => gaussianReal 0 (gvarF d L W g c) :=
  Measure.infinitePi_map_restrict _

/-- `RBM2D/Gauss/Model.lean:180`. -/
theorem measurable_Xentry (i j : Idx d L W) :
    Measurable fun ω : Ω d L W => Xentry d L W ω i j := by
  unfold Xentry
  split_ifs <;> exact by fun_prop

/-! ### The defining entry covariance -/

omit [NeZero L] in
/-- `RBM2D/Gauss/Model.lean:188`. -/
theorem integrable_sq_coord (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => (ω c) ^ 2) (PF d L W g) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 2) ((PF d L W g).map fun ω => ω c) := by
    rw [P_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gvarF d L W g c) 2).integrable_sq
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

omit [NeZero L] in
/-- `RBM2D/Gauss/Model.lean:198`. -/
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

/-- `E |X_ij|² = S_ij`, including the real diagonal convention.  `RBM2D/Gauss/Model.lean:210`. -/
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

/-- The matrix depends additively on its real Gaussian coordinates.
`RBM2D/Gauss/Model.lean:253`. -/
theorem Xmat_add (ω ν : Ω d L W) :
    Xmat d L W (ω + ν) = Xmat d L W ω + Xmat d L W ν := by
  ext i j
  simp only [fineModel_Xmat_apply, Matrix.add_apply]
  unfold Xentry
  split_ifs <;> simp only [Pi.add_apply, Complex.ofReal_add] <;> ring

/-- Real scaling of every coordinate scales the entire matrix.  `RBM2D/Gauss/Model.lean:261`. -/
theorem Xmat_smul (t : ℝ) (ω : Ω d L W) :
    Xmat d L W (t • ω) = t • Xmat d L W ω := by
  ext i j
  simp only [fineModel_Xmat_apply, Matrix.smul_apply]
  unfold Xentry
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Algebra.smul_def, Complex.coe_algebraMap] <;> ring

/-- The real-linear map from independent coordinates to the Hermitian matrix.
`RBM2D/Gauss/Model.lean:270`. -/
noncomputable def Xlinear : Ω d L W →ₗ[ℝ] Matrix (Idx d L W) (Idx d L W) ℂ where
  toFun := Xmat d L W
  map_add' := Xmat_add d L W
  map_smul' := Xmat_smul d L W

/-- The matrix direction attached to one independent real coordinate.  Unused coordinates
give the zero matrix.  `RBM2D/Gauss/Model.lean:277`. -/
noncomputable def coordinateMatrix (c : CoordF d L W) :
    Matrix (Idx d L W) (Idx d L W) ℂ := Xmat d L W (Pi.single c 1)

/-- `RBM2D/Gauss/Model.lean:283`. -/
theorem coordinateMatrix_isHermitian (c : CoordF d L W) :
    (coordinateMatrix d L W c).IsHermitian := Xmat_isHermitian d L W _

/-- Replacing one real coordinate moves the matrix in its coordinate direction.
`RBM2D/Gauss/Model.lean:287`. -/
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

/-- Exact finite coordinate decomposition of the one-time Gaussian matrix.
`RBM2D/Gauss/Model.lean:300`. -/
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

/-- The matrix is continuous as a function of the Gaussian coordinate vector.
`RBM2D/Gauss/Model.lean:319`. -/
theorem continuous_Xmat : Continuous (Xmat d L W) := by
  have h : Xmat d L W = fun ω : Ω d L W =>
      ∑ c : CoordF d L W, (ω c) • coordinateMatrix d L W c :=
    funext (Xmat_eq_sum_coordinates d L W)
  rw [h]
  exact continuous_finsetSum _ fun c _ => (continuous_apply c).smul continuous_const

/-- The one-time replacement for the paper's matrix Brownian flow (`(MBM)`, `1_2:686`, at one
time): `H_u = √u X`.  `RBM2D/Gauss/Model.lean:327`.  The sequence-level `Sizes.seqHflow` is this
map composed with `Sizes.slice` (`rfl`). -/
noncomputable def Hflow (u : ℝ) (ω : Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  (Real.sqrt u : ℂ) • Xmat d L W ω

/-- (Helper: `RBM2D/Gauss/Model.lean:330`, `Hflow_apply`; private.) -/
private theorem fineModel_Hflow_apply (u : ℝ) (ω : Ω d L W) (i j : Idx d L W) :
    Hflow d L W u ω i j = (Real.sqrt u : ℂ) * Xentry d L W ω i j := rfl

/-- The same flow written with the real scalar action used by differentiation.
`RBM2D/Gauss/Model.lean:337`. -/
theorem Hflow_eq_realSmul (u : ℝ) (ω : Ω d L W) :
    Hflow d L W u ω = Real.sqrt u • Xmat d L W ω := by
  ext i j
  change (Real.sqrt u : ℂ) * Xentry d L W ω i j =
    Real.sqrt u • Xentry d L W ω i j
  rw [Complex.real_smul]

/-- `RBM2D/Gauss/Model.lean:344`. -/
theorem continuous_Hflow (u : ℝ) : Continuous (Hflow d L W u) := by
  have h : Hflow d L W u = fun ω : Ω d L W => Real.sqrt u • Xmat d L W ω :=
    funext (Hflow_eq_realSmul d L W u)
  rw [h]
  exact (continuous_Xmat d L W).const_smul (Real.sqrt u)

/-- `RBM2D/Gauss/Model.lean:350`. -/
theorem Hflow_isHermitian (u : ℝ) (ω : Ω d L W) :
    (Hflow d L W u ω).IsHermitian := by
  ext i j
  change (starRingEnd ℂ) ((Real.sqrt u : ℂ) * Xentry d L W ω j i) =
    (Real.sqrt u : ℂ) * Xentry d L W ω i j
  rw [map_mul, Complex.conj_ofReal, ← Xentry_swap]

/-- `RBM2D/Gauss/Model.lean:357`. -/
theorem measurable_Hflow (u : ℝ) (i j : Idx d L W) :
    Measurable fun ω : Ω d L W => Hflow d L W u ω i j := by
  simp only [fineModel_Hflow_apply]
  exact (measurable_Xentry d L W i j).const_mul _

/-- The entire time dependence is one scalar.  `RBM2D/Gauss/Model.lean:363`. -/
theorem Hflow_sub (u v : ℝ) (ω : Ω d L W) :
    Hflow d L W u ω - Hflow d L W v ω =
      ((Real.sqrt u - Real.sqrt v : ℝ) : ℂ) • Xmat d L W ω := by
  simp only [Hflow, Complex.ofReal_sub, sub_smul]

/-- Entrywise coordinate decomposition of the time increment.  `RBM2D/Gauss/Model.lean:369`. -/
theorem Hflow_sub_apply (u v : ℝ) (ω : Ω d L W) (i j : Idx d L W) :
    (Hflow d L W u ω - Hflow d L W v ω) i j =
      ((Real.sqrt u - Real.sqrt v : ℝ) : ℂ) * Xentry d L W ω i j := by
  rw [Hflow_sub]
  rfl

/-- The flow's entry variance is `u S_ij` for nonnegative time.  `RBM2D/Gauss/Model.lean:376`. -/
theorem integral_normSq_Hflow (u : ℝ) (hu : 0 ≤ u) (i j : Idx d L W) :
    ∫ ω, ‖Hflow d L W u ω i j‖ ^ 2 ∂(PF d L W g) = u * svarF d L W g i j := by
  simp only [fineModel_Hflow_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u), mul_pow]
  rw [integral_const_mul, integral_normSq_Xentry, Real.sq_sqrt hu]

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- Exact deterministic modulus for the operator norm along the one-time coupling.
`RBM2D/Gauss/Model.lean:387`. -/
theorem norm_Hflow_sub (u v : ℝ) (ω : Ω d L W) :
    ‖Hflow d L W u ω - Hflow d L W v ω‖ =
      |Real.sqrt u - Real.sqrt v| * ‖Xmat d L W ω‖ := by
  rw [Hflow_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]

end OperatorNorm

end ModelLemmas

/-! ### The sequence-level lemmas -/

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- `RBM2D/Gauss/Model.lean:448`. -/
theorem seqP_map_eval (c : SeqCoord sz) :
    (seqP sz).map (fun ω => ω c) = gaussianReal 0 (seqGvar sz c) :=
  Measure.infinitePi_map_eval _ c

/-- `RBM2D/Gauss/Model.lean:452`. -/
theorem seqP_map_restrict (I : Finset (SeqCoord sz)) :
    (seqP sz).map I.restrict = Measure.pi fun c : I => gaussianReal 0 (seqGvar sz c) :=
  Measure.infinitePi_map_restrict _

/-- `RBM2D/Gauss/Model.lean:499`, where `seqHflow` is the composite `Hflow ∘ slice`; here
`seqHflow` is the probe's definition `√u • seqXmat`, so the lemma is the definition. -/
theorem seqHflow_eq_smul (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    seqHflow sz n u ω = (Real.sqrt u : ℂ) • seqXmat sz n ω := rfl

/-- `RBM2D/Gauss/Model.lean:508`. -/
theorem seqHflow_isHermitian (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    (seqHflow sz n u ω).IsHermitian :=
  Hflow_isHermitian d (sz.L n) (sz.W n) u (slice sz n ω)

/-- `RBM2D/Gauss/Model.lean:511`. -/
theorem measurable_seqHflow_entry (n : ℕ) (u : ℝ)
    (i j : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω : SeqΩ sz => seqHflow sz n u ω i j :=
  (measurable_Hflow d (sz.L n) (sz.W n) u i j).comp (measurable_slice sz n)

/-- The size-`n` matrix has the paper's covariance under the common probability measure
(`(eq:variancematrix)`, `1_2:304`, with the coupling `sz.lam n`).  `RBM2D/Gauss/Model.lean:517`. -/
theorem integral_normSq_seqXmat (n : ℕ) (i j : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, ‖seqXmat sz n ω i j‖ ^ 2 ∂(seqP sz) =
      svarF d (sz.L n) (sz.W n) (sz.lam n) i j := by
  change ∫ ω, ‖Xentry d (sz.L n) (sz.W n) (slice sz n ω) i j‖ ^ 2 ∂(seqP sz) = _
  have hf : AEMeasurable (slice sz n) (seqP sz) := (measurable_slice sz n).aemeasurable
  have hg : AEStronglyMeasurable
      (fun v : Ω d (sz.L n) (sz.W n) => ‖Xentry d (sz.L n) (sz.W n) v i j‖ ^ 2)
      ((seqP sz).map (slice sz n)) := by
    exact ((measurable_Xentry d (sz.L n) (sz.W n) i j).norm.pow_const 2).aestronglyMeasurable
  rw [← integral_map hf hg, seqP_map_slice]
  exact integral_normSq_Xentry _ _ _ _ _ _

/-- The common-space flow has entry variance `u S_ij` at nonnegative time.
`RBM2D/Gauss/Model.lean:530`. -/
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

/-- Exact coordinate decomposition at every size on the common space.
`RBM2D/Gauss/Model.lean:544`. -/
theorem seqXmat_eq_sum_coordinates (n : ℕ) (ω : SeqΩ sz) :
    seqXmat sz n ω = ∑ c : CoordF d (sz.L n) (sz.W n),
      (ω ⟨n, c⟩) • coordinateMatrix d (sz.L n) (sz.W n) c :=
  Xmat_eq_sum_coordinates _ _ _ _

/-- Updating one common-space coordinate updates only its matrix direction at this size.
`RBM2D/Gauss/Model.lean:550`. -/
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

/-! ## 6. Checks at the preflight sequence (`d = 3`)

`SizesInst.sz0` of `RBM3D/Defs/Sizes.lean` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`,
`N = 2097152`, `W^d = 32768`.  Each `example` applies a theorem of this file at these data, every
hypothesis discharged. -/

section Checks

open SizesInst

/-- `svarF_eq_svar` at the instance: the fine-lattice profile is the merged block-product one. -/
example (i j : Idx 3 4 32) :
    svarF 3 4 32 (1 / 64) i j = svar 3 4 32 (1 / 64) (split 3 4 32 i) (split 3 4 32 j) :=
  svarF_eq_svar 3 4 32 (1 / 64) i j

/-- `svarF_eq_svar` and `integral_normSq_Xentry` at size `0` of the admissible sequence `sz0`
(`L = 4`, `W = 32`, `lam = 1/64`, read off `sz0` itself). -/
example (i j : Idx 3 (sz0.L 0) (sz0.W 0)) :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j =
        svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (split 3 (sz0.L 0) (sz0.W 0) i)
          (split 3 (sz0.L 0) (sz0.W 0) j) ∧
      ∫ ω, ‖Xentry 3 (sz0.L 0) (sz0.W 0) ω i j‖ ^ 2 ∂(PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0)) =
        svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j :=
  ⟨svarF_eq_svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j,
    integral_normSq_Xentry 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j⟩

/-- `E|X_xx|² = S_xx = (W^3)⁻¹ (1 + 6 g²)⁻¹ > 0` on the diagonal (one real coordinate). -/
example : ∫ ω, ‖Xentry 3 4 32 ω 0 0‖ ^ 2 ∂(PF 3 4 32 (1 / 64)) =
    ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹ := by
  rw [integral_normSq_Xentry, svarF_diag]; norm_num

/-- `E|X_xy|² = S_xy = (W^3)⁻¹ g² (1 + 6 g²)⁻¹ > 0` off the diagonal (two real coordinates), for
`x = 0` and `y = (32, 0, 0)`, whose blocks are the neighbours `0` and `(1, 0, 0)` of `Z_4^3`. -/
example : ∫ ω, ‖Xentry 3 4 32 ω 0 ![32, 0, 0]‖ ^ 2 ∂(PF 3 4 32 (1 / 64)) =
    ((32 : ℝ) ^ 3)⁻¹ * ((1 / 64 : ℝ) ^ 2 * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹) := by
  rw [integral_normSq_Xentry]
  have h1 : (split 3 4 32 (0 : Idx 3 4 32)).1 = 0 := by decide
  have h2 : (split 3 4 32 (![32, 0, 0] : Idx 3 4 32)).1 = ![1, 0, 0] := by decide
  have h3 : zdistD 3 4 (-(![1, 0, 0] : Zd 3 4)) = 1 := by decide
  have h4 : (-(![1, 0, 0] : Zd 3 4)) ≠ 0 := by decide
  simp only [svarF, SBR, Matrix.of_apply, h1, h2, zero_sub, sbKernelR, h3, h4, ite_false,
    ite_true, zero_add]
  norm_num

/-- The rows of the fine-lattice variance profile sum to `1` (`Σ_y S_xy = 1`, `(eq:variancematrix)`
`1_2:304`): `W^d` points per block, `W^{-d}` per point, and the row sum `1` of `S^(B)(g)`
(`sum_sbKernelR`, `3 ≤ L`). -/
example (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g : ℝ) (i : Idx d L W) :
    ∑ j, svarF d L W g i j = 1 := by
  classical
  have h1 : ∑ j : Idx d L W, svarF d L W g i j =
      ∑ p : Vtx d L W, ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 p.1 :=
    Fintype.sum_equiv (splitEquiv d L W) _ _ fun j => rfl
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  have h2 : ∑ x : Zd d L, SBR d L g (split d L W i).1 x = 1 := by
    simp only [SBR, Matrix.of_apply]
    rw [← sum_sbKernelR d L g hL]
    exact Fintype.sum_equiv (Equiv.subLeft (split d L W i).1) _ _ fun x => rfl
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← h2]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  field_simp

/-- The size projection of the common product has the one-size law, at the instance. -/
example : (Sizes.seqP sz0).map (Sizes.slice sz0 0) = PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) :=
  Sizes.seqP_map_slice sz0 0

/-- The common product is a probability measure at the instance. -/
example : IsProbabilityMeasure (Sizes.seqP sz0) := inferInstance

/-- `E|X_xx|² = S_xx > 0` for the size-`0` matrix on the common space. -/
example : ∫ ω, ‖sz0.seqXmat 0 ω 0 0‖ ^ 2 ∂(Sizes.seqP sz0) =
    ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹ := by
  rw [Sizes.integral_normSq_seqXmat, svarF_diag, sz0_values.2.1, sz0_values.2.2.2]
  norm_num

/-- The flow at time `u = 4` has entry variance `4 S_xx`. -/
example : ∫ ω, ‖sz0.seqHflow 0 4 ω 0 0‖ ^ 2 ∂(Sizes.seqP sz0) =
    4 * (((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹) := by
  rw [Sizes.integral_normSq_seqHflow sz0 0 4 (by norm_num), svarF_diag, sz0_values.2.1,
    sz0_values.2.2.2]
  norm_num

/-- `H` and `H_u` are Hermitian at the instance, for every sample point and time. -/
example (u : ℝ) (ω : Sizes.SeqΩ sz0) :
    (sz0.seqXmat 0 ω).IsHermitian ∧ (sz0.seqHflow 0 u ω).IsHermitian :=
  ⟨Sizes.seqXmat_isHermitian sz0 0 ω, Sizes.seqHflow_isHermitian sz0 0 u ω⟩

/-- The coordinate decomposition and the one-coordinate update at the instance. -/
example (ω : Sizes.SeqΩ sz0) (c : CoordF 3 (sz0.L 0) (sz0.W 0)) (t : ℝ) :
    sz0.seqXmat 0 ω = ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0),
        (ω ⟨0, c⟩) • coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c ∧
      sz0.seqXmat 0 (Function.update ω ⟨0, c⟩ t) =
        sz0.seqXmat 0 ω + (t - ω ⟨0, c⟩) • coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c :=
  ⟨Sizes.seqXmat_eq_sum_coordinates sz0 0 ω, Sizes.seqXmat_update sz0 0 ω c t⟩

/-- The time increment of the flow is one scalar times the matrix (`Hflow_sub`), at `d = 3`,
`L = 4`, `W = 32`. -/
example (u v : ℝ) (ω : Ω 3 4 32) :
    Hflow 3 4 32 u ω - Hflow 3 4 32 v ω = ((Real.sqrt u - Real.sqrt v : ℝ) : ℂ) • Xmat 3 4 32 ω :=
  Hflow_sub 3 4 32 u v ω

/-- Each independent real coordinate is a centred Gaussian of variance `gvarF` (`P_map_eval`,
`integral_sq_coord`), at `d = 3`, `L = 4`, `W = 32`, `g = 1/64`. -/
example (c : CoordF 3 4 32) :
    (PF 3 4 32 (1 / 64)).map (fun ω => ω c) = gaussianReal 0 (gvarF 3 4 32 (1 / 64) c) ∧
      ∫ ω, (ω c) ^ 2 ∂(PF 3 4 32 (1 / 64)) = (gvarF 3 4 32 (1 / 64) c : ℝ) :=
  ⟨P_map_eval 3 4 32 (1 / 64) c, integral_sq_coord 3 4 32 (1 / 64) c⟩

/-- The remaining fixed-size lemmas of section 5 at `d = 3`, `L = 4`, `W = 32`, `g = 1/64`, at the
times `u = 4`, `v = 1`. -/
example (ω ν : Ω 3 4 32) (t : ℝ) (c : CoordF 3 4 32) (i j : Idx 3 4 32)
    (I : Finset (CoordF 3 4 32)) :
    (PF 3 4 32 (1 / 64)).map I.restrict =
        Measure.pi (fun c : I => gaussianReal 0 (gvarF 3 4 32 (1 / 64) c)) ∧
      Measurable (fun ω : Ω 3 4 32 => Xentry 3 4 32 ω i j) ∧
      Integrable (fun ω : Ω 3 4 32 => (ω c) ^ 2) (PF 3 4 32 (1 / 64)) ∧
      Xmat 3 4 32 (ω + ν) = Xmat 3 4 32 ω + Xmat 3 4 32 ν ∧
      Xmat 3 4 32 (t • ω) = t • Xmat 3 4 32 ω ∧
      Xlinear 3 4 32 ω = Xmat 3 4 32 ω ∧
      (coordinateMatrix 3 4 32 c).IsHermitian ∧
      Xmat 3 4 32 (Function.update ω c t) =
        Xmat 3 4 32 ω + (t - ω c) • coordinateMatrix 3 4 32 c ∧
      Xmat 3 4 32 ω = ∑ c : CoordF 3 4 32, (ω c) • coordinateMatrix 3 4 32 c ∧
      Continuous (Xmat 3 4 32) ∧
      Hflow 3 4 32 4 ω = Real.sqrt 4 • Xmat 3 4 32 ω ∧
      Continuous (Hflow 3 4 32 4) ∧ (Hflow 3 4 32 4 ω).IsHermitian ∧
      Measurable (fun ω : Ω 3 4 32 => Hflow 3 4 32 4 ω i j) ∧
      (Hflow 3 4 32 4 ω - Hflow 3 4 32 1 ω) i j =
        ((Real.sqrt 4 - Real.sqrt 1 : ℝ) : ℂ) * Xentry 3 4 32 ω i j ∧
      ∫ ω, ‖Hflow 3 4 32 4 ω i j‖ ^ 2 ∂(PF 3 4 32 (1 / 64)) = 4 * svarF 3 4 32 (1 / 64) i j :=
  ⟨P_map_restrict 3 4 32 (1 / 64) I, measurable_Xentry 3 4 32 i j,
    integrable_sq_coord 3 4 32 (1 / 64) c, Xmat_add 3 4 32 ω ν, Xmat_smul 3 4 32 t ω,
    rfl, coordinateMatrix_isHermitian 3 4 32 c, Xmat_update 3 4 32 ω c t,
    Xmat_eq_sum_coordinates 3 4 32 ω, continuous_Xmat 3 4 32, Hflow_eq_realSmul 3 4 32 4 ω,
    continuous_Hflow 3 4 32 4, Hflow_isHermitian 3 4 32 4 ω, measurable_Hflow 3 4 32 4 i j,
    Hflow_sub_apply 3 4 32 4 1 ω i j,
    integral_normSq_Hflow 3 4 32 (1 / 64) 4 (by norm_num) i j⟩

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- `‖H_4 - H_1‖ = ‖X‖` (`√4 - √1 = 1`): `norm_Hflow_sub` at `d = 3`, `L = 4`, `W = 32`. -/
example (ω : Ω 3 4 32) :
    ‖Hflow 3 4 32 4 ω - Hflow 3 4 32 1 ω‖ = ‖Xmat 3 4 32 ω‖ := by
  rw [norm_Hflow_sub, show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num), Real.sqrt_one]
  norm_num

end OperatorNorm

/-- The remaining sequence-level lemmas at `sz0`, `n = 0`. -/
example (c : Sizes.SeqCoord sz0) (I : Finset (Sizes.SeqCoord sz0)) (u : ℝ) (ω : Sizes.SeqΩ sz0)
    (i j : Idx 3 (sz0.L 0) (sz0.W 0)) :
    (Sizes.seqP sz0).map (fun ω => ω c) = gaussianReal 0 (Sizes.seqGvar sz0 c) ∧
      (Sizes.seqP sz0).map I.restrict =
        Measure.pi (fun c : I => gaussianReal 0 (Sizes.seqGvar sz0 c)) ∧
      sz0.seqHflow 0 u ω = (Real.sqrt u : ℂ) • sz0.seqXmat 0 ω ∧
      Measurable (fun ω : Sizes.SeqΩ sz0 => sz0.seqHflow 0 u ω i j) :=
  ⟨Sizes.seqP_map_eval sz0 c, Sizes.seqP_map_restrict sz0 I, Sizes.seqHflow_eq_smul sz0 0 u ω,
    Sizes.measurable_seqHflow_entry sz0 0 u i j⟩

end Checks

end RBM.Gauss
