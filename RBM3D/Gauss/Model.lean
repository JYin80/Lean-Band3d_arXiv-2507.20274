/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4
import RBM3D.Gauss.SteinMatrix
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Gaussian band matrix, as a measure on its independent entries

`(bandcw0)` and `(eq:variancematrix)`: `H = (H_xy : x, y ∈ Z_L^d)` is a complex Hermitian
Gaussian matrix whose entries are independent up to `H_xy = conj H_yx`, with

  `H_xy ~ N_ℝ(0, S_xy) 1_{x=y} + N_ℂ(0, S_xy) 1_{x≠y}`,  `S_xy = W^{-d} S^(B)_{ab}`

for `x ∈ [a]`, `y ∈ [b]`.  A vertex is therefore a block label together with a position
inside the block, which is `RBM.Gauss.Vtx d L W = Z_L^d × Fin (W^d)`, and the variance
depends only on the two block labels.

## The independent coordinates

Hermitian symmetry means the independent real coordinates are indexed by *ordered* pairs
`(x, y)` with a `Bool` selecting real or imaginary part, of which only those with
`vkey x ≤ vkey y` are read: `vkey` is an injection of the (finite) vertex set into `ℕ`,
used only to decide which of `H_xy`, `H_yx` carries the coordinates.  The variance of one
coordinate is `S_xx` on the diagonal (a single real Gaussian) and `S_xy/2` off it (two
independent reals), so that `E|H_xy|² = S_xy` in both cases.

## Fixed parameters, not a sequence

`RBM1D/Gauss/Model.lean` bundles `W(N)`, `L(N)` into a structure and builds **one** space
for the whole sequence, because its asymptotic statements quantify over `N` inside a single
probability space.  Here the model is built for fixed `d, L, W, g`, in the style of the rest
of this project: everything is parameterized, nothing is a sequence.  The coordinate set is
then finite, so the measure is `MeasureTheory.Measure.pi` rather than `Measure.infinitePi`,
and the box-uniqueness lemma available for the resampling step (`docs/QUEUE.md`, Q43b) is
`Measure.pi_eq`.

## Main definitions

* `RBM.Gauss.Vtx`, `RBM.Gauss.svar` : vertices and `(eq:variancematrix)`
* `RBM.Gauss.Coord`, `RBM.Gauss.Omega`, `RBM.Gauss.gvar`, `RBM.Gauss.P` : the independent
  coordinates and their law
* `RBM.Gauss.Hmat` : the matrix itself, and `RBM.Gauss.Hmat_isHermitian`
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable (d L W : ℕ) (g : ℝ)

/-! ### Vertices and the variance profile -/

/-- A vertex of the fine lattice: the block it lies in, and its position inside that block.
The paper writes `x ∈ [a]`; here `x.1 = a`. -/
abbrev Vtx : Type := Zd d L × Fin (W ^ d)

/-- **`(eq:variancematrix)`**: `S_xy = W^{-d} S^(B)_{ab}` for `x ∈ [a]`, `y ∈ [b]`. -/
noncomputable def svar (x y : Vtx d L W) : ℝ := ((W : ℝ) ^ d)⁻¹ * SBR d L g x.1 y.1

theorem svar_nonneg (x y : Vtx d L W) : 0 ≤ svar d L W g x y := by
  refine mul_nonneg (by positivity) ?_
  simpa [SBR] using sbKernelR_nonneg d L g (x.1 - y.1)

variable [NeZero L]

theorem svar_comm (x y : Vtx d L W) : svar d L W g x y = svar d L W g y x := by
  simp only [svar, SBR, Matrix.of_apply]
  rw [show y.1 - x.1 = -(x.1 - y.1) by ring, sbKernelR_neg]

/-! ### The independent coordinates -/

/-- An injection of the vertex set into `ℕ`.  Its only role is to decide which of `H_xy`,
`H_yx` carries the independent coordinates. -/
noncomputable def vkey (x : Vtx d L W) : ℕ := (Fintype.equivFin (Vtx d L W) x).val

theorem vkey_injective : Function.Injective (vkey d L W) := fun _ _ h =>
  (Fintype.equivFin (Vtx d L W)).injective (Fin.val_injective h)

/-- The independent real coordinates: `(x, y, b)` with `b = true` the real part and
`b = false` the imaginary part of `H_xy`.  Only the pairs with `vkey x ≤ vkey y` are read
by `Hmat`. -/
abbrev Coord : Type := Vtx d L W × Vtx d L W × Bool

/-- The sample space: one real coordinate per element of `Coord`. -/
abbrev Omega : Type := Coord d L W → ℝ

/-- The variance of one coordinate: `S_xx` on the diagonal (a single real Gaussian),
`S_xy/2` off it (two independent reals), so that `E|H_xy|² = S_xy` in both cases. -/
noncomputable def gvar (c : Coord d L W) : ℝ≥0 :=
  ⟨if c.1 = c.2.1 then svar d L W g c.1 c.2.1 else svar d L W g c.1 c.2.1 / 2, by
    split_ifs
    · exact svar_nonneg d L W g _ _
    · exact div_nonneg (svar_nonneg d L W g _ _) (by norm_num)⟩

/-- The law of the independent coordinates. -/
noncomputable def P : Measure (Omega d L W) :=
  Measure.pi fun c => gaussianReal 0 (gvar d L W g c)

instance isProbabilityMeasure_P : IsProbabilityMeasure (P d L W g) := by
  unfold P; infer_instance

/-! ### The matrix -/

/-- **`(bandcw0)`**: the Hermitian matrix built from the independent coordinates.  The
entry `H_xy` is read off the coordinates `(x, y, ·)` when `vkey x < vkey y`, conjugated from
`(y, x, ·)` when `vkey y < vkey x`, and is real on the diagonal. -/
noncomputable def Hmat (ω : Omega d L W) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.of fun x y =>
    if vkey d L W x < vkey d L W y then (ω (x, y, true) : ℂ) + (ω (x, y, false) : ℂ) * Complex.I
    else if vkey d L W y < vkey d L W x then
      (ω (y, x, true) : ℂ) - (ω (y, x, false) : ℂ) * Complex.I
    else (ω (x, y, true) : ℂ)

theorem Hmat_isHermitian (ω : Omega d L W) : (Hmat d L W ω).IsHermitian := by
  ext x y
  rcases lt_trichotomy (vkey d L W x) (vkey d L W y) with h | h | h
  · have h' : ¬ vkey d L W y < vkey d L W x := by omega
    simp [Matrix.conjTranspose_apply, Hmat, h, h']
  · have hxy : x = y := vkey_injective d L W h
    subst hxy
    simp [Matrix.conjTranspose_apply, Hmat]
  · have h' : ¬ vkey d L W x < vkey d L W y := by omega
    simp [Matrix.conjTranspose_apply, Hmat, h, h', Complex.ext_iff]

/-! ### Resampling one coordinate leaves the law invariant

This is the one place where independence is used.  Replacing the `c`-th coordinate by an
independent sample of its own law does not change `P`:

  `(P ⊗ γ_c).map (upd c) = P`.

Both sides are probability measures on a finite product, so it is enough to compare them on
measurable boxes (`MeasureTheory.Measure.pi_eq`); the preimage of a box under `upd c` is
again a box, with `univ` in the `c`-th slot. -/

omit [NeZero L] in
theorem preimage_upd_univ_pi (c : Coord d L W) (s : Coord d L W → Set ℝ) :
    upd c ⁻¹' (Set.univ.pi s) = (Set.univ.pi (Function.update s c Set.univ)) ×ˢ s c := by
  ext ⟨ω, t⟩
  constructor
  · intro h
    refine ⟨fun i _ => ?_, ?_⟩
    · by_cases hi : i = c
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using (by
          simpa [upd_of_ne c (ω, t) hi] using h i (Set.mem_univ i))
    · simpa [upd_self] using h c (Set.mem_univ c)
  · rintro ⟨hbox, hc⟩ i _
    by_cases hi : i = c
    · subst hi; simpa [upd_self] using hc
    · have := hbox i (Set.mem_univ i)
      rw [Function.update_of_ne hi] at this
      simpa [upd_of_ne c (ω, t) hi] using this

/-- **The invariance used by the resampling route.**  `(P ⊗ γ_c).map (upd c) = P`: the only
step of the stochastic layer that uses independence of the entries. -/
theorem P_map_update (c : Coord d L W) :
    ((P d L W g).prod (gaussianReal 0 (gvar d L W g c))).map (upd c) = P d L W g := by
  change _ = Measure.pi fun i => gaussianReal 0 (gvar d L W g i)
  refine (Measure.pi_eq (μ := fun i => gaussianReal 0 (gvar d L W g i)) fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_upd c) (MeasurableSet.univ_pi hs), preimage_upd_univ_pi,
    Measure.prod_prod, P, Measure.pi_pi]
  have hupd : ∀ i, (gaussianReal 0 (gvar d L W g i)) (Function.update s c Set.univ i)
      = Function.update (fun i => (gaussianReal 0 (gvar d L W g i)) (s i)) c 1 i := by
    intro i
    by_cases hi : i = c
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  simp only [hupd]
  rw [Finset.prod_update_of_mem (Finset.mem_univ c), one_mul,
    Finset.sdiff_singleton_eq_erase,
    ← Finset.prod_erase_mul Finset.univ
      (fun i => (gaussianReal 0 (gvar d L W g i)) (s i)) (Finset.mem_univ c)]

end RBM.Gauss
