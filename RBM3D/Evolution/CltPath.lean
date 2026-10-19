/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltResolvent
import RBM3D.Induction.Step5Pins

/-!
# The pointwise path bound of the replacement step

On the fine model `RBM3D/Gauss/FineModel.lean`, in the vocabulary of
`RBM3D/Evolution/CltResolvent.lean` (`Zd d L` for the block lattice, `zdistInf d L` for the
distance, `CoordF d L W` for the coordinates, `split` for the block splitting, `zt` for the
spectral path).  The scale is a parameter: the locality radius `ρ`, the separation `R` and the far
threshold `θ` of `cltGoodAt` are real parameters with

* `F.Local ρ` (every entry of a monomial is within `ρ` of a label),
* `R / 2 ≤ |[c.1] - b|_∞` (the first block of the replaced coordinate is far from the label),
* `θ ≤ R / 2 - ρ - 1` (`cltFarGeomNear`),

so that at `ρ = (log W)^3 ℓ_s`, `R = 10 (log W)^3 ℓ_s` the good set is the one with the far
threshold `θ = 4 (log W)^3 ℓ_s - 1 ≥ (log W)^3 ℓ_s` of the log-scale far decay of entries.

* `CltPathBoundMulti d L W k`, proved at `H₀ + H_u(ω)` as `cltPathMulti_boundOf`: along the segment
  that moves one coordinate `c` (whose two blocks are adjacent and far from the labels
  `b : Fin k → Zd d L`, all at once) from `ω₀ c` to `s`, the local form `cltYo F E u · b` with `k`
  labels changes by at most `|s - ω₀ c| · 4 · cltCoefSum F b · W^{-D'}` on the good set
  `cltGoodAt`.

The proof is the mean-value inequality on the segment.  At every point of the segment the matrix is
`Hflow u ω₀ + t • A`, `A = √u • coordinateMatrix c`, `|t| ≤ 2 W^{-1/2}`: all entries of the
perturbed resolvent are `≤ 4` (`cltPert_max_le`), the entries `G_t(σ)_{x a₀}`, `G_t(σ)_{x b₀}` for
the left index `x` of a monomial local to `b` are `≤ 2 W^{-D'}` (`cltFarGeomNear`, `cltGoodAt`,
`cltPert_sub_le`), and `cltpath_deriv` bounds the derivative along the path.  The step
length `|t| ≤ 2 W^{-1/2}` and the hypothesis `16 W^{-1/2} ≤ 1` are dimension free.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open Matrix RBM RBM.Gauss

/-! ## 1. The definitions -/

section Step

variable {d L W K k : ℕ} [NeZero L] [NeZero W]

/-- `Y_b(ω)` on the finite model with `k` labels: the local form at `H_u(ω)` (`clt-yform`). -/
def cltEvalAt (F : LocalForm d L W k K) (E u : ℝ) (ω : Ω d L W) (b : Fin k → Zd d L) : ℂ :=
  F.eval E u (Hflow d L W u ω) b

/-- `Y_b(ω)` at the matrix `H₀ + H_u(ω)` and the spectral value `m` (band: `H₀ = 0`, `m = mE E`). -/
def cltEvalAtOf (F : LocalForm d L W k K) (m : ℂ) (E u : ℝ) (H₀ : Matrix (Idx d L W) (Idx d L W) ℂ)
    (ω : Ω d L W) (b : Fin k → Zd d L) : ℂ :=
  F.evalOf m E u (H₀ + Hflow d L W u ω) b

/-- The coefficient weight `Σ_{j,q} |coef(b,j,q)| · j · 4^j` of the first-order bound
`cltpath_deriv` at `g = 4`, `k` labels. -/
def cltCoefSumMulti (F : LocalForm d L W k K) (b : Fin k → Zd d L) : ℝ :=
  ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
    ‖F.coef b j q‖ * (j : ℝ) * 4 ^ (j : ℕ)

end Step

/-- The deterministic good set at one sample point: all entries of `G_u(±)` are `≤ 2`, and the
entries whose blocks are at distance `≥ θ` (the far threshold) are `≤ W^{-D'}` (the events of
`CltGmaxWhpOf`, `CltFarEntryWhpOf`). -/
def cltGoodAt (d L W : ℕ) [NeZero L] [NeZero W] (E u θ D' : ℝ) (ω : Ω d L W) : Prop :=
  (∀ σ x y, ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ 2) ∧
    ∀ σ x y, θ ≤ (zdistInf d L ((split d L W x).1 - (split d L W y).1) : ℝ) →
      ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ (W : ℝ) ^ (-D')

/-- The deterministic good set at `H₀ + H_u(ω)` and the spectral value `m` (band: `H₀ = 0`, `m = mE E`). -/
def cltGoodAtOf (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u θ D' : ℝ)
    (H₀ : Matrix (Idx d L W) (Idx d L W) ℂ) (ω : Ω d L W) : Prop :=
  (∀ σ x y, ‖gEntryOf d L W m E u (H₀ + Hflow d L W u ω) σ x y‖ ≤ 2) ∧
    ∀ σ x y, θ ≤ (zdistInf d L ((split d L W x).1 - (split d L W y).1) : ℝ) →
      ‖gEntryOf d L W m E u (H₀ + Hflow d L W u ω) σ x y‖ ≤ (W : ℝ) ^ (-D')

/-- **The path bound**, `k` labels (deterministic).  At a good sample point `ω₀` (far threshold
`θ ≤ R/2 - ρ - 1`), for a coordinate
`c` whose two blocks are adjacent and whose first block is at distance `≥ R/2` from every label
`b_m`, moving `c` from `ω₀ c` to `s` (`|s - ω₀ c| ≤ 2 W^{-1/2}`) changes `Y_b` by at most
`|s - ω₀ c| · 4 · cltCoefSum F b · W^{-D'}`, for a local form `F` that is `ρ`-local.  Inputs:
`CltPertMaxLe`, `CltPertSubLe`, `CltFarGeomNear`, `CltCoordAdj`,
`Xmat_update`.  Consumers: `CltStep` (case A with `ω₀ = T_k`, `s = ω' c`; case B with `ω₀ = ω`,
`s = 0`). -/
def CltPathBoundMulti (d L W k : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm d L W k K) (E u ρ R θ D' : ℝ) (b : Fin k → Zd d L) (c : CoordF d L W)
    (ω₀ : Ω d L W) (s : ℝ),
    0 ≤ u → u < 1 → (zt E u).im ≠ 0 → F.Local ρ → 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 →
    zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1 →
    (∀ m, R / 2 ≤ (zdistInf d L ((split d L W c.1).1 - b m) : ℝ)) → θ ≤ R / 2 - ρ - 1 →
    cltGoodAt d L W E u θ D' ω₀ →
    |s - ω₀ c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) →
    ‖cltEvalAt F E u (Function.update ω₀ c s) b - cltEvalAt F E u ω₀ b‖ ≤
      |s - ω₀ c| * 4 * cltCoefSumMulti F b * (W : ℝ) ^ (-D')

/-- **The path bound** at `H₀ + H_u(ω)` and the spectral value `m`, `k` labels: `H₀` is a
deterministic Hermitian matrix; `cltCoefSumMulti` is spectrum-free. -/
def CltPathBoundMultiOf (d L W k : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm d L W k K) (m : ℂ) (E u ρ R θ D' : ℝ) (H₀ : Matrix (Idx d L W) (Idx d L W) ℂ)
    (b : Fin k → Zd d L) (c : CoordF d L W) (ω₀ : Ω d L W) (s : ℝ),
    H₀.IsHermitian → 0 ≤ u → u < 1 → (ztOf m E u).im ≠ 0 → F.Local ρ → 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 →
    zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1 →
    (∀ m', R / 2 ≤ (zdistInf d L ((split d L W c.1).1 - b m') : ℝ)) → θ ≤ R / 2 - ρ - 1 →
    cltGoodAtOf d L W m E u θ D' H₀ ω₀ →
    |s - ω₀ c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) →
    ‖cltEvalAtOf F m E u H₀ (Function.update ω₀ c s) b - cltEvalAtOf F m E u H₀ ω₀ b‖ ≤
      |s - ω₀ c| * 4 * cltCoefSumMulti F b * (W : ℝ) ^ (-D')

/-! ## 2. Private helpers -/

section Helpers

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `√u • coordinateMatrix c` is a `cltCoordDir` for `0 ≤ u ≤ 1` (the last two conjuncts of
`cltCoord_adj`, which holds for every `g`). -/
private theorem cltpath_coordDir {u : ℝ} (hu1 : u ≤ 1) (c : CoordF d L W) :
    cltCoordDir ((Real.sqrt u : ℂ) • coordinateMatrix d L W c) c.1 c.2.1 := by
  have hs0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hs1 : Real.sqrt u ≤ 1 := Real.sqrt_le_one.2 hu1
  have hc := cltCoord_adj d L W 0 c
  refine ⟨?_, fun a b => ?_, fun a b hab => ?_⟩
  · have h : (0 + (Real.sqrt u : ℂ) • coordinateMatrix d L W c).IsHermitian := by
      refine Matrix.isHermitian_zero.add ?_
      change Matrix.conjTranspose ((Real.sqrt u : ℂ) • coordinateMatrix d L W c) = _
      rw [Matrix.conjTranspose_smul, coordinateMatrix_isHermitian d L W c, Complex.star_def,
        Complex.conj_ofReal]
    rwa [zero_add] at h
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0]
    calc Real.sqrt u * ‖coordinateMatrix d L W c a b‖ ≤ 1 * 1 :=
          mul_le_mul hs1 (hc.2.2 a b) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · refine hc.2.1 a b fun h0 => hab ?_
    rw [Matrix.smul_apply, smul_eq_mul, h0, mul_zero]

/-- The spectral parameter of the `σ`-resolvent in `gEntryOf`. -/
private def cltpath_zs (m : ℂ) (E u : ℝ) (σ : Bool) : ℂ :=
  if σ then ztOf m E u else (starRingEnd ℂ) (ztOf m E u)

private theorem cltpath_zs_im {m : ℂ} {E u : ℝ} (hz : (ztOf m E u).im ≠ 0) (σ : Bool) :
    (cltpath_zs m E u σ).im ≠ 0 := by
  cases σ <;> simpa [cltpath_zs] using hz

private theorem cltpath_gEntry (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool)
    (x y : Idx d L W) : gEntryOf d L W m E u M σ x y = green M (cltpath_zs m E u σ) x y := by
  simp only [gEntryOf, Gres, green, cltpath_zs, Matrix.nonsing_inv_eq_ringInverse]

private theorem cltpath_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

/-- Moving the coordinate `c` of `ω₀` to `x` moves `Hflow` by `(x - ω₀ c) • A`,
`A = √u • coordinateMatrix c`. -/
private theorem cltpath_Hflow_update (u : ℝ) (ω₀ : Ω d L W) (c : CoordF d L W) (x : ℝ) :
    Hflow d L W u (Function.update ω₀ c x) =
      Hflow d L W u ω₀ + (((x - ω₀ c : ℝ)) : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix d L W c) := by
  rw [Hflow, Xmat_update, smul_add, ← Complex.coe_smul, smul_comm, Hflow]

/-- The mean-value inequality on `[-R, R]` for a function with a derivative bounded by `C` at each
point of the interval. -/
private theorem cltpath_mvt (h : ℝ → ℂ) (R C v : ℝ)
    (hD : ∀ t : ℝ, |t| ≤ R → ∃ D : ℂ, HasDerivAt h D t ∧ ‖D‖ ≤ C) (hv : |v| ≤ R) :
    ‖h v - h 0‖ ≤ C * |v| := by
  have hR : 0 ≤ R := (abs_nonneg v).trans hv
  have hmem : ∀ t : ℝ, t ∈ Set.Icc (-R) R ↔ |t| ≤ R := fun t => by
    rw [Set.mem_Icc, abs_le]
  have hf : ∀ t ∈ Set.Icc (-R) R, DifferentiableAt ℝ h t := fun t ht =>
    let ⟨_, hD1, _⟩ := hD t ((hmem t).1 ht)
    hD1.differentiableAt
  have hb : ∀ t ∈ Set.Icc (-R) R, ‖deriv h t‖ ≤ C := fun t ht =>
    let ⟨D, hD1, hD2⟩ := hD t ((hmem t).1 ht)
    hD1.deriv ▸ hD2
  have := Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_Icc (-R) R)
    ((hmem 0).2 (by simpa using hR)) ((hmem v).2 hv)
  simpa using this

/-- One point of the path: at `t` with `|t| ≤ 2 W^{-1/2}` the local form along the line
`M₀ + s A` has a derivative of norm at most `4 W^{-D'} cltCoefSumMulti F b`. -/
private theorem cltpath_deriv (K : ℕ) {k : ℕ} (F : LocalForm d L W k K) (mc : ℂ) (E u ρ R θ D' : ℝ)
    (H₀ : Matrix (Idx d L W) (Idx d L W) ℂ) (hH₀ : H₀.IsHermitian)
    (b : Fin k → Zd d L) (c : CoordF d L W) (ω₀ : Ω d L W) (hu1 : u < 1)
    (hz : (ztOf mc E u).im ≠ 0) (hloc : F.Local ρ) (hθ : 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1)
    (hadj : zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1)
    (hfar : ∀ m, R / 2 ≤ (zdistInf d L ((split d L W c.1).1 - b m) : ℝ)) (hθR : θ ≤ R / 2 - ρ - 1)
    (hgood : cltGoodAtOf d L W mc E u θ D' H₀ ω₀)
    (t : ℝ) (ht : |t| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) :
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => F.evalOf mc E u (H₀ + Hflow d L W u ω₀ +
        (s : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix d L W c)) b) D t ∧
      ‖D‖ ≤ 4 * (W : ℝ) ^ (-D') * cltCoefSumMulti F b := by
  set A : Matrix (Idx d L W) (Idx d L W) ℂ := (Real.sqrt u : ℂ) • coordinateMatrix d L W c with hA
  set M₀ : Matrix (Idx d L W) (Idx d L W) ℂ := H₀ + Hflow d L W u ω₀ with hM₀
  set γ : ℝ := (W : ℝ) ^ (-D') with hγdef
  have hγ0 : 0 ≤ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hherm : M₀.IsHermitian := hH₀.add (Hflow_isHermitian d L W u ω₀)
  have hdir : cltCoordDir A c.1 c.2.1 := cltpath_coordDir hu1.le c
  have h8 : 8 * |t| ≤ 1 := by linarith
  have hzσ : ∀ σ, (cltpath_zs mc E u σ).im ≠ 0 := cltpath_zs_im hz
  have hG0 : ∀ σ x y, ‖green M₀ (cltpath_zs mc E u σ) x y‖ ≤ 2 := fun σ x y => by
    rw [← cltpath_gEntry]; exact hgood.1 σ x y
  have hGt : ∀ σ x y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs mc E u σ) x y‖ ≤ 4 := fun σ x y => by
    have h := cltPert_max_le (Idx d L W) M₀ A c.1 c.2.1 (cltpath_zs mc E u σ) t 2 hherm hdir (hzσ σ)
      (hG0 σ) (by linarith) x y
    linarith
  have hnear : ∀ (j : Fin (K + 1)) (q : Fin j → Idx d L W × Idx d L W × Bool),
      F.coef b j q ≠ 0 → ∀ (i : Fin j) (σ : Bool),
        ‖gEntryOf d L W mc E u (M₀ + (t : ℂ) • A) σ (q i).1 c.1‖ ≤ 2 * γ ∧
          ‖gEntryOf d L W mc E u (M₀ + (t : ℂ) • A) σ (q i).1 c.2.1‖ ≤ 2 * γ := by
    intro j q hq i σ
    obtain ⟨m, hm⟩ := hloc b j q hq i
    have hm' : (zdistInf d L ((split d L W (q i).1).1 - b m) : ℝ) < ρ := by
      have h0 : (0 : ℝ) ≤ (zdistInf d L ((split d L W (q i).2.1).1 - b m) : ℝ) := Nat.cast_nonneg _
      push_cast at hm
      linarith
    have hadj' : zdistInf d L ((split d L W c.2.1).1 - (split d L W c.1).1) ≤ 1 := by
      have h := cltpath_zdistInf_neg (d := d) (L := L)
        ((split d L W c.1).1 - (split d L W c.2.1).1)
      rw [neg_sub] at h
      rw [h]
      exact hadj
    obtain ⟨h1, h2⟩ := cltFarGeomNear d L ρ R (split d L W c.1).1 (split d L W c.2.1).1 (b m)
      (split d L W (q i).1).1 (hfar m) hadj' hm'
    have ha := hgood.2 σ (q i).1 c.1 (hθR.trans h1)
    have hb := hgood.2 σ (q i).1 c.2.1 (hθR.trans h2)
    rw [cltpath_gEntry] at ha hb
    have hmax : max ‖green M₀ (cltpath_zs mc E u σ) (q i).1 c.1‖
        ‖green M₀ (cltpath_zs mc E u σ) (q i).1 c.2.1‖ ≤ γ := max_le ha hb
    have hsub := (cltPert_sub_le (Idx d L W) M₀ A c.1 c.2.1 (cltpath_zs mc E u σ) t 4 hherm hdir
      (hzσ σ) (hGt σ) (q i).1)
    have key : ∀ y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs mc E u σ) (q i).1 y -
        green M₀ (cltpath_zs mc E u σ) (q i).1 y‖ ≤ γ ∧ ‖green M₀ (cltpath_zs mc E u σ) (q i).1 y‖ ≤ γ →
        ‖green (M₀ + (t : ℂ) • A) (cltpath_zs mc E u σ) (q i).1 y‖ ≤ 2 * γ := fun y hy => by
      have := norm_sub_norm_le (green (M₀ + (t : ℂ) • A) (cltpath_zs mc E u σ) (q i).1 y)
        (green M₀ (cltpath_zs mc E u σ) (q i).1 y)
      linarith [hy.1, hy.2]
    have hstep : ∀ y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs mc E u σ) (q i).1 y -
        green M₀ (cltpath_zs mc E u σ) (q i).1 y‖ ≤ γ := fun y => by
      calc _ ≤ 2 * |t| * 4 * max ‖green M₀ (cltpath_zs mc E u σ) (q i).1 c.1‖
              ‖green M₀ (cltpath_zs mc E u σ) (q i).1 c.2.1‖ := (hsub y).1
        _ ≤ 2 * |t| * 4 * γ := by gcongr
        _ ≤ γ := by nlinarith [mul_le_mul_of_nonneg_right h8 hγ0]
    refine ⟨?_, ?_⟩
    · rw [cltpath_gEntry]; exact key _ ⟨hstep _, ha⟩
    · rw [cltpath_gEntry]; exact key _ ⟨hstep _, hb⟩
  obtain ⟨D, hD, hDb⟩ := cltDeriv_evalMulti_leOf d L W k K F mc E u M₀ A c.1 c.2.1 t 4 (2 * γ) b hherm
    hdir hz (fun σ x y => by rw [cltpath_gEntry]; exact hGt σ x y) hnear
  refine ⟨D, hD, hDb.trans (le_of_eq ?_)⟩
  unfold cltCoefSumMulti
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  ring

end Helpers

/-! ## 3. The path bound -/

section Bound

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- **The path bound**, `k` labels, at `H₀ + H_u(ω)` and the spectral value `m` (`CltPathBoundMultiOf`): the mean-value
inequality along the segment that moves the coordinate `c` from `ω₀ c` to `s`. -/
theorem cltPathMulti_boundOf (k : ℕ) : CltPathBoundMultiOf d L W k := by
  intro K F m E u ρ R θ D' H₀ b c ω₀ s hH₀ hu0 hu1 hz hloc hθ hadj hfar hθR hgood hs
  set h : ℝ → ℂ := fun t => F.evalOf m E u (H₀ + Hflow d L W u ω₀ +
    (t : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix d L W c)) b with hh
  have hpath : ∀ x : ℝ, cltEvalAtOf F m E u H₀ (Function.update ω₀ c x) b = h (x - ω₀ c) := by
    intro x
    rw [cltEvalAtOf, cltpath_Hflow_update, ← add_assoc]
  have h0 : cltEvalAtOf F m E u H₀ ω₀ b = h 0 := by
    have := hpath (ω₀ c)
    rwa [Function.update_eq_self, sub_self] at this
  have hmvt := cltpath_mvt h (2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) (4 * (W : ℝ) ^ (-D') * cltCoefSumMulti F b)
    (s - ω₀ c)
    (fun t ht => cltpath_deriv K F m E u ρ R θ D' H₀ hH₀ b c ω₀ hu1 hz hloc hθ hadj hfar hθR hgood t ht) hs
  rw [hpath s, h0]
  calc _ ≤ _ := hmvt
    _ = _ := by ring

end Bound

end RBM.Evol
