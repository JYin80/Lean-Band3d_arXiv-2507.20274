/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltResolvent
import RBM3D.Induction.Step5Pins

/-!
# The pointwise path bound of the replacement step (ticket T2144, row S5-18, part 2)

Port of `RBM2D/Evolution/CltPath.lean` (320 lines, commit `c9a24cf`) onto the fine model
`RBM3D/Gauss/FineModel.lean`, with the dictionary of `RBM3D/Evolution/CltResolvent.lean`
(`Z2 L ↦ Zd d L`, `zdist2 ↦ zdistInf d L`, `Coord ↦ CoordF d L W`, `splitEquiv ↦ split`,
`spectralZ ↦ zt`).  The scale is a parameter: RBM2D has the locality radius `ℓ_u W^τ`
(`F.Local τ u`), the separation `W^{2τ} ℓ_u / 2` and the hypotheses `6 ≤ W^τ`, `1 ≤ ellT L u`;
here the locality radius `ρ`, the separation `R` and the far threshold `θ` of `cltGoodAt` are real
parameters with

* `F.Local ρ` (every entry of a monomial is within `ρ` of a label),
* `R / 2 ≤ |[c.1] - b|_∞` (the first block of the replaced coordinate is far from the label),
* `θ ≤ R / 2 - ρ - 1` (`cltFarGeomNear`),

so that at `ρ = (log W)^3 ℓ_s`, `R = 10 (log W)^3 ℓ_s` the good set is the one with the far
threshold `θ = 4 (log W)^3 ℓ_s - 1 ≥ (log W)^3 ℓ_s` of `STFarEntryAtLog` (T2141, DECISIONS §43).

* `cltPath_bound : CltPathBound d L W` (RBM2D `P1`): along the segment that moves one coordinate
  `c` (whose two blocks are adjacent and far from the label `b`) from `ω₀ c` to `s`, the local form
  `cltYo F E u · b` changes by at most `|s - ω₀ c| · 4 · cltCoefSum F b · W^{-D'}` on the good set
  `cltGoodAt`.
* `cltPathMulti_bound : CltPathBoundMulti d L W k`: the same for a local form with `k` labels
  `b : Fin k → Zd d L`, far from the first block of `c` all at once (`STcltB` has two labels,
  RBM2D one); `cltPath_bound` is its case `k = 1`.

The proof is the mean-value inequality on the segment.  At every point of the segment the matrix is
`Hflow u ω₀ + t • A`, `A = √u • coordinateMatrix c`, `|t| ≤ 2 W^{-1/2}`: all entries of the
perturbed resolvent are `≤ 4` (`cltPert_max_le`), the entries `G_t(σ)_{x a₀}`, `G_t(σ)_{x b₀}` for
the left index `x` of a monomial local to `b` are `≤ 2 W^{-D'}` (`cltFarGeomNear`, `cltGoodAt`,
`cltPert_sub_le`), and `cltDeriv_evalMulti_le` bounds the derivative along the path.  The step
length `|t| ≤ 2 W^{-1/2}` and the hypothesis `16 W^{-1/2} ≤ 1` are dimension free.
The instance at the end is at `Step5Inst.szCL`, `n = 0` (`d = 3`, `L = 2 · 24^5`, `W = 2^24`).
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

/-- `Y_b(ω)` on the finite model (`clt-yform`), one label.  RBM2D `CltPath.lean:51`. -/
def cltYo (F : LocalForm d L W 1 K) (E u : ℝ) (ω : Ω d L W) (b : Zd d L) : ℂ :=
  cltY F E u (Hflow d L W u ω) b

/-- The coefficient weight `Σ_{j,q} |coef(b,j,q)| · j · 4^j` of the first-order bound
`CltDerivEvalMulti` at `g = 4`, `k` labels. -/
def cltCoefSumMulti (F : LocalForm d L W k K) (b : Fin k → Zd d L) : ℝ :=
  ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
    ‖F.coef b j q‖ * (j : ℝ) * 4 ^ (j : ℕ)

/-- The coefficient weight, one label.  RBM2D `CltPath.lean:56`. -/
def cltCoefSum (F : LocalForm d L W 1 K) (b : Zd d L) : ℝ :=
  cltCoefSumMulti F (fun _ => b)

end Step

/-- The deterministic good set at one sample point: all entries of `G_u(±)` are `≤ 2`, and the
entries whose blocks are at distance `≥ θ` (the far threshold; `STFarEntryAtLog`, DECISIONS §43)
are `≤ W^{-D'}` (the events of `CltGmaxWhp`, `CltFarEntryWhp`).  RBM2D `CltPath.lean:63`
(threshold `ρ = ellT L u * W^τ`, distance `zdist2`). -/
def cltGoodAt (d L W : ℕ) [NeZero L] [NeZero W] (E u θ D' : ℝ) (ω : Ω d L W) : Prop :=
  (∀ σ x y, ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ 2) ∧
    ∀ σ x y, θ ≤ (zdistInf d L ((split d L W x).1 - (split d L W y).1) : ℝ) →
      ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ (W : ℝ) ^ (-D')

/-- **Pin P1**, `k` labels (the pointwise path bound; deterministic; `clt-ibp-decay`,
`clt-ibp-bound1` / `clt-ibp-bound3` at first order, with the perturbation bounds `clt-gij-bound`,
`clt-gij-decay`).  At a good sample point `ω₀` (far threshold `θ ≤ R/2 - ρ - 1`), for a coordinate
`c` whose two blocks are adjacent and whose first block is at distance `≥ R/2` from every label
`b_m`, moving `c` from `ω₀ c` to `s` (`|s - ω₀ c| ≤ 2 W^{-1/2}`) changes `Y_b` by at most
`|s - ω₀ c| · 4 · cltCoefSum F b · W^{-D'}`, for a local form `F` that is `ρ`-local.  Inputs:
`CltPertMaxLe`, `CltPertSubLe`, `CltDerivEvalMulti`, `CltFarGeomNear`, `CltCoordAdj`,
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

/-- **Pin P1**, one label (RBM2D `CltPathBound`, with the scale parameters `ρ R θ` in place of
`τ`, `ellT L u`, `6 ≤ W^τ`). -/
def CltPathBound (d L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm d L W 1 K) (E u ρ R θ D' : ℝ) (b : Zd d L) (c : CoordF d L W)
    (ω₀ : Ω d L W) (s : ℝ),
    0 ≤ u → u < 1 → (zt E u).im ≠ 0 → F.Local ρ → 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 →
    zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1 →
    R / 2 ≤ (zdistInf d L ((split d L W c.1).1 - b) : ℝ) → θ ≤ R / 2 - ρ - 1 →
    cltGoodAt d L W E u θ D' ω₀ →
    |s - ω₀ c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) →
    ‖cltYo F E u (Function.update ω₀ c s) b - cltYo F E u ω₀ b‖ ≤
      |s - ω₀ c| * 4 * cltCoefSum F b * (W : ℝ) ^ (-D')

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

/-- The spectral parameter of the `σ`-resolvent in `gEntry`. -/
private def cltpath_zs (E u : ℝ) (σ : Bool) : ℂ :=
  if σ then zt E u else (starRingEnd ℂ) (zt E u)

private theorem cltpath_zs_im {E u : ℝ} (hz : (zt E u).im ≠ 0) (σ : Bool) :
    (cltpath_zs E u σ).im ≠ 0 := by
  cases σ <;> simpa [cltpath_zs] using hz

private theorem cltpath_gEntry (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool)
    (x y : Idx d L W) : gEntry d L W E u M σ x y = green M (cltpath_zs E u σ) x y := by
  simp only [gEntry, Gres, green, cltpath_zs, Matrix.nonsing_inv_eq_ringInverse]

open scoped Matrix.Norms.L2Operator in
/-- Every entry of the `σ`-resolvent of a Hermitian matrix is at most `η⁻¹` when `η ≤ |Im z|`. -/
private theorem cltpath_gEntry_le (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hH : M.IsHermitian) (σ : Bool) (x y : Idx d L W) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(zt E s).im|) : ‖gEntry d L W E s M σ x y‖ ≤ η⁻¹ :=
  (norm_matrix_entry_le_opNorm (Gres M (zt E s) σ) x y).trans
    (norm_Gsig_le_inv_eta hH hη hz σ)

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
private theorem cltpath_deriv (K : ℕ) {k : ℕ} (F : LocalForm d L W k K) (E u ρ R θ D' : ℝ)
    (b : Fin k → Zd d L) (c : CoordF d L W) (ω₀ : Ω d L W) (hu1 : u < 1)
    (hz : (zt E u).im ≠ 0) (hloc : F.Local ρ) (hθ : 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1)
    (hadj : zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1)
    (hfar : ∀ m, R / 2 ≤ (zdistInf d L ((split d L W c.1).1 - b m) : ℝ)) (hθR : θ ≤ R / 2 - ρ - 1)
    (hgood : cltGoodAt d L W E u θ D' ω₀)
    (t : ℝ) (ht : |t| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) :
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => F.eval E u (Hflow d L W u ω₀ +
        (s : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix d L W c)) b) D t ∧
      ‖D‖ ≤ 4 * (W : ℝ) ^ (-D') * cltCoefSumMulti F b := by
  set A : Matrix (Idx d L W) (Idx d L W) ℂ := (Real.sqrt u : ℂ) • coordinateMatrix d L W c with hA
  set M₀ : Matrix (Idx d L W) (Idx d L W) ℂ := Hflow d L W u ω₀ with hM₀
  set γ : ℝ := (W : ℝ) ^ (-D') with hγdef
  have hγ0 : 0 ≤ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hherm : M₀.IsHermitian := Hflow_isHermitian d L W u ω₀
  have hdir : cltCoordDir A c.1 c.2.1 := cltpath_coordDir hu1.le c
  have h8 : 8 * |t| ≤ 1 := by linarith
  have hzσ : ∀ σ, (cltpath_zs E u σ).im ≠ 0 := cltpath_zs_im hz
  have hG0 : ∀ σ x y, ‖green M₀ (cltpath_zs E u σ) x y‖ ≤ 2 := fun σ x y => by
    rw [← cltpath_gEntry]; exact hgood.1 σ x y
  have hGt : ∀ σ x y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) x y‖ ≤ 4 := fun σ x y => by
    have h := cltPert_max_le (Idx d L W) M₀ A c.1 c.2.1 (cltpath_zs E u σ) t 2 hherm hdir (hzσ σ)
      (hG0 σ) (by linarith) x y
    linarith
  have hnear : ∀ (j : Fin (K + 1)) (q : Fin j → Idx d L W × Idx d L W × Bool),
      F.coef b j q ≠ 0 → ∀ (i : Fin j) (σ : Bool),
        ‖gEntry d L W E u (M₀ + (t : ℂ) • A) σ (q i).1 c.1‖ ≤ 2 * γ ∧
          ‖gEntry d L W E u (M₀ + (t : ℂ) • A) σ (q i).1 c.2.1‖ ≤ 2 * γ := by
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
    have hmax : max ‖green M₀ (cltpath_zs E u σ) (q i).1 c.1‖
        ‖green M₀ (cltpath_zs E u σ) (q i).1 c.2.1‖ ≤ γ := max_le ha hb
    have hsub := (cltPert_sub_le (Idx d L W) M₀ A c.1 c.2.1 (cltpath_zs E u σ) t 4 hherm hdir
      (hzσ σ) (hGt σ) (q i).1)
    have key : ∀ y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y -
        green M₀ (cltpath_zs E u σ) (q i).1 y‖ ≤ γ ∧ ‖green M₀ (cltpath_zs E u σ) (q i).1 y‖ ≤ γ →
        ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y‖ ≤ 2 * γ := fun y hy => by
      have := norm_sub_norm_le (green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y)
        (green M₀ (cltpath_zs E u σ) (q i).1 y)
      linarith [hy.1, hy.2]
    have hstep : ∀ y, ‖green (M₀ + (t : ℂ) • A) (cltpath_zs E u σ) (q i).1 y -
        green M₀ (cltpath_zs E u σ) (q i).1 y‖ ≤ γ := fun y => by
      calc _ ≤ 2 * |t| * 4 * max ‖green M₀ (cltpath_zs E u σ) (q i).1 c.1‖
              ‖green M₀ (cltpath_zs E u σ) (q i).1 c.2.1‖ := (hsub y).1
        _ ≤ 2 * |t| * 4 * γ := by gcongr
        _ ≤ γ := by nlinarith [mul_le_mul_of_nonneg_right h8 hγ0]
    refine ⟨?_, ?_⟩
    · rw [cltpath_gEntry]; exact key _ ⟨hstep _, ha⟩
    · rw [cltpath_gEntry]; exact key _ ⟨hstep _, hb⟩
  obtain ⟨D, hD, hDb⟩ := cltDeriv_evalMulti_le d L W k K F E u M₀ A c.1 c.2.1 t 4 (2 * γ) b hherm
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

/-- **P1**, `k` labels (`CltPathBoundMulti`): the mean-value inequality along the segment that
moves the coordinate `c` from `ω₀ c` to `s`. -/
theorem cltPathMulti_bound (k : ℕ) : CltPathBoundMulti d L W k := by
  intro K F E u ρ R θ D' b c ω₀ s hu0 hu1 hz hloc hθ hadj hfar hθR hgood hs
  set h : ℝ → ℂ := fun t => F.eval E u (Hflow d L W u ω₀ +
    (t : ℂ) • ((Real.sqrt u : ℂ) • coordinateMatrix d L W c)) b with hh
  have hpath : ∀ x : ℝ, cltEvalAt F E u (Function.update ω₀ c x) b = h (x - ω₀ c) := by
    intro x
    rw [cltEvalAt, cltpath_Hflow_update]
  have h0 : cltEvalAt F E u ω₀ b = h 0 := by
    have := hpath (ω₀ c)
    rwa [Function.update_eq_self, sub_self] at this
  have hmvt := cltpath_mvt h (2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) (4 * (W : ℝ) ^ (-D') * cltCoefSumMulti F b)
    (s - ω₀ c)
    (fun t ht => cltpath_deriv K F E u ρ R θ D' b c ω₀ hu1 hz hloc hθ hadj hfar hθR hgood t ht) hs
  rw [hpath s, h0]
  calc _ ≤ _ := hmvt
    _ = _ := by ring

/-- **P1**, one label (`CltPathBound`): the case `k = 1` of `cltPathMulti_bound`. -/
theorem cltPath_bound : CltPathBound d L W :=
  fun K F E u ρ R θ D' b c ω₀ s hu0 hu1 hz hloc hθ hadj hfar hθR hgood hs =>
    cltPathMulti_bound d L W 1 K F E u ρ R θ D' (fun _ => b) c ω₀ s hu0 hu1 hz hloc hθ hadj
      (fun _ => hfar) hθR hgood hs

end Bound


/-! ## 4. Compiled instance: `cltPath_bound` at `Step5Inst.szCL`, `n = 0`, `d = 3`

`szCL` (`Step5Pins.lean:640`): `L_0 = 2 · 24^5 = 15925248`, `W_0 = 2^24`, `ilambda = 1`,
`ℓ_s = 1` (`szCL_ellT_s`).  Data: `E = 0`, `u = 1/2` (`z_u = i/2`), `ω₀ = 0` (so `G(σ)` is the
diagonal matrix `-z⁻¹ 1`, every entry `≤ 2`, the off-diagonal ones `= 0`); `w = (log W)^3 ℓ_s`,
`ρ = w`, `R = 10 w`, `θ = R/2 - ρ - 1 = 4 w - 1 > 0`; the form is one monomial `G_{x₀ x₀}` with
`x₀ = 0` (locality sum `0 < ρ`) on `k` labels all equal to `0`; the coordinate is
`c = (x₁, x₁, +)`, `x₁ = (70000 W, 0, 0)` (block distance `70000 ≥ R/2` from the label); the
step is `s = W^{-1/2} > 0`.  No hypothesis is left open. -/

section Checks

open RBM.Gauss.Step5Inst


private theorem cltpath_blk_zero {d L W : ℕ} [NeZero L] [NeZero W] :
    (split d L W (0 : Idx d L W)).1 = 0 := by
  funext i
  simp [split, blk]

private theorem cltpath_zdistInf_zero {d L : ℕ} : zdistInf d L 0 = 0 := by
  simp [zdistInf]

private theorem cltpath_Hflow_zero (d L W : ℕ) [NeZero L] [NeZero W] (u : ℝ) :
    Hflow d L W u (0 : Ω d L W) = 0 := by
  ext i j
  simp [Hflow, Xmat, Xentry]

/-- The `σ`-resolvent of the zero matrix is diagonal. -/
private theorem cltpath_gEntry_zero {d L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (hz : (zt E u).im ≠ 0) (σ : Bool) {x y : Idx d L W} (hxy : x ≠ y) :
    gEntry d L W E u 0 σ x y = 0 := by
  have hz' : (if σ then zt E u else (starRingEnd ℂ) (zt E u)) ≠ 0 := by
    intro h
    cases σ <;> simp at h <;> simp [h] at hz
  have h1 : (0 : Matrix (Idx d L W) (Idx d L W) ℂ) - (if σ then zt E u else (starRingEnd ℂ) (zt E u)) •
      (1 : Matrix (Idx d L W) (Idx d L W) ℂ) =
      (-(if σ then zt E u else (starRingEnd ℂ) (zt E u))) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
    rw [zero_sub, neg_smul]
  have h2 : ((-(if σ then zt E u else (starRingEnd ℂ) (zt E u))) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹
      = (-(if σ then zt E u else (starRingEnd ℂ) (zt E u)))⁻¹ • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ (neg_ne_zero.2 hz'),
      one_smul]
  unfold gEntry Gres
  rw [← Matrix.nonsing_inv_eq_ringInverse, h1, h2]
  simp [Matrix.one_apply_ne hxy]


private theorem cltpath_chk_z_ne : (zt 0 (1 / 2)).im ≠ 0 := by
  rw [zt_im, mE_im, show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The one-monomial form `G_{x₀ x₀}` (`K = 1`) with `k` labels, supported on the label `b₂`. -/
private def cltpath_chkForm {d L W : ℕ} (k : ℕ) (b₂ : Fin k → Zd d L) (x₀ : Idx d L W) :
    LocalForm d L W k 1 where
  coef := fun b' j q =>
    if h : (j : ℕ) = 1 then
      (if b' = b₂ ∧ q ⟨0, by omega⟩ = (x₀, x₀, true) then 1 else 0) else 0

private theorem cltpath_chk_local {d L W : ℕ} [NeZero L] [NeZero W] (k : ℕ) (m₀ : Fin k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (cltpath_chkForm k (fun _ => (0 : Zd d L)) (0 : Idx d L W)).Local ρ := by
  intro b j q hq i
  have hj : (j : ℕ) = 1 := by
    by_contra h
    apply hq
    simp [cltpath_chkForm, h]
  have hq0 : q ⟨0, by omega⟩ = (0, 0, true) := by
    by_contra h
    apply hq
    simp [cltpath_chkForm, hj, h]
  have hb : b = fun _ => (0 : Zd d L) := by
    by_contra h
    apply hq
    simp [cltpath_chkForm, hj, h]
  have hi : i = ⟨0, by omega⟩ := Fin.ext (by have := i.2; omega)
  subst hi
  subst hb
  refine ⟨m₀, ?_⟩
  rw [hq0]
  have h0 : zdistInf d L (0 : Zd d L) = 0 := cltpath_zdistInf_zero
  simp only [cltpath_blk_zero, sub_zero, h0, Nat.cast_zero, add_zero]
  exact hρ

private theorem cltpath_chk_sum {d L W : ℕ} [NeZero L] [NeZero W] (k : ℕ) (b₂ : Fin k → Zd d L)
    (x₀ : Idx d L W) : 4 ≤ cltCoefSumMulti (cltpath_chkForm k b₂ x₀) b₂ := by
  unfold cltCoefSumMulti
  have hnn : ∀ j : Fin (1 + 1), 0 ≤ ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
      ‖(cltpath_chkForm k b₂ x₀).coef b₂ j q‖ * (j : ℝ) * 4 ^ (j : ℕ) := fun j =>
    Finset.sum_nonneg fun q _ => by positivity
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ (1 : Fin (1 + 1))))
  refine le_trans ?_ (Finset.single_le_sum (f := fun q : Fin ((1 : Fin (1 + 1)) : ℕ) → Idx d L W × Idx d L W × Bool =>
      ‖(cltpath_chkForm k b₂ x₀).coef b₂ 1 q‖ * (((1 : Fin (1 + 1)) : ℕ) : ℝ) * 4 ^ (((1 : Fin (1 + 1)) : ℕ)))
    (fun q _ => by positivity) (Finset.mem_univ (fun _ => (x₀, x₀, true))))
  simp [cltpath_chkForm]


/-! ### The data at `szCL`, `n = 0` -/

private theorem cltpath_chk_L : szCL.L 0 = 15925248 := rfl
private theorem cltpath_chk_W : szCL.W 0 = 16777216 := rfl

/-- `w = (log W)^3 ℓ_s` at `szCL`, `n = 0` (`ℓ_s = 1`, `szCL_ellT_s`). -/
private noncomputable def cpw : ℝ :=
  Real.log ((szCL.W 0 : ℕ) : ℝ) ^ 3 * ellT (szCL.L 0) (szCL.lam 0) (sCL 0)

private theorem cpw_eq : cpw = Real.log ((szCL.W 0 : ℕ) : ℝ) ^ 3 := by
  rw [cpw, szCL_ellT_s, mul_one]

private theorem cpw_ge : 1 ≤ cpw := by
  rw [cpw_eq]; exact one_le_pow₀ (szCL_one_le_log_W 0)

private theorem cpw_le : cpw ≤ 24 ^ 3 := by
  rw [cpw_eq]
  have h := szCL_log_W_le 0
  have h0 := szCL_one_le_log_W 0
  push_cast at h
  exact pow_le_pow_left₀ (by linarith) (by linarith) 3

/-- The step `s = W^{-1/2}`. -/
private noncomputable def cpS : ℝ := ((szCL.W 0 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

private theorem cpS_pos : 0 < cpS := Real.rpow_pos_of_pos (by exact_mod_cast (szCL.W_pos 0)) _

private theorem cltpath_chk_step : 16 * (((szCL.W 0 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  have h : (((szCL.W 0 : ℕ) : ℝ)) = 4096 ^ 2 := by rw [cltpath_chk_W]; norm_num
  rw [h, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The point `x₁ = (70000 W, 0, 0)` of `Z_{WL}^3`: block `(70000, 0, 0)`. -/
private def cpx : Idx 3 (szCL.L 0) (szCL.W 0) :=
  fun i => if i = 0 then (((70000 * szCL.W 0 : ℕ)) : ZMod (szCL.W 0 * szCL.L 0)) else 0

private theorem cpx_far : (70000 : ℝ) ≤
    (zdistInf 3 (szCL.L 0) ((split 3 (szCL.L 0) (szCL.W 0) cpx).1 - 0) : ℝ) := by
  have hWL : 70000 * szCL.W 0 < szCL.W 0 * szCL.L 0 := by
    rw [cltpath_chk_L, cltpath_chk_W]; norm_num
  have h1 : (split 3 (szCL.L 0) (szCL.W 0) cpx).1 0 = ((70000 : ℕ) : ZMod (szCL.L 0)) := by
    simp only [split, blk, cpx, ite_true]
    rw [ZMod.val_natCast_of_lt hWL, Nat.mul_div_cancel _ (szCL.W_pos 0)]
  have h2 : zdist (szCL.L 0) (((70000 : ℕ) : ZMod (szCL.L 0))) = 70000 := by
    have hlt : 70000 < szCL.L 0 := by rw [cltpath_chk_L]; norm_num
    unfold zdist
    rw [ZMod.val_natCast_of_lt hlt]
    rw [cltpath_chk_L]; norm_num
  have h3 : zdist (szCL.L 0) ((split 3 (szCL.L 0) (szCL.W 0) cpx).1 0) ≤
      zdistInf 3 (szCL.L 0) ((split 3 (szCL.L 0) (szCL.W 0) cpx).1 - 0) := by
    rw [sub_zero]
    exact Finset.le_sup (f := fun i => zdist (szCL.L 0)
      ((split 3 (szCL.L 0) (szCL.W 0) cpx).1 i)) (Finset.mem_univ (0 : Fin 3))
  rw [h1, h2] at h3
  exact_mod_cast h3


/-- The good set at `ω₀ = 0`: all entries `≤ 2`, and the far (hence off-diagonal) ones vanish. -/
private theorem cltpath_chk_good (θ D' : ℝ) (hθ : 0 < θ) :
    cltGoodAt 3 (szCL.L 0) (szCL.W 0) 0 (1 / 2) θ D' 0 := by
  refine ⟨fun σ x y => ?_, fun σ x y hxy => ?_⟩
  · have h := cltpath_gEntry_le (d := 3) (L := szCL.L 0) (W := szCL.W 0) 0 (1 / 2)
      (Hflow 3 (szCL.L 0) (szCL.W 0) (1 / 2) 0) (Hflow_isHermitian _ _ _ _ _) σ x y (η := 1 / 2)
      (by norm_num)
      (by rw [zt_im, mE_im, show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
        abs_of_pos (by norm_num)]; norm_num)
    rwa [show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num] at h
  · have hne : x ≠ y := by
      intro h
      subst h
      rw [sub_self, cltpath_zdistInf_zero] at hxy
      norm_num at hxy
      linarith
    rw [cltpath_Hflow_zero, cltpath_gEntry_zero 0 (1 / 2) cltpath_chk_z_ne σ hne, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The coordinate `c = (x₁, x₁, +)`. -/
private def cpc : CoordF 3 (szCL.L 0) (szCL.W 0) := (cpx, cpx, true)

/-- **Instance of `cltPath_bound`** at `szCL`, `n = 0`, `d = 3`: `E = 0`, `u = 1/2`, `ω₀ = 0`,
`ρ = w`, `R = 10 w`, `θ = R/2 - ρ - 1`, `D' = 1`, one label `b = 0`, the step `s = W^{-1/2}`. -/
private theorem cltpath_chk_szCL :
    ‖cltYo (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L 0))) (0 : Idx 3 (szCL.L 0) (szCL.W 0)))
        0 (1 / 2) (Function.update 0 cpc cpS) 0 -
      cltYo (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L 0))) (0 : Idx 3 (szCL.L 0) (szCL.W 0)))
        0 (1 / 2) 0 0‖ ≤
    |cpS - (0 : Ω 3 (szCL.L 0) (szCL.W 0)) cpc| * 4 *
      cltCoefSum (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L 0)))
        (0 : Idx 3 (szCL.L 0) (szCL.W 0))) 0 * (((szCL.W 0 : ℕ) : ℝ)) ^ (-(1 : ℝ)) :=
  cltPath_bound 3 (szCL.L 0) (szCL.W 0) 1
    (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L 0))) (0 : Idx 3 (szCL.L 0) (szCL.W 0)))
    0 (1 / 2) cpw (10 * cpw) (10 * cpw / 2 - cpw - 1) 1 0 cpc 0 cpS (by norm_num) (by norm_num)
    cltpath_chk_z_ne (cltpath_chk_local 1 0 (by linarith [cpw_ge])) cltpath_chk_step
    (by simp only [cpc, sub_self, cltpath_zdistInf_zero]; norm_num)
    (le_trans (by have := cpw_le; norm_num at this ⊢; linarith) cpx_far)
    le_rfl (cltpath_chk_good _ _ (by linarith [cpw_ge]))
    (by
      rw [Pi.zero_apply, sub_zero, abs_of_pos cpS_pos]
      have := cpS_pos
      unfold cpS at *
      linarith)


/-- **Instance of `cltPathMulti_bound`** at the same data with two labels `b = (0, 0)` (the shape
of `STcltB`: `b : Fin 2 → Zd 3 L`). -/
private theorem cltpath_chk_szCL_multi :
    ‖cltEvalAt (cltpath_chkForm 2 (fun _ => (0 : Zd 3 (szCL.L 0)))
        (0 : Idx 3 (szCL.L 0) (szCL.W 0))) 0 (1 / 2) (Function.update 0 cpc cpS) (fun _ => 0) -
      cltEvalAt (cltpath_chkForm 2 (fun _ => (0 : Zd 3 (szCL.L 0)))
        (0 : Idx 3 (szCL.L 0) (szCL.W 0))) 0 (1 / 2) 0 (fun _ => 0)‖ ≤
    |cpS - (0 : Ω 3 (szCL.L 0) (szCL.W 0)) cpc| * 4 *
      cltCoefSumMulti (cltpath_chkForm 2 (fun _ => (0 : Zd 3 (szCL.L 0)))
        (0 : Idx 3 (szCL.L 0) (szCL.W 0))) (fun _ => 0) * (((szCL.W 0 : ℕ) : ℝ)) ^ (-(1 : ℝ)) :=
  cltPathMulti_bound 3 (szCL.L 0) (szCL.W 0) 2 1
    (cltpath_chkForm 2 (fun _ => (0 : Zd 3 (szCL.L 0))) (0 : Idx 3 (szCL.L 0) (szCL.W 0)))
    0 (1 / 2) cpw (10 * cpw) (10 * cpw / 2 - cpw - 1) 1 (fun _ => 0) cpc 0 cpS (by norm_num)
    (by norm_num) cltpath_chk_z_ne (cltpath_chk_local 2 0 (by linarith [cpw_ge]))
    cltpath_chk_step (by simp only [cpc, sub_self, cltpath_zdistInf_zero]; norm_num)
    (fun _ => le_trans (by have := cpw_le; norm_num at this ⊢; linarith) cpx_far) le_rfl
    (cltpath_chk_good _ _ (by linarith [cpw_ge]))
    (by
      rw [Pi.zero_apply, sub_zero, abs_of_pos cpS_pos]
      have := cpS_pos
      unfold cpS at *
      linarith)

/-- Nondegeneracy of the instance: the step is positive, the coefficient weight is `≥ 4`, and the
far threshold `θ = R/2 - ρ - 1 = 4 w - 1` of `cltFarGeomNear` is at least `c w` for `c ∈ {1, 3}`
(`w = (log W)^3 ℓ_s`, the threshold `c (log W)^3 ℓ_s` of `STFarEntryAtLog`). -/
private theorem cltpath_chk_nondeg :
    0 < cpS ∧
      4 ≤ cltCoefSum (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L 0)))
        (0 : Idx 3 (szCL.L 0) (szCL.W 0))) 0 ∧
      1 * cpw ≤ 10 * cpw / 2 - cpw - 1 ∧ 3 * cpw ≤ 10 * cpw / 2 - cpw - 1 :=
  ⟨cpS_pos, cltpath_chk_sum 1 _ _, by linarith [cpw_ge], by linarith [cpw_ge]⟩

end Checks

/-! ## Axioms of the declarations of this file -/

#print axioms cltPathMulti_bound
#print axioms cltPath_bound
#print axioms cltpath_chk_szCL
#print axioms cltpath_chk_szCL_multi
#print axioms cltpath_chk_nondeg

end RBM.Evol
