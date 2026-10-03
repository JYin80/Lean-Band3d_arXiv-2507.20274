/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.GLoopFlow
import RBM3D.Loop.TreeRep
import RBM3D.Gauss.FlowCalculus
import RBM3D.Gauss.FineModel
import RBM3D.Gauss.DominationAt
import RBM3D.Green.EntryCore
import RBM3D.Analysis.Resolvent
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The one-step expansion with its envelope, and the Lipschitz bound of the loop drift (ST2-20)

Ticket T2072 (ST2-20).  Port of `RBM2D/Path/OneStep.lean` (1692 lines) and
`RBM2D/Path/DriftLip.lean` (693 lines) at commit `c9a24cf` (cited `OneStep:<line>`,
`DriftLip:<line>`), onto the merged MD layer (`FineModel`, `GLoopFlow`, `TreeRep`) and the ST-1 flow
calculus (`FlowCalculus`).  Renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`; in addition
(merged vocabulary): `Z2 L` is `Zd d L`,
`BlockIndex L W` is `Vtx d L W`, `Gsig` is `Gres`, the list-based `gloop L W H z I` is
`loopL d L W H z I`, `spectralZ` is `zt`, `KLoop.mSig` is `mSigma`, `KLoop.primRhs` is
`treeEqRhs d L W g`, `Coord/Ω/P/gvar/svar` are `CoordF/Ω/PF d L W g/gvarF/svarF`.

## Main results

* `RBM.Path.genMat` : the generator of one Gaussian increment of the loop functional.
* `RBM.Path.envConst` : the explicit envelope constant `16 (k+3)^4 N^4 (1 + η_v^{-1})^{k+4}`,
  `N = (W L)^d`.
* `RBM.Path.OneStepEnvelope`, `RBM.Path.oneStepEnvelope` : the one-step expansion with its
  `Δ^{3/2}` envelope, for every real parameter `g`.
* `RBM.Path.norm_green_sub_le_of_herm`, `RBM.Path.loopDrift`, `RBM.Path.driftLip`,
  `RBM.Path.norm_loopDrift_sub_le` : the deterministic Lipschitz bound of the loop drift.

## Route

One step of Gaussian increment is split as `T₂ + T₁` with `τ = √Δ`: the space step at fixed time
by Stein's identity (coordinatewise) and the fencing lemma, and the time step at fixed sample by a
second-order Taylor expansion (`OneStepEnvelope`: `OneStep:1512`); the derivatives of the loop
functional are the jets of a word of resolvent factors, bounded by induction on the word.  The
counts use `N = (W L)^d`, `‖E_a‖ ≤ W^{-d} ≤ 1` and the row sums of `S^(B)(g)`, which are at most `1`
for every `L ≥ 1` (`OneStep_sum_sbKernelR_le`: the unit sphere of `Z_L^d` has at most `2d` points
for every `L`; for `3 ≤ L` it has exactly `2d`, `RBM3D/Defs/Neighbours.lean`).

Every helper is `private` or carries the prefix `OneStep_` / `DriftLip_`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Finset RBM RBM.Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator

namespace RBM.Path

-- the copied pins keep the probe's line breaks
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- The generator of one Gaussian increment for the loop functional `Φ_u(M) = 𝓛_{u,I}(M)`:
`½ Σ_c gvar(c) ∂²_c Φ_u(M) + ∂_u Φ_u(M)`, with one-variable derivatives along the coordinate
matrices `coordinateMatrix d L W c` and along the spectral path `zt E u`.
`RBM2D/Path/OneStep.lean:69` (`genMat`); the parameters `d` and `g` are new (rules R2, R4). -/
def genMat (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) (zt E u) I)) 0 +
    deriv (fun v : ℝ => loopL d L W (blockMat d L W M) (zt E v) I) u

/-- The explicit envelope constant of the one-step expansion:
`16 (k+3)^4 N^4 (1 + η_v^{-1})^{k+4}` for a loop of length `k`, `N = (W L)^d`, `v` the later time.
`RBM2D/Path/OneStep.lean:78` (`envConst`), rule R3. -/
def envConst (d L W : ℕ) (E : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  16 * ((k : ℝ) + 3) ^ 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 4 * (1 + (etaT E v)⁻¹) ^ (k + 4)

/-- **One-step expansion with envelope**: for Hermitian `M`, `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1` and a
well-formed loop of length `k`, `‖E Φ_{u+Δ}(M + √Δ X) - Φ_u(M) - Δ · gen_u(M)‖ ≤
envConst · Δ^{3/2}`, for every `d`, `L`, `W ≥ 1` and every real parameter `g` of `S^(B)(g)`.
`RBM2D/Path/OneStep.lean:86` (`OneStepEnvelope`), rules R1-R4. -/
def OneStepEnvelope : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : Loop.LoopIdx (Zd d L)),
    I.WF → ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
        ‖(∫ ω', loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω'))
              (zt E (u + Δ)) I ∂(PF d L W g)) -
            loopL d L W (blockMat d L W M) (zt E u) I - (Δ : ℂ) * genMat d L W g E u M I‖ ≤
          envConst d L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2)

/-! ### The resolvent difference at a fixed spectral parameter (`DriftLip:42`) -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem OneStep_green_eq (H : Matrix n n ℂ) (z : ℂ) : green H z = Gres H z true := by
  simp [green, Gres, Matrix.nonsing_inv_eq_ringInverse]

/-- `‖G(z)‖ ≤ |Im z|⁻¹` for Hermitian `H` (`RBM2D/Gauss/Envelope.lean:116`, `norm_green_le`). -/
private theorem OneStep_norm_green_le {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : ‖green H z‖ ≤ |z.im|⁻¹ := by
  rw [OneStep_green_eq]
  exact norm_Gsig_le_inv_eta hH (abs_pos.mpr hz) le_rfl true

/-- **The resolvent-difference bound.**  For Hermitian `M₁, M₂` and `z.im ≠ 0`,
`‖G(M₁, z) - G(M₂, z)‖ ≤ |z.im|⁻¹² ‖M₁ - M₂‖`.  `DriftLip:50`. -/
theorem norm_green_sub_le_of_herm {M₁ M₂ : Matrix n n ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖green M₁ z - green M₂ z‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by
  have hzpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  have hg1 : ‖green M₁ z‖ ≤ |z.im|⁻¹ := OneStep_norm_green_le hM₁ hz
  have hg2 : ‖green M₂ z‖ ≤ |z.im|⁻¹ := OneStep_norm_green_le hM₂ hz
  have hu1 := isUnit_sub_smul_of_isHermitian hM₁ hz
  have hu2 := isUnit_sub_smul_of_isHermitian hM₂ hz
  have hd1 : IsUnit (M₁ - z • (1 : Matrix n n ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu1
  have hd2 : IsUnit (M₂ - z • (1 : Matrix n n ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu2
  have hid : green M₁ z - green M₂ z = green M₁ z * (M₂ - M₁) * green M₂ z := by
    have hsub : M₂ - M₁ = (M₂ - z • (1 : Matrix n n ℂ)) - (M₁ - z • (1 : Matrix n n ℂ)) := by
      abel
    have h1 : green M₁ z * (M₂ - z • (1 : Matrix n n ℂ)) * green M₂ z = green M₁ z := by
      rw [green, green, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd2, Matrix.mul_one]
    have h2 : green M₁ z * (M₁ - z • (1 : Matrix n n ℂ)) * green M₂ z = green M₂ z := by
      rw [green, green, Matrix.nonsing_inv_mul _ hd1, Matrix.one_mul]
    rw [hsub, Matrix.mul_sub, Matrix.sub_mul, h1, h2]
  rw [hid]
  calc ‖green M₁ z * (M₂ - M₁) * green M₂ z‖
      ≤ ‖green M₁ z‖ * ‖M₂ - M₁‖ * ‖green M₂ z‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ |z.im|⁻¹ * ‖M₁ - M₂‖ * |z.im|⁻¹ := by
        rw [norm_sub_rev M₂ M₁]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)) hg2 (norm_nonneg _)
          (by positivity)
    _ = |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by ring

/-- Both spectral signs satisfy the same resolvent-difference bound (`DriftLip:80`,
`OneStep:540`). -/
private theorem OneStep_norm_Gsig_sub_le {M₁ M₂ : Matrix n n ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    ‖Gres M₁ z σ - Gres M₂ z σ‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by
  cases σ
  · have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
    have := norm_green_sub_le_of_herm hM₁ hM₂ hz'
    rw [OneStep_green_eq, OneStep_green_eq] at this
    simpa [Gres] using this
  · have := norm_green_sub_le_of_herm hM₁ hM₂ hz
    rwa [OneStep_green_eq, OneStep_green_eq] at this

end Resolvent

/-! ### Reindexing to block coordinates -/

section Reindex

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Reindexing by an equivalence is a star algebra homomorphism of matrix algebras. -/
private def DriftLip_reindexHom {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (e : k ≃ m) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix k k ℂ where
  toFun A := A.submatrix e e
  map_smul' c A := rfl
  map_zero' := rfl
  map_add' A B := rfl
  map_mul' A B := by
    exact (Matrix.submatrix_mul_equiv A B e e e).symm
  map_star' A := by
    exact (Matrix.conjTranspose_submatrix A e e).symm

/-- `blockMat` does not increase the operator norm (in fact it preserves it). -/
private theorem DriftLip_norm_blockMat (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ‖blockMat d L W A‖ = ‖A‖ := by
  have hinj : Function.Injective (DriftLip_reindexHom (splitEquiv d L W).symm) := by
    intro A B h
    ext i j
    have := congrFun (congrFun h ((splitEquiv d L W) i)) ((splitEquiv d L W) j)
    change A ((splitEquiv d L W).symm ((splitEquiv d L W) i))
      ((splitEquiv d L W).symm ((splitEquiv d L W) j)) =
        B ((splitEquiv d L W).symm ((splitEquiv d L W) i))
          ((splitEquiv d L W).symm ((splitEquiv d L W) j)) at this
    simpa using this
  exact NonUnitalStarAlgHom.norm_map _ hinj A

/-- `blockMat` of a Hermitian matrix is Hermitian. -/
private theorem DriftLip_isHermitian_blockMat {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) : (blockMat d L W A).IsHermitian :=
  hA.submatrix _

private theorem DriftLip_blockMat_sub (A B : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockMat d L W A - blockMat d L W B = blockMat d L W (A - B) := by
  rfl

end Reindex

/-! ### Label sums against `S^{(B)}`

The absolute row sums of `S^(B)(g)` are at most `1` for **every** `L ≥ 1` and every real `g`
(RBM2D: five points of mass `1/5`, `DriftLip:142`, `OneStep:839`): the kernel is
`a = (1 + 2 d g²)⁻¹` at `0` and `b = g² a` on the unit sphere, which has at most `2d` points for
every `L` (exactly `2d` for `3 ≤ L`, `RBM3D/Defs/Neighbours.lean`; the merged `sum_norm_SB_row`
needs `3 ≤ L`). -/

section LabelSums

variable {d L : ℕ} [NeZero L]

/-- On the cycle `ZMod L`, for every `L ≥ 1`, a point at distance `1` from the origin is `±1`
(the merged `zdist_eq_one_iff` needs `3 ≤ L`). -/
private theorem OneStep_zdist_eq_one {u : ZMod L} (h : zdist L u = 1) : u = 1 ∨ u = -1 := by
  have hu : u.val < L := ZMod.val_lt u
  simp only [zdist] at h
  rcases (show u.val = 1 ∨ L - u.val = 1 by omega) with h' | h'
  · left
    rw [← ZMod.natCast_zmod_val u, h', Nat.cast_one]
  · right
    have hv : u.val = L - 1 := by omega
    rw [← ZMod.natCast_zmod_val u, hv, Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]
    simp

/-- A point at distance `1` from the origin of `Z_L^d` is a unit vector `±eᵢ`, for every `L ≥ 1`
(proof of `exists_unitVec_of_zdistD_eq_one`, `RBM3D/Defs/Neighbours.lean`, with
`OneStep_zdist_eq_one`). -/
private theorem OneStep_exists_unitVec {x : Zd d L} (hx : zdistD d L x = 1) :
    ∃ p, unitVec d L p = x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : x = 0 := funext h
    rw [this, zdistD_zero] at hx
    exact absurd hx (by decide)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => zdist L (x j)) (Finset.mem_univ i)
  simp only [zdistD] at hx
  rw [hx] at hsplit
  have hpos : 0 < zdist L (x i) :=
    Nat.pos_of_ne_zero fun h => hi ((zdist_eq_zero_iff L).mp h)
  have hi1 : zdist L (x i) = 1 := by omega
  have hrest : ∑ j ∈ Finset.univ.erase i, zdist L (x j) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  have hx' : x = Pi.single i (x i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Pi.single_eq_of_ne hj]
      exact (zdist_eq_zero_iff L).mp (hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  rcases OneStep_zdist_eq_one hi1 with h | h
  · exact ⟨(i, true), by rw [hx', unitVec, h]; simp⟩
  · exact ⟨(i, false), by rw [hx', unitVec, h]; simp⟩

/-- The unit sphere of `Z_L^d` has at most `2d` points, for every `L ≥ 1`. -/
private theorem OneStep_card_sphere_le :
    (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1).card ≤ 2 * d := by
  have hsub : (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1) ⊆
      Finset.univ.image (unitVec d L) := by
    intro x hx
    obtain ⟨p, hp⟩ := OneStep_exists_unitVec (Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]

/-- The kernel mass of `S^(B)(g)` is at most `1`, for every `L ≥ 1` and every real `g`. -/
private theorem OneStep_sum_sbKernelR_le (g : ℝ) : ∑ x : Zd d L, sbKernelR d L g x ≤ 1 := by
  have hpos : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  simp only [sbKernelR, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (((Finset.univ.filter fun x : Zd d L => zdistD d L x = 1).card : ℕ) : ℝ) ≤ 2 * d := by
    exact_mod_cast OneStep_card_sphere_le (d := d) (L := L)
  set c : ℝ := (((Finset.univ.filter fun x : Zd d L => zdistD d L x = 1).card : ℕ) : ℝ) with hcdef
  calc (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ + c * (g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹)
      = (1 + c * g ^ 2) / (1 + 2 * (d : ℝ) * g ^ 2) := by field_simp
    _ ≤ 1 := (div_le_one hpos).mpr (by nlinarith [sq_nonneg g])

/-- The absolute row sums of `S^{(B)}(g)` are at most `1` (`DriftLip:142`, `OneStep:839`), for every
`L ≥ 1` and every real `g`. -/
private theorem OneStep_sum_norm_SB_row (g : ℝ) (a : Zd d L) :
    ∑ b : Zd d L, ‖SB d L g a b‖ ≤ 1 := by
  have h : ∀ b : Zd d L, ‖SB d L g a b‖ = sbKernelR d L g (a - b) := by
    intro b
    rw [SB_apply, sbKernel_eq_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (sbKernelR_nonneg d L g _)]
  simp_rw [h]
  exact le_trans (le_of_eq (Fintype.sum_equiv (Equiv.subLeft a)
    (fun b => sbKernelR d L g (a - b)) (fun x => sbKernelR d L g x) (fun b => rfl)))
    (OneStep_sum_sbKernelR_le g)

/-- A double label sum whose terms differ by at most `‖S_{ab}‖ · X` differs by at most `L^d X`
(`DriftLip:162`, `L²` becomes `L^d`). -/
private theorem DriftLip_sum_sub_le (g : ℝ) (f f' : Zd d L → Zd d L → ℂ) {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ a b, ‖f a b - f' a b‖ ≤ ‖SB d L g a b‖ * X) :
    ‖(∑ a, ∑ b, f a b) - ∑ a, ∑ b, f' a b‖ ≤ (L : ℝ) ^ d * X := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc ‖∑ a, ∑ b, (f a b - f' a b)‖ ≤ ∑ a, ‖∑ b, (f a b - f' a b)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Zd d L, X := Finset.sum_le_sum fun a _ => by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ b, ‖f a b - f' a b‖ ≤ ∑ b, ‖SB d L g a b‖ * X := Finset.sum_le_sum fun b _ => h a b
          _ = (∑ b, ‖SB d L g a b‖) * X := (Finset.sum_mul _ _ _).symm
          _ ≤ 1 * X := mul_le_mul_of_nonneg_right (OneStep_sum_norm_SB_row g a) hX
          _ = X := one_mul X
    _ = (L : ℝ) ^ d * X := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Zd]
        push_cast
        ring

end LabelSums

/-- Each block insertion has norm at most `1` (it is `W^{-d} ≤ 1`).  `DriftLip:187`,
`OneStep:642`. -/
private theorem OneStep_norm_Eblk_le_one {d L W : ℕ} [NeZero L] [NeZero W] (a : Zd d L) :
    ‖Eblk d L W a‖ ≤ 1 := by
  refine (norm_Eblk_le_inv_W_sq d L W a).trans ?_
  have hW : (1 : ℝ) ≤ (W : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W))
  exact inv_le_one_of_one_le₀ hW

/-- The operation `cutGlue` adds exactly one Green edge (`RBM2D/Hierarchy/Operations.lean:48`). -/
private theorem OneStep_length_cutGlue {α : Type*} (I : Loop.LoopIdx α) (b : α) {k : ℕ}
    (hk : k ≤ I.length) : (I.cutGlue k b).length = I.length + 1 := by
  simp only [Loop.LoopIdx.length, Loop.LoopIdx.cutGlue, List.length_append, List.length_take,
    List.length_cons, List.length_drop] at hk ⊢
  omega

/-- A valid one-based cut preserves well-formedness (`RBM2D/Hierarchy/Operations.lean:56`). -/
private theorem OneStep_wf_cutGlue {α : Type*} {I : Loop.LoopIdx α} (hI : I.WF) (b : α) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ I.length) : (I.cutGlue k b).WF := by
  simp only [Loop.LoopIdx.WF, Loop.LoopIdx.length, Loop.LoopIdx.cutGlue, List.length_append,
    List.length_take, List.length_cons, List.length_drop] at hI hk ⊢
  omega

/-! ### Envelope and Lipschitz bounds for loops and trace factors -/

section Loops

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The envelope of a signed word of Green functions and block insertions. -/
private theorem DriftLip_word_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hG : ∀ s, ‖Gres H z s‖ ≤ K)
    (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖ ≤ K ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ]
      calc ‖Gres H z p.1 * Eblk d L W p.2 *
            l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1‖
          ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ *
              ‖l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1‖ :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ K * 1 * K ^ l.length :=
            mul_le_mul (mul_le_mul (hG p.1) (OneStep_norm_Eblk_le_one p.2) (norm_nonneg _) hK)
              ih (norm_nonneg _) (by positivity)
        _ = K ^ l.length * K := by ring

/-- The telescoping bound for two signed words: `‖P₁ - P₂‖ ≤ ℓ K^ℓ Δg`. -/
private theorem DriftLip_word_sub_le {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {K Δg : ℝ} (hK : 1 ≤ K) (hΔ : 0 ≤ Δg)
    (hG₁ : ∀ s, ‖Gres H₁ z s‖ ≤ K) (hG₂ : ∀ s, ‖Gres H₂ z s‖ ≤ K)
    (hGd : ∀ s, ‖Gres H₁ z s - Gres H₂ z s‖ ≤ Δg) (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p M => Gres H₁ z p.1 * Eblk d L W p.2 * M)
          (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
      - l.foldr (fun p M => Gres H₂ z p.1 * Eblk d L W p.2 * M) 1‖
      ≤ (l.length : ℝ) * K ^ l.length * Δg := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons]
      set w₁ := l.foldr (fun p M => Gres H₁ z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) with hw₁
      set w₂ := l.foldr (fun p M => Gres H₂ z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) with hw₂
      have hsplit : Gres H₁ z p.1 * Eblk d L W p.2 * w₁ - Gres H₂ z p.1 * Eblk d L W p.2 * w₂
          = (Gres H₁ z p.1 - Gres H₂ z p.1) * Eblk d L W p.2 * w₁
            + Gres H₂ z p.1 * Eblk d L W p.2 * (w₁ - w₂) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub]
        abel
      have hw1 : ‖w₁‖ ≤ K ^ l.length := DriftLip_word_le hK0 hG₁ l
      have hE := OneStep_norm_Eblk_le_one (d := d) (L := L) (W := W) p.2
      have hA : ‖(Gres H₁ z p.1 - Gres H₂ z p.1) * Eblk d L W p.2 * w₁‖ ≤ Δg * K ^ l.length := by
        calc ‖(Gres H₁ z p.1 - Gres H₂ z p.1) * Eblk d L W p.2 * w₁‖
            ≤ ‖Gres H₁ z p.1 - Gres H₂ z p.1‖ * ‖Eblk d L W p.2‖ * ‖w₁‖ :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ Δg * 1 * K ^ l.length :=
              mul_le_mul (mul_le_mul (hGd p.1) hE (norm_nonneg _) hΔ) hw1 (norm_nonneg _)
                (by positivity)
          _ = Δg * K ^ l.length := by ring
      have hB : ‖Gres H₂ z p.1 * Eblk d L W p.2 * (w₁ - w₂)‖
          ≤ K * ((l.length : ℝ) * K ^ l.length * Δg) := by
        calc ‖Gres H₂ z p.1 * Eblk d L W p.2 * (w₁ - w₂)‖
            ≤ ‖Gres H₂ z p.1‖ * ‖Eblk d L W p.2‖ * ‖w₁ - w₂‖ :=
              (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ K * 1 * ((l.length : ℝ) * K ^ l.length * Δg) :=
              mul_le_mul (mul_le_mul (hG₂ p.1) hE (norm_nonneg _) hK0) ih (norm_nonneg _)
                (by positivity)
          _ = K * ((l.length : ℝ) * K ^ l.length * Δg) := by ring
      have hpow : K ^ l.length ≤ K ^ (l.length + 1) := pow_le_pow_right₀ hK (Nat.le_succ _)
      rw [hsplit]
      calc ‖(Gres H₁ z p.1 - Gres H₂ z p.1) * Eblk d L W p.2 * w₁
            + Gres H₂ z p.1 * Eblk d L W p.2 * (w₁ - w₂)‖
          ≤ Δg * K ^ l.length + K * ((l.length : ℝ) * K ^ l.length * Δg) :=
            (norm_add_le _ _).trans (add_le_add hA hB)
        _ ≤ Δg * K ^ (l.length + 1) + K * ((l.length : ℝ) * K ^ l.length * Δg) := by
            have := mul_le_mul_of_nonneg_left hpow hΔ
            linarith
        _ = ((l.length + 1 : ℕ) : ℝ) * K ^ (l.length + 1) * Δg := by
            push_cast
            ring

omit [NeZero W] in
/-- `N = (LW)^d` as a real number. -/
private theorem DriftLip_card_real :
    (Fintype.card (Vtx d L W) : ℝ) = (((L * W) ^ d : ℕ) : ℝ) := by
  rw [card_BlockIndex]

/-- The envelope of a well-formed `G`-loop: `‖𝓛‖ ≤ N K^ℓ`. -/
private theorem DriftLip_norm_gloop_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hG : ∀ s, ‖Gres H z s‖ ≤ K) {J : Loop.LoopIdx (Zd d L)} (hJ : J.WF) :
    ‖loopL d L W H z J‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * K ^ J.length := by
  have htrace := norm_matrix_trace_le_card_mul (gloopProd d L W H z J)
  have hword := DriftLip_word_le hK hG (J.σ.zip J.a)
  have hlen : (J.σ.zip J.a).length = J.length := by
    rw [List.length_zip]
    simp only [Loop.LoopIdx.WF] at hJ
    rw [hJ, min_self]
    rfl
  rw [hlen] at hword
  calc ‖loopL d L W H z J‖ ≤ (Fintype.card (Vtx d L W) : ℝ) * ‖gloopProd d L W H z J‖ := htrace
    _ ≤ (Fintype.card (Vtx d L W) : ℝ) * K ^ J.length :=
        mul_le_mul_of_nonneg_left hword (Nat.cast_nonneg _)
    _ = (((L * W) ^ d : ℕ) : ℝ) * K ^ J.length := by rw [DriftLip_card_real]

/-- The Lipschitz bound of a well-formed `G`-loop: `‖𝓛₁ - 𝓛₂‖ ≤ N ℓ K^ℓ Δg`. -/
private theorem DriftLip_norm_gloop_sub_le
    {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} {K Δg : ℝ}
    (hK : 1 ≤ K) (hΔ : 0 ≤ Δg)
    (hG₁ : ∀ s, ‖Gres H₁ z s‖ ≤ K) (hG₂ : ∀ s, ‖Gres H₂ z s‖ ≤ K)
    (hGd : ∀ s, ‖Gres H₁ z s - Gres H₂ z s‖ ≤ Δg) {J : Loop.LoopIdx (Zd d L)} (hJ : J.WF) :
    ‖loopL d L W H₁ z J - loopL d L W H₂ z J‖
      ≤ (((L * W) ^ d : ℕ) : ℝ) * ((J.length : ℝ) * K ^ J.length * Δg) := by
  have hlen : (J.σ.zip J.a).length = J.length := by
    rw [List.length_zip]
    simp only [Loop.LoopIdx.WF] at hJ
    rw [hJ, min_self]
    rfl
  have hword := DriftLip_word_sub_le hK hΔ hG₁ hG₂ hGd (J.σ.zip J.a)
  rw [hlen] at hword
  have htrace := norm_matrix_trace_le_card_mul (gloopProd d L W H₁ z J - gloopProd d L W H₂ z J)
  rw [Matrix.trace_sub] at htrace
  calc ‖loopL d L W H₁ z J - loopL d L W H₂ z J‖
      ≤ (Fintype.card (Vtx d L W) : ℝ) * ‖gloopProd d L W H₁ z J - gloopProd d L W H₂ z J‖ :=
        htrace
    _ ≤ (Fintype.card (Vtx d L W) : ℝ) * ((J.length : ℝ) * K ^ J.length * Δg) :=
        mul_le_mul_of_nonneg_left hword (Nat.cast_nonneg _)
    _ = (((L * W) ^ d : ℕ) : ℝ) * ((J.length : ℝ) * K ^ J.length * Δg) := by
        rw [DriftLip_card_real]

/-- The envelope of the trace factor `⟨(G(σ) - m(σ)) E_a⟩` of the `Ẽ` term. -/
private theorem DriftLip_norm_trace_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    {K μ : ℝ} (m : Bool → ℂ) (hG : ∀ s, ‖Gres H z s‖ ≤ K) (hm : ∀ s, ‖m s‖ ≤ μ)
    (σ : Bool) (a : Zd d L) :
    ‖Matrix.trace ((Gres H z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
        * Eblk d L W a)‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * (K + μ) := by
  have hX : ‖Gres H z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖ ≤ K + μ := by
    have hstep := norm_sub_le (Gres H z σ) (m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
    rw [norm_smul, norm_one, mul_one] at hstep
    exact hstep.trans (add_le_add (hG σ) (hm σ))
  have hK0 : (0 : ℝ) ≤ K + μ := le_trans (norm_nonneg _) hX
  calc ‖Matrix.trace ((Gres H z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
        * Eblk d L W a)‖
      ≤ (Fintype.card (Vtx d L W) : ℝ)
          * ‖(Gres H z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
            * Eblk d L W a‖ := norm_matrix_trace_le_card_mul _
    _ ≤ (Fintype.card (Vtx d L W) : ℝ) * ((K + μ) * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact (norm_mul_le _ _).trans
          (mul_le_mul hX (OneStep_norm_Eblk_le_one a) (norm_nonneg _) hK0)
    _ = (((L * W) ^ d : ℕ) : ℝ) * (K + μ) := by rw [DriftLip_card_real, mul_one]

/-- The Lipschitz bound of the trace factor: the `m`-part cancels. -/
private theorem DriftLip_norm_trace_sub_le
    {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} {Δg : ℝ} (hΔ : 0 ≤ Δg)
    (m : Bool → ℂ) (hGd : ∀ s, ‖Gres H₁ z s - Gres H₂ z s‖ ≤ Δg) (σ : Bool) (a : Zd d L) :
    ‖Matrix.trace ((Gres H₁ z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
        * Eblk d L W a)
      - Matrix.trace ((Gres H₂ z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
        * Eblk d L W a)‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * Δg := by
  have heq : Matrix.trace ((Gres H₁ z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
        * Eblk d L W a)
      - Matrix.trace ((Gres H₂ z σ - m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
        * Eblk d L W a) = Matrix.trace ((Gres H₁ z σ - Gres H₂ z σ) * Eblk d L W a) := by
    rw [← Matrix.trace_sub, ← Matrix.sub_mul]
    congr 2
    abel
  rw [heq]
  calc ‖Matrix.trace ((Gres H₁ z σ - Gres H₂ z σ) * Eblk d L W a)‖
      ≤ (Fintype.card (Vtx d L W) : ℝ) * ‖(Gres H₁ z σ - Gres H₂ z σ) * Eblk d L W a‖ :=
        norm_matrix_trace_le_card_mul _
    _ ≤ (Fintype.card (Vtx d L W) : ℝ) * (Δg * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact (norm_mul_le _ _).trans
          (mul_le_mul (hGd σ) (OneStep_norm_Eblk_le_one a) (norm_nonneg _) hΔ)
    _ = (((L * W) ^ d : ℕ) : ℝ) * Δg := by rw [DriftLip_card_real, mul_one]

end Loops

/-! ### The loop drift, its Lipschitz constant, and the summation lemmas -/

section Drift

/-- **The `Ẽ` term of the loop generator**, in the loop vocabulary of the merged `GLoopFlow`:

`Ẽ(H, z, I) = W^d ∑_{1 ≤ k ≤ n} ∑_{a,b ∈ Z_L^d}
  ⟨(G(σ_k) - m(σ_k)) E_a⟩ S^{(B)}_{ab}(g) 𝓛_{G_k^{(b)}(σ,a)}`.

`RBM2D/Path/DriftLip.lean:384` (`DriftLip_eGterm`), rule R3: the weight `W²` of the two-dimensional
loop generator is `W^d` (the weight of `treeEqRhs`, `1_2:990`, `(pro_dyncalK)`); the blocks `E_a`
carry `W^{-d}`; the labels are `Z_L^d` and the variance matrix is `S^{(B)}(g)`. -/
noncomputable def DriftLip_eGterm (d L W : ℕ) (g : ℝ) [NeZero L] (m : Bool → ℂ)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    Matrix.trace ((Gres H z (I.σ.getD (k - 1) true)
        - m (I.σ.getD (k - 1) true) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
      * Eblk d L W a) * SB d L g a b * loopL d L W H z (I.cutGlue k b)

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- **The loop drift** in the (fine) matrix argument: the `Ẽ` term plus the right-hand side
`treeEqRhs` of `(pro_dyncalK)` evaluated on the `G`-loops of the block-reindexed matrix, at
`z_u^{(E)}` (`RBM2D/Path/DriftLip.lean:396` (`loopDrift`), where `treeEqRhs` is `primRhs`). -/
noncomputable def loopDrift (E u : ℝ) (I : Loop.LoopIdx (Zd d L))
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  DriftLip_eGterm d L W g (mSigma E) (blockMat d L W M) (zt E u) I
    + Loop.treeEqRhs d L W g (loopL d L W (blockMat d L W M) (zt E u)) I

/-- `loopDrift` is, by definition, the sum of the `Ẽ` term and `treeEqRhs (loopL ·)`. -/
theorem loopDrift_eq (E u : ℝ) (I : Loop.LoopIdx (Zd d L)) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    loopDrift d L W g E u I M = DriftLip_eGterm d L W g (mSigma E) (blockMat d L W M) (zt E u) I
      + Loop.treeEqRhs d L W g (loopL d L W (blockMat d L W M) (zt E u)) I := rfl

omit [NeZero L] [NeZero W] in
/-- **The explicit, closed-form Lipschitz constant**: with `N = (LW)^d`, `K = 1 + η⁻¹`
and `‖m‖ = max ‖m true‖ ‖m false‖`,
`2 N³ n² (n+2) (K + ‖m‖) K^{n+1} η⁻²`.  Polynomial in `L, W, n, η⁻¹, ‖m‖`; no existential and no
dependence on the matrices. -/
noncomputable def driftLip (n : ℕ) (η : ℝ) (m : Bool → ℂ) : ℝ :=
  2 * (((L * W) ^ d : ℕ) : ℝ) ^ 3 * (n : ℝ) ^ 2 * ((n : ℝ) + 2)
    * ((1 + η⁻¹) + max ‖m true‖ ‖m false‖) * (1 + η⁻¹) ^ (n + 1) * η⁻¹ ^ 2

variable {d L W} {g}

omit [NeZero W] in
/-- Summation lemma for the `Ẽ` term: if every summand `A₁ B₁ - A₂ B₂` is at most `X`, then
`‖Ẽ₁ - Ẽ₂‖ ≤ W^d · n · L^d · X`. -/
private theorem DriftLip_eGterm_sub_le (m : Bool → ℂ) (z : ℂ)
    {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ} (I : Loop.LoopIdx (Zd d L)) {X : ℝ}
    (hX : 0 ≤ X)
    (hterm : ∀ k ∈ Icc 1 I.length, ∀ a b : Zd d L,
      ‖Matrix.trace ((Gres H₁ z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
            * Eblk d L W a) * loopL d L W H₁ z (I.cutGlue k b)
        - Matrix.trace ((Gres H₂ z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
            * Eblk d L W a) * loopL d L W H₂ z (I.cutGlue k b)‖ ≤ X) :
    ‖DriftLip_eGterm d L W g m H₁ z I - DriftLip_eGterm d L W g m H₂ z I‖
      ≤ (W : ℝ) ^ d * ((I.length : ℝ) * ((L : ℝ) ^ d * X)) := by
  unfold DriftLip_eGterm
  rw [← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_sub_distrib]
  have hk : ∀ k ∈ Icc 1 I.length,
      ‖(∑ a : Zd d L, ∑ b : Zd d L,
          Matrix.trace ((Gres H₁ z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
            * Eblk d L W a) * SB d L g a b * loopL d L W H₁ z (I.cutGlue k b))
        - ∑ a : Zd d L, ∑ b : Zd d L,
          Matrix.trace ((Gres H₂ z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
            * Eblk d L W a) * SB d L g a b * loopL d L W H₂ z (I.cutGlue k b)‖ ≤ (L : ℝ) ^ d * X := by
    intro k hk
    refine DriftLip_sum_sub_le g _ _ hX fun a b => ?_
    have hrw : ∀ A₁ A₂ B₁ B₂ : ℂ, A₁ * SB d L g a b * B₁ - A₂ * SB d L g a b * B₂
        = (A₁ * B₁ - A₂ * B₂) * SB d L g a b := fun A₁ A₂ B₁ B₂ => by ring
    rw [hrw, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hterm k hk a b) (norm_nonneg _)
  calc ‖∑ k ∈ Icc 1 I.length,
        ((∑ a : Zd d L, ∑ b : Zd d L,
          Matrix.trace ((Gres H₁ z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
            * Eblk d L W a) * SB d L g a b * loopL d L W H₁ z (I.cutGlue k b))
        - ∑ a : Zd d L, ∑ b : Zd d L,
          Matrix.trace ((Gres H₂ z (I.σ.getD (k - 1) true)
            - m (I.σ.getD (k - 1) true) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))
            * Eblk d L W a) * SB d L g a b * loopL d L W H₂ z (I.cutGlue k b))‖
      ≤ ∑ _k ∈ Icc 1 I.length, (L : ℝ) ^ d * X :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hk)
    _ = (I.length : ℝ) * ((L : ℝ) ^ d * X) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        congr 2

omit [NeZero W] in
/-- Summation lemma for `treeEqRhs`: if every pair term `X₁ Y₁ - X₂ Y₂` is at most `X`, then
`‖treeEqRhs K₁ - treeEqRhs K₂‖ ≤ W^d · n² · L^d · X`. -/
private theorem DriftLip_primRhs_sub_le (K₁ K₂ : Loop.LoopIdx (Zd d L) → ℂ) (I : Loop.LoopIdx (Zd d L))
    {X : ℝ} (hX : 0 ≤ X)
    (hpair : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length, ∀ a b : Zd d L,
      ‖K₁ (I.cutGlueL k l a) * K₁ (I.cutGlueR k l b)
        - K₂ (I.cutGlueL k l a) * K₂ (I.cutGlueR k l b)‖ ≤ X) :
    ‖Loop.treeEqRhs d L W g K₁ I - Loop.treeEqRhs d L W g K₂ I‖
      ≤ (W : ℝ) ^ d * ((I.length : ℝ) * ((I.length : ℝ) * ((L : ℝ) ^ d * X))) := by
  unfold Loop.treeEqRhs
  rw [← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_sub_distrib]
  have hl_aux : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length,
      ‖(∑ a : Zd d L, ∑ b : Zd d L,
          K₁ (I.cutGlueL k l a) * SB d L g a b * K₁ (I.cutGlueR k l b))
        - ∑ a : Zd d L, ∑ b : Zd d L,
          K₂ (I.cutGlueL k l a) * SB d L g a b * K₂ (I.cutGlueR k l b)‖ ≤ (L : ℝ) ^ d * X := by
    intro k hk l hl
    refine DriftLip_sum_sub_le g _ _ hX fun a b => ?_
    have hrw : ∀ A₁ A₂ B₁ B₂ : ℂ, A₁ * SB d L g a b * B₁ - A₂ * SB d L g a b * B₂
        = (A₁ * B₁ - A₂ * B₂) * SB d L g a b := fun A₁ A₂ B₁ B₂ => by ring
    rw [hrw, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hpair k hk l hl a b) (norm_nonneg _)
  refine (norm_sum_le _ _).trans <|
    (Finset.sum_le_sum (g := fun _ => (I.length : ℝ) * ((L : ℝ) ^ d * X)) ?_).trans ?_
  · intro k hk
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans <|
      (Finset.sum_le_sum (g := fun _ => (L : ℝ) ^ d * X) fun l hl => hl_aux k hk l hl).trans ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (by positivity)
  · rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp

/-- The telescoped product bound for complex numbers. -/
private theorem DriftLip_norm_mul_sub_mul_le {A₁ A₂ B₁ B₂ : ℂ} {a₂ b₁ da db : ℝ}
    (hA₂ : ‖A₂‖ ≤ a₂) (hB₁ : ‖B₁‖ ≤ b₁) (hdA : ‖A₁ - A₂‖ ≤ da) (hdB : ‖B₁ - B₂‖ ≤ db) :
    ‖A₁ * B₁ - A₂ * B₂‖ ≤ da * b₁ + a₂ * db := by
  have h : A₁ * B₁ - A₂ * B₂ = (A₁ - A₂) * B₁ + A₂ * (B₁ - B₂) := by ring
  rw [h]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul hdA hB₁ (norm_nonneg _) (le_trans (norm_nonneg _) hdA)
  · rw [norm_mul]
    exact mul_le_mul hA₂ hdB (norm_nonneg _) (le_trans (norm_nonneg _) hA₂)

/-- **The core Lipschitz bound**, on block matrices (`DriftLip:514`), with the pair terms of
`treeEqRhs` bounded through the lengths of their own two sub-loops (`ℓ₁ + ℓ₂ = n + 2`). -/
private theorem DriftLip_block_sub_le (m : Bool → ℂ) {z : ℂ} (hz : z.im ≠ 0)
    {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ‖(DriftLip_eGterm d L W g m H₁ z I + Loop.treeEqRhs d L W g (loopL d L W H₁ z) I)
        - (DriftLip_eGterm d L W g m H₂ z I + Loop.treeEqRhs d L W g (loopL d L W H₂ z) I)‖
      ≤ driftLip d L W I.σ.length |z.im| m * ‖H₁ - H₂‖ := by
  obtain ⟨n, hndef⟩ : ∃ n, n = I.σ.length := ⟨_, rfl⟩
  rw [← hndef]
  have hwf' : n = I.a.length := hndef ▸ hwf
  have hlen : I.length = n := hwf'.symm
  have hn' : 1 ≤ n := by rw [hwf']; exact hn
  have hηpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + |z.im|⁻¹ := ⟨_, rfl⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = max ‖m true‖ ‖m false‖ := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (((L * W) ^ d : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Δg, hΔgdef⟩ : ∃ Δg : ℝ, Δg = |z.im|⁻¹ ^ 2 * ‖H₁ - H₂‖ := ⟨_, rfl⟩
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    have : (0 : ℝ) ≤ |z.im|⁻¹ := by positivity
    linarith
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hμ0 : (0 : ℝ) ≤ μ := by rw [hμdef]; exact le_trans (norm_nonneg _) (le_max_left _ _)
  have hμall : ∀ s : Bool, ‖m s‖ ≤ μ := by
    intro s
    rw [hμdef]
    cases s <;> first | exact le_max_left _ _ | exact le_max_right _ _
  have hKμ : (1 : ℝ) ≤ K + μ := by linarith
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; positivity
  have hΔg0 : (0 : ℝ) ≤ Δg := by rw [hΔgdef]; positivity
  have hG₁ : ∀ s, ‖Gres H₁ z s‖ ≤ K := fun s =>
    (norm_Gsig_le_inv_eta h₁ hηpos le_rfl s).trans (by rw [hKdef]; linarith)
  have hG₂ : ∀ s, ‖Gres H₂ z s‖ ≤ K := fun s =>
    (norm_Gsig_le_inv_eta h₂ hηpos le_rfl s).trans (by rw [hKdef]; linarith)
  have hGd : ∀ s, ‖Gres H₁ z s - Gres H₂ z s‖ ≤ Δg := fun s => by
    rw [hΔgdef]; exact OneStep_norm_Gsig_sub_le h₁ h₂ hz s
  -- the common bound of a term of the `Ẽ` sum
  obtain ⟨XE, hXEdef⟩ : ∃ XE : ℝ,
      XE = N ^ 2 * (((n : ℝ) + 2) * (K + μ) * K ^ (n + 1) * Δg) := ⟨_, rfl⟩
  have hXE0 : 0 ≤ XE := by rw [hXEdef]; positivity
  have hE : ‖DriftLip_eGterm d L W g m H₁ z I - DriftLip_eGterm d L W g m H₂ z I‖
      ≤ (W : ℝ) ^ d * ((I.length : ℝ) * ((L : ℝ) ^ d * XE)) := by
    refine DriftLip_eGterm_sub_le m z I hXE0 fun k hk a b => ?_
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    have hwfb : (I.cutGlue k b).WF := OneStep_wf_cutGlue hwf b hk1 hkn
    have hlenb : (I.cutGlue k b).length = n + 1 := by
      rw [OneStep_length_cutGlue I b hkn, hlen]
    have hB₁ : ‖loopL d L W H₁ z (I.cutGlue k b)‖ ≤ N * K ^ (n + 1) := by
      have := DriftLip_norm_gloop_le hK0 hG₁ hwfb
      rw [hlenb, ← hNdef] at this
      exact this
    have hBd : ‖loopL d L W H₁ z (I.cutGlue k b) - loopL d L W H₂ z (I.cutGlue k b)‖
        ≤ N * (((n : ℝ) + 1) * K ^ (n + 1) * Δg) := by
      have := DriftLip_norm_gloop_sub_le hK1 hΔg0 hG₁ hG₂ hGd hwfb
      rw [hlenb, ← hNdef] at this
      push_cast at this
      exact this
    have hA₂ := DriftLip_norm_trace_le (H := H₂) (z := z) m hG₂ hμall (I.σ.getD (k - 1) true) a
    have hAd := DriftLip_norm_trace_sub_le (H₁ := H₁) (H₂ := H₂) (z := z) hΔg0 m hGd
      (I.σ.getD (k - 1) true) a
    rw [← hNdef] at hA₂ hAd
    refine (DriftLip_norm_mul_sub_mul_le hA₂ hB₁ hAd hBd).trans ?_
    have hc : 0 ≤ N ^ 2 * K ^ (n + 1) * Δg := by positivity
    calc N * Δg * (N * K ^ (n + 1)) + N * (K + μ) * (N * (((n : ℝ) + 1) * K ^ (n + 1) * Δg))
        = (N ^ 2 * K ^ (n + 1) * Δg) * (1 + ((n : ℝ) + 1) * (K + μ)) := by ring
      _ ≤ (N ^ 2 * K ^ (n + 1) * Δg) * (((n : ℝ) + 2) * (K + μ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          nlinarith
      _ = XE := by rw [hXEdef]; ring
  have hP : ‖Loop.treeEqRhs d L W g (loopL d L W H₁ z) I - Loop.treeEqRhs d L W g (loopL d L W H₂ z) I‖
      ≤ (W : ℝ) ^ d * ((I.length : ℝ) * ((I.length : ℝ) * ((L : ℝ) ^ d * XE))) := by
    refine DriftLip_primRhs_sub_le _ _ I hXE0 fun k hk l hl a b => ?_
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hkl, hln⟩ := Finset.mem_Ioc.mp hl
    have hwfL : (I.cutGlueL k l a).WF := Loop.LoopIdx.wf_cutGlueL I a hwf hk1 hkl hln
    have hwfR : (I.cutGlueR k l b).WF := Loop.LoopIdx.wf_cutGlueR I b hwf hk1 hkl hln
    have hℓ₁ := Loop.LoopIdx.length_cutGlueL I a hk1 hkl hln
    have hℓ₂ := Loop.LoopIdx.length_cutGlueR I b hk1 hkl hln
    have hsum : (I.cutGlueL k l a).length + (I.cutGlueR k l b).length = n + 2 := by omega
    have hX₂ : ‖loopL d L W H₂ z (I.cutGlueL k l a)‖ ≤ N * K ^ (I.cutGlueL k l a).length := by
      have := DriftLip_norm_gloop_le hK0 hG₂ hwfL
      rwa [← hNdef] at this
    have hY₁ : ‖loopL d L W H₁ z (I.cutGlueR k l b)‖ ≤ N * K ^ (I.cutGlueR k l b).length := by
      have := DriftLip_norm_gloop_le hK0 hG₁ hwfR
      rwa [← hNdef] at this
    have hXd : ‖loopL d L W H₁ z (I.cutGlueL k l a) - loopL d L W H₂ z (I.cutGlueL k l a)‖
        ≤ N * (((I.cutGlueL k l a).length : ℝ) * K ^ (I.cutGlueL k l a).length * Δg) := by
      have := DriftLip_norm_gloop_sub_le hK1 hΔg0 hG₁ hG₂ hGd hwfL
      rwa [← hNdef] at this
    have hYd : ‖loopL d L W H₁ z (I.cutGlueR k l b) - loopL d L W H₂ z (I.cutGlueR k l b)‖
        ≤ N * (((I.cutGlueR k l b).length : ℝ) * K ^ (I.cutGlueR k l b).length * Δg) := by
      have := DriftLip_norm_gloop_sub_le hK1 hΔg0 hG₁ hG₂ hGd hwfR
      rwa [← hNdef] at this
    refine (DriftLip_norm_mul_sub_mul_le hX₂ hY₁ hXd hYd).trans ?_
    have hcast : ((I.cutGlueL k l a).length : ℝ) + ((I.cutGlueR k l b).length : ℝ)
        = (n : ℝ) + 2 := by exact_mod_cast hsum
    have hpow : K ^ (n + 2) = K ^ (I.cutGlueL k l a).length * K ^ (I.cutGlueR k l b).length := by
      rw [← pow_add, hsum]
    have hpow' : K ^ (n + 2) ≤ (K + μ) * K ^ (n + 1) := by
      rw [pow_succ K (n + 1), mul_comm (K + μ)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc N * (((I.cutGlueL k l a).length : ℝ) * K ^ (I.cutGlueL k l a).length * Δg)
          * (N * K ^ (I.cutGlueR k l b).length)
        + N * K ^ (I.cutGlueL k l a).length
          * (N * (((I.cutGlueR k l b).length : ℝ) * K ^ (I.cutGlueR k l b).length * Δg))
        = N ^ 2 * (((I.cutGlueL k l a).length : ℝ) + ((I.cutGlueR k l b).length : ℝ))
            * (K ^ (I.cutGlueL k l a).length * K ^ (I.cutGlueR k l b).length) * Δg := by ring
      _ = N ^ 2 * (((n : ℝ) + 2) * K ^ (n + 2) * Δg) := by rw [hcast, ← hpow]; ring
      _ ≤ N ^ 2 * (((n : ℝ) + 2) * ((K + μ) * K ^ (n + 1)) * Δg) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow' (by positivity)) hΔg0
      _ = XE := by rw [hXEdef]; ring
  rw [hlen] at hE hP
  have hrearr : (DriftLip_eGterm d L W g m H₁ z I + Loop.treeEqRhs d L W g (loopL d L W H₁ z) I)
      - (DriftLip_eGterm d L W g m H₂ z I + Loop.treeEqRhs d L W g (loopL d L W H₂ z) I)
      = (DriftLip_eGterm d L W g m H₁ z I - DriftLip_eGterm d L W g m H₂ z I)
        + (Loop.treeEqRhs d L W g (loopL d L W H₁ z) I - Loop.treeEqRhs d L W g (loopL d L W H₂ z) I) := by
    ring
  rw [hrearr]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
  have hcomb : (n : ℝ) + (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
  have hWL : (W : ℝ) ^ d * (L : ℝ) ^ d = N := by rw [hNdef]; push_cast; ring
  calc ‖(DriftLip_eGterm d L W g m H₁ z I - DriftLip_eGterm d L W g m H₂ z I)
          + (Loop.treeEqRhs d L W g (loopL d L W H₁ z) I - Loop.treeEqRhs d L W g (loopL d L W H₂ z) I)‖
      ≤ (W : ℝ) ^ d * ((n : ℝ) * ((L : ℝ) ^ d * XE))
        + (W : ℝ) ^ d * ((n : ℝ) * ((n : ℝ) * ((L : ℝ) ^ d * XE))) :=
        (norm_add_le _ _).trans (add_le_add hE hP)
    _ = ((W : ℝ) ^ d * (L : ℝ) ^ d) * (((n : ℝ) + (n : ℝ) ^ 2) * XE) := by ring
    _ ≤ ((W : ℝ) ^ d * (L : ℝ) ^ d) * ((2 * (n : ℝ) ^ 2) * XE) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcomb hXE0) (by positivity)
    _ = driftLip d L W n |z.im| m * ‖H₁ - H₂‖ := by
        rw [hWL, hXEdef, hΔgdef]
        unfold driftLip
        rw [← hKdef, ← hμdef, ← hNdef]
        ring

variable (d L W g) in
/-- **The Lipschitz bound for the loop drift**: `loopDrift` is Lipschitz in the matrix argument
(on Hermitian matrices), deterministically, with the explicit constant `driftLip`.  No hypothesis on
`L` beyond `NeZero L`, and `W ≥ 1` through `NeZero W`. -/
theorem norm_loopDrift_sub_le {E u : ℝ} (hz : (zt E u).im ≠ 0)
    {M₁ M₂ : Matrix (Idx d L W) (Idx d L W) ℂ} (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian)
    {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ‖loopDrift d L W g E u I M₁ - loopDrift d L W g E u I M₂‖
      ≤ driftLip d L W I.σ.length |(zt E u).im| (mSigma E) * ‖M₁ - M₂‖ := by
  rw [loopDrift_eq, loopDrift_eq]
  refine (DriftLip_block_sub_le (mSigma E) hz (DriftLip_isHermitian_blockMat hM₁)
    (DriftLip_isHermitian_blockMat hM₂) hwf hn).trans (le_of_eq ?_)
  rw [DriftLip_blockMat_sub, DriftLip_norm_blockMat]

end Drift

/-! ## 1. Generic jets of a word of resolvent factors

A word `∏ᵢ R_{σᵢ} E_{aᵢ}` whose resolvent factors have the jets `R`, `r1 = -R D R`,
`r2 = 2 R D R D R` along a line has the jets `w0`, `w1`, `w2` below (Leibniz recursion). -/

section Jets

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- The word `∏ R_{σᵢ} E_{aᵢ}` (as in `gloopProd`). -/
private def OneStep_w0 (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (l : List (Bool × ι)) : Matrix n n ℂ :=
  l.foldr (fun p M => R p.1 * Ei p.2 * M) 1

/-- First jet of a resolvent factor. -/
private def OneStep_r1 (R D : Bool → Matrix n n ℂ) (σ : Bool) : Matrix n n ℂ :=
  -(R σ * D σ * R σ)

/-- Second jet of a resolvent factor. -/
private def OneStep_r2 (R D : Bool → Matrix n n ℂ) (σ : Bool) : Matrix n n ℂ :=
  R σ * D σ * R σ * D σ * R σ + R σ * D σ * R σ * D σ * R σ

/-- First derivative of the word. -/
private def OneStep_w1 (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) :
    List (Bool × ι) → Matrix n n ℂ
  | [] => 0
  | p :: l => (OneStep_r1 R D p.1 * Ei p.2) * OneStep_w0 R Ei l
      + (R p.1 * Ei p.2) * OneStep_w1 R D Ei l

/-- Second derivative of the word. -/
private def OneStep_w2 (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) :
    List (Bool × ι) → Matrix n n ℂ
  | [] => 0
  | p :: l => (OneStep_r2 R D p.1 * Ei p.2) * OneStep_w0 R Ei l
      + ((OneStep_r1 R D p.1 * Ei p.2) * OneStep_w1 R D Ei l
          + (OneStep_r1 R D p.1 * Ei p.2) * OneStep_w1 R D Ei l)
      + (R p.1 * Ei p.2) * OneStep_w2 R D Ei l

private theorem OneStep_w0_cons (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ) (p : Bool × ι)
    (l : List (Bool × ι)) :
    OneStep_w0 R Ei (p :: l) = R p.1 * Ei p.2 * OneStep_w0 R Ei l := rfl

private theorem OneStep_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

private theorem OneStep_nmul {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    ‖A * B‖ ≤ a * b :=
  (norm_mul_le _ _).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

private theorem OneStep_norm_sub_mul_le {A₁ A₂ B₁ B₂ : Matrix n n ℂ} {a₂ b₁ da db : ℝ}
    (hA₂ : ‖A₂‖ ≤ a₂) (hB₁ : ‖B₁‖ ≤ b₁) (hdA : ‖A₁ - A₂‖ ≤ da) (hdB : ‖B₁ - B₂‖ ≤ db) :
    ‖A₁ * B₁ - A₂ * B₂‖ ≤ da * b₁ + a₂ * db := by
  have h : A₁ * B₁ - A₂ * B₂ = (A₁ - A₂) * B₁ + A₂ * (B₁ - B₂) := by noncomm_ring
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (OneStep_nmul hdA hB₁) (OneStep_nmul hA₂ hdB))

private theorem OneStep_norm_add3 (X Y Z : Matrix n n ℂ) :
    ‖X + (Y + Y) + Z‖ ≤ ‖X‖ + 2 * ‖Y‖ + ‖Z‖ := by
  have h1 := norm_add_le (X + (Y + Y)) Z
  have h2 := norm_add_le X (Y + Y)
  have h3 := norm_add_le Y Y
  linarith

/-- The hypotheses of the norm bounds on the jets of a word. -/
private structure OneStep_Data (R D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (K b : ℝ) : Prop where
  hK : 0 ≤ K
  hb : 0 ≤ b
  hR : ∀ σ, ‖R σ‖ ≤ K
  hD : ∀ σ, ‖D σ‖ ≤ b
  hE : ∀ a, ‖Ei a‖ ≤ 1

/-- The hypotheses of the Lipschitz bounds: a second factor family at distance `K² δ`. -/
private structure OneStep_Diff (R₁ R₂ D : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (K b δ : ℝ) : Prop where
  d₁ : OneStep_Data R₁ D Ei K b
  hR₂ : ∀ σ, ‖R₂ σ‖ ≤ K
  hδ : 0 ≤ δ
  hdiff : ∀ σ, ‖R₁ σ - R₂ σ‖ ≤ K ^ 2 * δ

section Bounds

variable {R D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {K b : ℝ}

private theorem OneStep_norm_r1_le (h : OneStep_Data R D Ei K b) (σ : Bool) :
    ‖OneStep_r1 R D σ‖ ≤ K * b * K := by
  rw [OneStep_r1, norm_neg]
  exact OneStep_nmul (OneStep_nmul (h.hR σ) (h.hD σ)) (h.hR σ)

private theorem OneStep_norm_r2_le (h : OneStep_Data R D Ei K b) (σ : Bool) :
    ‖OneStep_r2 R D σ‖ ≤ 2 * (K * b * K * b * K) := by
  rw [OneStep_r2]
  have h5 := OneStep_nmul (OneStep_nmul (OneStep_nmul (OneStep_nmul (h.hR σ) (h.hD σ))
    (h.hR σ)) (h.hD σ)) (h.hR σ)
  calc ‖R σ * D σ * R σ * D σ * R σ + R σ * D σ * R σ * D σ * R σ‖
      ≤ ‖R σ * D σ * R σ * D σ * R σ‖ + ‖R σ * D σ * R σ * D σ * R σ‖ := norm_add_le _ _
    _ ≤ K * b * K * b * K + K * b * K * b * K := add_le_add h5 h5
    _ = 2 * (K * b * K * b * K) := by ring

private theorem OneStep_norm_w0_le (h : OneStep_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖OneStep_w0 R Ei l‖ ≤ K ^ l.length := by
  induction l with
  | nil => simpa [OneStep_w0] using OneStep_norm_one_le
  | cons p l ih =>
      rw [OneStep_w0_cons, List.length_cons, pow_succ]
      calc ‖R p.1 * Ei p.2 * OneStep_w0 R Ei l‖ ≤ (K * 1) * K ^ l.length :=
            OneStep_nmul (OneStep_nmul (h.hR p.1) (h.hE p.2)) ih
        _ = K ^ l.length * K := by ring

private theorem OneStep_norm_w1_le (h : OneStep_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖OneStep_w1 R D Ei l‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * b := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, List.length_cons]
      have h1 : ‖(OneStep_r1 R D p.1 * Ei p.2) * OneStep_w0 R Ei l‖
          ≤ (K * b * K * 1) * K ^ l.length :=
        OneStep_nmul (OneStep_nmul (OneStep_norm_r1_le h p.1) (h.hE p.2))
          (OneStep_norm_w0_le h l)
      have h2 : ‖(R p.1 * Ei p.2) * OneStep_w1 R D Ei l‖
          ≤ (K * 1) * ((l.length : ℝ) * K ^ (l.length + 1) * b) :=
        OneStep_nmul (OneStep_nmul (h.hR p.1) (h.hE p.2)) ih
      refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
      push_cast
      ring

private theorem OneStep_norm_w2_le (h : OneStep_Data R D Ei K b) (l : List (Bool × ι)) :
    ‖OneStep_w2 R D Ei l‖ ≤ (l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b ^ 2 := by
  induction l with
  | nil => simp [OneStep_w2]
  | cons p l ih =>
      rw [OneStep_w2, List.length_cons]
      have h1 : ‖(OneStep_r2 R D p.1 * Ei p.2) * OneStep_w0 R Ei l‖
          ≤ (2 * (K * b * K * b * K) * 1) * K ^ l.length :=
        OneStep_nmul (OneStep_nmul (OneStep_norm_r2_le h p.1) (h.hE p.2))
          (OneStep_norm_w0_le h l)
      have h2 : ‖(OneStep_r1 R D p.1 * Ei p.2) * OneStep_w1 R D Ei l‖
          ≤ (K * b * K * 1) * ((l.length : ℝ) * K ^ (l.length + 1) * b) :=
        OneStep_nmul (OneStep_nmul (OneStep_norm_r1_le h p.1) (h.hE p.2))
          (OneStep_norm_w1_le h l)
      have h3 : ‖(R p.1 * Ei p.2) * OneStep_w2 R D Ei l‖
          ≤ (K * 1) * ((l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b ^ 2) :=
        OneStep_nmul (OneStep_nmul (h.hR p.1) (h.hE p.2)) ih
      refine (OneStep_norm_add3 _ _ _).trans ((add_le_add (add_le_add h1
        (mul_le_mul_of_nonneg_left h2 zero_le_two)) h3).trans (le_of_eq ?_))
      push_cast
      ring

end Bounds

end Jets

section DiffBounds

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {R₁ R₂ D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {K b δ : ℝ}

private theorem OneStep_norm_r1_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ) (σ : Bool) :
    ‖OneStep_r1 R₁ D σ - OneStep_r1 R₂ D σ‖ ≤ 2 * (K ^ 3 * b * δ) := by
  have hK := h.d₁.hK
  have hb := h.d₁.hb
  have hA₂ : ‖R₂ σ * D σ‖ ≤ K * b := OneStep_nmul (h.hR₂ σ) (h.d₁.hD σ)
  have hdA : ‖R₁ σ * D σ - R₂ σ * D σ‖ ≤ K ^ 2 * δ * b := by
    rw [← Matrix.sub_mul]
    exact OneStep_nmul (h.hdiff σ) (h.d₁.hD σ)
  have := OneStep_norm_sub_mul_le hA₂ (h.d₁.hR σ) hdA (h.hdiff σ)
  have e : OneStep_r1 R₁ D σ - OneStep_r1 R₂ D σ
      = -(R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ) := by
    simp only [OneStep_r1]; abel
  rw [e, norm_neg]
  refine this.trans (le_of_eq ?_)
  ring

private theorem OneStep_norm_r2_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ) (σ : Bool) :
    ‖OneStep_r2 R₁ D σ - OneStep_r2 R₂ D σ‖ ≤ 6 * (K ^ 4 * b ^ 2 * δ) := by
  have hK := h.d₁.hK
  have hb := h.d₁.hb
  have hδ := h.hδ
  have hA₂ : ‖R₂ σ * D σ‖ ≤ K * b := OneStep_nmul (h.hR₂ σ) (h.d₁.hD σ)
  have hdA : ‖R₁ σ * D σ - R₂ σ * D σ‖ ≤ K ^ 2 * δ * b := by
    rw [← Matrix.sub_mul]
    exact OneStep_nmul (h.hdiff σ) (h.d₁.hD σ)
  -- `R D R`
  have h3 := OneStep_norm_sub_mul_le hA₂ (h.d₁.hR σ) hdA (h.hdiff σ)
  have h3' : ‖R₂ σ * D σ * R₂ σ‖ ≤ K * b * K :=
    OneStep_nmul (OneStep_nmul (h.hR₂ σ) (h.d₁.hD σ)) (h.hR₂ σ)
  -- `R D R D`
  have h4 : ‖(R₁ σ * D σ * R₁ σ) * D σ - (R₂ σ * D σ * R₂ σ) * D σ‖
      ≤ (K ^ 2 * δ * b * K + K * b * (K ^ 2 * δ)) * b := by
    rw [← Matrix.sub_mul]
    exact OneStep_nmul h3 (h.d₁.hD σ)
  have h4' : ‖R₂ σ * D σ * R₂ σ * D σ‖ ≤ K * b * K * b :=
    OneStep_nmul h3' (h.d₁.hD σ)
  -- `R D R D R`
  have h5 := OneStep_norm_sub_mul_le h4' (h.d₁.hR σ) h4 (h.hdiff σ)
  have e : OneStep_r2 R₁ D σ - OneStep_r2 R₂ D σ
      = (R₁ σ * D σ * R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ * D σ * R₂ σ)
        + (R₁ σ * D σ * R₁ σ * D σ * R₁ σ - R₂ σ * D σ * R₂ σ * D σ * R₂ σ) := by
    simp only [OneStep_r2]; abel
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add h5 h5).trans (le_of_eq ?_))
  ring

private theorem OneStep_norm_w0_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖OneStep_w0 R₁ Ei l - OneStep_w0 R₂ Ei l‖ ≤ (l.length : ℝ) * K ^ (l.length + 1) * δ := by
  induction l with
  | nil => simp [OneStep_w0]
  | cons p l ih =>
      rw [OneStep_w0_cons, OneStep_w0_cons, List.length_cons]
      have hA₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := OneStep_nmul (h.hR₂ p.1) (h.d₁.hE p.2)
      have hdA : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (h.hdiff p.1) (h.d₁.hE p.2)
      have := OneStep_norm_sub_mul_le hA₂ (OneStep_norm_w0_le h.d₁ l) hdA ih
      refine this.trans (le_of_eq ?_)
      push_cast
      ring

private theorem OneStep_norm_w1_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖OneStep_w1 R₁ D Ei l - OneStep_w1 R₂ D Ei l‖
      ≤ (l.length : ℝ) * (l.length + 1) * K ^ (l.length + 2) * b * δ := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, OneStep_w1, List.length_cons]
      have hE := h.d₁.hE p.2
      -- the `r1` part
      have hA₂ : ‖OneStep_r1 R₂ D p.1 * Ei p.2‖ ≤ K * b * K * 1 :=
        OneStep_nmul (OneStep_norm_r1_le ⟨h.d₁.hK, h.d₁.hb, h.hR₂, h.d₁.hD, h.d₁.hE⟩ p.1) hE
      have hdA : ‖OneStep_r1 R₁ D p.1 * Ei p.2 - OneStep_r1 R₂ D p.1 * Ei p.2‖
          ≤ 2 * (K ^ 3 * b * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (OneStep_norm_r1_sub_le h p.1) hE
      have hα := OneStep_norm_sub_mul_le hA₂ (OneStep_norm_w0_le h.d₁ l) hdA
        (OneStep_norm_w0_sub_le h l)
      -- the `R` part
      have hB₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := OneStep_nmul (h.hR₂ p.1) hE
      have hdB : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (h.hdiff p.1) hE
      have hβ := OneStep_norm_sub_mul_le hB₂ (OneStep_norm_w1_le h.d₁ l) hdB ih
      rw [add_sub_add_comm]
      refine (norm_add_le _ _).trans ((add_le_add hα hβ).trans (le_of_eq ?_))
      push_cast
      ring

private theorem OneStep_norm_w2_sub_le (h : OneStep_Diff R₁ R₂ D Ei K b δ)
    (l : List (Bool × ι)) :
    ‖OneStep_w2 R₁ D Ei l - OneStep_w2 R₂ D Ei l‖
      ≤ (l.length : ℝ) * (l.length + 1) * (l.length + 2) * K ^ (l.length + 3) * b ^ 2 * δ := by
  induction l with
  | nil => simp [OneStep_w2]
  | cons p l ih =>
      rw [OneStep_w2, OneStep_w2, List.length_cons]
      have hE := h.d₁.hE p.2
      have h₂ : OneStep_Data R₂ D Ei K b := ⟨h.d₁.hK, h.d₁.hb, h.hR₂, h.d₁.hD, h.d₁.hE⟩
      -- the `r2` part
      have hA₂ : ‖OneStep_r2 R₂ D p.1 * Ei p.2‖ ≤ 2 * (K * b * K * b * K) * 1 :=
        OneStep_nmul (OneStep_norm_r2_le h₂ p.1) hE
      have hdA : ‖OneStep_r2 R₁ D p.1 * Ei p.2 - OneStep_r2 R₂ D p.1 * Ei p.2‖
          ≤ 6 * (K ^ 4 * b ^ 2 * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (OneStep_norm_r2_sub_le h p.1) hE
      have hα := OneStep_norm_sub_mul_le hA₂ (OneStep_norm_w0_le h.d₁ l) hdA
        (OneStep_norm_w0_sub_le h l)
      -- the `r1` part
      have hB₂ : ‖OneStep_r1 R₂ D p.1 * Ei p.2‖ ≤ K * b * K * 1 :=
        OneStep_nmul (OneStep_norm_r1_le h₂ p.1) hE
      have hdB : ‖OneStep_r1 R₁ D p.1 * Ei p.2 - OneStep_r1 R₂ D p.1 * Ei p.2‖
          ≤ 2 * (K ^ 3 * b * δ) * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (OneStep_norm_r1_sub_le h p.1) hE
      have hβ := OneStep_norm_sub_mul_le hB₂ (OneStep_norm_w1_le h.d₁ l) hdB
        (OneStep_norm_w1_sub_le h l)
      -- the `R` part
      have hC₂ : ‖R₂ p.1 * Ei p.2‖ ≤ K * 1 := OneStep_nmul (h.hR₂ p.1) hE
      have hdC : ‖R₁ p.1 * Ei p.2 - R₂ p.1 * Ei p.2‖ ≤ K ^ 2 * δ * 1 := by
        rw [← Matrix.sub_mul]
        exact OneStep_nmul (h.hdiff p.1) hE
      have hγ := OneStep_norm_sub_mul_le hC₂ (OneStep_norm_w2_le h.d₁ l) hdC ih
      have e : ∀ a₁ a₂ c₁ c₂ d₁ d₂ : Matrix n n ℂ,
          (a₁ + (c₁ + c₁) + d₁) - (a₂ + (c₂ + c₂) + d₂)
            = (a₁ - a₂) + ((c₁ - c₂) + (c₁ - c₂)) + (d₁ - d₂) := fun _ _ _ _ _ _ => by abel
      rw [e]
      refine (OneStep_norm_add3 _ _ _).trans ((add_le_add (add_le_add hα
        (mul_le_mul_of_nonneg_left hβ zero_le_two)) hγ).trans (le_of_eq ?_))
      push_cast
      ring

end DiffBounds

section Deriv

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {Rt : ℝ → Bool → Matrix n n ℂ} {D : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ} {t : ℝ}

/-- Jets of a word along a family of resolvent factors with `R' = -R D R`. -/
private theorem OneStep_hasDerivAt_w0
    (hR : ∀ σ, HasDerivAt (fun s => Rt s σ) (-(Rt t σ * D σ * Rt t σ)) t) (l : List (Bool × ι)) :
    HasDerivAt (fun s => OneStep_w0 (Rt s) Ei l) (OneStep_w1 (Rt t) D Ei l) t := by
  induction l with
  | nil => simpa [OneStep_w0, OneStep_w1] using hasDerivAt_const t (1 : Matrix n n ℂ)
  | cons p l ih =>
      have h : HasDerivAt (fun s => Rt s p.1 * Ei p.2 * OneStep_w0 (Rt s) Ei l)
          ((-(Rt t p.1 * D p.1 * Rt t p.1)) * Ei p.2 * OneStep_w0 (Rt t) Ei l
            + Rt t p.1 * Ei p.2 * OneStep_w1 (Rt t) D Ei l) t :=
        ((hR p.1).mul_const (Ei p.2)).mul ih
      simpa only [OneStep_w0_cons, OneStep_w1, OneStep_r1] using h

private theorem OneStep_hasDerivAt_w1
    (hR : ∀ σ, HasDerivAt (fun s => Rt s σ) (-(Rt t σ * D σ * Rt t σ)) t) (l : List (Bool × ι)) :
    HasDerivAt (fun s => OneStep_w1 (Rt s) D Ei l) (OneStep_w2 (Rt t) D Ei l) t := by
  induction l with
  | nil => simpa [OneStep_w1, OneStep_w2] using hasDerivAt_const t (0 : Matrix n n ℂ)
  | cons p l ih =>
      have hr1 : HasDerivAt (fun s => OneStep_r1 (Rt s) D p.1)
          (OneStep_r2 (Rt t) D p.1) t := by
        have h : HasDerivAt (fun s => -(Rt s p.1 * D p.1 * Rt s p.1))
            (-(-(Rt t p.1 * D p.1 * Rt t p.1) * D p.1 * Rt t p.1
              + Rt t p.1 * D p.1 * -(Rt t p.1 * D p.1 * Rt t p.1))) t :=
          (((hR p.1).mul_const (D p.1)).mul (hR p.1)).neg
        have e : OneStep_r2 (Rt t) D p.1 = -(-(Rt t p.1 * D p.1 * Rt t p.1) * D p.1 * Rt t p.1
              + Rt t p.1 * D p.1 * -(Rt t p.1 * D p.1 * Rt t p.1)) := by
          simp only [OneStep_r2]
          noncomm_ring
        rw [e]
        exact h
      have h0 := OneStep_hasDerivAt_w0 (Ei := Ei) hR l
      have h1 : HasDerivAt (fun s => OneStep_r1 (Rt s) D p.1 * Ei p.2 * OneStep_w0 (Rt s) Ei l)
          (OneStep_r2 (Rt t) D p.1 * Ei p.2 * OneStep_w0 (Rt t) Ei l
            + OneStep_r1 (Rt t) D p.1 * Ei p.2 * OneStep_w1 (Rt t) D Ei l) t :=
        (hr1.mul_const (Ei p.2)).mul h0
      have h2 : HasDerivAt (fun s => Rt s p.1 * Ei p.2 * OneStep_w1 (Rt s) D Ei l)
          (OneStep_r1 (Rt t) D p.1 * Ei p.2 * OneStep_w1 (Rt t) D Ei l
            + Rt t p.1 * Ei p.2 * OneStep_w2 (Rt t) D Ei l) t :=
        ((hR p.1).mul_const (Ei p.2)).mul ih
      have h3 := h1.add h2
      refine h3.congr_deriv ?_
      simp only [OneStep_w2]
      abel

end Deriv

section LinCont

variable {n ι : Type*} [Fintype n] [DecidableEq n]
variable {R : Bool → Matrix n n ℂ} {Ei : ι → Matrix n n ℂ}

private theorem OneStep_w1_add (D₁ D₂ : Bool → Matrix n n ℂ) (l : List (Bool × ι)) :
    OneStep_w1 R (D₁ + D₂) Ei l = OneStep_w1 R D₁ Ei l + OneStep_w1 R D₂ Ei l := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, OneStep_w1, OneStep_w1, ih]
      simp only [OneStep_r1, Pi.add_apply]
      noncomm_ring

private theorem OneStep_w1_smul (c : ℝ) (D : Bool → Matrix n n ℂ) (l : List (Bool × ι)) :
    OneStep_w1 R (c • D) Ei l = c • OneStep_w1 R D Ei l := by
  induction l with
  | nil => simp [OneStep_w1]
  | cons p l ih =>
      rw [OneStep_w1, OneStep_w1, ih]
      simp only [OneStep_r1, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, smul_add, Matrix.neg_mul,
        smul_neg]

/-- `D ↦ w1 R D` is real-linear. -/
private def OneStep_w1Lin (R : Bool → Matrix n n ℂ) (Ei : ι → Matrix n n ℂ)
    (l : List (Bool × ι)) : (Bool → Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ where
  toFun D := OneStep_w1 R D Ei l
  map_add' D₁ D₂ := OneStep_w1_add D₁ D₂ l
  map_smul' c D := OneStep_w1_smul c D l

variable {X : Type*} [TopologicalSpace X] {Rt : X → Bool → Matrix n n ℂ}
  {D : Bool → Matrix n n ℂ}

private theorem OneStep_continuous_w0 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => OneStep_w0 (Rt x) Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih => exact (((h p.1).mul continuous_const).mul ih)

private theorem OneStep_continuous_w1 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => OneStep_w1 (Rt x) D Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hr1 : Continuous fun x => OneStep_r1 (Rt x) D p.1 :=
        (((h p.1).mul continuous_const).mul (h p.1)).neg
      exact ((hr1.mul continuous_const).mul (OneStep_continuous_w0 h l)).add
        (((h p.1).mul continuous_const).mul ih)

private theorem OneStep_continuous_w2 (h : ∀ σ, Continuous fun x => Rt x σ)
    (l : List (Bool × ι)) : Continuous fun x => OneStep_w2 (Rt x) D Ei l := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      have hr1 : Continuous fun x => OneStep_r1 (Rt x) D p.1 :=
        (((h p.1).mul continuous_const).mul (h p.1)).neg
      have hr2 : Continuous fun x => OneStep_r2 (Rt x) D p.1 := by
        have h5 : Continuous fun x => Rt x p.1 * D p.1 * Rt x p.1 * D p.1 * Rt x p.1 :=
          (((((h p.1).mul continuous_const).mul (h p.1)).mul continuous_const).mul (h p.1))
        exact h5.add h5
      have h1 : Continuous fun x => OneStep_r1 (Rt x) D p.1 * Ei p.2 * OneStep_w1 (Rt x) D Ei l :=
        (hr1.mul continuous_const).mul (OneStep_continuous_w1 (Ei := Ei) (D := D) h l)
      exact (((hr2.mul continuous_const).mul (OneStep_continuous_w0 h l)).add (h1.add h1)).add
        (((h p.1).mul continuous_const).mul ih)

end LinCont
/-! ## 2. The loop functional along a line and along the spectral path -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem OneStep_hasDerivAt_trace {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- The derivative of a signed resolvent along a moving Hermitian matrix and spectral parameter. -/
private theorem OneStep_hasDerivAt_Gsig {H : ℝ → Matrix n n ℂ} {zf : ℝ → ℂ}
    {H' : Matrix n n ℂ} {z' : ℂ} {t : ℝ}
    (hH : HasDerivAt H H' t) (hz : HasDerivAt zf z' t) (hherm : (H t).IsHermitian)
    (him : (zf t).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s => Gres (H s) (zf s) σ)
      (-(Gres (H t) (zf t) σ *
        (H' - (if σ then z' else (starRingEnd ℂ) z') • (1 : Matrix n n ℂ)) *
        Gres (H t) (zf t) σ)) t := by
  cases σ with
  | true => exact hasDerivAt_green_moving hH hz hherm him
  | false =>
      have hz' : HasDerivAt (fun s => (starRingEnd ℂ) (zf s)) ((starRingEnd ℂ) z') t := hz.star
      have him' : ((starRingEnd ℂ) (zf t)).im ≠ 0 := by simpa using him
      exact hasDerivAt_green_moving hH hz' hherm him'


set_option linter.unusedFintypeInType false in
/-- The affine line `s ↦ M + s • A` has derivative `A` (`RBM2D/Gauss/Envelope.lean:144`). -/
private theorem OneStep_hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian
(`RBM2D/Gauss/Envelope.lean:268`). -/
private theorem OneStep_isHermitian_add_realSmul {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

end Resolvent

section Loop

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The first jet `tr w1` of the loop functional with resolvent data `Gres H z` and directions
`D`. -/
private def OneStep_J1 (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  Matrix.trace (OneStep_w1 (fun σ => Gres H z σ) D (Eblk d L W) (I.σ.zip I.a))

/-- The second jet `tr w2` of the loop functional. -/
private def OneStep_J2 (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  Matrix.trace (OneStep_w2 (fun σ => Gres H z σ) D (Eblk d L W) (I.σ.zip I.a))

/-- The spectral direction of the factor `G(σ)`: `m_σ · 1`. -/
private def OneStep_Dsp (d L W : ℕ) (E : ℝ) :
    Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  fun σ => spectralMSign E σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)

section LineDeriv

variable {H B : Matrix (Vtx d L W) (Vtx d L W) ℂ}

private theorem OneStep_hasDerivAt_lineR (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (y : ℝ) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gres (H + (s : ℂ) • B) z σ)
      (-(Gres (H + (y : ℂ) • B) z σ * B * Gres (H + (y : ℂ) • B) z σ)) y := by
  have := OneStep_hasDerivAt_Gsig (OneStep_hasDerivAt_line H B y) (hasDerivAt_const y z)
    (OneStep_isHermitian_add_realSmul hH hB y) hz σ
  simpa using this

/-- First derivative of the loop functional along a Hermitian line. -/
private theorem OneStep_hasDerivAt_line0 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (y : ℝ) :
    HasDerivAt (fun s : ℝ => loopL d L W (H + (s : ℂ) • B) z I)
      (OneStep_J1 (H + (y : ℂ) • B) z (fun _ => B) I) y :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gres (H + (s : ℂ) • B) z σ) (D := fun _ => B)
      (Ei := Eblk d L W) (OneStep_hasDerivAt_lineR hH hB hz y) (I.σ.zip I.a))

/-- Second derivative of the loop functional along a Hermitian line. -/
private theorem OneStep_hasDerivAt_line1 (hH : H.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (y : ℝ) :
    HasDerivAt (fun s : ℝ => OneStep_J1 (H + (s : ℂ) • B) z (fun _ => B) I)
      (OneStep_J2 (H + (y : ℂ) • B) z (fun _ => B) I) y :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w1 (Rt := fun s σ => Gres (H + (s : ℂ) • B) z σ) (D := fun _ => B)
      (Ei := Eblk d L W) (OneStep_hasDerivAt_lineR hH hB hz y) (I.σ.zip I.a))

end LineDeriv

section SpecDeriv

variable {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}

private theorem OneStep_hasDerivAt_specR (hH : H.IsHermitian) {E v : ℝ}
    (hv : (zt E v).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gres H (zt E s) σ)
      (-(Gres H (zt E v) σ * OneStep_Dsp d L W E σ * Gres H (zt E v) σ)) v := by
  have := OneStep_hasDerivAt_Gsig (hasDerivAt_const v H) (hasDerivAt_spectralZ E v) hH hv σ
  refine this.congr_deriv ?_
  cases σ <;> simp [OneStep_Dsp, spectralMSign]

private theorem OneStep_hasDerivAt_spec0 (hH : H.IsHermitian) {E v : ℝ}
    (hv : (zt E v).im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    HasDerivAt (fun s : ℝ => loopL d L W H (zt E s) I)
      (OneStep_J1 H (zt E v) (OneStep_Dsp d L W E) I) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w0 (Rt := fun s σ => Gres H (zt E s) σ)
      (D := OneStep_Dsp d L W E) (Ei := Eblk d L W) (OneStep_hasDerivAt_specR hH hv) (I.σ.zip I.a))

private theorem OneStep_hasDerivAt_spec1 (hH : H.IsHermitian) {E v : ℝ}
    (hv : (zt E v).im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    HasDerivAt (fun s : ℝ => OneStep_J1 H (zt E s) (OneStep_Dsp d L W E) I)
      (OneStep_J2 H (zt E v) (OneStep_Dsp d L W E) I) v :=
  OneStep_hasDerivAt_trace
    (OneStep_hasDerivAt_w1 (Rt := fun s σ => Gres H (zt E s) σ)
      (D := OneStep_Dsp d L W E) (Ei := Eblk d L W) (OneStep_hasDerivAt_specR hH hv) (I.σ.zip I.a))

end SpecDeriv

end Loop

/-! ## 3. Norm and Lipschitz bounds for the jets of the loop functional -/

section LoopBounds

variable {d L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem OneStep_zip_length {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    (I.σ.zip I.a).length = I.length := by
  rw [List.length_zip]
  simp only [Loop.LoopIdx.WF] at hwf
  rw [hwf, min_self]
  rfl

private theorem OneStep_data {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    OneStep_Data (fun σ => Gres H z σ) D (Eblk d L W) η⁻¹ b :=
  ⟨by positivity, hb, fun σ => norm_Gsig_le_inv_eta hH hη hz σ, hD,
    fun a => OneStep_norm_Eblk_le_one a⟩

/-- `‖J1‖ ≤ N k K^{k+1} b`. -/
private theorem OneStep_norm_J1_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    ‖OneStep_J1 H z D I‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * η⁻¹ ^ (I.length + 1) * b) := by
  have h := OneStep_norm_w1_le (OneStep_data hH hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  exact (norm_matrix_trace_le_card_mul _).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2‖ ≤ N k (k+1) K^{k+2} b²`. -/
private theorem OneStep_norm_J2_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    ‖OneStep_J2 H z D I‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * η⁻¹ ^ (I.length + 2) * b ^ 2) := by
  have h := OneStep_norm_w2_le (OneStep_data hH hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  exact (norm_matrix_trace_le_card_mul _).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

private theorem OneStep_diff {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) :
    OneStep_Diff (fun σ => Gres H₁ z σ) (fun σ => Gres H₂ z σ) D (Eblk d L W) η⁻¹ b ‖H₁ - H₂‖ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  refine ⟨OneStep_data hH₁ hη hz hb hD, fun σ => norm_Gsig_le_inv_eta hH₂ hη hz σ,
    norm_nonneg _, fun σ => ?_⟩
  refine (OneStep_norm_Gsig_sub_le hH₁ hH₂ hzim σ).trans ?_
  have h1 : |z.im|⁻¹ ≤ η⁻¹ := inv_anti₀ hη hz
  have h2 : |z.im|⁻¹ ^ 2 ≤ η⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- `‖J1(H₁) - J1(H₂)‖ ≤ N k (k+1) K^{k+2} b ‖H₁ - H₂‖`. -/
private theorem OneStep_norm_J1_sub_le {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    ‖OneStep_J1 H₁ z D I - OneStep_J1 H₂ z D I‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * η⁻¹ ^ (I.length + 2) * b * ‖H₁ - H₂‖) := by
  have h := OneStep_norm_w1_sub_le (OneStep_diff hH₁ hH₂ hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  have := norm_matrix_trace_le_card_mul
    (OneStep_w1 (fun σ => Gres H₁ z σ) D (Eblk d L W) (I.σ.zip I.a)
      - OneStep_w1 (fun σ => Gres H₂ z σ) D (Eblk d L W) (I.σ.zip I.a))
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- `‖J2(H₁) - J2(H₂)‖ ≤ N k (k+1) (k+2) K^{k+3} b² ‖H₁ - H₂‖`. -/
private theorem OneStep_norm_J2_sub_le {H₁ H₂ : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|)
    {D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ σ, ‖D σ‖ ≤ b) {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    ‖OneStep_J2 H₁ z D I - OneStep_J2 H₂ z D I‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3) * b ^ 2 *
          ‖H₁ - H₂‖) := by
  have h := OneStep_norm_w2_sub_le (OneStep_diff hH₁ hH₂ hη hz hb hD) (I.σ.zip I.a)
  rw [OneStep_zip_length hwf] at h
  have := norm_matrix_trace_le_card_mul
    (OneStep_w2 (fun σ => Gres H₁ z σ) D (Eblk d L W) (I.σ.zip I.a)
      - OneStep_w2 (fun σ => Gres H₂ z σ) D (Eblk d L W) (I.σ.zip I.a))
  rw [Matrix.trace_sub] at this
  exact this.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

end LoopBounds

/-! ## 4. Counts: `Σ_c gvar_c ≤ 2N`, and `‖X‖ ≤ 2 Σ_c |ω_c|` -/

section Counts

private theorem OneStep_norm_single_le {n : Type*} [Fintype n] [DecidableEq n] (i j : n)
    (a : ℂ) : ‖(Matrix.single i j a : Matrix n n ℂ)‖ ≤ ‖a‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => ?_
  have h : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.single i j a) v
      = EuclideanSpace.single i (a * v j) := by
    ext k
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.single_mulVec, Function.update_apply]
  rw [h, EuclideanSpace.single, PiLp.norm_single, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)

/-- The `ℓ²` operator norm is at most the sum of the moduli of the entries. -/
private theorem OneStep_norm_le_sum_entries {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => OneStep_norm_single_le i j _))

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W]

private theorem OneStep_norm_Xentry_le (ω : Ω d L W) (i j : Idx d L W) :
    ‖Xentry d L W ω i j‖ ≤
      (|ω (i, j, true)| + |ω (i, j, false)|) + (|ω (j, i, true)| + |ω (j, i, false)|) := by
  have h1 := abs_nonneg (ω (i, j, true))
  have h2 := abs_nonneg (ω (i, j, false))
  have h3 := abs_nonneg (ω (j, i, true))
  have h4 := abs_nonneg (ω (j, i, false))
  unfold Xentry
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

private theorem OneStep_sum_coord (f : CoordF d L W → ℝ) :
    ∑ c : CoordF d L W, f c = ∑ i : Idx d L W, ∑ j : Idx d L W, (f (i, j, true) + f (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]

/-- `‖X‖ ≤ 2 Σ_c |ω_c|`, in block coordinates. -/
private theorem OneStep_norm_blockMat_Xmat_le (ω : Ω d L W) :
    ‖blockMat d L W (Xmat d L W ω)‖ ≤ 2 * ∑ c : CoordF d L W, |ω c| := by
  refine (OneStep_norm_le_sum_entries _).trans ?_
  have hent : ∑ p : Vtx d L W, ∑ q : Vtx d L W, ‖blockMat d L W (Xmat d L W ω) p q‖
      = ∑ i : Idx d L W, ∑ j : Idx d L W, ‖Xentry d L W ω i j‖ := by
    rw [← Equiv.sum_comp (splitEquiv d L W).symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp (splitEquiv d L W).symm]
    rfl
  rw [hent, OneStep_sum_coord]
  have hswap : ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (j, i, true)| + |ω (j, i, false)|)
      = ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (i, j, true)| + |ω (i, j, false)|) :=
    Finset.sum_comm
  calc ∑ i : Idx d L W, ∑ j : Idx d L W, ‖Xentry d L W ω i j‖
      ≤ ∑ i : Idx d L W, ∑ j : Idx d L W, ((|ω (i, j, true)| + |ω (i, j, false)|)
          + (|ω (j, i, true)| + |ω (j, i, false)|)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => OneStep_norm_Xentry_le ω i j
    _ = 2 * ∑ i : Idx d L W, ∑ j : Idx d L W, (|ω (i, j, true)| + |ω (i, j, false)|) := by
        simp only [Finset.sum_add_distrib] at hswap ⊢
        linarith [hswap]

private theorem OneStep_sbKernelR_le_one (x : Zd d L) : sbKernelR d L g x ≤ 1 :=
  (Finset.single_le_sum (fun y _ => sbKernelR_nonneg d L g y) (Finset.mem_univ x)).trans
    (OneStep_sum_sbKernelR_le g)

omit [NeZero L] in
private theorem OneStep_inv_pow_le_one : ((W : ℝ) ^ d)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀
    (one_le_pow₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)))

private theorem OneStep_svar_le_one (i j : Idx d L W) : svarF d L W g i j ≤ 1 := by
  unfold svarF
  have h0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have h2 : SBR d L g (split d L W i).1 (split d L W j).1 ≤ 1 :=
    OneStep_sbKernelR_le_one g _
  have h3 : 0 ≤ SBR d L g (split d L W i).1 (split d L W j).1 := sbKernelR_nonneg d L g _
  calc ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1 ≤ 1 * 1 :=
        mul_le_mul OneStep_inv_pow_le_one h2 h3 zero_le_one
    _ = 1 := one_mul 1

private theorem OneStep_gvar_le_svar (c : CoordF d L W) :
    (gvarF d L W g c : ℝ) ≤ svarF d L W g c.1 c.2.1 := by
  change (if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2) ≤ _
  have := svarF_nonneg d L W g c.1 c.2.1
  split_ifs <;> linarith

private theorem OneStep_gvar_le_one (c : CoordF d L W) : (gvarF d L W g c : ℝ) ≤ 1 :=
  (OneStep_gvar_le_svar g c).trans (OneStep_svar_le_one g _ _)

/-- The row sums of `svarF` are at most `1`, for every `L`, `W ≥ 1` and every real `g`
(`OneStep:859`: `Σ_j S_ij = W^d · W^{-d} Σ_b S^(B)_{ab}`). -/
private theorem OneStep_sum_svar_row (i : Idx d L W) : ∑ j : Idx d L W, svarF d L W g i j ≤ 1 := by
  have h1 : ∑ j : Idx d L W, svarF d L W g i j =
      ∑ p : Vtx d L W, ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 p.1 :=
    Fintype.sum_equiv (splitEquiv d L W) _ _ fun j => rfl
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  have h2 : ∑ x : Zd d L, SBR d L g (split d L W i).1 x ≤ 1 := by
    simp only [SBR, Matrix.of_apply]
    exact le_trans (le_of_eq (Fintype.sum_equiv (Equiv.subLeft (split d L W i).1)
      (fun x => sbKernelR d L g ((split d L W i).1 - x)) (fun x => sbKernelR d L g x)
      (fun _ => rfl))) (OneStep_sum_sbKernelR_le g)
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_trans (le_of_eq ?_) h2
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  field_simp

/-- `Σ_c gvar_c ≤ 2 N`, `N = |Idx|`. -/
private theorem OneStep_sum_gvar_le :
    ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) ≤ 2 * (Fintype.card (Idx d L W) : ℝ) := by
  rw [OneStep_sum_coord]
  calc ∑ i : Idx d L W, ∑ j : Idx d L W,
        ((gvarF d L W g (i, j, true) : ℝ) + (gvarF d L W g (i, j, false) : ℝ))
      ≤ ∑ i : Idx d L W, ∑ j : Idx d L W, 2 * svarF d L W g i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have h1 := OneStep_gvar_le_svar g (d := d) (L := L) (W := W) (i, j, true)
          have h2 := OneStep_gvar_le_svar g (d := d) (L := L) (W := W) (i, j, false)
          simp only at h1 h2
          linarith
    _ = 2 * ∑ i : Idx d L W, ∑ j : Idx d L W, svarF d L W g i j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 2 * ∑ _i : Idx d L W, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => OneStep_sum_svar_row g i)
          zero_le_two
    _ = 2 * (Fintype.card (Idx d L W) : ℝ) := by simp

/-- `|Idx| = (W L)^d`. -/
private theorem OneStep_card_Idx : (Fintype.card (Idx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
  rw [card_Idx]

/-! ### First absolute moments of the Gaussian coordinates -/

private theorem OneStep_integrable_abs_coord (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => |ω c|) (PF d L W g) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (integrable_sq_coord d L W g c))
    (continuous_abs.comp (continuous_apply c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]

private theorem OneStep_integral_abs_coord_le (c : CoordF d L W) :
    ∫ ω : Ω d L W, |ω c| ∂(PF d L W g) ≤ 1 := by
  have hint : Integrable (fun ω : Ω d L W => (1 + (ω c) ^ 2) / 2) (PF d L W g) :=
    ((integrable_const (1 : ℝ)).add (integrable_sq_coord d L W g c)).div_const 2
  have hmono : ∫ ω : Ω d L W, |ω c| ∂(PF d L W g) ≤ ∫ ω : Ω d L W, (1 + (ω c) ^ 2) / 2 ∂(PF d L W g) := by
    refine integral_mono (OneStep_integrable_abs_coord g c) hint fun ω => ?_
    nlinarith [sq_nonneg (|ω c| - 1), sq_abs (ω c)]
  refine hmono.trans ?_
  rw [integral_div, integral_add (integrable_const _) (integrable_sq_coord d L W g c),
    integral_sq_coord d L W g c]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have := OneStep_gvar_le_one g c
  linarith

private theorem OneStep_continuous_blockMat :
    Continuous (blockMat d L W : Matrix (Idx d L W) (Idx d L W) ℂ →
      Matrix (Vtx d L W) (Vtx d L W) ℂ) :=
  continuous_id.matrix_submatrix _ _

private theorem OneStep_integrable_sum_abs :
    Integrable (fun ω : Ω d L W => 2 * ∑ c : CoordF d L W, |ω c|) (PF d L W g) :=
  (integrable_finsetSum _ fun c _ => OneStep_integrable_abs_coord g c).const_mul 2

private theorem OneStep_integrable_normX :
    Integrable (fun ω : Ω d L W => ‖blockMat d L W (Xmat d L W ω)‖) (PF d L W g) := by
  refine Integrable.mono' (OneStep_integrable_sum_abs g) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (continuous_norm.comp
      (OneStep_continuous_blockMat.comp (continuous_Xmat d L W))).aestronglyMeasurable
  · rw [norm_norm]
    exact OneStep_norm_blockMat_Xmat_le ω

/-- `E ‖X‖ ≤ 4 N²` (in block coordinates), `N = (W L)^d`. -/
private theorem OneStep_integral_normX_le :
    ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(PF d L W g) ≤ 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 := by
  calc ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(PF d L W g)
      ≤ ∫ ω : Ω d L W, 2 * ∑ c : CoordF d L W, |ω c| ∂(PF d L W g) :=
        integral_mono (OneStep_integrable_normX g) (OneStep_integrable_sum_abs g)
          fun ω => OneStep_norm_blockMat_Xmat_le ω
    _ = 2 * ∑ c : CoordF d L W, ∫ ω : Ω d L W, |ω c| ∂(PF d L W g) := by
        rw [integral_const_mul, integral_finsetSum _ fun c _ => OneStep_integrable_abs_coord g c]
    _ ≤ 2 * ∑ _c : CoordF d L W, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => OneStep_integral_abs_coord_le g c)
          zero_le_two
    _ = 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        have : Fintype.card (CoordF d L W) = 2 * (Fintype.card (Idx d L W)) ^ 2 := by
          simp [CoordF, Fintype.card_prod, Fintype.card_bool]
          ring
        rw [this]
        push_cast
        rw [OneStep_card_Idx]
        push_cast
        ring

end Counts

/-! ## 5. The derivative of `x ↦ E f(M + x X)` by Stein's identity -/

section Fine

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W]

private theorem OneStep_blockMat_add_smul (A C : Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℂ) :
    blockMat d L W (A + y • C) = blockMat d L W A + y • blockMat d L W C := by
  ext p q
  simp [blockMat]

/-- The reindexed sample matrix `M + x X_ω`. -/
private def OneStep_Hs (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : ℝ) (ω : Ω d L W) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  blockMat d L W (M + (x : ℂ) • Xmat d L W ω)

private theorem OneStep_Hs_eq (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : ℝ) (ω : Ω d L W) :
    OneStep_Hs M x ω = blockMat d L W M + (x : ℂ) • blockMat d L W (Xmat d L W ω) :=
  OneStep_blockMat_add_smul _ _ _

private theorem OneStep_Hs_herm {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (x : ℝ)
    (ω : Ω d L W) : (OneStep_Hs M x ω).IsHermitian :=
  (OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d L W ω) x).submatrix _

private theorem OneStep_continuous_Hs (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : ℝ) :
    Continuous (OneStep_Hs M x) :=
  OneStep_continuous_blockMat.comp
    (continuous_const.add ((continuous_Xmat d L W).const_smul (x : ℂ)))

private theorem OneStep_Hs_update {M : Matrix (Idx d L W) (Idx d L W) ℂ} (x : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) (t : ℝ) :
    OneStep_Hs M x (Function.update ω c t) = OneStep_Hs M x ω
      + ((x * (t - ω c) : ℝ) : ℂ) • blockMat d L W (coordinateMatrix d L W c) := by
  rw [OneStep_Hs, OneStep_Hs, Xmat_update]
  ext p q
  simp only [blockMat, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private theorem OneStep_continuous_Gsig {V : Type*} [TopologicalSpace V]
    {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ} (hf : Continuous f)
    (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun v => Gres (f v) z σ := by
  cases σ
  · exact continuous_green_of_isHermitian hf hh (by simpa using hz)
  · exact continuous_green_of_isHermitian hf hh hz

section Cont

variable {V : Type*} [TopologicalSpace V] {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ}
  (hf : Continuous f) (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  (I : Loop.LoopIdx (Zd d L)) (D : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ)
include hf hh hz

private theorem OneStep_continuous_gloop : Continuous fun v => loopL d L W (f v) z I :=
  (continuous_matrixTrace d L W).comp
    (OneStep_continuous_w0 (fun σ => OneStep_continuous_Gsig hf hh hz σ) _)

private theorem OneStep_continuous_J1 : Continuous fun v => OneStep_J1 (f v) z D I :=
  (continuous_matrixTrace d L W).comp
    (OneStep_continuous_w1 (fun σ => OneStep_continuous_Gsig hf hh hz σ) _)

private theorem OneStep_continuous_J2 : Continuous fun v => OneStep_J2 (f v) z D I :=
  (continuous_matrixTrace d L W).comp
    (OneStep_continuous_w2 (fun σ => OneStep_continuous_Gsig hf hh hz σ) _)

end Cont

/-- Linearity of the first jet in the direction: `X = Σ_c ω_c C_c`. -/
private theorem OneStep_J1_Xmat (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) (ω : Ω d L W) :
    OneStep_J1 H z (fun _ => blockMat d L W (Xmat d L W ω)) I
      = ∑ c : CoordF d L W, (ω c : ℂ) *
          OneStep_J1 H z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I := by
  have hX : (fun _ : Bool => blockMat d L W (Xmat d L W ω))
      = ∑ c : CoordF d L W, (ω c) • (fun _ : Bool => blockMat d L W (coordinateMatrix d L W c)) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply]
    ext p q
    rw [Xmat_eq_sum_coordinates]
    simp [blockMat, Matrix.sum_apply]
  have hlin := map_sum (OneStep_w1Lin (fun σ => Gres H z σ) (Eblk d L W) (I.σ.zip I.a))
    (fun c : CoordF d L W => (ω c) • (fun _ : Bool => blockMat d L W (coordinateMatrix d L W c)))
    Finset.univ
  simp only [map_smul] at hlin
  unfold OneStep_J1
  rw [hX]
  change Matrix.trace ((OneStep_w1Lin (fun σ => Gres H z σ) (Eblk d L W) (I.σ.zip I.a)) _) = _
  rw [hlin, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.trace_smul, Complex.real_smul]
  rfl

/-- A Gaussian coordinate times a bounded continuous observable is integrable. -/
private theorem OneStep_integrable_coord_mul (c : CoordF d L W) {φ : Ω d L W → ℂ}
    (hg : Continuous φ) {C : ℝ} (hb : ∀ ω, ‖φ ω‖ ≤ C) :
    Integrable (fun ω : Ω d L W => (ω c : ℂ) * φ ω) (PF d L W g) := by
  have hf : AEMeasurable (fun ω : Ω d L W => ω c) (PF d L W g) := (measurable_pi_apply c).aemeasurable
  have hg' : Integrable (fun x : ℝ => x) ((PF d L W g).map fun ω => ω c) := by
    rw [P_map_eval d L W g c]
    exact RBM.integrable_id_gaussianReal (var := gvarF d L W g c)
  have hcoord : Integrable (fun ω : Ω d L W => ω c) (PF d L W g) :=
    (integrable_map_measure hg'.aestronglyMeasurable hf).1 hg'
  have h := hcoord.ofReal.bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa [Complex.real_smul, mul_comm] using h

section SteinStep

variable {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
  {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF)
include hM hz hwf

/-- The coordinate Stein identity, for the first jet along the coordinate direction. -/
private theorem OneStep_stein_coord (x : ℝ) (c : CoordF d L W) :
    ∫ ω : Ω d L W, (ω c : ℂ) *
        OneStep_J1 (OneStep_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g)
      = ((gvarF d L W g c : ℝ) : ℂ) * ((x : ℂ) * ∫ ω : Ω d L W,
        OneStep_J2 (OneStep_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
    := by
  set Cb := blockMat d L W (coordinateMatrix d L W c) with hCb
  have hCh : Cb.IsHermitian := (coordinateMatrix_isHermitian d L W c).submatrix _
  set φ : Ω d L W → ℂ := fun ω => OneStep_J1 (OneStep_Hs M x ω) z (fun _ => Cb) I with hg
  set φ' : Ω d L W → ℂ := fun ω => (x : ℂ) * OneStep_J2 (OneStep_Hs M x ω) z (fun _ => Cb) I
    with hg'
  have hgc : Continuous φ :=
    OneStep_continuous_J1 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz I _
  have hg'c : Continuous φ' :=
    continuous_const.mul
      (OneStep_continuous_J2 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz I _)
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hgb : ∃ C : ℝ, ∀ ω, ‖φ ω‖ ≤ C := ⟨_, fun ω =>
    OneStep_norm_J1_le (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb) (fun _ => le_rfl) hwf⟩
  have hg'b : ∃ C : ℝ, ∀ ω, ‖φ' ω‖ ≤ C := ⟨|x| * _, fun ω => by
    rw [hg', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (OneStep_norm_J2_le (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg Cb)
        (fun _ => le_rfl) hwf) (abs_nonneg _)⟩
  have hderiv : ∀ ω, HasDerivAt (fun t : ℝ => φ (Function.update ω c t)) (φ' ω) (ω c) := by
    intro ω
    have hAh := OneStep_Hs_herm hM x ω
    have hφ := OneStep_hasDerivAt_line1 hAh hCh hz I (x * (ω c - ω c))
    have hh : HasDerivAt (fun t : ℝ => x * (t - ω c)) x (ω c) := by
      simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul x
    have hcomp := hφ.scomp (ω c) hh
    have hfun : (fun t : ℝ => φ (Function.update ω c t)) =
        ((fun s : ℝ => OneStep_J1 (OneStep_Hs M x ω + (s : ℂ) • Cb) z (fun _ => Cb) I) ∘
          fun t : ℝ => x * (t - ω c)) := by
      funext t
      simp only [Function.comp, hg, OneStep_Hs_update, hCb]
    rw [hfun]
    refine hcomp.congr_deriv ?_
    simp [hg']
  have h := GaussianProduct.stein (gvarF d L W g) c φ φ' hgc hg'c hderiv hgb hg'b
  have hlaw : PF d L W g = GaussianProduct.law (gvarF d L W g) := rfl
  rw [← hlaw] at h
  simp only [Complex.real_smul] at h
  rw [h, hg', integral_const_mul]

/-- **The derivative of `x ↦ E f(M + x X)`**: `x Σ_c gvar_c E ∂²_c f(M + x X)`, by Stein. -/
private theorem OneStep_hasDerivAt_F (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ ω : Ω d L W, loopL d L W (OneStep_Hs M y ω) z I ∂(PF d L W g))
      ((x : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M x ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g)) x := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hcontgl : ∀ y : ℝ, Continuous fun ω : Ω d L W => loopL d L W (OneStep_Hs M y ω) z I :=
    fun y => OneStep_continuous_gloop (OneStep_continuous_Hs M y) (OneStep_Hs_herm hM y) hz I
  have hint : ∀ y : ℝ, Integrable (fun ω : Ω d L W => loopL d L W (OneStep_Hs M y ω) z I) (PF d L W g) :=
    fun y => Integrable.of_bound (hcontgl y).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude d L W (OneStep_Hs_herm hM y ω) hη le_rfl I hwf)
  have hJc : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      OneStep_J1 (OneStep_Hs M x ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I :=
    fun c => OneStep_continuous_J1 (OneStep_continuous_Hs M x) (OneStep_Hs_herm hM x) hz I _
  have hF'cont : Continuous fun ω : Ω d L W =>
      OneStep_J1 (OneStep_Hs M x ω) z (fun _ => blockMat d L W (Xmat d L W ω)) I := by
    simp only [OneStep_J1_Xmat]
    exact continuous_finsetSum _ fun c _ =>
      (Complex.continuous_ofReal.comp (continuous_apply c)).mul (hJc c)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := PF d L W g)
    (s := Set.univ) (x₀ := x)
    (F := fun y ω => loopL d L W (OneStep_Hs M y ω) z I)
    (F' := fun y ω => OneStep_J1 (OneStep_Hs M y ω) z (fun _ => blockMat d L W (Xmat d L W ω)) I)
    (bound := fun ω => ((Fintype.card (Vtx d L W) : ℝ) *
      ((I.length : ℝ) * |z.im|⁻¹ ^ (I.length + 1))) * ‖blockMat d L W (Xmat d L W ω)‖)
    Filter.univ_mem (Filter.Eventually.of_forall fun y => (hcontgl y).aestronglyMeasurable)
    (hint x) hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω y _ =>
      (OneStep_norm_J1_le (OneStep_Hs_herm hM y ω) hη le_rfl (norm_nonneg _) (fun _ => le_rfl)
        hwf).trans (le_of_eq (by ring)))
    ((OneStep_integrable_normX g).const_mul _)
    (Filter.Eventually.of_forall fun ω y _ => by
      have hXb : (blockMat d L W (Xmat d L W ω)).IsHermitian := (Xmat_isHermitian d L W ω).submatrix _
      have := OneStep_hasDerivAt_line0 hMb hXb hz I y
      simpa only [OneStep_Hs_eq] using this)
  refine hD.congr_deriv ?_
  simp only [OneStep_J1_Xmat]
  rw [integral_finsetSum _ fun c _ => OneStep_integrable_coord_mul g c (hJc c)
    (fun ω => OneStep_norm_J1_le (OneStep_Hs_herm hM x ω) hη le_rfl (norm_nonneg _)
      (fun _ => le_rfl) hwf)]
  simp_rw [OneStep_stein_coord g hM hz hwf x]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

end SteinStep

end Fine

/-! ## 6. The space step: `E f(M + τ X) - f(M) - τ² g(M)` -/

section SpaceStep

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W]

private theorem OneStep_card_Block :
    (Fintype.card (Vtx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
  rw [card_BlockIndex, mul_comm]

/-- The coordinate directions have norm at most `2` (in block coordinates). -/
private theorem OneStep_norm_Cb_le (c : CoordF d L W) : ‖blockMat d L W (coordinateMatrix d L W c)‖ ≤ 2 := by
  have h := OneStep_norm_blockMat_Xmat_le (d := d) (L := L) (W := W) (Pi.single c (1 : ℝ))
  have h1 : ∑ c' : CoordF d L W, |(Pi.single c (1 : ℝ) : CoordF d L W → ℝ) c'| = 1 := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ c) h
  rw [h1] at h
  simpa [coordinateMatrix] using h

/-- The `g`-part: `g_u(M) = ½ Σ_c gvar_c ∂²_c f(M)`. -/
private def OneStep_g (z : ℂ) (I : Loop.LoopIdx (Zd d L)) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
    OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I

variable {M : Matrix (Idx d L W) (Idx d L W) ℂ} {z : ℂ} {I : Loop.LoopIdx (Zd d L)}

/-- The Lipschitz estimate of one coordinate second jet along the Gaussian sample. -/
private theorem OneStep_coord_sub_le (hM : M.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) (c : CoordF d L W) (y : ℝ) (ω : Ω d L W) :
    ‖OneStep_J2 (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I‖
      ≤ (((Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4) * |y|) * ‖blockMat d L W (Xmat d L W ω)‖ := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have h := OneStep_norm_J2_sub_le (OneStep_Hs_herm hM y ω) hMb hη hz (D := fun _ =>
    blockMat d L W (coordinateMatrix d L W c)) (b := 2) zero_le_two (fun _ => OneStep_norm_Cb_le c) hwf
  have hd : ‖OneStep_Hs M y ω - blockMat d L W M‖ = |y| * ‖blockMat d L W (Xmat d L W ω)‖ := by
    rw [OneStep_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [hd] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- The key size estimate: the derivative of `ψ(y) = F(y) - F(0) - y² g(M)` is `O(y²)`. -/
private theorem OneStep_psi_deriv_le (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {y : ℝ} (hy : 0 ≤ y) :
    ‖(y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g)
      - ((2 * y : ℝ) : ℂ) * OneStep_g g z I M‖
      ≤ (32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) * y ^ 2 := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  set C₃ : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (I.length + 2) * η⁻¹ ^ (I.length + 3)) * 4 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  have hcont : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      OneStep_J2 (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I :=
    fun c => OneStep_continuous_J2 (OneStep_continuous_Hs M y) (OneStep_Hs_herm hM y) hz' I _
  have hint : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W =>
      OneStep_J2 (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) (PF d L W g) :=
    fun c => Integrable.of_bound (hcont c).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        OneStep_norm_J2_le (OneStep_Hs_herm hM y ω) hη hz (norm_nonneg _) (fun _ => le_rfl) hwf)
  -- one coordinate
  have hone : ∀ c : CoordF d L W,
      ‖(∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I‖
      ≤ (C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
    intro c
    have hsub : (∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I
        = ∫ ω : Ω d L W, (OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I
          - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) ∂(PF d L W g) := by
      rw [integral_sub (hint c) (integrable_const _)]
      simp
    rw [hsub]
    refine (norm_integral_le_of_norm_le (((OneStep_integrable_normX g).const_mul (C₃ * |y|)))
      (Filter.Eventually.of_forall fun ω =>
        OneStep_coord_sub_le hM hη hz hwf c y ω)).trans ?_
    rw [integral_const_mul, abs_of_nonneg hy]
    have := OneStep_integral_normX_le (d := d) (L := L) (W := W) g
    rw [← OneStep_card_Idx] at this
    calc C₃ * y * ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(PF d L W g)
        ≤ C₃ * y * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := rfl
  have hsum : ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) * ∫ ω : Ω d L W, OneStep_J2
        (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g)
      - 2 * OneStep_g g z I M
      = ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) := by
    simp only [OneStep_g, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hmain : (y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) * ∫ ω : Ω d L W, OneStep_J2
        (OneStep_Hs M y ω) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g)
      - ((2 * y : ℝ) : ℂ) * OneStep_g g z I M
      = (y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I) := by
    rw [← hsum]
    push_cast
    ring
  rw [hmain, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
  have hsn : ‖∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I)‖
      ≤ (2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : CoordF d L W, ‖((gvarF d L W g c : ℝ) : ℂ) *
          ((∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
            (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
          - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I)‖
        ≤ ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun c _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gvarF d L W g c).coe_nonneg]
            exact mul_le_mul_of_nonneg_left (hone c) (gvarF d L W g c).coe_nonneg
      _ = (∑ c : CoordF d L W, (gvarF d L W g c : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right (OneStep_sum_gvar_le g) (by positivity)
  calc y * ‖∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ((∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g))
        - OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W (coordinateMatrix d L W c)) I)‖
      ≤ y * ((2 * (Fintype.card (Idx d L W) : ℝ)) * ((C₃ * y) * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hsn hy
    _ = _ := by rw [hC₃]; ring

/-- **The space step** (port of RBM1D `oneStep_error_le`, with Stein in place of the
generator identity): `‖E f(M + τ X) - f(M) - τ² g(M)‖ ≤ (Λ'/3) τ³`. -/
private theorem OneStep_space_step (hM : M.IsHermitian) (hz' : z.im ≠ 0) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (hwf : I.WF) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) z I ∂(PF d L W g)) - loopL d L W (blockMat d L W M) z I
        - ((τ ^ 2 : ℝ) : ℂ) * OneStep_g g z I M‖
      ≤ ((32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
          ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3))) / 3)
        * τ ^ 3 := by
  set Λ : ℝ := 32 * (Fintype.card (Idx d L W) : ℝ) ^ 3 * (Fintype.card (Vtx d L W) : ℝ) *
    ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * η⁻¹ ^ (I.length + 3)) with hΛ
  set F : ℝ → ℂ := fun y => ∫ ω : Ω d L W, loopL d L W (OneStep_Hs M y ω) z I ∂(PF d L W g) with hF
  have hF0 : F 0 = loopL d L W (blockMat d L W M) z I := by
    simp [hF, OneStep_Hs]
  set ψ : ℝ → ℂ := fun y => F y - F 0 - ((y ^ 2 : ℝ) : ℂ) * OneStep_g g z I M with hψ
  set ψ' : ℝ → ℂ := fun y => (y : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        ∫ ω : Ω d L W, OneStep_J2 (OneStep_Hs M y ω) z
          (fun _ => blockMat d L W (coordinateMatrix d L W c)) I ∂(PF d L W g)
      - ((2 * y : ℝ) : ℂ) * OneStep_g g z I M with hψ'
  have hd : ∀ y : ℝ, HasDerivAt ψ (ψ' y) y := by
    intro y
    have h1 := ((OneStep_hasDerivAt_F g hM hz' hwf y).sub_const (F 0)).sub
      ((((hasDerivAt_pow 2 y).ofReal_comp)).mul_const (OneStep_g g z I M))
    refine h1.congr_deriv ?_
    simp only [hψ']
    push_cast
    ring
  have hcont : ContinuousOn ψ (Set.Icc 0 τ) := fun y _ => (hd y).continuousAt.continuousWithinAt
  have hB : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Λ / 3 * y ^ 3) (Λ * y ^ 2) y := by
    intro y
    refine ((hasDerivAt_pow 3 y).const_mul (Λ / 3)).congr_deriv ?_
    push_cast
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (f' := ψ') (a := 0)
    (b := τ) hcont (fun y _ => (hd y).hasDerivWithinAt)
    (by simp [hψ]) hB
    (fun y hy => OneStep_psi_deriv_le g hM hz' hη hz hwf hy.1)
  have := key (x := τ) ⟨hτ, le_rfl⟩
  simp only [hψ] at this
  rw [hF0] at this
  exact this

end SpaceStep

/-! ## 7. The time step, the closure of the constant, and the pin -/

section TimeStep

/-- Second-order Taylor bound (the fencing lemma twice). -/
private theorem OneStep_taylor2 {f f₁ f₂ : ℝ → ℂ} {a b B : ℝ} (hab : a ≤ b)
    (h1 : ∀ x ∈ Set.Icc a b, HasDerivAt f (f₁ x) x)
    (h2 : ∀ x ∈ Set.Icc a b, HasDerivAt f₁ (f₂ x) x) (hB : ∀ x ∈ Set.Icc a b, ‖f₂ x‖ ≤ B) :
    ‖f b - f a - ((b - a : ℝ) : ℂ) * f₁ a‖ ≤ B * (b - a) ^ 2 / 2 := by
  have hc1 : ContinuousOn f₁ (Set.Icc a b) := fun x hx => (h2 x hx).continuousAt.continuousWithinAt
  have hs1 := norm_image_sub_le_of_norm_deriv_right_le_segment (f := f₁) (f' := f₂) (C := B) hc1
    (fun x hx => (h2 x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (fun x hx => hB x ⟨hx.1, hx.2.le⟩)
  set ψ : ℝ → ℂ := fun x => f x - f a - ((x - a : ℝ) : ℂ) * f₁ a with hψ
  have hd : ∀ x ∈ Set.Icc a b, HasDerivAt ψ (f₁ x - f₁ a) x := by
    intro x hx
    have h := ((h1 x hx).sub_const (f a)).sub
      ((((hasDerivAt_id x).sub_const a).ofReal_comp).mul_const (f₁ a))
    refine h.congr_deriv ?_
    simp
  have hB' : ∀ x : ℝ, HasDerivAt (fun x : ℝ => B * (x - a) ^ 2 / 2) (B * (x - a)) x := by
    intro x
    refine ((((hasDerivAt_id x).sub_const a).pow 2).const_mul B |>.div_const 2).congr_deriv ?_
    simp
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ)
    (f' := fun x => f₁ x - f₁ a) (a := a) (b := b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (by simp [hψ]) hB'
    (fun x hx => by simpa [mul_comm] using hs1 x ⟨hx.1, hx.2.le⟩)
  exact key ⟨hab, le_rfl⟩

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem OneStep_norm_Dsp_le {E : ℝ} (hE : |E| < 2) (σ : Bool) :
    ‖OneStep_Dsp d L W E σ‖ ≤ 1 := by
  have hm : ‖spectralMSign E σ‖ = 1 := by
    cases σ <;> simp [spectralMSign, norm_spectralM hE.le]
  unfold OneStep_Dsp
  rw [norm_smul, hm, one_mul]
  exact OneStep_norm_one_le

private theorem OneStep_eta_pos {E u : ℝ} (hE : |E| < 2) (hu : u < 1) : 0 < etaT E u :=
  mul_pos (by linarith) (spectralM_im_pos hE)

/-- **The time step**: Taylor expansion of `v ↦ f_v(A)` at fixed `A`. -/
private theorem OneStep_time_step {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {E u Δ : ℝ} (hE : |E| < 2) (hΔ : 0 ≤ Δ) (hu1 : u + Δ < 1) {I : Loop.LoopIdx (Zd d L)} (hwf : I.WF) :
    ‖loopL d L W (blockMat d L W A) (zt E (u + Δ)) I - loopL d L W (blockMat d L W A) (zt E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W A) (zt E u) (OneStep_Dsp d L W E) I‖
      ≤ ((Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
          (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * Δ ^ 2 / 2 := by
  have hAb : (blockMat d L W A).IsHermitian := hA.submatrix _
  have hη := OneStep_eta_pos hE hu1
  have hv : ∀ v ∈ Set.Icc u (u + Δ), (zt E v).im ≠ 0 := fun v hv => by
    rw [spectralZ_im]
    exact (mul_pos (by linarith [hv.2]) (spectralM_im_pos hE)).ne'
  have hvη : ∀ v ∈ Set.Icc u (u + Δ), etaT E (u + Δ) ≤ |(zt E v).im| :=
    fun v hv => spectralZ_im_gap hE hu1 hv
  have h := OneStep_taylor2 (f := fun v => loopL d L W (blockMat d L W A) (zt E v) I)
    (f₁ := fun v => OneStep_J1 (blockMat d L W A) (zt E v) (OneStep_Dsp d L W E) I)
    (f₂ := fun v => OneStep_J2 (blockMat d L W A) (zt E v) (OneStep_Dsp d L W E) I)
    (a := u) (b := u + Δ)
    (B := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
      (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) (by linarith)
    (fun v hv' => OneStep_hasDerivAt_spec0 hAb (hv v hv') I)
    (fun v hv' => OneStep_hasDerivAt_spec1 hAb (hv v hv') I)
    (fun v hv' => by
      have := OneStep_norm_J2_le hAb hη (hvη v hv') zero_le_one (D := OneStep_Dsp d L W E)
        (OneStep_norm_Dsp_le hE) hwf
      simpa using this)
  simpa using h

end TimeStep

section Assembly

/-- The closure of the constant: `⅔·16·… ≤ 16 (k+3)⁴ N⁴ (1 + q)^{k+4}` with `q = η⁻¹`. -/
private theorem OneStep_closure (k : ℕ) {N q : ℝ} (hN : 1 ≤ N) (hq : 0 ≤ q) :
    32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
      + (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
    ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * (1 + q) ^ (k + 4) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK : (1 : ℝ) ≤ 1 + q := by linarith
  have hq3 : q ^ (k + 3) ≤ (1 + q) ^ (k + 3) := pow_le_pow_left₀ hq (by linarith) _
  have hq2 : q ^ (k + 2) ≤ (1 + q) ^ (k + 3) :=
    (pow_le_pow_left₀ hq (by linarith) _).trans (pow_le_pow_right₀ hK (by omega))
  have h4 : (1 + q) ^ (k + 3) ≤ (1 + q) ^ (k + 4) := pow_le_pow_right₀ hK (by omega)
  have ha3 : (k : ℝ) * (k + 1) * (k + 2) ≤ ((k : ℝ) + 3) ^ 3 := by nlinarith [sq_nonneg (k : ℝ)]
  have ha2 : (k : ℝ) * (k + 1) ≤ ((k : ℝ) + 3) ^ 3 := by nlinarith [sq_nonneg (k : ℝ)]
  have hN4 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have hN1 : N ≤ N ^ 4 := by nlinarith [pow_le_pow_right₀ hN (show 1 ≤ 4 by norm_num)]
  have hP : 0 ≤ ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3) := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hq0 : 0 ≤ q ^ (k + 3) := by positivity
  have e1 : 32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
      ≤ (32 / 3) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)) := by
    have : (k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3) ≤ ((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3) :=
      mul_le_mul ha3 hq3 hq0 (by positivity)
    calc 32 * N ^ 3 * N * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) / 3
        = (32 / 3) * N ^ 4 * ((k : ℝ) * (k + 1) * (k + 2) * q ^ (k + 3)) := by ring
      _ ≤ (32 / 3) * N ^ 4 * (((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3)) := by gcongr
      _ = _ := by ring
  have e2 : (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
      ≤ (9 / 2) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)) := by
    have h5 : (k : ℝ) * (k + 1) * q ^ (k + 2) ≤ ((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3) :=
      mul_le_mul ha2 hq2 (by positivity) (by positivity)
    have h6 : N * (1 / 2 + 4 * N ^ 2) ≤ (9 / 2) * N ^ 4 := by nlinarith
    calc (N * ((k : ℝ) * (k + 1) * q ^ (k + 2))) * (1 / 2 + 4 * N ^ 2)
        = (N * (1 / 2 + 4 * N ^ 2)) * ((k : ℝ) * (k + 1) * q ^ (k + 2)) := by ring
      _ ≤ ((9 / 2) * N ^ 4) * (((k : ℝ) + 3) ^ 3 * (1 + q) ^ (k + 3)) :=
          mul_le_mul h6 h5 (by positivity) (by positivity)
      _ = _ := by ring
  have e3 : (32 / 3 + 9 / 2) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3))
      ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * (1 + q) ^ (k + 4) := by
    have h7 : ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 3)
        ≤ ((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4) := by gcongr
    have h8 : 3 * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4))
        ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) ^ 3 * N ^ 4 * (1 + q) ^ (k + 4)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [h7, h8]
  linarith

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W]

/-- The mixed second derivative along a coordinate line, as the second jet. -/
private theorem OneStep_deriv_deriv {M C : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (hC : C.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    deriv (deriv (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • C)) z I)) 0
      = OneStep_J2 (blockMat d L W M) z (fun _ => blockMat d L W C) I := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hCb : (blockMat d L W C).IsHermitian := hC.submatrix _
  simp only [OneStep_blockMat_add_smul]
  have h1 : deriv (fun y : ℝ => loopL d L W (blockMat d L W M + (y : ℂ) • blockMat d L W C) z I)
      = fun y : ℝ => OneStep_J1 (blockMat d L W M + (y : ℂ) • blockMat d L W C) z (fun _ => blockMat d L W C) I := by
    funext y
    exact (OneStep_hasDerivAt_line0 hMb hCb hz I y).deriv
  rw [h1]
  simpa using (OneStep_hasDerivAt_line1 hMb hCb hz I 0).deriv

/-- **The one-step expansion with its envelope** (`OneStepEnvelope`, `OneStep:1512`).  The proof
splits the error into the space step at fixed time `u` (`OneStep_space_step`, by Stein) and the time
step at fixed sample (`OneStep_time_step`, by Taylor), and closes the constant with
`OneStep_closure`. -/
theorem oneStepEnvelope : OneStepEnvelope := by
  intro d L W g _ _ E hE I hwf u Δ hu hΔ hu1 M hM
  have hΔ1 : Δ < 1 := by linarith
  set τ : ℝ := Real.sqrt Δ with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg Δ
  have hτ2 : τ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hτΔ : Δ ≤ τ := by nlinarith
  have hτ3 : Δ ^ ((3 : ℝ) / 2) = τ ^ 3 := by
    rw [hτ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΔ]
    norm_num
  have hη : 0 < etaT E (u + Δ) := OneStep_eta_pos hE hu1
  have hzu : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'
  have hηu : etaT E (u + Δ) ≤ |(zt E u).im| :=
    spectralZ_im_gap hE hu1 ⟨le_rfl, by linarith⟩
  have hηv : etaT E (u + Δ) ≤ |(zt E (u + Δ)).im| :=
    spectralZ_im_gap (s := u) hE hu1 ⟨by linarith, le_rfl⟩
  have hzv : (zt E (u + Δ)).im ≠ 0 := fun h => absurd hηv (by rw [h]; simpa using hη)
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  set c₁ : ℝ := (Fintype.card (Vtx d L W) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
    (etaT E (u + Δ))⁻¹ ^ (I.length + 2)) with hc₁
  -- the generator, in the jets
  have hgen : genMat d L W g E u M I = OneStep_g g (zt E u) I M
      + OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I := by
    unfold genMat OneStep_g
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [OneStep_deriv_deriv hM (coordinateMatrix_isHermitian d L W c) hzu I]
    · exact (OneStep_hasDerivAt_spec0 hMb hzu I).deriv
  -- integrability of the sample functionals
  have hint : ∀ v : ℝ, (zt E v).im ≠ 0 → Integrable
      (fun ω : Ω d L W => loopL d L W (OneStep_Hs M τ ω) (zt E v) I) (PF d L W g) := fun v hv => by
    have hv' : 0 < |(zt E v).im| := abs_pos.mpr hv
    exact Integrable.of_bound (OneStep_continuous_gloop (OneStep_continuous_Hs M τ)
      (OneStep_Hs_herm hM τ) hv I).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω =>
        norm_gloop_le_crude d L W (OneStep_Hs_herm hM τ ω) hv' le_rfl I hwf)
  -- the space step
  have hT2 := OneStep_space_step g hM hzu hη hηu hwf hτ0
  -- the time step, integrated
  have hT1 : ‖(∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) (zt E (u + Δ)) I ∂(PF d L W g))
      - (∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) (zt E u) I ∂(PF d L W g))
      - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I‖
      ≤ c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
    have hpt : ∀ ω : Ω d L W, ‖loopL d L W (OneStep_Hs M τ ω) (zt E (u + Δ)) I
        - loopL d L W (OneStep_Hs M τ ω) (zt E u) I
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I‖
        ≤ c₁ * Δ ^ 2 / 2 + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖ := by
      intro ω
      have hA : (M + (τ : ℂ) • Xmat d L W ω).IsHermitian :=
        OneStep_isHermitian_add_realSmul hM (Xmat_isHermitian d L W ω) τ
      have h1 := OneStep_time_step hA hE hΔ hu1 hwf
      have h2 := OneStep_norm_J1_sub_le (OneStep_Hs_herm hM τ ω) hMb hη hηu zero_le_one
        (D := OneStep_Dsp d L W E) (OneStep_norm_Dsp_le hE) hwf
      have hd : ‖OneStep_Hs M τ ω - blockMat d L W M‖ = τ * ‖blockMat d L W (Xmat d L W ω)‖ := by
        rw [OneStep_Hs_eq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hτ0]
      rw [hd] at h2
      have hsplit : loopL d L W (OneStep_Hs M τ ω) (zt E (u + Δ)) I
          - loopL d L W (OneStep_Hs M τ ω) (zt E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I
          = (loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E (u + Δ)) I
            - loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u)
              (OneStep_Dsp d L W E) I)
            + (Δ : ℂ) * (OneStep_J1 (OneStep_Hs M τ ω) (zt E u) (OneStep_Dsp d L W E) I
              - OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I) := by
        simp only [OneStep_Hs]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h3 : ‖(Δ : ℂ) * (OneStep_J1 (OneStep_Hs M τ ω) (zt E u) (OneStep_Dsp d L W E) I
          - OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I)‖
          ≤ Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
        refine mul_le_mul_of_nonneg_left ?_ hΔ
        refine h2.trans (le_of_eq ?_)
        rw [hc₁]
        ring
      have h1' : ‖loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E (u + Δ)) I
            - loopL d L W (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u) I
            - (Δ : ℂ) * OneStep_J1 (blockMat d L W (M + (τ : ℂ) • Xmat d L W ω)) (zt E u)
              (OneStep_Dsp d L W E) I‖ ≤ c₁ * Δ ^ 2 / 2 := h1
      calc _ ≤ c₁ * Δ ^ 2 / 2 + Δ * (c₁ * (τ * ‖blockMat d L W (Xmat d L W ω)‖)) := add_le_add h1' h3
        _ = _ := by ring
    have hsub : (∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) (zt E (u + Δ)) I ∂(PF d L W g))
        - (∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) (zt E u) I ∂(PF d L W g))
        - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I
        = ∫ ω : Ω d L W, (loopL d L W (OneStep_Hs M τ ω) (zt E (u + Δ)) I
          - loopL d L W (OneStep_Hs M τ ω) (zt E u) I
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I)
            ∂(PF d L W g) := by
      have i12 : Integrable (fun ω : Ω d L W => loopL d L W (OneStep_Hs M τ ω) (zt E (u + Δ)) I
          - loopL d L W (OneStep_Hs M τ ω) (zt E u) I) (PF d L W g) :=
        (hint _ hzv).sub (hint _ hzu)
      rw [integral_sub i12 (integrable_const _), integral_sub (hint _ hzv) (hint _ hzu)]
      simp
    rw [hsub]
    have ib : Integrable (fun ω : Ω d L W => c₁ * Δ ^ 2 / 2
        + (c₁ * Δ * τ) * ‖blockMat d L W (Xmat d L W ω)‖) (PF d L W g) :=
      (integrable_const _).add ((OneStep_integrable_normX g).const_mul (c₁ * Δ * τ))
    refine (norm_integral_le_of_norm_le ib (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_const _) ((OneStep_integrable_normX g).const_mul _),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hν := OneStep_integral_normX_le (d := d) (L := L) (W := W) g
    rw [← OneStep_card_Idx] at hν
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
    have hΔ2 : Δ ^ 2 ≤ Δ * τ := by nlinarith
    calc c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * ∫ ω : Ω d L W, ‖blockMat d L W (Xmat d L W ω)‖ ∂(PF d L W g)
        ≤ c₁ * Δ ^ 2 / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ ≤ c₁ * (Δ * τ) / 2 + c₁ * Δ * τ * (4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          gcongr
      _ = c₁ * τ ^ 3 * (1 / 2 + 4 * (Fintype.card (Idx d L W) : ℝ) ^ 2) := by
          rw [← hτ2]
          ring
  -- assembly
  have hLHS : (∫ ω : Ω d L W, loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω))
        (zt E (u + Δ)) I ∂(PF d L W g)) - loopL d L W (blockMat d L W M) (zt E u) I
        - (Δ : ℂ) * genMat d L W g E u M I
      = ((∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) (zt E u) I ∂(PF d L W g))
          - loopL d L W (blockMat d L W M) (zt E u) I
          - ((τ ^ 2 : ℝ) : ℂ) * OneStep_g g (zt E u) I M)
        + ((∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) (zt E (u + Δ)) I ∂(PF d L W g))
          - (∫ ω : Ω d L W, loopL d L W (OneStep_Hs M τ ω) (zt E u) I ∂(PF d L W g))
          - (Δ : ℂ) * OneStep_J1 (blockMat d L W M) (zt E u) (OneStep_Dsp d L W E) I) := by
    rw [hgen, hτ2]
    simp only [OneStep_Hs]
    ring
  rw [hLHS]
  refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans ?_)
  rw [hτ3, OneStep_card_Idx, OneStep_card_Block]
  have hN : (1 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    have : 1 ≤ (W * L) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
        (Nat.pos_of_ne_zero (NeZero.ne L)))
    exact_mod_cast this
  have hcl := OneStep_closure I.length hN (inv_nonneg.mpr hη.le)
  unfold envConst
  have hτ3' : 0 ≤ τ ^ 3 := by positivity
  rw [hc₁, OneStep_card_Block]
  calc _ = (32 * (((W * L) ^ d : ℕ) : ℝ) ^ 3 * (((W * L) ^ d : ℕ) : ℝ) *
            ((I.length : ℝ) * (I.length + 1) * (I.length + 2) * (etaT E (u + Δ))⁻¹ ^ (I.length + 3))
            / 3
          + ((((W * L) ^ d : ℕ) : ℝ) * ((I.length : ℝ) * (I.length + 1) *
            (etaT E (u + Δ))⁻¹ ^ (I.length + 2))) * (1 / 2 + 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2))
          * τ ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcl hτ3'

end Assembly

/-! ## 8. Compiled nonempty instances at `d = 3`

Every hypothesis is discharged at concrete data: `d = 3`, `NeZero L`, `NeZero W`, `|E| = 0 < 2`, the
well-formed loop `(+,-; 0,0)` of length `k = 2`, `u = 1/2`, `Δ = 10⁻³` (`u + Δ < 1`), and Hermitian
matrices `1` (a nonzero sample point) and `0`. -/

section Instances

/-- A well-formed loop of length `2`: `σ = (+, -)`, `a = (0, 0)`. -/
private def OneStep_instLoop (d L : ℕ) : Loop.LoopIdx (Zd d L) := ⟨[true, false], [0, 0]⟩

private theorem OneStep_instLoop_wf (d L : ℕ) : (OneStep_instLoop d L).WF := rfl

/-- `oneStepEnvelope` at `d = 3`, `L = 3`, `W = 2` (`N = (W L)^3 = 216`), `g = 1/2`, `E = 0`,
`u = 1/2`, `Δ = 1/1000`, `M = 1`, the two-loop `(+,-; 0,0)`. -/
example :
    ‖(∫ ω', loopL 3 3 2 (blockMat 3 3 2 ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
          + (Real.sqrt (1 / 1000) : ℂ) • Xmat 3 3 2 ω')) (zt 0 (1 / 2 + 1 / 1000))
          (OneStep_instLoop 3 3) ∂(PF 3 3 2 (1 / 2))) -
        loopL 3 3 2 (blockMat 3 3 2 (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) (zt 0 (1 / 2))
          (OneStep_instLoop 3 3) -
        ((1 / 1000 : ℝ) : ℂ) * genMat 3 3 2 (1 / 2) 0 (1 / 2)
          (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (OneStep_instLoop 3 3)‖ ≤
      envConst 3 3 2 0 (OneStep_instLoop 3 3).length (1 / 2 + 1 / 1000) *
        (1 / 1000 : ℝ) ^ ((3 : ℝ) / 2) :=
  oneStepEnvelope 3 3 2 (1 / 2) 0 (by norm_num) (OneStep_instLoop 3 3) (OneStep_instLoop_wf 3 3)
    (1 / 2) (1 / 1000) (by norm_num) (by norm_num) (by norm_num) 1 Matrix.isHermitian_one

/-- `oneStepEnvelope` at the data of the admissible sequence `sz0` (`d = 3`, `L = 4`, `W = 32`,
`g = 1/64`), at `E = 0`, `u = 0`, `Δ = 1/1000`, `M = 1`. -/
example :
    ‖(∫ ω', loopL 3 4 32 (blockMat 3 4 32 ((1 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ)
          + (Real.sqrt (1 / 1000) : ℂ) • Xmat 3 4 32 ω')) (zt 0 (0 + 1 / 1000))
          (OneStep_instLoop 3 4) ∂(PF 3 4 32 (1 / 64))) -
        loopL 3 4 32 (blockMat 3 4 32 (1 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ)) (zt 0 0)
          (OneStep_instLoop 3 4) -
        ((1 / 1000 : ℝ) : ℂ) * genMat 3 4 32 (1 / 64) 0 0
          (1 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ) (OneStep_instLoop 3 4)‖ ≤
      envConst 3 4 32 0 (OneStep_instLoop 3 4).length (0 + 1 / 1000) *
        (1 / 1000 : ℝ) ^ ((3 : ℝ) / 2) :=
  oneStepEnvelope 3 4 32 (1 / 64) 0 (by norm_num) (OneStep_instLoop 3 4) (OneStep_instLoop_wf 3 4)
    0 (1 / 1000) le_rfl (by norm_num) (by norm_num) 1 Matrix.isHermitian_one

/-- The envelope constant is positive at the instance (`N = 216`, `k = 2`, `η_v = 0.4995`). -/
example : 0 < envConst 3 3 2 0 2 (1 / 2 + 1 / 1000) := by
  have hη : 0 < etaT 0 (1 / 2 + 1 / 1000) := OneStep_eta_pos (by norm_num) (by norm_num)
  unfold envConst
  positivity

/-- `norm_loopDrift_sub_le` at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `u = 1/2`, the two-loop
`(+,-; 0,0)` and the Hermitian matrices `0` and `1`. -/
example :
    ‖loopDrift 3 3 2 (1 / 2) 0 (1 / 2) (OneStep_instLoop 3 3) 0
        - loopDrift 3 3 2 (1 / 2) 0 (1 / 2) (OneStep_instLoop 3 3) 1‖
      ≤ driftLip 3 3 2 (OneStep_instLoop 3 3).σ.length |(zt 0 (1 / 2)).im| (mSigma 0) *
          ‖(0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) - 1‖ := by
  have hz : (zt 0 (1 / 2)).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by norm_num) (spectralM_im_pos (E := 0) (by norm_num))).ne'
  exact norm_loopDrift_sub_le 3 3 2 (1 / 2) hz Matrix.isHermitian_zero Matrix.isHermitian_one
    (OneStep_instLoop_wf 3 3) (by simp [OneStep_instLoop])

/-- `norm_green_sub_le_of_herm` for the `2 × 2` matrices `0` and `1` at `z = i`. -/
example :
    ‖green (0 : Matrix (Fin 2) (Fin 2) ℂ) Complex.I - green (1 : Matrix (Fin 2) (Fin 2) ℂ) Complex.I‖
      ≤ |Complex.I.im|⁻¹ ^ 2 * ‖(0 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ :=
  norm_green_sub_le_of_herm Matrix.isHermitian_zero Matrix.isHermitian_one (by simp)

end Instances

end RBM.Path
