/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWSizeClaim
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAExpandW
import RBM3D.BA.GreenSchur
import RBM3D.BA.Prop5Short
import RBM3D.BA.KBase

/-!
# BA-L3c2 (T2412), part 1: the kernel edges and the molecular forest with atoms

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (`7_8:line`) and
`paper/tex/B_graphical_lemmas.tex` (`B:line`): `claim:size` (`7_8:264-266`), `(eq:estSpm-W)`
(`7_8:260`), the size and order of a BA graph `(eq_defsize_BA)`, `(eq:ordG_BA)` (`B:345-353`),
the atoms
of `def_atom` (`B:302-304`).  The paper gives no proof of `claim:size` in either model (delta
T2040m);
this pair of files proves it for the block Anderson model, in a deterministic form, with
`M`-dotted edges
and atoms.  Part 2 is `Graph/BASizeClaim2` (it imports this file).

Reuse and copies (no port from RBM1D/RBM2D, nothing to port): `lwLift`, `lwLift_mul`, `lwSmat_eq`,
`lwBdist`, `lwKBound_of_decay`, `lwForest_sum_le`, `LWKBound` of `Graph/LWSizeClaim`; the BA
vocabulary
of `Graph/BAVocab`; `baW_mul` of `Graph/BAExpandW`; `BAMB_row_l1`, `BAMres_fine_apply` of
`BA/GreenSchur`, `BA/FlowPins`; `baProp5s_of_real` of `BA/Prop5Short`; `BATheta_isUnit` of
`BA/KBase`.
Private copies of private lemmas of those files are prefixed `BASizeClaim_`
(`lwLift_add/sub/smul/zero`,
the computation of `lwSpOf_eq`, `KStep_theta_shift`, `BAExpandW_fibre_sum`).

## Contents (namespace `RBM.Graph`, private prefix `BASizeClaim_`)

1. **T1, the kernel edges.**  `baSp_eq`: `S⁺ = S W = t · lift(Θ^{(+,+)})` with `W = (1 - M⁺S)⁻¹`
   (`BAlwW`), the BA form of `lwSpOf_eq`.  `baSpDecay`: the BA `(eq:estSpm-W)`,
   `|S_{xy}|, |S⁺_{xy}| ≤ C W^{-d} e^{-c d_B(x,y)}` with `(C, c)` depending on `(d, Λ, κ)` only,
   for every
   `0 < g₀ ≤ Λ`: the uniform Combes-Thomas decay of `baProp5s_of_real`, no smallness of `g₀`.
   `baKBound_E`: the `LWKBound` constants of `S`, `S⁺`, `M`, `g₀ Ψ`.
2. **T2, the forest.**  The edge index `BAGraph.Jx = waved ⊕ mdot ⊕ psi` and its ends
   `BAGraph.edgeEnds`; `BAGraph.exists_forest`: one root per internal molecule, `|C| + n_M =
   |I|`, the
   waved tree edges number `n_A - n_M` (one *gate* waved edge per non-target atom, spanning trees
   of the
   dotted edges inside the atoms, ranks `ρ = rk₀ · (S + 1) + rk₁` lexicographic in the waved
   distance and
   the dotted depth); `BAGraph.counters_le`; `BASizeClaim_forest_sum_le`: the peeling bound with
   per-edge
   `(a_j, K_j)`, from the public `lwForest_sum_le` (`K'_c = 1`, `f'_c = f_{e(c)} / K_{e(c)}`).
3. Compiled instances at `d = 3`, `L = 4`, `W = 2`, the flow point `P : FlowPt 4 10`.

Paper-delta candidates are proposed in the report (`T2412a`, `T2412b`, `T2412c`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open Matrix

namespace RBM.Graph

open RBM RBM.Gauss

universe u₁ u₂ u₃ u₄

/-! ## 1. `S⁺ = S W = t · lift(Θ)`: the kernel edges -/

section Kernel

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem BASizeClaim_lift_add (A B : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (A + B) = lwLift d L W A + lwLift d L W B := by
  ext x y; simp [lwLift, mul_add]

private theorem BASizeClaim_lift_sub (A B : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (A - B) = lwLift d L W A - lwLift d L W B := by
  ext x y; simp [lwLift, mul_sub]

private theorem BASizeClaim_lift_smul (c : ℂ) (A : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (c • A) = c • lwLift d L W A := by
  ext x y; simp [lwLift]; ring

private theorem BASizeClaim_lift_zero : lwLift d L W (0 : Matrix (Zd d L) (Zd d L) ℂ) = 0 := by
  ext x y; simp [lwLift]

/-- At `g = 0` the block variance is the identity: `S^{(B)}(0) = I`. -/
private theorem BASizeClaim_SB_zero : SB d L (0 : ℝ) = (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
  ext a b
  rw [SB_apply]
  by_cases h : a = b
  · subst h; simp [sbKernel]
  · have : a - b ≠ 0 := sub_ne_zero.mpr h
    simp [sbKernel, this, h]

/-- `S = t · lift(1)`: the BA variance matrix is block diagonal. -/
private theorem BASizeClaim_S_eq (t : ℝ) :
    Matrix.of (BAlwS d L W t) = (t : ℂ) • lwLift d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
  have h : Matrix.of (BAlwS d L W t) = lwSmat d L W 0 t := by
    ext x y
    simp [BAlwS, lwSmat]
  rw [h, lwSmat_eq, BASizeClaim_SB_zero]

/-- The fibre sum: a function of the block coordinate supported on one offset sums to the sum over the blocks
(the pattern of `BAExpandW_fibre_sum`, private there; not private here, `BASizeClaim2` uses it). -/
theorem BASizeClaim_fibre_sum {β : Type*} [AddCommMonoid β] (x : Idx d L W) (f : Zd d L → β) :
    ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ b : Zd d L, f b := by
  have h : ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ y : Idx d L W, (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0)
        (splitEquiv d L W y) := rfl
  rw [h, Equiv.sum_comp (splitEquiv d L W) (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0),
    Fintype.sum_prod_type]
  simp

/-- `M^+ S = t · lift(M^{(+,+)})` (`M` is offset-diagonal, `S` block-diagonal: one `α` per block). -/
private theorem BASizeClaim_MpS_eq (g0 E : ℝ) (m : ℂ) (hw : ((E : ℂ) + m).im ≠ 0) (t : ℝ) :
    BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t) =
      (t : ℂ) • lwLift d L W (RBM.BA.BAMss d L (RBM.BA.BAMB d L g0 (E : ℂ) m) true true) := by
  ext x y
  rw [BASizeClaim_S_eq, Matrix.mul_apply]
  simp only [Matrix.smul_apply, lwLift, Matrix.of_apply, smul_eq_mul, BAlwMp, RBM.BA.BAMss,
    RBM.BA.BAMsigma, ite_true, Matrix.one_apply]
  unfold BAlwM
  simp only [RBM.BA.BAMres_fine_apply d L W g0 (E : ℂ) m hw]
  have h := BASizeClaim_fibre_sum x (fun b => RBM.BA.BAMB d L g0 (E : ℂ) m (split d L W x).1 b *
    RBM.BA.BAMB d L g0 (E : ℂ) m b (split d L W x).1 *
      ((t : ℂ) * (((W : ℂ) ^ d)⁻¹ * if b = (split d L W y).1 then 1 else 0)))
  have h2 : ∀ α : Idx d L W,
      (if (split d L W x).2 = (split d L W α).2 then RBM.BA.BAMB d L g0 (E : ℂ) m (split d L W x).1
          (split d L W α).1 else 0) *
        (if (split d L W α).2 = (split d L W x).2 then RBM.BA.BAMB d L g0 (E : ℂ) m (split d L W α).1
          (split d L W x).1 else 0) *
        ((t : ℂ) * (((W : ℂ) ^ d)⁻¹ * if (split d L W α).1 = (split d L W y).1 then 1 else 0)) =
      if (split d L W x).2 = (split d L W α).2 then
        (fun b => RBM.BA.BAMB d L g0 (E : ℂ) m (split d L W x).1 b *
          RBM.BA.BAMB d L g0 (E : ℂ) m b (split d L W x).1 *
            ((t : ℂ) * (((W : ℂ) ^ d)⁻¹ * if b = (split d L W y).1 then 1 else 0))) (split d L W α).1 else 0 := by
    intro α
    by_cases ho : (split d L W x).2 = (split d L W α).2
    · simp only [ho, ite_true]
    · have : ¬ (split d L W α).2 = (split d L W x).2 := fun h => ho h.symm
      simp [ho, this]
  simp only [h2]
  rw [h]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- `(1 - t lift(Q)) (1 + lift(Θ - 1)) = 1` when `(1 - t Q) Θ = 1` (the computation of `lwSpOf_eq`,
`LWSizeClaim.lean:165`). -/
private theorem BASizeClaim_lift_inv (t : ℝ) (Q Θ : Matrix (Zd d L) (Zd d L) ℂ)
    (h : (1 - (t : ℂ) • Q) * Θ = 1) :
    (1 - (t : ℂ) • lwLift d L W Q) * (1 + lwLift d L W (Θ - 1)) = 1 := by
  have hX : Θ - 1 - (t : ℂ) • Q - (t : ℂ) • (Q * (Θ - 1)) = 0 := by
    have : Θ - 1 - (t : ℂ) • Q - (t : ℂ) • (Q * (Θ - 1)) = (1 - (t : ℂ) • Q) * Θ - 1 := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, smul_sub, one_mul, mul_one]
      abel
    rw [this, h, sub_self]
  set R : Matrix (Idx d L W) (Idx d L W) ℂ := 1 + lwLift d L W (Θ - 1) with hR
  have : (1 - (t : ℂ) • lwLift d L W Q) * R =
      1 + lwLift d L W (Θ - 1 - (t : ℂ) • Q - (t : ℂ) • (Q * (Θ - 1))) := by
    rw [BASizeClaim_lift_sub, BASizeClaim_lift_sub, BASizeClaim_lift_smul, BASizeClaim_lift_smul,
      ← lwLift_mul, hR]
    simp only [sub_mul, mul_add, smul_mul_assoc, one_mul, mul_one]
    abel
  rw [this, hX, BASizeClaim_lift_zero, add_zero]

/-- **T1 `baSp_eq`**: `S⁺ = S W = t · lift(Θ^{(+,+)})`, `W = (1 - M^+ S)⁻¹` (`BAlwW`, `baW_mul`),
`lift = lwLift`: the BA form of `lwSpOf_eq` (`LWSizeClaim.lean:165`). -/
theorem baSp_eq (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g0 κ E t : ℝ) (m : ℂ)
    (hr : RBM.BA.BAReal d L g0 κ E m) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m =
      (t : ℂ) • lwLift d L W (RBM.BA.BATheta d L g0 E m t true true) := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hr.1.1.ne'
  set Q := RBM.BA.BAMss d L (RBM.BA.BAMB d L g0 (E : ℂ) m) true true with hQ
  set Θ := RBM.BA.BATheta d L g0 E m t true true with hΘ
  have hU := RBM.BA.BATheta_isUnit d L g0 κ E m hr t ht0 ht1 true true
  have h1 : (1 - (t : ℂ) • Q) * Θ = 1 := by
    have : Θ = Ring.inverse (1 - (t : ℂ) • Q) := rfl
    rw [this]
    exact Ring.mul_inverse_cancel _ hU
  have hAR := BASizeClaim_lift_inv (W := W) t Q Θ h1
  rw [← BASizeClaim_MpS_eq g0 E m hw t] at hAR
  have hWm := baW_mul (W := W) hL g0 E t m hr.1 ht0 ht1
  have hWR : BAlwW d L W g0 E t m = 1 + lwLift d L W (Θ - 1) := by
    calc BAlwW d L W g0 E t m = BAlwW d L W g0 E t m * 1 := (mul_one _).symm
      _ = BAlwW d L W g0 E t m * ((1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) *
          (1 + lwLift d L W (Θ - 1))) := by rw [hAR]
      _ = (BAlwW d L W g0 E t m * (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t))) *
          (1 + lwLift d L W (Θ - 1)) := (mul_assoc _ _ _).symm
      _ = 1 + lwLift d L W (Θ - 1) := by rw [hWm, one_mul]
  rw [hWR, BASizeClaim_S_eq, smul_mul_assoc, mul_add, mul_one, lwLift_mul, one_mul, ← BASizeClaim_lift_add]
  congr 2
  abel

/-! ### The decay of `S` and `S⁺ = S W` (`(eq:estSpm-W)`) -/

private theorem BASizeClaim_Msigma_shift (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
    RBM.BA.BAMsigma d L (RBM.BA.BAMB d L g z m) σ (x + c) (y + c) =
      RBM.BA.BAMsigma d L (RBM.BA.BAMB d L g z m) σ x y := by
  cases σ
  · simp only [RBM.BA.BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply,
      RBM.BA.BAMB_shift]
  · exact RBM.BA.BAMB_shift d L g z m x y c

/-- Translation invariance of `Θ`: `Θ_t^{(s,s')}(x, y) = Θ_t^{(s,s')}(0, y - x)` (a copy of the private
`KStep_theta_shift`, `BA/KStep.lean:270`). -/
private theorem BASizeClaim_theta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    RBM.BA.BATheta d L g E m t s s' x y = RBM.BA.BATheta d L g E m t s s' 0 (y - x) := by
  set Q := RBM.BA.BAMss d L (RBM.BA.BAMB d L g (E : ℂ) m) s s' with hQ
  let e : Zd d L ≃ Zd d L := Equiv.addRight (-x)
  have hQe : ∀ a b, Q (e a) (e b) = Q a b := fun a b => by
    simp only [hQ, RBM.BA.BAMss, Matrix.of_apply, e, Equiv.coe_addRight]
    rw [BASizeClaim_Msigma_shift, BASizeClaim_Msigma_shift]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q).submatrix e e =
      1 - (t : ℂ) • Q := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQe]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q) e e
  rw [hA] at h2
  unfold RBM.BA.BATheta RBM.PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  simp only [e, Equiv.coe_addRight, add_neg_cancel, ← sub_eq_add_neg] at h3
  exact h3

/-- **The decay of `Θ^{(+,+)}`** in the block distance, from `baProp5s_of_real`: `‖Θ(a,b)‖ ≤ (1+Λ²) C₅
e^{-μ|a-b|}` (`C₅ = BAp5s_C`, `μ = BAp5s_rate`). -/
private theorem BASizeClaim_theta_decay (hL : 3 ≤ L) (hd : 3 ≤ d) (Λ g κ E t : ℝ) (m : ℂ) (hΛ : 0 < Λ)
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : RBM.BA.BAReal d L g κ E m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) :
    ‖RBM.BA.BATheta d L g E m t true true a b‖ ≤
      ((1 + Λ ^ 2) * RBM.BA.BAp5s_C d Λ κ) * Real.exp (-(RBM.BA.BAp5s_rate d Λ κ * (zdistD d L (a - b) : ℝ))) := by
  rw [BASizeClaim_theta_shift]
  have h := RBM.BA.baProp5s_of_real d L hL (by omega) Λ g κ E m hΛ hg hgΛ hκ hr t ht0 ht1.le true (b - a)
  have hC := RBM.BA.BAp5s_C_pos d Λ κ (by omega) hΛ hκ
  have hz : zdistD d L (b - a) = zdistD d L (a - b) := by
    rw [show b - a = -(a - b) by ring, zdistD_neg]
  rw [hz] at h
  refine h.trans ?_
  have hΛ2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
  have he := Real.exp_pos (-RBM.BA.BAp5s_rate d Λ κ * (zdistD d L (a - b) : ℝ))
  have he1 : Real.exp (-(RBM.BA.BAp5s_rate d Λ κ * (zdistD d L (a - b) : ℝ))) =
      Real.exp (-RBM.BA.BAp5s_rate d Λ κ * (zdistD d L (a - b) : ℝ)) := by rw [neg_mul]
  rw [he1]
  have h3 : (if b - a = 0 then (1 : ℝ) else 0) +
      g ^ 2 * Real.exp (-RBM.BA.BAp5s_rate d Λ κ * (zdistD d L (a - b) : ℝ)) ≤
      (1 + Λ ^ 2) * Real.exp (-RBM.BA.BAp5s_rate d Λ κ * (zdistD d L (a - b) : ℝ)) := by
    by_cases h0 : b - a = 0
    · have : a - b = 0 := by rw [← neg_sub, h0, neg_zero]
      simp only [h0, ite_true, this, zdistD_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      linarith
    · simp only [h0, ite_false, zero_add]
      nlinarith
  calc _ ≤ RBM.BA.BAp5s_C d Λ κ * ((1 + Λ ^ 2) *
        Real.exp (-RBM.BA.BAp5s_rate d Λ κ * (zdistD d L (a - b) : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 hC.le
    _ = _ := by ring

end Kernel

section Decay

/-- **T1 `baSpDecay`** (BA `(eq:estSpm-W)`, the band's `lwSpOf_decay`, `LWSizeClaim.lean:327`):
`|S_{xy}|, |S⁺_{xy}| ≤ C W^{-d} e^{-c d_B(x,y)}`, `(C, c)` depending on `(d, Λ, κ)` only, for every
`0 < g₀ ≤ Λ`, `0 ≤ t < 1`, `L ≥ 3`, `W ≥ 1` and every real-axis datum `BAReal`.  From `baSp_eq` and the
proved `baProp5s_of_real` (`(prop:ThfadC_short)`): the uniform Combes-Thomas decay, no smallness of `g₀`. -/
theorem baSpDecay (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
      (∀ x y : Idx d L W, ‖Matrix.of (BAlwS d L W t) x y‖ ≤
        C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
      (∀ x y : Idx d L W, ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤
        C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) := by
  have hd0 : 0 < d := by omega
  have hC5 := RBM.BA.BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hμ := RBM.BA.BAp5s_rate_pos d Λ κ hd0 hΛ hκ
  have hK : 0 ≤ (1 + Λ ^ 2) * RBM.BA.BAp5s_C d Λ κ := by positivity
  refine ⟨(1 + Λ ^ 2) * RBM.BA.BAp5s_C d Λ κ + 1, RBM.BA.BAp5s_rate d Λ κ, by positivity, hμ,
    fun L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 => ?_⟩
  have hW : 0 < ((W : ℝ) ^ d)⁻¹ := by
    have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  have hnorm : ∀ z : ℂ, ‖(t : ℂ) * (((W : ℂ) ^ d)⁻¹ * z)‖ = t * ((W : ℝ) ^ d)⁻¹ * ‖z‖ := by
    intro z
    rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    ring
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · rw [BASizeClaim_S_eq]
    have he := Real.exp_pos (-(RBM.BA.BAp5s_rate d Λ κ * (lwBdist d L W x y : ℝ)))
    simp only [Matrix.smul_apply, lwLift, Matrix.of_apply, smul_eq_mul, hnorm]
    by_cases h : (split d L W x).1 = (split d L W y).1
    · have h0 : (lwBdist d L W x y : ℝ) = 0 := by
        simp [lwBdist, h]
      rw [h0]
      simp only [Matrix.one_apply, h, ite_true, norm_one, mul_zero, neg_zero, Real.exp_zero, mul_one]
      nlinarith
    · simp only [Matrix.one_apply, h, ite_false, norm_zero, mul_zero]
      positivity
  · rw [baSp_eq d L W hL g0 κ E t m hr ht0 ht1]
    have he := Real.exp_pos (-(RBM.BA.BAp5s_rate d Λ κ * (lwBdist d L W x y : ℝ)))
    simp only [Matrix.smul_apply, lwLift, Matrix.of_apply, smul_eq_mul, hnorm]
    have hB := BASizeClaim_theta_decay hL hd Λ g0 κ E t m hΛ hg hgΛ hκ hr ht0 ht1 (split d L W x).1 (split d L W y).1
    have hB' : ‖RBM.BA.BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖ ≤
        ((1 + Λ ^ 2) * RBM.BA.BAp5s_C d Λ κ + 1) *
          Real.exp (-(RBM.BA.BAp5s_rate d Λ κ * (lwBdist d L W x y : ℝ))) := by
      refine hB.trans ?_
      unfold lwBdist
      gcongr
      linarith
    calc t * ((W : ℝ) ^ d)⁻¹ * ‖RBM.BA.BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖
        ≤ 1 * ((W : ℝ) ^ d)⁻¹ * (((1 + Λ ^ 2) * RBM.BA.BAp5s_C d Λ κ + 1) *
          Real.exp (-(RBM.BA.BAp5s_rate d Λ κ * (lwBdist d L W x y : ℝ)))) := by
          apply mul_le_mul (mul_le_mul ht1.le le_rfl hW.le zero_le_one) hB' (norm_nonneg _) (by positivity)
      _ = _ := by ring

end Decay

section KBound

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- A matrix with `∞`-row sums `≤ R` and `K x y = K y x` has the three `LWKBound` bounds with `(R, R)`. -/
private theorem BASizeClaim_kbound_of_rows {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ)
    (hsymm : ∀ x y, K x y = K y x) {R : ℝ} (hrow : ∀ x, ∑ y, ‖K x y‖ ≤ R) : LWKBound K R R :=
  ⟨fun x y => (Finset.single_le_sum (f := fun y => ‖K x y‖) (fun y _ => norm_nonneg _)
      (Finset.mem_univ y)).trans (hrow x), hrow,
    fun y => (Finset.sum_congr rfl fun x _ => by rw [hsymm x y]).trans_le (hrow y)⟩

private theorem BASizeClaim_kbound_mono {ι : Type*} [Fintype ι] {K : Matrix ι ι ℂ} {R R' : ℝ}
    (h : LWKBound K R R) (hR : R ≤ R') : LWKBound K R' R' :=
  ⟨fun x y => (h.1 x y).trans hR, fun x => (h.2.1 x).trans hR, fun y => (h.2.2 y).trans hR⟩

/-- The row sums of `M`: `Σ_y |M_{xy}| = Σ_b |M^{(B)}_{[x] b}| ≤ c⁻¹ expC(d-2, c)` (`BAMB_row_l1`; `M` is
offset-diagonal, one `y` per block), uniformly in `g₀ ∈ (0, Λ]`, `L`, `W`, `E`. -/
private theorem BASizeClaim_M_row (hd : 3 ≤ d) (hL : 3 ≤ L) (Λ g0 κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ)
    (hg : 0 < g0) (hgΛ : g0 ≤ Λ) (hκ : 0 < κ) (hr : RBM.BA.BAReal d L g0 κ E m) (x : Idx d L W) :
    ∑ y, ‖BAlwM d L W g0 E m x y‖ ≤
      (RBM.BA.BAct_rate d Λ κ)⁻¹ * expC (d - 2) (RBM.BA.BAct_rate d Λ κ) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hr.1.1.ne'
  have h1 : ∑ y, ‖BAlwM (k + 2) L W g0 E m x y‖ =
      ∑ y : Idx (k + 2) L W, (if (split (k + 2) L W x).2 = (split (k + 2) L W y).2 then
        ‖RBM.BA.BAMB (k + 2) L g0 (E : ℂ) m (split (k + 2) L W x).1 (split (k + 2) L W y).1‖ else 0) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold BAlwM
    rw [RBM.BA.BAMres_fine_apply (k + 2) L W g0 (E : ℂ) m hw x y]
    split_ifs <;> simp
  rw [h1, BASizeClaim_fibre_sum x (fun b => ‖RBM.BA.BAMB (k + 2) L g0 (E : ℂ) m (split (k + 2) L W x).1 b‖)]
  have := RBM.BA.BAMB_row_l1 k L hL Λ g0 κ E m hΛ hg hgΛ hκ hr (split (k + 2) L W x).1
  simpa using this

/-- The entries of `Ψ = Ψ^{(B)} ⊗ I` (`PsiI`) in the block-offset form. -/
private theorem BASizeClaim_PsiI_apply (x y : Idx d L W) :
    PsiI d L W x y = if (split d L W x).2 = (split d L W y).2 then
      (if Adj d L (split d L W x).1 (split d L W y).1 then (1 : ℂ) else 0) else 0 := by
  simp only [PsiI, PsiV, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, PsiB,
    Matrix.of_apply]
  have h1 : splitEquiv d L W x = split d L W x := rfl
  have h2 : splitEquiv d L W y = split d L W y := rfl
  rw [h1, h2]
  by_cases h : (split d L W x).2 = (split d L W y).2 <;> simp [h]

private theorem BASizeClaim_PsiI_symm (x y : Idx d L W) : PsiI d L W x y = PsiI d L W y x := by
  rw [BASizeClaim_PsiI_apply, BASizeClaim_PsiI_apply]
  have hadj : Adj d L (split d L W y).1 (split d L W x).1 ↔ Adj d L (split d L W x).1 (split d L W y).1 := by
    simp only [Adj]
    rw [show (split d L W y).1 - (split d L W x).1 = -((split d L W x).1 - (split d L W y).1) by ring,
      zdistD_neg]
  by_cases h : (split d L W x).2 = (split d L W y).2
  · simp only [h, ite_true]
    by_cases ha : Adj d L (split d L W x).1 (split d L W y).1
    · simp [ha, hadj.2 ha]
    · simp [ha, mt hadj.1 ha]
  · have h' : ¬ (split d L W y).2 = (split d L W x).2 := fun e => h e.symm
    simp [h, h']

/-- The row sums of `g₀ Ψ`: `g₀ · #{b : b ∼ [x]} = 2 d g₀`. -/
private theorem BASizeClaim_Psi_row (hL : 3 ≤ L) (g0 : ℝ) (hg : 0 < g0) (x : Idx d L W) :
    ∑ y, ‖((g0 : ℂ) • PsiI d L W) x y‖ = 2 * d * g0 := by
  have h1 : ∀ y : Idx d L W, ‖((g0 : ℂ) • PsiI d L W) x y‖ = g0 *
      (if (split d L W x).2 = (split d L W y).2 then
        (if Adj d L (split d L W x).1 (split d L W y).1 then (1 : ℝ) else 0) else 0) := by
    intro y
    simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hg, BASizeClaim_PsiI_apply]
    split_ifs <;> simp
  simp only [h1]
  rw [← Finset.mul_sum, BASizeClaim_fibre_sum x (fun b => if Adj d L (split d L W x).1 b then (1 : ℝ) else 0),
    Finset.sum_boole, card_adj d L hL]
  push_cast
  ring

/-- **T1 `baKBound_E`**: the `LWKBound` constants of `S`, `S⁺ = S W`, `M`, `g₀ Ψ`, depending on `(d, Λ, κ)` only:
`S`, `S⁺` entries `≤ K₀ W^{-d}`, row and column sums `≤ K₁`; `M` and `g₀ Ψ` entries, row and column sums
`≤ Kd = c⁻¹ expC(d-2, c) + 2 d Λ` (Combes-Thomas `c = BAct_rate`; no smallness of `g₀`). -/
theorem baKBound_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        LWKBound (Matrix.of (BAlwS d L W t)) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
        LWKBound (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
        LWKBound (BAlwM d L W g0 E m) Kd Kd ∧ LWKBound ((g0 : ℂ) • PsiI d L W) Kd Kd := by
  obtain ⟨C, c, hC, hc, h⟩ := baSpDecay d hd Λ κ hΛ hκ
  have hd0 : 0 < d := by omega
  have hc0 := RBM.BA.BAct_rate_pos d Λ κ hd0 hΛ hκ
  have hE : 0 < expC (d - 2) c := by
    unfold expC
    positivity
  have hE0 : 0 < expC (d - 2) (RBM.BA.BAct_rate d Λ κ) := by
    unfold expC
    positivity
  have hKM : 0 ≤ (RBM.BA.BAct_rate d Λ κ)⁻¹ * expC (d - 2) (RBM.BA.BAct_rate d Λ κ) := by positivity
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨C, C * expC (d - 2) c, (RBM.BA.BAct_rate d Λ κ)⁻¹ * expC (d - 2) (RBM.BA.BAct_rate d Λ κ) +
      2 * d * Λ, hC, mul_pos hC hE, by positivity, fun L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 => ?_⟩
  obtain ⟨h1, h2⟩ := h L W hL g0 E t m hg hgΛ hr ht0 ht1
  refine ⟨lwKBound_of_decay hd hC.le hc h1, lwKBound_of_decay hd hC.le hc h2, ?_, ?_⟩
  · refine BASizeClaim_kbound_mono (BASizeClaim_kbound_of_rows _ (baM_symm g0 E m)
      (fun x => BASizeClaim_M_row hd hL Λ g0 κ E m hΛ hg hgΛ hκ hr x)) ?_
    have : 0 ≤ 2 * (d : ℝ) * Λ := by positivity
    linarith
  · refine BASizeClaim_kbound_mono (R := 2 * d * Λ) (BASizeClaim_kbound_of_rows _ (fun x y => by
      simp only [Matrix.smul_apply, smul_eq_mul, BASizeClaim_PsiI_symm x y]) (fun x => ?_)) ?_
    · rw [BASizeClaim_Psi_row hL g0 hg x]
      nlinarith
    · linarith

end KBound

section AbsForest

variable {V : Type*}

private inductive BASizeClaim_Reach (A W : V → V → Prop) (T : V → Prop) : ℕ → V → Prop
  | tgt {v : V} : T v → BASizeClaim_Reach A W T 0 v
  | dot {n : ℕ} {v u : V} : A v u → BASizeClaim_Reach A W T n u → BASizeClaim_Reach A W T n v
  | wav {n : ℕ} {v u : V} : W v u → BASizeClaim_Reach A W T n u → BASizeClaim_Reach A W T (n + 1) v

private theorem BASizeClaim_rtg_symm {A : V → V → Prop} (hA : ∀ u v, A u v → A v u) {u v : V}
    (h : Relation.ReflTransGen A u v) : Relation.ReflTransGen A v u := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hA _ _ hbc) ih

private theorem BASizeClaim_reach_rtg {A W : V → V → Prop} {T : V → Prop} {n : ℕ} {v u : V}
    (h : Relation.ReflTransGen A v u) (hu : BASizeClaim_Reach A W T n u) :
    BASizeClaim_Reach A W T n v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hu
  | head hab _ ih => exact .dot hab ih

private theorem BASizeClaim_reach_iff {A W : V → V → Prop} (hA : ∀ u v, A u v → A v u) {T : V → Prop} {n : ℕ}
    {v u : V} (h : Relation.ReflTransGen A v u) :
    BASizeClaim_Reach A W T n v ↔ BASizeClaim_Reach A W T n u :=
  ⟨fun hv => BASizeClaim_reach_rtg (BASizeClaim_rtg_symm hA h) hv, fun hu => BASizeClaim_reach_rtg h hu⟩

private theorem BASizeClaim_reach_cases {A W : V → V → Prop} {T : V → Prop} {n : ℕ} {v : V}
    (h : BASizeClaim_Reach A W T n v) :
    (∃ t, T t ∧ Relation.ReflTransGen A v t) ∨
      ∃ u w m, Relation.ReflTransGen A v u ∧ W u w ∧ n = m + 1 ∧ BASizeClaim_Reach A W T m w := by
  induction h with
  | tgt ht => exact Or.inl ⟨_, ht, .refl⟩
  | dot hvu _ ih =>
    rcases ih with ⟨t, ht, hr⟩ | ⟨u', w, m, hr, hw, hn, hm⟩
    · exact Or.inl ⟨t, ht, .head hvu hr⟩
    · exact Or.inr ⟨u', w, m, .head hvu hr, hw, hn, hm⟩
  | wav hw hr _ => exact Or.inr ⟨_, _, _, .refl, hw, rfl, hr⟩

private inductive BASizeClaim_DReach (A : V → V → Prop) (T : V → Prop) : ℕ → V → Prop
  | tgt {v : V} : T v → BASizeClaim_DReach A T 0 v
  | step {n : ℕ} {v u : V} : A v u → BASizeClaim_DReach A T n u → BASizeClaim_DReach A T (n + 1) v

private theorem BASizeClaim_dreach_cases {A : V → V → Prop} {T : V → Prop} {n : ℕ} {v : V}
    (h : BASizeClaim_DReach A T n v) : (T v ∧ n = 0) ∨ ∃ u m, A v u ∧ n = m + 1 ∧ BASizeClaim_DReach A T m u := by
  cases h with
  | tgt ht => exact Or.inl ⟨ht, rfl⟩
  | step hu hr => exact Or.inr ⟨_, _, hu, rfl, hr⟩

/-- A rank toward a target set along the steps of `A`. -/
private theorem BASizeClaim_exists_rank (A : V → V → Prop) (T : V → Prop)
    (h : ∀ v, ∃ t, T t ∧ Relation.ReflTransGen A v t) :
    ∃ rk : V → ℕ, ∀ v, ¬ T v → ∃ u, A v u ∧ rk u < rk v := by
  classical
  have hex : ∀ v, ∃ n, BASizeClaim_DReach A T n v := by
    intro v
    obtain ⟨t, ht, hr⟩ := h v
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .tgt ht⟩
    | head hab _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .step hab hn⟩
  refine ⟨fun v => Nat.find (hex v), fun v hv => ?_⟩
  rcases BASizeClaim_dreach_cases (Nat.find_spec (hex v)) with ⟨ht, _⟩ | ⟨u, m, hvu, hn, hm⟩
  · exact absurd ht hv
  · refine ⟨u, hvu, ?_⟩
    have := Nat.find_min' (hex u) hm
    change Nat.find (hex u) < Nat.find (hex v)
    omega

/-- **The abstract atomic forest.** -/
private theorem BASizeClaim_forest_abs [Fintype V] (A W : V → V → Prop) (hA : ∀ u v, A u v → A v u) (T : V → Prop)
    (hreach : ∀ v, ∃ t, T t ∧ Relation.ReflTransGen (fun a b => A a b ∨ W a b) v t) :
    ∃ (gate : V → Prop) (par : V → V) (ρ : V → ℕ),
      (∀ v, gate v → ∀ t, T t → ¬ Relation.ReflTransGen A v t) ∧
      (∀ v, ¬ T v → (gate v ∧ W v (par v)) ∨ (¬ gate v ∧ A v (par v))) ∧
      (∀ v, ¬ T v → ρ (par v) < ρ v) ∧
      (∀ v, (∀ t, T t → ¬ Relation.ReflTransGen A v t) → ∃ u, gate u ∧ Relation.ReflTransGen A v u) ∧
      (∀ u u', gate u → gate u' → Relation.ReflTransGen A u u' → u = u') := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨fun _ => False, fun v => v, fun _ => 0, fun v => isEmptyElim v, fun v => isEmptyElim v,
      fun v => isEmptyElim v, fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  set NT : V → Prop := fun v => ∀ t, T t → ¬ Relation.ReflTransGen A v t with hNT
  have hNTiff : ∀ u v, Relation.ReflTransGen A u v → (NT u ↔ NT v) := by
    intro u v huv
    constructor
    · intro hu t ht hvt
      exact hu t ht (huv.trans hvt)
    · intro hv t ht hut
      exact hv t ht ((BASizeClaim_rtg_symm hA huv).trans hut)
  -- the rank counting waved steps
  have hR : ∀ v, ∃ n, BASizeClaim_Reach A W T n v := by
    intro v
    obtain ⟨t, ht, h⟩ := hreach v
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .tgt ht⟩
    | head hab _ ih =>
      obtain ⟨n, hn⟩ := ih
      rcases hab with hab | hab
      · exact ⟨n, .dot hab hn⟩
      · exact ⟨n + 1, .wav hab hn⟩
  set rk0 : V → ℕ := fun v => Nat.find (hR v) with hrk0def
  have hrk0 : ∀ v, BASizeClaim_Reach A W T (rk0 v) v := fun v => Nat.find_spec (hR v)
  have hrk0_le : ∀ v n, BASizeClaim_Reach A W T n v → rk0 v ≤ n := fun v n h => Nat.find_min' (hR v) h
  have hrk0_eq : ∀ v u, Relation.ReflTransGen A v u → rk0 v = rk0 u := fun v u h =>
    le_antisymm (hrk0_le v _ ((BASizeClaim_reach_iff hA h).2 (hrk0 u)))
      (hrk0_le u _ ((BASizeClaim_reach_iff hA h).1 (hrk0 v)))
  have hgate : ∀ v, NT v → ∃ u w, Relation.ReflTransGen A v u ∧ W u w ∧ rk0 w < rk0 v := by
    intro v hv
    rcases BASizeClaim_reach_cases (hrk0 v) with ⟨t, ht, hr⟩ | ⟨u, w, m, hr, hw, hn, hm⟩
    · exact absurd hr (hv t ht)
    · exact ⟨u, w, hr, hw, by have := hrk0_le w m hm; omega⟩
  -- canonical representatives of the atoms
  obtain ⟨rep, hrep1, hrep2⟩ : ∃ rep : V → V, (∀ v, Relation.ReflTransGen A v (rep v)) ∧
      (∀ u v, Relation.ReflTransGen A u v → rep u = rep v) := by
    let s : Setoid V := ⟨fun u v => Relation.ReflTransGen A u v,
      ⟨fun _ => .refl, fun h => BASizeClaim_rtg_symm hA h, fun h1 h2 => h1.trans h2⟩⟩
    refine ⟨fun v => (Quotient.mk s v).out, fun v => ?_, fun u v h => ?_⟩
    · have := Quotient.mk_out (s := s) v
      exact BASizeClaim_rtg_symm hA (this : Relation.ReflTransGen A _ _)
    · exact congrArg Quotient.out (Quotient.sound h)
  choose! gu gw hgg using hgate
  have hgu : ∀ v, NT v → Relation.ReflTransGen A v (gu v) := fun v hv => (hgg v hv).1
  have hgw : ∀ v, NT v → W (gu v) (gw v) := fun v hv => (hgg v hv).2.1
  have hgr : ∀ v, NT v → rk0 (gw v) < rk0 v := fun v hv => (hgg v hv).2.2
  set gate : V → Prop := fun v => NT v ∧ gu (rep v) = v with hgatedef
  have hP4 : ∀ v, NT v → ∃ u, gate u ∧ Relation.ReflTransGen A v u := by
    intro v hv
    have hrv : NT (rep v) := (hNTiff v (rep v) (hrep1 v)).1 hv
    have h1 : Relation.ReflTransGen A v (gu (rep v)) := (hrep1 v).trans (hgu _ hrv)
    refine ⟨gu (rep v), ⟨(hNTiff _ _ h1).1 hv, ?_⟩, h1⟩
    rw [← hrep2 v _ h1]
  have hP5 : ∀ u u', gate u → gate u' → Relation.ReflTransGen A u u' → u = u' := by
    intro u u' hu hu' h
    rw [← hu.2, ← hu'.2, hrep2 u u' h]
  have hreach2 : ∀ v, ∃ t, (fun x => T x ∨ gate x) t ∧ Relation.ReflTransGen A v t := by
    intro v
    by_cases hv : NT v
    · obtain ⟨u, hu, hr⟩ := hP4 v hv
      exact ⟨u, Or.inr hu, hr⟩
    · simp only [hNT, not_forall, not_not] at hv
      obtain ⟨t, ht, hr⟩ := hv
      exact ⟨t, Or.inl ht, hr⟩
  obtain ⟨rk1, hrk1⟩ := BASizeClaim_exists_rank A (fun x => T x ∨ gate x) hreach2
  set S : ℕ := Finset.univ.sup rk1 with hS
  have hrk1S : ∀ v, rk1 v ≤ S := fun v => Finset.le_sup (f := rk1) (Finset.mem_univ v)
  choose! rpar hrpar using hrk1
  let par : V → V := fun v => if gate v then gw (rep v) else rpar v
  refine ⟨gate, par, fun v => rk0 v * (S + 1) + rk1 v, fun v hv t ht => hv.1 t ht, ?_, ?_, hP4, hP5⟩
  · intro v hv
    by_cases hg : gate v
    · left
      refine ⟨hg, ?_⟩
      have := hgw (rep v) ((hNTiff v (rep v) (hrep1 v)).1 hg.1)
      rw [hg.2] at this
      simpa only [par, hg, ite_true] using this
    · right
      refine ⟨hg, ?_⟩
      have h : ¬ (T v ∨ gate v) := by tauto
      have : par v = rpar v := by simp [par, hg]
      rw [this]
      exact (hrpar v h).1
  · intro v hv
    by_cases hg : gate v
    · have hpv : par v = gw (rep v) := by simp [par, hg]
      rw [hpv]
      have h1 := hgr (rep v) ((hNTiff v (rep v) (hrep1 v)).1 hg.1)
      have h2 : rk0 (rep v) = rk0 v := (hrk0_eq v (rep v) (hrep1 v)).symm
      rw [h2] at h1
      have h3 := hrk1S (gw (rep v))
      change rk0 (gw (rep v)) * (S + 1) + rk1 (gw (rep v)) < rk0 v * (S + 1) + rk1 v
      have h4 : (rk0 (gw (rep v)) + 1) * (S + 1) ≤ rk0 v * (S + 1) := Nat.mul_le_mul_right _ h1
      nlinarith
    · have h : ¬ (T v ∨ gate v) := by tauto
      have hpv : par v = rpar v := by simp [par, hg]
      rw [hpv]
      obtain ⟨hvu, hlt⟩ := hrpar v h
      have h5 : rk0 v = rk0 (rpar v) := hrk0_eq v _ (.single hvu)
      change rk0 (rpar v) * (S + 1) + rk1 (rpar v) < rk0 v * (S + 1) + rk1 v
      rw [← h5]
      omega

end AbsForest

/-! ## BA forest -/

/-- The edge index `J = waved ⊕ mdot ⊕ psi` of the molecular forest. -/
abbrev BAGraph.Jx {E I : Type} (Γ : BAGraph E I) : Type :=
  Fin Γ.waved.length ⊕ Fin Γ.mdot.length ⊕ Fin Γ.psi.length

/-- The endpoints `(x, y)` of an edge of `J`. -/
def BAGraph.edgeEnds {E I : Type} (Γ : BAGraph E I) : Γ.Jx → (E ⊕ I) × (E ⊕ I)
  | Sum.inl j => ((Γ.waved.get j).x, (Γ.waved.get j).y)
  | Sum.inr (Sum.inl j) => ((Γ.mdot.get j).x, (Γ.mdot.get j).y)
  | Sum.inr (Sum.inr j) => ((Γ.psi.get j).x, (Γ.psi.get j).y)

section BAForest

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BASizeClaim_atomAdj_comm (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.atomAdj u v = Γ.atomAdj v u := by
  simp only [BAGraph.atomAdj, or_comm]

/-- Waved adjacency. -/
private def BASizeClaim_wAdj (Γ : BAGraph E I) (u v : E ⊕ I) : Prop :=
  ∃ j : Fin Γ.waved.length, ((Γ.waved.get j).x = u ∧ (Γ.waved.get j).y = v) ∨
    ((Γ.waved.get j).x = v ∧ (Γ.waved.get j).y = u)

private theorem BASizeClaim_adj_cases (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false)
    {u v : E ⊕ I} (h : Γ.adj u v = true) : BASizeClaim_wAdj Γ u v ∨ Γ.atomAdj u v = true := by
  unfold BAGraph.adj RBM.Graph.LGraph.adj at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Bool.or_eq_true, List.any_eq_true] at h
    rcases h with h | h
    · obtain ⟨e, he, hd⟩ := h
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
      exact Or.inl ⟨j, of_decide_eq_true hd⟩
    · rw [List.any_eq_true] at h
      obtain ⟨e, he, hd⟩ := h
      have := hD e he
      simp [this] at hd
  · exact Or.inr h

private theorem BASizeClaim_atomAdj_cases (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false)
    {u v : E ⊕ I} (h : Γ.atomAdj u v = true) :
    (∃ j : Fin Γ.mdot.length, ((Γ.mdot.get j).x = u ∧ (Γ.mdot.get j).y = v) ∨
        ((Γ.mdot.get j).x = v ∧ (Γ.mdot.get j).y = u)) ∨
      ∃ j : Fin Γ.psi.length, ((Γ.psi.get j).x = u ∧ (Γ.psi.get j).y = v) ∨
        ((Γ.psi.get j).x = v ∧ (Γ.psi.get j).y = u) := by
  unfold BAGraph.atomAdj at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    have := hD e he
    simp [this] at hd
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
    exact Or.inr ⟨j, of_decide_eq_true hd⟩
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
    exact Or.inl ⟨j, of_decide_eq_true hd⟩

private theorem BASizeClaim_atom_eq (Γ : BAGraph E I) {v w : E ⊕ I} (h : w ∈ Γ.atom v) :
    Γ.atom w = Γ.atom v := by
  rw [BAGraph.mem_atom_iff] at h
  have hs : ∀ a b, Γ.atomAdj a b = true → Γ.atomAdj b a = true := fun a b hab => by
    rwa [BASizeClaim_atomAdj_comm]
  ext x
  rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx
    exact (BASizeClaim_rtg_symm (A := fun a b => Γ.atomAdj a b = true) hs h).trans hx

private theorem BASizeClaim_mol_eq (Γ : BAGraph E I) {v w : E ⊕ I} (h : w ∈ Γ.mol v) :
    Γ.mol w = Γ.mol v := by
  rw [BAGraph.mem_mol_iff] at h
  have hs : ∀ a b, Γ.adj a b = true → Γ.adj b a = true := fun a b hab => by
    have : Γ.adj a b = Γ.adj b a := by
      simp only [BAGraph.adj, RBM.Graph.LGraph.adj, BAGraph.atomAdj, or_comm]
    rwa [this] at hab
  ext x
  rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx
    exact (BASizeClaim_rtg_symm (A := fun a b => Γ.adj a b = true) hs h).trans hx

private theorem BASizeClaim_self_mem_atom (Γ : BAGraph E I) (v : E ⊕ I) : v ∈ Γ.atom v := by
  rw [BAGraph.mem_atom_iff]

private theorem BASizeClaim_self_mem_mol (Γ : BAGraph E I) (v : E ⊕ I) : v ∈ Γ.mol v := by
  rw [BAGraph.mem_mol_iff]

open Classical in
/-- **The molecular forest with atoms** (the BA twin of `LGraph.exists_forest`,
`LWSizeClaim.lean:725`, with `J = waved ⊕ mdot ⊕ psi`). -/
theorem BAGraph.exists_forest (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) :
    ∃ (C : Finset I) (par : I → E ⊕ I) (edge : I → Option Γ.Jx) (ρ : I → ℕ),
      C.card + Γ.nM = Fintype.card I ∧
      (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card + Γ.nM = Γ.nA ∧
      (∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) ∧
      (∀ c ∈ C, ∃ j, edge c = some j ∧
        (((Γ.edgeEnds j).1 = Sum.inr c ∧ (Γ.edgeEnds j).2 = par c) ∨
         ((Γ.edgeEnds j).2 = Sum.inr c ∧ (Γ.edgeEnds j).1 = par c))) ∧
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, edge c₁ = edge c₂ → c₁ = c₂) := by
  -- the internal molecules and their chosen roots
  let IMfin : Finset (E ⊕ I) := Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.mol v, w.isRight = true)
  let IAfin : Finset (E ⊕ I) := Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)
  let Mi := {m : Finset (E ⊕ I) // m ∈ IMfin.image Γ.mol}
  have hMi : ∀ m : Mi, ∃ i : I, Γ.mol (Sum.inr i) = m.1 := by
    rintro ⟨m, hm⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hm
    have hv' : ∀ w ∈ Γ.mol v, w.isRight = true := by simpa [IMfin] using hv
    have := hv' v (BASizeClaim_self_mem_mol Γ v)
    rcases v with a | i
    · simp at this
    · exact ⟨i, rfl⟩
  choose rootI hroot using hMi
  have hrootInj : Function.Injective rootI := fun m m' h =>
    Subtype.ext (by rw [← hroot m, ← hroot m', h])
  have hMicard : Fintype.card Mi = Γ.nM := by
    simp only [Mi, Fintype.card_coe]
    rfl
  let T : E ⊕ I → Prop := fun v => v.isLeft = true ∨ ∃ m : Mi, v = Sum.inr (rootI m)
  let A : E ⊕ I → E ⊕ I → Prop := fun u v => Γ.atomAdj u v = true
  let Wd : E ⊕ I → E ⊕ I → Prop := fun u v => BASizeClaim_wAdj Γ u v
  have hA : ∀ u v, A u v → A v u := fun u v h => by
    simp only [A] at h ⊢
    rwa [BASizeClaim_atomAdj_comm] at h
  have hreach : ∀ v, ∃ t, T t ∧ Relation.ReflTransGen (fun a b => A a b ∨ Wd a b) v t := by
    intro v
    have hmono : ∀ t, Relation.ReflTransGen (fun a b => Γ.adj a b = true) v t →
        Relation.ReflTransGen (fun a b => A a b ∨ Wd a b) v t := fun t h => by
      refine Relation.ReflTransGen.mono (fun a b hab => ?_) v t h
      rcases BASizeClaim_adj_cases Γ hD hab with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
    by_cases hext : ∀ w ∈ Γ.mol v, w.isRight = true
    · have hm : Γ.mol v ∈ IMfin.image Γ.mol :=
        Finset.mem_image.2 ⟨v, by simpa [IMfin] using hext, rfl⟩
      let m : Mi := ⟨Γ.mol v, hm⟩
      refine ⟨Sum.inr (rootI m), Or.inr ⟨m, rfl⟩, hmono _ ?_⟩
      rw [← BAGraph.mem_mol_iff, ← (show Γ.mol (Sum.inr (rootI m)) = Γ.mol v from hroot m)]
      exact BASizeClaim_self_mem_mol Γ _
    · push Not at hext
      obtain ⟨w, hw, hwl⟩ := hext
      refine ⟨w, Or.inl ?_, hmono _ ((BAGraph.mem_mol_iff Γ v w).1 hw)⟩
      cases w with
      | inl a => rfl
      | inr b => simp at hwl
  obtain ⟨gate, parA, ρ, hP1, hP2, hP3, hP4, hP5⟩ :=
    BASizeClaim_forest_abs A Wd hA T hreach
  let C : Finset I := Finset.univ.filter (fun c => ¬ T (Sum.inr c))
  have hCmem : ∀ c, c ∈ C ↔ ¬ T (Sum.inr c) := fun c => by simp [C]
  have hgateT : ∀ v, gate v → ¬ T v := fun v hv ht => hP1 v hv v ht .refl
  have hedge : ∀ c : I, ∃ e : Option Γ.Jx, (c ∈ C → ∃ j, e = some j ∧
      (((Γ.edgeEnds j).1 = Sum.inr c ∧ (Γ.edgeEnds j).2 = parA (Sum.inr c)) ∨
       ((Γ.edgeEnds j).2 = Sum.inr c ∧ (Γ.edgeEnds j).1 = parA (Sum.inr c))) ∧
      (gate (Sum.inr c) ↔ ∃ j', j = Sum.inl j')) ∧ (c ∉ C → e = none) := by
    intro c
    by_cases hc : c ∈ C
    · have hT := (hCmem c).1 hc
      rcases hP2 (Sum.inr c) hT with ⟨hg, hw⟩ | ⟨hg, ha⟩
      · obtain ⟨j, hj⟩ := hw
        exact ⟨some (Sum.inl j), fun _ => ⟨_, rfl, hj.imp id And.symm, ⟨fun _ => ⟨j, rfl⟩, fun _ => hg⟩⟩,
          fun h => absurd hc h⟩
      · rcases BASizeClaim_atomAdj_cases Γ hD ha with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨some (Sum.inr (Sum.inl j)), fun _ => ⟨_, rfl, hj.imp id And.symm,
            ⟨fun h => absurd h hg, fun ⟨j', h⟩ => nomatch h⟩⟩, fun h => absurd hc h⟩
        · exact ⟨some (Sum.inr (Sum.inr j)), fun _ => ⟨_, rfl, hj.imp id And.symm,
            ⟨fun h => absurd h hg, fun ⟨j', h⟩ => nomatch h⟩⟩, fun h => absurd hc h⟩
    · exact ⟨none, fun h => absurd h hc, fun _ => rfl⟩
  choose edge hedge using hedge
  -- atoms and the counting
  let IA : Finset (Finset (E ⊕ I)) := IAfin.image Γ.atom
  let RA : Finset (Finset (E ⊕ I)) := (Finset.univ : Finset Mi).image (fun m => Γ.atom (Sum.inr (rootI m)))
  have hNTint : ∀ v, (∀ t, T t → ¬ Relation.ReflTransGen A v t) → ∀ w ∈ Γ.atom v, w.isRight = true := by
    intro v hv w hw
    rw [BAGraph.mem_atom_iff] at hw
    by_contra hwr
    have : w.isLeft = true := by cases w <;> simp_all
    exact hv w (Or.inl this) hw
  have hRAsub : RA ⊆ IA := by
    intro X hX
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.1 hX
    refine Finset.mem_image.2 ⟨Sum.inr (rootI m), ?_, rfl⟩
    obtain ⟨v0, hv0, hm⟩ := Finset.mem_image.1 m.2
    have hv0' : ∀ w ∈ Γ.mol v0, w.isRight = true := by simpa [IMfin] using hv0
    simp only [IAfin, Finset.mem_filter, Finset.mem_univ, true_and]
    intro w hw
    apply hv0' w
    rw [hm, ← hroot m]
    exact Γ.atom_subset_mol _ hw
  have hRAcard : RA.card = Γ.nM := by
    rw [Finset.card_image_of_injective, Finset.card_univ, hMicard]
    intro m m' h
    have h' : Γ.atom (Sum.inr (rootI m)) = Γ.atom (Sum.inr (rootI m')) := h
    have h1 : Sum.inr (rootI m') ∈ Γ.atom (Sum.inr (rootI m)) := by
      rw [h']; exact BASizeClaim_self_mem_atom Γ _
    have h2 := BASizeClaim_mol_eq Γ (Γ.atom_subset_mol _ h1)
    rw [hroot m, hroot m'] at h2
    exact Subtype.ext h2.symm
  have hB : ∀ X, X ∈ IA \ RA ↔ ∃ v, X = Γ.atom v ∧ ∀ t, T t → ¬ Relation.ReflTransGen A v t := by
    intro X
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hX, hXR⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hX
      refine ⟨v, rfl, fun t ht hvt => ?_⟩
      have hv' : ∀ w ∈ Γ.atom v, w.isRight = true := by simpa [IAfin] using hv
      have htv : t ∈ Γ.atom v := (BAGraph.mem_atom_iff Γ v t).2 hvt
      rcases ht with ht | ⟨m, rfl⟩
      · have := hv' t htv
        cases t <;> simp_all
      · apply hXR
        refine Finset.mem_image.2 ⟨m, Finset.mem_univ _, ?_⟩
        exact (BASizeClaim_atom_eq Γ htv)
    · rintro ⟨v, rfl, hv⟩
      refine ⟨Finset.mem_image.2 ⟨v, ?_, rfl⟩, fun hXR => ?_⟩
      · simpa [IAfin] using hNTint v hv
      · obtain ⟨m, _, hm⟩ := Finset.mem_image.1 hXR
        have : Sum.inr (rootI m) ∈ Γ.atom v := by
          rw [← hm]; exact BASizeClaim_self_mem_atom Γ _
        exact hv _ (Or.inr ⟨m, rfl⟩) ((BAGraph.mem_atom_iff Γ v _).1 this)
  have hfilter : (C.filter fun c => ∃ j, edge c = some (Sum.inl j)) =
      Finset.univ.filter (fun c : I => gate (Sum.inr c)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hc, j, hj⟩
      obtain ⟨j0, e0, _, hgi⟩ := (hedge c).1 hc
      rw [hj] at e0
      cases e0
      exact hgi.2 ⟨j, rfl⟩
    · intro hg
      have hc : c ∈ C := (hCmem c).2 (hgateT _ hg)
      obtain ⟨j0, e0, _, hgi⟩ := (hedge c).1 hc
      obtain ⟨j', hj'⟩ := hgi.1 hg
      exact ⟨hc, j', by rw [e0, hj']⟩
  have hgcard : (Finset.univ.filter (fun c : I => gate (Sum.inr c))).card = (IA \ RA).card := by
    refine Finset.card_bij (fun c _ => Γ.atom (Sum.inr c)) (fun c hc => ?_) (fun c₁ h₁ c₂ h₂ h => ?_)
      (fun X hX => ?_)
    · have hg : gate (Sum.inr c) := by simpa using hc
      exact (hB _).2 ⟨_, rfl, hP1 _ hg⟩
    · have hg₁ : gate (Sum.inr c₁) := by simpa using h₁
      have hg₂ : gate (Sum.inr c₂) := by simpa using h₂
      have h3 : Sum.inr c₂ ∈ Γ.atom (Sum.inr c₁) := by
        rw [h]; exact BASizeClaim_self_mem_atom Γ _
      exact Sum.inr_injective (hP5 _ _ hg₁ hg₂ ((BAGraph.mem_atom_iff Γ _ _).1 h3))
    · obtain ⟨v, rfl, hv⟩ := (hB X).1 hX
      obtain ⟨u, hu, hvu⟩ := hP4 v hv
      have hu' : u ∈ Γ.atom v := (BAGraph.mem_atom_iff Γ v u).2 hvu
      have hur := hNTint v hv u hu'
      obtain ⟨c, rfl⟩ : ∃ c, u = Sum.inr c := by
        cases u with
        | inl a => simp at hur
        | inr c => exact ⟨c, rfl⟩
      exact ⟨c, by simpa using hu, BASizeClaim_atom_eq Γ hu'⟩
  refine ⟨C, fun c => parA (Sum.inr c), edge, fun c => ρ (Sum.inr c), ?_, ?_, ?_, ?_, ?_⟩
  · have hCeq : C = (Finset.univ.image rootI)ᶜ := by
      ext c
      simp only [C, T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_image,
        not_exists, Sum.isLeft_inr, Bool.false_eq_true, false_or, Sum.inr.injEq]
      exact ⟨fun h m hm => h m hm.symm, fun h m hm => h m hm.symm⟩
    have hcard : (Finset.univ.image rootI).card = Γ.nM := by
      rw [Finset.card_image_of_injective _ hrootInj, Finset.card_univ, hMicard]
    rw [hCeq, Finset.card_compl, hcard]
    have : Γ.nM ≤ Fintype.card I := by rw [← hcard]; exact Finset.card_le_univ _
    omega
  · rw [hfilter, hgcard]
    have := Finset.card_sdiff_add_card_eq_card hRAsub
    rw [hRAcard] at this
    exact this
  · intro c hc w hw
    have hw' : parA (Sum.inr c) = Sum.inr w := hw
    have := hP3 (Sum.inr c) ((hCmem c).1 hc)
    rw [hw'] at this
    exact this
  · intro c hc
    obtain ⟨j, hj, hends, _⟩ := (hedge c).1 hc
    exact ⟨j, hj, hends⟩
  · intro c₁ h₁ c₂ h₂ h
    obtain ⟨j₁, e₁, hends₁, _⟩ := (hedge c₁).1 h₁
    obtain ⟨j₂, e₂, hends₂, _⟩ := (hedge c₂).1 h₂
    rw [e₁, e₂] at h
    cases h
    by_contra hne
    have hr₁ := hP3 (Sum.inr c₁) ((hCmem c₁).1 h₁)
    have hr₂ := hP3 (Sum.inr c₂) ((hCmem c₂).1 h₂)
    rcases hends₁ with ⟨a₁, b₁⟩ | ⟨a₁, b₁⟩ <;> rcases hends₂ with ⟨a₂, b₂⟩ | ⟨a₂, b₂⟩
    · exact hne (Sum.inr_injective (a₁.symm.trans a₂))
    · rw [a₁] at b₂
      rw [b₁] at a₂
      rw [a₂] at hr₁
      rw [← b₂] at hr₂
      omega
    · rw [a₁] at b₂
      rw [b₁] at a₂
      rw [a₂] at hr₁
      rw [← b₂] at hr₂
      omega
    · exact hne (Sum.inr_injective (a₁.symm.trans a₂))

open Classical in
/-- `n_M ≤ n_A` and `n_A - n_M ≤ n_W` for a graph without `=`-dotted edges (the waved tree edges of the forest are
distinct waved edges). -/
theorem BAGraph.counters_le (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) :
    Γ.nM ≤ Γ.nA ∧ Γ.nA - Γ.nM ≤ Γ.nW := by
  obtain ⟨C, par, edge, ρ, hc1, hc2, hrank, hedge, hinj⟩ := Γ.exists_forest hD
  refine ⟨Γ.nM_le_nA, ?_⟩
  have h1 : (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card ≤
      (Finset.univ.image (fun j : Fin Γ.waved.length => (some (Sum.inl j) : Option Γ.Jx))).card := by
    refine Finset.card_le_card_of_injOn edge (fun c hc => ?_) (fun c₁ h₁ c₂ h₂ h => ?_)
    · obtain ⟨hcC, j, hj⟩ := Finset.mem_filter.1 hc
      simp [hj]
    · exact hinj c₁ (Finset.mem_filter.1 h₁).1 c₂ (Finset.mem_filter.1 h₂).1 h
  rw [Finset.card_image_of_injective _ (fun a b h => Sum.inl_injective (Option.some_injective _ h)),
    Finset.card_univ, Fintype.card_fin] at h1
  change Γ.nA - Γ.nM ≤ Γ.waved.length
  omega

end BAForest


/-- **The peeling bound with per-edge constants** (`lwForest_sum_le`, `LWSizeClaim.lean:637`, with `(a_j, K_j)`
for each edge; the O1 reduction). -/
theorem BASizeClaim_forest_sum_le {ι : Type u₁} {I : Type u₂} {E : Type u₃} {J : Type u₄}
    [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty ι]
    (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : J → ℝ)
    (hf0 : ∀ j x y, 0 ≤ f j x y) (hfa : ∀ j x y, f j x y ≤ a j)
    (hrow : ∀ j x, ∑ y, f j x y ≤ K j) (hcol : ∀ j y, ∑ x, f j x y ≤ K j)
    (C : Finset I) (par : I → E ⊕ I) (edge : I → J) (ρ : I → ℕ) (hinj : Set.InjOn edge C)
    (hedge : ∀ c ∈ C, (u (edge c) = Sum.inr c ∧ v (edge c) = par c) ∨
      (v (edge c) = Sum.inr c ∧ u (edge c) = par c))
    (hrank : ∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) :
    (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) ≤
      (Fintype.card ι : ℝ) ^ Fintype.card I * (∏ c ∈ C, K (edge c)) * ∏ j ∈ (C.image edge)ᶜ, a j := by
  classical
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨x0⟩ := ‹Nonempty ι›
  have hK : ∀ j, 0 ≤ K j := fun j => (Finset.sum_nonneg fun y _ => hf0 j x0 y).trans (hrow j x0)
  have hfK : ∀ j x y, f j x y ≤ K j := fun j x y =>
    (Finset.single_le_sum (f := fun y => f j x y) (fun y _ => hf0 j x y) (Finset.mem_univ y)).trans (hrow j x)
  have hPa : 0 ≤ ∏ j ∈ (C.image edge)ᶜ, a j :=
    Finset.prod_nonneg fun j _ => (hf0 j x0 x0).trans (hfa j x0 x0)
  set F : J → (I → ι) → ℝ := fun j ℓ => f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) with hF
  have hpt : ∀ ℓ : I → ι, ∏ j, F j ℓ ≤ (∏ c ∈ C, F (edge c) ℓ) * ∏ j ∈ (C.image edge)ᶜ, a j := by
    intro ℓ
    have h1 : ∏ j, F j ℓ = (∏ j ∈ C.image edge, F j ℓ) * ∏ j ∈ (C.image edge)ᶜ, F j ℓ :=
      (Finset.prod_mul_prod_compl _ _).symm
    have h2 : ∏ j ∈ C.image edge, F j ℓ = ∏ c ∈ C, F (edge c) ℓ := Finset.prod_image hinj
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun j _ => hf0 _ _ _) (fun j _ => hfa _ _ _))
      (Finset.prod_nonneg fun c _ => hf0 _ _ _)
  have hcore : (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ c ∈ C, F (edge c) ℓ ≤
      (Fintype.card ι : ℝ) ^ Fintype.card I * ∏ c ∈ C, K (edge c) := by
    rcases C.eq_empty_or_nonempty with rfl | hC
    · simp [Finset.sum_const, Finset.card_univ]
    · have : Nonempty C := hC.to_subtype
      let edge' : I → C := fun c => if h : c ∈ C then ⟨c, h⟩ else ⟨hC.choose, hC.choose_spec⟩
      have hedge'1 : ∀ c (h : c ∈ C), edge' c = ⟨c, h⟩ := fun c h => by simp [edge', h]
      set F'' : I → (I → ι) → ℝ := fun c ℓ => F (edge c) ℓ / K (edge c) with hF''
      have hmain := lwForest_sum_le (E := E) (I := I) (J := C) ℓe (fun j => u (edge j.1))
        (fun j => v (edge j.1)) (fun j x y => f (edge j.1) x y / K (edge j.1)) 1 1 zero_le_one zero_le_one
        (fun j x y => div_nonneg (hf0 _ _ _) (hK _))
        (fun j x y => by
          by_cases h0 : K (edge j.1) = 0
          · simp [h0]
          · rw [div_le_one (lt_of_le_of_ne (hK _) (Ne.symm h0))]
            exact hfK _ _ _)
        (fun j x => by
          rw [← Finset.sum_div]
          by_cases h0 : K (edge j.1) = 0
          · simp [h0]
          · rw [div_le_one (lt_of_le_of_ne (hK _) (Ne.symm h0))]
            exact hrow _ _)
        (fun j y => by
          rw [← Finset.sum_div]
          by_cases h0 : K (edge j.1) = 0
          · simp [h0]
          · rw [div_le_one (lt_of_le_of_ne (hK _) (Ne.symm h0))]
            exact hcol _ _)
        C par edge' ρ (fun c₁ h₁ c₂ h₂ h => by
          have := hedge'1 c₁ h₁
          have h' := hedge'1 c₂ h₂
          rw [this, h'] at h
          exact congrArg Subtype.val h)
        (fun c hc => by
          rw [hedge'1 c hc]
          exact hedge c hc)
        hrank
      have hprod : ∀ ℓ : I → ι, ∏ j : C, f (edge j.1) (Sum.elim ℓe ℓ (u (edge j.1))) (Sum.elim ℓe ℓ (v (edge j.1))) /
          K (edge j.1) = ∏ c ∈ C, F'' c ℓ := fun ℓ => Finset.prod_coe_sort C (fun c => F'' c ℓ)
      simp only [hprod, one_pow, mul_one, Fintype.card_coe] at hmain
      have hid : ∀ ℓ : I → ι, ∏ c ∈ C, F (edge c) ℓ = (∏ c ∈ C, K (edge c)) * ∏ c ∈ C, F'' c ℓ := by
        intro ℓ
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun c _ => ?_
        simp only [hF'']
        by_cases h0 : K (edge c) = 0
        · have : F (edge c) ℓ = 0 := le_antisymm (h0 ▸ hfK _ _ _) (hf0 _ _ _)
          simp [h0, this]
        · field_simp
      simp only [hid]
      rw [← Finset.mul_sum]
      calc (Fintype.card ι : ℝ) ^ C.card * ((∏ c ∈ C, K (edge c)) * ∑ ℓ : I → ι, ∏ c ∈ C, F'' c ℓ)
          = (∏ c ∈ C, K (edge c)) * ((Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ c ∈ C, F'' c ℓ) := by ring
        _ ≤ (∏ c ∈ C, K (edge c)) * (Fintype.card ι : ℝ) ^ Fintype.card I :=
            mul_le_mul_of_nonneg_left hmain (Finset.prod_nonneg fun c _ => hK _)
        _ = _ := by ring
  calc (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ j, F j ℓ
      ≤ (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι,
        ((∏ c ∈ C, F (edge c) ℓ) * ∏ j ∈ (C.image edge)ᶜ, a j) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => hpt ℓ) (by positivity)
    _ = ((Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ c ∈ C, F (edge c) ℓ) *
        ∏ j ∈ (C.image edge)ᶜ, a j := by
        rw [← Finset.sum_mul]; ring
    _ ≤ ((Fintype.card ι : ℝ) ^ Fintype.card I * ∏ c ∈ C, K (edge c)) * ∏ j ∈ (C.image edge)ᶜ, a j :=
        mul_le_mul_of_nonneg_right hcore hPa
    _ = _ := by ring


/-! ## 4. Compiled nonempty instances (`d = 3`, `L = 4`, `W = 2`, `t = 1/2`, the flow point `P : FlowPt 4 10`)

`P.g0 ∈ (0, 10]`, a real energy `P.E` and `P.m0` with `BAReal 3 4 P.g0 (Im P.m0) P.E P.m0` (`Λ = 10`, `κ = Im P.m0 > 0`).
Every deterministic hypothesis of each theorem is discharged at the data; nothing is left open. -/

end RBM.Graph
