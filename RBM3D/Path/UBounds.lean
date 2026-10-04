/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Kernel
import RBM3D.Propagator.Deriv
import RBM3D.Loop.GLoop

/-!
# The `𝒰` bounds: nonnegativity, row sums, `lem:sum_Ndecay` at `n = 2`, back and one-step kernels

Ticket T2097 (ST2-25, part 1).  Port of `RBM2D/Path/UBounds.lean` at commit `c9a24cf` (cited
`UBounds:<line>`).  Paper: arXiv:2507.20274, `lem:sum_Ndecay` (`3_5_Loop_Hierarchy.tex:1620`,
`(sum_res_Ndecay)`, here `n = 2`), `def_Ustz` (`:116`).

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `Z2 L` becomes `Zd d L`; `SB L`, `Theta L`,
`ukerMat L`, `Uop L` become `SB d L g`, `Theta d L g`, `ukerMat d L g`, `Uop d L g` with the
coupling `g` an explicit real parameter (for the model, `g = sz.lam n`); `spectralM` becomes the
merged `mE`, `etaT` the merged `etaT` (`RBM3D/Loop/GLoop.lean:75`).  The statements that RBM2D
pins as `Prop` definitions over `L` keep that form, with the two parameters `(d, g)`.

* `thetaGenMat`, `thetaGen` : the generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰` (`UBounds:48`, `:52`).
* `normSqSpectralMOne` : `|m|² = 1` on `|E| ≤ 2` (`UBounds:416`; `norm_mE`).
* `ukerNonneg` : for real `ξ ≥ 0`, `0 ≤ v ≤ w`, `wξ < 1` the kernel `ukerMat` is entrywise a
  nonnegative real (`UBounds:424`).
* `ukerRowSum` : the row sums are `(1 - vξ)/(1 - wξ)` (`UBounds:445`).
* `sumNdecay`, `sumNdecayEta` : `lem:sum_Ndecay` at `n = 2`, deterministic, constant `1`.
* `uopBack` : `‖𝒰_{t,u} A‖_max ≤ 4 ‖A‖_max`; `uopOneStep` : `‖𝒰_{u,u+Δ} A - A - Δ Θ_u A‖_max
  ≤ 3 Δ² (1-u-Δ)^{-2} ‖A‖_max`.

`d` and `g` enter only through `Theta d L g` and `SB d L g`; the dimension-specific fact of
`UBounds:157` ("`sbKernel` is `1/5`") is replaced by `sbKernelR_nonneg` (the entries are
`(1 + 2dg²)⁻¹` on the diagonal, `g²(1 + 2dg²)⁻¹` on the `2d` neighbours, `0` elsewhere).  The
constants `1`, `4`, `3` are dimension free.  The operator-norm bound for complex `ξ`
(`‖Θ_z‖ ≤ (1 - ‖z‖)⁻¹`) is obtained from the merged `norm_Theta_le` at `z = ‖z‖ · (z/‖z‖)`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open Matrix RBM RBM.Gauss

section Hierarchy

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The per-slot generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰` (the `w`-derivative of `ukerMat`;
`UBounds:48`; `DefTHUST`). -/
def thetaGenMat (ξ : ℂ) (u : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  ξ • (SB d L g * Theta d L g ((u : ℂ) * ξ))

/-- `Θ_{u,(+,-)} ∘ A`, acting on the left in each slot (the generator of `Uop`; `UBounds:52`). -/
def thetaGen (ξ : ℂ) (u : ℝ) (A : Zd d L × Zd d L → ℂ) : Zd d L × Zd d L → ℂ :=
  fun a => ∑ b : Zd d L,
    (thetaGenMat d L g ξ u a.1 b * A (b, a.2) + thetaGenMat d L g ξ u a.2 b * A (a.1, b))

end Hierarchy

/-- **Pin E.1d (one step of `𝒰`)**, the grid form of `∂_w 𝒰_{u,w}|_{w=u} = Θ_u`
(`UBounds:62`): `‖𝒰_{u,u+Δ}A - A - Δ Θ_u A‖_max ≤ 3 Δ² (1-u-Δ)^{-2} ‖A‖_max`. -/
def UopOneStep (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ u Δ : ℝ, 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
    ∀ (A : Zd d L × Zd d L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Zd d L × Zd d L,
      ‖Uop d L g ξ u (u + Δ) A a - A a - (Δ : ℂ) * thetaGen d L g ξ u A a‖ ≤
        3 * Δ ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * α

/-- **Pin E.5a**: `|m|² = 1` on `|E| ≤ 2`, so `Uop` at `ξ = |m|²` is `Uop` at `ξ = 1`
(`UBounds:69`). -/
def NormSqSpectralMOne : Prop :=
  ∀ E : ℝ, |E| ≤ 2 → Complex.normSq (mE E) = 1

/-- **Pin E.5b (nonnegativity)**: for real `ξ ≥ 0`, `0 ≤ v ≤ w`, `wξ < 1`, the kernel
`(1 - vξS)Θ_{wξ} = I + (w-v)ξ SΘ_{wξ}` is real and entrywise `≥ 0` (needs `v ≤ w`;
`UBounds:74`). -/
def UkerNonneg (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ v w : ℝ, 0 ≤ ξ → 0 ≤ v → v ≤ w → w * ξ < 1 →
    ∀ a b : Zd d L, (ukerMat d L g (ξ : ℂ) v w a b).im = 0 ∧ 0 ≤ (ukerMat d L g (ξ : ℂ) v w a b).re

/-- **Pin E.5c (row sums)**: `Σ_b ((1 - vξS)Θ_{wξ})_{ab} = (1 - vξ)/(1 - wξ)` (`UBounds:79`). -/
def UkerRowSum (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ v w : ℝ, 0 ≤ ξ → 0 ≤ w → w * ξ < 1 → ∀ a : Zd d L,
    ∑ b : Zd d L, ukerMat d L g (ξ : ℂ) v w a b = (((1 - v * ξ) / (1 - w * ξ) : ℝ) : ℂ)

/-- **Pin E.5d (`lem:sum_Ndecay`, `n = 2`)**, deterministic with constant 1 (`UBounds:84`). -/
def SumNdecay (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ v w : ℝ, 0 ≤ ξ → 0 ≤ v → v ≤ w → w * ξ < 1 →
    ∀ (A : Zd d L × Zd d L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Zd d L × Zd d L,
      ‖Uop d L g (ξ : ℂ) v w A a‖ ≤ ((1 - v * ξ) / (1 - w * ξ)) ^ 2 * α

/-- **Pin E.5e (`lem:sum_Ndecay` in `η` form)** at `ξ = |m|²`: factor `(η_v/η_w)²`
(`UBounds:90`).  The window is `0 ≤ v ≤ w < 1`, `|E| < 2` (DECISIONS §29: no `w = 1`). -/
def SumNdecayEta (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E v w : ℝ, |E| < 2 → 0 ≤ v → v ≤ w → w < 1 →
    ∀ (A : Zd d L × Zd d L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Zd d L × Zd d L,
      ‖Uop d L g (Complex.normSq (mE E) : ℂ) v w A a‖ ≤ (etaT E v / etaT E w) ^ 2 * α

/-- **Pin E.5i (back-kernel bound)**: `‖𝒰_{t,u} A‖_max ≤ 4 ‖A‖_max` for `0 ≤ u ≤ t < 1`
(`UBounds:97`). -/
def UopBack (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ∀ u t : ℝ, 0 ≤ u → u ≤ t → t < 1 →
    ∀ (A : Zd d L × Zd d L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Zd d L × Zd d L,
      ‖Uop d L g ξ t u A a‖ ≤ 4 * α

/-! ## Helpers (all `private`) -/

section NonnegHelpers

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- `z` is a nonnegative real number, viewed inside `ℂ`; bookkeeping for the sign arguments
(`UBounds:110`; RBM1D `IsRealNonneg`, `Gauss/GridQVConv.lean:38`). -/
private def RealNonneg (z : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)

private theorem RealNonneg.ofNonneg {r : ℝ} (hr : 0 ≤ r) : RealNonneg (r : ℂ) := ⟨r, hr, rfl⟩

private theorem realNonneg_zero : RealNonneg (0 : ℂ) := ⟨0, le_refl _, by simp⟩

private theorem realNonneg_one : RealNonneg (1 : ℂ) := ⟨1, zero_le_one, by simp⟩

private theorem RealNonneg.add {z w : ℂ} (hz : RealNonneg z) (hw : RealNonneg w) :
    RealNonneg (z + w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 + r2, by positivity, by rw [e1, e2]; push_cast; ring⟩

private theorem RealNonneg.mul {z w : ℂ} (hz : RealNonneg z) (hw : RealNonneg w) :
    RealNonneg (z * w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 * r2, mul_nonneg hr1 hr2, by rw [e1, e2]; push_cast; ring⟩

private theorem RealNonneg.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, RealNonneg (f i)) : RealNonneg (∑ i ∈ s, f i) :=
  Finset.sum_induction f RealNonneg (fun _ _ ha hb => ha.add hb) realNonneg_zero h

omit [NeZero L] in
/-- The kernel `S^{(B)}` has nonnegative real entries.  `d ≥ 3`: the entries are
`(1 + 2dg²)⁻¹` (diagonal), `g²(1 + 2dg²)⁻¹` (`2d` neighbours), `0` elsewhere
(`sbKernelR_nonneg`); this replaces `UBounds:157` (the `d = 2` value `1/5`). -/
private theorem SB_realNonneg (a b : Zd d L) : RealNonneg (SB d L g a b) := by
  rw [SB_apply, sbKernel_eq_ofReal]
  exact ⟨_, sbKernelR_nonneg d L g _, rfl⟩

/-- For real `z ∈ [0,1)` the entries of `Θ_z` are nonnegative reals (`UBounds:201`; here from the
merged `Theta_real_eq`, `Theta_real_nonneg`). -/
private theorem Theta_real_realNonneg (hL : 3 ≤ L) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (a b : Zd d L) : RealNonneg (Theta d L g (z : ℂ) a b) :=
  ⟨(Theta d L g (z : ℂ) a b).re, Theta_real_nonneg hL hz0 hz1 a b, Theta_real_eq hL hz0 hz1 a b⟩

private theorem SB_mul_Theta_real_realNonneg (hL : 3 ≤ L) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (a b : Zd d L) : RealNonneg ((SB d L g * Theta d L g (z : ℂ)) a b) := by
  rw [Matrix.mul_apply]
  exact RealNonneg.sum Finset.univ _
    (fun c _ => (SB_realNonneg d L g a c).mul (Theta_real_realNonneg d L g hL hz0 hz1 c b))

end NonnegHelpers

section NormHelpers

/-- `‖(s : ℂ) ξ‖ = s ‖ξ‖` for `s ≥ 0`. -/
private theorem norm_ofReal_mul_eq {s : ℝ} (hs : 0 ≤ s) (ξ : ℂ) : ‖(s : ℂ) * ξ‖ = s * ‖ξ‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]

/-- `‖(s : ℂ) ξ‖ < 1` from `‖ξ‖ ≤ 1` and `0 ≤ s < 1`. -/
private theorem norm_ofReal_mul_lt {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s < 1) : ‖(s : ℂ) * ξ‖ < 1 := by
  rw [norm_ofReal_mul_eq h0]
  calc s * ‖ξ‖ ≤ s * 1 := mul_le_mul_of_nonneg_left hξ h0
    _ = s := mul_one s
    _ < 1 := h1

/-- `‖z‖ = re z` for a complex number with `im z = 0` and `0 ≤ re z`. -/
private theorem norm_eq_re_of {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : ‖z‖ = z.re := by
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  calc ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz
    _ = z.re := Complex.norm_of_nonneg hre

/-- Arithmetic core for the generator: for `r ≤ 1`, `0 ≤ s < 1`,
`r (1 - s r)⁻¹ ≤ (1 - s)⁻¹`. -/
private theorem arith_gen {r s : ℝ} (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    r * (1 - s * r)⁻¹ ≤ (1 - s)⁻¹ := by
  have hsr : s * r ≤ s := mul_le_of_le_one_right hs0 hr1
  have hd : 0 < 1 - s * r := by linarith
  have hd' : 0 < 1 - s := by linarith
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hd hd']
  nlinarith

/-- `(1 - s r)⁻¹ ≤ (1 - s)⁻¹` for `0 ≤ r ≤ 1`, `0 ≤ s < 1`. -/
private theorem arith_inv {r s : ℝ} (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 - s * r)⁻¹ ≤ (1 - s)⁻¹ := by
  have hd' : 0 < 1 - s := by linarith
  refine inv_anti₀ hd' ?_
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hr1)]

end NormHelpers

section KernelIdentity

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The exact form `𝒰`-kernel `= 1 + (w - v) · (ξ S Θ_{wξ})`, from `(1 - wξS) Θ_{wξ} = 1`:
`(1 - vξS) Θ_{wξ} = Θ_{wξ} - vξ SΘ_{wξ} = 1 + (w - v) ξ SΘ_{wξ}` (`UBounds:268`). -/
private theorem ukerMat_eq (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ} (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v w = 1 + ((w : ℂ) - (v : ℂ)) • thetaGenMat d L g ξ w := by
  have h := mul_Theta_of_three_le (d := d) (L := L) (g := g) hL hw
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  unfold ukerMat thetaGenMat
  rw [sub_mul, one_mul, smul_mul_assoc, smul_smul, ← h]
  module

/-- Entrywise form of `ukerMat_eq`. -/
private theorem ukerMat_apply_eq (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ} (hw : ‖(w : ℂ) * ξ‖ < 1)
    (a b : Zd d L) :
    ukerMat d L g ξ v w a b =
      (1 : Matrix (Zd d L) (Zd d L) ℂ) a b + ((w : ℂ) - (v : ℂ)) * thetaGenMat d L g ξ w a b := by
  rw [ukerMat_eq d L g hL hw]
  simp [Matrix.add_apply, Matrix.smul_apply]

/-- Entries of the generator for real `ξ ≥ 0`, `w ≥ 0`, `wξ < 1` are nonnegative reals. -/
private theorem thetaGenMat_realNonneg (hL : 3 ≤ L) {ξ w : ℝ} (hξ : 0 ≤ ξ) (hw : 0 ≤ w)
    (hwξ : w * ξ < 1) (a b : Zd d L) : RealNonneg (thetaGenMat d L g (ξ : ℂ) w a b) := by
  have hz : ((w : ℂ) * (ξ : ℂ)) = ((w * ξ : ℝ) : ℂ) := by push_cast; ring
  have h := SB_mul_Theta_real_realNonneg d L g hL (mul_nonneg hw hξ) hwξ a b
  rw [← hz] at h
  simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul]
  exact (RealNonneg.ofNonneg hξ).mul h

end KernelIdentity

section RowHelpers

variable (d L : ℕ) [NeZero L] (g : ℝ)

open scoped Matrix.Norms.Operator

/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm (as `sum_norm_Theta_row_le`). -/
private theorem sum_norm_row_le_opNorm (M : Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L) :
    ∑ c : Zd d L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Zd d L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Zd d L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Zd d L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- `‖Θ_z‖ ≤ (1 - ‖z‖)⁻¹` for complex `z`, `‖z‖ < 1` (merged `norm_Theta_le` at
`z = ‖z‖ · (z/‖z‖)`; replaces the RBM2D operator-norm bound `norm_Theta_le`, `Propagator/Bounds`). -/
private theorem norm_Theta_le_of_lt (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Theta d L g z‖ ≤ (1 - ‖z‖)⁻¹ := by
  by_cases h0 : z = 0
  · subst h0
    have := norm_Theta_le (d := d) (L := L) (g := g) hL (t := 0) le_rfl zero_lt_one (m := 1)
      (by simp)
    simpa using this
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr h0
    have hm : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm]; exact div_self hn.ne'
    have h := norm_Theta_le (d := d) (L := L) (g := g) hL (t := ‖z‖) hn.le hz hm
    have e : ((‖z‖ : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) = z := by
      have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rwa [e] at h

/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}` (`UBounds:313`; RBM1D `row_bound_edge`,
`Gauss/GridDriftAlgebra.lean:310`). -/
private theorem sum_norm_thetaGenMat_row_le (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ =
      ‖ξ‖ * ‖(SB d L g * Theta d L g ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_norm_row_le_opNorm d L _ x).trans ?_) (norm_nonneg _)
  calc ‖SB d L g * Theta d L g ((s : ℂ) * ξ)‖ ≤ ‖SB d L g‖ * ‖Theta d L g ((s : ℂ) * ξ)‖ :=
      norm_mul_le _ _
    _ = ‖Theta d L g ((s : ℂ) * ξ)‖ := by rw [norm_SB d L g hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := norm_Theta_le_of_lt d L g hL hsξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u`: by the resolvent
identity `Theta_sub_Theta`,
`ξ S Θ_{(u+Δ)ξ} - ξ S Θ_{uξ} = Δ ξ² S Θ_{(u+Δ)ξ} S Θ_{uξ}` (`UBounds:330`; the `hrow_diff` step
of RBM1D `Uker_step`, `Gauss/GridDriftAlgebra.lean:325`). -/
private theorem sum_norm_thetaGenMat_diff_row_le (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hu : ‖(u : ℂ) * ξ‖ < 1) (hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖ ≤
      Δ * ‖ξ‖ ^ 2 * ((1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹) := by
  have hTsub := Theta_sub_Theta d L g (norm_SB d L g hL) (ξ := (u : ℂ) * ξ)
    (ζ := ((u + Δ : ℝ) : ℂ) * ξ) hu hd
  have hcast : ((u + Δ : ℝ) : ℂ) * ξ - (u : ℂ) * ξ = ((Δ : ℝ) : ℂ) * ξ := by
    push_cast; ring
  rw [hcast] at hTsub
  have hM : thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u =
      (((Δ : ℝ) : ℂ) * ξ ^ 2) •
        (SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g *
          Theta d L g ((u : ℂ) * ξ))) := by
    unfold thetaGenMat
    rw [← smul_sub, ← Matrix.mul_sub, hTsub, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  have hnormeq : ∀ c : Zd d L, ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖ =
      Δ * ‖ξ‖ ^ 2 * ‖(SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g *
        Theta d L g ((u : ℂ) * ξ))) x c‖ := by
    intro c
    rw [hM, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hΔ, norm_pow]
  simp_rw [hnormeq]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_norm_row_le_opNorm d L _ x).trans ?_) (by positivity)
  calc ‖SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g * Theta d L g ((u : ℂ) * ξ))‖
      ≤ ‖SB d L g‖ * ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g *
          Theta d L g ((u : ℂ) * ξ)‖ :=
        norm_mul_le _ _
    _ = ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g * Theta d L g ((u : ℂ) * ξ)‖ := by
        rw [norm_SB d L g hL, one_mul]
    _ ≤ ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g‖ * ‖Theta d L g ((u : ℂ) * ξ)‖ :=
        norm_mul_le _ _
    _ ≤ (‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖SB d L g‖) * ‖Theta d L g ((u : ℂ) * ξ)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖Theta d L g ((u : ℂ) * ξ)‖ := by
        rw [norm_SB d L g hL, mul_one]
    _ ≤ (1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹ :=
        mul_le_mul (norm_Theta_le_of_lt d L g hL hd) (norm_Theta_le_of_lt d L g hL hu)
          (norm_nonneg _) (inv_nonneg.mpr (by linarith))

end RowHelpers

section SumHelpers

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- A matrix with row `ℓ¹` norms `≤ R` maps a max-norm bounded vector to a max-norm bounded
one. -/
private theorem norm_sum_mul_le {B : Matrix (Zd d L) (Zd d L) ℂ} {R α : ℝ}
    (hB : ∀ x : Zd d L, ∑ c : Zd d L, ‖B x c‖ ≤ R) (x : Zd d L) {f : Zd d L → ℂ}
    (hf : ∀ b, ‖f b‖ ≤ α) : ‖∑ b : Zd d L, B x b * f b‖ ≤ R * α := by
  have hα : 0 ≤ α := (norm_nonneg _).trans (hf x)
  calc ‖∑ b : Zd d L, B x b * f b‖ ≤ ∑ b : Zd d L, ‖B x b * f b‖ := norm_sum_le _ _
    _ = ∑ b : Zd d L, ‖B x b‖ * ‖f b‖ := by simp only [norm_mul]
    _ ≤ ∑ b : Zd d L, ‖B x b‖ * α :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hf b) (norm_nonneg _)
    _ = (∑ b : Zd d L, ‖B x b‖) * α := (Finset.sum_mul _ _ _).symm
    _ ≤ R * α := mul_le_mul_of_nonneg_right (hB x) hα

/-- The two-slot sum over `Zd d L × Zd d L` as an iterated sum. -/
private theorem sum_prod_eq_iter (P Q : Matrix (Zd d L) (Zd d L) ℂ) (A : Zd d L × Zd d L → ℂ)
    (a : Zd d L × Zd d L) :
    ∑ b : Zd d L × Zd d L, P a.1 b.1 * Q a.2 b.2 * A b =
      ∑ b₁ : Zd d L, P a.1 b₁ * ∑ b₂ : Zd d L, Q a.2 b₂ * A (b₁, b₂) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b₂ _ => by ring

private theorem norm_sum_prod_le {P Q : Matrix (Zd d L) (Zd d L) ℂ} {R R' α : ℝ}
    (hP : ∀ x : Zd d L, ∑ c : Zd d L, ‖P x c‖ ≤ R) (hQ : ∀ x : Zd d L, ∑ c : Zd d L, ‖Q x c‖ ≤ R')
    {A : Zd d L × Zd d L → ℂ} (hA : ∀ b, ‖A b‖ ≤ α) (a : Zd d L × Zd d L) :
    ‖∑ b : Zd d L × Zd d L, P a.1 b.1 * Q a.2 b.2 * A b‖ ≤ R * (R' * α) := by
  rw [sum_prod_eq_iter d L P Q A a]
  exact norm_sum_mul_le d L hP a.1 (fun b₁ => norm_sum_mul_le d L hQ a.2 (fun b₂ => hA (b₁, b₂)))

/-- `Uop` bounded by the square of a uniform row `ℓ¹` bound of `ukerMat`. -/
private theorem norm_Uop_le_of_rows (ξ : ℂ) (v w : ℝ) {R α : ℝ}
    (hR : ∀ x : Zd d L, ∑ c : Zd d L, ‖ukerMat d L g ξ v w x c‖ ≤ R)
    {A : Zd d L × Zd d L → ℂ} (hA : ∀ b, ‖A b‖ ≤ α) (a : Zd d L × Zd d L) :
    ‖Uop d L g ξ v w A a‖ ≤ R ^ 2 * α := by
  calc ‖Uop d L g ξ v w A a‖ ≤ R * (R * α) := norm_sum_prod_le d L hR hR hA a
    _ = R ^ 2 * α := by ring

end SumHelpers

/-! ## The pinned theorems -/

/-- **Pin E.5a**: `|m|² = 1` on `|E| ≤ 2` (`UBounds:416`; from `norm_mE`). -/
theorem normSqSpectralMOne : NormSqSpectralMOne := by
  intro E hE
  rw [Complex.normSq_eq_norm_sq, norm_mE hE]
  norm_num

/-- **Pin E.5b**: `ukerMat` is entrywise a nonnegative real for real `ξ ≥ 0`, `0 ≤ v ≤ w`,
`wξ < 1` (`UBounds:424`; method of RBM1D `Uker_one_nonneg`, `Gauss/GridQVConv.lean:179`, with
`ukerMat = 1 + (w - v) · ξ SΘ_{wξ}`).  Public here; the merged `StepDecompLoop_ukerNonneg`
(T2085, private) is a duplicate. -/
theorem ukerNonneg (d : ℕ) (g : ℝ) : UkerNonneg d g := by
  intro L _ hL ξ v w hξ hv hvw hwξ a b
  have hw0 : 0 ≤ w := hv.trans hvw
  have hwξ0 : 0 ≤ w * ξ := mul_nonneg hw0 hξ
  have hnorm : ‖(w : ℂ) * (ξ : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hwξ0]; exact hwξ
  rw [ukerMat_apply_eq d L g hL hnorm]
  have h1 : RealNonneg ((1 : Matrix (Zd d L) (Zd d L) ℂ) a b) := by
    rw [Matrix.one_apply]
    split_ifs
    · exact realNonneg_one
    · exact realNonneg_zero
  have hc : RealNonneg ((w : ℂ) - (v : ℂ)) :=
    ⟨w - v, by linarith, by push_cast; ring⟩
  have hres := h1.add (hc.mul (thetaGenMat_realNonneg d L g hL hξ hw0 hwξ a b))
  obtain ⟨r, hr, hreq⟩ := hres
  rw [hreq]
  simpa using hr

/-- **Pin E.5c**: the row sums of `ukerMat` are `(1 - vξ)/(1 - wξ)` (`UBounds:445`;
`(1 - vξS)Θ_{wξ} 1`, from `Theta_mulVec_one` and `SB_mulVec_one`). -/
theorem ukerRowSum (d : ℕ) (g : ℝ) : UkerRowSum d g := by
  intro L _ hL ξ v w hξ hw hwξ a
  have hwξ0 : 0 ≤ w * ξ := mul_nonneg hw hξ
  have hnorm : ‖(w : ℂ) * (ξ : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hwξ0]; exact hwξ
  have hmv : ukerMat d L g (ξ : ℂ) v w *ᵥ (1 : Zd d L → ℂ) =
      ((1 - (w : ℂ) * ξ)⁻¹ * (1 - (v : ℂ) * ξ)) • (1 : Zd d L → ℂ) := by
    unfold ukerMat
    rw [← Matrix.mulVec_mulVec, Theta_mulVec_one d L g (norm_SB d L g hL) (SB_mulVec_one d L g hL)
      hnorm, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      SB_mulVec_one d L g hL]
    funext x
    simp [Pi.smul_apply, Pi.sub_apply, mul_comm]
  have h := congrFun hmv a
  simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  have hne : (1 - (w : ℂ) * ξ) ≠ 0 := one_sub_ne_zero hnorm
  push_cast
  field_simp

private theorem ukerMat_row_norm_eq (d L : ℕ) [NeZero L] (g : ℝ) {ξ v w : ℝ} (hL : 3 ≤ L)
    (hξ : 0 ≤ ξ) (hv : 0 ≤ v) (hvw : v ≤ w) (hwξ : w * ξ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖ukerMat d L g (ξ : ℂ) v w x c‖ = (1 - v * ξ) / (1 - w * ξ) := by
  have hn : ∀ c : Zd d L, ‖ukerMat d L g (ξ : ℂ) v w x c‖ = (ukerMat d L g (ξ : ℂ) v w x c).re := by
    intro c
    obtain ⟨him, hre⟩ := ukerNonneg d g L hL ξ v w hξ hv hvw hwξ x c
    exact norm_eq_re_of him hre
  simp_rw [hn]
  have hs := ukerRowSum d g L hL ξ v w hξ (hv.trans hvw) hwξ x
  have hre := congrArg Complex.re hs
  rw [Complex.re_sum, Complex.ofReal_re] at hre
  exact hre

/-- **Pin E.5d (`lem:sum_Ndecay`, `n = 2`)**: `‖𝒰_{v,w} A‖_max ≤ ((1 - vξ)/(1 - wξ))² ‖A‖_max`
(`UBounds:480`); the kernel entries are nonnegative reals (`ukerNonneg`), so the row `ℓ¹` norm is
the row sum (`ukerRowSum`). -/
theorem sumNdecay (d : ℕ) (g : ℝ) : SumNdecay d g := by
  intro L _ hL ξ v w hξ hv hvw hwξ A α hA a
  exact norm_Uop_le_of_rows d L g (ξ : ℂ) v w
    (fun x => (ukerMat_row_norm_eq d L g hL hξ hv hvw hwξ x).le) hA a

/-- `η_v/η_w = (1 - v)/(1 - w)` for `|E| < 2` (`mE_im_pos`; as `Path/Scales.lean:92` of RBM2D). -/
private theorem etaT_div_etaT' {E v w : ℝ} (hE : |E| < 2) :
    etaT E v / etaT E w = (1 - v) / (1 - w) :=
  mul_div_mul_right _ _ (mE_im_pos hE).ne'

/-- **Pin E.5e**: the `η` form of `sumNdecay` at `ξ = |m|² = 1` (`UBounds:486`). -/
theorem sumNdecayEta (d : ℕ) (g : ℝ) : SumNdecayEta d g := by
  intro L _ hL E v w hE hv hvw hw A α hA a
  have h1 : (Complex.normSq (mE E) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [normSqSpectralMOne E hE.le]
  rw [h1, etaT_div_etaT' hE]
  have := sumNdecay d g L hL 1 v w zero_le_one hv hvw (by rwa [mul_one]) A α hA a
  simpa only [mul_one] using this

/-- The row `ℓ¹` norm of the back kernel `(1 - tξS)Θ_{uξ}`, `u ≤ t < 1`, `‖ξ‖ ≤ 1`, is at most
`1 + (t - u)‖ξ‖(1 - u‖ξ‖)⁻¹ ≤ 2` (`UBounds:497`; RBM1D `sum_norm_edgeKer_back_row_le`,
`Hierarchy/UkerBackBound.lean:76`). -/
private theorem sum_norm_ukerMat_back_row_le (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {u t : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖ukerMat d L g ξ t u x c‖ ≤ 2 := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht1
  have hu' : ‖(u : ℂ) * ξ‖ < 1 := norm_ofReal_mul_lt hξ hu0 hu1
  have hrow := sum_norm_thetaGenMat_row_le d L g hL hu' x
  rw [norm_ofReal_mul_eq hu0] at hrow
  have hentry : ∀ c : Zd d L, ‖ukerMat d L g ξ t u x c‖ ≤
      ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) x c‖ + (t - u) * ‖thetaGenMat d L g ξ u x c‖ := by
    intro c
    rw [ukerMat_apply_eq d L g hL hu']
    refine (norm_add_le _ _).trans (add_le_add (le_refl _) (le_of_eq ?_))
    rw [norm_mul]
    congr 1
    rw [show (u : ℂ) - (t : ℂ) = -((t - u : ℝ) : ℂ) by push_cast; ring, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hone : ∑ c : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) x c‖ = 1 := by
    have hc : ∀ c : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) x c‖ = if x = c then 1 else 0 := by
      intro c
      rw [Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [hc]
    rw [Finset.sum_ite_eq]
    simp
  calc ∑ c : Zd d L, ‖ukerMat d L g ξ t u x c‖
      ≤ ∑ c : Zd d L, (‖(1 : Matrix (Zd d L) (Zd d L) ℂ) x c‖ +
          (t - u) * ‖thetaGenMat d L g ξ u x c‖) :=
        Finset.sum_le_sum fun c _ => hentry c
    _ = 1 + (t - u) * ∑ c : Zd d L, ‖thetaGenMat d L g ξ u x c‖ := by
        rw [Finset.sum_add_distrib, hone, Finset.mul_sum]
    _ ≤ 1 + (t - u) * (‖ξ‖ * (1 - u * ‖ξ‖)⁻¹) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrow (by linarith))
    _ ≤ 2 := by
        have hr0 : 0 ≤ ‖ξ‖ := norm_nonneg _
        have hden : 0 < 1 - u * ‖ξ‖ := by
          have : u * ‖ξ‖ ≤ u := mul_le_of_le_one_right hu0 hξ
          linarith
        have htr : t * ‖ξ‖ ≤ t := mul_le_of_le_one_right (hu0.trans hut) hξ
        have hnum : (t - u) * ‖ξ‖ ≤ 1 - u * ‖ξ‖ := by nlinarith
        have : (t - u) * (‖ξ‖ * (1 - u * ‖ξ‖)⁻¹) ≤ 1 := by
          rw [← mul_assoc, ← div_eq_mul_inv]
          exact (div_le_one hden).mpr hnum
        linarith

/-- **Pin E.5i**: the back kernel `𝒰_{t,u}`, `u ≤ t`, has max-norm at most `4` (`UBounds:542`;
RBM1D `norm_Uker_back_le`, `Hierarchy/UkerBackBound.lean:100`). -/
theorem uopBack (d : ℕ) (g : ℝ) : UopBack d g := by
  intro L _ hL ξ hξ u t hu hut ht A α hA a
  have h := norm_Uop_le_of_rows d L g ξ t u
    (fun x => sum_norm_ukerMat_back_row_le d L g hL hξ hu hut ht x) hA a
  calc ‖Uop d L g ξ t u A a‖ ≤ 2 ^ 2 * α := h
    _ = 4 * α := by norm_num

/-- **Pin E.1d**: one step of `𝒰` (`UBounds:553`; RBM1D `Uker_step`,
`Gauss/GridDriftAlgebra.lean:325`, at `n = 2` with the same kernel in both slots): with
`G' = ξ SΘ_{(u+Δ)ξ}` and `G = ξ SΘ_{uξ}`, `ukerMat ξ u (u+Δ) = 1 + Δ G'` and
`𝒰A - A - ΔΘ_u A = Δ ((G'-G)⊗1 + 1⊗(G'-G)) A + Δ² (G'⊗G') A`. -/
theorem uopOneStep (d : ℕ) (g : ℝ) : UopOneStep d g := by
  intro L _ hL ξ hξ u Δ hu hΔ huΔ A α hA a
  have hu1 : u < 1 := by linarith
  have hu' : ‖(u : ℂ) * ξ‖ < 1 := norm_ofReal_mul_lt hξ hu hu1
  have hd' : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := norm_ofReal_mul_lt hξ (by linarith) huΔ
  set G' : Matrix (Zd d L) (Zd d L) ℂ := thetaGenMat d L g ξ (u + Δ) with hG'
  set G : Matrix (Zd d L) (Zd d L) ℂ := thetaGenMat d L g ξ u with hG
  have hK : ∀ x y : Zd d L, ukerMat d L g ξ u (u + Δ) x y =
      (1 : Matrix (Zd d L) (Zd d L) ℂ) x y + (Δ : ℂ) * G' x y := by
    intro x y
    rw [ukerMat_apply_eq d L g hL hd']
    congr 2
    push_cast; ring
  -- the inner sums
  have hin : ∀ b₁ : Zd d L, ∑ b₂ : Zd d L, ukerMat d L g ξ u (u + Δ) a.2 b₂ * A (b₁, b₂) =
      A (b₁, a.2) + (Δ : ℂ) * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂) := by
    intro b₁
    simp only [hK, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]
  have hexp : Uop d L g ξ u (u + Δ) A a = A a
      + (Δ : ℂ) * (∑ b : Zd d L, G' a.1 b * A (b, a.2) + ∑ b : Zd d L, G' a.2 b * A (a.1, b))
      + (Δ : ℂ) ^ 2 * ∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂) := by
    change ∑ b : Zd d L × Zd d L, ukerMat d L g ξ u (u + Δ) a.1 b.1 *
        ukerMat d L g ξ u (u + Δ) a.2 b.2 * A b = _
    rw [sum_prod_eq_iter d L (ukerMat d L g ξ u (u + Δ)) (ukerMat d L g ξ u (u + Δ)) A a]
    simp only [hin]
    have hterm : ∀ b₁ : Zd d L, ukerMat d L g ξ u (u + Δ) a.1 b₁ *
        (A (b₁, a.2) + (Δ : ℂ) * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)) =
        (1 : Matrix (Zd d L) (Zd d L) ℂ) a.1 b₁ * A (b₁, a.2)
        + (Δ : ℂ) * ((1 : Matrix (Zd d L) (Zd d L) ℂ) a.1 b₁ *
            ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂))
        + (Δ : ℂ) * (G' a.1 b₁ * A (b₁, a.2))
        + (Δ : ℂ) ^ 2 * (G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)) := by
      intro b₁
      rw [hK]; ring
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hgen : thetaGen d L g ξ u A a =
      ∑ b : Zd d L, G a.1 b * A (b, a.2) + ∑ b : Zd d L, G a.2 b * A (a.1, b) := by
    unfold thetaGen
    rw [Finset.sum_add_distrib]
  have hdiff : Uop d L g ξ u (u + Δ) A a - A a - (Δ : ℂ) * thetaGen d L g ξ u A a =
      (Δ : ℂ) * (∑ b : Zd d L, (G' - G) a.1 b * A (b, a.2)
          + ∑ b : Zd d L, (G' - G) a.2 b * A (a.1, b))
        + (Δ : ℂ) ^ 2 * ∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂) := by
    rw [hexp, hgen]
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have hβ : 0 < 1 - (u + Δ) := by linarith
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβdef
  have hβ0 : 0 ≤ β := inv_nonneg.mpr hβ.le
  have hnd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ = (u + Δ) * ‖ξ‖ := norm_ofReal_mul_eq (by linarith) ξ
  have hnu : ‖(u : ℂ) * ξ‖ = u * ‖ξ‖ := norm_ofReal_mul_eq hu ξ
  have hR1 : ∀ x : Zd d L, ∑ c : Zd d L, ‖G' x c‖ ≤ β := by
    intro x
    refine (sum_norm_thetaGenMat_row_le d L g hL hd' x).trans ?_
    rw [hnd]
    exact arith_gen hξ (by linarith) huΔ
  have hR2 : ∀ x : Zd d L, ∑ c : Zd d L, ‖(G' - G) x c‖ ≤ Δ * β ^ 2 := by
    intro x
    refine (sum_norm_thetaGenMat_diff_row_le d L g hL hΔ hu' hd' x).trans ?_
    rw [hnd, hnu]
    have h1 : (1 - (u + Δ) * ‖ξ‖)⁻¹ ≤ β := arith_inv hξ (by linarith) huΔ
    have h2 : (1 - u * ‖ξ‖)⁻¹ ≤ β :=
      (arith_inv hξ hu hu1).trans (inv_anti₀ hβ (by linarith))
    have hQ : 0 ≤ (1 - u * ‖ξ‖)⁻¹ := inv_nonneg.mpr (by
      have : u * ‖ξ‖ ≤ u := mul_le_of_le_one_right hu hξ
      linarith)
    have hxi2 : ‖ξ‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖ξ‖ := norm_nonneg _
      nlinarith
    calc Δ * ‖ξ‖ ^ 2 * ((1 - (u + Δ) * ‖ξ‖)⁻¹ * (1 - u * ‖ξ‖)⁻¹)
        ≤ Δ * 1 * (β * β) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hxi2 hΔ) (mul_le_mul h1 h2 hQ hβ0)
            (mul_nonneg (inv_nonneg.mpr (by
              have : (u + Δ) * ‖ξ‖ ≤ u + Δ := mul_le_of_le_one_right (by linarith) hξ
              linarith)) hQ)
            (by positivity)
      _ = Δ * β ^ 2 := by ring
  have hDA : ‖∑ b : Zd d L, (G' - G) a.1 b * A (b, a.2)‖ ≤ Δ * β ^ 2 * α :=
    norm_sum_mul_le d L hR2 a.1 (fun b => hA (b, a.2))
  have hDB : ‖∑ b : Zd d L, (G' - G) a.2 b * A (a.1, b)‖ ≤ Δ * β ^ 2 * α :=
    norm_sum_mul_le d L hR2 a.2 (fun b => hA (a.1, b))
  have hS3 : ‖∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)‖ ≤ β * (β * α) :=
    norm_sum_mul_le d L hR1 a.1 (fun b₁ => norm_sum_mul_le d L hR1 a.2 (fun b₂ => hA (b₁, b₂)))
  rw [hdiff]
  have hnΔ : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_of_nonneg hΔ]
  calc ‖(Δ : ℂ) * (∑ b : Zd d L, (G' - G) a.1 b * A (b, a.2)
          + ∑ b : Zd d L, (G' - G) a.2 b * A (a.1, b))
        + (Δ : ℂ) ^ 2 * ∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)‖
      ≤ Δ * (Δ * β ^ 2 * α + Δ * β ^ 2 * α) + Δ ^ 2 * (β * (β * α)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, hnΔ]
          exact mul_le_mul_of_nonneg_left
            ((norm_add_le _ _).trans (add_le_add hDA hDB)) hΔ
        · rw [norm_mul, norm_pow, hnΔ]
          exact mul_le_mul_of_nonneg_left hS3 (by positivity)
    _ = 3 * Δ ^ 2 * β ^ 2 * α := by ring

/-! ### Compiled nonempty instances (`d = 3`, `L = 3`, `g = 1/2`)

Data: `ξ = 1`, `0 < v = 1/2 < w = 3/4 < 1` for the kernel statements (`wξ = 3/4 < 1`), `E = 0`
(`|E| < 2`, `m = i`), `u = 1/4`, `t = 3/4`, `Δ = 1/4` and `Δ = 1/2` for the one-step bound; every
hypothesis is discharged by `norm_num`.  The tensor `A` is the nonconstant bounded function
`b ↦ 1` on the first diagonal pair and `1/2` elsewhere (`α = 1`). -/

section Instances

/-- A nonconstant tensor with `‖A‖_max = 1`: `A (0,0) = 1`, `A b = 1/2` otherwise. -/
private def instA : Zd 3 3 × Zd 3 3 → ℂ := fun b => if b = (0, 0) then 1 else 1 / 2

private theorem instA_le (b : Zd 3 3 × Zd 3 3) : ‖instA b‖ ≤ 1 := by
  unfold instA
  split_ifs <;> norm_num

/-- Check: the Prop `NormSqSpectralMOne` holds. -/
example : NormSqSpectralMOne := normSqSpectralMOne

/-- Check: `|m^{(0)}|² = 1` (`E = 0`). -/
example : Complex.normSq (mE 0) = 1 := normSqSpectralMOne 0 (by norm_num)

/-- Check: `ukerNonneg` at `d = 3`, `L = 3`, `g = 1/2`, `ξ = 1`, `v = 1/2`, `w = 3/4`. -/
example (a b : Zd 3 3) :
    (ukerMat 3 3 (1 / 2) ((1 : ℝ) : ℂ) (1 / 2) (3 / 4) a b).im = 0 ∧
      0 ≤ (ukerMat 3 3 (1 / 2) ((1 : ℝ) : ℂ) (1 / 2) (3 / 4) a b).re :=
  ukerNonneg 3 (1 / 2) 3 (by norm_num) 1 (1 / 2) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) a b

/-- Check: `ukerRowSum` at `d = 3`, `L = 3`, `g = 1/2`, `ξ = 1`, `v = 1/2`, `w = 3/4` (the row sum
is `2`). -/
example (a : Zd 3 3) :
    ∑ b : Zd 3 3, ukerMat 3 3 (1 / 2) ((1 : ℝ) : ℂ) (1 / 2) (3 / 4) a b =
      (((1 - 1 / 2 * 1) / (1 - 3 / 4 * 1) : ℝ) : ℂ) :=
  ukerRowSum 3 (1 / 2) 3 (by norm_num) 1 (1 / 2) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) a

/-- Check: `sumNdecay` at `d = 3`, `L = 3`, `g = 1/2`, `ξ = 1`, `v = 1/2`, `w = 3/4`, the
nonconstant tensor `instA`, `α = 1`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) ((1 : ℝ) : ℂ) (1 / 2) (3 / 4) instA a‖ ≤
      ((1 - 1 / 2 * 1) / (1 - 3 / 4 * 1)) ^ 2 * 1 :=
  sumNdecay 3 (1 / 2) 3 (by norm_num) 1 (1 / 2) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) instA 1 instA_le a

/-- Check: `sumNdecayEta` at `d = 3`, `L = 3`, `g = 1/2`, `E = 0`, `v = 1/2`, `w = 3/4`, `instA`,
`α = 1`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (Complex.normSq (mE 0) : ℂ) (1 / 2) (3 / 4) instA a‖ ≤
      (etaT 0 (1 / 2) / etaT 0 (3 / 4)) ^ 2 * 1 :=
  sumNdecayEta 3 (1 / 2) 3 (by norm_num) 0 (1 / 2) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) instA 1 instA_le a

/-- Check: `uopBack` at `d = 3`, `L = 3`, `g = 1/2`, `ξ = 1`, `u = 1/4`, `t = 3/4`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (1 : ℂ) (3 / 4) (1 / 4) instA a‖ ≤ 4 * 1 :=
  uopBack 3 (1 / 2) 3 (by norm_num) 1 (by norm_num) (1 / 4) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) instA 1 instA_le a

/-- Check: `uopOneStep` at `d = 3`, `L = 3`, `g = 1/2`, `ξ = 1`, `u = 1/4`, `Δ = 1/4`
(`u + Δ = 1/2`). -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (1 : ℂ) (1 / 4) (1 / 4 + 1 / 4) instA a - instA a -
        ((1 / 4 : ℝ) : ℂ) * thetaGen 3 3 (1 / 2) (1 : ℂ) (1 / 4) instA a‖ ≤
      3 * (1 / 4 : ℝ) ^ 2 * ((1 - (1 / 4 + 1 / 4))⁻¹) ^ 2 * 1 :=
  uopOneStep 3 (1 / 2) 3 (by norm_num) 1 (by norm_num) (1 / 4) (1 / 4) (by norm_num)
    (by norm_num) (by norm_num) instA 1 instA_le a

/-- Check: `uopOneStep` at `Δ = 1/2` (`u + Δ = 3/4`). -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (1 : ℂ) (1 / 4) (1 / 4 + 1 / 2) instA a - instA a -
        ((1 / 2 : ℝ) : ℂ) * thetaGen 3 3 (1 / 2) (1 : ℂ) (1 / 4) instA a‖ ≤
      3 * (1 / 2 : ℝ) ^ 2 * ((1 - (1 / 4 + 1 / 2))⁻¹) ^ 2 * 1 :=
  uopOneStep 3 (1 / 2) 3 (by norm_num) 1 (by norm_num) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) instA 1 instA_le a

/-! ### Boundary instances of the time windows (DECISIONS §29)

`v = w = 0` (`η_0 = 1`, `𝒰 = id`), `v = 0 < w = 999/1000` (`η_w = 10⁻³ Im m`, row sum `1000`),
`u = t = 0`, and the one-step window at `u = 0`, `Δ = 0` and at `u = 0`, `Δ = 999/1000`
(`u + Δ < 1`).  Hypotheses are discharged by `norm_num`; `|E| = 0 < 2`. -/

/-- Boundary: `v = w = 0`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (Complex.normSq (mE 0) : ℂ) 0 0 instA a‖ ≤
      (etaT 0 0 / etaT 0 0) ^ 2 * 1 :=
  sumNdecayEta 3 (1 / 2) 3 (by norm_num) 0 0 0 (by norm_num) le_rfl le_rfl (by norm_num) instA 1
    instA_le a

/-- Boundary: `v = 0`, `w = 999/1000`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (Complex.normSq (mE 0) : ℂ) 0 (999 / 1000) instA a‖ ≤
      (etaT 0 0 / etaT 0 (999 / 1000)) ^ 2 * 1 :=
  sumNdecayEta 3 (1 / 2) 3 (by norm_num) 0 0 (999 / 1000) (by norm_num) le_rfl (by norm_num)
    (by norm_num) instA 1 instA_le a

/-- Boundary: `u = t = 0`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (1 : ℂ) 0 0 instA a‖ ≤ 4 * 1 :=
  uopBack 3 (1 / 2) 3 (by norm_num) 1 (by norm_num) 0 0 le_rfl le_rfl (by norm_num) instA 1
    instA_le a

/-- Boundary: one-step window at `u = 0`, `Δ = 0`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (1 : ℂ) 0 (0 + 0) instA a - instA a -
        ((0 : ℝ) : ℂ) * thetaGen 3 3 (1 / 2) (1 : ℂ) 0 instA a‖ ≤
      3 * (0 : ℝ) ^ 2 * ((1 - (0 + 0))⁻¹) ^ 2 * 1 :=
  uopOneStep 3 (1 / 2) 3 (by norm_num) 1 (by norm_num) 0 0 le_rfl le_rfl (by norm_num) instA 1
    instA_le a

/-- Boundary: one-step window at `u = 0`, `Δ = 999/1000`. -/
example (a : Zd 3 3 × Zd 3 3) :
    ‖Uop 3 3 (1 / 2) (1 : ℂ) 0 (0 + 999 / 1000) instA a - instA a -
        ((999 / 1000 : ℝ) : ℂ) * thetaGen 3 3 (1 / 2) (1 : ℂ) 0 instA a‖ ≤
      3 * (999 / 1000 : ℝ) ^ 2 * ((1 - (0 + 999 / 1000))⁻¹) ^ 2 * 1 :=
  uopOneStep 3 (1 / 2) 3 (by norm_num) 1 (by norm_num) 0 (999 / 1000) le_rfl (by norm_num)
    (by norm_num) instA 1 instA_le a

end Instances

end RBM.Path

end
