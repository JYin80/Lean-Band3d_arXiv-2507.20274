/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWVocab
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWPins
import RBM3D.Propagator.Prop5Short
import RBM3D.Defs.RadialSum
import RBM3D.Defs.Sizes

/-!
# LW-09: `claim:size` (T2124)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (`7_8:line`): `def scaling`
(`7_8:232-255`), `claim:size` (`7_8:264-266`: `Γ ≺ size(Γ)` for every normal graph), the decay
`(eq:estSpm-W)` of
`S^±` (`7_8:260`) and `scalemole` (`7_8:190-193`, used at `7_8:258`: the vertices of a molecule
other than a free one are confined to `O(W (log W)^{3/2})`).  The paper gives no proof of
`claim:size` (T2040 inventory, delta T2040m); this file proves it, in a deterministic form.
Reuses `Graph/LWVocab` (`LGraph`, `LGraph.val`, `Normal`, `partition`, `scalingSize`,
`scalingSizeG`, the molecules), `Graph/LWPins` (`LWPins_lwSp`), `Graph/LWStein` (`lwSplus`) and the
proved `prop5Short_holds` (`(prop:ThfadC_short)`).  No port from RBM1D/RBM2D (nothing to port).

## Target 1: `(eq:estSpm-W)`

Theorems `lwSpOf_decay`, `lwSpOf_decay_E`, `lwKBound_E`, `LWPins_lwSp_decay`, `lwSplus_decay`.
`S = t · svarF` (`lwSmat`), `S^± = S (1 - m² S)⁻¹` (`lwSpOf`; it is `LWPins_lwSp d L W g E t` at
`m = mE E` and `lwSplus sz n t m`).  The formula `S^± = t · Lift(S^{(B)} Θ_{t m²})` (`lwSpOf_eq`,
`Lift(B)_{xy} = W^{-d} B_{[x][y]}`, multiplicative) reduces the bound to the propagator on the
block lattice, and `|S_{xy}|, |S^±_{xy}| ≤ C W^{-d} e^{-c d_B(x,y)}` with `d_B` the periodic `ℓ¹`
distance of the blocks (`lwBdist`), `(C, c)` depending on `(d, Λ, κ)` only, for `0 < g ≤ Λ`,
`0 ≤ t < 1`, `|E| ≤ 2 - κ`, every `L ≥ 3`, `W ≥ 1`.  The row and column sums are `≤ K₁`
(`lwKBound_E`, `LWKBound`).

## Target 2: `scalemole`

Theorems `lwForest_sum_le`, `LGraph.exists_forest`, `LGraph.waved_sum_le`, `lwKernel_tail`,
`lwSpOf_tail_E`, `lwTail_log32`.  The confinement of the non-free vertices to `W (log W)^{3/2}` is
not needed by the deterministic claim: the peeling bound `lwForest_sum_le` (each tree edge of a
forest costs `K₁` through the row and column sums, every other waved edge costs the entry bound
`a`, every root costs `N`) is sharper.  `LGraph.exists_forest` builds the forest of a graph without
`=`-dotted edges: one root per internal molecule, `n_V - n_M` children, distinct tree edges, ranks
by the distance to the roots and the external vertices.  `LGraph.waved_sum_le` is the molecule form
`Σ_{ℓ_I} ∏_{waved} |S-factor| ≤ N^{n_M} K₁^{n_V-n_M} a^{n_W-(n_V-n_M)}`.  The confinement itself is
the tail bound `lwKernel_tail` (`Σ_{d_B ≥ R} |S^±| ≤ C e^{-cR/2}`) and `lwTail_log32`
(`R = (log W)^{3/2}` gives `≤ W^{-D}` eventually).

## Target 3: `claim:size`

Theorems `lwClaimSize`, `lwClaimSizeG`, `lwClaimSize_E`, `lwClaimSizeG_E`.  For a normal graph `Γ`
and data with `M = m I`, the entry bound `|G_{xy}| ≤ Ψ` (`x ≠ y`), `|G_{xx} - m| ≤ Ψ` (hypotheses
on the sample; in the random setting `(GijGEX)`, `(GiiGEX)`), and `S`, `S^±` with entries
`≤ K₀ W^{-d}` and row and column sums `≤ K₁`: `|Γ.val| ≤ C_Γ · size(Γ)` with
`C_Γ = |coeff| K₁^{n_V-n_M} K₀^{n_W-(n_V-n_M)}` (`LGraph.sizeConst`), for every `Ψ ≥ 0`: no `N^τ`
loss, no window.  For a general graph `lwClaimSizeG` bounds by `(Σ_P C_P) · scalingSizeG`;
`lwClaimSize_E` supplies `(K₀, K₁)` from target 1, depending on `(d, Λ, κ)` only.

Section 9 holds the compiled instances at `d = 3`, `L = 4`, `W = 2`.  Paper-delta candidates are
proposed in the report (`T2124a`-`T2124d`).
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

/-! ## 1. Block-constant matrices on the fine lattice -/

section Lift

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The block-constant lift `W^{-d} B_{[x][y]}` of a matrix on the block lattice `Z_L^d` to the fine
lattice `Z_{WL}^d`. -/
def lwLift (B : Matrix (Zd d L) (Zd d L) ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun x y => ((W : ℂ) ^ d)⁻¹ * B (split d L W x).1 (split d L W y).1

/-- Summing a function of the block over the fine lattice multiplies by the block size `W^d`. -/
private theorem lwSum_split_fst (f : Zd d L → ℂ) :
    ∑ z : Idx d L W, f (split d L W z).1 = (W : ℂ) ^ d * ∑ c : Zd d L, f c := by
  rw [Fintype.sum_equiv (splitEquiv d L W) (fun z : Idx d L W => f (split d L W z).1)
    (fun p : Vtx d L W => f p.1) (fun z => rfl), Fintype.sum_prod_type]
  simp [Finset.sum_const, Fintype.card_fin, Finset.mul_sum]

theorem lwLift_mul (A B : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W A * lwLift d L W B = lwLift d L W (A * B) := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  ext x y
  simp only [lwLift, Matrix.mul_apply, Matrix.of_apply]
  have h := lwSum_split_fst d L W (fun c => A (split d L W x).1 c * B c (split d L W y).1)
  calc ∑ z, ((W : ℂ) ^ d)⁻¹ * A (split d L W x).1 (split d L W z).1 *
        (((W : ℂ) ^ d)⁻¹ * B (split d L W z).1 (split d L W y).1)
      = (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ z, A (split d L W x).1 (split d L W z).1 *
        B (split d L W z).1 (split d L W y).1 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => by ring
    _ = _ := by rw [h]; field_simp

private theorem lwLift_add (A B : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (A + B) = lwLift d L W A + lwLift d L W B := by
  ext x y; simp [lwLift, mul_add]

private theorem lwLift_sub (A B : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (A - B) = lwLift d L W A - lwLift d L W B := by
  ext x y; simp [lwLift, mul_sub]

private theorem lwLift_smul (c : ℂ) (A : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (c • A) = c • lwLift d L W A := by
  ext x y; simp [lwLift]; ring

end Lift

/-! ## 2. `S` and `S^±` on the fine lattice: the lift of `S^{(B)} Θ` -/

section Splus

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `S = t · svarF` (the variance matrix of `H_t = √t X`, `7_8:136`) as a complex matrix. -/
def lwSmat (g t : ℝ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun x y => ((t * svarF d L W g x y : ℝ) : ℂ)

/-- `S^± = S (1 - m² S)⁻¹` (`(eq:def-Spm)`) for `S = t · svarF`. -/
def lwSpOf (g t : ℝ) (m : ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  lwSmat d L W g t * Ring.inverse (1 - m ^ 2 • lwSmat d L W g t)

theorem lwSmat_eq (g t : ℝ) : lwSmat d L W g t = (t : ℂ) • lwLift d L W (SB d L g) := by
  ext x y
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  simp only [lwSmat, lwLift, Matrix.of_apply, Matrix.smul_apply, svarF, SB_apply,
    sbKernel_eq_ofReal, SBR, smul_eq_mul]
  push_cast
  ring

/-- `LWPins_lwSp` is `lwSpOf` at `m = mE E`. -/
theorem LWPins_lwSp_eq (g E t : ℝ) :
    LWPins_lwSp d L W g E t = lwSpOf d L W g t (mE E) := by
  have h : Matrix.of (LWPins_lwS d L W g t) = lwSmat d L W g t := by
    ext x y
    simp [LWPins_lwS, lwSmat]
  simp only [LWPins_lwSp, lwSpOf, h]

variable {d L W} in
/-- The merged `lwSplus` is `lwSpOf` (same size data). -/
theorem lwSplus_eq (sz : Sizes d) (n : ℕ) (u : ℝ) (m : ℂ) :
    lwSplus sz n u m = lwSpOf d (sz.L n) (sz.W n) (sz.lam n) u m := by
  rfl

private theorem lwLift_zero : lwLift d L W (0 : Matrix (Zd d L) (Zd d L) ℂ) = 0 := by
  ext x y; simp [lwLift]

/-- **The formula** `S^± = t · Lift(S^{(B)} Θ_{t m²})`: with `Lift(B)_{xy} = W^{-d} B_{[x][y]}`
multiplicative, `(1 - m² S)⁻¹ = 1 + Lift(Θ - 1)` for `S = t Lift(S^{(B)})`. -/
theorem lwSpOf_eq (hL : 3 ≤ L) {g t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {m : ℂ} (hm : ‖m‖ = 1) :
    lwSpOf d L W g t m =
      (t : ℂ) • lwLift d L W (SB d L g * Theta d L g ((t : ℂ) * m ^ 2)) := by
  set ξ : ℂ := (t : ℂ) * m ^ 2 with hξdef
  have hξ : ‖ξ‖ < 1 := by
    simp [hξdef, norm_pow, hm, abs_of_nonneg ht0, ht1]
  set Θ := Theta d L g ξ with hΘ
  have h1 : (1 - ξ • SB d L g) * Θ = 1 := mul_Theta_of_three_le hL hξ
  have hSm := lwSmat_eq d L W g t
  set LSB := lwLift d L W (SB d L g) with hLSB
  have hA : 1 - m ^ 2 • lwSmat d L W g t = 1 - ξ • LSB := by
    rw [hSm, smul_smul]
    congr 2
    rw [hξdef]; ring
  set R : Matrix (Idx d L W) (Idx d L W) ℂ := 1 + lwLift d L W (Θ - 1) with hR
  have hX : Θ - 1 - ξ • SB d L g - ξ • (SB d L g * (Θ - 1)) = 0 := by
    have : Θ - 1 - ξ • SB d L g - ξ • (SB d L g * (Θ - 1)) = (1 - ξ • SB d L g) * Θ - 1 := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, smul_sub, one_mul, mul_one]
      abel
    rw [this, h1, sub_self]
  have hAR : (1 - ξ • LSB) * R = 1 := by
    have : (1 - ξ • LSB) * R =
        1 + lwLift d L W (Θ - 1 - ξ • SB d L g - ξ • (SB d L g * (Θ - 1))) := by
      rw [lwLift_sub, lwLift_sub, lwLift_smul, lwLift_smul, ← lwLift_mul, hR]
      simp only [sub_mul, mul_add, smul_mul_assoc, one_mul, mul_one]
      abel
    rw [this, hX, lwLift_zero, add_zero]
  have hRA : R * (1 - ξ • LSB) = 1 := mul_eq_one_comm.1 hAR
  have hu : IsUnit (1 - ξ • LSB) := ⟨⟨_, R, hAR, hRA⟩, rfl⟩
  have hinv : Ring.inverse (1 - ξ • LSB) = R := by
    calc Ring.inverse (1 - ξ • LSB) = Ring.inverse (1 - ξ • LSB) * ((1 - ξ • LSB) * R) := by
          rw [hAR, mul_one]
      _ = (Ring.inverse (1 - ξ • LSB) * (1 - ξ • LSB)) * R := by rw [mul_assoc]
      _ = R := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
  unfold lwSpOf
  rw [hA, hinv, hSm, hR, smul_mul_assoc, mul_add, mul_one, hLSB, lwLift_mul, ← lwLift_add]
  congr 2
  simp only [mul_sub, mul_one]
  abel

end Splus

/-! ## 3. Target 1: `(eq:estSpm-W)`, the decay of `S` and `S^±` -/

section Decay

variable {d L : ℕ} [NeZero L]

private theorem lwNorm_SB (g : ℝ) (a c : Zd d L) : ‖SB d L g a c‖ = sbKernelR d L g (a - c) := by
  rw [SB_apply, sbKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sbKernelR_nonneg d L g _)]

private theorem lwSum_sbKernelR (g : ℝ) (hL : 3 ≤ L) (a : Zd d L) :
    ∑ c : Zd d L, sbKernelR d L g (a - c) = 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun c => rfl

private theorem lwSBR_support (g : ℝ) {x : Zd d L} (h : sbKernelR d L g x ≠ 0) : zdistD d L x ≤ 1 := by
  by_contra hx
  push Not at hx
  apply h
  have h0 : x ≠ 0 := by
    rintro rfl; simp at hx
  simp [sbKernelR, h0, show zdistD d L x ≠ 1 by omega]

/-- The block-level bound: `|(S^{(B)} Θ)_{ab}| ≤ C₀ e^{-c |a-b|}` from the short-range propagator
bound `Θ(0,a) ≤ C_s (1_{a=0} + g² e^{-c_s |a|})` (`prop5Short_holds`); `S^{(B)}` is stochastic with
range one. -/
private theorem lwSBTheta_bound {Λ κ Cs cs : ℝ} (hCs : 0 < Cs) (hcs : 0 < cs)
    (hΘ : ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta d L g ((t : ℂ) * m ^ 2) 0 a‖
          ≤ Cs * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-cs * (zdistD d L a : ℝ))))
    (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {m : ℂ}
    (hm : ‖m‖ = 1) (hmi : κ ≤ m.im) (a b : Zd d L) :
    ‖(SB d L g * Theta d L g ((t : ℂ) * m ^ 2)) a b‖ ≤
      (1 + Λ ^ 2) * Cs * Real.exp cs * Real.exp (-(cs * (zdistD d L (a - b) : ℝ))) := by
  have hξ : ‖(t : ℂ) * m ^ 2‖ < 1 := by
    simp [norm_pow, hm, abs_of_nonneg ht0, ht1]
  have hΛ2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ c, ‖SB d L g a c * Theta d L g ((t : ℂ) * m ^ 2) c b‖
      ≤ ∑ c, sbKernelR d L g (a - c) *
          ((1 + Λ ^ 2) * Cs * Real.exp cs * Real.exp (-(cs * (zdistD d L (a - b) : ℝ)))) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, lwNorm_SB]
        by_cases hc : sbKernelR d L g (a - c) = 0
        · simp [hc]
        refine mul_le_mul_of_nonneg_left ?_ (sbKernelR_nonneg d L g _)
        have hs := lwSBR_support g hc
        have hT : Theta d L g ((t : ℂ) * m ^ 2) c b = Theta d L g ((t : ℂ) * m ^ 2) 0 (b - c) := by
          have := Theta_apply_add_right_of_three_le (d := d) (L := L) (g := g) hL hξ 0 (b - c) c
          simpa using this
        rw [hT]
        refine (hΘ L hL g hg hgΛ t ht0 ht1 m hm hmi (b - c)).trans ?_
        have h1 : zdistD d L (a - b) ≤ zdistD d L (b - c) + 1 := by
          have := zdistD_add_le d L (a - c) (c - b)
          have h2 : zdistD d L (c - b) = zdistD d L (b - c) := by
            rw [← zdistD_neg d L (c - b)]; simp
          have h3 : a - c + (c - b) = a - b := by ring
          rw [h3] at this
          omega
        have h2 : Real.exp (-cs * (zdistD d L (b - c) : ℝ)) ≤
            Real.exp cs * Real.exp (-(cs * (zdistD d L (a - b) : ℝ))) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          have : (zdistD d L (a - b) : ℝ) ≤ zdistD d L (b - c) + 1 := by exact_mod_cast h1
          nlinarith
        have h3 : (if b - c = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-cs * (zdistD d L (b - c) : ℝ)) ≤
            (1 + Λ ^ 2) * Real.exp (-cs * (zdistD d L (b - c) : ℝ)) := by
          by_cases h0 : b - c = 0
          · simp [h0]; nlinarith
          · simp only [h0, ite_false, zero_add]
            have := Real.exp_pos (-cs * (zdistD d L (b - c) : ℝ))
            nlinarith
        calc Cs * ((if b - c = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-cs * (zdistD d L (b - c) : ℝ)))
            ≤ Cs * ((1 + Λ ^ 2) * Real.exp (-cs * (zdistD d L (b - c) : ℝ))) :=
              mul_le_mul_of_nonneg_left h3 hCs.le
          _ ≤ Cs * ((1 + Λ ^ 2) * (Real.exp cs * Real.exp (-(cs * (zdistD d L (a - b) : ℝ))))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hCs.le
          _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul, lwSum_sbKernelR g hL a, one_mul]

/-- The block distance of two fine-lattice points: the periodic `ℓ¹` distance of their blocks. -/
def lwBdist (d L W : ℕ) [NeZero L] [NeZero W] (x y : Idx d L W) : ℕ :=
  zdistD d L ((split d L W x).1 - (split d L W y).1)

theorem lwBdist_comm (d L W : ℕ) [NeZero L] [NeZero W] (x y : Idx d L W) :
    lwBdist d L W x y = lwBdist d L W y x := by
  unfold lwBdist
  rw [← zdistD_neg d L ((split d L W x).1 - (split d L W y).1)]
  simp

variable {W : ℕ} [NeZero W]

private theorem lwSpOf_entry_eq (hL : 3 ≤ L) {g t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {m : ℂ} (hm : ‖m‖ = 1)
    (x y : Idx d L W) :
    ‖lwSpOf d L W g t m x y‖ = t * ((W : ℝ) ^ d)⁻¹ *
      ‖(SB d L g * Theta d L g ((t : ℂ) * m ^ 2)) (split d L W x).1 (split d L W y).1‖ := by
  rw [lwSpOf_eq d L W hL ht0 ht1 hm]
  simp only [Matrix.smul_apply, lwLift, Matrix.of_apply, smul_eq_mul, norm_mul, norm_inv, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  ring

private theorem lwSBR_le_one (g : ℝ) (hL : 3 ≤ L) (x : Zd d L) : sbKernelR d L g x ≤ 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Finset.single_le_sum (f := fun y => sbKernelR d L g y) (fun y _ => sbKernelR_nonneg d L g y)
    (Finset.mem_univ x)

private theorem lwSmat_entry {g t : ℝ} (ht0 : 0 ≤ t) (x y : Idx d L W) :
    ‖lwSmat d L W g t x y‖ = t * ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g ((split d L W x).1 - (split d L W y).1) := by
  simp only [lwSmat, Matrix.of_apply, Complex.norm_real, Real.norm_eq_abs, svarF, SBR]
  rw [abs_of_nonneg (mul_nonneg ht0 (mul_nonneg (by positivity) (sbKernelR_nonneg d L g _)))]
  ring

/-- **Target 1, `(eq:estSpm-W)`** (`7_8:` `S^±_{xy} ≤ C W^{-d} e^{-c|x-y|/W}`, `A:` `lem_propTH`) on the
fine lattice with the block distance: for `0 < g ≤ Λ`, `0 ≤ t < 1`, `L ≥ 3`, `W ≥ 1`, and every
`‖m‖ = 1`, `Im m ≥ κ`, the matrices `S = t · svarF` and `S^± = S (1 - m² S)⁻¹` satisfy
`|S_{xy}|, |S^±_{xy}| ≤ C W^{-d} e^{-c d_B(x,y)}` with `(C, c)` depending on `(d, Λ, κ)` only.
From the proved `prop5Short_holds` (`(prop:ThfadC_short)`). -/
theorem lwSpOf_decay (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 →
        (∀ x y : Idx d L W, ‖lwSmat d L W g t x y‖ ≤
            C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ x y : Idx d L W, ‖lwSpOf d L W g t m x y‖ ≤
            C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
  obtain ⟨Cs, hCs, cs, hcs, h5⟩ := prop5Short_holds d Λ κ hd hΛ hκ
  refine ⟨max ((1 + Λ ^ 2) * Cs * Real.exp cs) (Real.exp cs), cs, lt_max_of_lt_right (Real.exp_pos _), hcs,
    fun L W _ _ hL g t hg hgΛ ht0 ht1 => ⟨fun x y => ?_, fun m hm hmi x y => ?_⟩⟩
  · rw [lwSmat_entry ht0]
    have hW : 0 < ((W : ℝ) ^ d)⁻¹ := by
      have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
      positivity
    have he := Real.exp_pos (-(cs * (lwBdist d L W x y : ℝ)))
    have hmax : Real.exp cs ≤ max ((1 + Λ ^ 2) * Cs * Real.exp cs) (Real.exp cs) := le_max_right _ _
    set a := (split d L W x).1 - (split d L W y).1 with ha
    by_cases h0 : sbKernelR d L g a = 0
    · rw [h0, mul_zero]; positivity
    · have hs := lwSBR_le_one g hL a
      have hs1 := lwSBR_support g h0
      have h1 : 1 ≤ Real.exp cs * Real.exp (-(cs * (lwBdist d L W x y : ℝ))) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have : (lwBdist d L W x y : ℝ) ≤ 1 := by exact_mod_cast hs1
        nlinarith
      have h2 : t * ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g a ≤ ((W : ℝ) ^ d)⁻¹ := by
        have := mul_le_mul (mul_le_mul ht1.le le_rfl hW.le zero_le_one) hs
          (sbKernelR_nonneg d L g a) (by positivity)
        linarith
      calc t * ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g a ≤ ((W : ℝ) ^ d)⁻¹ := h2
        _ ≤ ((W : ℝ) ^ d)⁻¹ * (Real.exp cs * Real.exp (-(cs * (lwBdist d L W x y : ℝ)))) := by
            nlinarith
        _ ≤ max ((1 + Λ ^ 2) * Cs * Real.exp cs) (Real.exp cs) * ((W : ℝ) ^ d)⁻¹ *
              Real.exp (-(cs * (lwBdist d L W x y : ℝ))) := by
            have : ((W : ℝ) ^ d)⁻¹ * (Real.exp cs * Real.exp (-(cs * (lwBdist d L W x y : ℝ)))) =
                (Real.exp cs * ((W : ℝ) ^ d)⁻¹) * Real.exp (-(cs * (lwBdist d L W x y : ℝ))) := by ring
            rw [this]
            gcongr
  · rw [lwSpOf_entry_eq hL ht0 ht1 hm]
    have hW : 0 < ((W : ℝ) ^ d)⁻¹ := by
      have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
      positivity
    have hB := lwSBTheta_bound (κ := κ) hCs hcs
      (fun L hL g hg hgΛ t ht0 ht1 m hm hmi a => by
        have := h5 L hL g hg hgΛ t ht0 ht1 m hm hmi true a
        simpa [PropSpin, sq] using this) hL hg hgΛ ht0 ht1 hm hmi (split d L W x).1 (split d L W y).1
    have hmax : (1 + Λ ^ 2) * Cs * Real.exp cs ≤ max ((1 + Λ ^ 2) * Cs * Real.exp cs) (Real.exp cs) :=
      le_max_left _ _
    have he := Real.exp_pos (-(cs * (lwBdist d L W x y : ℝ)))
    have hB' : ‖(SB d L g * Theta d L g ((t : ℂ) * m ^ 2)) (split d L W x).1 (split d L W y).1‖ ≤
        max ((1 + Λ ^ 2) * Cs * Real.exp cs) (Real.exp cs) * Real.exp (-(cs * (lwBdist d L W x y : ℝ))) :=
      hB.trans (by unfold lwBdist; gcongr)
    calc t * ((W : ℝ) ^ d)⁻¹ * ‖(SB d L g * Theta d L g ((t : ℂ) * m ^ 2)) (split d L W x).1 (split d L W y).1‖
        ≤ 1 * ((W : ℝ) ^ d)⁻¹ * (max ((1 + Λ ^ 2) * Cs * Real.exp cs) (Real.exp cs) *
            Real.exp (-(cs * (lwBdist d L W x y : ℝ)))) := by
          apply mul_le_mul (mul_le_mul ht1.le le_rfl hW.le zero_le_one) hB' (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- A weight matrix `K` on a finite label set with entries `≤ a`, and row sums and column sums
`≤ K₁` (of the entry norms): the three facts about `S` and `S^±` that `claim:size` uses. -/
def LWKBound {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) (a K₁ : ℝ) : Prop :=
  (∀ x y, ‖K x y‖ ≤ a) ∧ (∀ x, ∑ y, ‖K x y‖ ≤ K₁) ∧ (∀ y, ∑ x, ‖K x y‖ ≤ K₁)

private theorem lwSum_split_fst_real (f : Zd d L → ℝ) :
    ∑ z : Idx d L W, f (split d L W z).1 = (W : ℝ) ^ d * ∑ c : Zd d L, f c := by
  rw [Fintype.sum_equiv (splitEquiv d L W) (fun z : Idx d L W => f (split d L W z).1)
    (fun p : Vtx d L W => f p.1) (fun z => rfl), Fintype.sum_prod_type]
  simp [Finset.sum_const, Fintype.card_fin, Finset.mul_sum]

/-- Row sums of a kernel with the entry decay of `(eq:estSpm-W)`: `Σ_y W^{-d} e^{-c d_B(x,y)} ≤
expC(d-2, c)` (`W^d` points per block, `Σ_{b ∈ Z_L^d} e^{-c|b|} ≤ expC`). -/
private theorem lwSum_decay_row (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c) (x : Idx d L W) :
    ∑ y : Idx d L W, ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ≤ expC (d - 2) c := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hW : (0 : ℝ) < ((W : ℝ) ^ (k + 2)) := by
    have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  rw [← Finset.mul_sum]
  have h1 := lwSum_split_fst_real (d := k + 2) (L := L) (W := W)
    (fun b => Real.exp (-(c * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))))
  simp only [lwBdist]
  rw [h1]
  have h2 : ∑ b : Zd (k + 2) L, Real.exp (-(c * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))) ≤
      expC k c := by
    refine le_trans (le_of_eq ?_) (sum_radial_exp_decay_le (L := L) k hc)
    exact Fintype.sum_equiv (Equiv.subLeft _) _ _ fun b => rfl
  calc ((W : ℝ) ^ (k + 2))⁻¹ * ((W : ℝ) ^ (k + 2) * ∑ b : Zd (k + 2) L,
        Real.exp (-(c * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))))
      = ∑ b : Zd (k + 2) L, Real.exp (-(c * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))) := by
        field_simp
    _ ≤ expC k c := h2

/-- The row and column sums of a kernel with the entry decay of `(eq:estSpm-W)`. -/
theorem lwKBound_of_decay (hd : 3 ≤ d) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : ∀ x y, ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) :
    LWKBound K (C * ((W : ℝ) ^ d)⁻¹) (C * expC (d - 2) c) := by
  have hW : (0 : ℝ) < ((W : ℝ) ^ d)⁻¹ := by
    have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · refine (h x y).trans ?_
    have : Real.exp (-(c * (lwBdist d L W x y : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ c * (lwBdist d L W x y : ℝ) := by positivity
      linarith
    nlinarith [Real.exp_pos (-(c * (lwBdist d L W x y : ℝ))), mul_nonneg hC hW.le]
  · calc ∑ y, ‖K x y‖ ≤ ∑ y, C * (((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) :=
          Finset.sum_le_sum fun y _ => by have := h x y; linarith
      _ = C * ∑ y, ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ C * expC (d - 2) c := mul_le_mul_of_nonneg_left (lwSum_decay_row hd hc x) hC
  · calc ∑ x, ‖K x y‖ ≤ ∑ x, C * (((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W y x : ℝ)))) :=
          Finset.sum_le_sum fun x _ => by
            have := h x y; rw [lwBdist_comm] at this; linarith
      _ = C * ∑ x, ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W y x : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ C * expC (d - 2) c := mul_le_mul_of_nonneg_left (lwSum_decay_row hd hc y) hC

/-- In the bulk `|E| ≤ 2 - κ` the imaginary part of `m(E)` is at least `κ/2`. -/
private theorem lwIm_mE_ge {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.1 hE]) (abs_le.1 hE).2
    nlinarith [abs_le.1 hE, sq_abs E]
  have h4 : κ ^ 2 ≤ 4 - E ^ 2 := by nlinarith
  have : κ ≤ Real.sqrt (4 - E ^ 2) := Real.le_sqrt_of_sq_le h4
  linarith

/-- **Target 1 on the energy `E`** (`|E| ≤ 2 - κ`, `m = m(E)`): the entries of `S = t · svarF` and of
`S^± = S (1 - m(E)² S)⁻¹` are `≤ C W^{-d} e^{-c d_B}`, `(C, c)` depending on `(d, Λ, κ)` only, for every
`L ≥ 3`, `W ≥ 1`, `0 < g ≤ Λ`, `0 ≤ t < 1`. -/
theorem lwSpOf_decay_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
        (∀ x y : Idx d L W, ‖lwSmat d L W g t x y‖ ≤
            C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧
        ∀ x y : Idx d L W, ‖lwSpOf d L W g t (mE E) x y‖ ≤
            C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay d hd Λ (κ / 2) hΛ (by linarith)
  refine ⟨C, c, hC, hc, fun L W _ _ hL g t E hg hgΛ ht0 ht1 hE => ?_⟩
  obtain ⟨h1, h2⟩ := h L W hL g t hg hgΛ ht0 ht1
  exact ⟨h1, h2 (mE E) (norm_mE (by linarith [abs_nonneg E])) (lwIm_mE_ge hκ hE)⟩

/-- Target 1 with the row and column sums: the constants `(K₀, K₁)` of `LWKBound` for `S` and for
`S^± = S (1 - m(E)² S)⁻¹`, depending on `(d, Λ, κ)` only. -/
theorem lwKBound_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
        LWKBound (lwSmat d L W g t) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
        LWKBound (lwSpOf d L W g t (mE E)) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E d hd Λ κ hΛ hκ
  have hE : 0 < expC (d - 2) c := by
    unfold expC
    have : 0 < c := hc
    positivity
  refine ⟨C, C * expC (d - 2) c, hC, mul_pos hC hE, fun L W _ _ hL g t E hg hgΛ ht0 ht1 hEκ => ?_⟩
  obtain ⟨h1, h2⟩ := h L W hL g t E hg hgΛ ht0 ht1 hEκ
  exact ⟨lwKBound_of_decay hd hC.le hc h1, lwKBound_of_decay hd hC.le hc h2⟩

end Decay

/-! ## 4. The peeling bound (`scalemole`) -/

section Forest

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

omit [Fintype ι] [DecidableEq ι] [Fintype I] in
private theorem lwSplit_symm_update (a : I) (x y : ι) (ℓ' : {j // j ≠ a} → ι) :
    (Equiv.funSplitAt a ι).symm (x, ℓ') = Function.update ((Equiv.funSplitAt a ι).symm (y, ℓ')) a x := by
  funext j
  by_cases h : j = a
  · subst h; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

/-- Summing out one coordinate: if `G` and `H` do not depend on the coordinate `a` (apart from
the explicit `H`-slot), then `N Σ_ℓ G ℓ H(ℓ a, ℓ) ≤ K Σ_ℓ G ℓ` when `Σ_x H(x, ℓ) ≤ K`. -/
private theorem lwSum_sep [Nonempty ι] (a : I) (G : (I → ι) → ℝ) (H : ι → (I → ι) → ℝ) (K : ℝ)
    (hG : ∀ ℓ x, G (Function.update ℓ a x) = G ℓ)
    (hH : ∀ ℓ x x', H x' (Function.update ℓ a x) = H x' ℓ)
    (hGnn : ∀ ℓ, 0 ≤ G ℓ) (hK : ∀ ℓ, ∑ x, H x ℓ ≤ K) :
    (Fintype.card ι : ℝ) * ∑ ℓ, G ℓ * H (ℓ a) ℓ ≤ K * ∑ ℓ, G ℓ := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  set e := Equiv.funSplitAt a ι with he
  have hG' : ∀ x ℓ', G (e.symm (x, ℓ')) = G (e.symm (x₀, ℓ')) := fun x ℓ' => by
    rw [lwSplit_symm_update a x x₀ ℓ', hG]
  have hH' : ∀ x x' ℓ', H x' (e.symm (x, ℓ')) = H x' (e.symm (x₀, ℓ')) := fun x x' ℓ' => by
    rw [lwSplit_symm_update a x x₀ ℓ', hH]
  have hsym : ∀ x ℓ', (e.symm (x, ℓ')) a = x := fun x ℓ' => by
    simp [he, Equiv.funSplitAt, Equiv.piSplitAt]
  have h1 : ∑ ℓ, G ℓ * H (ℓ a) ℓ =
      ∑ ℓ' : {j // j ≠ a} → ι, G (e.symm (x₀, ℓ')) * ∑ x, H x (e.symm (x₀, ℓ')) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsym, hG', hH' x x ℓ']
  have h2 : ∑ ℓ, G ℓ = (Fintype.card ι : ℝ) * ∑ ℓ' : {j // j ≠ a} → ι, G (e.symm (x₀, ℓ')) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [hG']
    simp [Finset.sum_const, Finset.card_univ]
  rw [h1, h2, ← mul_assoc, mul_comm K, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ' _ => ?_
  rw [mul_comm K]
  exact mul_le_mul_of_nonneg_left (hK _) (hGnn _)


variable {E J : Type*} [Fintype J] [DecidableEq J]

/-- The forest sum: `ℓ ↦ ∏_{c ∈ s} f_{e(c)}(ℓ_c, ℓ_{par c})` summed over all labellings of the internal
vertices, for children `c ∈ s` whose parents have lower rank. -/
private theorem lwForest_core [Nonempty ι]
    (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf0 : ∀ j x y, 0 ≤ f j x y)
    (hrow : ∀ j x, ∑ y, f j x y ≤ K) (hcol : ∀ j y, ∑ x, f j x y ≤ K)
    (C : Finset I) (par : I → E ⊕ I) (edge : I → J) (ρ : I → ℕ)
    (hedge : ∀ c ∈ C, (u (edge c) = Sum.inr c ∧ v (edge c) = par c) ∨
      (v (edge c) = Sum.inr c ∧ u (edge c) = par c))
    (hrank : ∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) (s : Finset I) (hs : s ⊆ C) :
    (Fintype.card ι : ℝ) ^ s.card * ∑ ℓ : I → ι,
        ∏ c ∈ s, f (edge c) (Sum.elim ℓe ℓ (u (edge c))) (Sum.elim ℓe ℓ (v (edge c)))
      ≤ (Fintype.card ι : ℝ) ^ Fintype.card I * K ^ s.card := by
  classical
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  -- `par c ≠ inr c`
  have hpar : ∀ c ∈ C, par c ≠ Sum.inr c := fun c hc h => lt_irrefl _ (hrank c hc c h)
  induction s using Finset.induction_on_max_value ρ with
  | empty => simp
  | insert a s ha hmax ih =>
    have haC : a ∈ C := hs (Finset.mem_insert_self a s)
    have hsC : s ⊆ C := fun c hc => hs (Finset.mem_insert_of_mem hc)
    have ih' := ih hsC
    set hh : I → (I → ι) → ℝ := fun c ℓ =>
      f (edge c) (Sum.elim ℓe ℓ (u (edge c))) (Sum.elim ℓe ℓ (v (edge c))) with hhdef
    -- independence of the factors of `s` from the coordinate `a`
    have hind : ∀ c ∈ s, ∀ ℓ x, hh c (Function.update ℓ a x) = hh c ℓ := by
      intro c hc ℓ x
      have hcC := hsC hc
      have hca : c ≠ a := fun h => ha (h ▸ hc)
      have hpc : par c ≠ Sum.inr a := by
        intro h
        have := hrank c hcC a h
        have := hmax c hc
        omega
      have h1 : Sum.elim ℓe (Function.update ℓ a x) (Sum.inr c) = Sum.elim ℓe ℓ (Sum.inr c) := by
        simp [Function.update_of_ne hca]
      have h2 : Sum.elim ℓe (Function.update ℓ a x) (par c) = Sum.elim ℓe ℓ (par c) := by
        rcases hpar' : par c with e | w
        · simp
        · have hwa : w ≠ a := fun h => hpc (hpar' ▸ h ▸ rfl)
          simp [Function.update_of_ne hwa]
      simp only [hhdef]
      rcases hedge c hcC with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h3, h4, h1, h2]
      · rw [h3, h4, h1, h2]
    have hnn : ∀ c ℓ, 0 ≤ hh c ℓ := fun c ℓ => hf0 _ _ _
    have hGnn : ∀ ℓ, 0 ≤ ∏ c ∈ s, hh c ℓ := fun ℓ => Finset.prod_nonneg fun c _ => hnn c ℓ
    have hG : ∀ ℓ x, ∏ c ∈ s, hh c (Function.update ℓ a x) = ∏ c ∈ s, hh c ℓ := fun ℓ x =>
      Finset.prod_congr rfl fun c hc => hind c hc ℓ x
    have hH : ∀ ℓ x x', hh a (Function.update (Function.update ℓ a x) a x') = hh a (Function.update ℓ a x') := by
      intro ℓ x x'; rw [Function.update_idem]
    have hK' : ∀ ℓ, ∑ x, hh a (Function.update ℓ a x) ≤ K := by
      intro ℓ
      have h1 : ∀ x, Sum.elim ℓe (Function.update ℓ a x) (Sum.inr a) = x := by
        intro x; simp
      have h2 : ∀ x, Sum.elim ℓe (Function.update ℓ a x) (par a) = Sum.elim ℓe ℓ (par a) := by
        intro x
        rcases hpar' : par a with e | w
        · simp
        · have hwa : w ≠ a := fun h => hpar a haC (hpar' ▸ h ▸ rfl)
          simp [Function.update_of_ne hwa]
      simp only [hhdef]
      rcases hedge a haC with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · simp only [h3, h4, h1, h2]
        exact hcol _ _
      · simp only [h3, h4, h1, h2]
        exact hrow _ _
    have hsep := lwSum_sep a (fun ℓ => ∏ c ∈ s, hh c ℓ) (fun x ℓ => hh a (Function.update ℓ a x)) K
      hG (fun ℓ x x' => hH ℓ x x') hGnn hK'
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    have hsum : ∑ ℓ : I → ι, ∏ c ∈ insert a s, hh c ℓ =
        ∑ ℓ : I → ι, (∏ c ∈ s, hh c ℓ) * hh a (Function.update ℓ a (ℓ a)) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [Finset.prod_insert ha, Function.update_eq_self, mul_comm]
    change (Fintype.card ι : ℝ) ^ (insert a s).card * ∑ ℓ : I → ι, ∏ c ∈ insert a s, hh c ℓ ≤ _
    rw [hsum, hcard, pow_succ]
    calc (Fintype.card ι : ℝ) ^ s.card * (Fintype.card ι : ℝ) *
          ∑ ℓ : I → ι, (∏ c ∈ s, hh c ℓ) * hh a (Function.update ℓ a (ℓ a))
        = (Fintype.card ι : ℝ) ^ s.card * ((Fintype.card ι : ℝ) *
          ∑ ℓ : I → ι, (∏ c ∈ s, hh c ℓ) * hh a (Function.update ℓ a (ℓ a))) := by ring
      _ ≤ (Fintype.card ι : ℝ) ^ s.card * (K * ∑ ℓ : I → ι, ∏ c ∈ s, hh c ℓ) :=
          mul_le_mul_of_nonneg_left hsep (by positivity)
      _ = K * ((Fintype.card ι : ℝ) ^ s.card * ∑ ℓ : I → ι, ∏ c ∈ s, hh c ℓ) := by ring
      _ ≤ K * ((Fintype.card ι : ℝ) ^ Fintype.card I * K ^ s.card) :=
          mul_le_mul_of_nonneg_left ih' hK
      _ = _ := by ring

/-- **The peeling bound (`scalemole`, the sum over all but one vertex of each molecule, `7_8:255-258`)**:
a product of weights `f_j(ℓ_{u j}, ℓ_{v j})` over the edges `j ∈ J`, summed over the labels of the internal
vertices `I`, with entries `≤ a`, row sums and column sums `≤ K`.  If the edges contain a forest of children
`C ⊆ I` (each `c ∈ C` has its own parent edge `edge c` joining `c` to `par c`, a lower-rank internal
vertex or an external vertex), then
`N^{|C|} Σ_ℓ ∏_j f_j ≤ N^{|I|} K^{|C|} a^{|J| - |C|}`, i.e. each tree edge costs `K`, each other edge
`a`, and each root `N`. -/
theorem lwForest_sum_le [Nonempty ι]
    (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : ℝ) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hf0 : ∀ j x y, 0 ≤ f j x y) (hfa : ∀ j x y, f j x y ≤ a)
    (hrow : ∀ j x, ∑ y, f j x y ≤ K) (hcol : ∀ j y, ∑ x, f j x y ≤ K)
    (C : Finset I) (par : I → E ⊕ I) (edge : I → J) (ρ : I → ℕ) (hinj : Set.InjOn edge C)
    (hedge : ∀ c ∈ C, (u (edge c) = Sum.inr c ∧ v (edge c) = par c) ∨
      (v (edge c) = Sum.inr c ∧ u (edge c) = par c))
    (hrank : ∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) :
    (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι,
        ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j))
      ≤ (Fintype.card ι : ℝ) ^ Fintype.card I * K ^ C.card * a ^ (Fintype.card J - C.card) := by
  classical
  have hcore := lwForest_core ℓe u v f K hK hf0 hrow hcol C par edge ρ hedge hrank C subset_rfl
  have hpt : ∀ ℓ : I → ι, ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) ≤
      a ^ (Fintype.card J - C.card) *
        ∏ c ∈ C, f (edge c) (Sum.elim ℓe ℓ (u (edge c))) (Sum.elim ℓe ℓ (v (edge c))) := by
    intro ℓ
    set F : J → ℝ := fun j => f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) with hF
    have h1 : ∏ j, F j = (∏ j ∈ C.image edge, F j) * ∏ j ∈ (C.image edge)ᶜ, F j :=
      (Finset.prod_mul_prod_compl _ _).symm
    have h2 : ∏ j ∈ C.image edge, F j = ∏ c ∈ C, F (edge c) := Finset.prod_image hinj
    have h3 : ∏ j ∈ (C.image edge)ᶜ, F j ≤ a ^ (Fintype.card J - C.card) := by
      calc ∏ j ∈ (C.image edge)ᶜ, F j ≤ ∏ j ∈ (C.image edge)ᶜ, a :=
            Finset.prod_le_prod₀ (fun j _ => hf0 _ _ _) (fun j _ => hfa _ _ _)
        _ = a ^ ((C.image edge)ᶜ).card := Finset.prod_const _
        _ = _ := by rw [Finset.card_compl, Finset.card_image_of_injOn hinj]
    change ∏ j, F j ≤ _
    rw [h1, h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h3 (Finset.prod_nonneg fun c _ => hf0 _ _ _)
  calc (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j))
      ≤ (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, (a ^ (Fintype.card J - C.card) *
        ∏ c ∈ C, f (edge c) (Sum.elim ℓe ℓ (u (edge c))) (Sum.elim ℓe ℓ (v (edge c)))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => hpt ℓ) (by positivity)
    _ = a ^ (Fintype.card J - C.card) * ((Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι,
        ∏ c ∈ C, f (edge c) (Sum.elim ℓe ℓ (u (edge c))) (Sum.elim ℓe ℓ (v (edge c)))) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ a ^ (Fintype.card J - C.card) * ((Fintype.card ι : ℝ) ^ Fintype.card I * K ^ C.card) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = _ := by ring

end Forest

/-! ## 5. The molecular forest -/

/-- A rank function toward a target set: every non-target vertex has a neighbour of strictly smaller rank. -/
private theorem lwExists_rank {V : Type*} (G : SimpleGraph V) (T : V → Prop)
    (hT : ∀ v, ∃ t, T t ∧ G.Reachable v t) :
    ∃ rk : V → ℕ, ∀ v, ¬ T v → ∃ w, G.Adj v w ∧ rk w < rk v := by
  classical
  have hex : ∀ v, ∃ n, ∃ t, T t ∧ ∃ p : G.Walk v t, p.length = n := fun v => by
    obtain ⟨t, ht, ⟨p⟩⟩ := hT v
    exact ⟨p.length, t, ht, p, rfl⟩
  refine ⟨fun v => Nat.find (hex v), fun v hv => ?_⟩
  obtain ⟨t, ht, p, hp⟩ := Nat.find_spec (hex v)
  cases p with
  | nil => exact absurd ht hv
  | @cons _ w _ hadj p' =>
    refine ⟨w, hadj, ?_⟩
    have h1 : Nat.find (hex w) ≤ p'.length := Nat.find_min' (hex w) ⟨t, ht, p', rfl⟩
    rw [SimpleGraph.Walk.length_cons] at hp
    change Nat.find (hex w) < Nat.find (hex v)
    omega

section Cert

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem LGraph.adj_waved (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) {u v : E ⊕ I}
    (h : Γ.adj u v = true) :
    ∃ j : Fin Γ.waved.length, ((Γ.waved.get j).x = u ∧ (Γ.waved.get j).y = v) ∨
      ((Γ.waved.get j).x = v ∧ (Γ.waved.get j).y = u) := by
  unfold LGraph.adj at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
    exact ⟨j, of_decide_eq_true hd⟩
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hd⟩ := h
    have := hD e he
    simp [this] at hd

/-- **The molecular forest** of a graph without `=`-dotted edges: the internal vertices that are not the
chosen root of an internal molecule (`C`, `n_V - n_M` many) have a parent (an external vertex or an
internal vertex of strictly smaller rank, joined to the child by a waved edge `edge c`), and the waved
edges `edge c` are distinct.  Every internal molecule keeps exactly one root, the free vertex of
`7_8:252-253` (`|C| + n_M = n_V`). -/
theorem LGraph.exists_forest (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) :
    ∃ (C : Finset I) (par : I → E ⊕ I) (edge : I → Option (Fin Γ.waved.length)) (ρ : I → ℕ),
      C.card + Γ.nM = Fintype.card I ∧
      (∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) ∧
      (∀ c ∈ C, ∃ j, edge c = some j ∧
        (((Γ.waved.get j).x = Sum.inr c ∧ (Γ.waved.get j).y = par c) ∨
         ((Γ.waved.get j).y = Sum.inr c ∧ (Γ.waved.get j).x = par c))) ∧
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, edge c₁ = edge c₂ → c₁ = c₂) := by
  classical
  let Mi := {c : Γ.Mol // ¬ Γ.IsExtMol c}
  have hMi : ∀ c : Mi, ∃ i : I, Γ.molOf (Sum.inr i) = c.1 := by
    rintro ⟨c, hc⟩
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    rcases v with a | i
    · exact absurd ⟨a, rfl⟩ hc
    · exact ⟨i, rfl⟩
  choose rootI hroot using hMi
  let T : E ⊕ I → Prop := fun v => v.isLeft = true ∨ ∃ m : Mi, v = Sum.inr (rootI m)
  have hreach : ∀ v, ∃ t, T t ∧ Γ.molGraph.Reachable v t := by
    intro v
    by_cases h : Γ.IsExtMol (Γ.molOf v)
    · obtain ⟨a, ha⟩ := h
      exact ⟨Sum.inl a, Or.inl rfl, SimpleGraph.ConnectedComponent.eq.1 ha.symm⟩
    · refine ⟨Sum.inr (rootI ⟨Γ.molOf v, h⟩), Or.inr ⟨_, rfl⟩, ?_⟩
      exact SimpleGraph.ConnectedComponent.eq.1 (hroot ⟨Γ.molOf v, h⟩).symm
  obtain ⟨rk, hrk⟩ := lwExists_rank Γ.molGraph T hreach
  have hex : ∀ c : I, ¬ T (Sum.inr c) → ∃ (w : E ⊕ I) (j : Fin Γ.waved.length),
      (((Γ.waved.get j).x = Sum.inr c ∧ (Γ.waved.get j).y = w) ∨
        ((Γ.waved.get j).y = Sum.inr c ∧ (Γ.waved.get j).x = w)) ∧ rk w < rk (Sum.inr c) := by
    intro c hc
    obtain ⟨w, hadj, hlt⟩ := hrk _ hc
    refine ⟨w, ?_⟩
    rw [LGraph.molGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨_, hadj⟩ := hadj
    rcases hadj with h | h
    · obtain ⟨j, hj⟩ := Γ.adj_waved hD h
      exact ⟨j, hj.imp id And.symm, hlt⟩
    · obtain ⟨j, hj⟩ := Γ.adj_waved hD h
      exact ⟨j, hj.symm.imp id And.symm, hlt⟩
  choose! par' edge' hpe using hex
  let C : Finset I := Finset.univ.filter fun c => ¬ T (Sum.inr c)
  have hC : ∀ c ∈ C, ¬ T (Sum.inr c) := fun c hc => (Finset.mem_filter.1 hc).2
  have : Fintype Mi := Fintype.ofFinite _
  refine ⟨C, fun c => if c ∈ C then par' c else Sum.inr c,
    fun c => if h : c ∈ C then some (edge' c (hC c h)) else none, fun c => rk (Sum.inr c),
    ?_, ?_, ?_, ?_⟩
  · -- the count
    have hCc : C = (Finset.univ.image rootI)ᶜ := by
      ext c
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_image,
        not_exists, T]
      constructor
      · intro h m hm
        exact h (Or.inr ⟨m, by rw [hm]⟩)
      · intro h hT
        rcases hT with hT | ⟨m, hm⟩
        · simp at hT
        · exact h m (Sum.inr_injective hm).symm
    have hcard : (Finset.univ.image rootI).card = Γ.nM := by
      rw [Finset.card_image_of_injective, Finset.card_univ, Γ.nM_eq_card, Nat.card_eq_fintype_card]
      intro m m' h
      apply Subtype.ext
      rw [← hroot m, ← hroot m', h]
    rw [hCc, Finset.card_compl, hcard]
    have : Γ.nM ≤ Fintype.card I := by rw [← hcard]; exact Finset.card_le_univ _
    omega
  · intro c hc w hw
    simp only [hc, ite_true] at hw
    have := (hpe c (hC c hc)).2
    rw [hw] at this
    exact this
  · intro c hc
    simp only [hc, ite_true, dite_true]
    exact ⟨edge' c (hC c hc), rfl, by simpa using (hpe c (hC c hc)).1⟩
  · intro c₁ h₁ c₂ h₂ h
    simp only [h₁, h₂, dite_true, Option.some.injEq] at h
    by_contra hne
    obtain ⟨e1, r1⟩ := hpe c₁ (hC c₁ h₁)
    obtain ⟨e2, r2⟩ := hpe c₂ (hC c₂ h₂)
    rw [h] at e1
    rcases e1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases e2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · exact hne (Sum.inr_injective (a1.symm.trans a2))
    · rw [a1] at b2
      rw [b1] at a2
      rw [a2] at r1
      rw [← b2] at r2
      omega
    · rw [a1] at b2
      rw [b1] at a2
      rw [a2] at r1
      rw [← b2] at r2
      omega
    · exact hne (Sum.inr_injective (a1.symm.trans a2))

end Cert


/-! ## 6. Target 3: `claim:size` (deterministic form) -/

section Claim

variable {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] [Fintype I]
  [DecidableEq I]

/-- The (matrix-entry) value of a waved edge: `S_{xy}`, `S^+_{xy}` or `conj S^+_{yx}`. -/
def lwWVal (D : LData ι) (e : WEdge (E ⊕ I)) (x y : ι) : ℂ :=
  if e.col then (if e.σ then D.Sp x y else star (D.Sp y x)) else D.S x y

private theorem lwWVal_eq (D : LData ι) (ℓ : E ⊕ I → ι) (e : WEdge (E ⊕ I)) :
    WEdge.val D ℓ e = lwWVal D e (ℓ e.x) (ℓ e.y) := rfl

/-- The three bounds on `S`, `S^±` give the three bounds on every waved-edge weight. -/
private theorem lwWVal_bound {D : LData ι} {a K₁ : ℝ} (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁)
    (e : WEdge (E ⊕ I)) :
    (∀ x y, ‖lwWVal D e x y‖ ≤ a) ∧ (∀ x, ∑ y, ‖lwWVal D e x y‖ ≤ K₁) ∧
      (∀ y, ∑ x, ‖lwWVal D e x y‖ ≤ K₁) := by
  unfold lwWVal
  by_cases hc : e.col = true
  · by_cases hσ : e.σ = true
    · simp only [hc, hσ, ite_true]; exact hSp
    · have hσ' : e.σ = false := by simpa using hσ
      simp only [hc, hσ', ite_true, Bool.false_eq_true, ite_false, norm_star]
      exact ⟨fun x y => hSp.1 y x, fun x => hSp.2.2 x, fun y => hSp.2.1 y⟩
  · have hc' : e.col = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]; exact hS

omit [DecidableEq E] [DecidableEq I] [Fintype E] [Fintype I] in
private theorem lwProd_waved_eq (Γ : LGraph E I) (g : WEdge (E ⊕ I) → ℝ) :
    (Γ.waved.map g).prod = ∏ j : Fin Γ.waved.length, g (Γ.waved.get j) := by
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

private theorem lwNorm_list_prod (l : List ℂ) : ‖l.prod‖ = (l.map fun z => ‖z‖).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem lwList_prod_le (l : List ℝ) (Ψ : ℝ) (h0 : ∀ x ∈ l, 0 ≤ x) (h : ∀ x ∈ l, x ≤ Ψ) :
    l.prod ≤ Ψ ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ]
    have hx0 := h0 x (List.mem_cons_self ..)
    have hx := h x (List.mem_cons_self ..)
    have hl0 : 0 ≤ l.prod := List.prod_nonneg fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    have ih' := ih (fun y hy => h0 y (List.mem_cons_of_mem _ hy)) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have : 0 ≤ Ψ := hx0.trans hx
    calc x * l.prod ≤ Ψ * Ψ ^ l.length := mul_le_mul hx ih' hl0 this
      _ = _ := by ring

variable [Nonempty ι]

/-- The factor of a solid edge is `≤ Ψ` when the entry bound holds and a non-loop edge has distinct
labels at its ends. -/
private theorem lwSEdge_norm_le (D : LData ι) {m : ℂ} {Ψ : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (ℓ : E ⊕ I → ι) (e : SEdge (E ⊕ I)) (hloop : e.src = e.dst → e.circ = true)
    (hgood : e.src ≠ e.dst → ℓ e.src ≠ ℓ e.dst) : ‖SEdge.val D ℓ e‖ ≤ Ψ := by
  have hn : ‖SEdge.val D ℓ e‖ = ‖D.G (ℓ e.src) (ℓ e.dst) - if e.circ then D.M (ℓ e.src) (ℓ e.dst) else 0‖ := by
    unfold SEdge.val
    dsimp only
    cases e.σ
    · simp only [Bool.false_eq_true, ite_false]; exact norm_star _
    · simp
  rw [hn]
  by_cases hs : e.src = e.dst
  · rw [hloop hs, hs]
    simp only [ite_true, hM, ite_true]
    exact hGd _
  · have hne := hgood hs
    have : D.M (ℓ e.src) (ℓ e.dst) = 0 := by simp [hM, hne]
    split_ifs <;> simp [this] <;> exact hG _ _ hne

/-- Pointwise bound of one term: `|term| ≤ |coeff| Ψ^{n_S} ∏_{waved} |S-factor|`: the `×`-dotted
edges force distinct labels on the ends of every non-loop solid edge (`defnlvl0` (iii)), so each solid
edge is `≤ Ψ` by the entry bound; the dotted factors are `≤ 1`. -/
theorem LGraph.term_norm_le (Γ : LGraph E I) (hN : Γ.Normal) (D : LData ι) {m : ℂ} {Ψ : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ) (ℓ : E ⊕ I → ι) :
    ‖Γ.term D ℓ‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod := by
  have hΨ : 0 ≤ Ψ := by
    obtain ⟨x⟩ := ‹Nonempty ι›
    exact (norm_nonneg _).trans (hGd x)
  have hwn : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  by_cases hgood : ∀ e ∈ Γ.solid, e.src ≠ e.dst → ℓ e.src ≠ ℓ e.dst
  · unfold LGraph.term
    rw [norm_mul, norm_mul, norm_mul, lwNorm_list_prod, lwNorm_list_prod, lwNorm_list_prod]
    simp only [List.map_map]
    have h1 : (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D ℓ)).prod ≤ Ψ ^ Γ.nS := by
      have := lwList_prod_le (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D ℓ)) Ψ (by
          intro x hx
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
          exact norm_nonneg _) (by
          intro x hx
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
          exact lwSEdge_norm_le D hM hG hGd ℓ e (hN.2.2 e he) (hgood e he))
      simpa [LGraph.nS] using this
    have h3 : (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod ≤ 1 := by
      have := lwList_prod_le (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)) 1 (by
          intro x hx
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
          exact norm_nonneg _) (by
          intro x hx
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
          simp only [Function.comp, DEdge.val]
          split_ifs <;> simp)
      simpa using this
    have h0s : 0 ≤ (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D ℓ)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have h0d : 0 ≤ (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have hw' : (Γ.waved.map ((fun z : ℂ => ‖z‖) ∘ WEdge.val D ℓ)).prod =
        (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod := rfl
    rw [hw']
    calc ‖Γ.coeff‖ * (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D ℓ)).prod *
          (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod *
          (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod
        ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod * 1 := by
          gcongr
      _ = _ := mul_one _
  · push Not at hgood
    obtain ⟨e, he, hne, heq⟩ := hgood
    have hxb : Γ.XBetween e.src e.dst := (hN.2.1 e.src e.dst hne).2 ⟨e, he, hne, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨e', he', hf, hxy⟩ := hxb
    have hz : DEdge.val ℓ e' = 0 := by
      have : ℓ e'.x = ℓ e'.y := by
        rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact heq
        · rw [h1, h2]; exact heq.symm
      simp [DEdge.val, this, hf]
    have : (Γ.dotted.map (DEdge.val ℓ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.2 ⟨e', he', hz⟩)
    have h0 : Γ.term D ℓ = 0 := by unfold LGraph.term; rw [this, mul_zero]
    rw [h0, norm_zero]
    positivity

/-- The waved weights: `Σ_{ℓ_I} ∏_{waved} |factor| ≤ N^{n_M} K₁^{n_V-n_M} a^{n_W-(n_V-n_M)}` (the free
vertex of every internal molecule costs `N`, the other `n_V - n_M` vertices cost `K₁` through a tree edge,
and every non-tree waved edge costs `a`: `7_8:252-258`, with the peeling bound `lwForest_sum_le`). -/
theorem LGraph.waved_sum_le (Γ : LGraph E I) (hN : Γ.Normal) (D : LData ι) {a K₁ : ℝ}
    (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) (ℓe : E → ι) :
    ∑ ℓi : I → ι, (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod ≤
      (Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) * a ^ (Γ.nW - (Γ.nV - Γ.nM)) := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty ι›
  have ha : 0 ≤ a := (norm_nonneg _).trans (hS.1 x0 x0)
  have hK : 0 ≤ K₁ := (Finset.sum_nonneg fun y _ => norm_nonneg _).trans (hS.2.1 x0)
  have hN0 : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨C, par, edge, ρ, hcard, hrank, hedge, hinj⟩ := Γ.exists_forest hN.1
  have hnV : Γ.nV = Fintype.card I := rfl
  by_cases hn : Γ.waved.length = 0
  · -- no waved edges: `C = ∅`, every internal vertex is its own molecule
    have hCe : C = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨j, _⟩ := hedge c hc
      exact absurd j.2 (by omega)
    have hw : Γ.waved = [] := List.length_eq_zero_iff.1 hn
    have hM : Γ.nM = Fintype.card I := by rw [hCe] at hcard; simpa using hcard
    have hnW : Γ.nW = 0 := hn
    simp only [hw, List.map_nil, List.prod_nil, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, nsmul_eq_mul, mul_one, Nat.cast_pow, hnV, hM, Nat.sub_self, pow_zero, hnW]
    simp
  · have hpos : 0 < Γ.waved.length := Nat.pos_of_ne_zero hn
    set edgeT : I → Fin Γ.waved.length := fun c => (edge c).getD ⟨0, hpos⟩ with hedgeT
    have hedgeT' : ∀ c ∈ C, (((Γ.waved.get (edgeT c)).x = Sum.inr c ∧ (Γ.waved.get (edgeT c)).y = par c) ∨
        ((Γ.waved.get (edgeT c)).y = Sum.inr c ∧ (Γ.waved.get (edgeT c)).x = par c)) := by
      intro c hc
      obtain ⟨j, hj, h⟩ := hedge c hc
      simpa [hedgeT, hj] using h
    have hinjT : Set.InjOn edgeT (C : Set I) := by
      intro c₁ h₁ c₂ h₂ h
      obtain ⟨j₁, hj₁, _⟩ := hedge c₁ h₁
      obtain ⟨j₂, hj₂, _⟩ := hedge c₂ h₂
      refine hinj c₁ h₁ c₂ h₂ ?_
      simp only [hedgeT, hj₁, hj₂, Option.getD_some] at h
      rw [hj₁, hj₂, h]
    set f : Fin Γ.waved.length → ι → ι → ℝ := fun j x y => ‖lwWVal D (Γ.waved.get j) x y‖ with hf
    have hmain := lwForest_sum_le (E := E) (I := I) (J := Fin Γ.waved.length) ℓe
      (fun j => (Γ.waved.get j).x) (fun j => (Γ.waved.get j).y) f a K₁ ha hK
      (fun j x y => norm_nonneg _) (fun j x y => (lwWVal_bound hS hSp (Γ.waved.get j)).1 x y)
      (fun j x => (lwWVal_bound hS hSp (Γ.waved.get j)).2.1 x)
      (fun j y => (lwWVal_bound hS hSp (Γ.waved.get j)).2.2 y)
      C par edgeT ρ hinjT hedgeT' hrank
    have hsum : ∀ ℓi : I → ι, (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod =
        ∏ j : Fin Γ.waved.length, f j (Sum.elim ℓe ℓi (Γ.waved.get j).x) (Sum.elim ℓe ℓi (Γ.waved.get j).y) := by
      intro ℓi
      rw [lwProd_waved_eq Γ (fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖)]
      rfl
    simp only [hsum]
    have hNM : Fintype.card I = C.card + Γ.nM := hcard.symm
    have hCnV : C.card = Γ.nV - Γ.nM := by omega
    rw [hNM, pow_add, Fintype.card_fin] at hmain
    rw [← hCnV]
    have hNp : 0 < (Fintype.card ι : ℝ) ^ C.card := pow_pos hN0 _
    have : (Fintype.card ι : ℝ) ^ C.card * ∑ ℓi : I → ι,
        ∏ j : Fin Γ.waved.length, f j (Sum.elim ℓe ℓi (Γ.waved.get j).x) (Sum.elim ℓe ℓi (Γ.waved.get j).y) ≤
        (Fintype.card ι : ℝ) ^ C.card * ((Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ C.card * a ^ (Γ.nW - C.card)) := by
      refine hmain.trans (le_of_eq ?_)
      simp only [LGraph.nW]
      ring
    exact le_of_mul_le_mul_left this hNp

/-- `nM ≤ nV` and `nV - nM ≤ nW` for a graph without `=`-dotted edges (the tree edges of the forest are
distinct waved edges). -/
theorem LGraph.counters_le (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) :
    Γ.nM ≤ Γ.nV ∧ Γ.nV - Γ.nM ≤ Γ.nW := by
  classical
  obtain ⟨C, par, edge, ρ, hcard, hrank, hedge, hinj⟩ := Γ.exists_forest hD
  have hnV : Γ.nV = Fintype.card I := rfl
  refine ⟨by omega, ?_⟩
  have h1 : C.card ≤ (Finset.univ.image (Option.some : Fin Γ.waved.length → _)).card := by
    refine Finset.card_le_card_of_injOn edge (fun c hc => ?_) (fun c₁ h₁ c₂ h₂ h => hinj c₁ h₁ c₂ h₂ h)
    obtain ⟨j, hj, _⟩ := hedge c hc
    simp [hj]
  rw [Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_univ,
    Fintype.card_fin] at h1
  change Γ.nV - Γ.nM ≤ Γ.waved.length
  omega

/-- **The `L¹`-form of `claim:size`**: `|Γ.val| ≤ |coeff| Ψ^{n_S} N^{n_M} K₁^{n_V - n_M} a^{n_W - (n_V - n_M)}`
for a normal graph, data with `M = m I`, the entry bound `|G_{xy}| ≤ Ψ` (`x ≠ y`), `|G_{xx} - m| ≤ Ψ`, and
weights `S`, `S^±` with entries `≤ a` and row and column sums `≤ K₁`.  No window on `Ψ`, no `N^τ`. -/
theorem LGraph.val_norm_le (Γ : LGraph E I) (hN : Γ.Normal) (D : LData ι) {m : ℂ} {Ψ a K₁ : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) (ℓe : E → ι) :
    ‖Γ.val D ℓe‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      ((Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) * a ^ (Γ.nW - (Γ.nV - Γ.nM))) := by
  unfold LGraph.val
  calc ‖∑ ℓi : I → ι, Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ∑ ℓi : I → ι, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ℓi : I → ι, ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod :=
        Finset.sum_le_sum fun ℓi _ => Γ.term_norm_le hN D hM hG hGd _
    _ = ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        ∑ ℓi : I → ι, (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        have hΨ : 0 ≤ Ψ := by
          obtain ⟨x⟩ := ‹Nonempty ι›
          exact (norm_nonneg _).trans (hGd x)
        exact mul_le_mul_of_nonneg_left (Γ.waved_sum_le hN D hS hSp ℓe)
          (mul_nonneg (norm_nonneg _) (pow_nonneg hΨ _))

/-- The size identity `N^{n_M} (K₀ W^{-d})^{n_W-(n_V-n_M)} = K₀^{n_W-(n_V-n_M)} (L^d)^{n_M} W^{-d(n_W-n_V)}`
(`N = (W L)^d`, `7_8:238-241`). -/
private theorem lwSize_alg (W d L nM nV nW : ℕ) (hW : (W : ℝ) ≠ 0) (h1 : nM ≤ nV) (h2 : nV - nM ≤ nW) (K₀ : ℝ) :
    ((((W * L) ^ d : ℕ) : ℝ)) ^ nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (nW - (nV - nM)) =
      K₀ ^ (nW - (nV - nM)) * (((L : ℝ) ^ d) ^ nM * (W : ℝ) ^ (-(d : ℤ) * ((nW : ℤ) - nV))) := by
  obtain ⟨t, ht⟩ : ∃ t, nW = (nV - nM) + t := ⟨nW - (nV - nM), by omega⟩
  have htt : nW - (nV - nM) = t := by omega
  have hexp : -(d : ℤ) * ((nW : ℤ) - nV) = ((d * nM : ℕ) : ℤ) - ((d * t : ℕ) : ℤ) := by
    have : (nW : ℤ) - nV = (t : ℤ) - nM := by omega
    rw [this]; push_cast; ring
  rw [htt, hexp, zpow_sub₀ hW, zpow_natCast, zpow_natCast]
  push_cast
  rw [mul_pow, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  field_simp
  rw [pow_mul (W : ℝ) d t]

/-- The constant of `claim:size`: `C_Γ = |coeff| K₁^{n_V-n_M} K₀^{n_W-(n_V-n_M)}`, depending on the graph
and on `(K₀, K₁)` (that is on `d, Λ, κ`) only. -/
def LGraph.sizeConst (Γ : LGraph E I) (K₀ K₁ : ℝ) : ℝ :=
  ‖Γ.coeff‖ * K₁ ^ (Γ.nV - Γ.nM) * K₀ ^ (Γ.nW - (Γ.nV - Γ.nM))

theorem LGraph.sizeConst_nonneg (Γ : LGraph E I) {K₀ K₁ : ℝ} (h₀ : 0 ≤ K₀) (h₁ : 0 ≤ K₁) :
    0 ≤ Γ.sizeConst K₀ K₁ := by
  unfold LGraph.sizeConst; positivity

end Claim

section ClaimIdx

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
  [DecidableEq I]

/-- **`claim:size`** (`7_8:260-266`), deterministic form.  For a normal graph `Γ`, data `D` on the fine
lattice `Z_{WL}^d` with `M = m I`, the entry bound `|G_{xy}| ≤ Ψ` (`x ≠ y`), `|G_{xx} - m| ≤ Ψ`
(`(GijGEX)`, `(GiiGEX)` on the sample, as hypotheses), and weights `S`, `S^±` with entries `≤ K₀ W^{-d}` and
row and column sums `≤ K₁` (`(eq:estSpm-W)`, `lwKBound_E`):
`|Γ.val| ≤ C_Γ · size(Γ)` for every `Ψ` and every external labelling, with `C_Γ = Γ.sizeConst K₀ K₁`.
No `N^τ` loss and no window on `Ψ` is needed (T2124a). -/
theorem lwClaimSize (Γ : LGraph E I) (hN : Γ.Normal) (D : LData (Idx d L W)) {m : ℂ} {Ψ K₀ K₁ : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (ℓe : E → Idx d L W) :
    ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ * Γ.scalingSize Ψ W d L := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hb := Γ.val_norm_le hN D hM hG hGd hS hSp ℓe
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hcard : (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) := by
    rw [card_Idx]
  rw [hcard] at hb
  refine hb.trans (le_of_eq ?_)
  have hal := lwSize_alg W d L Γ.nM Γ.nV Γ.nW hW h1 h2 K₀
  unfold LGraph.sizeConst LGraph.scalingSize Counters.scalingSize
  change ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) *
      (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) = _
  calc ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) *
        (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)))
      = ‖Γ.coeff‖ * Ψ ^ Γ.nS * K₁ ^ (Γ.nV - Γ.nM) *
        (((((W * L) ^ d : ℕ) : ℝ)) ^ Γ.nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) := by ring
    _ = _ := by rw [hal]; simp only [LGraph.counters]; ring

/-- The constant of the general-graph form: the sum of the constants of the normal graphs of the dotted
edge partition. -/
def LGraph.sizeConstG (m : ℂ) (Γ : LGraph E I) (K₀ K₁ : ℝ) : ℝ :=
  ((Γ.partition m).map fun P => P.g.sizeConst K₀ K₁).sum

private theorem lwNorm_sum_le_of_le {α : Type*} (l : List α) (f : α → ℂ) (c : α → ℝ) (G : ℝ)
    (h : ∀ x ∈ l, ‖f x‖ ≤ c x * G) : ‖(l.map f).sum‖ ≤ (l.map c).sum * G := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    calc ‖f x + (l.map f).sum‖ ≤ ‖f x‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ c x * G + (l.map c).sum * G := add_le_add h1 h2
      _ = _ := by ring

/-- **`claim:size` for a general graph** (`7_8:248-250`, `scalingSizeG`): the dotted edge partition of
`Γ` (`Γ.val = Σ_{P ∈ partition} P.val`, the terms are normal graphs) gives
`|Γ.val| ≤ (Σ_P C_P) · size(Γ)` with `size(Γ) = max_P size(P.g)`. -/
theorem lwClaimSizeG (m : ℂ) (Γ : LGraph E I) (D : LData (Idx d L W)) {Ψ K₀ K₁ : ℝ}
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (ℓe : E → Idx d L W) :
    ‖Γ.val D ℓe‖ ≤ Γ.sizeConstG m K₀ K₁ * Γ.scalingSizeG m Ψ W d L := by
  rw [Γ.val_eq_partition m D (fun x => by simpa using hM x x) ℓe]
  unfold LComb.val LGraph.sizeConstG
  have hB := (Γ.scalingSizeG_le_iff m Ψ W d L _).1 le_rfl
  refine lwNorm_sum_le_of_le (Γ.partition m) (fun P : PGraph E => P.val D ℓe)
    (fun P : PGraph E => P.g.sizeConst K₀ K₁) _ fun P hP => ?_
  have hPN := Γ.partition_normal m P hP
  by_cases h : ∃ ℓ', ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    rw [P.val_of_factor D hℓ']
    exact (lwClaimSize P.g hPN D hM hG hGd hS hSp ℓ').trans
      (mul_le_mul_of_nonneg_left (hB.2 P hP) (P.g.sizeConst_nonneg hK₀ hK₁))
  · rw [P.val_of_not D h, norm_zero]
    exact mul_nonneg (P.g.sizeConst_nonneg hK₀ hK₁) hB.1

end ClaimIdx

/-! ## 7. `claim:size` for the matrices of the model -/

section Model

/-- **`claim:size` with the constants of the model** (target 3 with target 1).  For `d ≥ 3`, `Λ`, `κ > 0`
there are constants `(K₀, K₁)`, depending on `(d, Λ, κ)` only, such that for every `L ≥ 3`, `W ≥ 1`,
`0 < g ≤ Λ`, `0 ≤ t < 1`, `|E| ≤ 2 - κ`, every normal graph `Γ` and every data `D` with `S = t · svarF`,
`S^± = S (1 - m(E)² S)⁻¹`, `M = m(E) I`, `G` satisfying the entry bound with some `Ψ`
(`|G_{xy}| ≤ Ψ` for `x ≠ y`, `|G_{xx} - m| ≤ Ψ`):
`|Γ.val D ℓe| ≤ C_Γ · size(Γ)`, `C_Γ = |coeff| K₁^{n_V-n_M} K₀^{n_W-(n_V-n_M)}`, never depending on
`L, W, t, E, g, Ψ`. -/
theorem lwClaimSize_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
      ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : LGraph E' I'),
        Γ.Normal → ∀ D : LData (Idx d L W), D.S = lwSmat d L W g t → D.Sp = lwSpOf d L W g t (mE E) →
        (∀ x y, D.M x y = if x = y then mE E else 0) → ∀ Ψ : ℝ,
        (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - mE E‖ ≤ Ψ) → ∀ ℓe : E' → Idx d L W,
        ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ * Γ.scalingSize Ψ W d L := by
  obtain ⟨K₀, K₁, h₀, h₁, h⟩ := lwKBound_E d hd Λ κ hΛ hκ
  refine ⟨K₀, K₁, h₀, h₁, fun L W _ _ hL g t E hg hgΛ ht0 ht1 hE E' I' _ _ _ _ Γ hN D hS hSp hM Ψ hG hGd ℓe => ?_⟩
  obtain ⟨hS', hSp'⟩ := h L W hL g t E hg hgΛ ht0 ht1 hE
  rw [← hS] at hS'
  rw [← hSp] at hSp'
  exact lwClaimSize Γ hN D hM hG hGd hS' hSp' ℓe

/-- **`claim:size` for a general graph, with the constants of the model**: `|Γ.val| ≤ (Σ_P C_P) ·
size_G(Γ)`, `size_G(Γ) = max_P size(P)` over the dotted edge partition. -/
theorem lwClaimSizeG_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
      ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : LGraph E' I'),
        ∀ D : LData (Idx d L W), D.S = lwSmat d L W g t → D.Sp = lwSpOf d L W g t (mE E) →
        (∀ x y, D.M x y = if x = y then mE E else 0) → ∀ Ψ : ℝ,
        (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - mE E‖ ≤ Ψ) → ∀ ℓe : E' → Idx d L W,
        ‖Γ.val D ℓe‖ ≤ Γ.sizeConstG (mE E) K₀ K₁ * Γ.scalingSizeG (mE E) Ψ W d L := by
  obtain ⟨K₀, K₁, h₀, h₁, h⟩ := lwKBound_E d hd Λ κ hΛ hκ
  refine ⟨K₀, K₁, h₀, h₁, fun L W _ _ hL g t E hg hgΛ ht0 ht1 hE E' I' _ _ _ _ Γ D hS hSp hM Ψ hG hGd ℓe => ?_⟩
  obtain ⟨hS', hSp'⟩ := h L W hL g t E hg hgΛ ht0 ht1 hE
  rw [← hS] at hS'
  rw [← hSp] at hSp'
  exact lwClaimSizeG (mE E) Γ D h₀.le h₁.le hM hG hGd hS' hSp' ℓe

/-- The scaling size is homogeneous of degree `n_S` in `Ψ`: the "up to `N^τ`" of `Γ ≺ size(Γ)`
(`7_8:260`): if the entry bound holds with `Ψ' = λ Ψ`, `|Γ.val| ≤ C_Γ λ^{n_S} size_Ψ(Γ)`. -/
theorem LGraph.scalingSize_mul {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) (c Ψ : ℝ) (W d L : ℕ) :
    Γ.scalingSize (c * Ψ) W d L = c ^ Γ.nS * Γ.scalingSize Ψ W d L := by
  unfold LGraph.scalingSize Counters.scalingSize
  simp only [LGraph.counters]
  rw [mul_pow]; ring

end Model


/-! ## 8. Target 2: the confinement tail of `scalemole` -/

section Tail

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **The tail of a kernel with the decay of `(eq:estSpm-W)`** (`scalemole`, `7_8:255-258`): the weight
of the labels at block distance `≥ R` from `x` is `≤ C expC(d-2, c/2) e^{-cR/2}`, uniformly in `L, W`. -/
theorem lwKernel_tail (hd : 3 ≤ d) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {K : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : ∀ x y, ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (x : Idx d L W) (R : ℝ) :
    ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)), ‖K x y‖ ≤
      C * expC (d - 2) (c / 2) * Real.exp (-(c * R / 2)) := by
  have hW : (0 : ℝ) < ((W : ℝ) ^ d)⁻¹ := by
    have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  calc ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)), ‖K x y‖
      ≤ ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)),
        C * Real.exp (-(c * R / 2)) *
          (((W : ℝ) ^ d)⁻¹ * Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ)))) := by
        refine Finset.sum_le_sum fun y hy => ?_
        have hR : R ≤ (lwBdist d L W x y : ℝ) := (Finset.mem_filter.1 hy).2
        refine (h x y).trans ?_
        have h1 : Real.exp (-(c * (lwBdist d L W x y : ℝ))) ≤
            Real.exp (-(c * R / 2)) * Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ))) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        calc C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))
            ≤ C * ((W : ℝ) ^ d)⁻¹ * (Real.exp (-(c * R / 2)) *
              Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ)))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by ring
    _ ≤ ∑ y : Idx d L W, C * Real.exp (-(c * R / 2)) *
          (((W : ℝ) ^ d)⁻¹ * Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ)))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun y _ _ => by positivity
    _ = C * Real.exp (-(c * R / 2)) *
          ∑ y : Idx d L W, ((W : ℝ) ^ d)⁻¹ * Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ C * Real.exp (-(c * R / 2)) * expC (d - 2) (c / 2) :=
        mul_le_mul_of_nonneg_left (lwSum_decay_row hd (by linarith) x) (by positivity)
    _ = _ := by ring

/-- At the radius `R = (log W)^{3/2}` of `scalemole` the tail `e^{-cR/2}` is eventually `≤ W^{-D}`. -/
theorem lwTail_log32 {c : ℝ} (hc : 0 < c) (D : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      Real.exp (-(c * (Real.log W) ^ ((3 : ℝ) / 2) / 2)) ≤ (W : ℝ) ^ (-D) := by
  refine ⟨⌈Real.exp ((2 * |D| / c) ^ 2)⌉₊ + 2, fun W hW => ?_⟩
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast (by omega : 2 ≤ W)
  have hWpos : (0 : ℝ) < W := by linarith
  have hlogpos : 0 < Real.log W := Real.log_pos (by linarith)
  have hlog : (2 * |D| / c) ^ 2 ≤ Real.log W := by
    have h1 : Real.exp ((2 * |D| / c) ^ 2) ≤ (W : ℝ) := by
      have := Nat.le_ceil (Real.exp ((2 * |D| / c) ^ 2))
      have h2 : ((⌈Real.exp ((2 * |D| / c) ^ 2)⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈Real.exp ((2 * |D| / c) ^ 2)⌉₊ ≤ W)
      linarith
    rw [← Real.log_exp ((2 * |D| / c) ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) h1
  rw [Real.rpow_def_of_pos hWpos]
  apply Real.exp_le_exp.2
  have hsq : 2 * |D| / c ≤ Real.sqrt (Real.log W) := by
    apply Real.le_sqrt_of_sq_le hlog
  have h32 : (Real.log W) ^ ((3 : ℝ) / 2) = Real.log W * Real.sqrt (Real.log W) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hlogpos.le (by norm_num)]
    norm_num
  rw [h32]
  have h3 : c * (2 * |D| / c) = 2 * |D| := by field_simp
  have h4 : 2 * D ≤ c * Real.sqrt (Real.log W) := by
    have := mul_le_mul_of_nonneg_left hsq hc.le
    have := le_abs_self D
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hlogpos.le]

/-- Target 2 on the energy `E`: the tail of `S^±` beyond block distance `R` is `≤ C₂ e^{-c₂ R}`, uniformly
in `L, W, t, E, g` (`(C₂, c₂)` depend on `(d, Λ, κ)` only). -/
theorem lwSpOf_tail_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ →
        ∀ (x : Idx d L W) (R : ℝ),
          ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)),
            ‖lwSpOf d L W g t (mE E) x y‖ ≤ C₂ * Real.exp (-(c₂ * R)) := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E d hd Λ κ hΛ hκ
  have hE : 0 < expC (d - 2) (c / 2) := by
    unfold expC
    have : 0 < c / 2 := by linarith
    positivity
  refine ⟨C * expC (d - 2) (c / 2), c / 2, mul_pos hC hE, by linarith,
    fun L W _ _ hL g t E hg hgΛ ht0 ht1 hEκ x R => ?_⟩
  have := lwKernel_tail hd hC.le hc (h L W hL g t E hg hgΛ ht0 ht1 hEκ).2 x R
  convert this using 3
  ring

end Tail

/-! The same bound for the two objects the pins read: `LWPins_lwSp` (the one-size pins `LWweightExp`,
`LWedgeExp`, `LWggExp`) and `lwSplus` (the sequence-space `Graph/LWStein`). -/

section Names

/-- **Target 1 for `LWPins_lwSp`** (`S^± = S (1 - m(E)² S)⁻¹`, `S = t · svarF`). -/
theorem LWPins_lwSp_decay (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ g t E : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 → |E| ≤ 2 - κ → ∀ x y : Idx d L W,
        ‖LWPins_lwSp d L W g E t x y‖ ≤
          C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E d hd Λ κ hΛ hκ
  refine ⟨C, c, hC, hc, fun L W _ _ hL g t E hg hgΛ ht0 ht1 hE x y => ?_⟩
  rw [LWPins_lwSp_eq]
  exact (h L W hL g t E hg hgΛ ht0 ht1 hE).2 x y

/-- **Target 1 for `lwSplus`** on a size sequence `sz`: for every `n`, `0 < sz.lam n ≤ Λ`, `0 ≤ u < 1`,
`|E| ≤ 2 - κ`. -/
theorem lwSplus_decay (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ Λ →
      ∀ u E : ℝ, 0 ≤ u → u < 1 → |E| ≤ 2 - κ → ∀ x y : Idx d (sz.L n) (sz.W n),
        ‖lwSplus sz n u (mE E) x y‖ ≤
          C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E d hd Λ κ hΛ hκ
  refine ⟨C, c, hC, hc, fun sz n hg hgΛ u E hu0 hu1 hE x y => ?_⟩
  rw [lwSplus_eq]
  exact (h (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) u E hg hgΛ hu0 hu1 hE).2 x y

end Names

/-- **Instance of target 1 for `LWPins_lwSp` and `lwSplus`** at the merged `sz0` (`n = 0`: `L = 4`,
`W = 32`, `lam = 1/64`), `E = 0`, `u = t = 1/2`. -/
example : (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ x y : Idx 3 4 32, ‖LWPins_lwSp 3 4 32 (1 / 64) 0 (1 / 2) x y‖ ≤
        C * (((32 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 4 32 x y : ℝ)))) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ x y : Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0), ‖lwSplus SizesInst.sz0 0 (1 / 2) (mE 0) x y‖ ≤
        C * (((SizesInst.sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0) x y : ℝ)))) := by
  obtain ⟨C, c, hC, hc, h⟩ := LWPins_lwSp_decay 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  obtain ⟨C', c', hC', hc', h'⟩ := lwSplus_decay 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  refine ⟨⟨C, c, hC, hc, fun x y => h 4 32 (by norm_num) (1 / 64) (1 / 2) 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x y⟩,
    ⟨C', c', hC', hc', fun x y => h' SizesInst.sz0 0 (by rw [SizesInst.sz0_values.2.2.2]; norm_num) (by rw [SizesInst.sz0_values.2.2.2]; norm_num) (1 / 2) 0
      (by norm_num) (by norm_num) (by norm_num) x y⟩⟩

/-! ## 9. Compiled instances at `d = 3`, `L = 4`, `W = 2`, `g = 1/2`, `E = 0`, `t = 1/2` -/

section Instances

/-- Concrete data on `Z_8^3` (`L = 4`, `W = 2`, `N = 512`): `S = t · svarF`, `S^± = S (1 - m(0)² S)⁻¹` at
`g = 1/2`, `t = 1/2`; `M = m(0) I` with `m(0) = i`; and the dense resolvent-like matrix
`G = M + Ψ J` with `Ψ = 1/100`, every entry `≠ 0` and `|G_{xy}| = |G_{xx} - m| = Ψ`. -/
def lwSizeD0 : LData (Idx 3 4 2) where
  G := fun x y => (if x = y then mE 0 else 0) + (1 / 100 : ℂ)
  M := fun x y => if x = y then mE 0 else 0
  S := lwSmat 3 4 2 (1 / 2) (1 / 2)
  Sp := lwSpOf 3 4 2 (1 / 2) (1 / 2) (mE 0)

private theorem lwSizeD0_hG : ∀ x y, x ≠ y → ‖lwSizeD0.G x y‖ ≤ 1 / 100 := by
  intro x y hxy
  simp [lwSizeD0, hxy]

private theorem lwSizeD0_hGd : ∀ x, ‖lwSizeD0.G x x - mE 0‖ ≤ 1 / 100 := by
  intro x
  simp [lwSizeD0]

/-- **Instance of target 1** (`(eq:estSpm-W)`): the entry bounds for `S` and `S^±` at `d = 3`, `L = 4`,
`W = 2`, `g = 1/2`, `E = 0`, `t = 1/2` (`Λ = 1`, `κ = 1/2`), with the sanity fact that `S` is not zero. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ x y : Idx 3 4 2, ‖lwSmat 3 4 2 (1 / 2) (1 / 2) x y‖ ≤
        C * ((2 : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 4 2 x y : ℝ)))) ∧
    (∀ x y : Idx 3 4 2, ‖lwSpOf 3 4 2 (1 / 2) (1 / 2) (mE 0) x y‖ ≤
        C * ((2 : ℝ) ^ 3)⁻¹ * Real.exp (-(c * (lwBdist 3 4 2 x y : ℝ)))) ∧
    lwSmat 3 4 2 (1 / 2) (1 / 2) 0 0 ≠ 0 := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  obtain ⟨h1, h2⟩ := h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C, c, hC, hc, by simpa using h1, by simpa using h2, ?_⟩
  intro h0
  have := lwSmat_entry (d := 3) (L := 4) (W := 2) (g := 1 / 2) (t := 1 / 2) (by norm_num) 0 0
  rw [h0, norm_zero] at this
  have hpos : 0 < sbKernelR 3 4 (1 / 2) ((split 3 4 2 0).1 - (split 3 4 2 0).1) := by
    simp only [sub_self, sbKernelR]
    norm_num
  have : (0 : ℝ) < 1 / 2 * ((2 : ℝ) ^ 3)⁻¹ * sbKernelR 3 4 (1 / 2) ((split 3 4 2 0).1 - (split 3 4 2 0).1) := by
    positivity
  simp_all

/-- A pair of distinct external labels on `Z_8^3`. -/
def lwSizeEll : Fin 2 → Idx 3 4 2 := ![fun _ => 0, fun _ => 1]

private theorem lwSizeD0_hM : ∀ x y, lwSizeD0.M x y = if x = y then mE 0 else 0 := fun _ _ => rfl

/-- **Instance of target 3** (`claim:size`, normal form) on the merged `p2Graph` (`n_S = 6`, `n_W = 2`,
`n_V = 4`, `n_M = 2`) at the concrete data `lwSizeD0` (`Ψ = 1/100`): every hypothesis is discharged. -/
example : ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧
    p2Graph.nS = 6 ∧ p2Graph.nW = 2 ∧ p2Graph.nV = 4 ∧ p2Graph.nM = 2 ∧
    ‖p2Graph.val lwSizeD0 lwSizeEll‖ ≤
      p2Graph.sizeConst K₀ K₁ * p2Graph.scalingSize (1 / 100) 2 3 4 := by
  obtain ⟨K₀, K₁, h₀, h₁, h⟩ := lwClaimSize_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  exact ⟨K₀, K₁, h₀, h₁, p2Graph_counters.1, p2Graph_counters.2.1, p2Graph_counters.2.2.1,
    p2Graph_counters.2.2.2,
    h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Fin 2) (Fin 4) p2Graph (by decide) lwSizeD0 rfl rfl lwSizeD0_hM (1 / 100)
      lwSizeD0_hG lwSizeD0_hGd lwSizeEll⟩

/-- **Instance of target 3, general-graph form** (`scalingSizeG`, the dotted edge partition) on `p2Graph`;
the partition is not empty: `size_G(p2Graph) = size(p2Graph)` (a normal graph without repeated dotted
edges), a positive number. -/
example : ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧
    0 < p2Graph.scalingSizeG (mE 0) (1 / 100) 2 3 4 ∧
    ‖p2Graph.val lwSizeD0 lwSizeEll‖ ≤
      p2Graph.sizeConstG (mE 0) K₀ K₁ * p2Graph.scalingSizeG (mE 0) (1 / 100) 2 3 4 := by
  obtain ⟨K₀, K₁, h₀, h₁, h⟩ := lwClaimSizeG_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  refine ⟨K₀, K₁, h₀, h₁, ?_,
    h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Fin 2) (Fin 4) p2Graph lwSizeD0 rfl rfl lwSizeD0_hM (1 / 100)
      lwSizeD0_hG lwSizeD0_hGd lwSizeEll⟩
  rw [LGraph.scalingSizeG_of_normal (mE 0) p2Graph (by decide) (by decide) (by norm_num)]
  unfold LGraph.scalingSize Counters.scalingSize
  positivity

/-- **Instance of target 2** (`scalemole`, the weighted sum over the internal vertices of the two molecules
of `p2Graph`): `Σ_{ℓ_I} ∏_{waved} |S_{αβ}| ≤ N^{n_M} K₁^{n_V - n_M} (K₀ W^{-d})^{n_W - (n_V - n_M)}`. -/
example : ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧
    ∑ ℓi : Fin 4 → Idx 3 4 2, (p2Graph.waved.map fun e => ‖WEdge.val lwSizeD0 (Sum.elim lwSizeEll ℓi) e‖).prod ≤
      (Fintype.card (Idx 3 4 2) : ℝ) ^ p2Graph.nM * K₁ ^ (p2Graph.nV - p2Graph.nM) *
        (K₀ * ((2 : ℝ) ^ 3)⁻¹) ^ (p2Graph.nW - (p2Graph.nV - p2Graph.nM)) := by
  obtain ⟨K₀, K₁, h₀, h₁, h⟩ := lwKBound_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  obtain ⟨hS, hSp⟩ := h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have : Nonempty (Idx 3 4 2) := ⟨fun _ => 0⟩
  refine ⟨K₀, K₁, h₀, h₁, ?_⟩
  have := p2Graph.waved_sum_le (by decide) lwSizeD0 hS hSp lwSizeEll
  simpa using this

/-- **Instance of target 2, the tail**: the weight of the labels at block distance `≥ 1` from `x` in a row
of `S^±` is `≤ C₂ e^{-c₂}` (`d = 3`, `L = 4`, `W = 2`, `g = t = 1/2`, `E = 0`), and the tail at the radius
`(log W)^{3/2}` is eventually `≤ W^{-3}`. -/
example : (∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ x : Idx 3 4 2,
    ∑ y ∈ Finset.univ.filter (fun y => 1 ≤ (lwBdist 3 4 2 x y : ℝ)),
      ‖lwSpOf 3 4 2 (1 / 2) (1 / 2) (mE 0) x y‖ ≤ C₂ * Real.exp (-(c₂ * 1))) ∧
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → Real.exp (-(1 * (Real.log W) ^ ((3 : ℝ) / 2) / 2)) ≤ (W : ℝ) ^ (-(3 : ℝ)) := by
  obtain ⟨C₂, c₂, h₀, h₁, h⟩ := lwSpOf_tail_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  exact ⟨⟨C₂, c₂, h₀, h₁, fun x => h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x 1⟩, lwTail_log32 one_pos 3⟩

end Instances

end RBM.Graph
