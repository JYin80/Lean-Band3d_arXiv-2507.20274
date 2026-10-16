/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEProcBA
import RBM3D.BA.GUEOneLoop
import RBM3D.BA.TwistAvgA2

/-!
# BA-C5 row b′, part 1: the twisted 1-loop law on the GUE grid at block Anderson, Steps 1-3

Ticket T2519 (row b′; Amend 1 item 5, Amend 2 items 1-3, Amend 3 items 2-3; design gate D1 (i)
signed by `docs/reports/T2519-1a-audit.md`, probe `t/T2519` b992c2e7).  New BA leaf: no merged
file is edited.  The target `gueGrid_twistBA` (text `T2519_HoffBA`) is in `BA/GUETwistBA2`; this
file has Steps 1-3 of Lemma T.7 (TL1, `docs/tickets/T2398-TL-proofs.md:64-78`; its input
Lemma 8.3 is `lem:propM`, `paper/tex/7_8_light_weight.tex:1846-1910`) on the one-time Gaussian
law `law v` of the grid path, `v_c = t₁ gvar_c + c₀ w_c`, `Ŝ = t₁ S^{(B)}(0) + σ`
(`S^{(B)}(0) = 1`):

* §1 the twist matrix `Π_{qa}`, `Π Π^* = W^d E_a`; §2 Cauchy-Schwarz for traces; §3 the
  Hilbert-Schmidt bounds `GUETwistBA_RB1`, `GUETwistBA_RB2` of the two derivative terms against
  2- and 4-loops (Step 3); §4 the pair contraction `Σ_c v_c tr(A B_c) tr(C B_c)` (from
  `sum_coordinateBlock_trace_pair` and `OneLoop_sum_gue_block` at matrix units) and its two
  forms `𝒞₁`, `𝒞₂`; §5 the Stein identity with a test function and the Stein defect;
  §6 `Φ_p(x) = x^{p-1} x̄^p`; §7 the pointwise identity `G - M = -M(u m + X) G` for the twisted
  trace; §8 the vocabulary `GUETwistBA_Tm`, `_Dm`, `_R1m`, `_R2m`, `_g1`-`_g3`;
  §9 **`GUETwistBA_momentId`** (Steps 1-2: `𝔼|T_{qa}|^{2p} = 𝔼[Σ_{p'} M_{qp'} D_{p'}
  (M_{p'a} + T_{p'a}) Φ_p(T_{qa}) + (p-1) R₁ T^{p-2} T̄^p + p R₂ |T|^{2p-2}]`);
  §10 the envelope and the good-event bounds of `D`, `R₁`, `R₂`; §11 the PB interface
  `GUETwistBA_good` (`GUEPathBoundsBA` `lk 1, 2, 4`, `localLaw`, the K-bound and `Kt = m` give
  the good event off a set of probability `≤ N^{-D}`); §12 the identity
  `t_{aq} - M^{(++)}_{aq} = M^{(B)}_{aq} T_{qa}` (T2517 `(a)` row 8) and the entrywise bound of
  `T_{qa}`.
Private pieces of `BA/GUEOneLoop`, `Chain/ExpAvgGen` and `GUEPhase/OneLoop` are read by
`open private`; the pure-algebra lemmas `TwistAvgA2_cs`, `lwWx_Gres_conjTranspose` are read by
name.  Helpers carry the stem `GUETwistBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open private ExpAvgGen_G_cont ExpAvgGen_G_norm ExpAvgGen_Hb_herm ExpAvgGen_trG_bdd ExpAvgGen_trace3_le ExpAvgGen_norm_GXG
  ExpAvgGen_trace_expand ExpAvgGen_resolvent_id ExpAvgGen_Gres_blockMat ExpAvgGen_sum_Eblk ExpAvgGen_trace_Eblk
  ExpAvgGen_trace_four ExpAvgGen_HflowBlock_eq ExpAvgGen_blockMat_mul ExpAvgGen_blockMat_sub_smul ExpAvgGen_blockMat_one
  from RBM3D.Chain.ExpAvgGen
open private OneLoop_integrable_coord_smul OneLoop_integrable_of_cont_bdd OneLoop_sum_gue_block OneLoop_blockMat_Xmat
  OneLoop_gloop_one OneLoop_card_Zd from RBM3D.Universality.GUEPhase.OneLoop
open private GUEOneLoop_contract GUEOneLoop_H0_herm GUEOneLoop_Mdata from RBM3D.BA.GUEOneLoop

noncomputable section

namespace RBM.BA

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

section TwistAlg

variable {d L W : ℕ} [NeZero L] [NeZero W]

def GUETwistBA_Pi (d L W : ℕ) (q a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.of fun x y => if x.1 = a ∧ y.1 = q ∧ x.2 = y.2 then 1 else 0

theorem GUETwistBA_Pi_apply (q a : Zd d L) (x y : Vtx d L W) :
    GUETwistBA_Pi d L W q a x y = if x.1 = a ∧ y.1 = q ∧ x.2 = y.2 then 1 else 0 := rfl

theorem GUETwistBA_trace_Pi (Z : Matrix (Vtx d L W) (Vtx d L W) ℂ) (q a : Zd d L) :
    Matrix.trace (Z * GUETwistBA_Pi d L W q a) = ∑ o : Fin (W ^ d), Z (q, o) (a, o) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, GUETwistBA_Pi, Matrix.of_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem GUETwistBA_Pi_conjTranspose (q a : Zd d L) :
    (GUETwistBA_Pi d L W q a)ᴴ = GUETwistBA_Pi d L W a q := by
  ext x y
  simp only [Matrix.conjTranspose_apply, GUETwistBA_Pi_apply, apply_ite (star : ℂ → ℂ), star_one, star_zero]
  by_cases h : x.2 = y.2
  · simp [h, and_comm]
  · simp [h, Ne.symm h]

theorem GUETwistBA_Pi_mul_Pi_conjTranspose (q a : Zd d L) :
    GUETwistBA_Pi d L W q a * (GUETwistBA_Pi d L W q a)ᴴ = ((W : ℂ) ^ d) • Eblk d L W a := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  rw [GUETwistBA_Pi_conjTranspose]
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  simp only [Matrix.mul_apply, GUETwistBA_Pi_apply, Eblk_apply, Matrix.smul_apply, Fintype.sum_prod_type, smul_eq_mul]
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single x₂ (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ _) h)]
  by_cases h1 : x₁ = a <;> by_cases h2 : y₁ = a <;> by_cases h3 : x₂ = y₂ <;> simp [h1, h2, h3, hW, eq_comm (a := a)]

theorem GUETwistBA_Pi_conjTranspose_mul_Pi (q a : Zd d L) :
    (GUETwistBA_Pi d L W q a)ᴴ * GUETwistBA_Pi d L W q a = ((W : ℂ) ^ d) • Eblk d L W q := by
  have h := GUETwistBA_Pi_mul_Pi_conjTranspose (d := d) (L := L) (W := W) a q
  rw [GUETwistBA_Pi_conjTranspose a q] at h
  rw [GUETwistBA_Pi_conjTranspose q a]
  exact h

theorem GUETwistBA_Eblk_mul_Pi (q a : Zd d L) :
    ((W : ℂ) ^ d) • Eblk d L W a * GUETwistBA_Pi d L W q a = GUETwistBA_Pi d L W q a := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  ext x y
  simp only [Eblk, Matrix.smul_mul, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, GUETwistBA_Pi_apply]
  by_cases h : x.1 = a <;> simp [h, hW]

theorem GUETwistBA_Pi_mul_Eblk (q a : Zd d L) :
    GUETwistBA_Pi d L W q a * (((W : ℂ) ^ d) • Eblk d L W q) = GUETwistBA_Pi d L W q a := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  ext x y
  simp only [Eblk, Matrix.mul_smul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, GUETwistBA_Pi_apply]
  by_cases h : y.1 = q <;> simp [h, hW]

theorem GUETwistBA_Pi_mul_Eblk_ne (p' a p : Zd d L) :
    GUETwistBA_Pi d L W p' a * Eblk d L W p = if p = p' then (((W : ℂ) ^ d)⁻¹) • GUETwistBA_Pi d L W p' a else 0 := by
  ext x y
  by_cases hp : p = p'
  · subst hp
    by_cases h : y.1 = p <;> simp [Eblk, Matrix.mul_diagonal, GUETwistBA_Pi_apply, h]
  · by_cases h : y.1 = p <;> simp [Eblk, Matrix.mul_diagonal, GUETwistBA_Pi_apply, h, hp]

end TwistAlg


section CSAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GUETwistBA_trace_mul_conjTranspose (U : Matrix ι ι ℂ) :
    Matrix.trace (U * Uᴴ) = ((∑ i, ∑ k, ‖U i k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj']; push_cast; ring

theorem GUETwistBA_trace_conjTranspose_mul (V : Matrix ι ι ℂ) :
    Matrix.trace (Vᴴ * V) = ((∑ k, ∑ i, ‖V k i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace_mul_comm, GUETwistBA_trace_mul_conjTranspose]

theorem GUETwistBA_norm_trace_mul_le (U V : Matrix ι ι ℂ) :
    ‖Matrix.trace (U * V)‖ ≤ Real.sqrt ‖Matrix.trace (U * Uᴴ)‖ * Real.sqrt ‖Matrix.trace (Vᴴ * V)‖ := by
  have h := TwistAvgA2_cs (fun i k => U i k) (fun k i => V k i)
  have e1 : ‖Matrix.trace (U * Uᴴ)‖ = ∑ i, ∑ k, ‖U i k‖ ^ 2 := by
    rw [GUETwistBA_trace_mul_conjTranspose, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  have e2 : ‖Matrix.trace (Vᴴ * V)‖ = ∑ k, ∑ i, ‖V k i‖ ^ 2 := by
    rw [GUETwistBA_trace_conjTranspose_mul, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  rw [e1, e2]
  simpa [Matrix.trace, Matrix.mul_apply] using h

theorem GUETwistBA_norm_trace_mul_le_proj (U V P Q : Matrix ι ι ℂ)
    (hPU : P * U = U) (hUQ : U * Q = U) (hP : Pᴴ = P) (hPP : P * P = P) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) :
    ‖Matrix.trace (U * V)‖ ≤ Real.sqrt ‖Matrix.trace (U * Uᴴ)‖ * Real.sqrt ‖Matrix.trace (Vᴴ * Q * V * P)‖ := by
  have hU : U = P * U * Q := by rw [Matrix.mul_assoc, hUQ, hPU]
  have h1 : Matrix.trace (U * V) = Matrix.trace (U * (Q * V * P)) := by
    calc Matrix.trace (U * V) = Matrix.trace (P * U * Q * V) := by rw [← hU]
      _ = Matrix.trace (P * (U * Q * V)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((U * Q * V) * P) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (U * (Q * V * P)) := by simp only [Matrix.mul_assoc]
  have h2 : Matrix.trace ((Q * V * P)ᴴ * (Q * V * P)) = Matrix.trace (Vᴴ * Q * V * P) := by
    calc Matrix.trace ((Q * V * P)ᴴ * (Q * V * P)) = Matrix.trace (P * (Vᴴ * (Q * Q) * V * P)) := by
          simp only [Matrix.conjTranspose_mul, hP, hQ, Matrix.mul_assoc]
      _ = Matrix.trace ((Vᴴ * (Q * Q) * V * P) * P) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Vᴴ * Q * V * P) := by rw [hQQ]; simp only [Matrix.mul_assoc, hPP]
  rw [h1]
  refine (GUETwistBA_norm_trace_mul_le U (Q * V * P)).trans ?_
  rw [h2]

end CSAlg


section Loops

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem GUETwistBA_loop2 (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    loopL d L W H z ⟨[σ₁, σ₂], [a, b]⟩ =
      Matrix.trace (Gres H z σ₁ * Eblk d L W a * (Gres H z σ₂ * Eblk d L W b)) := by
  simp [loopL]

theorem GUETwistBA_loop4 (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (σ₁ σ₂ σ₃ σ₄ : Bool) (a b c e : Zd d L) :
    loopL d L W H z ⟨[σ₁, σ₂, σ₃, σ₄], [a, b, c, e]⟩ =
      Matrix.trace (Gres H z σ₁ * Eblk d L W a * (Gres H z σ₂ * Eblk d L W b * (Gres H z σ₃ * Eblk d L W c *
        (Gres H z σ₄ * Eblk d L W e)))) := by
  simp [loopL]

theorem GUETwistBA_Pb_mul (a : Zd d L) :
    (((W : ℂ) ^ d) • Eblk d L W a) * (((W : ℂ) ^ d) • Eblk d L W a) = ((W : ℂ) ^ d) • Eblk d L W a := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  ext x y
  simp only [Eblk, Matrix.smul_mul, Matrix.mul_smul, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases h : x.1 = a <;> simp [h, hW]
  · simp [hxy]

theorem GUETwistBA_Pb_conjTranspose (a : Zd d L) :
    (((W : ℂ) ^ d) • Eblk d L W a)ᴴ = ((W : ℂ) ^ d) • Eblk d L W a := by
  rw [Matrix.conjTranspose_smul, (Eblk_isHermitian a).eq]
  simp

theorem GUETwistBA_sqrt_scale (l : ℂ) :
    Real.sqrt ‖((W : ℂ) ^ d) ^ 2 * l‖ = ((W : ℝ) ^ d) * Real.sqrt ‖l‖ := by
  have h : ‖((W : ℂ) ^ d) ^ 2 * l‖ = (((W : ℝ) ^ d) ^ 2) * ‖l‖ := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem GUETwistBA_RB1 {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (p' q a s : Zd d L) :
    ‖Matrix.trace (GUETwistBA_Pi d L W p' a * Gres H z true * GUETwistBA_Pi d L W q a *
        (Gres H z true * Eblk d L W s * Gres H z true))‖ ≤
      ((W : ℝ) ^ d) ^ 2 * (Real.sqrt ‖loopL d L W H z ⟨[true, false], [a, p']⟩‖ *
        Real.sqrt ‖loopL d L W H z ⟨[false, false, true, true], [s, q, s, a]⟩‖) := by
  have hGb : Gres H z false = (Gres H z true)ᴴ := (RBM.Graph.lwWx_Gres_conjTranspose hH z).symm
  have hEs := (Eblk_isHermitian (d := d) (L := L) (W := W) s).eq
  have hcs := GUETwistBA_norm_trace_mul_le_proj
    (GUETwistBA_Pi d L W p' a * Gres H z true * GUETwistBA_Pi d L W q a) (Gres H z true * Eblk d L W s * Gres H z true)
    (((W : ℂ) ^ d) • Eblk d L W a) (((W : ℂ) ^ d) • Eblk d L W q)
    (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GUETwistBA_Eblk_mul_Pi])
    (by rw [Matrix.mul_assoc, GUETwistBA_Pi_mul_Eblk])
    (GUETwistBA_Pb_conjTranspose a) (GUETwistBA_Pb_mul a) (GUETwistBA_Pb_conjTranspose q) (GUETwistBA_Pb_mul q)
  have e1 : Matrix.trace ((GUETwistBA_Pi d L W p' a * Gres H z true * GUETwistBA_Pi d L W q a) *
      (GUETwistBA_Pi d L W p' a * Gres H z true * GUETwistBA_Pi d L W q a)ᴴ) =
      ((W : ℂ) ^ d) ^ 2 * loopL d L W H z ⟨[true, false], [a, p']⟩ := by
    rw [GUETwistBA_loop2, hGb]
    calc Matrix.trace ((GUETwistBA_Pi d L W p' a * Gres H z true * GUETwistBA_Pi d L W q a) *
          (GUETwistBA_Pi d L W p' a * Gres H z true * GUETwistBA_Pi d L W q a)ᴴ)
        = Matrix.trace (GUETwistBA_Pi d L W p' a * (Gres H z true * (GUETwistBA_Pi d L W q a * (GUETwistBA_Pi d L W q a)ᴴ *
            ((Gres H z true)ᴴ * (GUETwistBA_Pi d L W p' a)ᴴ)))) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Matrix.trace ((Gres H z true * ((((W : ℂ) ^ d) • Eblk d L W a) * ((Gres H z true)ᴴ * (GUETwistBA_Pi d L W p' a)ᴴ))) *
            GUETwistBA_Pi d L W p' a) := by
          rw [GUETwistBA_Pi_mul_Pi_conjTranspose]; exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Gres H z true * (((W : ℂ) ^ d) • Eblk d L W a) * (Gres H z true)ᴴ) *
            ((GUETwistBA_Pi d L W p' a)ᴴ * GUETwistBA_Pi d L W p' a)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((GUETwistBA_Pi d L W p' a)ᴴ * GUETwistBA_Pi d L W p' a) *
            (Gres H z true * (((W : ℂ) ^ d) • Eblk d L W a) * (Gres H z true)ᴴ)) := Matrix.trace_mul_comm _ _
      _ = _ := by
          rw [GUETwistBA_Pi_conjTranspose_mul_Pi]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
          ring
  have e2 : Matrix.trace ((Gres H z true * Eblk d L W s * Gres H z true)ᴴ * (((W : ℂ) ^ d) • Eblk d L W q) *
      (Gres H z true * Eblk d L W s * Gres H z true) * (((W : ℂ) ^ d) • Eblk d L W a)) =
      ((W : ℂ) ^ d) ^ 2 * loopL d L W H z ⟨[false, false, true, true], [s, q, s, a]⟩ := by
    rw [GUETwistBA_loop4, hGb]
    simp only [Matrix.conjTranspose_mul, hEs, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
    ring
  rw [e1, e2, GUETwistBA_sqrt_scale, GUETwistBA_sqrt_scale] at hcs
  refine hcs.trans (le_of_eq ?_)
  ring

theorem GUETwistBA_RB2 {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (p' q a s : Zd d L) :
    ‖Matrix.trace (GUETwistBA_Pi d L W p' a * (Gres H z true)ᴴ * (GUETwistBA_Pi d L W q a)ᴴ *
        ((Gres H z true)ᴴ * Eblk d L W s * Gres H z true))‖ ≤
      ((W : ℝ) ^ d) ^ 2 * (Real.sqrt ‖loopL d L W H z ⟨[false, true], [q, p']⟩‖ *
        Real.sqrt ‖loopL d L W H z ⟨[false, true, false, true], [s, a, s, a]⟩‖) := by
  have hGb : Gres H z false = (Gres H z true)ᴴ := (RBM.Graph.lwWx_Gres_conjTranspose hH z).symm
  have hEs := (Eblk_isHermitian (d := d) (L := L) (W := W) s).eq
  have hPq : (GUETwistBA_Pi d L W q a)ᴴ = GUETwistBA_Pi d L W a q := GUETwistBA_Pi_conjTranspose q a
  have hcs := GUETwistBA_norm_trace_mul_le_proj
    (GUETwistBA_Pi d L W p' a * (Gres H z true)ᴴ * (GUETwistBA_Pi d L W q a)ᴴ) ((Gres H z true)ᴴ * Eblk d L W s * Gres H z true)
    (((W : ℂ) ^ d) • Eblk d L W a) (((W : ℂ) ^ d) • Eblk d L W a)
    (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GUETwistBA_Eblk_mul_Pi])
    (by rw [Matrix.mul_assoc, hPq, GUETwistBA_Pi_mul_Eblk])
    (GUETwistBA_Pb_conjTranspose a) (GUETwistBA_Pb_mul a) (GUETwistBA_Pb_conjTranspose a) (GUETwistBA_Pb_mul a)
  have e1 : Matrix.trace ((GUETwistBA_Pi d L W p' a * (Gres H z true)ᴴ * (GUETwistBA_Pi d L W q a)ᴴ) *
      (GUETwistBA_Pi d L W p' a * (Gres H z true)ᴴ * (GUETwistBA_Pi d L W q a)ᴴ)ᴴ) =
      ((W : ℂ) ^ d) ^ 2 * loopL d L W H z ⟨[false, true], [q, p']⟩ := by
    rw [GUETwistBA_loop2, hGb]
    calc Matrix.trace ((GUETwistBA_Pi d L W p' a * (Gres H z true)ᴴ * (GUETwistBA_Pi d L W q a)ᴴ) *
          (GUETwistBA_Pi d L W p' a * (Gres H z true)ᴴ * (GUETwistBA_Pi d L W q a)ᴴ)ᴴ)
        = Matrix.trace (GUETwistBA_Pi d L W p' a * ((Gres H z true)ᴴ * (((GUETwistBA_Pi d L W q a)ᴴ * GUETwistBA_Pi d L W q a) *
            (Gres H z true * (GUETwistBA_Pi d L W p' a)ᴴ)))) := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Matrix.trace (((Gres H z true)ᴴ * ((((W : ℂ) ^ d) • Eblk d L W q) * (Gres H z true * (GUETwistBA_Pi d L W p' a)ᴴ))) *
            GUETwistBA_Pi d L W p' a) := by
          rw [GUETwistBA_Pi_conjTranspose_mul_Pi]; exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (((Gres H z true)ᴴ * (((W : ℂ) ^ d) • Eblk d L W q) * Gres H z true) *
            ((GUETwistBA_Pi d L W p' a)ᴴ * GUETwistBA_Pi d L W p' a)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((GUETwistBA_Pi d L W p' a)ᴴ * GUETwistBA_Pi d L W p' a) *
            ((Gres H z true)ᴴ * (((W : ℂ) ^ d) • Eblk d L W q) * Gres H z true)) := Matrix.trace_mul_comm _ _
      _ = _ := by
          rw [GUETwistBA_Pi_conjTranspose_mul_Pi]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
          ring
  have e2 : Matrix.trace (((Gres H z true)ᴴ * Eblk d L W s * Gres H z true)ᴴ * (((W : ℂ) ^ d) • Eblk d L W a) *
      ((Gres H z true)ᴴ * Eblk d L W s * Gres H z true) * (((W : ℂ) ^ d) • Eblk d L W a)) =
      ((W : ℂ) ^ d) ^ 2 * loopL d L W H z ⟨[false, true, false, true], [s, a, s, a]⟩ := by
    rw [GUETwistBA_loop4, hGb]
    simp only [Matrix.conjTranspose_mul, hEs, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
    ring
  rw [e1, e2, GUETwistBA_sqrt_scale, GUETwistBA_sqrt_scale] at hcs
  refine hcs.trans (le_of_eq ?_)
  ring

end Loops


section Pair

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem GUETwistBA_trace_single_mul_Eblk (j k : Vtx d L W) (p : Zd d L) :
    Matrix.trace (Matrix.single k j (1 : ℂ) * Eblk d L W p) = if j = k then (if j.1 = p then ((W : ℂ) ^ d)⁻¹ else 0) else 0 := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.single_apply, Eblk_apply]
  by_cases h : j = k
  · subst h
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
    refine Finset.sum_eq_zero fun a _ => ?_
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases h1 : k = a ∧ j = b <;> by_cases h2 : b = a <;> simp_all

/-- `tr(A B) tr(C B)` as a sum of four-fold products of entries of `B`, in the form of `sum_coordinateBlock_trace_pair`. -/
theorem GUETwistBA_trace_pair_expand (A C B : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (A * B) * Matrix.trace (C * B) =
      ∑ i, ∑ j, ∑ k, ∑ l, A i k * C j l * Matrix.trace (Matrix.single j k (1 : ℂ) * B * Matrix.single i l (1 : ℂ) * B) := by
  classical
  have h : ∀ i k j l : Vtx d L W, Matrix.trace (Matrix.single j k (1 : ℂ) * B * Matrix.single i l (1 : ℂ) * B) = B k i * B l j := by
    intro i k j l
    have h1 := trace_mul_single_mul_single B B j k i l (1 : ℂ) (1 : ℂ)
    calc Matrix.trace (Matrix.single j k (1 : ℂ) * B * Matrix.single i l (1 : ℂ) * B)
        = Matrix.trace (B * Matrix.single j k (1 : ℂ) * B * Matrix.single i l (1 : ℂ)) := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = B k i * B l j := by rw [h1]; ring
  simp only [h]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring


theorem GUETwistBA_sum_comm5 {α β γ δ ε R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε] [AddCommMonoid R]
    (F : α → β → γ → δ → ε → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, F a b c d e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]

theorem GUETwistBA_sum_comm4 {α β γ δ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (F : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ d, ∑ b, F a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem GUETwistBA_trace_E_A_E_C (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s p : Zd d L) :
    Matrix.trace (Eblk d L W s * A * Eblk d L W p * C) =
      ∑ i, ∑ k, (if i.1 = s then ((W : ℂ) ^ d)⁻¹ else 0) * A i k * (if k.1 = p then ((W : ℂ) ^ d)⁻¹ else 0) * C k i := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Eblk, Matrix.mul_diagonal, Matrix.diagonal_mul]


theorem GUETwistBA_pair_gvar (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) =
      ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, SB d L 0 p s * Matrix.trace (Eblk d L W s * A * Eblk d L W p * C) := by
  classical
  have e1 : ∀ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) =
      ∑ i, ∑ j, ∑ k, ∑ l, (A i k * C j l) * (((gvarF d L W 0 c : ℝ) : ℂ) *
        Matrix.trace (Matrix.single j k (1 : ℂ) * coordinateBlock d L W c * Matrix.single i l (1 : ℂ) * coordinateBlock d L W c)) := by
    intro c
    rw [GUETwistBA_trace_pair_expand A C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hL : ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) =
      ∑ i, ∑ j, ∑ k, ∑ l, (A i k * C j l) * (((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace (Matrix.single j k (1 : ℂ) * Eblk d L W p) * SB d L 0 p q * Matrix.trace (Matrix.single i l (1 : ℂ) * Eblk d L W q)) := by
    rw [Finset.sum_congr rfl fun c _ => e1 c, GUETwistBA_sum_comm5]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum, sum_coordinateBlock_trace_pair d L W 0 (Matrix.single j k (1 : ℂ)) (Matrix.single i l (1 : ℂ))]
  rw [hL]
  simp only [GUETwistBA_trace_single_mul_Eblk, GUETwistBA_trace_E_A_E_C]
  -- the left side: the Kronecker deltas collapse the sums over `p, q` and over the second row/column
  have hl : ∀ x x1 x2 x3 : Vtx d L W, A x x2 * C x1 x3 * (((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L,
      (if x2 = x1 then if x2.1 = p then ((W : ℂ) ^ d)⁻¹ else 0 else 0) * SB d L 0 p q *
        (if x3 = x then if x3.1 = q then ((W : ℂ) ^ d)⁻¹ else 0 else 0)) =
      if x2 = x1 then (if x3 = x then A x x2 * C x1 x3 * (((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹ * SB d L 0 x2.1 x3.1 * ((W : ℂ) ^ d)⁻¹)) else 0) else 0 := by
    intro x x1 x2 x3
    by_cases h1 : x2 = x1 <;> by_cases h2 : x3 = x <;> simp [h1, h2]
  simp only [hl, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [GUETwistBA_sum_comm4]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring


theorem GUETwistBA_trace_eq_sum_E (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (A * C) = ((W : ℂ) ^ d) ^ 2 * ∑ p : Zd d L, ∑ s : Zd d L, Matrix.trace (Eblk d L W s * A * Eblk d L W p * C) := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have h1 : ∑ p : Zd d L, ∑ s : Zd d L, Matrix.trace (Eblk d L W s * A * Eblk d L W p * C) =
      Matrix.trace ((∑ s : Zd d L, Eblk d L W s) * A * (∑ p : Zd d L, Eblk d L W p) * C) := by
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  rw [h1, ExpAvgGen_sum_Eblk]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  field_simp

theorem GUETwistBA_pair_unif (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) =
      Matrix.trace (A * C) := by
  classical
  have e1 : ∀ c : CoordF d L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) =
      ∑ i, ∑ j, ∑ k, ∑ l, (A i k * C j l) * ((if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (Matrix.single j k (1 : ℂ) * coordinateBlock d L W c * Matrix.single i l (1 : ℂ) * coordinateBlock d L W c)) := by
    intro c
    rw [GUETwistBA_trace_pair_expand A C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun c _ => e1 c, GUETwistBA_sum_comm5]
  have e2 : ∀ i j k l : Vtx d L W, ∑ c : CoordF d L W, (A i k * C j l) * ((if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (Matrix.single j k (1 : ℂ) * coordinateBlock d L W c * Matrix.single i l (1 : ℂ) * coordinateBlock d L W c)) =
      (A i k * C j l) * ((if j = k then (1 : ℂ) else 0) * (if i = l then (1 : ℂ) else 0)) := by
    intro i j k l
    rw [← Finset.mul_sum, OneLoop_sum_gue_block d L W]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.single_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases h1 : i = l
    · subst h1
      by_cases h2 : j = k
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · simp [h1, Ne.symm h1]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => e2 i j k l]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]


/-- **The pair contraction under the mixed variances** `v_c = t₁ gvar_c + c₀ w_c`:
`Σ_c v_c tr(A B_c) tr(C B_c) = W^d Σ_{p,s} Ŝ_{ps} tr(E_s A E_p C)`, `Ŝ = t₁ S^{(B)}(0) + σ`, `σ = c₀ W^d`
(the product of two traces: `sum_coordinateBlock_trace_pair` and `OneLoop_sum_gue_block` at matrix units). -/
theorem GUETwistBA_pair {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) =
      ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) * Matrix.trace (Eblk d L W s * A * Eblk d L W p * C) := by
  have hvC : ∀ c : CoordF d L W, ((v c : ℝ) : ℂ) =
      (t1 : ℂ) * ((gvarF d L W 0 c : ℝ) : ℂ) + (c0 : ℂ) * (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) := by
    intro c
    rw [hv c]
    split_ifs <;> push_cast <;> ring
  have hsplit : ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) =
      (t1 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) +
      (c0 : ℂ) * ∑ c : CoordF d L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        (Matrix.trace (A * coordinateBlock d L W c) * Matrix.trace (C * coordinateBlock d L W c)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hvC c]
    ring
  rw [hsplit, GUETwistBA_pair_gvar, GUETwistBA_pair_unif, GUETwistBA_trace_eq_sum_E A C, hσ]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  push_cast
  simp only [mul_add, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring

end Pair

section CEq

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The collapse of the block sum `Σ_p` of the pair contraction against `Π_{p'a}`: `Π E_p = δ_{pp'} W^{-d} Π`. -/
theorem GUETwistBA_pair_collapse {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (G Cm : Matrix (Vtx d L W) (Vtx d L W) ℂ) (p' a : Zd d L) :
    ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) *
        (Matrix.trace (G * GUETwistBA_Pi d L W p' a * coordinateBlock d L W c) * Matrix.trace (Cm * coordinateBlock d L W c)) =
      ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
        Matrix.trace (Eblk d L W s * G * GUETwistBA_Pi d L W p' a * Cm) := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  rw [GUETwistBA_pair hσ v hv]
  rw [Finset.sum_eq_single p' (fun p _ hp => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : Eblk d L W s * (G * GUETwistBA_Pi d L W p' a) * Eblk d L W p' * Cm =
        Eblk d L W s * G * (GUETwistBA_Pi d L W p' a * Eblk d L W p') * Cm := by simp only [Matrix.mul_assoc]
    rw [this, GUETwistBA_Pi_mul_Eblk_ne]
    simp only [ite_true, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
    field_simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    have : Eblk d L W s * (G * GUETwistBA_Pi d L W p' a) * Eblk d L W p * Cm =
        Eblk d L W s * G * (GUETwistBA_Pi d L W p' a * Eblk d L W p) * Cm := by simp only [Matrix.mul_assoc]
    rw [this, GUETwistBA_Pi_mul_Eblk_ne]
    simp [hp]


theorem GUETwistBA_coordinateBlock_conjTranspose (c : CoordF d L W) :
    (coordinateBlock d L W c)ᴴ = coordinateBlock d L W c :=
  ((coordinateMatrix_isHermitian d L W c).submatrix _).eq

theorem GUETwistBA_star_trace_mul_coordinateBlock (Cm : Matrix (Vtx d L W) (Vtx d L W) ℂ) (c : CoordF d L W) :
    star (Matrix.trace (Cm * coordinateBlock d L W c)) = Matrix.trace (Cmᴴ * coordinateBlock d L W c) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, GUETwistBA_coordinateBlock_conjTranspose]
  exact Matrix.trace_mul_comm _ _

theorem GUETwistBA_trace_cycle1 {ι : Type*} [Fintype ι] [DecidableEq ι] (E G P1 P2 : Matrix ι ι ℂ) :
    Matrix.trace (E * G * P1 * (G * P2 * G)) = Matrix.trace (P1 * G * P2 * (G * E * G)) := by
  calc Matrix.trace (E * G * P1 * (G * P2 * G)) = Matrix.trace ((E * G) * (P1 * (G * P2 * G))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((P1 * (G * P2 * G)) * (E * G)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (P1 * G * P2 * (G * E * G)) := by simp only [Matrix.mul_assoc]

theorem GUETwistBA_trace_cycle2 {ι : Type*} [Fintype ι] [DecidableEq ι] (E G P1 P2 : Matrix ι ι ℂ) :
    Matrix.trace (E * G * P1 * (G * P2 * G)ᴴ) = Matrix.trace (P1 * Gᴴ * P2ᴴ * (Gᴴ * E * G)) := by
  calc Matrix.trace (E * G * P1 * (G * P2 * G)ᴴ) = Matrix.trace ((E * G) * (P1 * (G * P2 * G)ᴴ)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((P1 * (G * P2 * G)ᴴ) * (E * G)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (P1 * Gᴴ * P2ᴴ * (Gᴴ * E * G)) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- `𝒞₁^{p'} = Σ_c v_c tr(B_c G Π_{p'a}) tr(B_c G Π_{qa} G) = Σ_s Ŝ_{p's} tr(Π_{p'a} G Π_{qa} · G E_s G)`. -/
theorem GUETwistBA_C1_eq {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (p' q a : Zd d L) :
    ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) *
        (Matrix.trace (G * GUETwistBA_Pi d L W p' a * coordinateBlock d L W c) *
          Matrix.trace (G * GUETwistBA_Pi d L W q a * G * coordinateBlock d L W c)) =
      ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
        Matrix.trace (GUETwistBA_Pi d L W p' a * G * GUETwistBA_Pi d L W q a * (G * Eblk d L W s * G)) := by
  rw [GUETwistBA_pair_collapse hσ v hv G (G * GUETwistBA_Pi d L W q a * G) p' a]
  exact Finset.sum_congr rfl fun s _ => by rw [GUETwistBA_trace_cycle1]

/-- `𝒞₂^{p'} = Σ_c v_c tr(B_c G Π_{p'a}) conj tr(B_c G Π_{qa} G) = Σ_s Ŝ_{p's} tr(Π_{p'a} G^* Π_{qa}^* · G^* E_s G)`. -/
theorem GUETwistBA_C2_eq {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (p' q a : Zd d L) :
    ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) *
        (Matrix.trace (G * GUETwistBA_Pi d L W p' a * coordinateBlock d L W c) *
          star (Matrix.trace (G * GUETwistBA_Pi d L W q a * G * coordinateBlock d L W c))) =
      ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
        Matrix.trace (GUETwistBA_Pi d L W p' a * Gᴴ * (GUETwistBA_Pi d L W q a)ᴴ * (Gᴴ * Eblk d L W s * G)) := by
  simp only [GUETwistBA_star_trace_mul_coordinateBlock]
  rw [GUETwistBA_pair_collapse hσ v hv G (G * GUETwistBA_Pi d L W q a * G)ᴴ p' a]
  exact Finset.sum_congr rfl fun s _ => by rw [GUETwistBA_trace_cycle2]

end CEq

section SteinF

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `∂_{ω_c} G = -G B_c G` along the coordinate fibre. -/
theorem GUETwistBA_hasDerivAt_G {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Ω d L W) (c : CoordF d L W) :
    HasDerivAt (fun t : ℝ => Gres (H₀b + HflowBlock d L W 1 (Function.update ω c t)) z true)
      (-(Gres (H₀b + HflowBlock d L W 1 ω) z true * coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true)) (ω c) := by
  have h1 := hasDerivAt_green_moving (H := fun t : ℝ => H₀b + HflowBlock d L W 1 (Function.update ω c t)) (z := fun _ => z)
    ((hasDerivAt_HflowBlock_update d L W 1 ω c).const_add H₀b) (hasDerivAt_const (ω c) z)
    (by simpa only [Function.update_eq_self] using ExpAvgGen_Hb_herm hH 1 ω) hz
  refine h1.congr_deriv ?_
  simp only [Function.update_eq_self, zero_smul, sub_zero, Real.sqrt_one, one_smul]

/-- A continuous function of the resolvent is bounded (the ball `‖G‖ ≤ |Im z|⁻¹` is compact). -/
theorem GUETwistBA_bdd_comp {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (Ψ : Matrix (Vtx d L W) (Vtx d L W) ℂ → ℂ) (hΨ : Continuous Ψ) :
    ∃ C : ℝ, ∀ ω : Ω d L W, ‖Ψ (Gres (H₀b + HflowBlock d L W 1 ω) z true)‖ ≤ C := by
  have : ProperSpace (Matrix (Vtx d L W) (Vtx d L W) ℂ) := FiniteDimensional.proper_rclike ℂ _
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Matrix (Vtx d L W) (Vtx d L W) ℂ) |z.im|⁻¹).exists_bound_of_continuousOn hΨ.continuousOn
  exact ⟨C, fun ω => hC _ (by simpa using ExpAvgGen_G_norm hH 1 hz ω)⟩

theorem GUETwistBA_cont_GBG (B K : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Continuous fun G : Matrix (Vtx d L W) (Vtx d L W) ℂ => Matrix.trace (B * (-(G * B * G)) * K) :=
  (continuous_matrixTrace d L W).comp ((continuous_const.mul (((continuous_id.mul continuous_const).mul continuous_id).neg)).mul
    continuous_const)

theorem GUETwistBA_integrable_of_cont_bdd (v : CoordF d L W → ℝ≥0) {f : Ω d L W → ℂ} (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C) : Integrable f (GaussianProduct.law v) := by
  obtain ⟨C, hC⟩ := hb
  exact OneLoop_integrable_of_cont_bdd d L W v hf hC

/-- `tr(X G K) F` is integrable (a finite sum of integrable `ω_c tr(B_c G K) F`). -/
theorem GUETwistBA_integrable_trX (v : CoordF d L W → ℝ≥0) {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (K : Matrix (Vtx d L W) (Vtx d L W) ℂ) {F : Ω d L W → ℂ} (hFc : Continuous F)
    (hFb : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C) :
    Integrable (fun ω : Ω d L W => Matrix.trace (blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω)
      (GaussianProduct.law v) := by
  classical
  obtain ⟨CF, hCF⟩ := hFb
  have hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true := ExpAvgGen_G_cont hH 1 hz
  have hexp : ∀ ω : Ω d L W, Matrix.trace (blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) =
      ∑ c : CoordF d L W, ω c • Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) := by
    intro ω
    simpa only [Matrix.one_mul] using ExpAvgGen_trace_expand 1 K (Gres (H₀b + HflowBlock d L W 1 ω) z true) ω
  have hsm : ∀ ω : Ω d L W, (∑ c : CoordF d L W, ω c • Matrix.trace (coordinateBlock d L W c *
        Gres (H₀b + HflowBlock d L W 1 ω) z true * K)) * F ω =
      ∑ c : CoordF d L W, ω c • (Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω) := by
    intro ω
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_mul_assoc]
  simp_rw [hexp, hsm]
  refine integrable_finsetSum _ fun c _ => ?_
  obtain ⟨C1, hC1⟩ : ∃ C : ℝ, ∀ ω : Ω d L W, ‖Matrix.trace (coordinateBlock d L W c *
      Gres (H₀b + HflowBlock d L W 1 ω) z true * K)‖ ≤ C :=
    GUETwistBA_bdd_comp hH hz (fun G => Matrix.trace (coordinateBlock d L W c * G * K)) (by fun_prop)
  have hf1 : Continuous fun ω : Ω d L W => Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) := by
    fun_prop
  refine OneLoop_integrable_coord_smul d L W v c _ ((hf1.mul hFc).measurable) (C := C1 * CF) fun ω => ?_
  rw [norm_mul]
  exact mul_le_mul (hC1 ω) (hCF ω) (norm_nonneg _) ((norm_nonneg _).trans (hC1 ω))

/-- **The Stein identity with a test function** (twin of `GUEOneLoop_stein_trace`, with the extra factor `F`): for a
continuous bounded `F` with the coordinate derivatives `F'_c`,
`𝔼[tr(X G K) F] = -W^d Σ_{p,s} Ŝ_{ps} 𝔼[tr(G K E_p) tr(G E_s) F] + Σ_c v_c 𝔼[tr(B_c G K) F'_c]`. -/
theorem GUETwistBA_stein_F {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (K : Matrix (Vtx d L W) (Vtx d L W) ℂ) (F : Ω d L W → ℂ) (F' : CoordF d L W → Ω d L W → ℂ)
    (hFc : Continuous F) (hF'c : ∀ c, Continuous (F' c))
    (hFd : ∀ (ω : Ω d L W) (c : CoordF d L W), HasDerivAt (fun t : ℝ => F (Function.update ω c t)) (F' c ω) (ω c))
    (hFb : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C) (hF'b : ∃ C : ℝ, ∀ c ω, ‖F' c ω‖ ≤ C) :
    ∫ ω : Ω d L W, Matrix.trace (blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω
        ∂(GaussianProduct.law v) =
      -(((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) * ∫ ω : Ω d L W,
          Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
            Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω ∂(GaussianProduct.law v)) +
      ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * ∫ ω : Ω d L W,
        Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω ∂(GaussianProduct.law v) := by
  classical
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CF', hCF'⟩ := hF'b
  have hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true := ExpAvgGen_G_cont hH 1 hz
  -- the integrands `tr(B_c G K) F` and its derivative
  have hf1 : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) :=
    fun c => by fun_prop
  have hf2 : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      Matrix.trace (coordinateBlock d L W c * (-(Gres (H₀b + HflowBlock d L W 1 ω) z true * coordinateBlock d L W c *
        Gres (H₀b + HflowBlock d L W 1 ω) z true)) * K) :=
    fun c => (GUETwistBA_cont_GBG (coordinateBlock d L W c) K).comp hGc
  have hb1 : ∀ c : CoordF d L W, ∃ C : ℝ, ∀ ω : Ω d L W,
      ‖Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K)‖ ≤ C :=
    fun c => GUETwistBA_bdd_comp hH hz (fun G => Matrix.trace (coordinateBlock d L W c * G * K)) (by fun_prop)
  have hb2 : ∀ c : CoordF d L W, ∃ C : ℝ, ∀ ω : Ω d L W,
      ‖Matrix.trace (coordinateBlock d L W c * (-(Gres (H₀b + HflowBlock d L W 1 ω) z true * coordinateBlock d L W c *
        Gres (H₀b + HflowBlock d L W 1 ω) z true)) * K)‖ ≤ C :=
    fun c => GUETwistBA_bdd_comp hH hz (fun G => Matrix.trace (coordinateBlock d L W c * (-(G * coordinateBlock d L W c * G)) * K))
      (GUETwistBA_cont_GBG _ _)
  have hmul_bdd : ∀ {f : Ω d L W → ℂ} {g : Ω d L W → ℂ}, (∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C) → (∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C) →
      ∃ C : ℝ, ∀ ω, ‖f ω * g ω‖ ≤ C := by
    rintro f g ⟨C1, h1⟩ ⟨C2, h2⟩
    exact ⟨C1 * C2, fun ω => by rw [norm_mul]; exact mul_le_mul (h1 ω) (h2 ω) (norm_nonneg _) ((norm_nonneg _).trans (h1 ω))⟩
  have hadd_bdd : ∀ {f : Ω d L W → ℂ} {g : Ω d L W → ℂ}, (∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C) → (∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C) →
      ∃ C : ℝ, ∀ ω, ‖f ω + g ω‖ ≤ C := by
    rintro f g ⟨C1, h1⟩ ⟨C2, h2⟩
    exact ⟨C1 + C2, fun ω => (norm_add_le _ _).trans (add_le_add (h1 ω) (h2 ω))⟩
  have hFcb : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C := ⟨CF, hCF⟩
  have hF'cb : ∀ c, ∃ C : ℝ, ∀ ω, ‖F' c ω‖ ≤ C := fun c => ⟨CF', hCF' c⟩
  -- one coordinate
  have hcoord : ∀ c : CoordF d L W, ∫ ω : Ω d L W, ω c • (Matrix.trace (coordinateBlock d L W c *
        Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω) ∂(GaussianProduct.law v) =
      ((v c : ℝ) : ℂ) * ∫ ω : Ω d L W, (Matrix.trace (coordinateBlock d L W c * (-(Gres (H₀b + HflowBlock d L W 1 ω) z true *
        coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true)) * K) * F ω +
        Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω) ∂(GaussianProduct.law v) := by
    intro c
    have hst := GaussianProduct.stein v c
      (fun ω : Ω d L W => Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω)
      (fun ω : Ω d L W => Matrix.trace (coordinateBlock d L W c * (-(Gres (H₀b + HflowBlock d L W 1 ω) z true *
        coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true)) * K) * F ω +
        Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω)
      ((hf1 c).mul hFc) (((hf2 c).mul hFc).add ((hf1 c).mul (hF'c c)))
      (fun ω => ?_) (hmul_bdd (hb1 c) hFcb) (hadd_bdd (hmul_bdd (hb2 c) hFcb) (hmul_bdd (hb1 c) (hF'cb c)))
    · simpa only [Complex.real_smul] using hst
    · set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
        LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
      have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
      have h1 := ((hasDerivAt_const (ω c) (coordinateBlock d L W c)).mul (GUETwistBA_hasDerivAt_G hH hz ω c)).mul_const K
      have h2 := T.hasFDerivAt.comp_hasDerivAt (ω c) h1
      have h3 := (h2.mul (hFd ω c))
      refine h3.congr_deriv ?_
      simp only [hT, Function.comp_apply, Pi.mul_apply, zero_mul, zero_add, Function.update_eq_self]
  -- the expansion `tr(X G K) = Σ_c ω_c tr(B_c G K)`
  have hexp : ∀ ω : Ω d L W, Matrix.trace (blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) =
      ∑ c : CoordF d L W, ω c • Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) := by
    intro ω
    simpa only [Matrix.one_mul] using ExpAvgGen_trace_expand 1 K (Gres (H₀b + HflowBlock d L W 1 ω) z true) ω
  have hsm : ∀ ω : Ω d L W, (∑ c : CoordF d L W, ω c • Matrix.trace (coordinateBlock d L W c *
        Gres (H₀b + HflowBlock d L W 1 ω) z true * K)) * F ω =
      ∑ c : CoordF d L W, ω c • (Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω) := by
    intro ω
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_mul_assoc]
  have hI1 : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => ω c • (Matrix.trace (coordinateBlock d L W c *
      Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω)) (GaussianProduct.law v) := by
    intro c
    obtain ⟨C1, hC1⟩ := hb1 c
    refine OneLoop_integrable_coord_smul d L W v c _ (((hf1 c).mul hFc).measurable) (C := C1 * CF) fun ω => ?_
    rw [norm_mul]
    exact mul_le_mul (hC1 ω) (hCF ω) (norm_nonneg _) ((norm_nonneg _).trans (hC1 ω))
  have hIA : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => Matrix.trace (coordinateBlock d L W c *
      (-(Gres (H₀b + HflowBlock d L W 1 ω) z true * coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true)) * K) * F ω)
      (GaussianProduct.law v) :=
    fun c => GUETwistBA_integrable_of_cont_bdd v ((hf2 c).mul hFc) (hmul_bdd (hb2 c) hFcb)
  have hIB : ∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => Matrix.trace (coordinateBlock d L W c *
      Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω) (GaussianProduct.law v) :=
    fun c => GUETwistBA_integrable_of_cont_bdd v ((hf1 c).mul (hF'c c)) (hmul_bdd (hb1 c) (hF'cb c))
  simp_rw [hexp, hsm]
  rw [integral_finsetSum _ (fun c _ => hI1 c)]
  simp_rw [hcoord]
  simp only [integral_add (hIA _) (hIB _), mul_add, Finset.sum_add_distrib]
  congr 1
  have hcontr : ∀ ω : Ω d L W, ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * Matrix.trace (coordinateBlock d L W c *
        (-(Gres (H₀b + HflowBlock d L W 1 ω) z true * coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true)) * K) =
      -(((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) *
        (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
          Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s))) := by
    intro ω
    simpa only [Matrix.one_mul, Matrix.mul_one] using GUEOneLoop_contract 0 hσ v hv (Gres (H₀b + HflowBlock d L W 1 ω) z true) 1 K
  have hIC : ∀ p s : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * (K * Eblk d L W p)) *
      (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω)) (GaussianProduct.law v) := by
    intro p s
    have hc : Continuous fun G : Matrix (Vtx d L W) (Vtx d L W) ℂ =>
        Matrix.trace (G * (K * Eblk d L W p)) * Matrix.trace (G * Eblk d L W s) :=
      ((continuous_matrixTrace d L W).comp (continuous_id.mul continuous_const)).mul
        ((continuous_matrixTrace d L W).comp (continuous_id.mul continuous_const))
    have h : Integrable (fun ω : Ω d L W => (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * (K * Eblk d L W p)) *
        Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s)) * F ω) (GaussianProduct.law v) :=
      GUETwistBA_integrable_of_cont_bdd v ((hc.comp hGc).mul hFc) (hmul_bdd (GUETwistBA_bdd_comp hH hz _ hc) hFcb)
    simpa only [mul_assoc] using h
  have e1 : ∑ x : CoordF d L W, ((v x : ℝ) : ℂ) * ∫ a : Ω d L W, Matrix.trace (coordinateBlock d L W x *
        -(Gres (H₀b + HflowBlock d L W 1 a) z true * coordinateBlock d L W x * Gres (H₀b + HflowBlock d L W 1 a) z true) * K) * F a
          ∂(GaussianProduct.law v) =
      ∫ a : Ω d L W, (∑ x : CoordF d L W, ((v x : ℝ) : ℂ) * Matrix.trace (coordinateBlock d L W x *
        -(Gres (H₀b + HflowBlock d L W 1 a) z true * coordinateBlock d L W x * Gres (H₀b + HflowBlock d L W 1 a) z true) * K)) * F a
          ∂(GaussianProduct.law v) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun c _ => (hIA c).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Finset.sum_mul, mul_assoc]
  rw [e1]
  simp_rw [hcontr, neg_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [integral_neg, integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun s _ => ((hIC p s).const_mul _).const_mul _))]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ (fun s _ => ((hIC p s).const_mul _).const_mul _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul, integral_const_mul]



theorem GUETwistBA_integrable_trGK_trGE (v : CoordF d L W → ℝ≥0) {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (K : Matrix (Vtx d L W) (Vtx d L W) ℂ) {F : Ω d L W → ℂ} (hFc : Continuous F)
    (hFb : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C) (p s : Zd d L) :
    Integrable (fun ω : Ω d L W => Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
      Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω) (GaussianProduct.law v) := by
  have hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true := ExpAvgGen_G_cont hH 1 hz
  have hc : Continuous fun G : Matrix (Vtx d L W) (Vtx d L W) ℂ =>
      Matrix.trace (G * K * Eblk d L W p) * Matrix.trace (G * Eblk d L W s) :=
    ((continuous_matrixTrace d L W).comp ((continuous_id.mul continuous_const).mul continuous_const)).mul
      ((continuous_matrixTrace d L W).comp (continuous_id.mul continuous_const))
  obtain ⟨C1, hC1⟩ := GUETwistBA_bdd_comp hH hz _ hc
  obtain ⟨CF, hCF⟩ := hFb
  exact GUETwistBA_integrable_of_cont_bdd v ((hc.comp hGc).mul hFc)
    ⟨C1 * CF, fun ω => by
      rw [norm_mul]; exact mul_le_mul (hC1 ω) (hCF ω) (norm_nonneg _) ((norm_nonneg _).trans (hC1 ω))⟩

theorem GUETwistBA_integrable_trBGK (v : CoordF d L W → ℝ≥0) {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (K : Matrix (Vtx d L W) (Vtx d L W) ℂ) {F : Ω d L W → ℂ} (hFc : Continuous F)
    (hFb : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C) (c : CoordF d L W) :
    Integrable (fun ω : Ω d L W => Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω)
      (GaussianProduct.law v) := by
  have hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true := ExpAvgGen_G_cont hH 1 hz
  have hc : Continuous fun G : Matrix (Vtx d L W) (Vtx d L W) ℂ => Matrix.trace (coordinateBlock d L W c * G * K) := by fun_prop
  obtain ⟨C1, hC1⟩ := GUETwistBA_bdd_comp hH hz _ hc
  obtain ⟨CF, hCF⟩ := hFb
  exact GUETwistBA_integrable_of_cont_bdd v ((hc.comp hGc).mul hFc)
    ⟨C1 * CF, fun ω => by
      rw [norm_mul]; exact mul_le_mul (hC1 ω) (hCF ω) (norm_nonneg _) ((norm_nonneg _).trans (hC1 ω))⟩

/-- The integrand of the Stein defect is integrable. -/
theorem GUETwistBA_integrable_defect {t1 σ : ℝ} (v : CoordF d L W → ℝ≥0)
    {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (K : Matrix (Vtx d L W) (Vtx d L W) ℂ) (F : Ω d L W → ℂ) (F' : CoordF d L W → Ω d L W → ℂ)
    (hFc : Continuous F) (hF'c : ∀ c, Continuous (F' c)) (hFb : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C)
    (hF'b : ∃ C : ℝ, ∀ c ω, ‖F' c ω‖ ≤ C) :
    Integrable (fun ω : Ω d L W => Matrix.trace (blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω +
        ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) *
          (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
            Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω) -
        ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * (Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) *
          F' c ω)) (GaussianProduct.law v) := by
  have hA := GUETwistBA_integrable_trX v hH hz K hFc hFb
  have hB : Integrable (fun ω : Ω d L W => ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) *
      (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
        Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω)) (GaussianProduct.law v) :=
    (integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun s _ =>
      (GUETwistBA_integrable_trGK_trGE v hH hz K hFc hFb p s).const_mul _).const_mul _
  have hC : Integrable (fun ω : Ω d L W => ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * (Matrix.trace (coordinateBlock d L W c *
      Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω)) (GaussianProduct.law v) := by
    obtain ⟨CF', hCF'⟩ := hF'b
    exact integrable_finsetSum _ fun c _ =>
      (GUETwistBA_integrable_trBGK v hH hz K (hF'c c) ⟨CF', hCF' c⟩ c).const_mul _
  exact (hA.add hB).sub hC

/-- **The Stein defect vanishes**: `𝔼[tr(X G K) F + W^d Σ_{p,s} Ŝ_{ps} tr(G K E_p) tr(G E_s) F - Σ_c v_c tr(B_c G K) F'_c] = 0`. -/
theorem GUETwistBA_stein_defect {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (K : Matrix (Vtx d L W) (Vtx d L W) ℂ) (F : Ω d L W → ℂ) (F' : CoordF d L W → Ω d L W → ℂ)
    (hFc : Continuous F) (hF'c : ∀ c, Continuous (F' c))
    (hFd : ∀ (ω : Ω d L W) (c : CoordF d L W), HasDerivAt (fun t : ℝ => F (Function.update ω c t)) (F' c ω) (ω c))
    (hFb : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C) (hF'b : ∃ C : ℝ, ∀ c ω, ‖F' c ω‖ ≤ C) :
    ∫ ω : Ω d L W, (Matrix.trace (blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F ω +
        ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) *
          (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
            Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω) -
        ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * (Matrix.trace (coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * K) *
          F' c ω)) ∂(GaussianProduct.law v) = 0 := by
  classical
  have hst := GUETwistBA_stein_F hσ v hv hH hz K F F' hFc hF'c hFd hFb hF'b
  have hA := GUETwistBA_integrable_trX v hH hz K hFc hFb
  have hB : Integrable (fun ω : Ω d L W => ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) *
      (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
        Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω)) (GaussianProduct.law v) :=
    (integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun s _ =>
      (GUETwistBA_integrable_trGK_trGE v hH hz K hFc hFb p s).const_mul _).const_mul _
  have hC : Integrable (fun ω : Ω d L W => ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * (Matrix.trace (coordinateBlock d L W c *
      Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω)) (GaussianProduct.law v) := by
    obtain ⟨CF', hCF'⟩ := hF'b
    exact integrable_finsetSum _ fun c _ =>
      (GUETwistBA_integrable_trBGK v hH hz K (hF'c c) ⟨CF', hCF' c⟩ c).const_mul _
  have eB : ∫ ω : Ω d L W, ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) *
      (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
        Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω) ∂(GaussianProduct.law v) =
      ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) * ∫ ω : Ω d L W,
          Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * K * Eblk d L W p) *
            Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W s) * F ω ∂(GaussianProduct.law v) := by
    rw [integral_const_mul, integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun s _ =>
      (GUETwistBA_integrable_trGK_trGE v hH hz K hFc hFb p s).const_mul _)]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ (fun s _ => (GUETwistBA_integrable_trGK_trGE v hH hz K hFc hFb p s).const_mul _)]
    exact Finset.sum_congr rfl fun s _ => by rw [integral_const_mul]
  have eC : ∫ ω : Ω d L W, ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * (Matrix.trace (coordinateBlock d L W c *
      Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω) ∂(GaussianProduct.law v) =
      ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * ∫ ω : Ω d L W, Matrix.trace (coordinateBlock d L W c *
        Gres (H₀b + HflowBlock d L W 1 ω) z true * K) * F' c ω ∂(GaussianProduct.law v) := by
    obtain ⟨CF', hCF'⟩ := hF'b
    rw [integral_finsetSum _ (fun c _ => (GUETwistBA_integrable_trBGK v hH hz K (hF'c c) ⟨CF', hCF' c⟩ c).const_mul _)]
    exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul]
  have e1 := integral_sub (μ := GaussianProduct.law v) (hA.add hB) hC
  have e2 := integral_add (μ := GaussianProduct.law v) hA hB
  simp only [Pi.add_apply] at e1
  rw [e1, e2, eB, eC, hst]
  ring

end SteinF

section PhiAlg

/-- `Φ_p(x) = x^{p-1} conj(x)^p` (`T Φ_p = |T|^{2p}`), the test function of the `p`-th moment. -/
def GUETwistBA_Phi (p : ℕ) (x : ℂ) : ℂ := x ^ (p - 1) * star x ^ p

/-- The derivative of `Φ_p(f(t))` is `Φ'_p(f(t), f'(t))`. -/
def GUETwistBA_Phi' (p : ℕ) (x y : ℂ) : ℂ :=
  ((↑(p - 1) * x ^ (p - 1 - 1) * y) * star x ^ p + x ^ (p - 1) * (↑p * star x ^ (p - 1) * star y))

theorem GUETwistBA_Phi_cont (p : ℕ) : Continuous (GUETwistBA_Phi p) := by
  unfold GUETwistBA_Phi; fun_prop

theorem GUETwistBA_Phi'_cont (p : ℕ) : Continuous (fun xy : ℂ × ℂ => GUETwistBA_Phi' p xy.1 xy.2) := by
  unfold GUETwistBA_Phi'; fun_prop

theorem GUETwistBA_hasDerivAt_Phi (p : ℕ) {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => GUETwistBA_Phi p (f s)) (GUETwistBA_Phi' p (f t) f') t := by
  have h1 := hf.fun_pow (p - 1)
  have h2 := hf.star.fun_pow p
  exact h1.mul h2

/-- `T Φ_p(T) = |T|^{2p}` for `p ≥ 1`. -/
theorem GUETwistBA_mul_Phi {p : ℕ} (hp : 1 ≤ p) (x : ℂ) :
    x * GUETwistBA_Phi p x = (((‖x‖ ^ (2 * p) : ℝ)) : ℂ) := by
  unfold GUETwistBA_Phi
  have h1 : x * (x ^ (p - 1) * star x ^ p) = (x * star x) ^ p := by
    have : x * x ^ (p - 1) = x ^ p := by rw [← pow_succ']; congr 1; omega
    calc x * (x ^ (p - 1) * star x ^ p) = (x * x ^ (p - 1)) * star x ^ p := by ring
      _ = x ^ p * star x ^ p := by rw [this]
      _ = (x * star x) ^ p := (mul_pow _ _ _).symm
  rw [h1, Complex.star_def, Complex.mul_conj']
  push_cast
  ring

end PhiAlg

section Defs

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The centred twisted block trace of a matrix `G`: `W^{-d} tr(G Π_{qa}) - M^{(B)}_{qa}` (`G = G(ω)` below). -/
def GUETwistBA_Tm (d L W : ℕ) [NeZero L] [NeZero W] (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  ((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gm * GUETwistBA_Pi d L W q a) - Mbl q a

/-- `D_{p'} = Σ_s Ŝ_{p's} (g_s - m)`, `g_s = tr(G E_s)`, `Ŝ = t₁ S^{(B)}(0) + σ` (the diagonal 1-loops against `m`). -/
def GUETwistBA_Dm (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (m : ℂ) (p' : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) * (Matrix.trace (Gm * Eblk d L W s) - m)

/-- The derivative term `R₁ = W^{-2d} Σ_{p'} M_{qp'} Σ_s Ŝ_{p's} tr(Π_{p'a} G Π_{qa} · G E_s G)` (`𝒮₁` of T.7, grid profile). -/
def GUETwistBA_R1m (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ p' : Zd d L, Mbl q p' * ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
    Matrix.trace (GUETwistBA_Pi d L W p' a * Gm * GUETwistBA_Pi d L W q a * (Gm * Eblk d L W s * Gm))

/-- The derivative term `R₂ = W^{-2d} Σ_{p'} M_{qp'} Σ_s Ŝ_{p's} tr(Π_{p'a} G^* Π_{qa}^* · G^* E_s G)` (`𝒮₂` of T.7). -/
def GUETwistBA_R2m (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ p' : Zd d L, Mbl q p' * ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
    Matrix.trace (GUETwistBA_Pi d L W p' a * Gmᴴ * (GUETwistBA_Pi d L W q a)ᴴ * (Gmᴴ * Eblk d L W s * Gm))

/-- The three groups of the `p`-th moment identity (`Σ_{p'} M_{qp'} D_{p'} (M_{p'a} + T_{p'a}) Φ`, `R₁ T^{p-2} T̄^p`, `R₂ |T|^{2p-2}`). -/
def GUETwistBA_g1 (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (m : ℂ) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ) (q a : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  ∑ p' : Zd d L, Mbl q p' * (GUETwistBA_Dm d L W t1 σ m p' Gm * (Mbl p' a + GUETwistBA_Tm d L W Mbl p' a Gm) *
    GUETwistBA_Phi p (GUETwistBA_Tm d L W Mbl q a Gm))

def GUETwistBA_g2 (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ) (q a : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  GUETwistBA_R1m d L W t1 σ Mbl q a Gm * (GUETwistBA_Tm d L W Mbl q a Gm ^ (p - 2) * star (GUETwistBA_Tm d L W Mbl q a Gm) ^ p)

def GUETwistBA_g3 (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ) (q a : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  GUETwistBA_R2m d L W t1 σ Mbl q a Gm * (((‖GUETwistBA_Tm d L W Mbl q a Gm‖ ^ (2 * p - 2) : ℝ)) : ℂ)

theorem GUETwistBA_hrow (hL : 3 ≤ L) {t1 σ u : ℝ} (hu : t1 + (L : ℝ) ^ d * σ = u) (p' : Zd d L) :
    ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_SB_row d L 0 hL p', Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    OneLoop_card_Zd d L, ← hu]
  push_cast
  ring

theorem GUETwistBA_Tm_cont (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L) : Continuous (GUETwistBA_Tm d L W Mbl q a) := by
  unfold GUETwistBA_Tm
  exact (continuous_const.mul ((continuous_matrixTrace d L W).comp (continuous_id.mul continuous_const))).sub continuous_const

theorem GUETwistBA_Dm_cont (t1 σ : ℝ) (m : ℂ) (p' : Zd d L) : Continuous (GUETwistBA_Dm d L W t1 σ m p') := by
  unfold GUETwistBA_Dm
  exact continuous_finsetSum _ fun s _ => continuous_const.mul
    (((continuous_matrixTrace d L W).comp (continuous_id.mul continuous_const)).sub continuous_const)

theorem GUETwistBA_R1m_cont (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L) : Continuous (GUETwistBA_R1m d L W t1 σ Mbl q a) := by
  unfold GUETwistBA_R1m
  refine continuous_const.mul (continuous_finsetSum _ fun p' _ => continuous_const.mul (continuous_finsetSum _ fun s _ =>
    continuous_const.mul ((continuous_matrixTrace d L W).comp ?_)))
  exact ((continuous_const.mul continuous_id).mul continuous_const).mul ((continuous_id.mul continuous_const).mul continuous_id)

theorem GUETwistBA_R2m_cont (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L) : Continuous (GUETwistBA_R2m d L W t1 σ Mbl q a) := by
  unfold GUETwistBA_R2m
  refine continuous_const.mul (continuous_finsetSum _ fun p' _ => continuous_const.mul (continuous_finsetSum _ fun s _ =>
    continuous_const.mul ((continuous_matrixTrace d L W).comp ?_)))
  have hct : Continuous fun G : Matrix (Vtx d L W) (Vtx d L W) ℂ => Gᴴ := continuous_id.matrix_conjTranspose
  exact ((continuous_const.mul hct).mul continuous_const).mul ((hct.mul continuous_const).mul continuous_id)

theorem GUETwistBA_g1_cont (t1 σ : ℝ) (m : ℂ) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ) (q a : Zd d L) :
    Continuous (GUETwistBA_g1 d L W t1 σ m Mbl p q a) := by
  unfold GUETwistBA_g1
  refine continuous_finsetSum _ fun p' _ => continuous_const.mul (((GUETwistBA_Dm_cont t1 σ m p').mul
    (continuous_const.add (GUETwistBA_Tm_cont Mbl p' a))).mul ((GUETwistBA_Phi_cont p).comp (GUETwistBA_Tm_cont Mbl q a)))

theorem GUETwistBA_g2_cont (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ) (q a : Zd d L) :
    Continuous (GUETwistBA_g2 d L W t1 σ Mbl p q a) := by
  unfold GUETwistBA_g2
  exact (GUETwistBA_R1m_cont t1 σ Mbl q a).mul (((GUETwistBA_Tm_cont Mbl q a).pow _).mul
    ((GUETwistBA_Tm_cont Mbl q a).star.pow _))

theorem GUETwistBA_g3_cont (t1 σ : ℝ) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ) (q a : Zd d L) :
    Continuous (GUETwistBA_g3 d L W t1 σ Mbl p q a) := by
  unfold GUETwistBA_g3
  exact (GUETwistBA_R2m_cont t1 σ Mbl q a).mul
    (Complex.continuous_ofReal.comp ((continuous_norm.comp (GUETwistBA_Tm_cont Mbl q a)).pow _))

end Defs

section TDef

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The centred twisted block trace `T_{qa}(ω) = W^{-d} tr(G Π_{qa}) - M^{(B)}_{qa}` (the fine-lattice form is the probe's `twTrBA`, `t/T2519` b992c2e7). -/
def GUETwistBA_T (d L W : ℕ) [NeZero L] [NeZero W] (H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L) (ω : Ω d L W) : ℂ :=
  GUETwistBA_Tm d L W Mbl q a (Gres (H₀b + HflowBlock d L W 1 ω) z true)

/-- `∂_c T_{qa} = -W^{-d} tr(G B_c G Π_{qa})` (of the matrix `G`). -/
def GUETwistBA_T'm (d L W : ℕ) [NeZero L] [NeZero W] (q a : Zd d L) (c : CoordF d L W)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  -(((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gm * coordinateBlock d L W c * Gm * GUETwistBA_Pi d L W q a))

def GUETwistBA_T' (d L W : ℕ) [NeZero L] [NeZero W] (H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (q a : Zd d L) (c : CoordF d L W) (ω : Ω d L W) : ℂ :=
  GUETwistBA_T'm d L W q a c (Gres (H₀b + HflowBlock d L W 1 ω) z true)

theorem GUETwistBA_hasDerivAt_T {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L) (ω : Ω d L W) (c : CoordF d L W) :
    HasDerivAt (fun t : ℝ => GUETwistBA_T d L W H₀b z Mbl q a (Function.update ω c t))
      (GUETwistBA_T' d L W H₀b z q a c ω) (ω c) := by
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h1 := (GUETwistBA_hasDerivAt_G hH hz ω c).mul_const (GUETwistBA_Pi d L W q a)
  have h2 := T.hasFDerivAt.comp_hasDerivAt (ω c) h1
  have h3 := (h2.const_mul (((W : ℂ) ^ d)⁻¹)).sub_const (Mbl q a)
  refine h3.congr_deriv ?_
  simp only [GUETwistBA_T', GUETwistBA_T'm, hT, Matrix.neg_mul, Matrix.trace_neg, mul_neg]


end TDef

section TEq

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem GUETwistBA_trace_Mb_mul {Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mbl : Zd d L → Zd d L → ℂ}
    (hMb : ∀ (b b' : Zd d L) (o o' : Fin (W ^ d)), Mb (b, o) (b', o') = if o = o' then Mbl b b' else 0)
    (Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) (q a : Zd d L) :
    Matrix.trace (Mb * Y * GUETwistBA_Pi d L W q a) = ∑ p' : Zd d L, Mbl q p' * Matrix.trace (Y * GUETwistBA_Pi d L W p' a) := by
  simp only [GUETwistBA_trace_Pi, Matrix.mul_apply, Fintype.sum_prod_type, hMb, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem GUETwistBA_trace_Mb_Pi {Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mbl : Zd d L → Zd d L → ℂ}
    (hMb : ∀ (b b' : Zd d L) (o o' : Fin (W ^ d)), Mb (b, o) (b', o') = if o = o' then Mbl b b' else 0) (q a : Zd d L) :
    Matrix.trace (Mb * GUETwistBA_Pi d L W q a) = ((W : ℂ) ^ d) * Mbl q a := by
  simp only [GUETwistBA_trace_Pi, hMb, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring


/-- **The pointwise resolvent identity for the twisted trace** (`G - M = -M(u m + X)G`, `M = M^{(B)} ⊗ 1`):
`T_{qa} = -W^{-d} Σ_{p'} M^{(B)}_{qp'} (u m tr(G Π_{p'a}) + tr(X G Π_{p'a}))`. -/
theorem GUETwistBA_T_eq {u : ℝ} {H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0)
    (hM : (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1)
    {Mbl : Zd d L → Zd d L → ℂ} (hMb : ∀ (b b' : Zd d L) (o o' : Fin (W ^ d)), Mb (b, o) (b', o') = if o = o' then Mbl b b' else 0)
    (q a : Zd d L) (ω : Ω d L W) :
    GUETwistBA_T d L W H₀b z Mbl q a ω =
      -(((W : ℂ) ^ d)⁻¹ * ∑ p' : Zd d L, Mbl q p' * (((u : ℂ) * m) * Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true *
        GUETwistBA_Pi d L W p' a) + Matrix.trace (blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true *
          GUETwistBA_Pi d L W p' a))) := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have hM1 : (H₀b - (z + ((1 : ℝ) : ℂ) * ((u : ℂ) * m)) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1 := by simpa using hM
  have h := ExpAvgGen_resolvent_id (Mb := Mb) hH hz hM1 ω
  simp only [Complex.ofReal_one, one_mul, Real.sqrt_one, one_smul] at h
  have h1 : Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * GUETwistBA_Pi d L W q a) =
      ((W : ℂ) ^ d) * Mbl q a - Matrix.trace (Mb * (((u : ℂ) * m) • (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true) * GUETwistBA_Pi d L W q a) := by
    conv_lhs => rw [h]
    rw [Matrix.sub_mul, Matrix.trace_sub, GUETwistBA_trace_Mb_Pi hMb]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_assoc]
  have h2 := GUETwistBA_trace_Mb_mul hMb (((u : ℂ) * m) • (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true) q a
  unfold GUETwistBA_T GUETwistBA_Tm
  rw [h1, h2]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  field_simp
  ring

end TEq

section DPhi

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem GUETwistBA_trace_cyc_B (B G K : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (B * G * K) = Matrix.trace (G * K * B) := by
  calc Matrix.trace (B * G * K) = Matrix.trace (B * (G * K)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((G * K) * B) := Matrix.trace_mul_comm _ _

theorem GUETwistBA_trace_cyc_GBG (B G K : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (G * B * G * K) = Matrix.trace (G * K * G * B) := by
  calc Matrix.trace (G * B * G * K) = Matrix.trace ((G * B) * (G * K)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((G * K) * (G * B)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (G * K * G * B) := by simp only [Matrix.mul_assoc]

/-- The coordinate sum of the derivative of `Φ_p(T)` against `tr(B_c G Π_{p'a})`: the two derivative terms `𝒞₁`, `𝒞₂`. -/
theorem GUETwistBA_dPhi_sum {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) (p : ℕ) (p' q a : Zd d L) (x : ℂ) :
    ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * (Matrix.trace (coordinateBlock d L W c * Gm * GUETwistBA_Pi d L W p' a) *
        GUETwistBA_Phi' p x (-(((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gm * coordinateBlock d L W c * Gm * GUETwistBA_Pi d L W q a)))) =
      -(((W : ℂ) ^ d)⁻¹) * ((↑(p - 1) * x ^ (p - 1 - 1) * star x ^ p) * ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
          Matrix.trace (GUETwistBA_Pi d L W p' a * Gm * GUETwistBA_Pi d L W q a * (Gm * Eblk d L W s * Gm)) +
        (x ^ (p - 1) * (↑p * star x ^ (p - 1))) * ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
          Matrix.trace (GUETwistBA_Pi d L W p' a * Gmᴴ * (GUETwistBA_Pi d L W q a)ᴴ * (Gmᴴ * Eblk d L W s * Gm))) := by
  have hWr : star (((W : ℂ) ^ d)⁻¹) = ((W : ℂ) ^ d)⁻¹ := by simp
  have e1 : ∀ c : CoordF d L W, Matrix.trace (coordinateBlock d L W c * Gm * GUETwistBA_Pi d L W p' a) =
      Matrix.trace (Gm * GUETwistBA_Pi d L W p' a * coordinateBlock d L W c) := fun c => GUETwistBA_trace_cyc_B _ _ _
  have e2 : ∀ c : CoordF d L W, Matrix.trace (Gm * coordinateBlock d L W c * Gm * GUETwistBA_Pi d L W q a) =
      Matrix.trace (Gm * GUETwistBA_Pi d L W q a * Gm * coordinateBlock d L W c) := fun c => GUETwistBA_trace_cyc_GBG _ _ _
  simp only [e1, e2]
  rw [← GUETwistBA_C1_eq hσ v hv Gm p' q a, ← GUETwistBA_C2_eq hσ v hv Gm p' q a]
  simp only [GUETwistBA_Phi', star_neg, star_mul', hWr, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring


theorem GUETwistBA_trace_Pi_Eblk (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) (p' a p : Zd d L) :
    Matrix.trace (Gm * GUETwistBA_Pi d L W p' a * Eblk d L W p) =
      if p = p' then ((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gm * GUETwistBA_Pi d L W p' a) else 0 := by
  rw [Matrix.mul_assoc, GUETwistBA_Pi_mul_Eblk_ne]
  by_cases hp : p = p'
  · simp [hp, Matrix.trace_smul]
  · simp [hp]

/-- The collapse of the block sum of the Stein term: `W^d Σ_{p,s} Ŝ_{ps} tr(G Π_{p'a} E_p) tr(G E_s) F = tr(G Π_{p'a}) (Σ_s Ŝ_{p's} tr(G E_s)) F`. -/
theorem GUETwistBA_collapse_B (t1 σ : ℝ) (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) (p' a : Zd d L) (F : ℂ) :
    ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) *
        (Matrix.trace (Gm * GUETwistBA_Pi d L W p' a * Eblk d L W p) * Matrix.trace (Gm * Eblk d L W s) * F) =
      Matrix.trace (Gm * GUETwistBA_Pi d L W p' a) * (∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
        Matrix.trace (Gm * Eblk d L W s)) * F := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  simp only [GUETwistBA_trace_Pi_Eblk]
  rw [Finset.sum_eq_single p' (fun p _ hp => by simp [hp]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [ite_true, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

end DPhi

section Moment

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem GUETwistBA_pow_star (x : ℂ) (k : ℕ) : x ^ k * star x ^ k = (((‖x‖ ^ (2 * k) : ℝ)) : ℂ) := by
  rw [← mul_pow, Complex.star_def, Complex.mul_conj']
  push_cast
  ring

theorem GUETwistBA_unif_bdd {ι : Type*} [Finite ι] {Ω' : Type*} {f : ι → Ω' → ℂ} (h : ∀ i, ∃ C : ℝ, ∀ ω, ‖f i ω‖ ≤ C) :
    ∃ C : ℝ, ∀ i ω, ‖f i ω‖ ≤ C := by
  have := Fintype.ofFinite ι
  choose C hC using h
  exact ⟨∑ i, |C i|, fun i ω => (hC i ω).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))⟩

theorem GUETwistBA_T'_cont {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hH : H₀b.IsHermitian) (hz : z.im ≠ 0)
    (q a : Zd d L) (c : CoordF d L W) :
    Continuous fun ω : Ω d L W => GUETwistBA_T' d L W H₀b z q a c ω := by
  have hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true := ExpAvgGen_G_cont hH 1 hz
  have h : Continuous fun G : Matrix (Vtx d L W) (Vtx d L W) ℂ =>
      -(((W : ℂ) ^ d)⁻¹ * Matrix.trace (G * coordinateBlock d L W c * G * GUETwistBA_Pi d L W q a)) :=
    (continuous_const.mul ((continuous_matrixTrace d L W).comp
      (((continuous_id.mul continuous_const).mul continuous_id).mul continuous_const))).neg
  exact h.comp hGc


/-- The Stein defect integrand at `K = Π_{p'a}`, `F = Φ_p(T_{qa})`, `F'_c = Φ'_p(T_{qa}, ∂_c T_{qa})`, as a function of the matrices
`X` and `G`. -/
def GUETwistBA_Zm (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (v : CoordF d L W → ℝ≥0) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ)
    (q a p' : Zd d L) (Xm Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  Matrix.trace (Xm * Gm * GUETwistBA_Pi d L W p' a) * GUETwistBA_Phi p (GUETwistBA_Tm d L W Mbl q a Gm) +
    ((W : ℂ) ^ d) * ∑ p'' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p'' s + (σ : ℂ)) *
      (Matrix.trace (Gm * GUETwistBA_Pi d L W p' a * Eblk d L W p'') * Matrix.trace (Gm * Eblk d L W s) *
        GUETwistBA_Phi p (GUETwistBA_Tm d L W Mbl q a Gm)) -
    ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * (Matrix.trace (coordinateBlock d L W c * Gm * GUETwistBA_Pi d L W p' a) *
      GUETwistBA_Phi' p (GUETwistBA_Tm d L W Mbl q a Gm) (GUETwistBA_T'm d L W q a c Gm))

def GUETwistBA_Z (d L W : ℕ) [NeZero L] [NeZero W] (t1 σ : ℝ) (v : CoordF d L W → ℝ≥0) (H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (z : ℂ) (Mbl : Zd d L → Zd d L → ℂ) (p : ℕ) (q a p' : Zd d L) (ω : Ω d L W) : ℂ :=
  GUETwistBA_Zm d L W t1 σ v Mbl p q a p' (blockMat d L W (Xmat d L W ω)) (Gres (H₀b + HflowBlock d L W 1 ω) z true)

/-- The pure algebra of the moment identity, for one `p'` (`c = u m`, `D = D̃ - c`, `M + T = W^{-d} tr(G Π)`). -/
theorem GUETwistBA_alg {Wd Mb c A Xp Φ Dt Dm MT C1 C2 a1 bb pp : ℂ} (hDm : Dm = Dt - c) (hMT : MT = Wd * A) :
    -(Wd * Mb * (c * A + Xp) * Φ) =
      Mb * (Dm * MT * Φ) + (pp - 1) * Wd ^ 2 * Mb * C1 * a1 + pp * Wd ^ 2 * Mb * C2 * bb +
        (-Wd) * Mb * (Xp * Φ + A * Dt * Φ + Wd * ((pp - 1) * a1 * C1 + pp * bb * C2)) := by
  subst hDm hMT
  ring

/-- **The pointwise form of the moment identity** (matrix level): if `T_{qa}(G) = -W^{-d} Σ_{p'} M_{qp'} (u m tr(G Π_{p'a}) + tr(X G Π_{p'a}))`
(the resolvent identity) and `Σ_s Ŝ_{p's} = u`, then `|T|^{2p} = g₁ + (p-1) g₂ + p g₃ - W^{-d} Σ_{p'} M_{qp'} Z_{p'}`. -/
theorem GUETwistBA_pointwise {t1 c0 σ u : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (hrow : ∀ p' : Zd d L,
      ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ))
    (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {m : ℂ} {Mbl : Zd d L → Zd d L → ℂ} (p : ℕ) (hp : 1 ≤ p) (q a : Zd d L) (Xm Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (hx : GUETwistBA_Tm d L W Mbl q a Gm = -(((W : ℂ) ^ d)⁻¹ * ∑ p' : Zd d L, Mbl q p' * (((u : ℂ) * m) *
      Matrix.trace (Gm * GUETwistBA_Pi d L W p' a) + Matrix.trace (Xm * Gm * GUETwistBA_Pi d L W p' a)))) :
    ((‖GUETwistBA_Tm d L W Mbl q a Gm‖ ^ (2 * p) : ℝ) : ℂ) =
      (GUETwistBA_g1 d L W t1 σ m Mbl p q a Gm + ((p : ℂ) - 1) * GUETwistBA_g2 d L W t1 σ Mbl p q a Gm +
        (p : ℂ) * GUETwistBA_g3 d L W t1 σ Mbl p q a Gm) +
      (-(((W : ℂ) ^ d)⁻¹)) * ∑ p' : Zd d L, Mbl q p' * GUETwistBA_Zm d L W t1 σ v Mbl p q a p' Xm Gm := by
  classical
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have hαβ1 : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by rw [Nat.cast_sub hp]; simp
  have hp2 : p - 1 - 1 = p - 2 := by omega
  have hp3 : 2 * (p - 1) = 2 * p - 2 := by omega
  set x := GUETwistBA_Tm d L W Mbl q a Gm with hxd
  have hbb : x ^ (p - 1) * (↑p * star x ^ (p - 1)) = (p : ℂ) * (((‖x‖ ^ (2 * p - 2) : ℝ)) : ℂ) := by
    rw [← hp3, ← GUETwistBA_pow_star]; ring
  have hZ : ∀ p' : Zd d L, GUETwistBA_Zm d L W t1 σ v Mbl p q a p' Xm Gm =
      Matrix.trace (Xm * Gm * GUETwistBA_Pi d L W p' a) * GUETwistBA_Phi p x +
      Matrix.trace (Gm * GUETwistBA_Pi d L W p' a) * (∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
        Matrix.trace (Gm * Eblk d L W s)) * GUETwistBA_Phi p x +
      ((W : ℂ) ^ d)⁻¹ * (((p : ℂ) - 1) * (x ^ (p - 2) * star x ^ p) * (∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
          Matrix.trace (GUETwistBA_Pi d L W p' a * Gm * GUETwistBA_Pi d L W q a * (Gm * Eblk d L W s * Gm))) +
        (p : ℂ) * (((‖x‖ ^ (2 * p - 2) : ℝ)) : ℂ) * (∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
          Matrix.trace (GUETwistBA_Pi d L W p' a * Gmᴴ * (GUETwistBA_Pi d L W q a)ᴴ * (Gmᴴ * Eblk d L W s * Gm)))) := by
    intro p'
    unfold GUETwistBA_Zm
    rw [← hxd, GUETwistBA_collapse_B t1 σ Gm p' a (GUETwistBA_Phi p x)]
    have h := GUETwistBA_dPhi_sum hσ v hv Gm p p' q a x
    simp only [GUETwistBA_T'm]
    rw [h, hαβ1, hp2, hbb]
    ring
  have hDm : ∀ p' : Zd d L, GUETwistBA_Dm d L W t1 σ m p' Gm = (∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
      Matrix.trace (Gm * Eblk d L W s)) - (u : ℂ) * m := by
    intro p'
    unfold GUETwistBA_Dm
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow p']
  have hMT : ∀ p' : Zd d L, Mbl p' a + GUETwistBA_Tm d L W Mbl p' a Gm = ((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gm * GUETwistBA_Pi d L W p' a) := by
    intro p'
    unfold GUETwistBA_Tm
    ring
  obtain ⟨Dt, hDt⟩ : ∃ f : Zd d L → ℂ, ∀ p', f p' = ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
      Matrix.trace (Gm * Eblk d L W s) := ⟨fun p' => _, fun _ => rfl⟩
  obtain ⟨C1f, hC1f⟩ : ∃ f : Zd d L → ℂ, ∀ p', f p' = ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
      Matrix.trace (GUETwistBA_Pi d L W p' a * Gm * GUETwistBA_Pi d L W q a * (Gm * Eblk d L W s * Gm)) := ⟨fun p' => _, fun _ => rfl⟩
  obtain ⟨C2f, hC2f⟩ : ∃ f : Zd d L → ℂ, ∀ p', f p' = ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) *
      Matrix.trace (GUETwistBA_Pi d L W p' a * Gmᴴ * (GUETwistBA_Pi d L W q a)ᴴ * (Gmᴴ * Eblk d L W s * Gm)) := ⟨fun p' => _, fun _ => rfl⟩
  simp only [← hDt, ← hC1f, ← hC2f] at hZ hDm
  rw [← GUETwistBA_mul_Phi hp x]
  have e1 : x * GUETwistBA_Phi p x = (-(((W : ℂ) ^ d)⁻¹ * ∑ p' : Zd d L, Mbl q p' * (((u : ℂ) * m) *
      Matrix.trace (Gm * GUETwistBA_Pi d L W p' a) + Matrix.trace (Xm * Gm * GUETwistBA_Pi d L W p' a)))) * GUETwistBA_Phi p x :=
    congrArg (fun y => y * GUETwistBA_Phi p x) hx
  rw [e1]
  simp only [GUETwistBA_g1, GUETwistBA_g2, GUETwistBA_g3, GUETwistBA_R1m, GUETwistBA_R2m, ← hxd, ← hC1f, ← hC2f]
  simp only [hZ, hDm, hMT, Finset.mul_sum, Finset.sum_mul, neg_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p' _ => ?_
  have := GUETwistBA_alg (Wd := ((W : ℂ) ^ d)⁻¹) (Mb := Mbl q p') (c := (u : ℂ) * m)
    (A := Matrix.trace (Gm * GUETwistBA_Pi d L W p' a)) (Xp := Matrix.trace (Xm * Gm * GUETwistBA_Pi d L W p' a))
    (Φ := GUETwistBA_Phi p x) (Dt := Dt p') (Dm := Dt p' - (u : ℂ) * m)
    (MT := ((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gm * GUETwistBA_Pi d L W p' a)) (C1 := C1f p') (C2 := C2f p')
    (a1 := x ^ (p - 2) * star x ^ p) (bb := (((‖x‖ ^ (2 * p - 2) : ℝ)) : ℂ)) (pp := (p : ℂ)) rfl rfl
  linear_combination this

/-- **The `p`-th moment identity of the twisted trace under the one-time grid law** (Steps 1-3 of Lemma T.7, grid form): for
`p ≥ 1` and `G = (H₀ + X - z)⁻¹`, `X ~ law v` (variances `v_c = t₁ gvar_c + c₀ w_c`),
`𝔼|T_{qa}|^{2p} = 𝔼[Σ_{p'} M_{qp'} D_{p'} (M_{p'a} + T_{p'a}) Φ_p(T_{qa}) + (p-1) R₁ T^{p-2} T̄^p + p R₂ |T|^{2p-2}]`. -/
theorem GUETwistBA_momentId {t1 c0 σ u : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (hu : t1 + (L : ℝ) ^ d * σ = u) (hL : 3 ≤ L)
    (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0)
    (hM : (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1)
    {Mbl : Zd d L → Zd d L → ℂ} (hMb : ∀ (b b' : Zd d L) (o o' : Fin (W ^ d)), Mb (b, o) (b', o') = if o = o' then Mbl b b' else 0)
    (p : ℕ) (hp : 1 ≤ p) (q a : Zd d L) :
    ∫ ω : Ω d L W, ((‖GUETwistBA_T d L W H₀b z Mbl q a ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(GaussianProduct.law v) =
      ∫ ω : Ω d L W, (GUETwistBA_g1 d L W t1 σ m Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        ((p : ℂ) - 1) * GUETwistBA_g2 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        (p : ℂ) * GUETwistBA_g3 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true)) ∂(GaussianProduct.law v) := by
  classical
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true := ExpAvgGen_G_cont hH 1 hz
  have hTc : Continuous fun ω : Ω d L W => GUETwistBA_T d L W H₀b z Mbl q a ω := (GUETwistBA_Tm_cont Mbl q a).comp hGc
  -- the test function and its derivatives
  have hFc : Continuous fun ω : Ω d L W => GUETwistBA_Phi p (GUETwistBA_T d L W H₀b z Mbl q a ω) := (GUETwistBA_Phi_cont p).comp hTc
  have hF'c : ∀ c : CoordF d L W, Continuous fun ω : Ω d L W =>
      GUETwistBA_Phi' p (GUETwistBA_T d L W H₀b z Mbl q a ω) (GUETwistBA_T' d L W H₀b z q a c ω) :=
    fun c => by
      have h := (GUETwistBA_Phi'_cont p).comp (hTc.prodMk (GUETwistBA_T'_cont hH hz q a c))
      exact h
  have hFd : ∀ (ω : Ω d L W) (c : CoordF d L W), HasDerivAt
      (fun t : ℝ => GUETwistBA_Phi p (GUETwistBA_T d L W H₀b z Mbl q a (Function.update ω c t)))
      (GUETwistBA_Phi' p (GUETwistBA_T d L W H₀b z Mbl q a ω) (GUETwistBA_T' d L W H₀b z q a c ω)) (ω c) := by
    intro ω c
    have h := GUETwistBA_hasDerivAt_Phi p (GUETwistBA_hasDerivAt_T hH hz Mbl q a ω c)
    simpa only [Function.update_eq_self] using h
  have hFb : ∃ C : ℝ, ∀ ω : Ω d L W, ‖GUETwistBA_Phi p (GUETwistBA_T d L W H₀b z Mbl q a ω)‖ ≤ C :=
    GUETwistBA_bdd_comp hH hz (fun G => GUETwistBA_Phi p (GUETwistBA_Tm d L W Mbl q a G))
      ((GUETwistBA_Phi_cont p).comp (GUETwistBA_Tm_cont Mbl q a))
  have hF'b : ∃ C : ℝ, ∀ (c : CoordF d L W) (ω : Ω d L W),
      ‖GUETwistBA_Phi' p (GUETwistBA_T d L W H₀b z Mbl q a ω) (GUETwistBA_T' d L W H₀b z q a c ω)‖ ≤ C := by
    refine GUETwistBA_unif_bdd fun c => ?_
    refine GUETwistBA_bdd_comp hH hz (fun G => GUETwistBA_Phi' p (GUETwistBA_Tm d L W Mbl q a G)
      (-(((W : ℂ) ^ d)⁻¹ * Matrix.trace (G * coordinateBlock d L W c * G * GUETwistBA_Pi d L W q a)))) ?_
    have h1 : Continuous fun G : Matrix (Vtx d L W) (Vtx d L W) ℂ =>
        -(((W : ℂ) ^ d)⁻¹ * Matrix.trace (G * coordinateBlock d L W c * G * GUETwistBA_Pi d L W q a)) :=
      (continuous_const.mul ((continuous_matrixTrace d L W).comp
        (((continuous_id.mul continuous_const).mul continuous_id).mul continuous_const))).neg
    have h := (GUETwistBA_Phi'_cont p).comp ((GUETwistBA_Tm_cont Mbl q a).prodMk h1)
    exact h
  have hdef := fun p' : Zd d L => GUETwistBA_stein_defect (t1 := t1) hσ v hv hH hz (GUETwistBA_Pi d L W p' a)
    (fun ω => GUETwistBA_Phi p (GUETwistBA_T d L W H₀b z Mbl q a ω))
    (fun c ω => GUETwistBA_Phi' p (GUETwistBA_T d L W H₀b z Mbl q a ω) (GUETwistBA_T' d L W H₀b z q a c ω)) hFc hF'c hFd hFb hF'b
  have hdefI := fun p' : Zd d L => GUETwistBA_integrable_defect (t1 := t1) (σ := σ) v hH hz (GUETwistBA_Pi d L W p' a)
    (fun ω => GUETwistBA_Phi p (GUETwistBA_T d L W H₀b z Mbl q a ω))
    (fun c ω => GUETwistBA_Phi' p (GUETwistBA_T d L W H₀b z Mbl q a ω) (GUETwistBA_T' d L W H₀b z q a c ω)) hFc hF'c hFb hF'b
  have hZpI : ∀ p' : Zd d L, Integrable (fun ω : Ω d L W => GUETwistBA_Z d L W t1 σ v H₀b z Mbl p q a p' ω) (GaussianProduct.law v) :=
    fun p' => hdefI p'
  have hZp0 : ∀ p' : Zd d L, ∫ ω : Ω d L W, GUETwistBA_Z d L W t1 σ v H₀b z Mbl p q a p' ω ∂(GaussianProduct.law v) = 0 :=
    fun p' => hdef p'
  have hrow : ∀ p' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ) := GUETwistBA_hrow hL hu
  have hpt : ∀ ω : Ω d L W, ((‖GUETwistBA_T d L W H₀b z Mbl q a ω‖ ^ (2 * p) : ℝ) : ℂ) =
      (GUETwistBA_g1 d L W t1 σ m Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        ((p : ℂ) - 1) * GUETwistBA_g2 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        (p : ℂ) * GUETwistBA_g3 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true)) +
      (-(((W : ℂ) ^ d)⁻¹)) * ∑ p' : Zd d L, Mbl q p' * GUETwistBA_Z d L W t1 σ v H₀b z Mbl p q a p' ω :=
    fun ω => GUETwistBA_pointwise hσ hrow v hv p hp q a (blockMat d L W (Xmat d L W ω))
      (Gres (H₀b + HflowBlock d L W 1 ω) z true) (GUETwistBA_T_eq hH hz hM hMb q a ω)
  have hLc : Continuous fun ω : Ω d L W => ((‖GUETwistBA_T d L W H₀b z Mbl q a ω‖ ^ (2 * p) : ℝ) : ℂ) := by
    have h := Complex.continuous_ofReal.comp ((continuous_norm.comp hTc).pow (2 * p))
    exact h
  have hLb : ∃ C : ℝ, ∀ ω : Ω d L W, ‖((‖GUETwistBA_T d L W H₀b z Mbl q a ω‖ ^ (2 * p) : ℝ) : ℂ)‖ ≤ C :=
    GUETwistBA_bdd_comp hH hz (fun G => ((‖GUETwistBA_Tm d L W Mbl q a G‖ ^ (2 * p) : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((continuous_norm.comp (GUETwistBA_Tm_cont Mbl q a)).pow (2 * p)))
  have hLI := GUETwistBA_integrable_of_cont_bdd v hLc hLb
  have hZI : Integrable (fun ω : Ω d L W => (-(((W : ℂ) ^ d)⁻¹)) * ∑ p' : Zd d L, Mbl q p' *
      GUETwistBA_Z d L W t1 σ v H₀b z Mbl p q a p' ω) (GaussianProduct.law v) :=
    (integrable_finsetSum _ fun p' _ => (hZpI p').const_mul _).const_mul _
  have hPI : Integrable (fun ω : Ω d L W => GUETwistBA_g1 d L W t1 σ m Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        ((p : ℂ) - 1) * GUETwistBA_g2 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        (p : ℂ) * GUETwistBA_g3 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true)) (GaussianProduct.law v) := by
    have h := hLI.sub hZI
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    rw [hpt ω]
    ring
  have hZ0 : ∫ ω : Ω d L W, (-(((W : ℂ) ^ d)⁻¹)) * ∑ p' : Zd d L, Mbl q p' *
      GUETwistBA_Z d L W t1 σ v H₀b z Mbl p q a p' ω ∂(GaussianProduct.law v) = 0 := by
    rw [integral_const_mul, integral_finsetSum _ (fun p' _ => (hZpI p').const_mul _)]
    simp only [integral_const_mul, hZp0, mul_zero, Finset.sum_const_zero]
  calc ∫ ω : Ω d L W, ((‖GUETwistBA_T d L W H₀b z Mbl q a ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(GaussianProduct.law v)
      = ∫ ω : Ω d L W, ((GUETwistBA_g1 d L W t1 σ m Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        ((p : ℂ) - 1) * GUETwistBA_g2 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true) +
        (p : ℂ) * GUETwistBA_g3 d L W t1 σ Mbl p q a (Gres (H₀b + HflowBlock d L W 1 ω) z true)) +
        (-(((W : ℂ) ^ d)⁻¹)) * ∑ p' : Zd d L, Mbl q p' * GUETwistBA_Z d L W t1 σ v H₀b z Mbl p q a p' ω) ∂(GaussianProduct.law v) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = _ := by rw [integral_add hPI hZI, hZ0, add_zero]

end Moment

section Bounds

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `Ŝ_{p's} = t₁ S^{(B)}(0)_{p's} + σ = (t₁ δ_{p's} + σ)` is a real nonnegative number (`S^{(B)}(0) = 1`). -/
theorem GUETwistBA_Shat_eq (t1 σ : ℝ) (p s : Zd d L) :
    ((t1 : ℂ) * SB d L 0 p s + (σ : ℂ)) = (((if p = s then t1 else 0) + σ : ℝ) : ℂ) := by
  have : SB d L 0 p s = if p = s then 1 else 0 := by rw [EMn2BA_SB_zero]; simp [Matrix.one_apply]
  rw [this]
  split_ifs <;> simp

theorem GUETwistBA_Shat_nonneg {t1 σ : ℝ} (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ) (p s : Zd d L) : 0 ≤ (if p = s then t1 else 0) + σ := by
  split_ifs <;> linarith

theorem GUETwistBA_Shat_row {t1 σ u : ℝ} (hrow : ∀ p' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ))
    (p' : Zd d L) : ∑ s : Zd d L, ((if p' = s then t1 else 0) + σ : ℝ) = u := by
  have h := hrow p'
  simp only [GUETwistBA_Shat_eq] at h
  exact_mod_cast h

/-- The good-event bound of `D_{p'} = Σ_s Ŝ_{p's} (g_s - m)`: `‖D‖ ≤ u B₁` when `‖g_s - m‖ ≤ B₁`. -/
theorem GUETwistBA_Dm_le {t1 σ u B1 : ℝ} (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ)
    (hrow : ∀ p' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ)) (m : ℂ) (p' : Zd d L)
    (Gm : Matrix (Vtx d L W) (Vtx d L W) ℂ) (h1 : ∀ s : Zd d L, ‖Matrix.trace (Gm * Eblk d L W s) - m‖ ≤ B1) :
    ‖GUETwistBA_Dm d L W t1 σ m p' Gm‖ ≤ u * B1 := by
  unfold GUETwistBA_Dm
  refine (norm_sum_le _ _).trans ?_
  calc ∑ s, ‖((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) * (Matrix.trace (Gm * Eblk d L W s) - m)‖
      ≤ ∑ s, ((if p' = s then t1 else 0) + σ) * B1 := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [norm_mul, GUETwistBA_Shat_eq, Complex.norm_real, Real.norm_of_nonneg (GUETwistBA_Shat_nonneg ht1 hσ p' s)]
        exact mul_le_mul_of_nonneg_left (h1 s) (GUETwistBA_Shat_nonneg ht1 hσ p' s)
    _ = u * B1 := by rw [← Finset.sum_mul, GUETwistBA_Shat_row hrow p']

/-- The weighted double sum of the derivative terms: `‖W^{-2d} Σ_{p'} M_{qp'} Σ_s Ŝ_{p's} x_{p's}‖ ≤ (Σ_{p'} |M_{qp'}|) u B` when `‖x_{p's}‖ ≤ W^{2d} B`. -/
theorem GUETwistBA_R_aux {t1 σ u B : ℝ} (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ)
    (hrow : ∀ p' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ))
    (Mbl : Zd d L → Zd d L → ℂ) (q : Zd d L) (x : Zd d L → Zd d L → ℂ) (hx : ∀ p' s, ‖x p' s‖ ≤ ((W : ℝ) ^ d) ^ 2 * B) :
    ‖(((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ p' : Zd d L, Mbl q p' * ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) * x p' s‖ ≤
      (∑ p', ‖Mbl q p'‖) * u * B := by
  have hW : (0 : ℝ) < (W : ℝ) ^ d := pow_pos (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne W))) d
  rw [norm_mul]
  have hc : ‖(((W : ℂ) ^ d)⁻¹) ^ 2‖ = ((W : ℝ) ^ d)⁻¹ ^ 2 := by simp
  rw [hc]
  have hS : ∀ p' : Zd d L, ‖∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) * x p' s‖ ≤ u * (((W : ℝ) ^ d) ^ 2 * B) := by
    intro p'
    refine (norm_sum_le _ _).trans ?_
    calc ∑ s, ‖((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) * x p' s‖
        ≤ ∑ s, ((if p' = s then t1 else 0) + σ) * (((W : ℝ) ^ d) ^ 2 * B) := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [norm_mul, GUETwistBA_Shat_eq, Complex.norm_real, Real.norm_of_nonneg (GUETwistBA_Shat_nonneg ht1 hσ p' s)]
          exact mul_le_mul_of_nonneg_left (hx p' s) (GUETwistBA_Shat_nonneg ht1 hσ p' s)
      _ = _ := by rw [← Finset.sum_mul, GUETwistBA_Shat_row hrow p']
  calc ((W : ℝ) ^ d)⁻¹ ^ 2 * ‖∑ p' : Zd d L, Mbl q p' * ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) * x p' s‖
      ≤ ((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ p' : Zd d L, ‖Mbl q p'‖ * (u * (((W : ℝ) ^ d) ^ 2 * B)) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p' _ => ?_)) (by positivity)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hS p') (norm_nonneg _)
    _ = (∑ p', ‖Mbl q p'‖) * u * B := by
        rw [← Finset.sum_mul]
        field_simp

/-- The good-event bound of `R₁`: `‖R₁‖ ≤ (Σ_{p'} |M_{qp'}|) u (B₂ B₄)^{1/2}` from the loop bounds `‖𝓛²‖ ≤ B₂`, `‖𝓛⁴‖ ≤ B₄` (`GUETwistBA_RB1`). -/
theorem GUETwistBA_R1m_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {t1 σ u B2 B4 : ℝ}
    (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ)
    (hrow : ∀ p' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ))
    (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L)
    (h2 : ∀ p' : Zd d L, ‖loopL d L W H z ⟨[true, false], [a, p']⟩‖ ≤ B2)
    (h4 : ∀ s : Zd d L, ‖loopL d L W H z ⟨[false, false, true, true], [s, q, s, a]⟩‖ ≤ B4) :
    ‖GUETwistBA_R1m d L W t1 σ Mbl q a (Gres H z true)‖ ≤ (∑ p', ‖Mbl q p'‖) * u * Real.sqrt (B2 * B4) :=
  GUETwistBA_R_aux ht1 hσ hrow Mbl q _ fun p' s =>
    (GUETwistBA_RB1 hH z p' q a s).trans (mul_le_mul_of_nonneg_left (by
      rw [← Real.sqrt_mul (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (mul_le_mul (h2 p') (h4 s) (norm_nonneg _) ((norm_nonneg _).trans (h2 p')))) (by positivity))

theorem GUETwistBA_R2m_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {t1 σ u B2 B4 : ℝ}
    (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ)
    (hrow : ∀ p' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ))
    (Mbl : Zd d L → Zd d L → ℂ) (q a : Zd d L)
    (h2 : ∀ p' : Zd d L, ‖loopL d L W H z ⟨[false, true], [q, p']⟩‖ ≤ B2)
    (h4 : ∀ s : Zd d L, ‖loopL d L W H z ⟨[false, true, false, true], [s, a, s, a]⟩‖ ≤ B4) :
    ‖GUETwistBA_R2m d L W t1 σ Mbl q a (Gres H z true)‖ ≤ (∑ p', ‖Mbl q p'‖) * u * Real.sqrt (B2 * B4) := by
  exact GUETwistBA_R_aux ht1 hσ hrow Mbl q _ fun p' s =>
    (GUETwistBA_RB2 hH z p' q a s).trans (mul_le_mul_of_nonneg_left (by
      rw [← Real.sqrt_mul (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (mul_le_mul (h2 p') (h4 s) (norm_nonneg _) ((norm_nonneg _).trans (h2 p')))) (by positivity))


/-- **The crude envelope** (global, every sample): with `N = (L W)^d`, `r = η⁻¹ ≥ 1`, `‖G‖ ≤ r`, `|M_{ab}| ≤ 1`, `‖m‖ ≤ 1`, all of
`‖T_{qa}‖, ‖D_{p'}‖, ‖R₁‖, ‖R₂‖` are at most `2 N² r³` (`norm_gloop_le_crude` for the loops of `R_i`). -/
theorem GUETwistBA_env {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hηz : η ≤ |z.im|) (hη1 : η ≤ 1) {t1 σ u : ℝ} (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ) (hu1 : u ≤ 1)
    (hrow : ∀ p' : Zd d L, ∑ s : Zd d L, ((t1 : ℂ) * SB d L 0 p' s + (σ : ℂ)) = (u : ℂ)) {m : ℂ} (hm : ‖m‖ ≤ 1)
    (Mbl : Zd d L → Zd d L → ℂ) (hMbl : ∀ b b', ‖Mbl b b'‖ ≤ 1) (p' q a : Zd d L) :
    ‖GUETwistBA_Tm d L W Mbl q a (Gres H z true)‖ ≤ 2 * (((L * W) ^ d : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ 3 ∧
    ‖GUETwistBA_Dm d L W t1 σ m p' (Gres H z true)‖ ≤ 2 * (((L * W) ^ d : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ 3 ∧
    ‖GUETwistBA_R1m d L W t1 σ Mbl q a (Gres H z true)‖ ≤ 2 * (((L * W) ^ d : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ 3 ∧
    ‖GUETwistBA_R2m d L W t1 σ Mbl q a (Gres H z true)‖ ≤ 2 * (((L * W) ^ d : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ 3 := by
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hW1 : (1 : ℝ) ≤ (W : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W))
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L))
  set N : ℝ := (((L * W) ^ d : ℕ) : ℝ) with hN
  have hNeq : N = (L : ℝ) ^ d * (W : ℝ) ^ d := by rw [hN]; push_cast; ring
  have hN1 : 1 ≤ N := by rw [hNeq]; nlinarith
  have hLN : (L : ℝ) ^ d ≤ N := by rw [hNeq]; nlinarith
  set r : ℝ := η⁻¹ with hr
  have hr1 : 1 ≤ r := (one_le_inv₀ hη).2 hη1
  have hr0 : 0 < r := by linarith
  have hG : ‖Gres H z true‖ ≤ r := norm_Gsig_le_inv_eta hH hη hηz true
  have hE0 : 1 ≤ 2 * N ^ 2 * r ^ 3 := by
    have : 1 ≤ N ^ 2 * r ^ 3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) (one_le_pow₀ hr1)
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `T`
    unfold GUETwistBA_Tm
    have h1 : ‖((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gres H z true * GUETwistBA_Pi d L W q a)‖ ≤ r := by
      rw [GUETwistBA_trace_Pi, norm_mul]
      have : ‖∑ o : Fin (W ^ d), Gres H z true (q, o) (a, o)‖ ≤ (W : ℝ) ^ d * r := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ o : Fin (W ^ d), ‖Gres H z true (q, o) (a, o)‖ ≤ ∑ o : Fin (W ^ d), r :=
              Finset.sum_le_sum fun o _ => (norm_matrix_entry_le_opNorm _ _ _).trans hG
          _ = _ := by simp
      calc ‖((W : ℂ) ^ d)⁻¹‖ * ‖∑ o : Fin (W ^ d), Gres H z true (q, o) (a, o)‖ ≤ ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d * r) := by
            gcongr
            simp
        _ = r := by field_simp
    calc _ ≤ ‖((W : ℂ) ^ d)⁻¹ * Matrix.trace (Gres H z true * GUETwistBA_Pi d L W q a)‖ + ‖Mbl q a‖ := norm_sub_le _ _
      _ ≤ r + 1 := add_le_add h1 (hMbl q a)
      _ ≤ 2 * N ^ 2 * r ^ 3 := by
        have : r ≤ r ^ 3 := by nlinarith [one_le_pow₀ hr1 (n := 2)]
        nlinarith [one_le_pow₀ hN1 (n := 2)]
  · -- `D`
    have hg : ∀ s : Zd d L, ‖Matrix.trace (Gres H z true * Eblk d L W s) - m‖ ≤ 2 * N * r := by
      intro s
      have h1 := ExpAvgGen_trG_bdd (Gres H z true) (Eblk d L W s) hG
      have h2 : ‖Eblk d L W s‖ ≤ 1 := (norm_Eblk_le_inv_W_sq d L W s).trans (inv_le_one_of_one_le₀ hW1)
      have h3 : ‖Matrix.trace (Gres H z true * Eblk d L W s)‖ ≤ N * r :=
        h1.trans (by
          calc N * (r * ‖Eblk d L W s‖) ≤ N * (r * 1) := by gcongr
            _ = N * r := by ring)
      calc _ ≤ ‖Matrix.trace (Gres H z true * Eblk d L W s)‖ + ‖m‖ := norm_sub_le _ _
        _ ≤ N * r + 1 := add_le_add h3 hm
        _ ≤ 2 * N * r := by nlinarith [mul_le_mul hN1 hr1 zero_le_one (by linarith : (0 : ℝ) ≤ N)]
    refine (GUETwistBA_Dm_le ht1 hσ hrow m p' _ hg).trans ?_
    have : 2 * N * r ≤ 2 * N ^ 2 * r ^ 3 := by
      have h3 : 1 ≤ N * r ^ 2 := one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hr1)
      nlinarith [mul_pos (by linarith : (0 : ℝ) < N) hr0]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < N) hr0]
  all_goals
    have hW2 : ((W : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
    have hl : ∀ (I : Loop.LoopIdx (Zd d L)), I.WF → ‖loopL d L W H z I‖ ≤ N * (r * ((W : ℝ) ^ d)⁻¹) ^ I.a.length :=
      fun I hI => norm_gloop_le_crude d L W hH hη hηz I hI
    have hl2 : ∀ (σ₁ σ₂ : Bool) (x y : Zd d L), ‖loopL d L W H z ⟨[σ₁, σ₂], [x, y]⟩‖ ≤ N * r ^ 2 := fun σ₁ σ₂ x y =>
      (hl ⟨[σ₁, σ₂], [x, y]⟩ (by simp [Loop.LoopIdx.WF])).trans (by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ N)
        change (r * ((W : ℝ) ^ d)⁻¹) ^ 2 ≤ r ^ 2
        exact pow_le_pow_left₀ (by positivity) (by nlinarith [inv_nonneg.2 (zero_le_one.trans hW1)]) 2)
    have hl4 : ∀ (σ₁ σ₂ σ₃ σ₄ : Bool) (x y w v : Zd d L), ‖loopL d L W H z ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩‖ ≤ N * r ^ 4 :=
      fun σ₁ σ₂ σ₃ σ₄ x y w v => (hl ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩ (by simp [Loop.LoopIdx.WF])).trans (by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ N)
        change (r * ((W : ℝ) ^ d)⁻¹) ^ 4 ≤ r ^ 4
        exact pow_le_pow_left₀ (by positivity) (by nlinarith [inv_nonneg.2 (zero_le_one.trans hW1)]) 4)
    have hsq : Real.sqrt (N * r ^ 2 * (N * r ^ 4)) = N * r ^ 3 := by
      rw [show N * r ^ 2 * (N * r ^ 4) = (N * r ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hsM : ∑ p', ‖Mbl q p'‖ ≤ N := by
      calc ∑ p', ‖Mbl q p'‖ ≤ ∑ _p' : Zd d L, (1 : ℝ) := Finset.sum_le_sum fun p' _ => hMbl q p'
        _ = (L : ℝ) ^ d := by simp [Zd, ZMod.card]
        _ ≤ N := hLN
  · have h := GUETwistBA_R1m_le hH z ht1 hσ hrow Mbl q a (B2 := N * r ^ 2) (B4 := N * r ^ 4) (fun p' => hl2 _ _ _ _)
      (fun s => hl4 _ _ _ _ _ _ _ _)
    rw [hsq] at h
    refine h.trans ?_
    have : (∑ p', ‖Mbl q p'‖) * u * (N * r ^ 3) ≤ N * 1 * (N * r ^ 3) := by
      have hu0 : 0 ≤ u := by
        have := hrow q
        have h0 : (0 : ℝ) ≤ ∑ s : Zd d L, ((if q = s then t1 else 0) + σ) := Finset.sum_nonneg fun s _ => GUETwistBA_Shat_nonneg ht1 hσ q s
        rw [GUETwistBA_Shat_row hrow q] at h0; exact h0
      gcongr
    nlinarith [pow_pos hr0 3, pow_pos (by linarith : (0 : ℝ) < N) 2]
  · have h := GUETwistBA_R2m_le hH z ht1 hσ hrow Mbl q a (B2 := N * r ^ 2) (B4 := N * r ^ 4) (fun p' => hl2 _ _ _ _)
      (fun s => hl4 _ _ _ _ _ _ _ _)
    rw [hsq] at h
    refine h.trans ?_
    have : (∑ p', ‖Mbl q p'‖) * u * (N * r ^ 3) ≤ N * 1 * (N * r ^ 3) := by
      have hu0 : 0 ≤ u := by
        have h0 : (0 : ℝ) ≤ ∑ s : Zd d L, ((if q = s then t1 else 0) + σ) := Finset.sum_nonneg fun s _ => GUETwistBA_Shat_nonneg ht1 hσ q s
        rw [GUETwistBA_Shat_row hrow q] at h0; exact h0
      gcongr
    nlinarith [pow_pos hr0 3, pow_pos (by linarith : (0 : ℝ) < N) 2]

end Bounds

section Good

variable {d : ℕ}

/-- The good event of the path bounds at one `n`: at every grid time `j ≤ K n`, with `Λ_j = (N η_j)⁻¹` and `ρ = N^ε`: the diagonal
1-loops are within `ρ Λ_j` of `m`; if `Λ_j ≤ 1`, the 2- and 4-loops are `≤ 2 ρ Λ_j`, `≤ 2 ρ Λ_j³`; the entries of `G - M` are `≤ ρ Λ_j^{1/2}`. -/
def GUETwistBA_Good (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (ε : ℝ) (n : ℕ) (ω : PathΩ (sz.withLam 0)) : Prop :=
  ∀ j : Fin (K n + 1),
    (∀ b : Zd d (sz.L n), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n j)) ⟨[true], [b]⟩ - m n‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ∧
    ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ≤ 1 →
      (∀ (σ₁ σ₂ : Bool) (x y : Zd d (sz.L n)),
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n j)) ⟨[σ₁, σ₂], [x, y]⟩‖ ≤
        2 * (((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹)) ∧
      (∀ (σ₁ σ₂ σ₃ σ₄ : Bool) (x y w v : Zd d (sz.L n)),
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n j)) ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩‖ ≤
        2 * (((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 3))) ∧
    (∀ x y : Idx d (sz.L n) (sz.W n),
      ‖green (gueHBA sz g t1 t0 K n j ω) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) x y -
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ ((1 : ℝ) / 2))


theorem GUETwistBA_toMeas {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') (S1 S2 S3 S4 : Set Ω') {x : ℝ} (hx : 0 ≤ x)
    (h1 : μ S1 ≤ ENNReal.ofReal x) (h2 : μ S2 ≤ ENNReal.ofReal x) (h3 : μ S3 ≤ ENNReal.ofReal x) (h4 : μ S4 ≤ ENNReal.ofReal x) :
    ∃ B : Set Ω', MeasurableSet B ∧ S1 ∪ S2 ∪ S3 ∪ S4 ⊆ B ∧ μ B ≤ ENNReal.ofReal (4 * x) := by
  refine ⟨toMeasurable μ (S1 ∪ S2 ∪ S3 ∪ S4), measurableSet_toMeasurable _ _, subset_toMeasurable _ _, ?_⟩
  rw [measure_toMeasurable]
  calc μ (S1 ∪ S2 ∪ S3 ∪ S4) ≤ μ (S1 ∪ S2 ∪ S3) + μ S4 := measure_union_le _ _
    _ ≤ (μ (S1 ∪ S2) + μ S3) + μ S4 := add_le_add_left (measure_union_le _ _) _
    _ ≤ ((μ S1 + μ S2) + μ S3) + μ S4 := add_le_add_left (add_le_add_left (measure_union_le _ _) _) _
    _ ≤ ((ENNReal.ofReal x + ENNReal.ofReal x) + ENNReal.ofReal x) + ENNReal.ofReal x :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = ENNReal.ofReal (4 * x) := by
        rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity) hx, ← ENNReal.ofReal_add (by positivity) hx]
        congr 1; ring

/-- **The good event off the bad sets** (the pointwise half of `GUETwistBA_good`): if at every grid time `j` the 1-, 2- and 4-loops are
within `N^ε Λ_j^k` of the primitive family `Kt`, the entries of `G - M` are within `N^ε Λ_j^{1/2}`, and `Kt` satisfies the K-bound and is `m`
on 1-loops, then the path satisfies `GUETwistBA_Good`: the diagonal 1-loops are within `ρ Λ_j` of `m`, the 2- and 4-loops are `≤ 2 ρ Λ_j`,
`≤ 2 ρ Λ_j³` when `Λ_j ≤ 1`. -/
theorem GUETwistBA_Good_of_loops (sz : Sizes d) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {K : ℕ → ℕ}
    {Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ} {ε : ℝ} {n : ℕ} {ω : PathΩ (sz.withLam 0)}
    (hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ))
    (hKm : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ)
    (hKn : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length → I.length ≤ 4 →
      ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1))
    (hgrid : ∀ j : Fin (K n + 1), gridTime t1 t0 K n j ∈ Set.Icc (t1 n) (t0 n))
    (e1 : ∀ (j : Fin (K n + 1)) (σ : Fin 1 → Bool) (a : Fin 1 → Zd d (sz.L n)),
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (loopOf σ a) - Kt n (gridTime t1 t0 K n j) (loopOf σ a)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 1)
    (e2 : ∀ (j : Fin (K n + 1)) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (loopOf σ a) - Kt n (gridTime t1 t0 K n j) (loopOf σ a)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 2)
    (e4 : ∀ (j : Fin (K n + 1)) (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)),
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (loopOf σ a) - Kt n (gridTime t1 t0 K n j) (loopOf σ a)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 4)
    (eL : ∀ (j : Fin (K n + 1)) (x y : Idx d (sz.L n) (sz.W n)),
        ‖green (gueHBA sz g t1 t0 K n j ω) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) x y -
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ ((1 : ℝ) / 2)) :
    GUETwistBA_Good sz g E t1 t0 m K ε n ω := by
  intro j
  have hs := hgrid j
  have e1 := e1 j
  have e2 := e2 j
  have e4 := e4 j
  have eL := eL j
  have hNε : 0 < ((sz.size n : ℕ) : ℝ) ^ ε := Real.rpow_pos_of_pos hN0 _
  set Λ : ℝ := (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have h : ‖Kt n (gridTime t1 t0 K n j) ⟨[true, true], [0, 0]⟩‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Λ ^ 1 :=
      hKn _ hs ⟨[true, true], [0, 0]⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length])
    have h' : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Λ := by
      have := (norm_nonneg _).trans h
      simpa using this
    exact (mul_nonneg_iff_of_pos_left hNε).1 h'
  refine ⟨fun b => ?_, fun hΛ1 => ⟨fun σ₁ σ₂ x y => ?_, fun σ₁ σ₂ σ₃ σ₄ x y w v => ?_⟩, eL⟩
  · have h := e1 (fun _ => true) (fun _ => b)
    have hL : loopOf (fun _ : Fin 1 => true) (fun _ => b) = (⟨[true], [b]⟩ : LoopIdx (Zd d (sz.L n))) := by
      simp [loopOf, List.ofFn_succ]
    rw [hL, hKm _ hs true b] at h
    simpa [mSigOf] using h
  · have h := e2 ![σ₁, σ₂] ![x, y]
    have hK : ‖Kt n (gridTime t1 t0 K n j) ⟨[σ₁, σ₂], [x, y]⟩‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Λ ^ 1 :=
      hKn _ hs ⟨[σ₁, σ₂], [x, y]⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length])
    have hL : loopOf ![σ₁, σ₂] ![x, y] = (⟨[σ₁, σ₂], [x, y]⟩ : LoopIdx (Zd d (sz.L n))) := by simp [loopOf, List.ofFn_succ]
    rw [hL] at h
    calc _ ≤ ‖Kt n (gridTime t1 t0 K n j) ⟨[σ₁, σ₂], [x, y]⟩‖ + ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
          (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) ⟨[σ₁, σ₂], [x, y]⟩ -
          Kt n (gridTime t1 t0 K n j) ⟨[σ₁, σ₂], [x, y]⟩‖ := by
          refine le_of_eq_of_le ?_ (norm_add_le _ _); congr 1; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Λ + ((sz.size n : ℕ) : ℝ) ^ ε * Λ ^ 2 := add_le_add (by simpa using hK) h
      _ ≤ 2 * (((sz.size n : ℕ) : ℝ) ^ ε * Λ) := by nlinarith [mul_le_mul_of_nonneg_left (show Λ ^ 2 ≤ Λ by nlinarith) hNε.le]
  · have h := e4 ![σ₁, σ₂, σ₃, σ₄] ![x, y, w, v]
    have hK : ‖Kt n (gridTime t1 t0 K n j) ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Λ ^ 3 :=
      hKn _ hs ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length])
    have hL : loopOf ![σ₁, σ₂, σ₃, σ₄] ![x, y, w, v] = (⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩ : LoopIdx (Zd d (sz.L n))) := by
      simp [loopOf, List.ofFn_succ]
    rw [hL] at h
    calc _ ≤ ‖Kt n (gridTime t1 t0 K n j) ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩‖ + ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
          (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩ -
          Kt n (gridTime t1 t0 K n j) ⟨[σ₁, σ₂, σ₃, σ₄], [x, y, w, v]⟩‖ := by
          refine le_of_eq_of_le ?_ (norm_add_le _ _); congr 1; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Λ ^ 3 + ((sz.size n : ℕ) : ℝ) ^ ε * Λ ^ 4 := add_le_add hK h
      _ ≤ 2 * (((sz.size n : ℕ) : ℝ) ^ ε * Λ ^ 3) := by
          nlinarith [mul_le_mul_of_nonneg_left (show Λ ^ 4 ≤ Λ ^ 3 by nlinarith [pow_nonneg hΛ0 3]) hNε.le]


/-- **The PB interface** (R1's inputs, `T2519_PBBA` at the grid): from `GUEPathBoundsBA` (`lk 1, 2, 4` and `localLaw`), the K-bound at the
grid times and `Kt = m` on 1-loops, there is, eventually in `n`, a measurable exceptional set `B` of probability `≤ N^{-D}` off which
`GUETwistBA_Good` holds. -/
theorem GUETwistBA_good (sz : Sizes d) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {K : ℕ → ℕ} {n0 : ℕ}
    {Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ}
    (hsize : Tendsto (fun n => sz.size n) atTop atTop) (hn0 : 4 ≤ n0)
    (hPB : GUEPathBoundsBA sz g E t1 t0 m K n0 Kt)
    (hKm : ∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ)
    (hKb : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)),
      I.WF → 2 ≤ I.length → I.length ≤ 4 →
      ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1))
    (hgrid : ∀ n (k : ℕ), k ≤ K n → gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n)) {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∀ᶠ n in atTop, 0 < g n → ∃ B : Set (PathΩ (sz.withLam 0)), MeasurableSet B ∧
      Pgue (sz.withLam 0) B ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) ∧ ∀ ω ∉ B, GUETwistBA_Good sz g E t1 t0 m K ε n ω := by
  obtain ⟨hlk, hLL⟩ := hPB
  have h1 := hlk 1 le_rfl (by omega) ε hε (D + 1) (by linarith)
  have h2 := hlk 2 (by norm_num) (by omega) ε hε (D + 1) (by linarith)
  have h4 := hlk 4 (by norm_num) hn0 ε hε (D + 1) (by linarith)
  have hL := hLL ε hε (D + 1) (by linarith)
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_iff.mpr hsize
  filter_upwards [h1, h2, h4, hL, hKb ε hε, hsz.eventually (eventually_ge_atTop 4)] with n h1n h2n h4n hLn hKn hN4 hg
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  obtain ⟨B, hBm, hsub, hBμ⟩ := GUETwistBA_toMeas (Pgue (sz.withLam 0)) _ _ _ _ (x := ((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) (Real.rpow_nonneg hN0.le _) h1n h2n h4n hLn
  refine ⟨B, hBm, hBμ.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have h : ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) = ((sz.size n : ℕ) : ℝ) ^ (-D) * ((sz.size n : ℕ) : ℝ)⁻¹ := by
      rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    rw [h]
    have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
    have : 4 * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN4
    nlinarith [mul_le_mul_of_nonneg_left this hp.le]
  · intro ω hω
    refine GUETwistBA_Good_of_loops sz hN0 (hKm n hg) hKn (fun j => hgrid n j (Nat.lt_succ_iff.1 j.isLt)) ?_ ?_ ?_ ?_
    · intro j σ a
      by_contra hc
      exact hω (hsub (Or.inl (Or.inl (Or.inl ⟨(j, σ, a), lt_of_not_ge hc⟩))))
    · intro j σ a
      by_contra hc
      exact hω (hsub (Or.inl (Or.inl (Or.inr ⟨(j, σ, a), lt_of_not_ge hc⟩))))
    · intro j σ a
      by_contra hc
      exact hω (hsub (Or.inl (Or.inr ⟨(j, σ, a), lt_of_not_ge hc⟩)))
    · intro j x y
      by_contra hc
      exact hω (hsub (Or.inr ⟨(j, x, y), lt_of_not_ge hc⟩))

end Good

section Ident

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `Σ_{x∈[a]} f x = Σ_o f (a, o)`: a block as its offsets (probe `t/T2519` b992c2e7 `probe_iblk`). -/
theorem GUETwistBA_iblk (a : Zd d L) (f : Idx d L W → ℂ) :
    ∑ x ∈ Iblk d L W a, f x = ∑ o : Fin (W ^ d), f ((splitEquiv d L W).symm (a, o)) := by
  have hs : ∀ x ∈ Iblk d L W a, (splitEquiv d L W).symm (a, (split d L W x).2) = x := fun x hx => by
    simp only [Iblk, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have : ((split d L W x).1, (split d L W x).2) = split d L W x := rfl
    rw [hx] at this; rw [this]; exact (splitEquiv d L W).symm_apply_apply x
  refine Finset.sum_nbij' (fun x => (split d L W x).2) (fun o => (splitEquiv d L W).symm (a, o))
    (fun _ _ => Finset.mem_univ _) (fun o _ => ?_) hs (fun o _ => congrArg Prod.snd ((splitEquiv d L W).apply_symm_apply (a, o)))
    (fun x hx => by rw [hs x hx])
  simp only [Iblk, Finset.mem_filter, Finset.mem_univ, true_and]
  exact congrArg Prod.fst ((splitEquiv d L W).apply_symm_apply (a, o))

/-- The fine entries of `M = Mres (g Ψ_I) E m = M^{(B)} ⊗ 1` in offset coordinates (`BAMres_fine_apply`). -/
theorem GUETwistBA_Mres_entry (g : ℝ) (E m : ℂ) (hw : (E + m).im ≠ 0) (b b' : Zd d L) (o o' : Fin (W ^ d)) :
    Mres ((g : ℂ) • PsiI d L W) E m ((splitEquiv d L W).symm (b, o)) ((splitEquiv d L W).symm (b', o')) =
      if o = o' then BAMB d L g E m b b' else 0 := by
  rw [BAMres_fine_apply d L W g E m hw]
  have h1 := (splitEquiv d L W).apply_symm_apply (b, o)
  have h2 := (splitEquiv d L W).apply_symm_apply (b', o')
  change split d L W _ = _ at h1 h2
  rw [h1, h2]

/-- **The identity** (T2517 `(a)` row 8; probe `probe_ident`): `t_{aq} - M^{(++)}_{aq} = M^{(B)}_{aq} T_{qa}` for every matrix `G`,
`T_{qa} = W^{-d} Σ_o (G - M)_{(q,o),(a,o)}` (here in the block form `GUETwistBA_Tm` of `blockMat G`). -/
theorem GUETwistBA_ident (g : ℝ) (E m : ℂ) (hw : (E + m).im ≠ 0) (G : Matrix (Idx d L W) (Idx d L W) ℂ) (a q : Zd d L) :
    ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, Mres ((g : ℂ) • PsiI d L W) E m x y * G y x -
        BAMss d L (BAMB d L g E m) true true a q =
      BAMB d L g E m a q * GUETwistBA_Tm d L W (BAMB d L g E m) q a (blockMat d L W G) := by
  classical
  have hM := GUETwistBA_Mres_entry (d := d) (L := L) (W := W) g E m hw
  have hWd : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  rw [GUETwistBA_iblk a]
  simp_rw [GUETwistBA_iblk q, hM]
  simp only [GUETwistBA_Tm, GUETwistBA_trace_Pi, blockMat, Matrix.submatrix_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, BAMss, BAMsigma, Matrix.of_apply]
  rw [← Finset.mul_sum]
  ring

/-- `T_{qa}` of the block matrix of `G` as the average of the entries of `G - M` (`M = Mres (g Ψ_I) E m`): the trivial regime of
`gueGrid_twistBA` uses the entrywise local law only. -/
theorem GUETwistBA_Tm_le_entries (g : ℝ) (E m : ℂ) (hw : (E + m).im ≠ 0) (G : Matrix (Idx d L W) (Idx d L W) ℂ) (q a : Zd d L) {b : ℝ}
    (hb : ∀ x y : Idx d L W, ‖G x y - Mres ((g : ℂ) • PsiI d L W) E m x y‖ ≤ b) :
    ‖GUETwistBA_Tm d L W (BAMB d L g E m) q a (blockMat d L W G)‖ ≤ b := by
  have hWd : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have hWr : (0 : ℝ) < (W : ℝ) ^ d := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)) d
  have h1 : GUETwistBA_Tm d L W (BAMB d L g E m) q a (blockMat d L W G) = ((W : ℂ) ^ d)⁻¹ * ∑ o : Fin (W ^ d),
      (G ((splitEquiv d L W).symm (q, o)) ((splitEquiv d L W).symm (a, o)) -
        Mres ((g : ℂ) • PsiI d L W) E m ((splitEquiv d L W).symm (q, o)) ((splitEquiv d L W).symm (a, o))) := by
    simp only [GUETwistBA_Tm, GUETwistBA_trace_Pi, blockMat, Matrix.submatrix_apply, Finset.sum_sub_distrib,
      GUETwistBA_Mres_entry g E m hw, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  rw [h1, norm_mul]
  have hs : ‖∑ o : Fin (W ^ d), (G ((splitEquiv d L W).symm (q, o)) ((splitEquiv d L W).symm (a, o)) -
      Mres ((g : ℂ) • PsiI d L W) E m ((splitEquiv d L W).symm (q, o)) ((splitEquiv d L W).symm (a, o)))‖ ≤ (W : ℝ) ^ d * b := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _o : Fin (W ^ d), b := Finset.sum_le_sum fun o _ => hb _ _
      _ = _ := by simp
  calc ‖((W : ℂ) ^ d)⁻¹‖ * ‖∑ o : Fin (W ^ d), _‖ ≤ ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d * b) := by
        gcongr
        simp
    _ = b := by field_simp

end Ident

end RBM.BA

end
