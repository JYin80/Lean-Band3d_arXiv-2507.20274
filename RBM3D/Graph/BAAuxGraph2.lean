/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Carrier
import RBM3D.Graph.LWPins
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenLDE
import RBM3D.BA.Ward
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.PerTimeCalc
import RBM3D.Induction.DecayLoopB

/-!
# The edge variables `ζ` on the block Anderson carrier `baFMz` (part 1)

Paper: (B.21) `Gyiyjatom`, (B.22) `eq:Gbyxi2_BA`, (B.25) `G_by_auxG_BA`; (7.32) `eq:Gbyxi`, (7.33)
`eq:xia1a2`, and the claim stating (7.34) `eq:Gbyxi2`.  The band counterpart is
`RBM3D/Graph/AuxGraph2.lean` (Sections 1-3); this file works on the BA carrier `baFMz sz z`
(`FlowFM`, law `seqP (sz.withLam 0)`, `BAFlow`, horizon `BAflowT0`).  The claims on `ζ` are in
`RBM3D/Graph/BAAuxGraph2B.lean`.

* Section 1: `baZetaSq`, `baZetaVar`: the block loop-window variable `ζ([a₁],[a₂])²` with the
  floor `W^{-D₁}`.  Here `ζ` is the block loop-window variable, not the atom-centre entry sum of
  (B.21), and the floor `W^{-D₁}` is the `+ W^{-D}` of (B.21).
* Section 2: `baZetaVar_nonneg`, `baZetaVar_symm`, the lattice helpers, and the Ward part
  `baZeta_ward_sum` (private Ward lemmas for both charges, any Hermitian `H`, `Im z > 0`) in block
  form: `Σ_{a₂} ζ([a₁],[a₂])² ≺ (W^d η)⁻¹` (the paper's `Σ_α ζ² ≺ η⁻¹` is on the fine lattice).
* Section 3: the `≺` helpers (stem `BAAuxGraph2_`, shared with part 2) and the deterministic
  comparisons `Φ(m) ≤ K(ρ) Φ(ℓ)`, `ζ² ≲ Φ(ℓ)² + W^{-D₁}`, the floor against `Φ²`.
* Section 4: `LWXigL`, the carrier form of `LWXi`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



noncomputable section

namespace RBM.Graph

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA
open scoped Matrix

/-! ## 1. The vocabulary of (B.21) `Gyiyjatom` -/

/-- **`ζ([a₁],[a₂])²`** ((B.21) `Gyiyjatom`, with the block loop window of (7.33) `eq:xia1a2`) on the carrier `baFMz sz z`
at the block radius `ρ n`: the `(+,-)` and `(-,+)` two-loops `𝓛^{(2)}_{t,σ,(b₁,b₂)}` over the `‖·‖_∞`-ball pairs `|b₁ - a₁|, |b₂ - a₂| ≤ ρ`
(summed over the two charges), plus `W^{-d} 1(|a₁ - a₂| ≤ ρ)`, plus the floor `W^{-D₁}` (the `+ W^{-D}` of (B.21)). -/
def baZetaSq {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℝ :=
  (∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
    ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0) +
    ((sz.W n : ℕ) : ℝ) ^ (-D₁)

/-- **The edge variable `ζ([a₁],[a₂])`**: `ζ = √(ζ²)`. -/
def baZetaVar {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℝ :=
  Real.sqrt (baZetaSq sz z t ρ D₁ n a₁ a₂ ω)

/-! ## 2. Deterministic facts -/

section Lattice

theorem BAAuxGraph2_zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

theorem BAAuxGraph2_zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

theorem BAAuxGraph2_zdistInf_tri (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    zdistInf d L (x - w) ≤ zdistInf d L (x - y) + zdistInf d L (y - w) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact BAAuxGraph2_zdistInf_add_le d L _ _

theorem BAAuxGraph2_zdistInf_sub_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, BAAuxGraph2_zdistInf_neg]

theorem BAAuxGraph2_zdistInf_tri_real (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    (zdistInf d L (x - w) : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + (zdistInf d L (y - w) : ℝ) := by
  exact_mod_cast BAAuxGraph2_zdistInf_tri d L x y w

theorem BAAuxGraph2_zdistInf_le_L (d L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L x ≤ L := by
  refine Finset.sup_le fun i _ => ?_
  unfold zdist
  exact (min_le_left _ _).trans (ZMod.val_lt _).le

end Lattice

section Basic

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ)

/-- `ζ² ≥ 0`. -/
theorem BAAuxGraph2_zetaSq_nonneg (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    0 ≤ baZetaSq sz z t ρ D₁ n a₁ a₂ ω := by
  unfold baZetaSq
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine add_nonneg (add_nonneg (Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ =>
    Finset.sum_nonneg fun σ _ => norm_nonneg _) ?_) hW
  have : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  split_ifs <;> positivity

/-- `ζ ≥ 0` (as `lwXiVar_nonneg`; the first conjunct of `LWXigL`, part 1). -/
theorem baZetaVar_nonneg (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    0 ≤ baZetaVar sz z t ρ D₁ n a₁ a₂ ω := Real.sqrt_nonneg _

theorem BAAuxGraph2_zetaVar_sq (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    baZetaVar sz z t ρ D₁ n a₁ a₂ ω ^ 2 = baZetaSq sz z t ρ D₁ n a₁ a₂ ω :=
  Real.sq_sqrt (BAAuxGraph2_zetaSq_nonneg sz z t ρ D₁ n a₁ a₂ ω)

/-- Cyclicity of the trace: the two-loop with the two entries swapped (`loopM` at length two), for any `H`, `z`. -/
theorem BAAuxGraph2_loopFine_two_swap {L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z' : ℂ)
    (σ₁ σ₂ : Bool) (a b : Zd d L) :
    loopFine d L W H z' ![σ₁, σ₂] ![a, b] = loopFine d L W H z' ![σ₂, σ₁] ![b, a] := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact Matrix.trace_mul_comm _ _

/-- The same for the loops of the carrier `baFMz`. -/
theorem BAAuxGraph2_L_two_swap (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) (t' : ℝ) :
    (baFMz sz z).L n t' ![σ₁, σ₂] ![a, b] ω = (baFMz sz z).L n t' ![σ₂, σ₁] ![b, a] ω :=
  BAAuxGraph2_loopFine_two_swap _ _ σ₁ σ₂ a b

theorem BAAuxGraph2_pair_sum (g : (Fin 2 → Bool) → ℝ) :
    ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), g σ =
      g ![true, false] + g ![false, true] := by
  rw [Finset.sum_pair]
  intro h
  have := congrFun h 0
  simp at this

/-- **`ζ([a₁],[a₂]) = ζ([a₂],[a₁])`** (as `lwXiVar_symm`; the first conjunct of `LWXigL`, part 2): reindex
`(b₁, b₂) ↦ (b₂, b₁)`; `‖𝓛_{(s,!s),(b₂,b₁)}‖ = ‖𝓛_{(!s,s),(b₁,b₂)}‖` by cyclicity of the trace. -/
theorem baZetaVar_symm (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    baZetaVar sz z t ρ D₁ n a₁ a₂ ω = baZetaVar sz z t ρ D₁ n a₂ a₁ ω := by
  unfold baZetaVar
  congr 1
  unfold baZetaSq
  congr 2
  · rw [Finset.sum_comm (s := Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n))]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
    rw [BAAuxGraph2_pair_sum, BAAuxGraph2_pair_sum,
      BAAuxGraph2_L_two_swap sz z n true false b₁ b₂ ω (t n),
      BAAuxGraph2_L_two_swap sz z n false true b₁ b₂ ω (t n)]
    ring
  · rw [BAAuxGraph2_zdistInf_sub_comm]

end Basic

/-! ### The Ward part of the claim (7.34) -/

section Ward

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem BAAuxGraph2_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

private theorem BAAuxGraph2_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) :
    Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

private theorem BAAuxGraph2_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) :
    Gres H z false = green H ((starRingEnd ℂ) z) := by
  simp only [green, Gres, Bool.false_eq_true, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

private theorem BAAuxGraph2_gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

omit [NeZero W] in
private theorem BAAuxGraph2_trace_pm_formula (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
    ((G * Eblk d L W a) * (Gᴴ * Eblk d L W b)).trace =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ v : Vtx d L W, ∑ w : Vtx d L W,
          (if v.1 = b ∧ w.1 = a then ‖G v w‖ ^ 2 else 0) : ℝ) : ℂ) := by
  have hE : ∀ c : Zd d L, Eblk d L W c = Matrix.diagonal fun x : Vtx d L W =>
      if x.1 = c then (((W : ℂ)) ^ d)⁻¹ else 0 := fun c => rfl
  rw [hE a, hE b]
  have h1 : G * Matrix.diagonal (fun x : Vtx d L W => if x.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => G i j * (if j.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal]
  have h2 : Gᴴ * Matrix.diagonal (fun x : Vtx d L W => if x.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => star (G j i) * (if j.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i.1 = b <;> by_cases hj : j.1 = a <;> simp [hi, hj]
  have h := Complex.mul_conj' (G i j)
  linear_combination (((W : ℂ) ^ d)⁻¹) ^ 2 * h

omit [NeZero W] in
private theorem BAAuxGraph2_sum_Eblk :
    ∑ a, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- The two-loop `𝓛^{(2)}_{(s,!s),(a,b)}` is a non-negative real: `W^{-2d} Σ_{v∈[b], w∈[a]} |G(s)_{vw}|²`. -/
private theorem BAAuxGraph2_loop2_real (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (s : Bool) (a b : Zd d L) :
    ∃ r : ℝ, 0 ≤ r ∧ loopFine d L W H z ![s, !s] ![a, b] = (r : ℂ) := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  refine ⟨((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ v : Vtx d L W, ∑ w : Vtx d L W,
      (if v.1 = b ∧ w.1 = a then ‖Gres (blockMat d L W H) z s v w‖ ^ 2 else 0), ?_, ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => by
      split_ifs <;> positivity)
  · unfold loopFine loopM
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    rw [← BAAuxGraph2_Gres_conjTranspose hHb z s, BAAuxGraph2_trace_pm_formula]

/-- Summing the last label of `𝓛^{(2)}_{(s,!s),(a,b)}` removes `E_b` with the factor `W^{-d}`. -/
private theorem BAAuxGraph2_loop2_rowsum (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (s : Bool) (a : Zd d L) :
    ∑ b, loopFine d L W H z ![s, !s] ![a, b] =
      (((W : ℂ) ^ d)⁻¹) * Matrix.trace (Gres (blockMat d L W H) z s * Eblk d L W a *
        Gres (blockMat d L W H) z (!s)) := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [← Matrix.trace_sum]
  have : ∀ b : Zd d L, Gres (blockMat d L W H) z s * Eblk d L W a *
      (Gres (blockMat d L W H) z (!s) * Eblk d L W b) =
      (Gres (blockMat d L W H) z s * Eblk d L W a * Gres (blockMat d L W H) z (!s)) * Eblk d L W b := by
    intro b; simp only [Matrix.mul_assoc]
  simp_rw [this]
  rw [← Finset.mul_sum, BAAuxGraph2_sum_Eblk, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- **Ward's identity for the `(s,!s)` two-loop**, both charges:
`2iη Σ_b 𝓛^{(2)}_{(s,!s),(a,b)} = W^{-d} (tr(G(+)E_a) - tr(G(-)E_a))`. -/
private theorem BAAuxGraph2_rowsum_ward (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (s : Bool) (a : Zd d L) :
    (2 * Complex.I * (z.im : ℂ)) * ∑ b, loopFine d L W H z ![s, !s] ![a, b] =
      (((W : ℂ) ^ d)⁻¹) * (Matrix.trace (Gres (blockMat d L W H) z true * Eblk d L W a) -
        Matrix.trace (Gres (blockMat d L W H) z false * Eblk d L W a)) := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hu : IsUnit (blockMat d L W H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hHb hz
  have hu' : IsUnit (blockMat d L W H - ((starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hHb (by simpa using hz)
  rw [BAAuxGraph2_loop2_rowsum, BAAuxGraph2_Gres_true, BAAuxGraph2_Gres_false]
  rw [mul_left_comm]
  congr 1
  cases s with
  | true =>
    simp only [Bool.not_true]
    rw [BAAuxGraph2_Gres_true, BAAuxGraph2_Gres_false, Matrix.trace_mul_cycle]
    have h := RBM.trace_green_sub_trace_green_conj' hu hu' (Eblk d L W a)
    rw [h]
  | false =>
    simp only [Bool.not_false]
    rw [BAAuxGraph2_Gres_true, BAAuxGraph2_Gres_false, Matrix.trace_mul_cycle]
    have h := congrArg (fun M : Matrix (Vtx d L W) (Vtx d L W) ℂ => Matrix.trace (M * Eblk d L W a))
      (RBM.green_sub_green hu hu')
    have hc : z - (starRingEnd ℂ) z = 2 * Complex.I * (z.im : ℂ) := by
      have h0 := Complex.sub_conj z
      push_cast at h0
      linear_combination h0
    simp only [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hc,
      Matrix.mul_assoc] at h
    rw [h]
    simp only [Matrix.mul_assoc]

/-- `|tr(M E_a)| ≤ max_v |M_{vv}|`: the trace against the block `E_a = W^{-d} 1_{[a]}` is an average. -/
private theorem BAAuxGraph2_norm_trace_le (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) {g : ℝ}
    (hg : ∀ v, ‖M v v‖ ≤ g) (a : Zd d L) :
    ‖Matrix.trace (M * Eblk d L W a)‖ ≤ g := by
  have hE : Eblk d L W a = Matrix.diagonal fun x : Vtx d L W =>
      if x.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0 := rfl
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  have htr : Matrix.trace (M * Eblk d L W a) =
      ∑ v : Vtx d L W, M v v * (if v.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    rw [hE]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  rw [htr]
  calc ‖∑ v : Vtx d L W, M v v * (if v.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0)‖
      ≤ ∑ v : Vtx d L W, ‖M v v * (if v.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ v : Vtx d L W, (if v.1 = a then g * ((W : ℝ) ^ d)⁻¹ else 0) := by
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : v.1 = a
        · simp only [hv, ite_true, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_right (hg v) (by positivity)
        · simp [hv]
    _ = g := by
        rw [Fintype.sum_prod_type]
        have hx : ∀ x : Zd d L, (∑ _y : Fin (W ^ d), (if x = a then g * ((W : ℝ) ^ d)⁻¹ else 0)) =
            if x = a then g else 0 := by
          intro x
          by_cases h : x = a
          · simp only [h, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            field_simp
          · simp [h]
        simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A finite sum of non-negative reals (as complex numbers) has norm the sum of the norms. -/
private theorem BAAuxGraph2_sum_norm_eq {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (h : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ f i = (r : ℂ)) : ∑ i, ‖f i‖ = ‖∑ i, f i‖ := by
  choose r hr0 hr using h
  have h1 : ∑ i, f i = ((∑ i, r i : ℝ) : ℂ) := by
    simp only [hr, Complex.ofReal_sum]
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hr0 i)]
  exact Finset.sum_congr rfl fun i _ => by rw [hr, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]

/-- **Ward's bound for the `(s,!s)` two-loop**: `Σ_b ‖𝓛^{(2)}_{(s,!s),(a,b)}‖ ≤ (W^d η)⁻¹ g` where `g ≥ |G_{yy}|`
for every `y` and `η = Im z > 0`. -/
private theorem BAAuxGraph2_rowsum_norm_le (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hη : 0 < z.im) {g : ℝ} (hg : ∀ y : Idx d L W, ‖Gres H z true y y‖ ≤ g) (s : Bool) (a : Zd d L) :
    ∑ b, ‖loopFine d L W H z ![s, !s] ![a, b]‖ ≤ (((W : ℝ) ^ d) * z.im)⁻¹ * g := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  rw [BAAuxGraph2_sum_norm_eq _ (fun b => BAAuxGraph2_loop2_real H hH z s a b)]
  have hw := BAAuxGraph2_rowsum_ward H hH z hη.ne' s a
  have hn := congrArg norm hw
  rw [norm_mul (2 * Complex.I * (z.im : ℂ)) _, norm_mul (((W : ℂ) ^ d)⁻¹) _] at hn
  have hg1 : ∀ v : Vtx d L W, ‖Gres (blockMat d L W H) z true v v‖ ≤ g := by
    intro v
    rw [BAAuxGraph2_gres_blockMat_true]
    exact hg _
  have hg2 : ∀ v : Vtx d L W, ‖Gres (blockMat d L W H) z false v v‖ ≤ g := by
    intro v
    have h := BAAuxGraph2_Gres_conjTranspose hHb z true
    simp only [Bool.not_true] at h
    rw [← h, Matrix.conjTranspose_apply, norm_star]
    exact hg1 v
  have t1 := BAAuxGraph2_norm_trace_le _ hg1 a
  have t2 := BAAuxGraph2_norm_trace_le _ hg2 a
  have h2 : ‖(2 : ℂ) * Complex.I * (z.im : ℂ)‖ = 2 * z.im := by
    simp [abs_of_pos hη]
  rw [h2] at hn
  have h3 : ‖(((W : ℂ) ^ d)⁻¹)‖ = (((W : ℝ) ^ d))⁻¹ := by simp
  rw [h3] at hn
  have h4 : ‖Matrix.trace (Gres (blockMat d L W H) z true * Eblk d L W a) -
      Matrix.trace (Gres (blockMat d L W H) z false * Eblk d L W a)‖ ≤ 2 * g :=
    (norm_sub_le _ _).trans (by linarith)
  have h5 : (2 * z.im) * ‖∑ b, loopFine d L W H z ![s, !s] ![a, b]‖ ≤ ((W : ℝ) ^ d)⁻¹ * (2 * g) := by
    rw [hn]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have hη2 : 0 < 2 * z.im := by linarith
  have h6 : ‖∑ b, loopFine d L W H z ![s, !s] ![a, b]‖ ≤
      (((W : ℝ) ^ d)⁻¹ * (2 * g)) / (2 * z.im) := by
    rw [le_div_iff₀ hη2, mul_comm]; exact h5
  refine h6.trans (le_of_eq ?_)
  have hη0 : z.im ≠ 0 := hη.ne'
  have hWd0 : ((W : ℝ) ^ d) ≠ 0 := hWd.ne'
  field_simp

end Ward

section Basic2

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ)

/-- The BA flow matrix is Hermitian. -/
theorem BAAuxGraph2_seqHflowBA_herm (lam0 : ℕ → ℝ) (u : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine Matrix.IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- **The Ward part of (B.22) `eq:Gbyxi2_BA`, block form** (as `lwXi_ward_sum`): for
`0 ≤ t ≤ T₀`, `0 ≤ ρ`, and `A` a bound of `‖(G_t - M)_{xy}‖` over all `x, y`, with `η = η_t = C.eta`,
`Σ_{a₂} ζ([a₁],[a₂])² ≤ 2 (2ρ+1)^{2d} (W^d η)⁻¹ (1 + A) + (2ρ+1)^d W^{-d} + L^d W^{-D₁}`.  Proof: two ball counts
(`DecayLoopB_card_ball`), Ward's identity for `𝓛^{(2)}_{(s,!s)} ≥ 0` (`W^{-2d} Σ |G_{vw}|²`), `|𝓛^{(1)}| ≤ |M_{yy}| + A ≤ 1 + A`
(`ba_G_data`: `‖M‖_max ≤ 1`), the floor summed over `L^d` blocks. -/
theorem baZeta_ward_sum {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (h0 : 0 ≤ t n)
    (hT : t n ≤ BAflowT0 sz z n) (hρ : 0 ≤ ρ n) (ω : sz.SeqΩ) {A : ℝ}
    (hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ A) (a₁ : Zd d (sz.L n)) :
    ∑ a₂, baZetaSq sz z t ρ D₁ n a₁ a₂ ω ≤
      2 * (2 * ρ n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (t n))⁻¹ * (1 + A)) +
        (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁) := by
  classical
  obtain ⟨ht1, -, hmi, hzi, -, hM1⟩ := ba_G_data hκ sz hflow n h0 hT
  set zt := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n) with hz
  have hηe : (baFMz sz z).eta n (t n) = zt.im := by rw [hz, ztOf_im]; rfl
  rw [hηe]
  have hHerm := BAAuxGraph2_seqHflowBA_herm sz n (BAflowLam0 sz z) (t n) ω
  have hg : ∀ y : Idx d (sz.L n) (sz.W n),
      ‖Gres (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zt true y y‖ ≤ 1 + A := by
    intro y
    have h1 := hA y y
    have h2 := hM1 y y
    have h3 : (baFMz sz z).GM n (t n) ω y y = Gres (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zt true y y -
        BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n y y := rfl
    rw [h3] at h1
    calc ‖Gres (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zt true y y‖
        = ‖(Gres (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zt true y y -
            BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n y y) +
              BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n y y‖ := by rw [sub_add_cancel]
      _ ≤ ‖Gres (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zt true y y -
            BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n y y‖ +
              ‖BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n y y‖ := norm_add_le _ _
      _ ≤ 1 + A := by linarith
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
    positivity
  -- the two charges
  set Cw : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * zt.im)⁻¹ * (1 + A) with hCw
  have hrow : ∀ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ ≤ 2 * Cw := by
    intro b₁
    simp_rw [BAAuxGraph2_pair_sum]
    rw [Finset.sum_add_distrib]
    have h1 := BAAuxGraph2_rowsum_norm_le (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) hHerm zt hzi hg true b₁
    have h2 := BAAuxGraph2_rowsum_norm_le (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) hHerm zt hzi hg false b₁
    have e1 : ∀ b₂ : Zd d (sz.L n), ‖(baFMz sz z).L n (t n) ![true, false] ![b₁, b₂] ω‖ =
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zt ![true, !true] ![b₁, b₂]‖ :=
      fun _ => rfl
    have e2 : ∀ b₂ : Zd d (sz.L n), ‖(baFMz sz z).L n (t n) ![false, true] ![b₁, b₂] ω‖ =
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zt ![false, !false] ![b₁, b₂]‖ :=
      fun _ => rfl
    simp only [e1, e2]
    linarith
  have hcard : ∀ c : Zd d (sz.L n), (((Finset.univ.filter fun b : Zd d (sz.L n) =>
      (zdistInf d (sz.L n) (b - c) : ℝ) ≤ ρ n).card : ℕ) : ℝ) ≤ (2 * ρ n + 1) ^ d := by
    intro c
    have := RBM.Ind.DecayLoopB_card_ball (L := sz.L n) c hρ
    have e : (Finset.univ.filter fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - c) : ℝ) ≤ ρ n) =
        Finset.univ.filter fun u : Zd d (sz.L n) => (zdistInf d (sz.L n) (c - u) : ℝ) ≤ ρ n := by
      refine Finset.filter_congr fun b _ => ?_
      rw [BAAuxGraph2_zdistInf_sub_comm]
    rw [e]; exact this
  have hf0 : ∀ b₁ b₂ : Zd d (sz.L n), 0 ≤ ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ := fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hρ1 : (0 : ℝ) ≤ 2 * ρ n + 1 := by linarith
  have hCw0 : 0 ≤ Cw := by
    have h1 := hg (fun _ => 0)
    have : 0 ≤ 1 + A := (norm_nonneg _).trans h1
    positivity
  unfold baZetaSq
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- first part
    rw [Finset.sum_comm]
    -- inner bound for fixed b₁
    have hin : ∀ b₁ : Zd d (sz.L n),
        ∑ a₂ : Zd d (sz.L n), ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
          ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
            ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ ≤ (2 * ρ n + 1) ^ d * (2 * Cw) := by
      intro b₁
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      calc _ ≤ ∑ b₂ : Zd d (sz.L n), (2 * ρ n + 1) ^ d *
            ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
              ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ := by
            refine Finset.sum_le_sum fun b₂ _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            have := RBM.Ind.DecayLoopB_card_ball (L := sz.L n) b₂ hρ
            exact mul_le_mul_of_nonneg_right this (hf0 b₁ b₂)
        _ = (2 * ρ n + 1) ^ d * ∑ b₂ : Zd d (sz.L n),
            ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
              ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hrow b₁) (by positivity)
    calc _ ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
          (2 * ρ n + 1) ^ d * (2 * Cw) := Finset.sum_le_sum fun b₁ _ => hin b₁
      _ = ((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n)).card : ℝ) *
            ((2 * ρ n + 1) ^ d * (2 * Cw)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ρ n + 1) ^ d * ((2 * ρ n + 1) ^ d * (2 * Cw)) :=
          mul_le_mul_of_nonneg_right (hcard a₁) (by positivity)
      _ = 2 * (2 * ρ n + 1) ^ (2 * d) * Cw := by rw [show 2 * d = d + d from two_mul d, pow_add]; ring
  · -- the indicator part
    rw [← Finset.mul_sum]
    have : ∑ a₂ : Zd d (sz.L n), (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then (1 : ℝ) else 0) =
        (((Finset.univ.filter fun u : Zd d (sz.L n) => (zdistInf d (sz.L n) (a₁ - u) : ℝ) ≤ ρ n).card : ℕ) : ℝ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [this]
    have := RBM.Ind.DecayLoopB_card_ball (L := sz.L n) a₁ hρ
    calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ρ n + 1) ^ d :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_comm _ _
  · -- the floor
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hc : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by simp [Zd, ZMod.card]
    rw [hc]
    push_cast
    exact le_rfl

end Basic2


/-! ## 3. The `≺` helpers and the deterministic comparisons -/

section PrecHelpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {size : ℕ → ℕ}

/-- A failure event of `(ξ, ζ)` that is eventually contained in the failure event of one domination
`(ξ₁, ζ₁)` (the parameter types may differ). -/
theorem BAAuxGraph2_prec_of_imp {U V : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    {ξ₁ ζ₁ : ∀ l, V l → Ω → ℝ} (h : StochDomAt P size ξ₁ ζ₁)
    (himp : ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∀ᶠ l : ℕ in atTop, ∀ (ω : Ω) (u : U l),
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω → ∃ v : V l, (size l : ℝ) ^ τ' * ζ₁ l v ω < ξ₁ l v ω) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  refine (MeasureTheory.measure_mono ?_).trans h2
  rintro ω ⟨u, hu⟩
  exact h1 ω u hu

/-- The same with the union of two failure events. -/
theorem BAAuxGraph2_prec_of_imp_union (hsize : Tendsto size atTop atTop) {U V₁ V₂ : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ₁ ζ₁ : ∀ l, V₁ l → Ω → ℝ} {ξ₂ ζ₂ : ∀ l, V₂ l → Ω → ℝ}
    (h₁ : StochDomAt P size ξ₁ ζ₁) (h₂ : StochDomAt P size ξ₂ ζ₂)
    (himp : ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∀ᶠ l : ℕ in atTop, ∀ (ω : Ω) (u : U l),
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω →
        (∃ v : V₁ l, (size l : ℝ) ^ τ' * ζ₁ l v ω < ξ₁ l v ω) ∨
        (∃ v : V₂ l, (size l : ℝ) ^ τ' * ζ₂ l v ω < ξ₂ l v ω)) :
    StochDomAt P size ξ ζ := by
  refine StochDomAt.of_subset_union hsize h₁ h₂ fun τ hτ => ?_
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  refine ⟨τ', hτ', ?_⟩
  filter_upwards [hs] with l hl
  rintro ω ⟨u, hu⟩
  rcases hl ω u hu with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨v, hv⟩
  · exact Or.inr ⟨v, hv⟩

end PrecHelpers


section SizesHelpers

variable {d : ℕ} (sz : Sizes d)

/-- `‖G_t - M‖_max ≤ W^{-ε₁/2}` holds w.h.p. under the entry law `‖G_t - M‖_max ≺ W^{-ε₁}` over the carrier `C` and the law `μ`
(`N^{τ} W^{-ε₁} ≤ W^{-ε₁/2}` at `τ = 𝔠 ε₁/2`, `W ≥ N^𝔠`; the event `Ω(t, ε₁/2)` of `lem_GbEXP_BA`); as
`auxGraph2_whp_entry` in `Graph/AuxGraph2.lean`. -/
theorem BAAuxGraph2_whp_entry (μ : Measure sz.SeqΩ) (C : FlowFM sz) (t : ℕ → ℝ) {𝔠 ε₁ : ℝ} (h𝔠 : 0 < 𝔠)
    (hε₁ : 0 < ε₁) (hband : sz.Bandwidth 𝔠)
    (hent : PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖C.GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁))) :
    HighProbAt μ sz.size (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖C.GM n (t n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2))}) := by
  have hτ : 0 < 𝔠 * ε₁ / 2 := by positivity
  refine HighProbAt.mono (StochDomAt.highProb (show StochDomAt μ sz.size _ _ from hent) hτ) ?_
  filter_upwards [hband] with n hb
  intro ω hω x y
  have h1 : ‖C.GM n (t n) ω x y‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) := hω (x, y)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) := by
    have := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₁ / 2) hτ.le
    have e : 𝔠 * ε₁ / 2 / 𝔠 = ε₁ / 2 := by field_simp
    rwa [e] at this
  calc ‖C.GM n (t n) ω x y‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) := h1
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hW.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) := by
        rw [← Real.rpow_add hW]; congr 1; ring

variable (z : ℕ → ℂ)

/-- `η_t ≤ 1` on the BA flow (`η_t = (1 - t) Im m ≤ |m| ≤ 1`, `BAm_norm_le_one`). -/
theorem BAAuxGraph2_eta_le_one {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
    (h0 : 0 ≤ t) (hT : t ≤ BAflowT0 sz z n) : (baFMz sz z).eta n t ≤ 1 := by
  obtain ⟨ht1, hr, hmi, -, -, -⟩ := ba_G_data hκ sz hflow n h0 hT
  have hm1 : ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 :=
    BAm_norm_le_one d (sz.L n) _ ((BAflowEs sz z n : ℝ) : ℂ) _ (by simp) hr.1
  have him : (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≤ 1 := (Complex.im_le_norm _).trans hm1
  show (1 - t) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≤ 1
  nlinarith

/-- `W` is eventually large: `K ≤ W^s` (`W ≥ N^𝔠`, `N → ∞`). -/
theorem BAAuxGraph2_ev_W_big {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (K : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n in atTop, K ≤ ((sz.W n : ℕ) : ℝ) ^ s := by
  obtain ⟨h𝔠, -, hsz, hbw, -⟩ := hA
  have hlim := (tendsto_rpow_atTop (show 0 < 𝔠 * s by positivity)).comp hsz
  filter_upwards [hbw, hlim.eventually_ge_atTop K, hsz.eventually_ge_atTop 1] with n hb h1 h2
  calc K ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * s) := h1
    _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ s := by rw [← Real.rpow_mul (by linarith)]
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ s := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hb hs.le

/-- **The floor of the Ward sum**: `L^d W^{-D₁} ≤ W^{-d}` for `D₁ ≥ 1/𝔠` (`N = W^d L^d ≤ W^{1/𝔠}`). -/
theorem BAAuxGraph2_floorL_le {𝔠 D₁ : ℝ} (h𝔠 : 0 < 𝔠) (n : ℕ) (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ))
    (hD : 1 / 𝔠 ≤ D₁) :
    ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 1) zero_le_one
  rw [Real.rpow_one] at hN
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  rw [hsize] at hN
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hLd : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [le_mul_inv_iff₀ hWd, mul_comm]; exact hN
  have hex : ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ 1 := by
    rw [← Real.rpow_add hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hWD : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg hW0.le _
  calc ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁)
      ≤ (((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) * ((sz.W n : ℕ) : ℝ) ^ (-D₁) :=
        mul_le_mul_of_nonneg_right hLd hWD
    _ = (((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-D₁)) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by ring
    _ ≤ 1 * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := mul_le_mul_of_nonneg_right hex (inv_nonneg.2 hWd.le)
    _ = _ := one_mul _

/-- **The floor against `Φ²`** (the floor `W^{-D₁}` of `ζ²`, from (B.21), is below `Φ(ℓ)²` for every `0 ≤ ℓ ≤ L`): from (3.28) `eq:Psi`,
`W^{-d/2} ≤ C₃ Φ(0)`: `Φ(ℓ) ≥ W^{-d/2} / (K (ℓ+1)^{C₂})`, `ℓ ≤ L ≤ W^{1/(𝔠 d)}`, so `D₁ ≥ d + 2C₂/(𝔠 d) + 1` and
`K 2^{C₂} ≤ W^{1/2}` give `W^{-D₁} ≤ Φ(ℓ)²`. -/
theorem BAAuxGraph2_floor_le (hd : 0 < d) (n : ℕ) {C₁ C₂ C₃ Cc2 𝔠 D₁ : ℝ} (Φn : ℝ → ℝ)
    (hpos : ∀ r : ℝ, 0 ≤ r → 0 < Φn r) (hC₁ : 1 < C₁) (hC₂ : 1 < C₂) (hCc : 0 < Cc2) (hC₃ : 0 < C₃)
    (h1 : ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ 2 → Φn 0 ≤ Cc2 * Φn ℓ)
    (h2 : ∀ ℓ₁ ℓ₂ : ℝ, 1 ≤ ℓ₁ → ℓ₁ ≤ ℓ₂ → Φn ℓ₁ ≤ C₁ * (ℓ₂ / ℓ₁) ^ C₂ * Φn ℓ₂)
    (hwin : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ C₃ * Φn 0)
    (h𝔠 : 0 < 𝔠) (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ))
    (hD₁ : (d : ℝ) + 2 * C₂ / (𝔠 * d) + 1 ≤ D₁)
    (hbig : C₃ * Cc2 * C₁ * 2 ^ C₂ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ))
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ ((sz.L n : ℕ) : ℝ)) :
    ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ Φn ℓ ^ 2 := by
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : 1 ≤ W := Nat.one_le_cast.2 (sz.W_pos n)
  have hW0 : 0 < W := by linarith
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set e : ℝ := C₂ / (𝔠 * d) with he
  have he0 : 0 < e := by rw [he]; have : 0 < C₂ := by linarith
                         positivity
  have h2e : 2 * C₂ / (𝔠 * d) = 2 * e := by rw [he]; ring
  have hΦℓ := hpos ℓ hℓ0
  -- step 1
  have hP1 : 1 ≤ (ℓ + 1) ^ C₂ := Real.one_le_rpow (by linarith) (by linarith)
  have hstep1 : W ^ (-(d : ℝ) / 2) ≤ C₃ * Cc2 * C₁ * (ℓ + 1) ^ C₂ * Φn ℓ := by
    by_cases hl2 : ℓ ≤ 2
    · have := h1 ℓ hℓ0 hl2
      calc W ^ (-(d : ℝ) / 2) ≤ C₃ * Φn 0 := hwin
        _ ≤ C₃ * (Cc2 * Φn ℓ) := mul_le_mul_of_nonneg_left this hC₃.le
        _ = C₃ * Cc2 * Φn ℓ := by ring
        _ ≤ C₃ * Cc2 * C₁ * (ℓ + 1) ^ C₂ * Φn ℓ := by
            refine mul_le_mul_of_nonneg_right ?_ hΦℓ.le
            have h : 1 ≤ C₁ * (ℓ + 1) ^ C₂ := by nlinarith
            nlinarith [mul_pos hC₃ hCc]
    · push Not at hl2
      have a1 := h1 1 zero_le_one (by norm_num)
      have a2 := h2 1 ℓ le_rfl (by linarith)
      rw [div_one] at a2
      have a3 : ℓ ^ C₂ ≤ (ℓ + 1) ^ C₂ := Real.rpow_le_rpow hℓ0 (by linarith) (by linarith)
      have hℓC : 0 ≤ ℓ ^ C₂ := Real.rpow_nonneg hℓ0 _
      calc W ^ (-(d : ℝ) / 2) ≤ C₃ * Φn 0 := hwin
        _ ≤ C₃ * (Cc2 * Φn 1) := mul_le_mul_of_nonneg_left a1 hC₃.le
        _ ≤ C₃ * (Cc2 * (C₁ * ℓ ^ C₂ * Φn ℓ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a2 hCc.le) hC₃.le
        _ = C₃ * Cc2 * C₁ * ℓ ^ C₂ * Φn ℓ := by ring
        _ ≤ C₃ * Cc2 * C₁ * (ℓ + 1) ^ C₂ * Φn ℓ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a3 (by positivity)) hΦℓ.le
  -- step 2: `L ≤ W^{1/(𝔠 d)}`, `(ℓ+1)^{C₂} ≤ 2^{C₂} W^e`
  have hLW : ((sz.L n : ℕ) : ℝ) ≤ W ^ (1 / (𝔠 * d)) := by
    have hN := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 1) zero_le_one
    rw [Real.rpow_one] at hN
    have hLd : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
      have : (sz.L n) ^ d ≤ sz.size n :=
        Nat.pow_le_pow_left (Nat.le_mul_of_pos_left (sz.L n) (sz.W_pos n)) d
      exact_mod_cast this
    have := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) d) (hLd.trans hN) (inv_nonneg.2 hd'.le)
    rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hd.ne', ← Real.rpow_mul hW0.le] at this
    convert this using 2
    field_simp
  have hL3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
  have hP2 : (ℓ + 1) ^ C₂ ≤ 2 ^ C₂ * W ^ e := by
    calc (ℓ + 1) ^ C₂ ≤ (2 * ((sz.L n : ℕ) : ℝ)) ^ C₂ :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ = 2 ^ C₂ * ((sz.L n : ℕ) : ℝ) ^ C₂ := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 ^ C₂ * (W ^ (1 / (𝔠 * d))) ^ C₂ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hLW (by linarith)) (by positivity)
      _ = 2 ^ C₂ * W ^ e := by
          rw [← Real.rpow_mul hW0.le, he]; congr 2; ring
  -- step 3
  have hK0 : 0 ≤ C₃ * Cc2 * C₁ := by positivity
  have hstep3 : W ^ (-(d : ℝ) / 2) * W ^ (-e) ≤ (C₃ * Cc2 * C₁ * 2 ^ C₂) * Φn ℓ := by
    have h3 : W ^ (-(d : ℝ) / 2) ≤ (C₃ * Cc2 * C₁ * 2 ^ C₂) * W ^ e * Φn ℓ :=
      hstep1.trans (by
        calc C₃ * Cc2 * C₁ * (ℓ + 1) ^ C₂ * Φn ℓ
            ≤ C₃ * Cc2 * C₁ * (2 ^ C₂ * W ^ e) * Φn ℓ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP2 hK0) hΦℓ.le
          _ = (C₃ * Cc2 * C₁ * 2 ^ C₂) * W ^ e * Φn ℓ := by ring)
    have hWe : W ^ e * W ^ (-e) = 1 := by rw [← Real.rpow_add hW0]; simp
    calc W ^ (-(d : ℝ) / 2) * W ^ (-e) ≤ ((C₃ * Cc2 * C₁ * 2 ^ C₂) * W ^ e * Φn ℓ) * W ^ (-e) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hW0.le _)
      _ = (C₃ * Cc2 * C₁ * 2 ^ C₂) * Φn ℓ * (W ^ e * W ^ (-e)) := by ring
      _ = _ := by rw [hWe, mul_one]
  -- step 4
  have hhalf : (C₃ * Cc2 * C₁ * 2 ^ C₂) * W ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have : W ^ (1 / 2 : ℝ) * W ^ (-(1 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hW0]; simp
    calc (C₃ * Cc2 * C₁ * 2 ^ C₂) * W ^ (-(1 / 2 : ℝ)) ≤ W ^ (1 / 2 : ℝ) * W ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hW0.le _)
      _ = 1 := this
  have hD2 : W ^ (-D₁ / 2) ≤ W ^ (-(d : ℝ) / 2) * W ^ (-e) * W ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hroot : W ^ (-D₁ / 2) ≤ Φn ℓ := by
    calc W ^ (-D₁ / 2) ≤ W ^ (-(d : ℝ) / 2) * W ^ (-e) * W ^ (-(1 / 2 : ℝ)) := hD2
      _ ≤ ((C₃ * Cc2 * C₁ * 2 ^ C₂) * Φn ℓ) * W ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep3 (Real.rpow_nonneg hW0.le _)
      _ = ((C₃ * Cc2 * C₁ * 2 ^ C₂) * W ^ (-(1 / 2 : ℝ))) * Φn ℓ := by ring
      _ ≤ 1 * Φn ℓ := mul_le_mul_of_nonneg_right hhalf hΦℓ.le
      _ = Φn ℓ := one_mul _
  have hsq : W ^ (-D₁) = (W ^ (-D₁ / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  rw [hsq]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hW0.le _) hroot 2

end SizesHelpers

/-- The arithmetic of the comparison `ζ² ≲ Φ²`, in powers of `u = N^{τ/8}` (as `auxGraph2_num` in `Graph/AuxGraph2.lean`, with `+ 1` for the floor,
`W^{-D₁} ≤ Φ²`, and `3 ≤ u^8`). -/
theorem BAAuxGraph2_num {u A₁ K2 S : ℝ} (hu : 1 ≤ u) (hA : 2 * A₁ ≤ u ^ 2) (hC : S ≤ u ^ 4)
    (hK : K2 ≤ u ^ 2) (h3 : 3 ≤ u ^ 8) (hA0 : 0 ≤ A₁) (hS0 : 0 ≤ S) (hK0 : 0 ≤ K2) :
    (2 * A₁ * u ^ 4 + S) * K2 + 1 ≤ (u ^ 8) ^ 2 := by
  have hu0 : 0 ≤ u := by linarith
  have h1 : 2 * A₁ * u ^ 4 ≤ u ^ 6 := by
    calc _ ≤ u ^ 2 * u ^ 4 := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = u ^ 6 := by ring
  have h2' : u ^ 4 ≤ u ^ 6 := pow_le_pow_right₀ hu (by norm_num)
  have h3' : 2 * A₁ * u ^ 4 + S ≤ 2 * u ^ 6 := by linarith
  have h4 : (2 * A₁ * u ^ 4 + S) * K2 ≤ 2 * u ^ 6 * u ^ 2 :=
    mul_le_mul h3' hK hK0 (by positivity)
  have h5 : 2 * u ^ 6 * u ^ 2 = 2 * u ^ 8 := by ring
  have h6 : 3 * u ^ 8 ≤ (u ^ 8) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h3 (pow_nonneg hu0 8)
    nlinarith
  have h7 : (1 : ℝ) ≤ u ^ 8 := by linarith
  linarith


/-- **`Φ(m) ≤ K(ρ) Φ(ℓ)` when `ℓ ≤ 2ρ + m`** ((3.28) `eq:Psi`): the split at `max(4ρ, 2)`. -/
theorem BAAuxGraph2_phi_cmp {Φ : ℝ → ℝ} {C₁ C₂ Cc2 ρ : ℝ} (hρ : 0 ≤ ρ)
    (hanti : AntitoneOn Φ (Set.Ici 0)) (hpos : ∀ r, 0 ≤ r → 0 < Φ r) (hC₁ : 1 < C₁) (hC₂ : 1 < C₂)
    (hCc : 0 < Cc2) (h1 : ∀ ℓ, 0 ≤ ℓ → ℓ ≤ 2 → Φ 0 ≤ Cc2 * Φ ℓ)
    (h2 : ∀ ℓ₁ ℓ₂, 1 ≤ ℓ₁ → ℓ₁ ≤ ℓ₂ → Φ ℓ₁ ≤ C₁ * (ℓ₂ / ℓ₁) ^ C₂ * Φ ℓ₂)
    {ℓ m : ℝ} (hℓ : 0 ≤ ℓ) (hm : 0 ≤ m) (hlm : ℓ ≤ 2 * ρ + m) :
    Φ m ≤ (C₁ * 2 ^ C₂ + Cc2 + Cc2 * C₁) * (4 * ρ + 2) ^ C₂ * Φ ℓ := by
  have hP : 1 ≤ (4 * ρ + 2) ^ C₂ := Real.one_le_rpow (by linarith) (by linarith)
  have hK : 0 < C₁ * 2 ^ C₂ + Cc2 + Cc2 * C₁ := by
    have : 0 < (2 : ℝ) ^ C₂ := by positivity
    have : 0 < C₁ * 2 ^ C₂ := by positivity
    have : 0 < Cc2 * C₁ := by positivity
    linarith
  have hΦℓ := hpos ℓ hℓ
  have hKP : ∀ x, 0 ≤ x → x ≤ C₁ * 2 ^ C₂ + Cc2 + Cc2 * C₁ →
      x ≤ (C₁ * 2 ^ C₂ + Cc2 + Cc2 * C₁) * (4 * ρ + 2) ^ C₂ := fun x hx hxK =>
    hxK.trans (le_mul_of_one_le_right hK.le hP)
  by_cases hcase : 4 * ρ ≤ ℓ ∧ 2 ≤ ℓ
  · obtain ⟨hc1, hc2⟩ := hcase
    have hm2 : ℓ / 2 ≤ m := by linarith
    have hl2 : 1 ≤ ℓ / 2 := by linarith
    have e1 : Φ m ≤ Φ (ℓ / 2) := hanti (show (0:ℝ) ≤ ℓ / 2 by linarith) hm hm2
    have e2 := h2 (ℓ / 2) ℓ hl2 (by linarith)
    have e3 : ℓ / (ℓ / 2) = 2 := by field_simp
    rw [e3] at e2
    have e4 : C₁ * 2 ^ C₂ ≤ (C₁ * 2 ^ C₂ + Cc2 + Cc2 * C₁) * (4 * ρ + 2) ^ C₂ :=
      hKP _ (by positivity) (by nlinarith [mul_pos hCc (by linarith : (0:ℝ) < C₁)])
    calc Φ m ≤ Φ (ℓ / 2) := e1
      _ ≤ C₁ * 2 ^ C₂ * Φ ℓ := e2
      _ ≤ _ := mul_le_mul_of_nonneg_right e4 hΦℓ.le
  · have e1 : Φ m ≤ Φ 0 := hanti (le_refl (0:ℝ)) hm hm
    by_cases hl2 : ℓ ≤ 2
    · have e2 := h1 ℓ hℓ hl2
      have e4 : Cc2 ≤ (C₁ * 2 ^ C₂ + Cc2 + Cc2 * C₁) * (4 * ρ + 2) ^ C₂ :=
        hKP _ hCc.le (by nlinarith [mul_pos (by linarith : (0:ℝ) < C₁) (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) C₂), mul_pos hCc (by linarith : (0:ℝ) < C₁)])
      calc Φ m ≤ Φ 0 := e1
        _ ≤ Cc2 * Φ ℓ := e2
        _ ≤ _ := mul_le_mul_of_nonneg_right e4 hΦℓ.le
    · push Not at hl2
      have hl4 : ℓ < 4 * ρ := by
        by_contra h; push Not at h; exact hcase ⟨h, hl2.le⟩
      have e2 := h1 1 zero_le_one (by norm_num)
      have e3 := h2 1 ℓ le_rfl (by linarith)
      rw [div_one] at e3
      have e5 : ℓ ^ C₂ ≤ (4 * ρ + 2) ^ C₂ := Real.rpow_le_rpow hℓ (by linarith) (by linarith)
      have hΦ1 := hpos 1 zero_le_one
      have e6 : Φ 0 ≤ Cc2 * (C₁ * (4 * ρ + 2) ^ C₂ * Φ ℓ) := by
        calc Φ 0 ≤ Cc2 * Φ 1 := e2
          _ ≤ Cc2 * (C₁ * ℓ ^ C₂ * Φ ℓ) := mul_le_mul_of_nonneg_left e3 hCc.le
          _ ≤ Cc2 * (C₁ * (4 * ρ + 2) ^ C₂ * Φ ℓ) := by
              refine mul_le_mul_of_nonneg_left ?_ hCc.le
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e5 (by linarith)) hΦℓ.le
      calc Φ m ≤ Φ 0 := e1
        _ ≤ Cc2 * (C₁ * (4 * ρ + 2) ^ C₂ * Φ ℓ) := e6
        _ = (Cc2 * C₁) * (4 * ρ + 2) ^ C₂ * Φ ℓ := by ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ hΦℓ.le
            refine mul_le_mul_of_nonneg_right ?_ (by linarith)
            nlinarith [mul_pos (by linarith : (0:ℝ) < C₁) (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) C₂)]


/-- Polynomial radii are `N^{o(1)}`: `c (aρ + b)^e ≤ N^τ` eventually. -/
theorem BAAuxGraph2_ev_poly {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {ρ : ℕ → ℝ}
    (hρ0 : ∀ n, 0 ≤ ρ n)
    (hρ : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ)
    {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, c * (a * ρ n + b) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
  set τ₂ := τ / (2 * (e + 1)) with hτ₂
  have hτ₂0 : 0 < τ₂ := by positivity
  have h1 := hρ τ₂ hτ₂0
  have h2 : ∀ᶠ n in atTop, c * (a + b) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop _
  filter_upwards [h1, h2, hsize.eventually_ge_atTop 1] with n h1 h2 hX1
  set X := ((sz.size n : ℕ) : ℝ) with hXdef
  have hX0 : 0 < X := by linarith
  have e1 : a * ρ n + b ≤ (a + b) * X ^ τ₂ := by
    calc a * ρ n + b ≤ (a + b) * (ρ n + 1) := by nlinarith [hρ0 n]
      _ ≤ (a + b) * X ^ τ₂ := mul_le_mul_of_nonneg_left h1 (by linarith)
  have e2 : (a * ρ n + b) ^ e ≤ (a + b) ^ e * X ^ (τ₂ * e) := by
    have : 0 ≤ a * ρ n + b := by have := hρ0 n; positivity
    calc (a * ρ n + b) ^ e ≤ ((a + b) * X ^ τ₂) ^ e := Real.rpow_le_rpow this e1 he
      _ = (a + b) ^ e * (X ^ τ₂) ^ e := Real.mul_rpow (by linarith) (by positivity)
      _ = (a + b) ^ e * X ^ (τ₂ * e) := by rw [← Real.rpow_mul hX0.le]
  have e3 : X ^ (τ₂ * e) ≤ X ^ (τ / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    have : τ₂ * (e + 1) = τ / 2 := by rw [hτ₂]; field_simp
    nlinarith
  calc c * (a * ρ n + b) ^ e ≤ c * ((a + b) ^ e * X ^ (τ₂ * e)) := mul_le_mul_of_nonneg_left e2 hc
    _ = (c * (a + b) ^ e) * X ^ (τ₂ * e) := by ring
    _ ≤ X ^ (τ / 2) * X ^ (τ / 2) :=
        mul_le_mul h2 e3 (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hX0.le _)
    _ = X ^ τ := by rw [← Real.rpow_add hX0]; congr 1; ring

theorem BAAuxGraph2_card_ball {d L : ℕ} [NeZero L] (c : Zd d L) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (((Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ).card : ℕ) : ℝ) ≤
      (2 * ρ + 1) ^ d := by
  have := RBM.Ind.DecayLoopB_card_ball (L := L) c hρ
  have e : (Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ) =
      Finset.univ.filter fun u : Zd d L => (zdistInf d L (c - u) : ℝ) ≤ ρ := by
    refine Finset.filter_congr fun b _ => ?_
    rw [BAAuxGraph2_zdistInf_sub_comm]
  rw [e]; exact this

/-- `N^{𝔠 ε₁/2} W^{-ε₁} ≤ W^{-ε₁/2} ≤ 1` (`W ≥ N^𝔠`): the entry law at `τ = 𝔠 ε₁/2` is `≤ W^{-ε₁/2}`. -/
theorem BAAuxGraph2_pow_small {d : ℕ} (sz : Sizes d) (n : ℕ) {𝔠 ε₁ : ℝ} (h𝔠 : 0 < 𝔠) (hε₁ : 0 < ε₁)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) :
    ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) ∧
      ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) ≤ 1 := by
  have hτ : 0 < 𝔠 * ε₁ / 2 := by positivity
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) := by
    have := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₁ / 2) hτ.le
    have e : 𝔠 * ε₁ / 2 / 𝔠 = ε₁ / 2 := by field_simp
    rwa [e] at this
  refine ⟨?_, Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)⟩
  calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁)
      ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hW.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) := by
        rw [← Real.rpow_add hW]; congr 1; ring

theorem BAAuxGraph2_rpow_nat (X : ℝ) (hX : 0 ≤ X) (x : ℝ) (k : ℕ) : (X ^ x) ^ k = X ^ (x * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]

/-- **`ξ([a₁],[a₂])² ≲ Φ(|a₁ - a₂|)²` from (3.27) `eq:LW_assm` and (3.28) `eq:Psi`** (deterministic part):
if every `‖𝓛^{(2)}_{(s,!s),(b₁,b₂)}‖ ≤ B Φ(|b₁ - b₂|)²`, `Φ(m) ≤ K Φ(ℓ)` for `ℓ ≤ 2ρ + m` and
`W^{-d} ≤ C₃² Φ(0)²`, then `ξ² ≤ (2 (2ρ+1)^{2d} B + C₃²) K² Φ(|a₁ - a₂|)²`. -/
theorem BAAuxGraph2_zetaSq_le {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (Φn : ℝ → ℝ) (hρ : 0 ≤ ρ n) {B K C₃ : ℝ} (hB : 0 ≤ B)
    (hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖(baFMz sz z).L n (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
        B * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2)
    (hΦnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ Φn r)
    (hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φn m ≤ K * Φn ℓ)
    (hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ ^ 2 * Φn 0 ^ 2) (a₁ a₂ : Zd d (sz.L n)) :
    baZetaSq sz z t ρ D₁ n a₁ a₂ ω ≤
      (2 * (2 * ρ n + 1) ^ (2 * d) * B + C₃ ^ 2) * K ^ 2 *
        Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) ^ 2 + ((sz.W n : ℕ) : ℝ) ^ (-D₁) := by
  classical
  set ℓ : ℝ := ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) with hℓ
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  set Q : ℝ := K ^ 2 * Φn ℓ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hterm : ∀ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∀ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ ≤ 2 * B * Q := by
    intro b₁ hb₁ b₂ hb₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
    set m : ℝ := ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) with hm
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have t1 := BAAuxGraph2_zdistInf_tri_real d (sz.L n) a₁ b₁ a₂
    have t2 := BAAuxGraph2_zdistInf_tri_real d (sz.L n) b₁ b₂ a₂
    have h1 : (zdistInf d (sz.L n) (a₁ - b₁) : ℝ) ≤ ρ n := by
      rw [BAAuxGraph2_zdistInf_sub_comm]; exact hb₁
    have h2 : (zdistInf d (sz.L n) (b₂ - a₂) : ℝ) ≤ ρ n := hb₂
    have hlm : ℓ ≤ 2 * ρ n + m := by
      have := BAAuxGraph2_zdistInf_tri_real d (sz.L n) a₁ b₁ a₂
      have t3 := BAAuxGraph2_zdistInf_tri_real d (sz.L n) b₁ b₂ a₂
      rw [hℓ, hm]
      linarith
    have hΦ : Φn m ≤ K * Φn ℓ := hcmp ℓ m hℓ0 hm0 hlm
    have hsq : Φn m ^ 2 ≤ Q := by
      rw [hQ, ← mul_pow]
      exact pow_le_pow_left₀ (hΦnn m hm0) hΦ 2
    rw [BAAuxGraph2_pair_sum]
    have e1 := hloop true b₁ b₂
    have e2 := hloop false b₁ b₂
    have e3 : B * Φn m ^ 2 ≤ B * Q := mul_le_mul_of_nonneg_left hsq hB
    simp only [Bool.not_true, Bool.not_false] at e1 e2
    linarith
  have hfirst : ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
        ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖ ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q := by
    calc _ ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
          ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
            2 * B * Q :=
          Finset.sum_le_sum fun b₁ hb₁ => Finset.sum_le_sum fun b₂ hb₂ => hterm b₁ hb₁ b₂ hb₂
      _ = (((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
          ((((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
            (2 * B * Q)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ρ n + 1) ^ d * ((2 * ρ n + 1) ^ d * (2 * B * Q)) := by
          have c1 := BAAuxGraph2_card_ball (d := d) a₁ hρ
          have c2 := BAAuxGraph2_card_ball (d := d) a₂ hρ
          have hBQ : 0 ≤ 2 * B * Q := by positivity
          exact mul_le_mul c1 (mul_le_mul_of_nonneg_right c2 hBQ) (by positivity) (by positivity)
      _ = 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q := by
          rw [show 2 * d = d + d from two_mul d, pow_add]; ring
  have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0) ≤ C₃ ^ 2 * Q := by
    split_ifs with hc
    · have : Φn 0 ≤ K * Φn ℓ := hcmp ℓ 0 hℓ0 le_rfl (by rw [hℓ]; linarith)
      have h0 : 0 ≤ Φn 0 := hΦnn 0 le_rfl
      have : Φn 0 ^ 2 ≤ Q := by
        rw [hQ, ← mul_pow]; exact pow_le_pow_left₀ h0 this 2
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 ≤ C₃ ^ 2 * Φn 0 ^ 2 := by rw [mul_one]; exact hW
        _ ≤ C₃ ^ 2 * Q := mul_le_mul_of_nonneg_left this (by positivity)
    · rw [mul_zero]; positivity
  unfold baZetaSq
  calc _ ≤ (2 * (2 * ρ n + 1) ^ (2 * d) * B * Q + C₃ ^ 2 * Q) + ((sz.W n : ℕ) : ℝ) ^ (-D₁) :=
        add_le_add_left (add_le_add hfirst hsecond) _
    _ = _ := by rw [hQ]; ring

/-! ## 4. The carrier form of `LWXi` -/

/-- **`LWXi` over a carrier `C` and a law `μ`** ((7.38) `eq:Gbyxi3`; `LWXi`, `Graph/LWPins.lean`, with `Prec sz` replaced by
`PrecL sz μ` and `etaT (E n) (t n)` by `C.eta n (t n)`): the edge variables
`ξ_{αβ} = ξ_{βα} ≥ 0`, `ξ_{αβ} ≺ Ψ_t(|α-β|)` and `Σ_β |ξ_{αβ}|² ≺ (W^d η_t)⁻¹`, uniformly in `α, β ∈ Z_L^d`.  Generic over the carrier: the
BA instance is `C = baFMz sz z`, `μ = seqP (sz.withLam 0)`; it is used in `Graph/BAAnpLift.lean`. -/
def LWXigL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹)

end RBM.Graph

end
