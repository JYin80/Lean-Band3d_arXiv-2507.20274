/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.GLoopFlow
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The block Anderson wrapper (MD-3)

Ticket T2013 (MD-3).  Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited
`1_2:line`) and `paper/tex/7_8_light_weight.tex` (cited `7_8:line`).  Section 5 and the block
Anderson items of section 6 of the compiled T2002 probe (`RBM3D/Probe/T2002Vocab.lean` at
`5d2a4a8` on branch `t/T2002`, never merged; lines 448-501, 656-695), copied with their docstrings
and proofs: `Ψ^{(B)}`, `Ψ` (`PsiB`, `PsiV`, `PsiI`, `(eq:Psi3D)`), the flow `Sizes.seqHflowBA`
(`H_u = λ₀ Ψ + √u V`), the matrix `Sizes.seqHBA` (`H = V + λ Ψ`, `(eq:H_blocka)`) and the pointwise
identity `Sizes.Gt_BA` (`(eq:zztE_BA)`).

The block Anderson model fits the band vocabulary of `RBM3D/Loop/GLoopFlow.lean`, with three
differences: (i) the Gaussian part is the model of `sz.withLam 0`, because `S^{(B)}(0) = I`;
(ii) the deterministic shift `H_0 = λ₀ Ψ`; (iii) the data `m`, `M` of `(self_m)`, `(def_G0)`, which
enter only through `ztOf` and `Mres`.  The deterministic layer that supplies `m₀ = m(E, λ₀)`
(`m(z, λ)`, `M^{(B)}`, `e_λ`) is separate (DECISIONS §11); `Gt_BA` takes its two scalar clauses
`λ₀ = √t₀ λ` and `z_{t₀}(E, λ₀) = √t₀ z` as hypotheses.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

/-! ## 5. Block Anderson: the same vocabulary, three differences -/

section BlockAnderson

open scoped Kronecker

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `Ψ^(B)` of `(eq:Psi3D)` (`1_2:616`): the adjacency matrix of the block lattice,
`Ψ^(B)_{ab} = 1(a ∼ b)` with `a ∼ b` the merged `Adj`. -/
def PsiB : Matrix (Zd d L) (Zd d L) ℂ := Matrix.of fun a b => if Adj d L a b then 1 else 0

/-- `Ψ = Ψ^(B) ⊗ I_{W^d}` on the block-product index (`(eq:Psi3D)`, `1_2:615`). -/
def PsiV : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  PsiB d L ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)

/-- `Ψ` on the fine lattice (`(eq:Psi3D)`, `1_2:615`), through the bridge `splitEquiv`. -/
def PsiI : Matrix (Idx d L W) (Idx d L W) ℂ :=
  (PsiV d L W).submatrix (splitEquiv d L W) (splitEquiv d L W)

theorem PsiB_isHermitian : (PsiB d L).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, PsiB, Matrix.of_apply]
  have hadj : Adj d L b a ↔ Adj d L a b := by
    simp only [Adj]
    rw [show b - a = -(a - b) by ring, zdistD_neg]
  by_cases h : Adj d L a b
  · simp [h, hadj.mpr h]
  · simp [h, mt hadj.mp h]

theorem PsiI_isHermitian : (PsiI d L W).IsHermitian := by
  have h : (PsiV d L W).IsHermitian := by
    unfold PsiV IsHermitian
    rw [conjTranspose_kronecker, (PsiB_isHermitian d L).eq, conjTranspose_one]
  exact h.submatrix _

end BlockAnderson

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **The block Anderson flow at one time** (`(MBM)`, `1_2:686`, with `H_0 = ilambda_0 Ψ`;
`lam0` is the flow coupling, `ilambda_0 = √t0 · ilambda` in `(eq:t0E0_BA)`, `7_8:1798`): the
Gaussian part is the model of `sz.withLam 0`, because `S^(B)(0) = I` (`bandcwV`, `1_2:606`).
So the block Anderson model *fits the band vocabulary*: it differs by (i) the coupling
`0` in the law, (ii) the deterministic shift `H_0`, (iii) the deterministic data `m`, `M`
(`self_m`, `def_G0`), which enter only through `ztOf` and the matrix `M`, see section 6. -/
def seqHflowBA (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) +
    Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => seqHflow (sz.withLam 0) n u ω i j

end Sizes

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **`H` of the block Anderson model** (`(eq:H_blocka)`, `1_2:611`): `H = V + ilambda Ψ`, with `V`
the Gaussian potential of `sz.withLam 0` (`(bandcwV)`). -/
def seqHBA (n : ℕ) (ω : SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n) +
    Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => seqXmat (sz.withLam 0) n ω i j

theorem seqHBA_isHermitian (n : ℕ) (ω : SeqΩ sz) : (seqHBA sz n ω).IsHermitian := by
  unfold seqHBA
  refine IsHermitian.add ?_ (seqXmat_isHermitian (sz.withLam 0) n ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (sz.lam n : ℂ) = (sz.lam n : ℂ) from Complex.conj_ofReal _]

/-- **`zztE_BA`, third clause, pointwise** (`(eq:zztE_BA)`, `7_8:1801`): for the block Anderson
flow `H_u = lam0·Ψ + √u V` the identity `G(z, λ) = √t₀ G_{t₀;E,λ₀}` holds pointwise, given the two
deterministic clauses `λ₀ = √t₀ λ` and `z_{t₀}(E, λ₀) = √t₀ z` of `(eq:t0E0_BA)`, `(eq:zztE_BA)`
(data of the deterministic layer: `m0 = m(E, λ₀)`). -/
theorem Gt_BA (lam0 : ℕ → ℝ) (n : ℕ) {z m0 : ℂ} {E t0 : ℝ} (hz : 0 < z.im) (ht0 : 0 < t0)
    (hlam0 : lam0 n = Real.sqrt t0 * sz.lam n)
    (hzt : ztOf m0 E t0 = (Real.sqrt t0 : ℂ) * z) (ω : SeqΩ sz) :
    (Real.sqrt t0 : ℂ) • Gres (seqHflowBA sz lam0 n t0 ω) (ztOf m0 E t0) true =
      Gres (seqHBA sz n ω) z true := by
  have hr0 : (Real.sqrt t0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 ht0).ne'
  have hA : IsUnit (seqHBA sz n ω - z • (1 : Matrix _ _ ℂ)) :=
    isUnit_sub_smul_of_isHermitian (seqHBA_isHermitian sz n ω) hz.ne'
  have hHt : seqHflowBA sz lam0 n t0 ω - ztOf m0 E t0 • (1 : Matrix _ _ ℂ) =
      (Real.sqrt t0 : ℂ) • (seqHBA sz n ω - z • (1 : Matrix _ _ ℂ)) := by
    have hBA : seqHflowBA sz lam0 n t0 ω = (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) +
        (Real.sqrt t0 : ℂ) • (Matrix.of fun i j : Idx d (sz.L n) (sz.W n) =>
          seqXmat (sz.withLam 0) n ω i j) := rfl
    rw [hzt, hBA, seqHBA, hlam0]
    simp only [smul_sub, smul_add, ← mul_smul, Complex.ofReal_mul]
  unfold Gres
  simp only [↓reduceIte]
  rw [hHt, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
  have : Invertible (Real.sqrt t0 : ℂ) := invertibleOfNonzero hr0
  rw [Matrix.inv_smul (A := seqHBA sz n ω - z • (1 : Matrix _ _ ℂ)) (Real.sqrt t0 : ℂ)
    ((Matrix.isUnit_iff_isUnit_det _).mp hA), smul_smul, invOf_eq_inv,
    mul_inv_cancel₀ hr0, one_smul]

end Sizes

end RBM.Gauss

/-! ## Compiled nonempty instances at the preflight sequence

`d = 3`, `SizesInst.sz0` at `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`) and the target
`GLoopFlowInst.z0 = 1/2 + i N^{-4/5}`.  `Gt_BA_sz0` is the probe's section 9 instance
(`Gt_BA_sz0`, lines 1382-1393), with the two scalar clauses discharged instead of kept as
hypotheses; the envelope instances are new.

The clauses `λ₀ = √t₀ λ` and `z_{t₀}(E, λ₀) = √t₀ z` of `(eq:t0E0_BA)`, `(eq:zztE_BA)` are
identities between numbers, and are met by the data `t₀ = 1/4`, `E = 1/4`, `λ₀ = λ/2`,
`m₀ = i (2/3) Im z0` (so `Im m₀ > 0`).  These are not the values of the deterministic layer
(`m₀ = m(E, λ₀)` solves `(self_m)`); for those values the preflight (section (a), instance B)
checks both clauses numerically at `sz0` and `z0`, with `t₀ ∈ (0, 1)`. -/

namespace RBM.Gauss.BlockAndersonInst

open SizesInst GLoopFlowInst

/-- `Ψ^{(B)}` at `d = 3`, `L = 4` is a nonzero adjacency matrix: `0` and `e₁` are neighbours of
`Z_4^3`, `0` is not its own neighbour, and `Ψ^{(B)}`, `Ψ` (block product and fine lattice) are
Hermitian. -/
example : PsiB 3 4 0 ![1, 0, 0] = 1 ∧ PsiB 3 4 0 0 = 0 ∧ (PsiB 3 4).IsHermitian ∧
    (PsiV 3 4 32).IsHermitian ∧ (PsiI 3 4 32).IsHermitian := by
  refine ⟨?_, ?_, PsiB_isHermitian 3 4, ?_, PsiI_isHermitian 3 4 32⟩
  · have h : Adj 3 4 0 ![1, 0, 0] := by unfold Adj; decide
    simp [PsiB, h]
  · have h : ¬ Adj 3 4 0 0 := by unfold Adj; decide
    simp [PsiB, h]
  · unfold PsiV Matrix.IsHermitian
    rw [Matrix.conjTranspose_kronecker, (PsiB_isHermitian 3 4).eq, Matrix.conjTranspose_one]

/-- The flow data of the block Anderson instance: `t₀ = 1/4`. -/
def t0 : ℝ := 1 / 4

/-- `E = 1/4` (the energy of `G_{t₀;E,λ₀}`). -/
def E0 : ℝ := 1 / 4

/-- The flow coupling `λ₀ = √t₀ λ = λ/2`. -/
def lam0 : ℕ → ℝ := fun n => (1 / 2) * sz0.lam n

/-- The datum `m₀` with `z_{t₀}(E, λ₀) = E + (1 - t₀) m₀ = √t₀ z0`: purely imaginary, with
`Im m₀ = (2/3) Im z0`. -/
def m0 : ℂ := ⟨0, (2 / 3) * z0.im⟩

theorem sqrt_t0 : Real.sqrt t0 = 1 / 2 := by
  rw [t0, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem t0_pos : 0 < t0 := by norm_num [t0]

/-- `Im m₀ > 0`. -/
theorem m0_im_pos : 0 < m0.im := by
  have h := z0_im_pos
  change 0 < (2 / 3) * z0.im
  positivity

theorem hlam0 : lam0 0 = Real.sqrt t0 * sz0.lam 0 := by
  rw [sqrt_t0]
  rfl

theorem hzt0 : ztOf m0 E0 t0 = (Real.sqrt t0 : ℂ) * z0 := by
  rw [sqrt_t0]
  have hre : z0.re = 1 / 2 := rfl
  apply Complex.ext
  · simp [ztOf, m0, E0, t0, hre]
    norm_num
  · simp [ztOf, m0, E0, t0]
    ring

/-- **`Gt_BA` at the instance**: `G(z0, λ) = √t₀ G_{t₀;E,λ₀}` pointwise in `ω`, every hypothesis of
`Gt_BA` discharged (`0 < Im z0`, `0 < t₀`, `λ₀ = √t₀ λ`, `z_{t₀}(E, λ₀) = √t₀ z0`). -/
theorem Gt_BA_sz0 (ω : Sizes.SeqΩ sz0) :
    (Real.sqrt t0 : ℂ) • Gres (sz0.seqHflowBA lam0 0 t0 ω) (ztOf m0 E0 t0) true =
      Gres (sz0.seqHBA 0 ω) z0 true :=
  Sizes.Gt_BA sz0 lam0 0 z0_im_pos t0_pos hlam0 hzt0 ω

/-- At `t = 0` the block Anderson flow is `H_0 = λ₀ Ψ`, not `0` (the first difference with the band
model, where `H_0 = 0`; `Lloop_zero_one`). -/
example (ω : Sizes.SeqΩ sz0) :
    sz0.seqHflowBA lam0 0 0 ω = (lam0 0 : ℂ) • PsiI 3 (sz0.L 0) (sz0.W 0) := by
  ext i j
  have h : (sz0.withLam 0).seqHflow 0 0 ω i j = 0 := by
    have h0 : (sz0.withLam 0).seqHflow 0 0 ω = 0 := by simp [Sizes.seqHflow]
    rw [h0]
    rfl
  simp [Sizes.seqHflowBA, h]

/-- `H = V + λ Ψ` is Hermitian at the instance (`seqHBA_isHermitian`). -/
example (ω : Sizes.SeqΩ sz0) : (sz0.seqHBA 0 ω).IsHermitian := Sizes.seqHBA_isHermitian sz0 0 ω

/-- **The envelope for the block Anderson matrix, at the instance**: `H = λ Ψ + V` read on the
block-product index, at the target `z0`; every `2`-loop is bounded by `(Im z0)⁻²`
(`GLoopFlow.norm_loopM_le`, Hermitian is the only hypothesis). -/
theorem norm_loop_BA_sz0 (ω : Sizes.SeqΩ sz0) :
    ‖loopM 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (sz0.seqHBA 0 ω)) z0
        ![true, false] ![0, 0]‖ ≤ (z0.im)⁻¹ ^ 2 :=
  norm_loopM_le 3 (sz0.L 0) (sz0.W 0) ((Sizes.seqHBA_isHermitian sz0 0 ω).submatrix _)
    z0_im_pos (le_abs_self _) _ _

/-- **The sharp envelope for the block Anderson matrix, at the instance**
(`GLoopFlow.norm_loopM_le_sharp`): the `2`-loop of `H = λ Ψ + V` at `z0` is bounded by
`(Im z0)⁻² W^{-3}`. -/
theorem norm_loop_BA_sharp_sz0 (ω : Sizes.SeqΩ sz0) :
    ‖loopM 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (sz0.seqHBA 0 ω)) z0
        ![true, false] ![0, 0]‖ ≤ (z0.im)⁻¹ ^ 2 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ^ 1 :=
  norm_loopM_le_sharp 3 (sz0.L 0) (sz0.W 0) ((Sizes.seqHBA_isHermitian sz0 0 ω).submatrix _)
    z0_im_pos (le_abs_self _) _ _

end RBM.Gauss.BlockAndersonInst
