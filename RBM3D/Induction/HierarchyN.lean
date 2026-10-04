/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.HierAlgebra

/-!
# The general-`n` `(𝓛 - 𝒦)` hierarchy identity (ST2-28a, ticket T2095)

Port of RBM2D `Induction/HierarchyN.lean` at commit `c9a24cf` (`HN:<line>`; 76 lines there) and of
the pins `HierarchyN`, `LoopGenN` of `Induction/HierVocab.lean` (`HierVocab:206`, `:548`), in the
shape of the merged `n = 2` forms `HierarchyN2`, `LoopGenN2` (`Path/DriftAlgebra.lean`, D149):
`∀ sz n` at `g = sz.lam n`, merged `ST*` vocabulary.

* `STLoopGenNForm d` : the general-`n` loop-generator identity `genMat(𝓛_I) = pair + 𝓔^{G̃}`
  (`eq:mainStoflow`, `1_2`, drift part; RBM2D `LoopGenN`).  Not proved here (ST2-28 proves it): it
  is the explicit hypothesis of `hierarchyN_of_loopGenN` (ticket Amend 1, DECISIONS §32).
* `HierarchyN d` : the drift part of (`LK_SDE`, `3_5:133`):
  `genMat(𝓛) - ∂_u 𝒦 = Θ^{(k)}_{u,σ}(𝓛-𝒦) + Σ_{l=3}^k [𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)} + 𝓔^{LK×LK} + 𝓔^{G̃}`,
  the shape of `STgDriftN` at `H = M` plus `genMat`.
* `hierarchyN_of_loopGenN` : `STLoopGenNForm d → HierarchyN d`, from `loopDrift_sub_K_deriv_n`
  (RBM2D `hierarchyN`, `HN:31-34`, rewrote by the merged `loopGenN`).
* the reductions at `n = 2`, `σ = (+,-)`: `HierarchyN d → HierarchyN2 d` and `LoopGenN2 d` implies
  `STLoopGenNForm d` at length `2`, `σ = (+,-)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **The general-`n` loop generator (`eq:mainStoflow`, `1_2`, drift part), the shape of
`LoopGenN2`**: for Hermitian `M` and every loop `(σ, a)` of length `k ≥ 2`,
`genMat(𝓛_{σ,a}) = W^d Σ_{k<l} Σ_{a,b} 𝓛 S^{(B)} 𝓛 + 𝓔^{(G̃)}` (`STllPairN`, `STegtM`).
RBM2D `LoopGenN` (`HierVocab:548`) with `W² → W^d`, `g = sz.lam n`.  **Owed** (ST2-28, DECISIONS
§32); at `k = 2`, `σ = (+,-)` it is implied by `LoopGenN2` (`loopGenNForm_two_of_loopGenN2`). -/
def STLoopGenNForm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) =
          sz.STllPairN n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)

/-- **The general-`n` hierarchy identity `HierarchyN`** (`LK_SDE`, `3_5:133`, drift part;
`eq_L-Keee`, `3_5:73`; `DefKsimLK` `3_5:89`, `def_ELKLK` `3_5:97`, `DefTHUST` `3_5:109`): for
Hermitian `M` and every loop `(σ, a)` of length `k ≥ 2`,
`genMat(𝓛) - ∂_u 𝒦 = Θ^{(k)}_{u,σ}∘(𝓛-𝒦) (a) + Σ_{l=3}^k [𝒦^{(l)}∼(𝓛-𝒦)]^{(k)} + 𝓔^{LK×LK} + 𝓔^{G̃}`.
The shape of `HierarchyN2` (`∀ sz n`, `g = sz.lam n`, merged `ST*` vocabulary); the right side is
`STgDriftN` of `Step2Defs` at `H = M`.  At `k = 2`, `σ = (+,-)` it is `HierarchyN2`
(`hierarchyN_two`). -/
def HierarchyN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) -
            deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
          ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
              (fun b => sz.STLKIM n E u M (loopOf σ b)) a +
            ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a) +
            sz.STelklkM n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)

/-- **`hierarchyN`** (RBM2D `HN:31`): the general-`n` hierarchy identity from the general-`n`
loop generator (`STLoopGenNForm`) and the matrix-level identity `loopDrift_sub_K_deriv_n`. -/
theorem hierarchyN_of_loopGenN (d : ℕ) : STLoopGenNForm d → HierarchyN d := by
  intro h sz n E hE u hu0 hu1 M hM k hk σ a
  rw [h sz n E hE u hu0 hu1 M hM k hk σ a]
  exact loopDrift_sub_K_deriv_n sz n E hE u hu0 hu1 M hk σ a

/-! ## The reductions at `n = 2`, `σ = (+,-)` -/

section Two

variable {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
  (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- `𝓛_{I}` of a list index `loopOf σ a` is `STLM` (`loopM_eq_loopL`). -/
private theorem HierarchyN_STLIM_loopOf {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    sz.STLIM n E u H (loopOf σ a) = sz.STLM n E u H σ a :=
  (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a).symm

private theorem HierarchyN_STLKIM_loopOf {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    sz.STLKIM n E u H (loopOf σ a) = sz.STLKM n E u H σ a := by
  unfold STLKIM STLKM
  rw [HierarchyN_STLIM_loopOf sz n E u H σ a]
  rfl

private theorem HierarchyN_ThetaN_two (σ : Fin 2 → Bool)
    (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u A a = sz.STthetaOp n E u σ A a := by
  unfold ThetaN STthetaOp
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  have hμ : cycProd (fun i => mSigma E (σ i)) i = STmsig E (σ 0) * STmsig E (σ 1) := by
    fin_cases i
    · rfl
    · exact mul_comm _ _
  simp only [thetaKer, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, hμ]

private theorem HierarchyN_length_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    (loopOf σ a).length = 2 := by
  change (List.ofFn a).length = 2
  simp

private theorem HierarchyN_STelklkM_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STelklkM n E u H (loopOf σ a) = sz.STELKLKM n E u H σ a := by
  unfold STelklkM STELKLKM
  rw [HierarchyN_length_two sz n σ a]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  have h2 : (Finset.Ioc 1 2 : Finset ℕ) = {2} := by decide
  have h3 : (Finset.Ioc 2 2 : Finset ℕ) = ∅ := by decide
  rw [h1, Finset.sum_pair (by decide), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  congr 1

private theorem HierarchyN_STegtM_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STegtM n E u H (loopOf σ a) = sz.STEGtM n E u H σ a := by
  unfold STegtM STEGtM
  rw [HierarchyN_length_two sz n σ a]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  rw [h1, Finset.sum_pair (by decide)]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rfl

private theorem HierarchyN_SB_symm (x y : Zd d (sz.L n)) :
    SB d (sz.L n) (sz.lam n) x y = SB d (sz.L n) (sz.lam n) y x :=
  congrFun (congrFun (SB_transpose d (sz.L n) (sz.lam n)) y) x

private theorem HierarchyN_STllPairN_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STllPairN n E u H (loopOf σ a)
      = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
          sz.STLM n E u H σ ![a 0, b₁] * SB d (sz.L n) (sz.lam n) b₁ b₂ *
            sz.STLM n E u H σ ![b₂, a 1] := by
  unfold STllPairN
  rw [HierarchyN_length_two sz n σ a]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  have h2 : (Finset.Ioc 1 2 : Finset ℕ) = {2} := by decide
  have h3 : (Finset.Ioc 2 2 : Finset ℕ) = ∅ := by decide
  rw [h1, Finset.sum_pair (by decide), h2, h3]
  simp only [Finset.sum_singleton, Finset.sum_empty, add_zero]
  refine congrArg ((((sz.W n : ℕ) : ℂ) ^ d) * ·) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  have hL : (loopOf σ a).cutGlueL 1 2 b₂ = loopOf σ ![b₂, a 1] := rfl
  have hR : (loopOf σ a).cutGlueR 1 2 b₁ = loopOf σ ![a 0, b₁] := rfl
  rw [hL, hR, HierarchyN_STLIM_loopOf, HierarchyN_STLIM_loopOf, HierarchyN_SB_symm sz n b₂ b₁]
  ring

end Two

/-- **`HierarchyN` at `n = 2`, `σ = (+,-)` is `HierarchyN2`**: the general-`n` identity implies the
merged pin (`Path/DriftAlgebra.lean`, `STthetaOp`, `STELKLKM`, `STEGtM`; `Σ_{l ∈ Icc 3 2}` is empty). -/
theorem hierarchyN_two (d : ℕ) : HierarchyN d → HierarchyN2 d := by
  intro h sz n E hE u hu0 hu1 M hM a₁ a₂
  have h2 := h sz n E hE u hu0 hu1 M hM 2 le_rfl ![true, false] ![a₁, a₂]
  have hfun : (fun b : Fin 2 → Zd d (sz.L n) => sz.STLKIM n E u M (loopOf ![true, false] b))
      = sz.STLKM n E u M ![true, false] :=
    funext fun b => HierarchyN_STLKIM_loopOf sz n E u M ![true, false] b
  rw [HierarchyN_ThetaN_two, hfun, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, add_zero,
    HierarchyN_STelklkM_two, HierarchyN_STegtM_two] at h2
  exact h2

/-- **`LoopGenN2` implies the body of `STLoopGenNForm` at `k = 2`, `σ = (+,-)`**: the general-`n`
loop-generator form is the right one (`STllPairN` at length `2` is the first term of `LoopGenN2`,
`STegtM` at length `2` is `STEGtM`). -/
theorem loopGenNForm_two_of_loopGenN2 (d : ℕ) (h : LoopGenN2 d) (sz : Sizes d) (n : ℕ) (E : ℝ)
    (hE : |E| < 2) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (a₁ a₂ : Zd d (sz.L n)) :
    genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf ![true, false] ![a₁, a₂]) =
      sz.STllPairN n E u M (loopOf ![true, false] ![a₁, a₂]) +
        sz.STegtM n E u M (loopOf ![true, false] ![a₁, a₂]) := by
  rw [HierarchyN_STllPairN_two, HierarchyN_STegtM_two]
  exact h sz n E hE u hu0 hu1 M hM a₁ a₂

/-! ## Compiled nonempty instances

At the merged admissible sequence `sz0` (`RBM.Gauss.SizesInst.sz0`: `d = 3`, `L_0 = 4`, `W_0 = 32`,
`lam_0 = 1/64`), size index `0`, `E = 0` (`|E| < 2`), `u = 1/2` (`0 ≤ u < 1`), `M = 1` (Hermitian).
`hierarchyN_of_loopGenN` is applied at the loop `(+,-,+)`, `a = (0,1,2)` of length `k = 3`; the only
hypothesis kept is the owed pin `STLoopGenNForm 3` (ST2-28).  `hierarchyN_two` is applied at
`n = 2` with `HierarchyN 3` kept as the hypothesis.  `loopGenNForm_two_of_loopGenN2` is applied
unconditionally (`loopGenN2 3` is proved in `Path/DriftAlgebra.lean`). -/

section Instances

open RBM.Gauss.SizesInst

/-- **`hierarchyN_of_loopGenN` at `sz0`**, `k = 3`, `σ = (+,-,+)`, `a = (0,1,2)`: the general-`n`
identity, with the generator identity `STLoopGenNForm 3` (owed, ST2-28) as the only hypothesis. -/
theorem HierarchyN_check_sz0 (h : STLoopGenNForm 3) :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]) -
        deriv (fun v : ℝ => sz0.STKloop 0 0 v ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2])
          (1 / 2) =
      ThetaN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma 0 (![true, false, true] i)) (1 / 2)
            (fun b => sz0.STLKIM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
              (loopOf ![true, false, true] b)) ![(0 : Zd 3 (sz0.L 0)), 1, 2]
        + ∑ l ∈ Finset.Icc 3 3, sz0.STksimLKM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) l
            (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2])
        + sz0.STelklkM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
            (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2])
        + sz0.STegtM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
            (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]) :=
  hierarchyN_of_loopGenN 3 h sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) _ _

/-- **`hierarchyN_two` at `sz0`**: from `HierarchyN 3` the merged `n = 2` identity at `M = 1`,
`a = (0,1)`. -/
theorem HierarchyN_check_two_sz0 (h : HierarchyN 3) :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        ⟨[true, false], [(0 : Zd 3 (sz0.L 0)), 1]⟩ -
        deriv (fun v : ℝ => sz0.STKloop 0 0 v ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1]) (1 / 2) =
      sz0.STthetaOp 0 0 (1 / 2) ![true, false]
          (sz0.STLKM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ![true, false]) ![(0 : Zd 3 (sz0.L 0)), 1] +
        sz0.STELKLKM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1] +
        sz0.STEGtM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1] :=
  hierarchyN_two 3 h sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 0 1

/-- **`loopGenNForm_two_of_loopGenN2` at `sz0`**, unconditional (`loopGenN2 3`): the general-`n`
generator identity at length `2`, `σ = (+,-)`, `M = 1`, `a = (0,1)`. -/
theorem HierarchyN_check_loopGenNForm_two_sz0 :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        (loopOf ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1]) =
      sz0.STllPairN 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          (loopOf ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1]) +
        sz0.STegtM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          (loopOf ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1]) :=
  loopGenNForm_two_of_loopGenN2 3 (loopGenN2 3) sz0 0 0 (by norm_num) (1 / 2) (by norm_num)
    (by norm_num) 1 Matrix.isHermitian_one 0 1

/-- The three `Prop`s at `d = 3`: the conditional general-`n` identity and the `n = 2` reduction. -/
example : (STLoopGenNForm 3 → HierarchyN 3) ∧ (HierarchyN 3 → HierarchyN2 3) :=
  ⟨hierarchyN_of_loopGenN 3, hierarchyN_two 3⟩

end Instances

end RBM.Ind

end

#print axioms RBM.Ind.hierarchyN_of_loopGenN
#print axioms RBM.Ind.hierarchyN_two
#print axioms RBM.Ind.loopGenNForm_two_of_loopGenN2
