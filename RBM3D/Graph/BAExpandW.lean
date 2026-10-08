/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExpand
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# BA-L2b1: the weight expansion `lem_lweight` and `lanlw` as a graph operation (T2303)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:359-387` (cited `B:line`; `lanlw` =
`(eq:BE)`, [yang2024Del, Lemma B.9]; `lem_lweight` = `(eq:LW)`, [yang2024Del, Lemma B.10]).  The
law is the block Anderson flow `H_t = g₀ Ψ + √t V` with `S^{(B)}(0) = I`, i.e. `PF d L W 0`
(DECISIONS §57 (3)).  Design: T2161 (split P.9, row BA-L2); BA-L2b is cut in two by DECISIONS
§129 (1): this file is BA-L2b1.

## Contents (namespace `RBM.Graph`, private prefix `BAExpandW_`)

1. **The pin and the vocabulary**, copied verbatim from `docs/tickets/checks/T2303-check.lean`
   sections 2 and 3: `BAlweightL`, `BAlweightR`, `BAlweight`; `BAlwData`, `BAGraph.lanlwExt`,
   `BAGraph.lanlwT1`, `BAGraph.lanlwD`, `BAGraph.lanlwTerms`.
2. **Target 1** (the weight expansion): `baM_symm`, `baM_row_sq` (the fine Ward row
   `Σ_α |M_{xα}|² = 1`), `baW_isUnit` (Gershgorin for the non-diagonal `M^+S`), `baW_mul`
   (`W (1 - M^+S) = 1`), and **`baLweight_holds : ∀ d, BAlweight d`**, unconditionally (`gaussIBP`
   discharged): `lanlw` at `(y, y)` (`baLanlw_holds`) gives the linear system `v = (M^+S) v + r` for
   `v_y = 𝔼 Ǧ_{yy} f`, solved by `W = (1 - M^+S)⁻¹`.
3. **Target 3(b)**: `lanlw_val`, the identity of expectations of values
   `𝔼 Γ.val = 𝔼 Σ_{Δ ∈ lanlwTerms Γ p} Δ.val` at the model data `BAlwData`, from `BAExpand_integral`
   at every labelling on `Sizes.seqP` (`BAExpandW_lanlw_val_seq`, the BA twin of `owx_graph_E`),
   transported to `PF d L W 0` by `lwWx_integral`.
4. Compiled instances (`RBM.Graph.BAExpandWInst`): (I5) `baLweight_holds` at `t = 0` and at a
   point with every hypothesis discharged, (I6) `baW_isUnit` and the Ward row at `d = 3`, `L = 3`,
   `W = 1`, `g₀ = 0`, `E = 0`, `m = i`, `t = 1/2`; `lanlw_val` on `baGcxy` and `baGcxx`.

Not in this file: the raw counters and the `scalingOrderG` claim of the terms of `lanlw` (target
3(c), instances (I3), (I4)) are T2315 (`Graph/BAExpandWOrd`); the `lem_lweight` graph operation
(DECISIONS §129 (2)).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green

/-! ## 1. The pin and the vocabulary (copied verbatim from the check file, sections 2 and 3) -/

section LWBAPinsW

variable (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ)
  (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)

/-- Left side of `lem_lweight`: `Ǧ_{xx} f` (`B:376-387`, [yang2024Del, Lemma B.10]). -/
noncomputable def BAlweightL (x : Idx d L W) (ω : Ω d L W) : ℂ :=
  BAlwGc d L W g0 E t m ω x x * BAlwf d L W g0 E t m P ω

/-- Right side of `lem_lweight` before `𝔼`: `Σ_y (1 + M^+S^+)_{xy} (Σ_{α,β} M_{yα} S_{αβ} Ǧ_{αy} Ǧ_{ββ} f -
Σ_{α,β} M_{yα} S_{αβ} G_{βy} ∂_{h_{βα}} f)`, with `1 + M^+S^+ = (1 - M^+S)⁻¹ = BAlwW` (`B:380-385`). -/
noncomputable def BAlweightR (x : Idx d L W) (ω : Ω d L W) : ℂ :=
  ∑ y, BAlwW d L W g0 E t m x y *
    (∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω α y *
        BAlwGc d L W g0 E t m ω β β * BAlwf d L W g0 E t m P ω -
      ∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwG d L W g0 E t m ω β y *
        BAlwdf d L W g0 E t m P ω β α)

variable {d L W g0 E t m P}

/-- **`lem_lweight`** (`B:376-387`, [yang2024Del, Lemma B.10]): `𝔼[BAlweightL] = 𝔼[BAlweightR]` for every resolvent
polynomial `f` over the BA law `PF d L W 0`.  Needs `(self_m)` (through `lanlw`) and `IsUnit (1 - M^+S)` (from
`BASelf`, `t < 1`: the rows of `M^+S` have absolute sum `≤ t`).  Registry: proved (T2303). -/
def BAlweight (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W),
      ∫ ω, BAlweightL d L W g0 E t m P x ω ∂(PF d L W 0) = ∫ ω, BAlweightR d L W g0 E t m P x ω ∂(PF d L W 0)

end LWBAPinsW

/-! ## 3. `lanlw` as a graph operation: vocabulary (copied verbatim) -/

section ModelData

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The graph data of the BA flow at the sample `ω` (T2287 Consumers): `G` the flow resolvent, `M = BAlwM`,
`S = t·svarF d L W 0`, `S⁺ = S (1 - M^+S)⁻¹`, `gPsi = g₀ Ψ`. -/
noncomputable def BAlwData (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) : BALData (Idx d L W) where
  G := Matrix.of fun x y => BAlwG d L W g0 E t m ω x y
  M := BAlwM d L W g0 E m
  S := Matrix.of (BAlwS d L W t)
  Sp := Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m
  gPsi := (g0 : ℂ) • PsiI d L W

end ModelData

section LanlwGraph

variable {E I : Type}

/-- `Γ` on the vertices `E ⊕ (I ⊕ Fin 2)` (old vertices by `owxEmb 2`, `α = inr (inr 0)`, `β = inr (inr 1)`) with
its solid edges replaced by `rest`, the solid edges `s`, waved edges `w`, `M`-dotted edges `md` appended, the
`Ψ`-dotted edges carried along, and the coefficient multiplied by `c`. -/
def BAGraph.lanlwExt (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (c : ℂ)
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.mk (({ Γ.toLGraph with solid := rest } : LGraph E I).owxExt (owxEmb 2) c s w)
    (Γ.psi.map (BAPsiEdge.map (owxEmb 2))) (md ++ Γ.mdot.map (BAMEdge.map (owxEmb 2)))

/-- **Term 1 of `lanlw`** (`B:363`) for `p ∈ lwSplit Γ.solid` with `p.1 = Ǧ_{xy}` (blue, circled; `x = p.1.src`,
`y = p.1.dst`): `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} f`; `coeff = coeff Γ`. -/
def BAGraph.lanlwT1 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.lanlwExt Γ p.2 1
    [⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 p.1.dst⟩]
    [⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]
    [⟨true, owxEmb 2 p.1.src, Sum.inr (Sum.inr 0)⟩]

/-- **The derivative term of `lanlw` for the solid edge `q.1` of `f`** (`q ∈ lwSplit p.2`, `B:363`):
`-Σ_{α,β} M_{xα} S_{αβ} G_{βy} ∂_{h_{βα}}` applied to `q.1`, i.e. `q.1` replaced by the two edges of `owxDE β α`
(`G_{ab} ↦ G_{aβ} G_{αb}`, `Ḡ_{ab} ↦ Ḡ_{aα} Ḡ_{βb}`); **`coeff = + coeff Γ`** (the `-` of `lanlw` cancels the `-` of
`∂G = -GG`; T2295-prove (a) row 10). -/
def BAGraph.lanlwD (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.lanlwExt Γ q.2 1
    [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 p.1.dst⟩]
    [⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]
    [⟨true, owxEmb 2 p.1.src, Sum.inr (Sum.inr 0)⟩]

/-- **The terms of `lanlw`** at the edge `p.1` of `Γ`: term 1, then one derivative term for each solid edge of
`f` (light-weights, weights and red edges included). -/
def BAGraph.lanlwTerms (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (BAGraph E (I ⊕ Fin 2)) :=
  BAGraph.lanlwT1 Γ p :: (lwSplit p.2).map (BAGraph.lanlwD Γ p)

end LanlwGraph

/-! ## 4. Target 1: the weight expansion -/

section BAWeightProof

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The fibre sum: a function of the block coordinate supported on one offset sums to the sum over the blocks
(the pattern of `BA/GreenSchur.lean`, `GreenSchur_fibre_sum`, private there). -/
private theorem BAExpandW_fibre_sum (d L W : ℕ) [NeZero L] [NeZero W] (x : Idx d L W) (f : Zd d L → ℝ) :
    ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ b : Zd d L, f b := by
  have h : ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ y : Idx d L W, (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0)
        (splitEquiv d L W y) := rfl
  rw [h, Equiv.sum_comp (splitEquiv d L W) (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0),
    Fintype.sum_prod_type]
  simp

/-- `Ψ^{(B)}` is symmetric (the block lattice adjacency is symmetric, `zdistD_neg`). -/
private theorem BAExpandW_PsiB_transpose (d L : ℕ) [NeZero L] : (PsiB d L)ᵀ = PsiB d L := by
  ext a b
  simp only [Matrix.transpose_apply, PsiB, Matrix.of_apply]
  have hadj : Adj d L b a ↔ Adj d L a b := by
    simp only [Adj]
    rw [show b - a = -(a - b) by ring, zdistD_neg]
  by_cases h : Adj d L a b
  · simp [h, hadj.mpr h]
  · simp [h, mt hadj.mp h]

/-- `Ψ = Ψ^{(B)} ⊗ I` on the fine lattice is symmetric. -/
private theorem BAExpandW_PsiI_transpose (d L W : ℕ) [NeZero L] [NeZero W] :
    (PsiI d L W)ᵀ = PsiI d L W := by
  unfold PsiI PsiV
  rw [Matrix.transpose_submatrix, ← Matrix.kroneckerMap_transpose, BAExpandW_PsiB_transpose,
    Matrix.transpose_one]

/-- **`M` is symmetric**, `M_{xα} = M_{αx}` (`M = (g₀ Ψ - E - m)⁻¹` with `Ψ` symmetric), unconditionally. -/
theorem baM_symm (g0 E : ℝ) (m : ℂ) (x α : Idx d L W) :
    BAlwM d L W g0 E m x α = BAlwM d L W g0 E m α x := by
  have hT : (BAlwM d L W g0 E m)ᵀ = BAlwM d L W g0 E m := by
    unfold BAlwM Mres
    rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv]
    congr 1
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, BAExpandW_PsiI_transpose,
      Matrix.transpose_one]
  exact (congrFun (congrFun hT x) α).symm

/-- **The fine Ward row** (`(eq:WardM)`, `7_8:1869`): `Σ_α |M_{xα}|² = 1` (target 1b). -/
theorem baM_row_sq (d L W : ℕ) [NeZero L] [NeZero W] (g0 E : ℝ) (m : ℂ) (h : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (x : Idx d L W) : ∑ α, ‖BAlwM d L W g0 E m x α‖ ^ 2 = 1 := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using h.1.ne'
  have h1 : ∑ α, ‖BAlwM d L W g0 E m x α‖ ^ 2 =
      ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then
        ‖RBM.BA.BAMB d L g0 (E : ℂ) m (split d L W x).1 (split d L W y).1‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold BAlwM
    rw [RBM.BA.BAMres_fine_apply d L W g0 (E : ℂ) m hw x y]
    split_ifs <;> simp
  rw [h1, BAExpandW_fibre_sum d L W x (fun b => ‖RBM.BA.BAMB d L g0 (E : ℂ) m (split d L W x).1 b‖ ^ 2)]
  exact RBM.BA.BAMB_row_sq_real d L g0 E m h _

/-- The rows of `svarF` at coupling `0` sum to `1` (`lwS_row_sum` at `u = 1` through the bridge). -/
private theorem BAExpandW_svarF_row (hL : 3 ≤ L) (x : Idx d L W) : ∑ y, svarF d L W 0 x y = 1 := by
  have h := lwS_row_sum (sz := lwWxSizes d L W 0 hL) (n := 0) 1 x
  simp only [lwS, Matrix.of_apply, one_mul] at h
  exact_mod_cast h

/-- `‖S_{xy}‖ = t svarF`, so the rows of `S` have absolute sum `t` (`0 ≤ t`). -/
private theorem BAExpandW_S_row_norm (hL : 3 ≤ L) {t : ℝ} (ht : 0 ≤ t) (x : Idx d L W) :
    ∑ y, ‖BAlwS d L W t x y‖ = t := by
  have : ∀ y, ‖BAlwS d L W t x y‖ = t * svarF d L W 0 x y := fun y => by
    simp only [BAlwS, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht, abs_of_nonneg (svarF_nonneg d L W 0 x y)]
  simp_rw [this]
  rw [← Finset.mul_sum, BAExpandW_svarF_row hL, mul_one]

/-- Gershgorin: a matrix with row absolute sums `≤ t < 1` has `1 - P` invertible. -/
private theorem BAExpandW_isUnit_of_row {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) {t : ℝ}
    (ht : t < 1) (h : ∀ k, ∑ j, ‖P k j‖ ≤ t) : IsUnit (1 - P) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖(1 - P) k j‖ = ‖P k j‖ := by
    intro j hj
    have hjk : k ≠ j := fun e => (Finset.ne_of_mem_erase hj) e.symm
    simp [Matrix.sub_apply, Matrix.one_apply_ne hjk]
  rw [Finset.sum_congr rfl hoff]
  have hsum : ∑ j ∈ Finset.univ.erase k, ‖P k j‖ = ∑ j, ‖P k j‖ - ‖P k k‖ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    ring
  have hdiag : 1 - ‖P k k‖ ≤ ‖(1 - P) k k‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (P k k)
    simpa using h1
  rw [hsum]
  linarith [h k]

/-- **`1 - M^+S` is invertible** (target 1b; Gershgorin: the rows of `M^+S` have absolute sum `≤ t Σ_α |M_{xα}|² = t`,
from `M_{αx} = M_{xα}`, `S ≥ 0` with rows `t`, and the fine Ward row). -/
theorem baW_isUnit (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IsUnit (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) := by
  refine BAExpandW_isUnit_of_row _ ht1 fun k => ?_
  have hb : ∀ j, ‖(BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) k j‖ ≤
      ∑ α, ‖BAlwM d L W g0 E m k α‖ ^ 2 * ‖BAlwS d L W t α j‖ := by
    intro j
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    simp only [BAlwMp, Matrix.of_apply, norm_mul, baM_symm g0 E m α k]
    rw [sq]
  calc ∑ j, ‖(BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) k j‖
      ≤ ∑ j, ∑ α, ‖BAlwM d L W g0 E m k α‖ ^ 2 * ‖BAlwS d L W t α j‖ := Finset.sum_le_sum fun j _ => hb j
    _ = ∑ α, ‖BAlwM d L W g0 E m k α‖ ^ 2 * ∑ j, ‖BAlwS d L W t α j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun α _ => (Finset.mul_sum _ _ _).symm
    _ = t := by
        simp_rw [BAExpandW_S_row_norm hL ht0]
        rw [← Finset.sum_mul, baM_row_sq d L W g0 E m hSelf k, one_mul]

/-- `W (1 - M^+S) = 1`. -/
theorem baW_mul (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BAlwW d L W g0 E t m * (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) = 1 :=
  Ring.inverse_mul_cancel _ (baW_isUnit d L W hL g0 E t m hSelf ht0 ht1)

end BAWeightProof

section BAWeightHolds

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Closure of `Tame` under the operations of the expansion (copy of the local macro `ba_tame` of
`Graph/BAExpand.lean`, which is not exported). -/
local macro "baw_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply BAExpand_tame_baG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply lwStein_tame_hflow
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-- A tame function of the sequence space, read through the slice at size `0`, is integrable for `PF d L W 0`. -/
private theorem BAExpandW_integrable_PF (hL : 3 ≤ L) {F : Sizes.SeqΩ (lwWxSizes d L W 0 hL) → ℂ}
    {G : Ω d L W → ℂ} (hF : Tame (lwWxSizes d L W 0 hL) F)
    (h : ∀ ω', G (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') = F ω') : Integrable G (PF d L W 0) := by
  have hG : G = F ∘ lwWxSec 0 hL := by
    funext ω
    have := h (lwWxSec 0 hL ω)
    rw [lwWx_slice_sec] at this
    exact this
  have hGc : Continuous G := by rw [hG]; exact hF.cont.comp (lwWx_continuous_sec hL)
  have hmap := Sizes.seqP_map_slice (lwWxSizes d L W 0 hL) 0
  rw [← hmap]
  refine (integrable_map_measure hGc.aestronglyMeasurable
    (Sizes.measurable_slice (lwWxSizes d L W 0 hL) 0).aemeasurable).2 ?_
  have e : G ∘ Sizes.slice (lwWxSizes d L W 0 hL) 0 = F := funext h
  rw [e]
  exact Tame.integrable (gaussIBP (lwWxSizes d L W 0 hL)) hF

variable (d L W) in
/-- The bracket of `BAlweightR`, the `y`-th summand without the weight `(1 + M^+S^+)_{xy}`. -/
private def BAExpandW_Bf (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (y : Idx d L W) (ω : Ω d L W) : ℂ :=
  ∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω α y *
        BAlwGc d L W g0 E t m ω β β * BAlwf d L W g0 E t m P ω -
      ∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwG d L W g0 E t m ω β y *
        BAlwdf d L W g0 E t m P ω β α

/-- `Σ_α Σ_β M_{yα} S_{αβ} Ǧ_{ββ} G_{αy} f - ... = Σ_β (M^+S)_{yβ} Ǧ_{ββ} f + (bracket)`, pathwise:
`G_{αy} = M_{αy} + Ǧ_{αy}`. -/
private theorem BAExpandW_pathwise (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (y : Idx d L W) (ω : Ω d L W) :
    BAlanlwR d L W g0 E t m P y y ω =
      ∑ β, (BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) y β * BAlanlwL d L W g0 E t m P β β ω +
        BAExpandW_Bf d L W g0 E t m P y ω := by
  unfold BAlanlwR BAExpandW_Bf BAlanlwL
  have hG : ∀ α, BAlwG d L W g0 E t m ω α y = BAlwGc d L W g0 E t m ω α y + BAlwM d L W g0 E m α y :=
    fun α => by simp [BAlwGc]
  have key : ∑ β, (BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) y β *
      (BAlwGc d L W g0 E t m ω β β * BAlwf d L W g0 E t m P ω) =
      ∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω β β *
        BAlwM d L W g0 E m α y * BAlwf d L W g0 E t m P ω := by
    simp only [Matrix.mul_apply, Matrix.of_apply, BAlwMp, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  have e1 : ∀ α β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω β β *
      BAlwG d L W g0 E t m ω α y * BAlwf d L W g0 E t m P ω =
      BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω α y *
        BAlwGc d L W g0 E t m ω β β * BAlwf d L W g0 E t m P ω +
      BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω β β *
        BAlwM d L W g0 E m α y * BAlwf d L W g0 E t m P ω := fun α β => by
    rw [hG α]; ring
  simp_rw [e1, Finset.sum_add_distrib]
  rw [key]
  ring



/-- **`lem_lweight`** (`B:376-387`, [yang2024Del, Lemma B.10]) on the block Anderson law `PF d L W 0`, for every `d`: the
pin `BAlweight`.  For `0 < t < 1`: `lanlw` at `(y, y)` (`baLanlw_holds`) gives `v = (M^+S) v + r` for the vector
`v_y = 𝔼 Ǧ_{yy} f` and `r_y = 𝔼[bracket]`, so `v = W r` by `W (1 - M^+S) = 1`; for `t = 0` both sides vanish. -/
theorem baLweight_holds (d : ℕ) : BAlweight d := by
  intro L W _ _ hL g0 E t m hSelf ht0 ht1 P x
  have hm : 0 < m.im := hSelf.1
  rcases ht0.eq_or_lt with rfl | ht
  · have hL0 : ∀ ω, BAlweightL d L W g0 E 0 m P x ω = 0 := fun ω => by
      simp [BAlweightL, BAExpand_Gc_zero]
    have hR0 : ∀ ω, BAlweightR d L W g0 E 0 m P x ω = 0 := fun ω => by
      simp [BAlweightR, BAlwS]
    simp [hL0, hR0]
  · have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    have hf : Tame1 (lwWxSizes d L W 0 hL) 0 (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)) :=
      baPoly_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz g0 t (lwWxRename d L W P)
    have tf : Tame (lwWxSizes d L W 0 hL) (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)) :=
      hf.tame
    have tD : ∀ α β : Idx d L W, Tame (lwWxSizes d L W 0 hL)
        (dhSample (lwWxSizes d L W 0 hL) 0 t α β (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P))) :=
      fun α β => lwStein_tame_dhSample hf t α β
    have tG : ∀ i j : Idx d L W, Tame (lwWxSizes d L W 0 hL) (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t i j) :=
      fun i j => BAExpand_tame_baG (lwWxSizes d L W 0 hL) 0 hz g0 t i j
    -- integrability of the two kinds of integrands on `PF d L W 0`
    have hIntA : ∀ β : Idx d L W, Integrable (fun ω => BAlanlwL d L W g0 E t m P β β ω) (PF d L W 0) := by
      intro β
      refine BAExpandW_integrable_PF hL (F := fun ω' => (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β β ω' -
        BAlwM d L W g0 E m β β) * baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P) ω') ?_ ?_
      · baw_tame
      · intro ω'
        unfold BAlanlwL BAlwGc
        rw [← baWx_baPoly hL g0 E t m ω' P]
        rfl
    have hIntB : ∀ y : Idx d L W, Integrable (fun ω => BAExpandW_Bf d L W g0 E t m P y ω) (PF d L W 0) := by
      intro y
      refine BAExpandW_integrable_PF hL (F := fun ω' =>
        ∑ α, ∑ β, BAlwM d L W g0 E m y α * lwS (lwWxSizes d L W 0 hL) 0 t α β *
          (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t α y ω' - BAlwM d L W g0 E m α y) *
          (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β β ω' - BAlwM d L W g0 E m β β) *
          baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P) ω' -
        ∑ α, ∑ β, BAlwM d L W g0 E m y α * lwS (lwWxSizes d L W 0 hL) 0 t α β *
          baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β y ω' *
          dhSample (lwWxSizes d L W 0 hL) 0 t β α
            (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)) ω') ?_ ?_
      · baw_tame
      · intro ω'
        have hdf : ∀ β α : Idx d L W, BAlwdf d L W g0 E t m P (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') β α =
            dhSample (lwWxSizes d L W 0 hL) 0 t β α
              (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)) ω' :=
          fun β α => (baWx_dh hL hz ht g0 β α ω' P).symm
        unfold BAExpandW_Bf BAlwGc
        simp only [hdf, ← baWx_baPoly hL g0 E t m ω' P, lwWx_lwS_apply hL t]
        rfl
    -- the vector of expectations and its linear relation
    set Pm : Matrix (Idx d L W) (Idx d L W) ℂ := BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t) with hPm
    set v : Idx d L W → ℂ := fun y => ∫ ω, BAlanlwL d L W g0 E t m P y y ω ∂(PF d L W 0) with hv
    set r : Idx d L W → ℂ := fun y => ∫ ω, BAExpandW_Bf d L W g0 E t m P y ω ∂(PF d L W 0) with hr
    have hrel : ∀ y, v y - ∑ β, Pm y β * v β = r y := by
      intro y
      have h1 := baLanlw_holds d L W hL g0 E t m hSelf ht.le ht1 P y y
      have h2 : ∫ ω, BAlanlwR d L W g0 E t m P y y ω ∂(PF d L W 0) = ∑ β, Pm y β * v β + r y := by
        simp_rw [BAExpandW_pathwise]
        rw [integral_add (integrable_finsetSum _ fun β _ => (hIntA β).const_mul _) (hIntB y),
          integral_finsetSum _ fun β _ => (hIntA β).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun β _ => integral_const_mul _ _
      have : v y = ∑ β, Pm y β * v β + r y := h1.trans h2
      rw [this]; ring
    have hW : BAlwW d L W g0 E t m * (1 - Pm) = 1 := baW_mul hL g0 E t m hSelf ht.le ht1
    have hvec : v = BAlwW d L W g0 E t m *ᵥ r := by
      have h1 : (1 - Pm) *ᵥ v = r := by
        funext y
        have := hrel y
        simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
        simpa [Matrix.mulVec, dotProduct] using this
      rw [← h1, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]
    have e1 : ∫ ω, BAlweightR d L W g0 E t m P x ω ∂(PF d L W 0) = ∑ y, BAlwW d L W g0 E t m x y * r y := by
      have : ∀ ω, BAlweightR d L W g0 E t m P x ω =
          ∑ y, BAlwW d L W g0 E t m x y * BAExpandW_Bf d L W g0 E t m P y ω := fun ω => rfl
      simp_rw [this]
      rw [integral_finsetSum _ fun y _ => (hIntB y).const_mul _]
      exact Finset.sum_congr rfl fun y _ => integral_const_mul _ _
    rw [e1]
    have h3 : v x = ∑ y, BAlwW d L W g0 E t m x y * r y := by
      have := congrFun hvec x
      simpa [Matrix.mulVec, dotProduct] using this
    exact h3

end BAWeightHolds

/-! ## 5. `lanlw` as a graph operation: the value identity (`lanlw_val`)

The BA twin of the graph-derivative value layer of `Graph/LWStein.lean:1412-1583` (`lwSampleData`, `lwK`,
`lwStein_term_eq`, `lwStein_dh_sedge_val`) for the shifted resolvent `baG`, and of `owx_term_integral`/`owx_graph_E`
(`Graph/LWWeightExp.lean:1060-1369`) for the two families of terms of `lanlw` (`BAGraph.lanlwT1`, `BAGraph.lanlwD`).
The identity is proved on the sequence space `Sizes.seqP` from `BAExpand_integral` at every labelling, then
transported to `PF d L W 0` by `lwWx_integral`. -/

section BASeq

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- The graph data at the sample `ω` of the sequence space: the shifted resolvent `baGm` (the only random matrix),
the deterministic `M`, `S`, `S⁺` and `gPsi`. -/
def BAExpandW_sampleData (g0 : ℝ) (z : ℂ) (u : ℝ)
    (M S Sp gPsi : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ω : Sizes.SeqΩ sz) :
    BALData (Idx d (sz.L n) (sz.W n)) :=
  { G := baGm sz n g0 z u ω, M := M, S := S, Sp := Sp, gPsi := gPsi }

variable {sz n}
variable {g0 : ℝ} {z : ℂ} {u : ℝ} {M S Sp gPsi : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

theorem BAExpandW_sedge_val_blue {V : Type*} (e : SEdge V) (hσ : e.σ = true) (ℓ : V → Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) :
    SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ e =
      baG sz n g0 z u (ℓ e.src) (ℓ e.dst) ω - (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) := by
  simp [SEdge.val, hσ, BAExpandW_sampleData, baG]

theorem BAExpandW_sedge_val_red {V : Type*} (e : SEdge V) (hσ : e.σ = false) (ℓ : V → Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) :
    SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ e =
      star (baG sz n g0 z u (ℓ e.src) (ℓ e.dst) ω) - star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) := by
  simp [SEdge.val, hσ, BAExpandW_sampleData, baG, star_sub]

/-- The factor of a solid edge is `C¹`-tame as a function of the sample. -/
theorem BAExpandW_sedge_val_tame1 (hz : z.im ≠ 0) {V : Type*} (e : SEdge V) (ℓ : V → Idx d (sz.L n) (sz.W n)) :
    Tame1 sz n (fun ω => SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ e) := by
  have hG := baG_tame1 (sz := sz) (n := n) hz g0 u (ℓ e.src) (ℓ e.dst)
  cases hσ : e.σ
  · have h := hG.conj.sub (Tame1.const (n := n) (sz := sz) (star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0)))
    convert h using 1
    funext ω
    exact BAExpandW_sedge_val_red e hσ ℓ ω
  · have h := hG.sub (Tame1.const (n := n) (sz := sz) (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0))
    convert h using 1
    funext ω
    exact BAExpandW_sedge_val_blue e hσ ℓ ω

/-- **The derivative of one edge factor**: `∂_{h_{αw}} (G-M)_{ab} = -G_{aα} G_{wb}` (blue),
`∂_{h_{αw}} \overline{(G-M)_{ab}} = -\bar G_{aw} \bar G_{αb}` (red). -/
theorem BAExpandW_dh_sedge_val (hz : z.im ≠ 0) (hu : 0 < u) {V : Type*} (e : SEdge V)
    (α w : Idx d (sz.L n) (sz.W n)) (ℓ : V → Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    dhSample sz n u α w (fun ω => SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ e) ω =
      if e.σ then -(baG sz n g0 z u (ℓ e.src) α ω * baG sz n g0 z u w (ℓ e.dst) ω)
      else -(star (baG sz n g0 z u (ℓ e.src) w ω) * star (baG sz n g0 z u α (ℓ e.dst) ω)) := by
  cases hσ : e.σ
  · have hfun : (fun ω => SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ e) = fun ω =>
        star (baG sz n g0 z u (ℓ e.src) (ℓ e.dst) ω) - star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) :=
      funext (BAExpandW_sedge_val_red e hσ ℓ)
    rw [hfun, lwStein_dh_sub (baG_tame1 hz g0 u _ _).conj (Tame1.const _), lwStein_dh_const,
      dhSample_baG_star hz hu g0]
    simp [star_mul']
  · have hfun : (fun ω => SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ e) = fun ω =>
        baG sz n g0 z u (ℓ e.src) (ℓ e.dst) ω - (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0) :=
      funext (BAExpandW_sedge_val_blue e hσ ℓ)
    rw [hfun, lwStein_dh_sub (baG_tame1 hz g0 u _ _) (Tame1.const _), lwStein_dh_const, dhSample_baG hz hu g0]
    simp

/-- The resolvent polynomial of a solid edge (`owxEdgePoly`) evaluates to its value. -/
theorem BAExpandW_baPoly_edgePoly {V : Type*} (ℓ : V → Idx d (sz.L n) (sz.W n)) (e : SEdge V)
    (ω : Sizes.SeqΩ sz) :
    baPoly sz n g0 z u (owxEdgePoly sz n M ℓ e) ω =
      SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ e := by
  cases hσ : e.σ
  · rw [BAExpandW_sedge_val_red e hσ ℓ ω]
    simp [owxEdgePoly, hσ, baPoly, baVar]
  · rw [BAExpandW_sedge_val_blue e hσ ℓ ω]
    simp [owxEdgePoly, hσ, baPoly, baVar]

theorem BAExpandW_baPoly_edgePoly_prod {V : Type*} (ℓ : V → Idx d (sz.L n) (sz.W n)) (l : List (SEdge V))
    (ω : Sizes.SeqΩ sz) :
    baPoly sz n g0 z u ((l.map (owxEdgePoly sz n M ℓ)).prod) ω =
      (l.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ)).prod := by
  unfold baPoly
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact BAExpandW_baPoly_edgePoly ℓ e ω

variable {E I : Type} [Fintype I] [DecidableEq I]

/-- The part of the value of a term that does not depend on the sample: coefficient, waved, dotted, `Ψ`- and
`M`-dotted factors. -/
def BAExpandW_K {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E I) (M S Sp gPsi : Matrix ι ι ℂ)
    (ℓ : E ⊕ I → ι) : ℂ :=
  Γ.coeff * (Γ.waved.map (WEdge.val (⟨0, M, S, Sp⟩ : LData ι) ℓ)).prod * (Γ.dotted.map (DEdge.val ℓ)).prod *
    (Γ.psi.map (BAPsiEdge.val (⟨⟨0, M, S, Sp⟩, gPsi⟩ : BALData ι) ℓ)).prod *
    (Γ.mdot.map (BAMEdge.val (⟨⟨0, M, S, Sp⟩, gPsi⟩ : BALData ι) ℓ)).prod

/-- The term of a graph is the sample-independent part times the product of the solid edge factors. -/
theorem BAExpandW_term_eq (Γ : BAGraph E I) (ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    Γ.term (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓ =
      BAExpandW_K Γ M S Sp gPsi ℓ * (Γ.solid.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ)).prod := by
  have hW : WEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ =
      WEdge.val (⟨0, M, S, Sp⟩ : LData _) ℓ := rfl
  have hP : BAPsiEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓ =
      BAPsiEdge.val (⟨⟨0, M, S, Sp⟩, gPsi⟩ : BALData _) ℓ := rfl
  have hM : BAMEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓ =
      BAMEdge.val (⟨⟨0, M, S, Sp⟩, gPsi⟩ : BALData _) ℓ := rfl
  simp only [BAGraph.term, LGraph.term, BAExpandW_K, hW, hP, hM]
  ring

/-- The term of a graph is `C¹`-tame as a function of the sample. -/
theorem BAExpandW_term_tame1 (hz : z.im ≠ 0) (Γ : BAGraph E I) (ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n)) :
    Tame1 sz n (fun ω => Γ.term (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓ) := by
  have hfun : (fun ω => Γ.term (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓ) = fun ω =>
      BAExpandW_K Γ M S Sp gPsi ℓ *
        (Γ.solid.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω).toLData ℓ)).prod :=
    funext (BAExpandW_term_eq Γ ℓ)
  rw [hfun]
  exact (Tame1.const _).mul (Tame1.listProd _ fun e _ => BAExpandW_sedge_val_tame1 hz e ℓ)

end BASeq

section BALanlwTerms

variable {E I : Type} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The labelling of `E ⊕ (I ⊕ Fin 2)` extending `(ℓe, ℓi)` by the labels `α, β` of the two new vertices. -/
theorem BAExpandW_lanlwExt_term (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (c : ℂ)
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (D : BALData ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) :
    (Γ.lanlwExt rest c s w md).term D ℓ' =
      c * ({ Γ with solid := rest } : BAGraph E I).term D (ℓ' ∘ owxEmb 2) * (s.map (SEdge.val D.toLData ℓ')).prod *
        (w.map (WEdge.val D.toLData ℓ')).prod * (md.map (BAMEdge.val D ℓ')).prod := by
  have h1 : (BAPsiEdge.val D ℓ') ∘ (BAPsiEdge.map (owxEmb 2)) = BAPsiEdge.val D (ℓ' ∘ owxEmb 2) :=
    funext fun e => rfl
  have h2 : (BAMEdge.val D ℓ') ∘ (BAMEdge.map (owxEmb 2)) = BAMEdge.val D (ℓ' ∘ owxEmb 2) :=
    funext fun e => rfl
  unfold BAGraph.lanlwExt BAGraph.term
  simp only [LGraph.term_owxExt, List.map_append, List.prod_append, List.map_map, h1, h2]
  ring

/-- **The value of a term of `lanlwT1`**: `K · f · M_{xα} S_{αβ} Ǧ_{ββ} G_{αy}` at a labelling `ℓ'` of the extended
vertex set that restricts to `ℓ` (`x = ℓ src`, `y = ℓ dst` of `p.1`). -/
theorem BAExpandW_lanlwT1_term (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) (hℓ : ℓ' ∘ owxEmb 2 = ℓ) :
    (BAGraph.lanlwT1 Γ p).term D ℓ' = ({ Γ with solid := p.2 } : BAGraph E I).term D ℓ *
      (((D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 1))) - D.M (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 1)))) *
        D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ p.1.dst)) * D.S (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 1))) *
        D.M (ℓ p.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) := by
  have hq : ∀ v, ℓ' (owxEmb 2 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  rw [BAGraph.lanlwT1, BAExpandW_lanlwExt_term, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val,
    BAMEdge.val, hq]
  simp
  ring

/-- **The value of a term of `lanlwD`** for the solid edge `q.1` of `f`:
`K · (others) · (G_{aβ} G_{αb} or its red twin) G_{βy} S_{αβ} M_{xα}`. -/
theorem BAExpandW_lanlwD_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) (hℓ : ℓ' ∘ owxEmb 2 = ℓ) :
    (BAGraph.lanlwD Γ p q).term D ℓ' = ({ Γ with solid := q.2 } : BAGraph E I).term D ℓ *
      ((if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)
        else star (D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q.1.dst))) *
        D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ p.1.dst)) * D.S (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 1))) *
        D.M (ℓ p.1.src) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hq : ∀ v, ℓ' (owxEmb 2 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  have h : SEdge.val D.toLData ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1 *
      SEdge.val D.toLData ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2 =
      if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)
      else star (D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq]
  rw [BAGraph.lanlwD, BAExpandW_lanlwExt_term, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc ((SEdge.val D.toLData ℓ' _)), h]
  simp [SEdge.val, WEdge.val, BAMEdge.val, hq]

end BALanlwTerms

section BALanlwIntegral

/-- The labelling of `E ⊕ (I ⊕ Fin 2)` extending `(ℓe, ℓi)` by the labels `α, β` restricts to `(ℓe, ℓi)`
(`owxLab2_emb` without the `Fintype E` instance). -/
theorem BAExpandW_lab2_emb {E I : Type} {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α β : ι) :
    owxLab2 ℓe ℓi α β ∘ owxEmb 2 = Sum.elim ℓe ℓi := by
  funext v
  rcases v with a | b <;> rfl

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype I] [DecidableEq I]
variable {g0 : ℝ} {z : ℂ} {u : ℝ} {M Sp gPsi : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- **`lanlw` for one labelling of the vertices of `Γ`** (expectations of terms): the blue circled edge `p.1` of `Γ`
(`p.1.src = x`, `p.1.dst = y`, `Γ.term = K Ǧ_{xy} f`); `𝔼 Γ.term(ℓ)` is the sum over the new labels `α, β` of the
expectations of the terms of `lanlwT1` and, for each solid edge `q.1` of `f`, of `lanlwD`.  Hypotheses: `GaussIBP`
(`gaussIBP`, proved), `Im z ≠ 0`, `u > 0`, `M_{ββ} = m` and `G - M = -M (H_u + u m) G` (as `BAExpand_integral`). -/
theorem BAExpandW_term_integral (hG : GaussIBP sz) (hz : z.im ≠ 0) (hu : 0 < u) (m : ℂ)
    (hMd : ∀ β, M β β = m)
    (hGM : ∀ ω, baGm sz n g0 z u ω - M = -(M * (sz.seqHflow n u ω + ((u : ℂ) * m) •
      (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) * baGm sz n g0 z u ω))
    (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : p.1.σ = true) (hc : p.1.circ = true)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) (ℓi : I → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) =
      ∑ α, ∑ β, ∫ ω, (BAGraph.lanlwT1 Γ p).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω)
          (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) +
      ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (BAGraph.lanlwD Γ p q).term
          (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
  classical
  set ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n) := Sum.elim ℓe ℓi with hℓ
  obtain ⟨x, hx⟩ : ∃ x : Idx d (sz.L n) (sz.W n), ℓ p.1.src = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Idx d (sz.L n) (sz.W n), ℓ p.1.dst = y := ⟨_, rfl⟩
  set K : ℂ := BAExpandW_K Γ M (lwS sz n u) Sp gPsi ℓ with hK
  set P := (p.2.map (owxEdgePoly sz n M ℓ)).prod with hPdef
  have hf : ∀ ω, baPoly sz n g0 z u P ω =
      (p.2.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω).toLData ℓ)).prod :=
    fun ω => BAExpandW_baPoly_edgePoly_prod ℓ p.2 ω
  have hP1 : Tame1 sz n (baPoly sz n g0 z u P) := baPoly_tame1 hz g0 u P
  have hw : ∀ ω, SEdge.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω).toLData ℓ p.1 =
      baG sz n g0 z u x y ω - M x y := by
    intro ω
    rw [BAExpandW_sedge_val_blue p.1 hσ ℓ ω, hc, hx, hy]
    simp
  have hΓ : ∀ ω, Γ.term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓ =
      K * ((baG sz n g0 z u x y ω - M x y) * baPoly sz n g0 z u P ω) := by
    intro ω
    rw [BAExpandW_term_eq, lwSplit_prod Γ.solid _ p hp, hw ω, hf ω]
  have hK' : ∀ s : List (SEdge (E ⊕ I)),
      BAExpandW_K ({ Γ with solid := s } : BAGraph E I) M (lwS sz n u) Sp gPsi ℓ = K := fun s => rfl
  have hT1 : ∀ α β ω, (BAGraph.lanlwT1 Γ p).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω)
      (owxLab2 ℓe ℓi α β) =
      K * baPoly sz n g0 z u P ω * (M x α * lwS sz n u α β *
        ((baG sz n g0 z u β β ω - M β β) * baG sz n g0 z u α y ω)) := by
    intro α β ω
    rw [BAExpandW_lanlwT1_term Γ p _ ℓ _ (BAExpandW_lab2_emb ℓe ℓi α β)]
    have : ({ Γ with solid := p.2 } : BAGraph E I).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓ =
        K * baPoly sz n g0 z u P ω := by
      rw [BAExpandW_term_eq, hf ω, hK']
    rw [this]
    have e0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
    have e1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
    rw [e0, e1, hx, hy]
    dsimp only [BAExpandW_sampleData, baG]
    ring
  have hD : ∀ (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α β ω,
      (BAGraph.lanlwD Γ p q).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β) =
      K * (q.2.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω).toLData ℓ)).prod *
        ((if q.1.σ then baG sz n g0 z u (ℓ q.1.src) β ω * baG sz n g0 z u α (ℓ q.1.dst) ω
          else star (baG sz n g0 z u (ℓ q.1.src) α ω) * star (baG sz n g0 z u β (ℓ q.1.dst) ω)) *
          baG sz n g0 z u β y ω) * lwS sz n u α β * M x α := by
    intro q α β ω
    rw [BAExpandW_lanlwD_term Γ p q _ ℓ _ (BAExpandW_lab2_emb ℓe ℓi α β)]
    have : ({ Γ with solid := q.2 } : BAGraph E I).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓ =
        K * (q.2.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω).toLData ℓ)).prod := by
      rw [BAExpandW_term_eq, hK']
    rw [this]
    have e0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
    have e1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
    rw [e0, e1, hx, hy]
    dsimp only [BAExpandW_sampleData, baG]
  have hdh : ∀ (α w : Idx d (sz.L n) (sz.W n)) ω, dhSample sz n u α w (baPoly sz n g0 z u P) ω =
      ((lwSplit p.2).map fun q =>
        (if q.1.σ then -(baG sz n g0 z u (ℓ q.1.src) α ω * baG sz n g0 z u w (ℓ q.1.dst) ω)
          else -(star (baG sz n g0 z u (ℓ q.1.src) w ω) * star (baG sz n g0 z u α (ℓ q.1.dst) ω))) *
        (q.2.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω).toLData ℓ)).prod).sum := by
    intro α w ω
    have hfun : baPoly sz n g0 z u P = fun ω => (p.2.map fun a =>
        SEdge.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω).toLData ℓ a).prod := funext hf
    rw [hfun, lwStein_dh_listProd p.2 (fun e _ => BAExpandW_sedge_val_tame1 hz e ℓ)]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [BAExpandW_dh_sedge_val hz hu q.1 α w ℓ ω]
  have hSD : ∀ α β ω, ((lwSplit p.2).map fun q => (BAGraph.lanlwD Γ p q).term
      (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β)).sum =
      -(K * (M x α * lwS sz n u α β * baG sz n g0 z u β y ω) *
        dhSample sz n u β α (baPoly sz n g0 z u P) ω) := by
    intro α β ω
    have h := owx_list_aux (lwSplit p.2) (K * (M x α * lwS sz n u α β * baG sz n g0 z u β y ω))
      (fun q => (if q.1.σ then -(baG sz n g0 z u (ℓ q.1.src) β ω * baG sz n g0 z u α (ℓ q.1.dst) ω)
          else -(star (baG sz n g0 z u (ℓ q.1.src) α ω) * star (baG sz n g0 z u β (ℓ q.1.dst) ω))) *
        (q.2.map (SEdge.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω).toLData ℓ)).prod)
      (fun q => (BAGraph.lanlwD Γ p q).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω)
        (owxLab2 ℓe ℓi α β)) (fun q _ => by
        rw [hD q α β ω]
        by_cases hσ : q.1.σ <;> simp [hσ] <;> ring)
    rw [h, ← hdh β α ω]
  have hpath : ∀ ω, K * (∑ α, ∑ β, M x α * lwS sz n u α β * (baG sz n g0 z u β β ω - M β β) *
        baG sz n g0 z u α y ω * baPoly sz n g0 z u P ω -
      ∑ α, ∑ β, M x α * lwS sz n u α β * baG sz n g0 z u β y ω *
        dhSample sz n u β α (baPoly sz n g0 z u P) ω) =
      ∑ α, ∑ β, (BAGraph.lanlwT1 Γ p).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω)
        (owxLab2 ℓe ℓi α β) +
      ∑ α, ∑ β, ((lwSplit p.2).map fun q => (BAGraph.lanlwD Γ p q).term
        (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β)).sum := by
    intro ω
    simp only [hT1, hSD]
    have hA : ∑ α, ∑ β, K * baPoly sz n g0 z u P ω * (M x α * lwS sz n u α β *
          ((baG sz n g0 z u β β ω - M β β) * baG sz n g0 z u α y ω)) =
        K * ∑ α, ∑ β, M x α * lwS sz n u α β * (baG sz n g0 z u β β ω - M β β) *
          baG sz n g0 z u α y ω * baPoly sz n g0 z u P ω := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    have hB : ∑ α, ∑ β, -(K * (M x α * lwS sz n u α β * baG sz n g0 z u β y ω) *
          dhSample sz n u β α (baPoly sz n g0 z u P) ω) =
        -(K * ∑ α, ∑ β, M x α * lwS sz n u α β * baG sz n g0 z u β y ω *
          dhSample sz n u β α (baPoly sz n g0 z u P) ω) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [hA, hB]
    ring
  have key := BAExpand_integral hG hz g0 hu M m hMd hGM P x y
  have hint : ∀ (T : BAGraph E (I ⊕ Fin 2)) (ℓ' : E ⊕ (I ⊕ Fin 2) → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (BAExpandW_term_tame1 hz T ℓ').tame
  have e1 : ∫ ω, Γ.term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓ ∂(Sizes.seqP sz) =
      K * ∫ ω, (baG sz n g0 z u x y ω - M x y) * baPoly sz n g0 z u P ω ∂(Sizes.seqP sz) := by
    simp_rw [hΓ]
    rw [integral_const_mul]
  rw [e1, key, ← integral_const_mul]
  simp_rw [hpath]
  set S1 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, (BAGraph.lanlwT1 Γ p).term
    (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β) with hS1
  set S2 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, ((lwSplit p.2).map fun q => (BAGraph.lanlwD Γ p q).term
    (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β)).sum with hS2
  have hi1 : Integrable S1 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _
  have hi2 : Integrable S2 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _
  change ∫ ω, (S1 ω + S2 ω) ∂(Sizes.seqP sz) = _
  rw [integral_add hi1 hi2]
  have e1' : ∫ ω, S1 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ∫ ω, (BAGraph.lanlwT1 Γ p).term
      (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
    rw [hS1, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact integral_finsetSum _ fun β _ => hint _ _
  have e2' : ∫ ω, S2 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (BAGraph.lanlwD Γ p q).term
      (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    rw [hS2, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun β _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  rw [e1', e2']

end BALanlwIntegral

section BALanlwVal

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype I] [DecidableEq I]
variable {g0 : ℝ} {z : ℂ} {u : ℝ} {M Sp gPsi : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The expectation of the value of a graph with two new internal vertices is the sum, over the labels of the old
internal vertices and of the new ones, of the expectations of its terms (the BA twin of `owx_integral_val2`). -/
theorem BAExpandW_integral_val2 (hG : GaussIBP sz) (hz : z.im ≠ 0)
    (S : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (T : BAGraph E (I ⊕ Fin 2))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, T.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ∫ ω, T.term (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω)
        (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
  have hint : ∀ ℓ', Integrable (fun ω => T.term (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓ') (Sizes.seqP sz) :=
    fun ℓ' => Tame.integrable hG (BAExpandW_term_tame1 hz T ℓ').tame
  have h1 : ∀ ω, T.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓe =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β,
        T.term (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) (owxLab2 ℓe ℓi α β) :=
    fun ω => owx_sum_fin2 (fun ℓ' => T.term (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) (Sum.elim ℓe ℓ'))
  simp_rw [h1]
  rw [integral_finsetSum _ fun ℓi _ => integrable_finsetSum _ fun α _ =>
    integrable_finsetSum _ fun β _ => hint _]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact integral_finsetSum _ fun β _ => hint _

/-- **`lanlw` as a graph operation: the identity of expectations of values on the sequence space** (`B:359-372`).
For a graph `Γ` with the blue circled edge `p.1 = Ǧ_{xy}` (`p ∈ lwSplit Γ.solid`, `Γ.val = 𝔼[Ǧ_{xy} f]` with the
monomial `f`): `𝔼 Γ.val = 𝔼 (lanlwT1 Γ p).val + Σ_q 𝔼 (lanlwD Γ p q).val`, `q` running over `lwSplit p.2`. -/
theorem BAExpandW_lanlw_val_seq (hG : GaussIBP sz) (hz : z.im ≠ 0) (hu : 0 < u) (m : ℂ)
    (hMd : ∀ β, M β β = m)
    (hGM : ∀ ω, baGm sz n g0 z u ω - M = -(M * (sz.seqHflow n u ω + ((u : ℂ) * m) •
      (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) * baGm sz n g0 z u ω))
    (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : p.1.σ = true) (hc : p.1.circ = true) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ =>
        Δ.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe).sum ∂(Sizes.seqP sz) := by
  classical
  have hintT : ∀ (T : BAGraph E (I ⊕ Fin 2)) (ℓ' : E ⊕ (I ⊕ Fin 2) → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (BAExpandW_term_tame1 hz T ℓ').tame
  have hintV : ∀ T : BAGraph E (I ⊕ Fin 2),
      Integrable (fun ω => T.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe) (Sizes.seqP sz) :=
    fun T => integrable_finsetSum _ fun ℓ' _ => hintT T _
  have hL : ∫ ω, Γ.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, Γ.term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω)
        (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
    unfold BAGraph.val
    exact integral_finsetSum _ fun ℓi _ => Tame.integrable hG (BAExpandW_term_tame1 hz Γ _).tame
  have hR : ∫ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ =>
        Δ.val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe).sum ∂(Sizes.seqP sz) =
      ∫ ω, (BAGraph.lanlwT1 Γ p).val (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe ∂(Sizes.seqP sz) +
        ((lwSplit p.2).map fun q => ∫ ω, (BAGraph.lanlwD Γ p q).val
          (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe ∂(Sizes.seqP sz)).sum := by
    unfold BAGraph.lanlwTerms
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    rw [integral_add (hintV _) (owx_integrable_list_sum _ _ fun q _ => hintV _),
      owx_integral_list_sum _ _ _ fun q _ => hintV _]
  have h4 : ((lwSplit p.2).map fun q => ∫ ω, (BAGraph.lanlwD Γ p q).val
        (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (BAGraph.lanlwD Γ p q).term
        (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit p.2).map fun q => ∫ ω, (BAGraph.lanlwD Γ p q).val
          (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit p.2).map fun q => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ∫ ω,
          (BAGraph.lanlwD Γ p q).term (BAExpandW_sampleData sz n g0 z u M (lwS sz n u) Sp gPsi ω)
            (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q _ => BAExpandW_integral_val2 hG hz _ _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  rw [hR, BAExpandW_integral_val2 hG hz _ _ ℓe, h4, hL]
  simp_rw [BAExpandW_term_integral hG hz hu m hMd hGM Γ p hp hσ hc ℓe]
  simp only [Finset.sum_add_distrib]

end BALanlwVal

section BALanlwPF

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The value of a graph is tame as a function of the sample (a finite sum of tame terms). -/
private theorem BAExpandW_val_tame {sz : Sizes d} {n : ℕ} {g0 : ℝ} {z : ℂ} {u : ℝ}
    {M S Sp gPsi : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hz : z.im ≠ 0)
    {E I : Type} [Fintype I] [DecidableEq I] (T : BAGraph E I) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => T.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓe) := by
  unfold BAGraph.val
  exact Tame.sum _ fun ℓi _ => (BAExpandW_term_tame1 hz T _).tame

/-- Every term of `lanlwTerms` carries the waved factor `S_{αβ}`: at `S = 0` it vanishes. -/
private theorem BAExpandW_lanlwTerm_zero {E I : Type} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (hS : D.S = 0) (Δ : BAGraph E (I ⊕ Fin 2)) (hΔ : Δ ∈ BAGraph.lanlwTerms Γ p) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) :
    Δ.term D ℓ' = 0 := by
  have hw : WEdge.val D.toLData ℓ' (⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩ :
      WEdge (E ⊕ (I ⊕ Fin 2))) = 0 := by
    simp [WEdge.val, hS]
  unfold BAGraph.lanlwTerms at hΔ
  rcases List.mem_cons.mp hΔ with rfl | hΔ
  · rw [BAGraph.lanlwT1, BAExpandW_lanlwExt_term]
    simp [hw]
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hΔ
    rw [BAGraph.lanlwD, BAExpandW_lanlwExt_term]
    simp [hw]

/-- **`lanlw` as a graph operation** (`B:359-372`, [yang2024Del, Lemma B.9]; target 3(b)): for a block Anderson graph
`Γ` and an edge `p.1 = Ǧ_{xy}` of `Γ` (`p ∈ lwSplit Γ.solid`, blue, circled), the expectation of the value of `Γ` at
the model data `BAlwData` is that of the sum of the values of the graphs of `lanlwTerms Γ p`.  For `0 < t < 1`:
`BAExpandW_lanlw_val_seq` (from `BAExpand_integral` at every labelling) through the bridge; for `t = 0` both sides
vanish (`Ǧ = 0`, `S = 0`).  The order bookkeeping of the terms (`lanlw_ord`, `lanlw_scalingOrderG`) is T2315's. -/
theorem lanlw_val (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {Ex Ix : Type} [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true)
    (hc : p.1.circ = true) (ℓe : Ex → Idx d L W) :
    ∫ ω, Γ.val (BAlwData d L W g0 E t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ => Δ.val (BAlwData d L W g0 E t m ω) ℓe).sum ∂(PF d L W 0) := by
  have hm : 0 < m.im := hSelf.1
  rcases ht0.eq_or_lt with rfl | ht
  · -- `t = 0`: `Ǧ = 0` on the left, `S = 0` on the right
    have hSz : (BAlwData d L W g0 E 0 m (fun _ => 0)).S = 0 := by
      ext i j
      simp [BAlwData, BAlwS]
    have hR : ∀ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ => Δ.val (BAlwData d L W g0 E 0 m ω) ℓe).sum = 0 := by
      intro ω
      refine List.sum_eq_zero fun a ha => ?_
      obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.mp ha
      unfold BAGraph.val
      refine Finset.sum_eq_zero fun ℓi _ => ?_
      exact BAExpandW_lanlwTerm_zero Γ p _ (by simpa [BAlwData] using hSz) Δ hΔ _
    have hLz : ∀ ω, Γ.val (BAlwData d L W g0 E 0 m ω) ℓe = 0 := by
      intro ω
      unfold BAGraph.val
      refine Finset.sum_eq_zero fun ℓi _ => ?_
      have h0 : SEdge.val (BAlwData d L W g0 E 0 m ω).toLData (Sum.elim ℓe ℓi) p.1 = 0 := by
        have := BAExpand_Gc_zero (d := d) (L := L) (W := W) g0 E m ω
          (Sum.elim ℓe ℓi p.1.src) (Sum.elim ℓe ℓi p.1.dst)
        simp only [SEdge.val, hσ, hc, BAlwData, ite_true]
        simpa [BAlwGc] using this
      simp only [BAGraph.term, LGraph.term, lwSplit_prod Γ.solid _ p hp, h0]
      simp
    simp [hLz, hR]
  · have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    have hS : Matrix.of (BAlwS d L W t) = lwS (lwWxSizes d L W 0 hL) 0 t := by
      ext i j
      simp [lwS, BAlwS]
    have key := BAExpandW_lanlw_val_seq (sz := lwWxSizes d L W 0 hL) (n := 0) (g0 := g0) (z := ztOf m E t) (u := t)
      (M := BAlwM d L W g0 E m)
      (Sp := Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) (gPsi := (g0 : ℂ) • PsiI d L W)
      (gaussIBP (lwWxSizes d L W 0 hL)) hz ht m (BAExpand_M_diag g0 E m hSelf)
      (fun ω => BAExpand_G_sub_M (lwWxSizes d L W 0 hL) 0 g0 E t m hm ht1 ω) Γ p hp hσ hc ℓe
    rw [← hS] at key
    have hF1 : Continuous (fun ω' : Sizes.SeqΩ (lwWxSizes d L W 0 hL) => Γ.val (BAExpandW_sampleData (lwWxSizes d L W 0 hL) 0 g0
        (ztOf m E t) t (BAlwM d L W g0 E m) (Matrix.of (BAlwS d L W t))
        (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) ((g0 : ℂ) • PsiI d L W) ω') ℓe) :=
      (BAExpandW_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz Γ ℓe).cont
    have hF2 : Continuous (fun ω' : Sizes.SeqΩ (lwWxSizes d L W 0 hL) =>
        ((BAGraph.lanlwTerms Γ p).map fun Δ => Δ.val (BAExpandW_sampleData (lwWxSizes d L W 0 hL) 0 g0
          (ztOf m E t) t (BAlwM d L W g0 E m) (Matrix.of (BAlwS d L W t))
          (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) ((g0 : ℂ) • PsiI d L W) ω') ℓe).sum) :=
      continuous_list_sum _ fun Δ _ =>
        (BAExpandW_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz Δ ℓe).cont
    exact (lwWx_integral hL hF1 fun ω' => rfl).trans (key.trans (lwWx_integral hL hF2 fun ω' => rfl).symm)

end BALanlwPF

/-! ## 6. Instance graphs and compiled instances (namespace `RBM.Graph.BAExpandWInst`)

The graphs `baGcxy`, `baGcxx` are copied from `docs/tickets/checks/T2303-check.lean` section 4 (instances (I3), (I4) of
T2295; their counters are T2315's). -/

/-- (I3): `Ǧ_{xy}`, `x, y = inl 0, inl 1` external. -/
def baGcxy : BAGraph (Fin 2) (Fin 0) where
  solid := [⟨true, true, .inl 0, .inl 1⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

/-- (I4): the weight `Ǧ_{xx}`, `x = inr 0` internal. -/
def baGcxx : BAGraph (Fin 0) (Fin 1) where
  solid := [⟨true, true, .inr 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

namespace BAExpandWInst

/-- (I5) at `t = 0` both sides of `lem_lweight` vanish pointwise (`Ǧ = 0`, `S = 0`); `baLweight_holds 3` at `t = 0`
is the equality `0 = 0` of the two integrals. -/
theorem baLweight_t0 (g0 E : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf 3 3 g0 (E : ℂ) m)
    (P : MvPolynomial (Bool × Idx 3 3 1 × Idx 3 3 1) ℂ) (x : Idx 3 3 1) :
    ∫ ω, BAlweightL 3 3 1 g0 E 0 m P x ω ∂(PF 3 3 1 0) = 0 ∧
      ∫ ω, BAlweightR 3 3 1 g0 E 0 m P x ω ∂(PF 3 3 1 0) = 0 ∧
      ∫ ω, BAlweightL 3 3 1 g0 E 0 m P x ω ∂(PF 3 3 1 0) =
        ∫ ω, BAlweightR 3 3 1 g0 E 0 m P x ω ∂(PF 3 3 1 0) := by
  have hL0 : ∀ ω, BAlweightL 3 3 1 g0 E 0 m P x ω = 0 := fun ω => by
    simp [BAlweightL, BAExpand_Gc_zero]
  have hR0 : ∀ ω, BAlweightR 3 3 1 g0 E 0 m P x ω = 0 := fun ω => by
    simp [BAlweightR, BAlwS]
  refine ⟨by simp [hL0], by simp [hR0], ?_⟩
  exact baLweight_holds 3 3 1 (by norm_num) g0 E 0 m hSelf le_rfl one_pos P x

/-- **Instance of `baLweight_holds`** (the point `g₀ = 0`, `E = 0`, `m = i`, every hypothesis discharged;
`d = 3`, `L = 3`, `W = 1`, `t = 1/2`; `x = 0`, `P = X (true, e₀, 0) * X (false, e₀, 0)`, i.e. `f = G_{e₀ 0} Ḡ_{e₀ 0}`). -/
example :
    ∫ ω, BAlweightL 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0 ω ∂(PF 3 3 1 0) =
    ∫ ω, BAlweightR 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0 ω ∂(PF 3 3 1 0) :=
  baLweight_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num) _ _

/-- **Instance of `baLweight_holds` at `g₀ = 1/2`** (`d = 3`, `L = 3`, `W = 1`, `E = 3/10`, `t = 1/2`; `x = e₀`,
`P = X (true, e₀, 0)`): the datum `m` solving `(self_m)` is a hypothesis of the example (`hSelf`); every other
hypothesis is discharged. -/
example (m : ℂ) (hSelf : RBM.BA.BASelf 3 3 (1 / 2) (((3 / 10 : ℝ)) : ℂ) m) :
    ∫ ω, BAlweightL 3 3 1 (1 / 2) (3 / 10) (1 / 2) m
      (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0)) (fun i => if i = 0 then 1 else 0) ω
        ∂(PF 3 3 1 0) =
    ∫ ω, BAlweightR 3 3 1 (1 / 2) (3 / 10) (1 / 2) m
      (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0)) (fun i => if i = 0 then 1 else 0) ω
        ∂(PF 3 3 1 0) :=
  baLweight_holds 3 3 1 (by norm_num) (1 / 2) (3 / 10) (1 / 2) m hSelf (by norm_num) (by norm_num) _ _

/-- (I6) `1 - M^+S` is invertible at `d = 3`, `L = 3`, `W = 1`, `g₀ = 0`, `E = 0`, `m = i`, `t = 1/2`
(there `M = i·1`, `M^+S = -S`), every hypothesis discharged. -/
example : IsUnit (1 - BAlwMp 3 3 1 0 0 Complex.I * Matrix.of (BAlwS 3 3 1 (1 / 2))) :=
  baW_isUnit 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)

/-- (I6) `W (1 - M^+S) = 1` at the same data. -/
example : BAlwW 3 3 1 0 0 (1 / 2) Complex.I * (1 - BAlwMp 3 3 1 0 0 Complex.I * Matrix.of (BAlwS 3 3 1 (1 / 2))) = 1 :=
  baW_mul (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)

/-- (I6) the fine Ward row `Σ_α |M_{xα}|² = 1` and the symmetry of `M` at the same data. -/
example (x : Idx 3 3 1) : ∑ α, ‖BAlwM 3 3 1 0 0 Complex.I x α‖ ^ 2 = 1 :=
  baM_row_sq 3 3 1 0 0 Complex.I BAExpandInst.baSelf_zero x

example (x α : Idx 3 3 1) : BAlwM 3 3 1 0 0 Complex.I x α = BAlwM 3 3 1 0 0 Complex.I α x :=
  baM_symm 0 0 Complex.I x α

/-- **Instance of `lanlw_val` for `Ǧ_{xy}` (`baGcxy`)** at `d = 3`, `L = 3`, `W = 1`, `g₀ = 0`, `E = 0`, `m = i`,
`t = 1/2`, the labelling `x = 0`, `y = e₀ ≠ x`: every hypothesis discharged (the edge `p.1` is the one edge of `baGcxy`). -/
example :
    ∫ ω, baGcxy.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω)
        ![(0 : Idx 3 3 1), fun i => if i = 0 then 1 else 0] ∂(PF 3 3 1 0) =
      ∫ ω, ((BAGraph.lanlwTerms baGcxy ⟨⟨true, true, .inl 0, .inl 1⟩, []⟩).map fun Δ =>
        Δ.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω)
          ![(0 : Idx 3 3 1), fun i => if i = 0 then 1 else 0]).sum ∂(PF 3 3 1 0) :=
  lanlw_val 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
    baGcxy _ (by simp [baGcxy, lwSplit]) rfl rfl _

/-- **Instance of `lanlw_val` for the weight `Ǧ_{xx}` (`baGcxx`)** at the same data; the internal vertex `x = inr 0`
is summed over `Idx 3 3 1`, every hypothesis discharged. -/
example :
    ∫ ω, baGcxx.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) (fun i => i.elim0) ∂(PF 3 3 1 0) =
      ∫ ω, ((BAGraph.lanlwTerms baGcxx ⟨⟨true, true, .inr 0, .inr 0⟩, []⟩).map fun Δ =>
        Δ.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) (fun i => i.elim0)).sum ∂(PF 3 3 1 0) :=
  lanlw_val 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
    baGcxx _ (by simp [baGcxx, lwSplit]) rfl rfl _

end BAExpandWInst

end RBM.Graph

end
