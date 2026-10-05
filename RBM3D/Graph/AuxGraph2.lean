/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.LWPins
import RBM3D.Green.GbEXP
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.PerTimeCalc
import RBM3D.Induction.DecayLoopB

/-!
# LW-11b: `claim:xi`, the edge variables `ξ` of `(eq:xia1a2)` and the bridge `(eq:Gbyxi)` (T2185)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `(yixi)`,
`(eq:Gbyxi)`, `(eq:xia1a2)`, `claim:xi` (`7_8:873-890`, no proof in the paper, D101), the use in
`GtoAG` (`7_8:914-921`) and `(eq:Gbyxi3)` (`7_8:960-966`); `lem_GbEXP` (`3_5:14-40`).  The
deterministic half of `GtoAG` is LW-11a (`RBM3D/Graph/AuxGraph.lean`, T2170); this file is the
random layer.

* Section 1: the vocabulary `lwXiSq`, `lwXiVar` (`(eq:xia1a2)` squared, and its square root).
* Section 2: the deterministic facts `lwXiVar_nonneg`, `lwXiVar_symm`, `lwXiSq_ge_W`,
  `lwXi_gexRHS_le` (the inclusion of `(eq:Gbyxi)`), and the Ward part of `claim:xi`
  (`lwXi_ward_sum`, with the private Ward lemmas for both charges).
* Section 3: the `≺` helpers (bad-set implications, the event `Ω(t, ε₁/2)`, indicator removal) and
  the deterministic comparisons `Φ(m) ≤ K(ρ) Φ(ℓ)`, `ξ² ≲ Φ(ℓ)²`.
* Section 4: `claim:xi` (`LWXiClaim`, `lwXiClaim_holds`).
* Section 5: `(eq:Gbyxi)` off the diagonal (`LWGbyXi`, `lwGbyXi_holds`, `lwGbyXi_hxi`) and
  entrywise (`LWEntryPsi`, `lwEntryPsi_holds`).
* Section 6: the radii (`LWXiRad`, `lwXiRad_holds`).
* Section 7: compiled nonempty instances at the merged `d = 3` data.

Ports (RBM1D and RBM2D have no light-weight graph layer; every port is from a merged RBM3D file
where the declaration is `private`): the lattice helpers `auxGraph2_zdistInf_*` from
`RBM3D/Path/LemDecCalE.lean:109-142`; `auxGraph2_trace_pm_formula` from
`RBM3D/Green/Pins.lean:377-400`; `auxGraph2_gres_blockMat_true` from
`RBM3D/Green/Pins.lean:350-364`;
`auxGraph2_Gres_true`, `auxGraph2_Gres_false`, `auxGraph2_Gres_conjTranspose` from
`RBM3D/Induction/ConArgDet.lean:141-163`.
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

open RBM RBM.Gauss RBM.Gauss.Sizes Filter
open scoped Matrix

/-! ## 1. The vocabulary of `(eq:xia1a2)` (target 1) -/

/-- **`[ξ([a₁],[a₂])]²` of `(eq:xia1a2)`** (`7_8:882`) at the block radius `ρ n` (the paper: `(log W)^{1+2ε₁}`):
the `(+,-)` and `(-,+)` two-loops `𝓛^{(2)}_{t,σ,(b₁,b₂)}` over the `‖·‖_∞`-ball pairs `|b₁ - a₁|, |b₂ - a₂| ≤ ρ`
(summed over the two charges; the paper takes the maximum, at most a factor 2), plus `W^{-d} 1(|a₁ - a₂| ≤ ρ)`.  The
charge set and the summand are those of the merged `STgexRHS` (the right side of `(GijGEX)`). -/
def lwXiSq {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  (∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
    ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0)

/-- **The edge variables `ξ([a₁],[a₂])`** of `(eq:xia1a2)`: the square root of `lwXiSq`; the shape of the `ξ` of the merged
`LWXi`, `LWAnp`. -/
def lwXiVar {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  Real.sqrt (lwXiSq sz E t ρ n a₁ a₂ ω)

/-! ## 2. Deterministic facts (target 2) -/

section Lattice

private theorem auxGraph2_zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem auxGraph2_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private theorem auxGraph2_zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

private theorem auxGraph2_zdistInf_tri (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    zdistInf d L (x - w) ≤ zdistInf d L (x - y) + zdistInf d L (y - w) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact auxGraph2_zdistInf_add_le d L _ _

private theorem auxGraph2_zdistInf_sub_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, auxGraph2_zdistInf_neg]

private theorem auxGraph2_zdistInf_tri_real (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    (zdistInf d L (x - w) : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + (zdistInf d L (y - w) : ℝ) := by
  exact_mod_cast auxGraph2_zdistInf_tri d L x y w

/-- `zdistInf (a - A) ≤ R` from `zdistD (A - a) ≤ R`. -/
private theorem auxGraph2_zdistInf_le_of_zdistD (d L : ℕ) [NeZero L] (A a : Zd d L) {R : ℝ}
    (h : (zdistD d L (A - a) : ℝ) ≤ R) :
    (zdistInf d L (a - A) : ℝ) ≤ R := by
  rw [auxGraph2_zdistInf_sub_comm]
  exact (by exact_mod_cast zdistInf_le_zdistD d L (A - a) : (zdistInf d L (A - a) : ℝ) ≤ zdistD d L (A - a)).trans h

end Lattice

section Basic

variable {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ)

private theorem auxGraph2_xiSq_nonneg (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    0 ≤ lwXiSq sz E t ρ n a₁ a₂ ω := by
  unfold lwXiSq
  refine add_nonneg (Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ =>
    Finset.sum_nonneg fun σ _ => norm_nonneg _) ?_
  have : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  split_ifs <;> positivity

/-- `lwXiVar ≥ 0` (the first conjunct of `LWXi`, part 1). -/
theorem lwXiVar_nonneg (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    0 ≤ lwXiVar sz E t ρ n a₁ a₂ ω := Real.sqrt_nonneg _

private theorem auxGraph2_xiVar_sq (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwXiVar sz E t ρ n a₁ a₂ ω ^ 2 = lwXiSq sz E t ρ n a₁ a₂ ω :=
  Real.sq_sqrt (auxGraph2_xiSq_nonneg sz E t ρ n a₁ a₂ ω)

/-- Cyclicity of the trace: the two-loop with the two entries swapped (`loopM` at length two). -/
private theorem auxGraph2_Lloop_two_swap (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) (E' t' : ℝ) :
    Lloop sz n E' t' ![σ₁, σ₂] ![a, b] ω = Lloop sz n E' t' ![σ₂, σ₁] ![b, a] ω := by
  unfold Lloop loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact Matrix.trace_mul_comm _ _

private theorem auxGraph2_pair_sum (g : (Fin 2 → Bool) → ℝ) :
    ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), g σ =
      g ![true, false] + g ![false, true] := by
  rw [Finset.sum_pair]
  intro h
  have := congrFun h 0
  simp at this

/-- **`ξ([a₁],[a₂]) = ξ([a₂],[a₁])`** (the first conjunct of `LWXi`, part 2): reindex `(b₁, b₂) ↦ (b₂, b₁)`;
`‖𝓛_{(s,!s),(b₂,b₁)}‖ = ‖𝓛_{(!s,s),(b₁,b₂)}‖` by cyclicity of the trace. -/
theorem lwXiVar_symm (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwXiVar sz E t ρ n a₁ a₂ ω = lwXiVar sz E t ρ n a₂ a₁ ω := by
  unfold lwXiVar
  congr 1
  unfold lwXiSq
  congr 1
  · rw [Finset.sum_comm (s := Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n))]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
    rw [auxGraph2_pair_sum, auxGraph2_pair_sum,
      auxGraph2_Lloop_two_swap sz n true false b₁ b₂ ω (E n) (t n),
      auxGraph2_Lloop_two_swap sz n false true b₁ b₂ ω (E n) (t n)]
    ring
  · rw [auxGraph2_zdistInf_sub_comm]

/-- **The variables are not void**: `W^{-d} ≤ ξ([a],[a])²` (`0 ≤ ρ`). -/
theorem lwXiSq_ge_W (hρ : 0 ≤ ρ n) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ lwXiSq sz E t ρ n a a ω := by
  unfold lwXiSq
  have h1 : 0 ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a) : ℝ) ≤ ρ n),
      ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a) : ℝ) ≤ ρ n),
        ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ :=
    Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ => Finset.sum_nonneg fun σ _ => norm_nonneg _
  have h2 : (if (zdistInf d (sz.L n) (a - a) : ℝ) ≤ ρ n then (1 : ℝ) else 0) = 1 := by
    rw [sub_self, auxGraph2_zdistInf_zero]
    simp [hρ]
  rw [h2]
  linarith

/-- **The inclusion of `(eq:Gbyxi)`** (`7_8:878-880`): for `0 ≤ R`, `2R + 1 ≤ ρ`, and blocks `a`, `b` at
`zdistD`-distance `≤ R` from `[x]`, `[y]`, the right side `STgexRHS` of `(GijGEX)` at `([x], [y])` is at most
`ξ(a, b)²`: `|a' - a| ≤ 1 + R ≤ ρ`, `|b' - b| ≤ ρ`, and `|a - b| ≤ 2R + 1 ≤ ρ` when `|[x] - [y]| ≤ 1`. -/
theorem lwXi_gexRHS_le {R : ℝ} (hR : 0 ≤ R) (hρ : 2 * R + 1 ≤ ρ n)
    (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hx : (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R)
    (hy : (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R) :
    STgexRHS sz n (E n) (t n) ω (STblk sz n x) (STblk sz n y) ≤ lwXiSq sz E t ρ n a b ω := by
  set A := STblk sz n x with hA
  set B := STblk sz n y with hB
  have hxA : (zdistInf d (sz.L n) (a - A) : ℝ) ≤ R :=
    auxGraph2_zdistInf_le_of_zdistD d (sz.L n) A a hx
  have hyB : (zdistInf d (sz.L n) (b - B) : ℝ) ≤ R :=
    auxGraph2_zdistInf_le_of_zdistD d (sz.L n) B b hy
  unfold STgexRHS lwXiSq
  refine add_le_add ?_ ?_
  · -- the sums
    have hsub1 : Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - A) ≤ 1) ⊆
        Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a) : ℝ) ≤ ρ n) := by
      intro a' ha'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
      have h1 : (zdistInf d (sz.L n) (a' - A) : ℝ) ≤ 1 := by exact_mod_cast ha'
      have := auxGraph2_zdistInf_tri_real d (sz.L n) a' A a
      have h2 : (zdistInf d (sz.L n) (A - a) : ℝ) ≤ R := by
        rw [auxGraph2_zdistInf_sub_comm]; exact hxA
      linarith
    have hsub2 : Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - B) ≤ 1) ⊆
        Finset.univ.filter (fun c : Zd d (sz.L n) => (zdistInf d (sz.L n) (c - b) : ℝ) ≤ ρ n) := by
      intro b' hb'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb' ⊢
      have h1 : (zdistInf d (sz.L n) (b' - B) : ℝ) ≤ 1 := by exact_mod_cast hb'
      have := auxGraph2_zdistInf_tri_real d (sz.L n) b' B b
      have h2 : (zdistInf d (sz.L n) (B - b) : ℝ) ≤ R := by
        rw [auxGraph2_zdistInf_sub_comm]; exact hyB
      linarith
    -- reorder the sums of `STgexRHS`: `σ` outermost → innermost
    have hre : ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - A) ≤ 1),
          ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - B) ≤ 1),
            ‖Lloop sz n (E n) (t n) σ ![a', b'] ω‖ =
        ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - A) ≤ 1),
          ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - B) ≤ 1),
            ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
              ‖Lloop sz n (E n) (t n) σ ![a', b'] ω‖ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a' _ => Finset.sum_comm
    rw [hre]
    have hnn : ∀ a' b' : Zd d (sz.L n), 0 ≤ ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖Lloop sz n (E n) (t n) σ ![a', b'] ω‖ := fun a' b' =>
      Finset.sum_nonneg fun σ _ => norm_nonneg _
    calc _ ≤ ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - A) ≤ 1),
          ∑ c ∈ Finset.univ.filter (fun c : Zd d (sz.L n) => (zdistInf d (sz.L n) (c - b) : ℝ) ≤ ρ n),
            ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
              ‖Lloop sz n (E n) (t n) σ ![a', c] ω‖ :=
          Finset.sum_le_sum fun a' _ =>
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun c _ _ => hnn a' c
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun a' _ _ =>
          Finset.sum_nonneg fun c _ => hnn a' c
  · -- the indicator
    have hW : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hW
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h2
      have h1' : (zdistInf d (sz.L n) (A - B) : ℝ) ≤ 1 := by exact_mod_cast h1
      have t1 := auxGraph2_zdistInf_tri_real d (sz.L n) a A b
      have t2 := auxGraph2_zdistInf_tri_real d (sz.L n) A B b
      have t3 : (zdistInf d (sz.L n) (B - b) : ℝ) ≤ R := by
        rw [auxGraph2_zdistInf_sub_comm]; exact hyB
      linarith
    · exact zero_le_one
    · exact le_rfl

end Basic

/-! ### The Ward part of `claim:xi` -/

section Ward

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem auxGraph2_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private theorem auxGraph2_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) :
    Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

private theorem auxGraph2_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) :
    Gres H z false = green H ((starRingEnd ℂ) z) := by
  simp only [green, Gres, Bool.false_eq_true, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

private theorem auxGraph2_gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ)
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
private theorem auxGraph2_trace_pm_formula (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
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
private theorem auxGraph2_sum_Eblk :
    ∑ a, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- The two-loop `𝓛^{(2)}_{(s,!s),(a,b)}` is a non-negative real: `W^{-2d} Σ_{v∈[b], w∈[a]} |G(s)_{vw}|²`. -/
private theorem auxGraph2_loop2_real (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
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
    rw [← auxGraph2_Gres_conjTranspose hHb z s, auxGraph2_trace_pm_formula]

/-- Summing the last label of `𝓛^{(2)}_{(s,!s),(a,b)}` removes `E_b` with the factor `W^{-d}`. -/
private theorem auxGraph2_loop2_rowsum (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (s : Bool) (a : Zd d L) :
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
  rw [← Finset.mul_sum, auxGraph2_sum_Eblk, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- **Ward's identity for the `(s,!s)` two-loop**, both charges:
`2iη Σ_b 𝓛^{(2)}_{(s,!s),(a,b)} = W^{-d} (tr(G(+)E_a) - tr(G(-)E_a))`. -/
private theorem auxGraph2_rowsum_ward (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (s : Bool) (a : Zd d L) :
    (2 * Complex.I * (z.im : ℂ)) * ∑ b, loopFine d L W H z ![s, !s] ![a, b] =
      (((W : ℂ) ^ d)⁻¹) * (Matrix.trace (Gres (blockMat d L W H) z true * Eblk d L W a) -
        Matrix.trace (Gres (blockMat d L W H) z false * Eblk d L W a)) := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hu : IsUnit (blockMat d L W H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hHb hz
  have hu' : IsUnit (blockMat d L W H - ((starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hHb (by simpa using hz)
  rw [auxGraph2_loop2_rowsum, auxGraph2_Gres_true, auxGraph2_Gres_false]
  rw [mul_left_comm]
  congr 1
  cases s with
  | true =>
    simp only [Bool.not_true]
    rw [auxGraph2_Gres_true, auxGraph2_Gres_false, Matrix.trace_mul_cycle]
    have h := RBM.trace_green_sub_trace_green_conj' hu hu' (Eblk d L W a)
    rw [h]
  | false =>
    simp only [Bool.not_false]
    rw [auxGraph2_Gres_true, auxGraph2_Gres_false, Matrix.trace_mul_cycle]
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
private theorem auxGraph2_norm_trace_le (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) {g : ℝ}
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
private theorem auxGraph2_sum_norm_eq {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (h : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ f i = (r : ℂ)) : ∑ i, ‖f i‖ = ‖∑ i, f i‖ := by
  choose r hr0 hr using h
  have h1 : ∑ i, f i = ((∑ i, r i : ℝ) : ℂ) := by
    simp only [hr, Complex.ofReal_sum]
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hr0 i)]
  exact Finset.sum_congr rfl fun i _ => by rw [hr, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]

/-- **Ward's bound for the `(s,!s)` two-loop**: `Σ_b ‖𝓛^{(2)}_{(s,!s),(a,b)}‖ ≤ (W^d η)⁻¹ g` where `g ≥ |G_{yy}|`
for every `y` and `η = Im z > 0`. -/
private theorem auxGraph2_rowsum_norm_le (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hη : 0 < z.im) {g : ℝ} (hg : ∀ y : Idx d L W, ‖Gres H z true y y‖ ≤ g) (s : Bool) (a : Zd d L) :
    ∑ b, ‖loopFine d L W H z ![s, !s] ![a, b]‖ ≤ (((W : ℝ) ^ d) * z.im)⁻¹ * g := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  rw [auxGraph2_sum_norm_eq _ (fun b => auxGraph2_loop2_real H hH z s a b)]
  have hw := auxGraph2_rowsum_ward H hH z hη.ne' s a
  have hn := congrArg norm hw
  rw [norm_mul (2 * Complex.I * (z.im : ℂ)) _, norm_mul (((W : ℂ) ^ d)⁻¹) _] at hn
  have hg1 : ∀ v : Vtx d L W, ‖Gres (blockMat d L W H) z true v v‖ ≤ g := by
    intro v
    rw [auxGraph2_gres_blockMat_true]
    exact hg _
  have hg2 : ∀ v : Vtx d L W, ‖Gres (blockMat d L W H) z false v v‖ ≤ g := by
    intro v
    have h := auxGraph2_Gres_conjTranspose hHb z true
    simp only [Bool.not_true] at h
    rw [← h, Matrix.conjTranspose_apply, norm_star]
    exact hg1 v
  have t1 := auxGraph2_norm_trace_le _ hg1 a
  have t2 := auxGraph2_norm_trace_le _ hg2 a
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

variable {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ)

/-- **The Ward part of `claim:xi`** (`7_8:884-890`): for `|E| < 2`, `t < 1`, `0 ≤ ρ`, and `A` a bound of
`‖(G_t - M)_{xy}‖` over all `x, y`,
`Σ_{a₂} ξ([a₁],[a₂])² ≤ 2 (2ρ+1)^{2d} (W^d η)⁻¹ (1 + A) + (2ρ+1)^d W^{-d}` (`η = η_t`).  Route: two ball counts
(`DecayLoopB_card_ball`), Ward's identity for `𝓛^{(2)}_{(s,!s)} ≥ 0` (`W^{-2d} Σ |G_{vw}|²`), `|𝓛^{(1)}| ≤ 1 + A`. -/
theorem lwXi_ward_sum (hE : |E n| < 2) (ht1 : t n < 1) (hρ : 0 ≤ ρ n) (ω : sz.SeqΩ) {A : ℝ}
    (hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (E n) (t n) ω x y‖ ≤ A) (a₁ : Zd d (sz.L n)) :
    ∑ a₂, lwXiSq sz E t ρ n a₁ a₂ ω ≤
      2 * (2 * ρ n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (t n))⁻¹ * (1 + A)) +
        (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  classical
  set z := zt (E n) (t n) with hz
  have hη : 0 < z.im := by rw [hz, ← etaT_eq_zt_im]; exact etaT_pos hE ht1
  have hηe : etaT (E n) (t n) = z.im := etaT_eq_zt_im
  rw [hηe]
  have hHerm := sz.seqHflow_isHermitian n (t n) ω
  have hg : ∀ y : Idx d (sz.L n) (sz.W n),
      ‖Gres (sz.seqHflow n (t n) ω) z true y y‖ ≤ 1 + A := by
    intro y
    have h1 := hA y y
    have h2 : ‖mE (E n)‖ = 1 := norm_mE hE.le
    have h3 : STGM sz n (E n) (t n) ω y y = Gres (sz.seqHflow n (t n) ω) z true y y - mE (E n) := by
      simp [STGM, Gt, hz]
    rw [h3] at h1
    calc ‖Gres (sz.seqHflow n (t n) ω) z true y y‖
        = ‖(Gres (sz.seqHflow n (t n) ω) z true y y - mE (E n)) + mE (E n)‖ := by rw [sub_add_cancel]
      _ ≤ ‖Gres (sz.seqHflow n (t n) ω) z true y y - mE (E n)‖ + ‖mE (E n)‖ := norm_add_le _ _
      _ ≤ 1 + A := by linarith
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
    positivity
  -- the two charges
  set Cw : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * z.im)⁻¹ * (1 + A) with hCw
  have hrow : ∀ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n), ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ 2 * Cw := by
    intro b₁
    simp_rw [auxGraph2_pair_sum]
    rw [Finset.sum_add_distrib]
    have h1 := auxGraph2_rowsum_norm_le (sz.seqHflow n (t n) ω) hHerm z hη hg true b₁
    have h2 := auxGraph2_rowsum_norm_le (sz.seqHflow n (t n) ω) hHerm z hη hg false b₁
    have e1 : ∀ b₂ : Zd d (sz.L n), ‖Lloop sz n (E n) (t n) ![true, false] ![b₁, b₂] ω‖ =
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) z ![true, !true] ![b₁, b₂]‖ := fun _ => rfl
    have e2 : ∀ b₂ : Zd d (sz.L n), ‖Lloop sz n (E n) (t n) ![false, true] ![b₁, b₂] ω‖ =
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) z ![false, !false] ![b₁, b₂]‖ := fun _ => rfl
    simp only [e1, e2]
    linarith
  have hcard : ∀ c : Zd d (sz.L n), (((Finset.univ.filter fun b : Zd d (sz.L n) =>
      (zdistInf d (sz.L n) (b - c) : ℝ) ≤ ρ n).card : ℕ) : ℝ) ≤ (2 * ρ n + 1) ^ d := by
    intro c
    have := RBM.Ind.DecayLoopB_card_ball (L := sz.L n) c hρ
    have e : (Finset.univ.filter fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - c) : ℝ) ≤ ρ n) =
        Finset.univ.filter fun u : Zd d (sz.L n) => (zdistInf d (sz.L n) (c - u) : ℝ) ≤ ρ n := by
      refine Finset.filter_congr fun b _ => ?_
      rw [auxGraph2_zdistInf_sub_comm]
    rw [e]; exact this
  have hf0 : ∀ b₁ b₂ : Zd d (sz.L n), 0 ≤ ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ := fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hρ1 : (0 : ℝ) ≤ 2 * ρ n + 1 := by linarith
  have hCw0 : 0 ≤ Cw := by
    have h1 := hg (fun _ => 0)
    have : 0 ≤ 1 + A := (norm_nonneg _).trans h1
    positivity
  unfold lwXiSq
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · -- first part
    rw [Finset.sum_comm]
    -- inner bound for fixed b₁
    have hin : ∀ b₁ : Zd d (sz.L n),
        ∑ a₂ : Zd d (sz.L n), ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
          ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
            ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ (2 * ρ n + 1) ^ d * (2 * Cw) := by
      intro b₁
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      calc _ ≤ ∑ b₂ : Zd d (sz.L n), (2 * ρ n + 1) ^ d *
            ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
              ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ := by
            refine Finset.sum_le_sum fun b₂ _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            have := RBM.Ind.DecayLoopB_card_ball (L := sz.L n) b₂ hρ
            exact mul_le_mul_of_nonneg_right this (hf0 b₁ b₂)
        _ = (2 * ρ n + 1) ^ d * ∑ b₂ : Zd d (sz.L n),
            ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
              ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ := by rw [Finset.mul_sum]
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

end Basic2


/-! ## 3. The `≺` helpers and the deterministic comparisons -/

section PrecHelpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {size : ℕ → ℕ}

/-- A failure event of `(ξ, ζ)` that is eventually contained in the failure event of one domination
`(ξ₁, ζ₁)` (the parameter types may differ). -/
private theorem auxGraph2_prec_of_imp {U V : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
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
private theorem auxGraph2_prec_of_imp_union (hsize : Tendsto size atTop atTop) {U V₁ V₂ : ℕ → Type*}
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

/-- `‖G_t - M‖_max ≤ W^{-ε₁/2}` holds w.h.p. under the entry law `‖G_t - M‖_max ≺ W^{-ε₁}`
(`N^{τ} W^{-ε₁} ≤ W^{-ε₁/2}` at `τ = 𝔠 ε₁/2`, `W ≥ N^𝔠`; the event `Ω(t, ε₁/2)` of `lem_GbEXP`). -/
private theorem auxGraph2_whp_entry (E t : ℕ → ℝ) {𝔠 ε₁ : ℝ} (h𝔠 : 0 < 𝔠) (hε₁ : 0 < ε₁)
    (hband : sz.Bandwidth 𝔠)
    (hent : Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁))) :
    sz.Whp (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖STGM sz n (E n) (t n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2))}) := by
  have hτ : 0 < 𝔠 * ε₁ / 2 := by positivity
  refine HighProbAt.mono (Sizes.Prec.whp sz hent hτ) ?_
  filter_upwards [hband] with n hb
  intro ω hω x y
  have h1 : ‖STGM sz n (E n) (t n) ω x y‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) := hω (x, y)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) := by
    have := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₁ / 2) hτ.le
    have e : 𝔠 * ε₁ / 2 / 𝔠 = ε₁ / 2 := by field_simp
    rwa [e] at this
  calc ‖STGM sz n (E n) (t n) ω x y‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) := h1
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hW.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) := by
        rw [← Real.rpow_add hW]; congr 1; ring

/-- **Removing the indicator of `Ω(t, A)`** (`STindMax`) from a domination `1(Ω) ξ ≺ ζ` when
`‖G_t - M‖_max ≤ A` holds w.h.p. -/
private theorem auxGraph2_remove_indicator (E t A : ℕ → ℝ) (hsize : sz.SizeTendsto)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hΩ : sz.Whp (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖STGM sz n (E n) (t n) ω x y‖ ≤ A n}))
    (h : Prec sz (fun n u ω => STindMax sz n (E n) (t n) (A n) ω * ξ n u ω) ζ) :
    Prec sz ξ ζ := by
  refine RBM.Ind.PerTimeCalc.Unif.stochDom_of_indicator (sz.tendsto_size hsize)
    (Ωs := fun n _ => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖STGM sz n (E n) (t n) ω x y‖ ≤ A n}) ?_ ?_
  · exact HighProbAt.mono hΩ (Eventually.of_forall fun n ω hω u => hω)
  · have e : (fun n (u : U n) ω => ({ω : sz.SeqΩ | ∀ x y : Idx d (sz.L n) (sz.W n),
        ‖STGM sz n (E n) (t n) ω x y‖ ≤ A n}).indicator (fun ω => ξ n u ω) ω) =
        fun n u ω => STindMax sz n (E n) (t n) (A n) ω * ξ n u ω := by
      funext n u ω
      unfold STindMax
      by_cases hω : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (E n) (t n) ω x y‖ ≤ A n
      · simp [Set.indicator, hω]
      · simp [Set.indicator, hω]
    rw [e]
    exact h

/-- The flow facts used by the three probabilistic targets: `|E_n| < 2`, `t_n < 1`, admissibility. -/
private theorem auxGraph2_flow_facts {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (h : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (h1 : ∀ n, t n ≤ lemT (z n)) :
    (∀ n, |STflowE z n| < 2) ∧ (∀ n, t n < 1) ∧ sz.Admissible 𝔠 𝔡 := by
  obtain ⟨hA, hE, ht, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε h h1
  exact ⟨fun n => (hE n).trans (by linarith), ht, hA⟩

end SizesHelpers

private theorem auxGraph2_etaT_le_one {E t : ℝ} (hE : |E| < 2) (h0 : 0 ≤ t) (ht : t < 1) :
    etaT E t ≤ 1 := by
  have h1 : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  have h2 : 0 < (mE E).im := mE_im_pos hE
  unfold etaT
  nlinarith

/-- **`Φ(m) ≤ K(ρ) Φ(ℓ)` when `ℓ ≤ 2ρ + m`** (target 3 (c), `(eq:Psi)`): the split at `max(4ρ, 2)`. -/
private theorem auxGraph2_phi_cmp {Φ : ℝ → ℝ} {C₁ C₂ Cc2 ρ : ℝ} (hρ : 0 ≤ ρ)
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
private theorem auxGraph2_ev_poly {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {ρ : ℕ → ℝ}
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

private theorem auxGraph2_card_ball {d L : ℕ} [NeZero L] (c : Zd d L) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (((Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ).card : ℕ) : ℝ) ≤
      (2 * ρ + 1) ^ d := by
  have := RBM.Ind.DecayLoopB_card_ball (L := L) c hρ
  have e : (Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ) =
      Finset.univ.filter fun u : Zd d L => (zdistInf d L (c - u) : ℝ) ≤ ρ := by
    refine Finset.filter_congr fun b _ => ?_
    rw [auxGraph2_zdistInf_sub_comm]
  rw [e]; exact this

/-- **`ξ([a₁],[a₂])² ≲ Φ(|a₁ - a₂|)²` from `(LW_assm)` and `(eq:Psi)`** (target 3 (c), deterministic part):
if every `‖𝓛^{(2)}_{(s,!s),(b₁,b₂)}‖ ≤ B Φ(|b₁ - b₂|)²`, `Φ(m) ≤ K Φ(ℓ)` for `ℓ ≤ 2ρ + m` and
`W^{-d} ≤ C₃² Φ(0)²`, then `ξ² ≤ (2 (2ρ+1)^{2d} B + C₃²) K² Φ(|a₁ - a₂|)²`. -/
private theorem auxGraph2_xiSq_le {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (Φn : ℝ → ℝ) (hρ : 0 ≤ ρ n) {B K C₃ : ℝ} (hB : 0 ≤ B)
    (hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖Lloop sz n (E n) (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
        B * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2)
    (hΦnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ Φn r)
    (hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φn m ≤ K * Φn ℓ)
    (hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ ^ 2 * Φn 0 ^ 2) (a₁ a₂ : Zd d (sz.L n)) :
    lwXiSq sz E t ρ n a₁ a₂ ω ≤
      (2 * (2 * ρ n + 1) ^ (2 * d) * B + C₃ ^ 2) * K ^ 2 *
        Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) ^ 2 := by
  classical
  set ℓ : ℝ := ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) with hℓ
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  set Q : ℝ := K ^ 2 * Φn ℓ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hterm : ∀ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∀ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ 2 * B * Q := by
    intro b₁ hb₁ b₂ hb₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
    set m : ℝ := ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) with hm
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have t1 := auxGraph2_zdistInf_tri_real d (sz.L n) a₁ b₁ a₂
    have t2 := auxGraph2_zdistInf_tri_real d (sz.L n) b₁ b₂ a₂
    have h1 : (zdistInf d (sz.L n) (a₁ - b₁) : ℝ) ≤ ρ n := by
      rw [auxGraph2_zdistInf_sub_comm]; exact hb₁
    have h2 : (zdistInf d (sz.L n) (b₂ - a₂) : ℝ) ≤ ρ n := hb₂
    have hlm : ℓ ≤ 2 * ρ n + m := by
      have := auxGraph2_zdistInf_tri_real d (sz.L n) a₁ b₁ a₂
      have t3 := auxGraph2_zdistInf_tri_real d (sz.L n) b₁ b₂ a₂
      rw [hℓ, hm]
      linarith
    have hΦ : Φn m ≤ K * Φn ℓ := hcmp ℓ m hℓ0 hm0 hlm
    have hsq : Φn m ^ 2 ≤ Q := by
      rw [hQ, ← mul_pow]
      exact pow_le_pow_left₀ (hΦnn m hm0) hΦ 2
    rw [auxGraph2_pair_sum]
    have e1 := hloop true b₁ b₂
    have e2 := hloop false b₁ b₂
    have e3 : B * Φn m ^ 2 ≤ B * Q := mul_le_mul_of_nonneg_left hsq hB
    simp only [Bool.not_true, Bool.not_false] at e1 e2
    linarith
  have hfirst : ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
        ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q := by
    calc _ ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
          ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
            2 * B * Q :=
          Finset.sum_le_sum fun b₁ hb₁ => Finset.sum_le_sum fun b₂ hb₂ => hterm b₁ hb₁ b₂ hb₂
      _ = (((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
          ((((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
            (2 * B * Q)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ρ n + 1) ^ d * ((2 * ρ n + 1) ^ d * (2 * B * Q)) := by
          have c1 := auxGraph2_card_ball (d := d) a₁ hρ
          have c2 := auxGraph2_card_ball (d := d) a₂ hρ
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
  unfold lwXiSq
  calc _ ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q + C₃ ^ 2 * Q := add_le_add hfirst hsecond
    _ = _ := by rw [hQ]; ring


/-- `N^{𝔠 ε₁/2} W^{-ε₁} ≤ W^{-ε₁/2} ≤ 1` (`W ≥ N^𝔠`): the entry law at `τ = 𝔠 ε₁/2` is `≤ W^{-ε₁/2}`. -/
private theorem auxGraph2_pow_small {d : ℕ} (sz : Sizes d) (n : ℕ) {𝔠 ε₁ : ℝ} (h𝔠 : 0 < 𝔠) (hε₁ : 0 < ε₁)
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

private theorem auxGraph2_rpow_nat (X : ℝ) (hX : 0 ≤ X) (x : ℝ) (k : ℕ) : (X ^ x) ^ k = X ^ (x * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]

/-- The arithmetic of target 3 (c), in powers of `u = N^{τ/8}`. -/
private theorem auxGraph2_num {u A₁ K2 S : ℝ} (hu : 1 ≤ u) (hA : 2 * A₁ ≤ u ^ 2) (hC : S ≤ u ^ 4)
    (hK : K2 ≤ u ^ 2) (h2 : 2 ≤ u ^ 8) (hA0 : 0 ≤ A₁) (hS0 : 0 ≤ S) (hK0 : 0 ≤ K2) :
    (2 * A₁ * u ^ 4 + S) * K2 ≤ (u ^ 8) ^ 2 := by
  have hu0 : 0 ≤ u := by linarith
  have h1 : 2 * A₁ * u ^ 4 ≤ u ^ 6 := by
    calc _ ≤ u ^ 2 * u ^ 4 := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = u ^ 6 := by ring
  have h2' : u ^ 4 ≤ u ^ 6 := pow_le_pow_right₀ hu (by norm_num)
  have h3 : 2 * A₁ * u ^ 4 + S ≤ 2 * u ^ 6 := by linarith
  have h4 : (2 * A₁ * u ^ 4 + S) * K2 ≤ 2 * u ^ 6 * u ^ 2 :=
    mul_le_mul h3 hK hK0 (by positivity)
  have h5 : 2 * u ^ 6 * u ^ 2 = 2 * u ^ 8 := by ring
  have h6 : 2 * u ^ 8 ≤ (u ^ 8) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 (pow_nonneg hu0 8)
    nlinarith
  linarith

/-! ## 4. `claim:xi` (target 3) -/

/-- **Target 3, `claim:xi`** (`7_8:884-890`, `(eq:Gbyxi2)`): under `(LW_assm)` for a class `Φ` with `(eq:Psi)`, and
`‖G_t - M‖_max ≺ W^{-ε₁}`, the variables `lwXiVar` at a radius `ρ = N^{o(1)}` satisfy the merged `LWXi`: symmetric,
non-negative, `ξ([a₁],[a₂]) ≺ Ψ_t(|a₁ - a₂|)` and `Σ_{a₂} ξ([a₁],[a₂])² ≺ (W^d η_t)⁻¹` (Ward's identity). -/
def LWXiClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2 sz (STflowE z) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ) →
            LWXi sz (STflowE z) t Φ (lwXiVar sz (STflowE z) t ρ)

theorem lwXiClaim_holds (d : ℕ) : LWXiClaim d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ C₁ C₂ C₃ Cc Φ hΦ hL ε₁ hε₁ hent ρ hρ0 hρ
  obtain ⟨hE, htlt, hadm⟩ := auxGraph2_flow_facts sz hκ hε hflow ht1
  have hsize : sz.SizeTendsto := hadm.2.2.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hd0 : 0 < d := by omega
  refine ⟨fun n α β ω => ⟨lwXiVar_nonneg sz _ t ρ n α β ω, lwXiVar_symm sz _ t ρ n α β ω⟩, ?_, ?_⟩
  · -- conjunct 2: `ξ ≺ Φ(|a₁ - a₂|)`
    obtain ⟨hcls, hC3, hwin⟩ := hΦ.2.1
    obtain ⟨hanti, hC₁, hC₂, hrel1, hrel2⟩ := hΦ.2.2
    refine auxGraph2_prec_of_imp hL ?_
    intro τ hτ
    refine ⟨τ / 2, half_pos hτ, ?_⟩
    set K₀ : ℝ := C₁ * 2 ^ C₂ + Cc 2 + Cc 2 * C₁ with hK₀
    have p1 := auxGraph2_ev_poly sz hsize hρ0 hρ (a := 2) (b := 1) (c := 2) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) (τ := τ / 4) (by positivity)
    have p2 := auxGraph2_ev_poly sz hsize hρ0 hρ (a := 4) (b := 2) (c := |K₀|) (e := C₂)
      (by norm_num) (by norm_num) (abs_nonneg _) (by linarith) (τ := τ / 8) (by positivity)
    have p3 : ∀ᶠ n in atTop, C₃ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop _
    have p4 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
      ((tendsto_rpow_atTop hτ).comp hsize).eventually_ge_atTop _
    filter_upwards [hcls, hwin, hrel1 2 (by norm_num), hrel2, p1, p2, p3, p4,
      hsize.eventually_ge_atTop 1] with n hcl hwn hr1 hr2 q1 q2 q3 q4 hX1
    intro ω p hp
    by_contra hno
    push Not at hno
    set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
    have hX0 : 0 < X := by linarith
    set u : ℝ := X ^ (τ / 8) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow hX1 (by positivity)
    have hpow : ∀ k : ℕ, X ^ (τ / 8 * (k : ℝ)) = u ^ k := fun k =>
      (auxGraph2_rpow_nat X hX0.le _ k).symm
    have hΦn0 : ∀ r : ℝ, 0 ≤ r → 0 < Φ n r := fun r hr => (hcl r hr).1
    have hCc2 : 0 < Cc 2 := by
      by_contra h
      push Not at h
      have := hr1 0 le_rfl (by norm_num)
      have := hΦn0 0 le_rfl
      have := hΦn0 1 zero_le_one
      nlinarith
    have hK₀pos : 0 < K₀ := by
      have : 0 < C₁ * 2 ^ C₂ := by positivity
      have : 0 < Cc 2 * C₁ := by positivity
      rw [hK₀]; linarith
    set P : ℝ := (4 * ρ n + 2) ^ C₂ with hP
    have hP0 : 0 ≤ P := Real.rpow_nonneg (by have := hρ0 n; linarith) _
    set Kn : ℝ := K₀ * P with hKn
    have hKn0 : 0 ≤ Kn := by positivity
    -- the loop bound on the complement of the bad event
    have hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
        ‖Lloop sz n (STflowE z n) (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
          X ^ (τ / 2) * Φ n ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2 := fun s b₁ b₂ =>
      hno (s, b₁, b₂)
    have hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φ n m ≤ Kn * Φ n ℓ := by
      intro ℓ m hℓ hm hlm
      exact auxGraph2_phi_cmp (Φ := Φ n) (hρ0 n) (hanti n) hΦn0 hC₁ hC₂ hCc2 hr1 hr2 hℓ hm hlm
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
    have hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ ^ 2 * Φ n 0 ^ 2 := by
      have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        rw [auxGraph2_rpow_nat _ hWpos.le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring,
          Real.rpow_neg hWpos.le, Real.rpow_natCast]
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 := e.symm
        _ ≤ (C₃ * Φ n 0) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hWpos.le _) hwn 2
        _ = C₃ ^ 2 * Φ n 0 ^ 2 := by ring
    have hbound := auxGraph2_xiSq_le sz (STflowE z) t ρ n ω (Φ n) (hρ0 n) (B := X ^ (τ / 2)) (K := Kn)
      (C₃ := C₃) (Real.rpow_nonneg hX0.le _) hloop (fun r hr => (hΦn0 r hr).le) hcmp hW p.1 p.2
    set ℓ : ℝ := ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ) with hℓ
    have hp' : X ^ τ * Φ n ℓ < lwXiVar sz (STflowE z) t ρ n p.1 p.2 ω := hp
    have e2 : X ^ (τ / 4) = u ^ 2 := by rw [← hpow 2]; congr 1; push_cast; ring
    have e4 : X ^ (τ / 2) = u ^ 4 := by rw [← hpow 4]; congr 1; push_cast; ring
    have e8 : X ^ τ = u ^ 8 := by rw [← hpow 8]; congr 1; push_cast; ring
    have hA1 : 2 * (2 * ρ n + 1) ^ (2 * d) ≤ u ^ 2 := by
      have := q1
      rw [Real.rpow_natCast, e2] at this
      exact this
    have hKn : Kn ^ 2 ≤ u ^ 2 := by
      have h1 : Kn ≤ u := by
        calc Kn = K₀ * P := rfl
          _ ≤ |K₀| * P := mul_le_mul_of_nonneg_right (le_abs_self _) hP0
          _ ≤ u := q2
      exact pow_le_pow_left₀ hKn0 h1 2
    have hnum := auxGraph2_num hu1 hA1 (by rw [← e4]; exact q3) hKn (by rw [← e8]; exact q4)
      (pow_nonneg (by have := hρ0 n; linarith) _) (sq_nonneg _) (sq_nonneg _)
    rw [e4] at hbound
    have hΦℓ := (hΦn0 ℓ (Nat.cast_nonneg _)).le
    have hsq : lwXiSq sz (STflowE z) t ρ n p.1 p.2 ω ≤ (X ^ τ * Φ n ℓ) ^ 2 := by
      calc _ ≤ _ := hbound
        _ = ((2 * (2 * ρ n + 1) ^ (2 * d) * u ^ 4 + C₃ ^ 2) * Kn ^ 2) * Φ n ℓ ^ 2 := by ring
        _ ≤ (u ^ 8) ^ 2 * Φ n ℓ ^ 2 := mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
        _ = (X ^ τ * Φ n ℓ) ^ 2 := by rw [e8]; ring
    have hle : lwXiVar sz (STflowE z) t ρ n p.1 p.2 ω ≤ X ^ τ * Φ n ℓ :=
      Real.sqrt_le_iff.2 ⟨by positivity, hsq⟩
    linarith
  · -- conjunct 3: `Σ_β ξ² ≺ (W^d η)⁻¹` (Ward's identity on `‖G - M‖_max ≤ 1`)
    refine auxGraph2_prec_of_imp hent ?_
    intro τ hτ
    refine ⟨𝔠 * ε₁ / 2, by positivity, ?_⟩
    have p1 := auxGraph2_ev_poly sz hsize hρ0 hρ (a := 2) (b := 1) (c := 5) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) hτ
    filter_upwards [hadm.2.2.2.1, p1] with n hb q1
    intro ω α hα
    by_contra hno
    push Not at hno
    have hsm := auxGraph2_pow_small sz n h𝔠 hε₁ hb
    have hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω x y‖ ≤ 1 := fun x y =>
      ((hno (x, y)).trans hsm.1).trans hsm.2
    have hw := lwXi_ward_sum sz (STflowE z) t ρ n (hE n) (htlt n) (hρ0 n) ω hA α
    set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
    set Q : ℝ := ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ with hQ
    have hα' : X ^ τ * Q < ∑ β, lwXiVar sz (STflowE z) t ρ n α β ω ^ 2 := hα
    simp_rw [auxGraph2_xiVar_sq] at hα'
    have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE n) (htlt n)
    have hη1 : etaT (STflowE z n) (t n) ≤ 1 := auxGraph2_etaT_le_one (hE n) (ht0 n) (htlt n)
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
      have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
      positivity
    have hQ0 : 0 < Q := inv_pos.2 (mul_pos hWd hη0)
    have hWQ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Q :=
      inv_anti₀ (mul_pos hWd hη0) (by nlinarith)
    have hρ1 : (1 : ℝ) ≤ 2 * ρ n + 1 := by have := hρ0 n; linarith
    have hA01 : (2 * ρ n + 1) ^ d ≤ (2 * ρ n + 1) ^ (2 * d) :=
      pow_le_pow_right₀ hρ1 (by omega)
    have hA1pos : 0 ≤ (2 * ρ n + 1) ^ (2 * d) := pow_nonneg (by linarith) _
    have hq : 5 * (2 * ρ n + 1) ^ (2 * d) ≤ X ^ τ := by
      have := q1
      rwa [Real.rpow_natCast] at this
    have hsum : ∑ β, lwXiSq sz (STflowE z) t ρ n α β ω ≤ 5 * (2 * ρ n + 1) ^ (2 * d) * Q := by
      refine hw.trans ?_
      have h1 : (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (2 * ρ n + 1) ^ (2 * d) * Q :=
        mul_le_mul hA01 hWQ (by positivity) hA1pos
      nlinarith
    have := mul_le_mul_of_nonneg_right hq hQ0.le
    linarith


/-! ## 5. `(eq:Gbyxi)` off the diagonal and entrywise (targets 4 and 5) -/

/-- **Target 4, `(eq:Gbyxi)` off the diagonal** (`7_8:878-880`, from `(GijGEX)`): uniformly in `x ≠ y` and in the blocks
`a`, `b` at `zdistD`-distance `≤ R` from `[x]`, `[y]` (the premise `hξ` of the merged `LWGtoAG`), `|G_{xy}| ≺ ξ(a, b)`
whenever `2R + 1 ≤ ρ`. -/
def LWGbyXi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₁ : ℝ, 0 < ε₁ →
        Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
          (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ ρ R : ℕ → ℝ, (∀ n, 0 ≤ R n) → (∀ n, 2 * R n + 1 ≤ ρ n) →
          Prec sz (U := fun n => {q : (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ×
              (Zd d (sz.L n) × Zd d (sz.L n)) // q.1.1 ≠ q.1.2 ∧
              (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.1).1 - q.2.1) : ℝ) ≤ R n ∧
              (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.2).1 - q.2.2) : ℝ) ≤ R n})
            (fun n q ω => ‖Gt sz n (STflowE z n) (t n) true ω q.1.1.1 q.1.1.2‖)
            (fun n q ω => lwXiVar sz (STflowE z) t ρ n q.1.2.1 q.1.2.2 ω)

theorem lwGbyXi_holds (d : ℕ) : LWGbyXi d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₁ hε₁ hent ρ R hR hρR
  obtain ⟨hE, htlt, hadm⟩ := auxGraph2_flow_facts sz hκ hε hflow ht1
  have hsize : sz.SizeTendsto := hadm.2.2.1
  have hij : STGijGEX sz (STflowE z) t (ε₁ / 2) :=
    (RBM.Green.stGbEXP_holds hd).2.1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 (ε₁ / 2) (half_pos hε₁)
  have hΩ := auxGraph2_whp_entry sz (STflowE z) t hadm.1 hε₁ hadm.2.2.2.1 hent
  have h1 : Prec sz (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
      (fun n p ω => ‖Gt sz n (STflowE z n) (t n) true ω p.1.1 p.1.2‖ ^ 2)
      (fun n p ω => STgexRHS sz n (STflowE z n) (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2)) :=
    auxGraph2_remove_indicator sz (STflowE z) t (fun n => ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2))) hsize hΩ hij
  refine auxGraph2_prec_of_imp h1 ?_
  intro τ hτ
  refine ⟨τ * 2, by positivity, Eventually.of_forall fun n ω q hq => ?_⟩
  refine ⟨⟨q.1.1, q.2.1⟩, ?_⟩
  set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hq' : X ^ τ * lwXiVar sz (STflowE z) t ρ n q.1.2.1 q.1.2.2 ω <
      ‖Gt sz n (STflowE z n) (t n) true ω q.1.1.1 q.1.1.2‖ := hq
  have hsq := pow_lt_pow_left₀ hq' (mul_nonneg (Real.rpow_nonneg hX0 _)
    (lwXiVar_nonneg sz (STflowE z) t ρ n _ _ ω)) (two_ne_zero)
  have hle := lwXi_gexRHS_le sz (STflowE z) t ρ n (hR n) (hρR n) q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 ω
    q.2.2.1 q.2.2.2
  have e1 : (X ^ τ * lwXiVar sz (STflowE z) t ρ n q.1.2.1 q.1.2.2 ω) ^ 2 =
      X ^ (τ * 2) * lwXiSq sz (STflowE z) t ρ n q.1.2.1 q.1.2.2 ω := by
    rw [mul_pow, auxGraph2_rpow_nat X hX0, auxGraph2_xiVar_sq]
    norm_num
  show X ^ (τ * 2) * STgexRHS sz n (STflowE z n) (t n) ω (STblk sz n q.1.1.1) (STblk sz n q.1.1.2) <
    ‖Gt sz n (STflowE z n) (t n) true ω q.1.1.1 q.1.1.2‖ ^ 2
  calc _ ≤ X ^ (τ * 2) * lwXiSq sz (STflowE z) t ρ n q.1.2.1 q.1.2.2 ω :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hX0 _)
    _ = _ := e1.symm
    _ < _ := hsq

/-- **`hξ` of the merged `LWGtoAG` from `(eq:Gbyxi)`** (the type match with LW-11a): for `c ≥ 0` and a sample `ω` with
`‖G_{xy}‖ ≤ c ξ(a, b)` on the `R`-balls, the edge variables `ξ = c · lwXiVar` are non-negative and satisfy the
premise `hξ` of `lwGtoAG_holds` verbatim for the sample data `D = lwSampleData sz n (zt E t) t M S Sp ω`
(`D.G = Gt` by `rfl`). -/
theorem lwGbyXi_hxi {d : ℕ} (sz : Sizes d) (E t ρ R : ℕ → ℝ) (n : ℕ)
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ω : sz.SeqΩ) {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)), x ≠ y →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖Gt sz n (E n) (t n) true ω x y‖ ≤ c * lwXiVar sz E t ρ n a b ω) :
    (∀ a b : Zd d (sz.L n), 0 ≤ (fun a b : Zd d (sz.L n) => c * lwXiVar sz E t ρ n a b ω) a b) ∧
    (∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)), x ≠ y →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n →
      ‖(lwSampleData sz n (zt (E n) (t n)) (t n) M S Sp ω).G x y‖ ≤
        (fun a b : Zd d (sz.L n) => c * lwXiVar sz E t ρ n a b ω) a b) :=
  ⟨fun a b => mul_nonneg hc (lwXiVar_nonneg sz E t ρ n a b ω), fun x y a b hxy hx hy => h x y a b hxy hx hy⟩

/-- **Target 5, `(eq:Gbyxi)` entrywise: `|(G - M)_{xy}| ≺ Ψ_t(0)`** (`7_8:880`, the `Ψ_t(0) δ_{xy}` term, from `(GiiGEX)`
and `(LW_assm)`): the premises `|G_{xy}| ≤ Ψ`, `|G_{xx} - m| ≤ Ψ` of the merged `LWGtoAG` at `Ψ = Φ n 0`. -/
def LWEntryPsi (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
          LWLoop2 sz (STflowE z) t Φ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖)
            (fun n _ _ => Φ n 0)

theorem lwEntryPsi_holds (d : ℕ) : LWEntryPsi d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ C₁ C₂ C₃ Cc Φ hΦ hL ε₁ hε₁ hent
  obtain ⟨hE, htlt, hadm⟩ := auxGraph2_flow_facts sz hκ hε hflow ht1
  have hsize : sz.SizeTendsto := hadm.2.2.1
  have hii : STGiiGEX sz (STflowE z) t (ε₁ / 2) :=
    (RBM.Green.stGbEXP_holds hd).1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 (ε₁ / 2) (half_pos hε₁)
  have hΩ := auxGraph2_whp_entry sz (STflowE z) t hadm.1 hε₁ hadm.2.2.2.1 hent
  have h1 : Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖ ^ 2)
      (fun n _ ω => STmaxLoop2 sz n (STflowE z n) (t n) ω) :=
    auxGraph2_remove_indicator sz (STflowE z) t (fun n => ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2))) hsize hΩ hii
  refine auxGraph2_prec_of_imp_union (sz.tendsto_size hsize) h1 hL ?_
  intro τ hτ
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hΦ.2.1.1] with n hcl
  intro ω p hp
  by_contra hno
  push Not at hno
  obtain ⟨hno1, hno2⟩ := hno
  set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hXτ : 0 ≤ X ^ τ := Real.rpow_nonneg hX0 _
  have hΦ0 : 0 < Φ n 0 := (hcl 0 le_rfl).1
  have hmax : STmaxLoop2 sz n (STflowE z n) (t n) ω ≤ X ^ τ * Φ n 0 ^ 2 := by
    unfold Sizes.STmaxLoop2
    refine Finset.sup'_le _ _ fun pr _ => ?_
    have h1 := hno2 (false, pr.1, pr.2)
    have h2 : Φ n ((zdistInf d (sz.L n) (pr.1 - pr.2) : ℕ) : ℝ) ≤ Φ n 0 :=
      hΦ.2.2.1 n (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have h3 : 0 < Φ n ((zdistInf d (sz.L n) (pr.1 - pr.2) : ℕ) : ℝ) := (hcl _ (Nat.cast_nonneg _)).1
    have h4 : Φ n ((zdistInf d (sz.L n) (pr.1 - pr.2) : ℕ) : ℝ) ^ 2 ≤ Φ n 0 ^ 2 :=
      pow_le_pow_left₀ h3.le h2 2
    exact h1.trans (mul_le_mul_of_nonneg_left h4 hXτ)
  have hG := hno1 p
  have hp' : X ^ τ * Φ n 0 < ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖ := hp
  have hsq := pow_lt_pow_left₀ hp' (mul_nonneg hXτ hΦ0.le) (two_ne_zero)
  have : ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖ ^ 2 ≤ (X ^ τ * Φ n 0) ^ 2 := by
    calc _ ≤ X ^ τ * STmaxLoop2 sz n (STflowE z n) (t n) ω := hG
      _ ≤ X ^ τ * (X ^ τ * Φ n 0 ^ 2) := mul_le_mul_of_nonneg_left hmax hXτ
      _ = (X ^ τ * Φ n 0) ^ 2 := by ring
  linarith

/-! ## 6. The radii (target 6) -/

/-- **Target 6, polylogarithmic radii are `N^{o(1)}`**: the radius premise of target 3 for `ρ = C (log W)^K + C'`. -/
def LWXiRad : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), sz.SizeTendsto → ∀ C C' K : ℝ, 0 ≤ C → 0 ≤ C' → 0 ≤ K →
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      C * Real.log ((sz.W n : ℕ) : ℝ) ^ K + C' + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ

theorem lwXiRad_holds : LWXiRad := by
  intro d sz hsz C C' K hC hC' hK τ hτ
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso
      subst h
      have h1 : (fun n => ((sz.size n : ℕ) : ℝ)) = fun _ => (1 : ℝ) := by
        funext n; simp [Sizes.size]
      have h2 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsz
      rw [h1] at h2
      exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds h2
    · exact h
  have hlit := (isLittleO_log_rpow_rpow_atTop K hτ).def (c := 1 / (2 * (C + 1))) (by positivity)
  have h1 := hsz.eventually hlit
  have h2 : ∀ᶠ n in atTop, C' + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ / 2 :=
    ((((tendsto_rpow_atTop hτ).comp hsz).atTop_div_const (by norm_num : (0 : ℝ) < 2)).eventually_ge_atTop
      (C' + 1))
  filter_upwards [h1, h2, hsz.eventually_ge_atTop 1] with n hn1 hn2 hX1
  set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hWX : ((sz.W n : ℕ) : ℝ) ≤ X := by
    have hL : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
    have h : sz.W n ≤ sz.size n :=
      calc sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
        _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow hd.ne' _
    exact Nat.cast_le.2 h
  have hlog : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log (by linarith) hWX
  have hlog0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
  have hXlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have e1 : Real.log ((sz.W n : ℕ) : ℝ) ^ K ≤ Real.log X ^ K :=
    Real.rpow_le_rpow hlog0 hlog hK
  have e2 : Real.log X ^ K ≤ 1 / (2 * (C + 1)) * X ^ τ := by
    have := hn1
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg hXlog0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at this
  have hXτ : 0 ≤ X ^ τ := Real.rpow_nonneg (by linarith) _
  have e3 : C * (1 / (2 * (C + 1)) * X ^ τ) ≤ X ^ τ / 2 := by
    have : C / (2 * (C + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc C * (1 / (2 * (C + 1)) * X ^ τ) = (C / (2 * (C + 1))) * X ^ τ := by ring
      _ ≤ 1 / 2 * X ^ τ := mul_le_mul_of_nonneg_right this hXτ
      _ = X ^ τ / 2 := by ring
  have := mul_le_mul_of_nonneg_left (e1.trans e2) hC
  linarith


/-- Every entry of `G_t - M` is at most the sum of all entries (used to discharge `hA` at a concrete bound). -/
private theorem auxGraph2_entry_le_sum {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖STGM sz n E t ω x y‖ ≤ ∑ x', ∑ y', ‖STGM sz n E t ω x' y'‖ :=
  (Finset.single_le_sum (f := fun y' => ‖STGM sz n E t ω x y'‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ y)).trans
    (Finset.single_le_sum (f := fun x' => ∑ y', ‖STGM sz n E t ω x' y'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x))

/-! ## 7. Compiled nonempty instances at the merged `d = 3` data

`d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`), `z0`, `flow_z0`, `tInst ≡ 1/16`, the class `Φ0 ≡ W⁻¹` with
`psiAll0` (`C₁ = C₂ = 2`, `C₃ = 1`, `Cc ≡ 1`, `ε₀ = 1/20`), `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `ε₁ = 1/20`,
`R0 n = (log W_n)^{3/2}`, `ρ0 n = 2 (log W_n)^{3/2} + 1`.  What stays a hypothesis of an instance is another gate's
stochastic input: `LWLoop2 sz0 (STflowE z0) tInst Φ0` and the entry law `‖G_t - M‖_max ≺ W^{-ε₁}`. -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- The radius `R0 n = (log W_n)^{3/2}` (the radius of the merged tail `lwTail_log32`). -/
private noncomputable def auxGraph2_R0 : ℕ → ℝ := fun n => Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)

/-- The radius `ρ0 n = 2 (log W_n)^{3/2} + 1 = 2 R0 n + 1`. -/
private noncomputable def auxGraph2_ρ0 : ℕ → ℝ := fun n =>
  2 * Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + 1

private theorem auxGraph2_R0_nonneg (n : ℕ) : 0 ≤ auxGraph2_R0 n :=
  Real.rpow_nonneg (Real.log_nonneg (RBM.Gauss.LWInst.one_le_W n)) _

private theorem auxGraph2_ρ0_nonneg (n : ℕ) : 0 ≤ auxGraph2_ρ0 n := by
  have := auxGraph2_R0_nonneg n
  unfold auxGraph2_R0 at this
  unfold auxGraph2_ρ0
  linarith

private theorem auxGraph2_ρ0_ge (n : ℕ) : 2 * auxGraph2_R0 n + 1 ≤ auxGraph2_ρ0 n := le_rfl

/-- The radius premise of target 3 from target 6 at `C = 2`, `C' = 1`, `K = 3/2`. -/
private theorem auxGraph2_ρ0_rad :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, auxGraph2_ρ0 n + 1 ≤ ((sz0.size n : ℕ) : ℝ) ^ τ := fun τ hτ =>
  lwXiRad_holds sz0 sz0_tendsto 2 1 (3 / 2) (by norm_num) (by norm_num) (by norm_num) τ hτ

/-- The entry law `‖G_t - M‖_max ≺ W^{-ε₁}` at `ε₁ = 1/20` (a stochastic input, kept as a hypothesis). -/
private def auxGraph2_Entry : Prop :=
  Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
    (fun n p ω => ‖STGM sz0 n (STflowE z0 n) (tInst n) ω p.1 p.2‖)
    (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))

/-- Two distinct points of the fine lattice, at every size. -/
private theorem auxGraph2_exists_ne (n : ℕ) : ∃ x y : Idx 3 (sz0.L n) (sz0.W n), x ≠ y := by
  have h3 := sz0.three_le_L n
  have h1 := sz0.W_pos n
  have : Nontrivial (ZMod (sz0.W n * sz0.L n)) :=
    ZMod.nontrivial_iff.2 (by nlinarith)
  refine ⟨0, Pi.single 0 1, fun h => ?_⟩
  have := congrFun h 0
  simp at this

/-- **Instance 1** (target 2): `W^{-d} ≤ ξ([a],[a])²`, `ξ([a],[a]) > 0`, at every size, block and sample. -/
example : ∀ (n : ℕ) (a : Zd 3 (sz0.L n)) (ω : sz0.SeqΩ),
    (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ lwXiSq sz0 (STflowE z0) tInst auxGraph2_ρ0 n a a ω ∧
      0 < lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 n a a ω := by
  intro n a ω
  have h := lwXiSq_ge_W sz0 (STflowE z0) tInst auxGraph2_ρ0 n (auxGraph2_ρ0_nonneg n) a ω
  have hW : (0 : ℝ) < (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ := by
    have := RBM.Gauss.LWInst.one_le_W n
    positivity
  exact ⟨h, Real.sqrt_pos.2 (lt_of_lt_of_le hW h)⟩

/-- **Instance 1** (target 2): the first conjunct of `LWXi` for `lwXiVar` at `n = 0`. -/
example (a b : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) :
    0 ≤ lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a b ω ∧
      lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a b ω =
        lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 b a ω :=
  ⟨lwXiVar_nonneg sz0 _ _ _ 0 a b ω, lwXiVar_symm sz0 _ _ _ 0 a b ω⟩

/-- **Instance 1** (target 2, `(eq:Gbyxi)`): `lwXi_gexRHS_le` at `n = 0` for two distinct points, with the blocks
`a = [x]`, `b = [y]` and `R = R0 0`, `ρ = ρ0 0`. -/
example (ω : sz0.SeqΩ) :
    ∃ x y : Idx 3 (sz0.L 0) (sz0.W 0), x ≠ y ∧
      STgexRHS sz0 0 (STflowE z0 0) (tInst 0) ω (STblk sz0 0 x) (STblk sz0 0 y) ≤
        lwXiSq sz0 (STflowE z0) tInst auxGraph2_ρ0 0 (STblk sz0 0 x) (STblk sz0 0 y) ω := by
  obtain ⟨x, y, hxy⟩ := auxGraph2_exists_ne 0
  refine ⟨x, y, hxy, lwXi_gexRHS_le sz0 (STflowE z0) tInst auxGraph2_ρ0 0 (auxGraph2_R0_nonneg 0)
    (auxGraph2_ρ0_ge 0) x y (STblk sz0 0 x) (STblk sz0 0 y) ω ?_ ?_⟩
  · show (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - (split 3 (sz0.L 0) (sz0.W 0) x).1) : ℝ) ≤ _
    rw [sub_self, zdistD_zero, Nat.cast_zero]; exact auxGraph2_R0_nonneg 0
  · show (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - (split 3 (sz0.L 0) (sz0.W 0) y).1) : ℝ) ≤ _
    rw [sub_self, zdistD_zero, Nat.cast_zero]; exact auxGraph2_R0_nonneg 0

/-- **Instance 1** (target 2, the Ward part): `lwXi_ward_sum` at `n = 0`, `A` the sum of the entries of `G_t - M`
(so the hypothesis `hA` holds), every sample and block. -/
example (ω : sz0.SeqΩ) (a₁ : Zd 3 (sz0.L 0)) :
    ∑ a₂, lwXiSq sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a₁ a₂ ω ≤
      2 * (2 * auxGraph2_ρ0 0 + 1) ^ (2 * 3) * ((((sz0.W 0 : ℕ) : ℝ) ^ 3 * etaT (STflowE z0 0) (tInst 0))⁻¹ *
        (1 + ∑ x, ∑ y, ‖STGM sz0 0 (STflowE z0 0) (tInst 0) ω x y‖)) +
      (2 * auxGraph2_ρ0 0 + 1) ^ 3 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ := by
  refine lwXi_ward_sum sz0 (STflowE z0) tInst auxGraph2_ρ0 0 (abs_lemE_lt_two (z0_im_pos 0))
    (by simp only [tInst]; norm_num) (auxGraph2_ρ0_nonneg 0) ω (fun x y => ?_) a₁
  exact auxGraph2_entry_le_sum sz0 0 (STflowE z0 0) (tInst 0) ω x y

/-- **Instance 2** (target 3, `claim:xi`): `LWXi` for `ξ = lwXiVar` at the merged data; the premises `LWLoop2` and the
entry law stay hypotheses, the radius premise is target 6. -/
example (hL : LWLoop2 sz0 (STflowE z0) tInst RBM.Gauss.LWInst.Φ0) (hent : auxGraph2_Entry) :
    LWXi sz0 (STflowE z0) tInst RBM.Gauss.LWInst.Φ0 (lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0) :=
  lwXiClaim_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst RBM.Gauss.LWInst.tInst_range.1 RBM.Gauss.LWInst.tInst_range.2 (1 / 20) 2 2 1
    (fun _ => 1) RBM.Gauss.LWInst.Φ0 RBM.Gauss.LWInst.psiAll0 hL (1 / 20) (by norm_num) hent
    auxGraph2_ρ0 auxGraph2_ρ0_nonneg auxGraph2_ρ0_rad

/-- **Instance 3** (the consumer): the merged `LWAnp` (`h`, owed to LW-02) fed with `ξ = lwXiVar`. -/
example (h : LWAnp 3) (hL : LWLoop2 sz0 (STflowE z0) tInst RBM.Gauss.LWInst.Φ0) (hent : auxGraph2_Entry) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 n α β ω)
          (fun _ => ab.1) (fun _ => ab.2))
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          RBM.Gauss.LWInst.Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 *
          RBM.Gauss.LWInst.Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ))) :=
  RBM.Gauss.LWInst.inst_Anp h (lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0)
    (lwXiClaim_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
      sz0 z0 flow_z0 tInst RBM.Gauss.LWInst.tInst_range.1 RBM.Gauss.LWInst.tInst_range.2 (1 / 20) 2 2 1
      (fun _ => 1) RBM.Gauss.LWInst.Φ0 RBM.Gauss.LWInst.psiAll0 hL (1 / 20) (by norm_num) hent
      auxGraph2_ρ0 auxGraph2_ρ0_nonneg auxGraph2_ρ0_rad)

/-- The index set of target 4: pairs `x ≠ y` with blocks `a`, `b` within `zdistD`-distance `R0 n` of `[x]`, `[y]`. -/
private abbrev auxGraph2_Ugb (n : ℕ) : Type :=
  {q : (Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
    q.1.1 ≠ q.1.2 ∧
    (zdistD 3 (sz0.L n) ((split 3 (sz0.L n) (sz0.W n) q.1.1).1 - q.2.1) : ℝ) ≤ auxGraph2_R0 n ∧
    (zdistD 3 (sz0.L n) ((split 3 (sz0.L n) (sz0.W n) q.1.2).1 - q.2.2) : ℝ) ≤ auxGraph2_R0 n}

/-- **Instance 4** (target 4, `(eq:Gbyxi)` off the diagonal): the index set is nonempty at every size, and
`|G_{xy}| ≺ ξ(a, b)` holds under the entry law at the merged data. -/
example (hent : auxGraph2_Entry) :
    (∀ n, Nonempty (auxGraph2_Ugb n)) ∧
    Prec sz0 (U := auxGraph2_Ugb)
      (fun n q ω => ‖Gt sz0 n (STflowE z0 n) (tInst n) true ω q.1.1.1 q.1.1.2‖)
      (fun n q ω => lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 n q.1.2.1 q.1.2.2 ω) := by
  refine ⟨fun n => ?_, lwGbyXi_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst RBM.Gauss.LWInst.tInst_range.1
    RBM.Gauss.LWInst.tInst_range.2 (1 / 20) (by norm_num) hent auxGraph2_ρ0 auxGraph2_R0
    auxGraph2_R0_nonneg auxGraph2_ρ0_ge⟩
  obtain ⟨x, y, hxy⟩ := auxGraph2_exists_ne n
  refine ⟨⟨((x, y), (STblk sz0 n x, STblk sz0 n y)), hxy, ?_, ?_⟩⟩
  · show (zdistD 3 (sz0.L n) ((split 3 (sz0.L n) (sz0.W n) x).1 - (split 3 (sz0.L n) (sz0.W n) x).1) : ℝ) ≤ _
    rw [sub_self, zdistD_zero, Nat.cast_zero]; exact auxGraph2_R0_nonneg n
  · show (zdistD 3 (sz0.L n) ((split 3 (sz0.L n) (sz0.W n) y).1 - (split 3 (sz0.L n) (sz0.W n) y).1) : ℝ) ≤ _
    rw [sub_self, zdistD_zero, Nat.cast_zero]; exact auxGraph2_R0_nonneg n

/-- **Instance 5** (target 5, `(eq:Gbyxi)` entrywise): `‖G_t - M‖_max ≺ Φ0(0)` at the merged data. -/
example (hL : LWLoop2 sz0 (STflowE z0) tInst RBM.Gauss.LWInst.Φ0) (hent : auxGraph2_Entry) :
    Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖STGM sz0 n (STflowE z0 n) (tInst n) ω p.1 p.2‖)
      (fun n _ _ => RBM.Gauss.LWInst.Φ0 n 0) :=
  lwEntryPsi_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst RBM.Gauss.LWInst.tInst_range.1 RBM.Gauss.LWInst.tInst_range.2 (1 / 20) 2 2 1
    (fun _ => 1) RBM.Gauss.LWInst.Φ0 RBM.Gauss.LWInst.psiAll0 hL (1 / 20) (by norm_num) hent

/-- **Instance 6** (`lwGbyXi_hxi`): the premises `hξ0`, `hξ` of the merged `lwGtoAG_holds` for
`D = lwSampleData sz0 0 (zt _ _) _ M S Sp ω`, `ξ = c · lwXiVar`, from the sample event of target 4. -/
example (M S Sp : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) (ω : sz0.SeqΩ)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : Zd 3 (sz0.L 0)), x ≠ y →
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - a) : ℝ) ≤ auxGraph2_R0 0 →
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - b) : ℝ) ≤ auxGraph2_R0 0 →
      ‖Gt sz0 0 (STflowE z0 0) (tInst 0) true ω x y‖ ≤
        c * lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a b ω) :
    (∀ a b : Zd 3 (sz0.L 0), 0 ≤ c * lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a b ω) ∧
      (∀ (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : Zd 3 (sz0.L 0)), x ≠ y →
        (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - a) : ℝ) ≤ auxGraph2_R0 0 →
        (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - b) : ℝ) ≤ auxGraph2_R0 0 →
        ‖(lwSampleData sz0 0 (zt (STflowE z0 0) (tInst 0)) (tInst 0) M S Sp ω).G x y‖ ≤
          (fun a b : Zd 3 (sz0.L 0) => c * lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a b ω) a b) :=
  lwGbyXi_hxi sz0 (STflowE z0) tInst auxGraph2_ρ0 auxGraph2_R0 0 M S Sp ω hc h

/-- **Instance 6, composed**: the merged deterministic `lwGtoAG_holds` at the sample data
`D = lwSampleData sz0 0 (zt _ _) _ M S Sp ω` and `ξ = c_ξ · lwXiVar`, its premises `hξ0`, `hξ` supplied by
`lwGbyXi_hxi`; the other premises (target 5, the decay of `S`, `S⁺`, the graph) stay hypotheses (LW-02). -/
example {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (hN : Γ.Normal) (hext : ∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b)
    (M S Sp : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) (ω : sz0.SeqΩ)
    (m : ℂ) (Ψ C c r cξ : ℝ) (hcξ : 0 ≤ cξ)
    (hM : ∀ x y, M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖Gt sz0 0 (STflowE z0 0) (tInst 0) true ω x y‖ ≤ Ψ)
    (hGd : ∀ x, ‖Gt sz0 0 (STflowE z0 0) (tInst 0) true ω x x - m‖ ≤ Ψ)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖S x y‖ ≤ C * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ *
      Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hSp : ∀ x y, ‖Sp x y‖ ≤ C * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ *
      Real.exp (-(c * (lwBdist 3 (sz0.L 0) (sz0.W 0) x y : ℝ))))
    (hwin : ((sz0.W 0 : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) ≤ Ψ) (hr : 0 ≤ r)
    (hRr : (Fintype.card (E ⊕ I) : ℝ) * r ≤ auxGraph2_R0 0)
    (h : ∀ (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a b : Zd 3 (sz0.L 0)), x ≠ y →
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) x).1 - a) : ℝ) ≤ auxGraph2_R0 0 →
      (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) y).1 - b) : ℝ) ≤ auxGraph2_R0 0 →
      ‖Gt sz0 0 (STflowE z0 0) (tInst 0) true ω x y‖ ≤
        cξ * lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a b ω)
    (ℓe : E → Idx 3 (sz0.L 0) (sz0.W 0)) :=
  lwGtoAG_holds 3 le_rfl (sz0.L 0) (sz0.W 0) Γ hN hext
    (lwSampleData sz0 0 (zt (STflowE z0 0) (tInst 0)) (tInst 0) M S Sp ω) m Ψ C c r (auxGraph2_R0 0)
    (fun a b => cξ * lwXiVar sz0 (STflowE z0) tInst auxGraph2_ρ0 0 a b ω) hM hG hGd hC hc hS hSp hwin hr hRr
    (lwGbyXi_hxi sz0 (STflowE z0) tInst auxGraph2_ρ0 auxGraph2_R0 0 M S Sp ω hcξ h).1
    (lwGbyXi_hxi sz0 (STflowE z0) tInst auxGraph2_ρ0 auxGraph2_R0 0 M S Sp ω hcξ h).2 ℓe

/-- **Instance** (target 6): the radii `R0`, `ρ0` are `N^{o(1)}` along `sz0`. -/
example : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, auxGraph2_ρ0 n + 1 ≤ ((sz0.size n : ℕ) : ℝ) ^ τ :=
  auxGraph2_ρ0_rad

end Instances

end RBM.Graph
