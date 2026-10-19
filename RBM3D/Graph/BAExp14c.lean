/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAS3CloseC
import RBM3D.Graph.BAAtom

/-!
# The `BAExp14bS3` side: the analytic bound, the sub-root, the bridge, the kit, the `t`-class (A)

Paper: Subappendix B.1, proof of Lemma 6.2 (`lem:LWterm_EXP`), the graphical part from (B.5)
`eq;I42inG` to (B.9) `eq:GGraisesord` and the closing remark.  This is the BA counterpart of
`Graph/LWExpTerm3.lean` (Sections 1-2, the kit of Section 3, and Section 4).  Part B is
`Graph/BAExp14cB.lean`.

## Contents (namespace `RBM.BA`; private prefix `BAExp14c_`)

1. The sub-root `baS3RootT0` (`T3C-tr_0` of `baS3RootM`), its partition, list and identity.
2. The bridge `BAS3Bridge`, `baS3Bridge_holds`.
3. The `≺ → 𝔼` kit of a BA graph value.
4. The `t`-carrying fold class `BAFoldLeafT`, `BAS3CloseT`.
5. The statement defs `BAG5LeafPrec`, `BAS3LeafAvg`, `BAExp14bS3OfLeaf`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

open private BAS3Close_root_identity from RBM3D.Graph.BAS3Close
open private BAS3Close_blk_sum BAS3Close_D BAS3Close_D_S BAS3Close_D_M BAS3Close_hG BAS3Close_data BAS3Close_facts BAS3Close_D_Sp
  BAS3Close_Fact from RBM3D.Graph.BAS3CloseC
open private BAS3Close_Hq BAS3Close_Kern BAS3Close_rho BAS3Close_Bd BAS3Close_Bd_of BAS3Close_fold_gen_i BAS3Close_kD BAS3Close_kK
  BAS3Close_kKK BAS3Close_kB BAS3Close_k1 BAS3Close_hZ_D BAS3Close_hZ_K BAS3Close_hZ_KK BAS3Close_hN_D BAS3Close_hN_K BAS3Close_hN_B
  BAS3Close_hN_1 BAS3Close_hq00 BAS3Close_hq01 BAS3Close_hq02 BAS3Close_hq03 BAS3Close_hq04 BAS3Close_hq05 BAS3Close_hq06
  BAS3Close_hq10 BAS3Close_hq11 BAS3Close_hq12 BAS3Close_hq13 BAS3Close_hq14 BAS3Close_hq15 BAS3Close_hq16
  from RBM3D.Graph.BAS3CloseC
open private BAVocab_val_of_factor BAVocab_val_of_not from RBM3D.Graph.BAVocab

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The sub-root of `T3C-tr_0` -/

/-- **The sub-root `T3C-tr_0`**: the data of `baS3RootM` with the first solid edge `G(x, i0)` circled,
`Ǧ(x,i0) G(i2,y) G(i3,i2) G(i1,i3)` and the tail `G(y,x)` (`s = true`) or `Ḡ(x,y)` (`s = false`); black `S(i1,i2)`, `S(i0,i3)`;
`M(i0,i1)`; coefficient `1`.  `baS3RootM = T3C-tr_0 + D1X` at the level of values. -/
def baS3RootT0 (s : Bool) : BAGraph (Fin 2) (Fin 4) :=
  { solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 2) (Sum.inl 1),
      SEdge.mk true false (Sum.inr 3) (Sum.inr 2), SEdge.mk true false (Sum.inr 1) (Sum.inr 3),
      if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
    waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 2), WEdge.mk false false (Sum.inr 0) (Sum.inr 3)],
    dotted := [], coeff := 1, psi := [],
    mdot := [BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)] }

/-- A circled first edge: the circled child is the first of the two children of the uncircled edge in `baSplitSolid`. -/
private theorem BAExp14c_split_circ {V : Type*} (e : SEdge V) (es : List (SEdge V)) (he : e.circ = false)
    (r : List (SEdge V) × List (BAMEdge V)) (hr : r ∈ baSplitSolid (SEdge.mk e.σ true e.src e.dst :: es)) :
    r ∈ baSplitSolid (e :: es) := by
  simp only [baSplitSolid, List.mem_flatMap, ite_true, List.mem_singleton] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  simp only [baSplitSolid, List.mem_flatMap, he, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_singleton]
  exact ⟨r0, hr0, Or.inl rfl⟩

/-- **Inclusion of the partitions**: every term of the sub-root's partition is a term of that of `baS3RootM`
(the circled child of `G(x,i0)` in the first step of `baSplitSolid`). -/
theorem baS3RootT0_sub : ∀ s : Bool, ∀ P ∈ (baS3RootT0 s).partition, P ∈ (baS3RootM s).partition := by
  intro s P hP
  unfold BAGraph.partition BAGraph.splitG at hP ⊢
  simp only [List.mem_map] at hP ⊢
  obtain ⟨Γ, ⟨r, hr, rfl⟩, rfl⟩ := hP
  exact ⟨_, ⟨r, BAExp14c_split_circ (SEdge.mk true false (Sum.inl 0) (Sum.inr 0)) _ rfl r hr, rfl⟩, rfl⟩

/-- **Inclusion of the expanded lists**: every output of the expansion of the sub-root is an output of
the list of `baS3RootM` (index `0` of `BAS3expandRoot`), so the closure of the expansion lists classifies it. -/
theorem baS3RootT0_list : ∀ (sel : BASel) (fuel : ℕ) (s : Bool),
    ∀ q ∈ (baS3RootT0 s).partition.flatMap (fun P => (BAexpand sel fuel P).map Prod.snd), q ∈ BAS3expandRoot sel fuel 0 s := by
  intro sel fuel s q hq
  obtain ⟨P, hP, hq⟩ := List.mem_flatMap.1 hq
  exact List.mem_flatMap.2 ⟨P, baS3RootT0_sub s P hP, hq⟩

/-- **The identity of the sub-root** (as `BAS3Identity` for one root): `𝔼 root = Σ_μ 𝔼 Γ_μ`
at `BAlwData` over `PF d L W 0`, `BASelf`, `0 ≤ t < 1`, every selector and fuel. -/
theorem baS3RootT0_identity (d : ℕ) : ∀ (sel : BASel) (fuel : ℕ) (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ),
    BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 → ∀ (s : Bool) (x y : Idx d L W),
      ∫ ω, (baS3RootT0 s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
        (((baS3RootT0 s).partition.flatMap (fun P => (BAexpand sel fuel P).map Prod.snd)).map fun q =>
          ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum := by
  intro sel fuel L W _ _ hL g0 E t m hSelf ht0 ht1 s x y
  exact BAS3Close_root_identity d sel fuel (baS3RootT0 s) L W hL g0 E t m hSelf ht0 ht1 x y

/-! ## 2. The bridge: the `BAExp14bS3` families are `t⁻¹ ×` the block average of the root values

Root value `= Σ` over the internal labels of the product of the edge factors (`sum_pi_fin_succ`); the black edge `S(i0, i3)` of a root is the
block identity `S_{wv} = t W^{-d} 1[v ∈ [w]]`, which turns the `v`-sum into the block sum `Σ_{v ∈ [w]}` inside `∂X_{[α]}`
(`BAExp14b_dX`) and produces the factor `t`; `W^{(0)} = 1` collapses `α = w`; `W^{(1)} = W - 1 = M⁺ S⁺` (`S⁺ = S W`). -/

local macro "BAExp14c_peel" : tactic => `(tactic| repeat (refine Finset.sum_congr rfl fun _ _ => ?_))

section Shapes
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem BAExp14c_shapeM (s : Bool) (D : BALData ι) (x y : ι) :
    (baS3RootM s).val D ![x, y] = ∑ i0, ∑ i1, ∑ i2, ∑ i3, D.G x i0 * D.G i2 y * D.G i3 i2 * D.G i1 i3 *
      (if s then D.G y x else star (D.G x y)) * D.S i1 i2 * D.S i0 i3 * D.M i0 i1 := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, baS3RootM]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, sub_zero]
  all_goals
    BAExp14c_peel
    ring

private theorem BAExp14c_shapeT1 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (baS3Root1 s).val D ![x, y] = ∑ i0, ∑ i1, ∑ i2, ∑ i3, ∑ i4, ∑ i5, GM x i2 * D.G i4 y * D.G i5 i4 * D.G i3 i5 *
      (if s then D.G y x else star (D.G x y)) * D.Sp i1 i2 * D.S i3 i4 * D.S i0 i5 * D.M i0 i1 * D.M i1 i0 * D.M i2 i3 := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, baS3Root1]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, sub_zero, hG]
  all_goals
    BAExp14c_peel
    ring

private theorem BAExp14c_shapeD (s : Bool) (D : BALData ι) (x y : ι) :
    (baS3RootD s).val D ![x, y] = ∑ i0, ∑ i1, ∑ i2, ∑ i3, D.G i3 i0 * D.G i2 i3 * D.G i1 i2 *
      (if s then D.G y x else star (D.G x y)) * D.S i1 i3 * D.S i0 i2 * D.M x i1 * D.M i0 y := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, baS3RootD]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, sub_zero]
  all_goals
    BAExp14c_peel
    ring

private theorem BAExp14c_shapeT0 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (baS3RootT0 s).val D ![x, y] = ∑ i0, ∑ i1, ∑ i2, ∑ i3, GM x i0 * D.G i2 y * D.G i3 i2 * D.G i1 i3 *
      (if s then D.G y x else star (D.G x y)) * D.S i1 i2 * D.S i0 i3 * D.M i0 i1 := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, baS3RootT0]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG, sub_zero]
  all_goals
    BAExp14c_peel
    ring

private theorem BAExp14c_collapse (F : ι → ι → ι → ι → ℂ) :
    ∑ α, ∑ w, ∑ γ, ∑ δ, (1 : Matrix ι ι ℂ) α w * F α w γ δ = ∑ w, ∑ γ, ∑ δ, F w w γ δ := by
  calc ∑ α, ∑ w, ∑ γ, ∑ δ, (1 : Matrix ι ι ℂ) α w * F α w γ δ
      = ∑ α, ∑ w, (if α = w then ∑ γ, ∑ δ, F α w γ δ else 0) := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun w _ => ?_
        by_cases h : α = w
        · subst h; simp
        · simp [h]
    _ = ∑ α, ∑ γ, ∑ δ, F α α γ δ := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_ite_eq]; simp

end Shapes

section Pointwise
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ}

private theorem BAExp14c_D_G (ω : sz.SeqΩ) (a b : Idx d (sz.L n) (sz.W n)) :
    (BAS3Close_D sz z n t ω).G a b = (baFMz sz z).G n t ω a b := rfl

private theorem BAExp14c_D_S' (ω : sz.SeqΩ) (a b : Idx d (sz.L n) (sz.W n)) :
    (BAS3Close_D sz z n t ω).S a b = BAlwS d (sz.L n) (sz.W n) t a b := rfl

private theorem BAExp14c_blk (α : Idx d (sz.L n) (sz.W n)) :
    Iblk d (sz.L n) (sz.W n) (STblk sz n α) = twBlk n (split d (sz.L n) (sz.W n) α).1 := rfl

private theorem BAExp14c_S_blk (u : Idx d (sz.L n) (sz.W n)) (f : Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ a, BAlwS d (sz.L n) (sz.W n) t u a * f a =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a ∈ twBlk n (split d (sz.L n) (sz.W n) u).1, f a) := by
  simp only [BAExp14a_S_apply]
  exact BAS3Close_blk_sum u f

private theorem BAExp14c_ptT0 (ω : sz.SeqΩ) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    (t : ℂ) * (BAExp14a_tail sz z n t ω σ x y * ∑ α, ∑ w, ∑ γ, ∑ δ,
      -(BAExp14a_Wk sz z n t false α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ)) =
    (baS3RootT0 σ).val (BAS3Close_D sz z n t ω) ![x, y] := by
  rw [BAExp14c_shapeT0 σ (BAS3Close_D sz z n t ω) ((baFMz sz z).GM n t ω) (BAS3Close_hG sz z n t ω)]
  simp only [BAExp14c_D_G, BAS3Close_D_M, BAExp14c_D_S']
  have e1 : ∀ α w γ δ : Idx d (sz.L n) (sz.W n),
      -(BAExp14a_Wk sz z n t false α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ) =
      (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) α w *
        (-((baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ)) := by
    intro α w γ δ
    simp only [BAExp14a_Wk, Bool.false_eq_true, ↓reduceIte]
    ring
  simp only [e1]
  rw [BAExp14c_collapse]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ => ?_
  have key : ∑ i3, (baFMz sz z).GM n t ω x i0 * (baFMz sz z).G n t ω i2 y * (baFMz sz z).G n t ω i3 i2 *
      (baFMz sz z).G n t ω i1 i3 * (if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)) * BAlwS d (sz.L n) (sz.W n) t i1 i2 *
      BAlwS d (sz.L n) (sz.W n) t i0 i3 * (baFMz sz z).M n i0 i1 =
      ((baFMz sz z).GM n t ω x i0 * (baFMz sz z).G n t ω i2 y * (if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)) *
        BAlwS d (sz.L n) (sz.W n) t i1 i2 * (baFMz sz z).M n i0 i1) *
      ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ twBlk n (split d (sz.L n) (sz.W n) i0).1,
        (baFMz sz z).G n t ω v i2 * (baFMz sz z).G n t ω i1 v)) := by
    rw [← BAExp14c_S_blk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i3 _ => ?_
    ring
  rw [key]
  simp only [BAExp14b_dX, BAExp14a_tail, BAExp14c_blk]
  ring


private theorem BAExp14c_insb {ι : Type} [Fintype ι] (A : ι → ι → ι → ℂ) (F : ι → ι → ι → ι → ℂ) :
    ∑ α, ∑ w, ∑ γ, ∑ δ, (∑ b, A α b w) * F α w γ δ = ∑ α, ∑ b, ∑ w, ∑ γ, ∑ δ, A α b w * F α w γ δ := by
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Finset.sum_mul]
  calc ∑ w, ∑ γ, ∑ δ, ∑ b, A α b w * F α w γ δ
      = ∑ w, ∑ b, ∑ γ, ∑ δ, A α b w * F α w γ δ := by
        refine Finset.sum_congr rfl fun w _ => ?_
        calc ∑ γ, ∑ δ, ∑ b, A α b w * F α w γ δ = ∑ γ, ∑ b, ∑ δ, A α b w * F α w γ δ :=
              Finset.sum_congr rfl fun γ _ => Finset.sum_comm
          _ = ∑ b, ∑ γ, ∑ δ, A α b w * F α w γ δ := Finset.sum_comm
    _ = ∑ b, ∑ w, ∑ γ, ∑ δ, A α b w * F α w γ δ := Finset.sum_comm

private theorem BAExp14c_Ssum (u : Idx d (sz.L n) (sz.W n)) (c : ℂ) (f : Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ a, c * (BAlwS d (sz.L n) (sz.W n) t u a * f a) =
      c * ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a ∈ twBlk n (split d (sz.L n) (sz.W n) u).1, f a)) := by
  rw [← Finset.mul_sum, BAExp14c_S_blk]

private theorem BAExp14c_valM_split (s : Bool) {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (GM : ι → ι → ℂ)
    (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (baS3RootM s).val D ![x, y] = (baS3RootT0 s).val D ![x, y] + ∑ i0, ∑ i1, ∑ i2, ∑ i3, D.M x i0 * D.G i2 y * D.G i3 i2 *
      D.G i1 i3 * (if s then D.G y x else star (D.G x y)) * D.S i1 i2 * D.S i0 i3 * D.M i0 i1 := by
  rw [BAExp14c_shapeM, BAExp14c_shapeT0 s D GM hG x y, add_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i0 _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i1 _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i2 _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i3 _ => ?_
  have h : D.G x i0 = D.M x i0 + GM x i0 := by rw [← hG]; ring
  rw [h]; ring

private theorem BAExp14c_ptD1 (ω : sz.SeqΩ) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    (t : ℂ) * (BAExp14a_tail sz z n t ω σ x y * ∑ α, ∑ α', ∑ β,
      -((baFMz sz z).M n x α * (baFMz sz z).M n α α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β y *
        BAExp14b_dX sz z n t ω α β α')) =
    ∑ i0, ∑ i1, ∑ i2, ∑ i3, (baFMz sz z).M n x i0 * (baFMz sz z).G n t ω i2 y * (baFMz sz z).G n t ω i3 i2 *
      (baFMz sz z).G n t ω i1 i3 * BAExp14a_tail sz z n t ω σ x y * BAlwS d (sz.L n) (sz.W n) t i1 i2 *
      BAlwS d (sz.L n) (sz.W n) t i0 i3 * (baFMz sz z).M n i0 i1 := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ => ?_
  have key : ∑ i3, (baFMz sz z).M n x i0 * (baFMz sz z).G n t ω i2 y * (baFMz sz z).G n t ω i3 i2 *
      (baFMz sz z).G n t ω i1 i3 * BAExp14a_tail sz z n t ω σ x y * BAlwS d (sz.L n) (sz.W n) t i1 i2 *
      BAlwS d (sz.L n) (sz.W n) t i0 i3 * (baFMz sz z).M n i0 i1 =
      ((baFMz sz z).M n x i0 * (baFMz sz z).G n t ω i2 y * BAExp14a_tail sz z n t ω σ x y *
        BAlwS d (sz.L n) (sz.W n) t i1 i2 * (baFMz sz z).M n i0 i1) *
      ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ twBlk n (split d (sz.L n) (sz.W n) i0).1,
        (baFMz sz z).G n t ω v i2 * (baFMz sz z).G n t ω i1 v)) := by
    rw [← BAExp14c_Ssum]
    refine Finset.sum_congr rfl fun i3 _ => ?_
    ring
  rw [key]
  simp only [BAExp14b_dX, BAExp14c_blk]
  ring

private theorem BAExp14c_W_sub_one_mat {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {g0 E t : ℝ} {m : ℂ}
    (hSelf : BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BAlwW d L W g0 E t m - 1 = BAlwMp d L W g0 E m * (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) := by
  have hmul := baW_mul (W := W) hL g0 E t m hSelf ht0 ht1
  have hmul' : (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) * BAlwW d L W g0 E t m = 1 :=
    mul_eq_one_comm.1 hmul
  rw [sub_mul, one_mul] at hmul'
  rw [← Matrix.mul_assoc]
  exact sub_eq_of_eq_add' (sub_eq_iff_eq_add.1 hmul')

private theorem BAExp14c_Wk1 {κ : ℝ} (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (α w : Idx d (sz.L n) (sz.W n)) :
    BAExp14a_Wk sz z n t true α w =
      ∑ b, (baFMz sz z).M n α b * (baFMz sz z).M n b α * (BAS3Close_D sz z n t ω).Sp b w := by
  have h := BAExp14c_W_sub_one_mat (W := sz.W n) (sz.three_le_L n) hr.1 ht0 ht1
  have h2 := congrFun (congrFun h α) w
  simp only [BAExp14a_Wk, ite_true]
  rw [h2, Matrix.mul_apply]
  rfl

private theorem BAExp14c_ptT1 {κ : ℝ} (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    (t : ℂ) * (BAExp14a_tail sz z n t ω σ x y * ∑ α, ∑ w, ∑ γ, ∑ δ,
      -(BAExp14a_Wk sz z n t true α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ)) =
    (baS3Root1 σ).val (BAS3Close_D sz z n t ω) ![x, y] := by
  rw [BAExp14c_shapeT1 σ (BAS3Close_D sz z n t ω) ((baFMz sz z).GM n t ω) (BAS3Close_hG sz z n t ω)]
  simp only [BAExp14c_D_G, BAS3Close_D_M, BAExp14c_D_S']
  have e1 : ∀ α w γ δ : Idx d (sz.L n) (sz.W n),
      -(BAExp14a_Wk sz z n t true α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ) =
      BAExp14a_Wk sz z n t true α w *
        (-((baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ)) := by
    intro α w γ δ
    ring
  simp only [e1]
  simp only [BAExp14c_Wk1 hr ht0 ht1 ω]
  rw [BAExp14c_insb]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
    Finset.sum_congr rfl fun i3 _ => Finset.sum_congr rfl fun i4 _ => ?_
  have key : ∑ i5, (baFMz sz z).GM n t ω x i2 * (baFMz sz z).G n t ω i4 y * (baFMz sz z).G n t ω i5 i4 *
      (baFMz sz z).G n t ω i3 i5 * (if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)) * (BAS3Close_D sz z n t ω).Sp i1 i2 *
      BAlwS d (sz.L n) (sz.W n) t i3 i4 * BAlwS d (sz.L n) (sz.W n) t i0 i5 * (baFMz sz z).M n i0 i1 *
      (baFMz sz z).M n i1 i0 * (baFMz sz z).M n i2 i3 =
      ((baFMz sz z).GM n t ω x i2 * (baFMz sz z).G n t ω i4 y * (if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)) *
        (BAS3Close_D sz z n t ω).Sp i1 i2 * BAlwS d (sz.L n) (sz.W n) t i3 i4 * (baFMz sz z).M n i0 i1 *
        (baFMz sz z).M n i1 i0 * (baFMz sz z).M n i2 i3) *
      ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ twBlk n (split d (sz.L n) (sz.W n) i0).1,
        (baFMz sz z).G n t ω v i4 * (baFMz sz z).G n t ω i3 v)) := by
    rw [← BAExp14c_Ssum]
    refine Finset.sum_congr rfl fun i5 _ => ?_
    ring
  rw [key]
  simp only [BAExp14b_dX, BAExp14a_tail, BAExp14c_blk]
  ring

private theorem BAExp14c_ptD2 (ω : sz.SeqΩ) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    (t : ℂ) * (BAExp14a_tail sz z n t ω σ x y * ∑ α, ∑ α', ∑ β,
      -((baFMz sz z).M n x α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β α * (baFMz sz z).M n α y *
        BAExp14b_dX sz z n t ω α β α')) =
    (baS3RootD σ).val (BAS3Close_D sz z n t ω) ![x, y] := by
  rw [BAExp14c_shapeD σ (BAS3Close_D sz z n t ω)]
  simp only [BAExp14c_D_G, BAS3Close_D_M, BAExp14c_D_S']
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i3 _ => ?_
  have key : ∑ i2, (baFMz sz z).G n t ω i3 i0 * (baFMz sz z).G n t ω i2 i3 * (baFMz sz z).G n t ω i1 i2 *
      (if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)) * BAlwS d (sz.L n) (sz.W n) t i1 i3 * BAlwS d (sz.L n) (sz.W n) t i0 i2 *
      (baFMz sz z).M n x i1 * (baFMz sz z).M n i0 y =
      ((baFMz sz z).G n t ω i3 i0 * (if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)) * BAlwS d (sz.L n) (sz.W n) t i1 i3 *
        (baFMz sz z).M n x i1 * (baFMz sz z).M n i0 y) *
      ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ twBlk n (split d (sz.L n) (sz.W n) i0).1,
        (baFMz sz z).G n t ω v i3 * (baFMz sz z).G n t ω i1 v)) := by
    rw [← BAExp14c_Ssum]
    refine Finset.sum_congr rfl fun i2 _ => ?_
    ring
  rw [key]
  simp only [BAExp14b_dX, BAExp14a_tail, BAExp14c_blk]
  ring

private theorem BAExp14c_frame (ω : sz.SeqΩ) (σ : Bool) (a b : Zd d (sz.L n))
    (Tf : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (V : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (h : ∀ x y, (t : ℂ) * (BAExp14a_tail sz z n t ω σ x y * ∑ α, Tf x y α) = V x y) :
    (t : ℂ) * BAExp14b_outerDX sz z n t ω σ a b Tf =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, V x y := by
  unfold BAExp14b_outerDX
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => h x y

end Pointwise

/-- **The bridge**. -/
def BAS3Bridge (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (σ : Bool) (a b : Zd d (sz.L n)),
      ((t : ℂ) * BAExp14b_FT3CX sz z n t ω false σ a b =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (baS3RootT0 σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y]) ∧
      ((t : ℂ) * (BAExp14b_FD1X sz z n t ω σ a b + BAExp14b_FT3CX sz z n t ω false σ a b) =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (baS3RootM σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y]) ∧
      ((t : ℂ) * BAExp14b_FT3CX sz z n t ω true σ a b =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (baS3Root1 σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y]) ∧
      ((t : ℂ) * BAExp14b_FD2X sz z n t ω σ a b =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (baS3RootD σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y])

theorem baS3Bridge_holds : ∀ d : ℕ, BAS3Bridge d := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω σ a b
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hf n ht0 ht
  have h0 : (t : ℂ) * BAExp14b_FT3CX sz z n t ω false σ a b = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 *
      ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, (baS3RootT0 σ).val (BAS3Close_D sz z n t ω) ![x, y] :=
    BAExp14c_frame (t := t) ω σ a b _ _ (fun x y => BAExp14c_ptT0 (z := z) ω σ x y)
  have h1 : (t : ℂ) * BAExp14b_FD1X sz z n t ω σ a b = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 *
      ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, ∑ i0, ∑ i1, ∑ i2, ∑ i3, (baFMz sz z).M n x i0 * (baFMz sz z).G n t ω i2 y *
        (baFMz sz z).G n t ω i3 i2 * (baFMz sz z).G n t ω i1 i3 * BAExp14a_tail sz z n t ω σ x y *
        BAlwS d (sz.L n) (sz.W n) t i1 i2 * BAlwS d (sz.L n) (sz.W n) t i0 i3 * (baFMz sz z).M n i0 i1 :=
    BAExp14c_frame (t := t) ω σ a b _ _ (fun x y => BAExp14c_ptD1 (z := z) ω σ x y)
  have h2 : (t : ℂ) * BAExp14b_FT3CX sz z n t ω true σ a b = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 *
      ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, (baS3Root1 σ).val (BAS3Close_D sz z n t ω) ![x, y] :=
    BAExp14c_frame (t := t) ω σ a b _ _ (fun x y => BAExp14c_ptT1 (z := z) hr ht0 ht1 ω σ x y)
  have h3 : (t : ℂ) * BAExp14b_FD2X sz z n t ω σ a b = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 *
      ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, (baS3RootD σ).val (BAS3Close_D sz z n t ω) ![x, y] :=
    BAExp14c_frame (t := t) ω σ a b _ _ (fun x y => BAExp14c_ptD2 (z := z) ω σ x y)
  refine ⟨h0, ?_, h2, h3⟩
  rw [mul_add, h1, h0, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  change _ = (baS3RootM σ).val (BAS3Close_D sz z n t ω) ![x, y]
  rw [BAExp14c_valM_split σ (BAS3Close_D sz z n t ω) ((baFMz sz z).GM n t ω) (BAS3Close_hG sz z n t ω) x y]
  simp only [BAExp14c_D_G, BAS3Close_D_M, BAExp14c_D_S', BAExp14a_tail]
  ring


/-! ## 3. The `≺ → 𝔼` kit of a BA graph value (the cut of the band, `Graph/LWExpTerm3.lean` Section 3)

At `t = 0` a graph with a waved edge vanishes (`BAlwS 0 = 0`, `S⁺ = S W`); for `t > 0` the value has the polynomial envelope
`t^{n_W} N^K` (`|G| ≤ η⁻¹ ≤ 2 κ⁻¹ N^{1-ε}`, `|M| ≤ 1`, `S = t svarF`, `S⁺ = S W` with `W - 1` of bounded `ℓ¹` norm, `|g₀ Ψ| ≤ 𝔡⁻¹`,
`N^{|I'|}` labellings); the floor is `N⁻¹ ≤ B` (`expAvg_Bctl_ge`). -/


/-- **Values at `t = 0`**. -/
theorem BAExp14c_val_zero : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (ω : sz.SeqΩ) (P : BAPGraph (Fin 2)), P.g.nW ≠ 0 →
    ∀ ℓ : Fin 2 → Idx d (sz.L n) (sz.W n),
      P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) 0 ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ℓ = 0 := by
  intro d sz z n ω P hnW ℓ
  classical
  have hS0 : ∀ x y, (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) 0 ((baFMz sz z).m n)
      (BAExp14a_slc sz n ω)).S x y = 0 := by
    intro x y; simp [BAlwData, BAlwS]
  have hSp0 : ∀ x y, (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) 0 ((baFMz sz z).m n)
      (BAExp14a_slc sz n ω)).Sp x y = 0 := by
    intro x y; simp [BAlwData, BAlwS, Matrix.mul_apply]
  unfold BAPGraph.val
  split_ifs with h
  · unfold BAGraph.val
    refine Finset.sum_eq_zero fun ℓi _ => ?_
    unfold BAGraph.term RBM.Graph.LGraph.term
    have hW : (P.g.waved.map (WEdge.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) 0
        ((baFMz sz z).m n) (BAExp14a_slc sz n ω)).toLData (Sum.elim h.choose ℓi))).prod = 0 := by
      apply List.prod_eq_zero
      obtain ⟨e, he⟩ : ∃ e, e ∈ P.g.waved := List.exists_mem_of_length_pos (by
        have : P.g.waved.length ≠ 0 := hnW
        omega)
      refine List.mem_map.2 ⟨e, he, ?_⟩
      simp only [WEdge.val]
      split_ifs <;> simp [hS0, hSp0]
    rw [hW]; ring
  · rfl

private theorem BAExp14c_list_prod_le {α : Type*} (l : List α) (f : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ e ∈ l, ‖f e‖ ≤ B) : ‖(l.map f).prod‖ ≤ B ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    refine (norm_mul_le _ _).trans ?_
    calc ‖f a‖ * ‖(l.map f).prod‖ ≤ B * B ^ l.length :=
          mul_le_mul (h a (List.mem_cons_self)) (ih fun e he => h e (List.mem_cons_of_mem a he))
            (norm_nonneg _) hB
      _ = _ := by ring

/-- The envelope of a graph value: every solid edge `≤ Bd`, every waved edge `≤ t Bd`, every `Ψ`- and `M`-dotted edge `≤ Bd`, every
dotted edge `≤ 1`, `|ι|^{n_V}` labellings (as `lwExpTerm3_val_norm_le` in `Graph/LWExpTerm3.lean`). -/
private theorem BAExp14c_val_norm_le {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) {Bd t : ℝ} (hBd : 1 ≤ Bd) (ht : 0 ≤ t)
    (hG : ∀ x y, ‖D.G x y‖ + ‖D.M x y‖ ≤ Bd) (hM : ∀ x y, ‖D.M x y‖ ≤ Bd) (hS : ∀ x y, ‖D.S x y‖ ≤ t * Bd)
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ t * Bd) (hΨ : ∀ x y, ‖D.gPsi x y‖ ≤ Bd) (ℓe : E → ι) :
    ‖Γ.val D ℓe‖ ≤ t ^ Γ.waved.length * (‖Γ.coeff‖ * (Fintype.card ι : ℝ) ^ Fintype.card I *
      Bd ^ (Γ.solid.length + Γ.waved.length + Γ.psi.length + Γ.mdot.length)) := by
  classical
  have hB0 : 0 ≤ Bd := by linarith
  have hGb : ∀ x y, ‖D.G x y‖ ≤ Bd := fun x y => (le_add_of_nonneg_right (norm_nonneg _)).trans (hG x y)
  unfold BAGraph.val
  have hterm : ∀ ℓi : I → ι, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ t ^ Γ.waved.length * (‖Γ.coeff‖ *
      Bd ^ (Γ.solid.length + Γ.waved.length + Γ.psi.length + Γ.mdot.length)) := by
    intro ℓi
    unfold BAGraph.term RBM.Graph.LGraph.term
    have h1 := BAExp14c_list_prod_le Γ.solid (SEdge.val D.toLData (Sum.elim ℓe ℓi)) Bd hB0
      (fun e _ => by
        unfold SEdge.val
        simp only
        have hg : ‖D.G (Sum.elim ℓe ℓi e.src) (Sum.elim ℓe ℓi e.dst) -
            (if e.circ then D.M (Sum.elim ℓe ℓi e.src) (Sum.elim ℓe ℓi e.dst) else 0)‖ ≤ Bd := by
          split_ifs
          · exact (norm_sub_le _ _).trans (hG _ _)
          · simpa using hGb _ _
        cases hs : e.σ
        · simp only [Bool.false_eq_true, ↓reduceIte, norm_star]; exact hg
        · simp only [↓reduceIte]; exact hg)
    have h2 := BAExp14c_list_prod_le Γ.waved (WEdge.val D.toLData (Sum.elim ℓe ℓi)) (t * Bd) (mul_nonneg ht hB0)
      (fun e _ => by
        unfold WEdge.val
        split_ifs with hc hσ
        · exact hSp _ _
        · rw [norm_star]; exact hSp _ _
        · exact hS _ _)
    have h3 := BAExp14c_list_prod_le Γ.dotted (DEdge.val (Sum.elim ℓe ℓi)) 1 zero_le_one
      (fun e _ => by
        unfold DEdge.val
        split_ifs <;> simp)
    have h4 := BAExp14c_list_prod_le Γ.psi (BAPsiEdge.val D (Sum.elim ℓe ℓi)) Bd hB0
      (fun e _ => hΨ _ _)
    have h5 := BAExp14c_list_prod_le Γ.mdot (BAMEdge.val D (Sum.elim ℓe ℓi)) Bd hB0
      (fun e _ => by
        unfold BAMEdge.val
        split_ifs
        · exact hM _ _
        · rw [norm_star]; exact hM _ _)
    rw [one_pow] at h3
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    have n1 := norm_nonneg (Γ.coeff)
    have n2 := norm_nonneg ((Γ.solid.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod)
    have n3 := norm_nonneg ((Γ.waved.map (WEdge.val D.toLData (Sum.elim ℓe ℓi))).prod)
    have n4 := norm_nonneg ((Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod)
    have n5 := norm_nonneg ((Γ.psi.map (BAPsiEdge.val D (Sum.elim ℓe ℓi))).prod)
    have n6 := norm_nonneg ((Γ.mdot.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod)
    calc ‖Γ.coeff‖ * ‖(Γ.solid.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod‖ *
          ‖(Γ.waved.map (WEdge.val D.toLData (Sum.elim ℓe ℓi))).prod‖ *
          ‖(Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod‖ *
          ‖(Γ.psi.map (BAPsiEdge.val D (Sum.elim ℓe ℓi))).prod‖ * ‖(Γ.mdot.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod‖
        ≤ ‖Γ.coeff‖ * Bd ^ Γ.solid.length * (t * Bd) ^ Γ.waved.length * 1 * Bd ^ Γ.psi.length * Bd ^ Γ.mdot.length := by
          gcongr
      _ = _ := by rw [mul_pow, pow_add, pow_add, pow_add]; ring
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun ℓi _ => hterm ℓi).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  push_cast
  apply le_of_eq
  ring

section Carrier
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `η⁻¹ ≤ 2 κ⁻¹ N^{1-ε}` along the flow (`η⁻¹ ≤ κ⁻¹ (1-t)⁻¹`, `1 - t ≥ Im z / 2`, `Im z ≥ N^{-1+ε}`; no sign of `ε`). -/
theorem BAExp14c_etainv (hd : 3 ≤ d) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) :
    ((baFMz sz z).eta n t)⁻¹ ≤ 2 * κ⁻¹ * ((sz.size n : ℕ) : ℝ) ^ (1 - ε) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨ht1, -⟩ := BAS3Close_data sz hflow n ht0 ht
  have h1 := BAExp14a_eta_inv_le hκ hflow n ht1
  have h2 := BAExp14a_one_sub_t hκ hflow n ht
  obtain ⟨-, hz, -⟩ := hflow.2 n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNe : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos hN _
  have hzi : 0 < (z n).im := lt_of_lt_of_le hNe hz
  have h3 : (1 - t)⁻¹ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (1 - ε) := by
    calc (1 - t)⁻¹ ≤ ((z n).im / 2)⁻¹ := inv_anti₀ (div_pos hzi two_pos) h2
      _ = 2 * ((z n).im)⁻¹ := by rw [inv_div]; ring
      _ ≤ 2 * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hNe hz) (by norm_num)
      _ = 2 * ((sz.size n : ℕ) : ℝ) ^ (1 - ε) := by
          rw [← Real.rpow_neg hN.le]; congr 2; ring
  calc ((baFMz sz z).eta n t)⁻¹ ≤ κ⁻¹ * (1 - t)⁻¹ := h1
    _ ≤ κ⁻¹ * (2 * ((sz.size n : ℕ) : ℝ) ^ (1 - ε)) := mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hκ.le)
    _ = _ := by ring

/-- The polynomial scale `Bd = N^{c}`, `c = |1 - ε| + 1`: eventually `η⁻¹ + 1 ≤ N^c`, `Kc ≤ N^c`, `1 ≤ N^c`, uniformly in `t ∈ [0, T₀]`. -/
theorem BAExp14c_scale (hd : 3 ≤ d) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (Kc : ℝ) :
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
      ((baFMz sz z).eta n t)⁻¹ + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (|1 - ε| + 1) ∧
        Kc ≤ ((sz.size n : ℕ) : ℝ) ^ (|1 - ε| + 1) ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (|1 - ε| + 1) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  filter_upwards [(tendsto_natCast_atTop_iff.2 hsz).eventually (eventually_ge_atTop (2 * κ⁻¹ + 1 + |Kc|))]
    with n hN t ht0 ht
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hκi : 0 < κ⁻¹ := inv_pos.2 hκ
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) ≤ |Kc| := abs_nonneg _
    have hh : 2 * κ⁻¹ + 1 + |Kc| ≤ N := hN
    linarith
  have hN0 : 0 < N := by linarith
  have hp1 : 1 ≤ N ^ |1 - ε| := Real.one_le_rpow hN1 (abs_nonneg _)
  have hexp : N ^ (|1 - ε| + 1) = N * N ^ |1 - ε| := by
    rw [Real.rpow_add hN0, Real.rpow_one]; ring
  have hh : 2 * κ⁻¹ + 1 + |Kc| ≤ N := hN
  have hη := BAExp14c_etainv hd hκ hflow n ht0 ht
  have hle : N ^ (1 - ε) ≤ N ^ |1 - ε| := Real.rpow_le_rpow_of_exponent_le hN1 (le_abs_self _)
  rw [hexp]
  refine ⟨?_, ?_, ?_⟩
  · calc ((baFMz sz z).eta n t)⁻¹ + 1 ≤ 2 * κ⁻¹ * N ^ |1 - ε| + 1 := by
          have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * κ⁻¹)
          linarith
      _ ≤ (2 * κ⁻¹ + 1) * N ^ |1 - ε| := by nlinarith
      _ ≤ N * N ^ |1 - ε| := by
          have : 0 ≤ |Kc| := abs_nonneg _
          exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · calc Kc ≤ |Kc| := le_abs_self _
      _ ≤ N := by linarith [(by positivity : (0 : ℝ) ≤ 2 * κ⁻¹)]
      _ ≤ N * N ^ |1 - ε| := by nlinarith
  · nlinarith

/-- The entries of the graph data at the carrier, in one polynomial scale `Bd`: `G ≤ η⁻¹`, `M ≤ 1`, `S ≤ t`, `S⁺ ≤ t (K + 1)`, `g₀Ψ ≤ 𝔡⁻¹`. -/
private theorem BAExp14c_entries (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) {m Kf : ℝ} (hFact : BAS3Close_Fact sz z n t m Kf)
    (hwin : 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹) {Bd : ℝ} (hBd : 1 ≤ Bd)
    (hη : ((baFMz sz z).eta n t)⁻¹ + 1 ≤ Bd) (hK : Kf + 1 ≤ Bd) (h𝔡 : 𝔡⁻¹ ≤ Bd) (ω : sz.SeqΩ) :
    (∀ x y, ‖(BAS3Close_D sz z n t ω).G x y‖ + ‖(BAS3Close_D sz z n t ω).M x y‖ ≤ Bd) ∧
      (∀ x y, ‖(BAS3Close_D sz z n t ω).M x y‖ ≤ Bd) ∧
      (∀ x y, ‖(BAS3Close_D sz z n t ω).S x y‖ ≤ t * Bd) ∧
      (∀ x y, ‖(BAS3Close_D sz z n t ω).Sp x y‖ ≤ t * Bd) ∧
      (∀ x y, ‖(BAS3Close_D sz z n t ω).gPsi x y‖ ≤ Bd) := by
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hflow n ht0 ht
  have hM1 : ∀ x y, ‖(BAS3Close_D sz z n t ω).M x y‖ ≤ 1 := fun x y => BAExp14a_M_le_one hr.1 x y
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hW1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast sz.W_pos n))
  have hnormW : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ ≤ 1 := by simpa using hW1
  have hom : ∀ a b, ‖BAExp14b_om sz z n t a b‖ ≤ Kf + 1 := by
    intro a b
    have h1 : ‖(BAExp14b_om sz z n t - 1) a b‖ ≤ Kf :=
      (Finset.single_le_sum (f := fun b' => ‖(BAExp14b_om sz z n t - 1) a b'‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ b)).trans (hFact.2.2.1 a)
    have h2 : BAExp14b_om sz z n t a b = (BAExp14b_om sz z n t - 1) a b + (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b := by
      simp [Matrix.sub_apply]
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    have : ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ ≤ 1 := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    linarith
  refine ⟨fun x y => ?_, fun x y => (hM1 x y).trans hBd, fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
  · have hG : ‖(BAS3Close_D sz z n t ω).G x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ := BAExp14a_G_le hκ hflow n ht0 ht ω x y
    linarith [hM1 x y]
  · rw [BAS3Close_D_S, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ ht0
    have h1 : ‖(if (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1 then (1 : ℂ) else 0)‖ ≤ 1 := by
      split_ifs <;> simp
    calc _ ≤ 1 * 1 := mul_le_mul hnormW h1 (norm_nonneg _) zero_le_one
      _ ≤ Bd := by linarith
  · rw [BAS3Close_D_Sp hr ht0 ht1 ω x y, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ ht0
    calc _ ≤ 1 * (Kf + 1) := mul_le_mul hnormW (hom _ _) (norm_nonneg _) zero_le_one
      _ ≤ Bd := by linarith
  · change ‖(((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) x y‖ ≤ Bd
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hwin.1.le]
    have h1 : ‖PsiI d (sz.L n) (sz.W n) x y‖ ≤ 1 := by
      rw [BAAtom_PsiI_apply]; split_ifs <;> simp
    calc _ ≤ 𝔡⁻¹ * 1 := mul_le_mul hwin.2 h1 (norm_nonneg _) (inv_nonneg.2 (by
            have := hflow.1.2.1; linarith))
      _ ≤ Bd := by linarith

end Carrier

/-- **The envelope** (as `lwExpTerm3_val_norm_le`, `lwExpTerm3_X_norm_le`, `lwExpTerm3_poly` in `Graph/LWExpTerm3.lean`): for every packed BA graph a polynomial envelope `t^{n_W} N^K`, eventually in `n`, uniformly in
`0 ≤ t ≤ T₀`, the sample and the labels. -/
theorem BAExp14c_val_env : ∀ (d : ℕ), 3 ≤ d → ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ P : BAPGraph (Fin 2), ∃ K : ℝ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
      ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
        ‖P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
            (BAExp14a_slc sz n ω)) ![x, y]‖ ≤ t ^ P.g.nW * ((sz.size n : ℕ) : ℝ) ^ K := by
  intro d hd κ ε 𝔠 𝔡 sz z hκ hf P
  classical
  have h𝔡 : 0 < 𝔡 := hf.1.2.1
  obtain ⟨m, Kf, hm1, hK1, hev⟩ := BAS3Close_facts hd κ ε 𝔡 hκ 𝔠 h𝔡 sz z hf
  set c : ℝ := |1 - ε| + 1 with hc
  set e : ℕ := P.g.solid.length + P.g.waved.length + P.g.psi.length + P.g.mdot.length with he
  refine ⟨(Fintype.card P.I' : ℝ) + c * e + 1, ?_⟩
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hf.1.2.2.1
  filter_upwards [hev, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hf, BAExp14c_scale hd hκ hf (max (Kf + 1) 𝔡⁻¹),
    (tendsto_natCast_atTop_iff.2 hsz).eventually (eventually_ge_atTop ‖P.g.coeff‖)] with n hFn hwin hscale hcoeff
    t ht0 ht ω x y
  obtain ⟨hηB, hKB, h1B⟩ := hscale t ht0 ht
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact this
  have hN0 : 0 < N := by linarith
  by_cases hex : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ![x, y] = ℓ' ∘ P.ext
  swap
  · rw [BAVocab_val_of_not P _ hex, norm_zero]
    exact mul_nonneg (pow_nonneg ht0 _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨ℓ', hℓ'⟩ := hex
  rw [BAVocab_val_of_factor P _ hℓ']
  obtain ⟨hG, hM, hS, hSp, hΨ⟩ := BAExp14c_entries hκ hf ht0 ht (hFn t ht0 ht) hwin h1B hηB
    ((le_max_left _ _).trans hKB) ((le_max_right _ _).trans hKB) ω
  have hbd := BAExp14c_val_norm_le P.g (BAS3Close_D sz z n t ω) h1B ht0 hG hM hS hSp hΨ ℓ'
  refine hbd.trans ?_
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    simp [Sizes.size, Idx, mul_comm, hN]
  rw [hcard]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht0 _)
  have h2 : N ^ ((Fintype.card P.I' : ℝ) + c * e + 1) = N * N ^ (Fintype.card P.I') * (N ^ c) ^ e := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast, Real.rpow_one, Real.rpow_mul hN0.le, Real.rpow_natCast]
    ring
  rw [h2]
  have hc0 : 0 ≤ (N ^ c) ^ e := pow_nonneg (Real.rpow_nonneg hN0.le _) _
  calc ‖P.g.coeff‖ * N ^ Fintype.card P.I' * (N ^ c) ^ e ≤ N * N ^ Fintype.card P.I' * (N ^ c) ^ e := by
        gcongr
    _ = _ := by ring

/-- **`η ≤ 1`** (as `lwExpTerm3_etaT_le_one`): `η_t = (1 - t) Im m ≤ 1` (`‖m‖ ≤ 1`). -/
theorem BAExp14c_eta_le_one {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) : (baFMz sz z).eta n t ≤ 1 := by
  obtain ⟨ht1, hr, hmi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hm1 : ‖(baFMz sz z).m n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hr.1
  have h1 : ((baFMz sz z).m n).im ≤ 1 := (Complex.im_le_norm _).trans hm1
  rw [BAExp14a_eta_eq]
  unfold etaOf
  have h2 : 1 - t ≤ 1 := by linarith
  have h3 : 0 ≤ 1 - t := by linarith
  nlinarith [mul_le_mul h2 h1 hmi.le zero_le_one]

/-- **The floor** (as `lwExpTerm3_floor`; from `expAvg_Bctl_ge`): for `N ≥ 2` and `W^{-d} B_{t,0} ≤ 2`,
`N^{-|o|/2} ≤ η⁻¹ B^{o/2}` for every integer `o` (the BA form has `B ≤ 2`, not `B ≤ 1`). -/
theorem BAExp14c_floor {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (hN : 2 ≤ ((sz.size n : ℕ) : ℝ)) (hB : sz.Bctl n t ≤ 2)
    (o : ℤ) :
    ((sz.size n : ℕ) : ℝ) ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ ((baFMz sz z).eta n t)⁻¹ * (sz.Bctl n t) ^ ((o : ℝ) / 2) := by
  obtain ⟨ht1, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hη0 := BAExp14a_eta_pos hκ hflow n ht0 ht
  have hη1 := BAExp14c_eta_le_one hκ hflow n ht0 ht
  have hB0 := STBctl_pos sz n ht1
  have hNB := expAvg_Bctl_ge sz n ht0 ht1
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hη' : 1 ≤ ((baFMz sz z).eta n t)⁻¹ := (one_le_inv₀ hη0).2 hη1
  have hBo : 0 ≤ (sz.Bctl n t) ^ ((o : ℝ) / 2) := Real.rpow_nonneg hB0.le _
  have hB' : ((sz.size n : ℕ) : ℝ) ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ (sz.Bctl n t) ^ ((o : ℝ) / 2) := by
    rcases le_or_gt 0 o with ho | ho
    · have h1 : (|o| : ℤ) = o := abs_of_nonneg ho
      rw [h1]
      have ho' : (0 : ℝ) ≤ (o : ℝ) / 2 := by positivity
      calc ((sz.size n : ℕ) : ℝ) ^ (-((o : ℝ) / 2)) = (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((o : ℝ) / 2) := by
            rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]
        _ ≤ (sz.Bctl n t) ^ ((o : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hNB ho'
    · have h1 : (|o| : ℤ) = -o := abs_of_neg ho
      have ho' : (o : ℝ) / 2 ≤ 0 := by
        have : (o : ℝ) < 0 := by exact_mod_cast ho
        linarith
      have h2 : (2 : ℝ) ^ ((o : ℝ) / 2) ≤ (sz.Bctl n t) ^ ((o : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos hB0 hB ho'
      have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ (2 : ℝ) ^ ((o : ℝ) / 2) := by
        rw [h1]
        push_cast
        have e1 : (-(-(o : ℝ) / 2)) = (o : ℝ) / 2 := by ring
        rw [e1]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hN ho'
      exact h3.trans h2
  calc _ ≤ (sz.Bctl n t) ^ ((o : ℝ) / 2) := hB'
    _ = 1 * (sz.Bctl n t) ^ ((o : ℝ) / 2) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hη' hBo


/-! ## 4. The `t`-carrying fold class

The `BAExp14bS3` integrand is `t⁻¹ ×` the root average (Section 2), and `BAFoldLeaf` hides the `t^p`, `p ≥ 2`, of its weight (`ρ = BAS3Close_rho (2 + qq)
= t · BAS3Close_rho (1 + qq)`, `Graph/BAS3CloseC.lean`).  `BAFoldLeafT` keeps one factor `t` outside the weight, whose `ℓ¹` bounds are those of
`BAS3Close_rho (1 + qq)`; all 14 catalogue graphs belong to it (the kernel facts are those of the closure files, through `open private`). -/

/-- **The fold class with the factor `t`**: `BAFoldLeaf` (`Graph/BAS3CloseC.lean`) with the weight `t · ρ` in clause (i)
and the uniform `ℓ¹` bounds on `ρ` in clause (ii). -/
def BAFoldLeafT (q : BAPGraph (Fin 2)) : Prop :=
  ∃ (σ e : Bool) (ρ : ∀ (d : ℕ) (sz : Sizes d), (ℕ → ℂ) → ∀ n : ℕ, ℝ → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ),
    (∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y] =
          twLoop2X n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
            (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
              ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
            (fun c₁ c₂ c₃ c₄ => (t : ℂ) * ρ d sz z n t a b c₁ c₂ c₃ c₄ *
              (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
                (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)) a) ∧
    (∀ (d : ℕ), 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
      BAFlow sz κ ε 𝔠 𝔡 z → ∃ Cρ : ℝ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
        ∀ a b : Zd d (sz.L n), (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ))

/-- **Transfer**: the class depends on `q` only through its value. -/
theorem baFoldLeafT_congr : ∀ q q' : BAPGraph (Fin 2),
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι), q.val D ℓ = q'.val D ℓ) →
      BAFoldLeafT q → BAFoldLeafT q' := by
  rintro q q' h ⟨σ, e, ρ, h1, h2⟩
  refine ⟨σ, e, ρ, ?_, h2⟩
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω a b
  rw [← h1 d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω a b]
  simp only [h]

/-- The generic reduction of the closure (`BAS3Close_fold_gen_i` in `Graph/BAS3CloseC.lean`) with one factor `t` kept outside the weight: the weight `BAS3Close_rho (2 + qq)`
is `t · BAS3Close_rho (1 + qq)`. -/
private theorem BAExp14c_foldT_gen (q : BAPGraph (Fin 2)) (σ e : Bool) (qq : ℕ) (Zk Nk : BAS3Close_Kern)
    (hq : BAS3Close_Hq q σ e qq Zk Nk) (hbd : BAS3Close_Bd (1 + qq) Zk Nk) : BAFoldLeafT q := by
  refine ⟨σ, e, BAS3Close_rho (1 + qq) Zk Nk, ?_, hbd⟩
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω a b
  rw [BAS3Close_fold_gen_i q σ e qq Zk Nk hq d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω a b]
  refine congrArg (fun f => twLoop2X n _ _ _ f a) (funext fun c₁ => funext fun c₂ => funext fun c₃ => funext fun c₄ => ?_)
  simp only [BAS3Close_rho]
  ring

/-- **The catalogue**: the 14 stuck graphs, both roots `T3C-tr_k`, both tail charges, belong to `BAFoldLeafT`
(the weights of the closure have a spare factor `t`: `p = 2 + qq ≥ 2`). -/
theorem baS3FoldT_holds : ∀ (k : Bool) (j : Fin 7) (s : Bool), BAFoldLeafT (baS3Stuck k j s) := by
  intro k j s
  obtain ⟨j, hj⟩ := j
  interval_cases j <;> cases k
  · exact BAExp14c_foldT_gen _ s false 0 BAS3Close_kD BAS3Close_kD (BAS3Close_hq00 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_D BAS3Close_hN_D)
  · exact BAExp14c_foldT_gen _ s false 0 BAS3Close_kK BAS3Close_kD (BAS3Close_hq10 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_K BAS3Close_hN_D)
  · exact BAExp14c_foldT_gen _ s false 0 BAS3Close_kD BAS3Close_kK (BAS3Close_hq01 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_D BAS3Close_hN_K)
  · exact BAExp14c_foldT_gen _ s false 0 BAS3Close_kK BAS3Close_kK (BAS3Close_hq11 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_K BAS3Close_hN_K)
  · exact BAExp14c_foldT_gen _ s false 0 BAS3Close_kK BAS3Close_kD (BAS3Close_hq02 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_K BAS3Close_hN_D)
  · exact BAExp14c_foldT_gen _ s false 0 BAS3Close_kKK BAS3Close_kD (BAS3Close_hq12 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_KK BAS3Close_hN_D)
  · exact BAExp14c_foldT_gen _ s true 1 BAS3Close_kD BAS3Close_k1 (BAS3Close_hq03 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_D BAS3Close_hN_1)
  · exact BAExp14c_foldT_gen _ s true 1 BAS3Close_kK BAS3Close_k1 (BAS3Close_hq13 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_K BAS3Close_hN_1)
  · exact BAExp14c_foldT_gen _ s false 1 BAS3Close_kD BAS3Close_kB (BAS3Close_hq04 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_D BAS3Close_hN_B)
  · exact BAExp14c_foldT_gen _ s false 1 BAS3Close_kK BAS3Close_kB (BAS3Close_hq14 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_K BAS3Close_hN_B)
  · exact BAExp14c_foldT_gen _ s true 1 BAS3Close_kK BAS3Close_k1 (BAS3Close_hq05 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_K BAS3Close_hN_1)
  · exact BAExp14c_foldT_gen _ s true 1 BAS3Close_kKK BAS3Close_k1 (BAS3Close_hq15 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_KK BAS3Close_hN_1)
  · exact BAExp14c_foldT_gen _ s false 1 BAS3Close_kK BAS3Close_kB (BAS3Close_hq06 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_K BAS3Close_hN_B)
  · exact BAExp14c_foldT_gen _ s false 1 BAS3Close_kKK BAS3Close_kB (BAS3Close_hq16 s)
      (BAS3Close_Bd_of _ _ _ BAS3Close_hZ_KK BAS3Close_hN_B)

/-- **The closure with the `t`-carrying class**: every output of the three lists at `BAselStar`, fuel `2`,
both tail charges, is a `BAG5LeafProps` leaf or a `BAFoldLeafT` leaf. -/
def BAS3CloseT : Prop :=
  ∀ (r : Fin 3) (s : Bool), ∀ q ∈ BAS3expandRoot BAselStar 2 r s, BAG5LeafProps (fun _ _ => [q]) ∨ BAFoldLeafT q

theorem baS3CloseT_holds : BAS3CloseT := by
  intro r s q hq
  rcases baS3Close_mod r s q hq with h | ⟨k, j, hj⟩
  · exact Or.inl h
  · exact Or.inr (baFoldLeafT_congr (baS3Stuck k j s) q (fun D ℓ => (hj D ℓ).symm) (baS3FoldT_holds k j s))

/-! ## 5. The statement defs (proved in `Graph/BAExp14cB.lean`)

The leaf statement `BAG5LeafPrec` occurs only as the antecedent of `BAS3LeafAvg` and `BAExp14bS3OfLeaf`;
no public result takes it as a hypothesis binder. -/

/-- **The leaf statement** (as `LwGraphPrec1` in `Graph/LWExpTerm3.lean`): for every `P` with the leaf properties of `BAG5LeafProps` and every pair `(x, y)`,
`‖𝔼 P_{xy}‖ ≺ t^{n_W} η_t⁻¹ Bctl^{ord(P)/2}` at `BAlwData` over the carrier law, under the five premises of `BAExp14bS3`. -/
def BAG5LeafPrec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-- **`BAS3LeafAvg`**: given the leaf statement and the five premises, every
`q` that is a `BAG5LeafProps` leaf or a `BAFoldLeafT` leaf has `‖𝔼 W^{-2d} Σ_{x∈[a], y∈[b]} q_{xy}‖ ≺ t (1 - t)⁻¹ Bctl^{5/2}`, uniformly in the
block pair `(a, b)`.  A `BAG5LeafProps` leaf goes through `GtoAG` / (B.7) `Gammamuxy` pointwise (the leaf statement, per pair) and is then averaged, with the
`x ~ y` support; a fold leaf goes through the fold bound directly, in averaged form (`twFold2Prec` with `baS3Xprec_holds`; `𝔼`
through `BAExp14a_prec_integral`; the factor `t` restored afterwards). -/
def BAS3LeafAvg (d : ℕ) : Prop :=
  BAG5LeafPrec d →
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ q : BAPGraph (Fin 2), (BAG5LeafProps (fun _ _ => [q]) ∨ BAFoldLeafT q) →
        PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p _ => ‖∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n p.1, ∑ y ∈ twBlk n p.2,
              q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
                (BAExp14a_slc sz n ω)) ![x, y]) ∂μ‖)
          (fun n _ _ => t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))

/-- **`BAExp14bS3OfLeaf`** (the assembly): the leaf statement gives `BAExp14bS3` (per family, five premises), unchanged. -/
def BAExp14bS3OfLeaf (d : ℕ) : Prop := BAG5LeafPrec d → BAExp14bS3 d

end RBM.BA

end
