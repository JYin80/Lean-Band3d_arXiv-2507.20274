/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.HierarchyN
import RBM3D.Hierarchy.ContractionSecondLoop
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Gauss.LoopCoordinate
import RBM3D.Gauss.LoopGenerator

/-!
# The general-`n` loop generator (ST2-28, ticket T2103, part 1)

Port of RBM2D `Induction/LoopGenN.lean` at commit `c9a24cf` (cited `LoopGenN:<line>`; 575 lines
there), the pin `LoopGenN` of `Induction/HierVocab.lean`, onto the merged vocabulary.  Renaming
rules R1-R4 of `docs/tickets/ST1-COMMON.md`; `Z2 L → Zd d L`, `Idx L W → Idx d L W`,
`BlockIndex L W → Vtx d L W`, `Gsig → Gres`, `spectralZ → zt`, `gloop L W → loopL d L W`,
`Coord/gvar → CoordF/gvarF`, `SB L → SB d L g`, `W ^ 2 → W ^ d` (the block size `W^d`: `tr E_a = 1`,
`Σ_b E_b = W^{-d} 1`), `LLf/avgErr/llPairN/egtN → STLIM/STavgErrM/STllPairN/STegtM`.

## Main results

* `RBM.Ind.loopGenN` : for every `d L W`, coupling `g`, `3 ≤ L`, Hermitian `M` and loop `(σ, a)`,
  `genMat(𝓛_{σ,a}) = W^d Σ_{k<l} Σ_{x,y} 𝓛 S^{(B)} 𝓛`
  `+ W^d Σ_k Σ_{x,y} (𝓛_{(σ_k),(x)} - m(σ_k)) S^{(B)} 𝓛`
  (`eq:mainStoflow`, `1_2`, drift part, with `def_EwtG`).
* `RBM.Ind.stLoopGenNForm_holds` : the owed pin `STLoopGenNForm d` of `Induction/HierarchyN.lean`
  (DECISIONS §32), its type unchanged.
* `RBM.Ind.hierarchyN_holds` : the unconditional `HierarchyN d`
  (`hierarchyN_of_loopGenN d (stLoopGenNForm_holds d)`).

## Route (as in RBM2D, `LoopGenN:1-30`)

The Hessian of `genMat` along `coordinateMatrix c` is the coordinate Hessian of the flow sample
`ω_M` at the auxiliary time `1` (`LoopGenN:82-112`); the merged
`sum_coordinateSecondWordDeriv_allCuts` contracts it into same-edge and pair cuts; the spectral
derivative is a sum of single-edge insertions (`LoopGenN:113-236`) turned into single-edge cuts by
`neg_trace_scalarDrift_cutGlue_split`; the cut enumerations are reindexed (`LoopGenN:237-419`) and
the single-edge algebra uses `Σ_a S^{(B)}_{ab} = 1`, true for `3 ≤ L`
(`LoopGenN:436`, `LoopGenN_sum_SB_col`).

Every helper is `private` and prefixed `LoopGenN_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. The matrix bridge -/

section MatrixBridge

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- The real coordinates of a matrix: real parts on `true`, imaginary parts on `false`. -/
private def LoopGenN_omega (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Ω d L W :=
  fun c => if c.2.2 then (M c.1 c.2.1).re else (M c.1 c.2.1).im

/-- A Hermitian matrix is the Gaussian matrix of its coordinates. -/
private theorem LoopGenN_Xmat_omega {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    Xmat d L W (LoopGenN_omega M) = M := by
  ext i j
  change Xentry d L W (LoopGenN_omega M) i j = M i j
  rw [Xentry]
  simp only [LoopGenN_omega, ite_true, Bool.false_eq_true, ite_false]
  split_ifs with h1 h2
  · apply Complex.ext <;> simp
  · rw [← hM.apply i j]
    apply Complex.ext <;> simp
  · have hij : i = j := by
      rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
      · exact absurd h h1
      · exact h
      · exact absurd h h2
    subst hij
    exact hM.coe_re_apply_self i

/-- At the auxiliary flow time `1`, the flow sample of `ω_M` is `blockMat d L W M`. -/
private theorem LoopGenN_HflowBlock_one {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    HflowBlock d L W 1 (LoopGenN_omega M) = blockMat d L W M := by
  rw [HflowBlock, Hflow, Real.sqrt_one, Complex.ofReal_one, one_smul, LoopGenN_Xmat_omega hM]

end MatrixBridge

/-! ## 2. The second-derivative bridge -/

section SecondBridge

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- The line Hessian of the loop along `coordinateMatrix c` at a Hermitian `M` is the coordinate
Hessian of the flow sample `ω_M` at the auxiliary time `1`. -/
private theorem LoopGenN_deriv2 {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hI : I.WF) :
    deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) z I)) 0 =
      Matrix.trace (coordinateSecondWordDeriv d L W 1 (LoopGenN_omega M) c z (I.σ.zip I.a)) := by
  set ω := LoopGenN_omega M with hω
  set φ : ℝ → ℂ := fun s => loopL d L W (HflowBlock d L W 1 (Function.update ω c s)) z I with hφ
  have hfg : (fun y : ℝ =>
      loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) z I) =
      fun y => φ (y + ω c) := by
    funext y
    simp only [hφ, HflowBlock_update, hω, LoopGenN_HflowBlock_one hM, Real.sqrt_one, one_mul,
      add_sub_cancel_right]
    congr 1
  rw [hfg]
  have h1 : deriv (fun y : ℝ => φ (y + ω c)) = fun y => deriv φ (y + ω c) := by
    funext y
    exact deriv_comp_add_const _ _ _
  rw [h1, deriv_comp_add_const, zero_add]
  exact (hasDerivAt_deriv_gloop_update d L W 1 ω c hz I hI).deriv

end SecondBridge

/-! ## 3. The spectral bridge at a general Hermitian block matrix -/

section SpectralBridge

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- The signed word `Π G(σ) E_a` of a list of edges, at a general block matrix. -/
private def LoopGenN_word (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

private theorem LoopGenN_word_eq (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    LoopGenN_word H z l = gloopProd d L W H z ⟨l.map Prod.fst, l.map Prod.snd⟩ := by
  have hzip : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons p l ih => simp [ih]
  rw [gloopProd, hzip]
  rfl

/-- The derivative of the generic spectral flow: `d_u ztOf m E u = -m`. -/
private theorem LoopGenN_hasDerivAt_ztOf (m : ℂ) (E u : ℝ) : HasDerivAt (ztOf m E) (-m) u := by
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
  have h2 : HasDerivAt (fun v : ℝ => ((E : ℂ) + (1 - (v : ℂ)) * m)) (-m) u := by
    have h := (((hasDerivAt_const u (1 : ℂ)).sub h1).mul_const m).const_add (E : ℂ)
    simpa using h
  exact h2

/-- The spectral derivative of one signed resolvent at a fixed Hermitian matrix
(the generic-`H` form of the private `OneStep_hasDerivAt_spec0`). -/
private theorem LoopGenN_hasDerivAt_Gsig_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu : u < 1) (σ : Bool) :
    HasDerivAt (fun v : ℝ => Gres H (ztOf m E v) σ)
      (-(Gres H (ztOf m E u) σ *
        (PropSpin m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        Gres H (ztOf m E u) σ)) u := by
  have him : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im, etaOf]
    exact ne_of_gt (mul_pos (by linarith) hm)
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) (LoopGenN_hasDerivAt_ztOf m E u) hH him
      simpa only [PropSpin, ite_true, zero_sub, neg_smul, neg_neg] using h
  | false =>
      have hz : HasDerivAt (fun v : ℝ => (starRingEnd ℂ) (ztOf m E v))
          (-((starRingEnd ℂ) m)) u := by
        simpa using (LoopGenN_hasDerivAt_ztOf m E u).star
      have him' : ((starRingEnd ℂ) (ztOf m E u)).im ≠ 0 := by simpa using him
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) hz hH him'
      have hfun : (fun v : ℝ => Gres H (ztOf m E v) false) =
          fun v : ℝ => Gres H ((starRingEnd ℂ) (ztOf m E v)) true := by
        funext v
        simp [Gres]
      rw [hfun]
      have hG : Gres H (ztOf m E u) false = Gres H ((starRingEnd ℂ) (ztOf m E u)) true := by
        simp [Gres]
      rw [hG]
      simpa only [PropSpin, Bool.false_eq_true, ite_false, zero_sub, neg_smul, neg_neg] using h

/-- The scalar insertion at one selected edge. -/
private def LoopGenN_edgeTerm (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (m : ℂ) (E u : ℝ)
    (e : EdgeSplit (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  -(LoopGenN_word H (ztOf m E u) e.before *
    (Gres H (ztOf m E u) e.selected.1 *
        (PropSpin m e.selected.1 • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
      (Gres H (ztOf m E u) e.selected.1 * Eblk d L W e.selected.2 *
        LoopGenN_word H (ztOf m E u) e.after)))

/-- The product rule over the word: the spectral derivative is the sum of the edge insertions. -/
private theorem LoopGenN_hasDerivAt_word_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu : u < 1) (l : List (Bool × Zd d L)) :
    HasDerivAt (fun v : ℝ => LoopGenN_word H (ztOf m E v) l)
      (((edgeSplits l).map (LoopGenN_edgeTerm H m E u)).sum) u := by
  induction l with
  | nil =>
      simpa [LoopGenN_word, edgeSplits] using
        hasDerivAt_const u (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have h := ((LoopGenN_hasDerivAt_Gsig_spec hH hm E hu p.1).mul_const (Eblk d L W p.2)).mul ih
      have hfun : (fun v : ℝ => Gres H (ztOf m E v) p.1 * Eblk d L W p.2) *
          (fun v : ℝ => LoopGenN_word H (ztOf m E v) l) =
          fun v : ℝ => LoopGenN_word H (ztOf m E v) (p :: l) := by
        funext v
        rfl
      rw [hfun] at h
      refine h.congr_deriv ?_
      have hcons : ∀ e : EdgeSplit (Bool × Zd d L),
          LoopGenN_edgeTerm H m E u ⟨p :: e.before, e.selected, e.after⟩ =
            (Gres H (ztOf m E u) p.1 * Eblk d L W p.2) * LoopGenN_edgeTerm H m E u e := by
        intro e
        simp only [LoopGenN_edgeTerm, LoopGenN_word, List.foldr_cons, Matrix.mul_neg,
          Matrix.mul_assoc]
      simp only [edgeSplits, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        hcons, List.sum_map_mul_left]
      simp only [LoopGenN_edgeTerm, LoopGenN_word, List.foldr_nil, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.neg_mul]

/-- The spectral derivative of a loop at a fixed Hermitian block matrix. -/
private theorem LoopGenN_deriv_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu : u < 1) (I : Loop.LoopIdx (Zd d L)) :
    deriv (fun v : ℝ => loopL d L W H (ztOf m E v) I) u =
      ((edgeSplits (I.σ.zip I.a)).map
        (fun e => Matrix.trace (LoopGenN_edgeTerm H m E u e))).sum := by
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u
    (LoopGenN_hasDerivAt_word_spec hH hm E hu (I.σ.zip I.a))
  simp only [hT, Function.comp_def] at h
  have hfun : (fun v : ℝ => loopL d L W H (ztOf m E v) I) =
      fun v : ℝ => Matrix.trace (LoopGenN_word H (ztOf m E v) (I.σ.zip I.a)) := by
    funext v
    rfl
  rw [hfun, h.deriv, Matrix.trace_list_sum, List.map_map]
  rfl


/-- One edge insertion is a sum of single-edge cuts. -/
private theorem LoopGenN_trace_edgeTerm (H : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (m : ℂ) (E u : ℝ) (e : EdgeSplit (Bool × Zd d L)) :
    Matrix.trace (LoopGenN_edgeTerm H m E u e) =
      -(PropSpin m e.selected.1 * (W : ℂ) ^ d) *
        ∑ b : Zd d L, loopL d L W H (ztOf m E u)
          ((⟨e.before.map Prod.fst ++ e.selected.1 :: e.after.map Prod.fst,
              e.before.map Prod.snd ++ e.selected.2 :: e.after.map Prod.snd⟩ :
            Loop.LoopIdx (Zd d L)).cutGlue ((e.before.map Prod.fst).length + 1) b) := by
  have hpre : (e.before.map Prod.fst).length = (e.before.map Prod.snd).length := by simp
  have h := neg_trace_scalarDrift_cutGlue_split d L W H (ztOf m E u)
    (e.before.map Prod.fst) (e.after.map Prod.fst)
    (e.before.map Prod.snd) (e.after.map Prod.snd)
    e.selected.1 e.selected.2 (PropSpin m e.selected.1) hpre
  rw [← h, LoopGenN_edgeTerm, Matrix.trace_neg, LoopGenN_word_eq, LoopGenN_word_eq]

end SpectralBridge

/-! ## 4. Reindexing the cut enumerations -/

section Reindex

/-- A list sum over `List.range n` is the `Finset.range` sum. -/
private theorem LoopGenN_sum_listRange (n : ℕ) (f : ℕ → ℂ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- `Σ_{i<n} F(i+1) = Σ_{k ∈ [1,n]} F k`. -/
private theorem LoopGenN_sum_range_Icc (n : ℕ) (F : ℕ → ℂ) :
    ∑ i ∈ Finset.range n, F (i + 1) = ∑ k ∈ Finset.Icc 1 n, F k := by
  refine Finset.sum_nbij' (fun i => i + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]; omega
  · intro i _; simp
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro i _; rfl

/-- A sum over the edge enumeration, whose summand depends only on the one-based position. -/
private theorem LoopGenN_sum_edgeSplits {α : Type*} (l : List α) (f : EdgeSplit α → ℂ)
    (F : ℕ → ℂ) (h : ∀ e ∈ edgeSplits l, f e = F (e.before.length + 1)) :
    ((edgeSplits l).map f).sum = ∑ k ∈ Finset.Icc 1 l.length, F k := by
  rw [List.map_congr_left h]
  have hmap : (edgeSplits l).map (fun e => F (e.before.length + 1)) =
      ((edgeSplits l).map (fun e => e.before.length)).map (fun i => F (i + 1)) := by
    rw [List.map_map]
    rfl
  rw [hmap, edgeSplits_prefix_lengths, LoopGenN_sum_listRange, LoopGenN_sum_range_Icc]

/-- The sum of a `flatMap` is the sum of the inner sums. -/
private theorem LoopGenN_sum_flatMap {α β : Type*} (xs : List α) (g : α → List β) (f : β → ℂ) :
    ((xs.flatMap g).map f).sum = (xs.map fun x => ((g x).map f).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp

/-- A sum over the pair enumeration, whose summand depends only on the two one-based positions. -/
private theorem LoopGenN_sum_pairSplits {α : Type*} (l : List α) (f : PairSplit α → ℂ)
    (F : ℕ → ℕ → ℂ)
    (h : ∀ p ∈ pairSplits l,
      f p = F (p.before.length + 1) (p.before.length + p.middle.length + 2)) :
    ((pairSplits l).map f).sum =
      ∑ k ∈ Finset.Icc 1 l.length, ∑ l' ∈ Finset.Ioc k l.length, F k l' := by
  rw [List.map_congr_left h, pairSplits, LoopGenN_sum_flatMap]
  refine LoopGenN_sum_edgeSplits l _ _ fun e he => ?_
  have hlen : l.length = e.before.length + 1 + e.after.length := by
    have hr := edgeSplits_reconstruct l e he
    rw [← hr, List.length_append, List.length_cons]
    omega
  rw [List.map_map]
  rw [LoopGenN_sum_edgeSplits e.after _
    (fun j => F (e.before.length + 1) (e.before.length + j + 1)) (fun d _ => by
      simp only [Function.comp_apply]
      congr 1)]
  refine Finset.sum_nbij' (fun j => e.before.length + j + 1)
    (fun l' => l' - (e.before.length + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_Ioc]; omega
  · intro l' hl'; simp only [Finset.mem_Ioc] at hl'
    simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro l' hl'; simp only [Finset.mem_Ioc] at hl'; omega
  · intro j _; rfl

end Reindex

/-! ## 5. Identifying each cut term with the loop's own cuts -/

section Cuts

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- A selected edge of the zipped word of a well-formed loop splits that loop. -/
private theorem LoopGenN_edge_eq (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Zd d L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    I = ⟨e.before.map Prod.fst ++ e.selected.1 :: e.after.map Prod.fst,
      e.before.map Prod.snd ++ e.selected.2 :: e.after.map Prod.snd⟩ := by
  have hr := edgeSplits_reconstruct _ e he
  have h1 := congrArg (List.map Prod.fst) hr
  have h2 := congrArg (List.map Prod.snd) hr
  rw [List.map_fst_zip hI.le] at h1
  rw [List.map_snd_zip hI.ge] at h2
  simp only [List.map_append, List.map_cons] at h1 h2
  cases I with
  | mk σ a =>
      simp only at h1 h2
      subst h1 h2
      rfl

/-- Two selected edges of the zipped word of a well-formed loop split that loop. -/
private theorem LoopGenN_pair_eq (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (p : PairSplit (Bool × Zd d L)) (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    I = ⟨p.before.map Prod.fst ++ p.first.1 :: p.middle.map Prod.fst ++
          p.second.1 :: p.after.map Prod.fst,
      p.before.map Prod.snd ++ p.first.2 :: p.middle.map Prod.snd ++
          p.second.2 :: p.after.map Prod.snd⟩ := by
  have hr := pairSplits_reconstruct _ p hp
  have h1 := congrArg (List.map Prod.fst) hr
  have h2 := congrArg (List.map Prod.snd) hr
  rw [List.map_fst_zip hI.le] at h1
  rw [List.map_snd_zip hI.ge] at h2
  simp only [List.map_append, List.map_cons] at h1 h2
  cases I with
  | mk σ a =>
      simp only at h1 h2
      subst h1 h2
      rfl

/-- The sign at the selected edge. -/
private theorem LoopGenN_getD (b a : List (Bool × Zd d L)) (s : Bool) :
    (b.map Prod.fst ++ s :: a.map Prod.fst).getD (b.length + 1 - 1) false = s := by
  rw [Nat.add_sub_cancel, List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- Cut-and-glue at the edge after a matching prefix (RBM2D `LoopIdx.cutGlue_split`,
`Hierarchy/Operations.lean:40`; private copy). -/
private theorem LoopGenN_cutGlue_split (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a b : Zd d L) (h₁ : σ₁.length = a₁.length) :
    Loop.LoopIdx.cutGlue (σ₁.length + 1) b
      (⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : Loop.LoopIdx (Zd d L)) =
      ⟨σ₁ ++ s :: s :: σ₂, a₁ ++ b :: a :: a₂⟩ := by
  simp [Loop.LoopIdx.cutGlue, List.take_append, h₁]

private theorem LoopGenN_loopL_eq (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I = Matrix.trace (gloopProd d L W H z I) := rfl

private theorem LoopGenN_gloopProd_nil (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) :
    gloopProd d L W H z ⟨[], []⟩ = 1 := rfl

private theorem LoopGenN_gloopProd_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) :
    gloopProd d L W H z ⟨s :: σ, b :: a⟩ =
      Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩ := rfl

private theorem LoopGenN_gloopProd_append (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    {σ₁ : List Bool} {a₁ : List (Zd d L)} (h₁ : σ₁.length = a₁.length)
    (σ₂ : List Bool) (a₂ : List (Zd d L)) :
    gloopProd d L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩ =
      gloopProd d L W H z ⟨σ₁, a₁⟩ * gloopProd d L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp [gloopProd]
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, LoopGenN_gloopProd_cons, ih h, Matrix.mul_assoc]

/-- The rotated same-edge loop is the single-edge cut of the original loop. -/
private theorem LoopGenN_gloop_same (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (b a : List (Bool × Zd d L)) (s : Bool) (x p : Zd d L) :
    loopL d L W H z ⟨s :: (a.map Prod.fst ++ (b.map Prod.fst ++ [s])),
        x :: (a.map Prod.snd ++ (b.map Prod.snd ++ [p]))⟩ =
      loopL d L W H z ((⟨b.map Prod.fst ++ s :: a.map Prod.fst,
        b.map Prod.snd ++ x :: a.map Prod.snd⟩ : Loop.LoopIdx (Zd d L)).cutGlue (b.length + 1) p) := by
  have hb : (b.map Prod.fst).length = (b.map Prod.snd).length := by simp
  have ha : (a.map Prod.fst).length = (a.map Prod.snd).length := by simp
  have hc := LoopGenN_cutGlue_split (b.map Prod.fst) (a.map Prod.fst) (b.map Prod.snd)
    (a.map Prod.snd) s x p hb
  rw [List.length_map] at hc
  rw [hc]
  simp only [LoopGenN_loopL_eq, LoopGenN_gloopProd_cons, LoopGenN_gloopProd_append H z ha,
    LoopGenN_gloopProd_append H z hb, LoopGenN_gloopProd_nil]
  have h := Matrix.trace_mul_comm (Gres H z s * Eblk d L W x * gloopProd d L W H z
      ⟨a.map Prod.fst, a.map Prod.snd⟩)
    (gloopProd d L W H z ⟨b.map Prod.fst, b.map Prod.snd⟩ * (Gres H z s * Eblk d L W p))
  simp only [Matrix.mul_assoc, Matrix.mul_one] at h ⊢
  exact h

/-- The same-edge cut value at a selected edge, as a function of its one-based position. -/
private theorem LoopGenN_sameEdge {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (z : ℂ) (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Zd d L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    sameEdgeCutValue d L W g 1 (LoopGenN_omega M) z e =
      ∑ p : Zd d L, ∑ q : Zd d L, loopL d L W (blockMat d L W M) z (I.cutGlue (e.before.length + 1) p) *
        SB d L g p q * Matrix.trace (Gres (blockMat d L W M) z (I.σ.getD (e.before.length + 1 - 1) false) *
          Eblk d L W q) := by
  have hIe := LoopGenN_edge_eq I hI e he
  simp only [sameEdgeCutValue, segmentLoopIdx, LoopGenN_HflowBlock_one hM]
  rw [hIe, LoopGenN_getD]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [LoopGenN_gloop_same]
  congr 1
  simp [loopL]

/-- The pair cut value at two selected edges, as a function of their one-based positions. -/
private theorem LoopGenN_pairCut {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (z : ℂ) (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (p : PairSplit (Bool × Zd d L)) (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    pairCutValue d L W g 1 (LoopGenN_omega M) z p =
      ∑ v : Zd d L, ∑ w : Zd d L,
        loopL d L W (blockMat d L W M) z (I.cutGlueL (p.before.length + 1)
            (p.before.length + p.middle.length + 2) v) * SB d L g v w *
          loopL d L W (blockMat d L W M) z (I.cutGlueR (p.before.length + 1)
            (p.before.length + p.middle.length + 2) w) := by
  have hIp := LoopGenN_pair_eq I hI p hp
  simp only [pairCutValue, segmentLoopIdx, LoopGenN_HflowBlock_one hM, List.length_map]
  rw [← hIp]

/-- The spectral insertion at a selected edge, as a function of its one-based position. -/
private theorem LoopGenN_specEdge (H : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (m : ℂ) (E u : ℝ) (I : Loop.LoopIdx (Zd d L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Zd d L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    Matrix.trace (LoopGenN_edgeTerm H m E u e) =
      -(PropSpin m (I.σ.getD (e.before.length + 1 - 1) false) * (W : ℂ) ^ d) *
        ∑ b : Zd d L, loopL d L W H (ztOf m E u) (I.cutGlue (e.before.length + 1) b) := by
  have hIe := LoopGenN_edge_eq I hI e he
  rw [LoopGenN_trace_edgeTerm, List.length_map]
  conv_rhs => rw [hIe, LoopGenN_getD]


end Cuts

/-! ## 6. The single-edge algebra and the assembly -/

section Assembly

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- `⟨G̃(σ) E_a⟩ = 𝓛^{(1)}_{(σ),(a)} - m(σ)` (the body of `STavgErrM`, `def_EwtG`). -/
private def LoopGenN_avg (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool)
    (a : Zd d L) : ℂ :=
  loopL d L W (blockMat d L W M) (ztOf m E u) ⟨[σ], [a]⟩ - PropSpin m σ

/-- `⟨G̃(σ) E_a⟩ = ⟨G(σ) E_a⟩ - m(σ)`. -/
private theorem LoopGenN_avg_eq (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool)
    (a : Zd d L) :
    LoopGenN_avg m E u M σ a =
      Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) σ * Eblk d L W a) - PropSpin m σ := by
  simp only [LoopGenN_avg, loopL, List.zip_cons_cons, List.zip_nil_left, List.foldr_cons,
    List.foldr_nil, Matrix.mul_one]


/-- Column sums of `S^{(B)}` are `1`. -/
private theorem LoopGenN_sum_SB_col (hL : 3 ≤ L) (b : Zd d L) : ∑ a : Zd d L, SB d L g a b = 1 := by
  rw [← sum_SB_row d L g hL b]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact congrFun (congrFun (SB_transpose d L g) b) a

/-- `Σ_{a,b} (t_a - m) S_{ab} f_b = Σ_{p,q} g_p S_{pq} t_q - m Σ_b f_b`. -/
private theorem LoopGenN_sum_algebra (hL : 3 ≤ L) (f t : Zd d L → ℂ) (m : ℂ) :
    ∑ a' : Zd d L, ∑ b' : Zd d L, (t a' - m) * SB d L g a' b' * f b' =
      ∑ p : Zd d L, ∑ q : Zd d L, f p * SB d L g p q * t q - m * ∑ p : Zd d L, f p := by
  have hS : ∀ p q : Zd d L, SB d L g p q = SB d L g q p := fun p q =>
    congrFun (congrFun (SB_transpose d L g) q) p
  have h1 : ∑ a' : Zd d L, ∑ b' : Zd d L, t a' * SB d L g a' b' * f b' =
      ∑ p : Zd d L, ∑ q : Zd d L, f p * SB d L g p q * t q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hS q p]
    ring
  have h2 : ∑ a' : Zd d L, ∑ b' : Zd d L, m * SB d L g a' b' * f b' = m * ∑ p : Zd d L, f p := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, LoopGenN_sum_SB_col hL, mul_one]
  rw [← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

/-- The same-edge cuts and the spectral cuts of one edge combine into its `𝓔^{(G̃)}` term. -/
private theorem LoopGenN_edge_algebra (hL : 3 ≤ L) (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (I : Loop.LoopIdx (Zd d L)) (k : ℕ) :
    (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
        loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k p) * SB d L g p q *
          Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (I.σ.getD (k - 1) false) *
            Eblk d L W q) +
      -(PropSpin m (I.σ.getD (k - 1) false) * (W : ℂ) ^ d) *
        ∑ b : Zd d L, loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b) =
    (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
      LoopGenN_avg m E u M (I.σ.getD (k - 1) false) a * SB d L g a b *
        loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b) := by
  simp only [LoopGenN_avg_eq]
  rw [LoopGenN_sum_algebra hL (fun b => loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b))
    (fun a => Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (I.σ.getD (k - 1) false) *
      Eblk d L W a))]
  ring


end Assembly

/-- `genMat` along the generic flow `ztOf m E u` (the generic-`m` form of `Path/OneStep.lean:68`;
`genMat_eq_genMatOf` is `rfl`). -/
def genMatOf (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) (ztOf m E u) I)) 0 +
    deriv (fun v : ℝ => loopL d L W (blockMat d L W M) (ztOf m E v) I) u

theorem genMat_eq_genMatOf (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : Loop.LoopIdx (Zd d L)) :
    genMat d L W g E u M I = genMatOf d L W g (mE E) E u M I := rfl

/-- **`loopGenNOf`** (the generic form of `loopGenN`): the loop generator identity along the flow
`ztOf m E u` for every one-loop value `m` with `0 < m.im`, every coupling `g` of `S^{(B)}(g)` and `3 ≤ L`. -/
theorem loopGenNOf (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (m : ℂ) (E : ℝ) (hL : 3 ≤ L)
    (hm : 0 < m.im) (u : ℝ) (hu1 : u < 1) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    genMatOf d L W g m E u M (loopOf σ a) =
      (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 (loopOf σ a).length,
          ∑ l' ∈ Finset.Ioc k' (loopOf σ a).length, ∑ x : Zd d L, ∑ y : Zd d L,
        loopL d L W (blockMat d L W M) (ztOf m E u) ((loopOf σ a).cutGlueL k' l' x) * SB d L g x y *
          loopL d L W (blockMat d L W M) (ztOf m E u) ((loopOf σ a).cutGlueR k' l' y) +
        (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 (loopOf σ a).length, ∑ x : Zd d L, ∑ y : Zd d L,
          (loopL d L W (blockMat d L W M) (ztOf m E u)
              ⟨[(loopOf σ a).σ.getD (k' - 1) false], [x]⟩ -
            PropSpin m ((loopOf σ a).σ.getD (k' - 1) false)) * SB d L g x y *
          loopL d L W (blockMat d L W M) (ztOf m E u) ((loopOf σ a).cutGlue k' y) := by
  set I : Loop.LoopIdx (Zd d L) := loopOf σ a with hIdef
  have hI : I.WF := by simp [hIdef, loopOf, Loop.LoopIdx.WF]
  have hlen : (I.σ.zip I.a).length = I.length := by
    simp [Loop.LoopIdx.length, List.length_zip, hI.symm]
  have hz : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im, etaOf]
    exact ne_of_gt (mul_pos (by linarith) hm)
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  set l := I.σ.zip I.a with hl
  set ω := LoopGenN_omega M with hω
  set z := ztOf m E u with hzdef
  -- the three families of cut terms as functions of the one-based positions
  set Fs : ℕ → ℂ := fun k' => ∑ p : Zd d L, ∑ q : Zd d L,
    loopL d L W (blockMat d L W M) z (I.cutGlue k' p) * SB d L g p q *
      Matrix.trace (Gres (blockMat d L W M) z (I.σ.getD (k' - 1) false) * Eblk d L W q) with hFs
  set Fsp : ℕ → ℂ := fun k' => -(PropSpin m (I.σ.getD (k' - 1) false) * (W : ℂ) ^ d) *
    ∑ b : Zd d L, loopL d L W (blockMat d L W M) z (I.cutGlue k' b) with hFsp
  set Fp : ℕ → ℕ → ℂ := fun k' l' => ∑ v : Zd d L, ∑ w : Zd d L,
    loopL d L W (blockMat d L W M) z (I.cutGlueL k' l' v) * SB d L g v w *
      loopL d L W (blockMat d L W M) z (I.cutGlueR k' l' w) with hFp
  have hsame := LoopGenN_sum_edgeSplits l (sameEdgeCutValue d L W g 1 ω z) Fs
    (fun e he => LoopGenN_sameEdge hM z I hI e he)
  have hpair := LoopGenN_sum_pairSplits l (pairCutValue d L W g 1 ω z) Fp
    (fun p hp => LoopGenN_pairCut hM z I hI p hp)
  have hspec := LoopGenN_sum_edgeSplits l
    (fun e => Matrix.trace (LoopGenN_edgeTerm (blockMat d L W M) m E u e)) Fsp
    (fun e he => LoopGenN_specEdge (blockMat d L W M) m E u I hI e he)
  -- the left side
  have hlhs : genMatOf d L W g m E u M I =
      (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 I.length, Fs k' +
        (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k' I.length, Fp k' l' +
        ∑ k' ∈ Finset.Icc 1 I.length, Fsp k' := by
    rw [genMatOf, Finset.sum_congr rfl fun c _ => by rw [LoopGenN_deriv2 hM c hz I hI],
      sum_coordinateSecondWordDeriv_allCuts d L W g 1 zero_le_one ω z l,
      LoopGenN_deriv_spec hH hm E hu1 I, hsame, hpair, hspec, hlen]
    push_cast
    ring
  have hedge : ∑ k' ∈ Finset.Icc 1 I.length, ((W : ℂ) ^ d * Fs k' + Fsp k') =
      (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 I.length, ∑ x : Zd d L, ∑ y : Zd d L,
        LoopGenN_avg m E u M (I.σ.getD (k' - 1) false) x * SB d L g x y *
          loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k' y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => LoopGenN_edge_algebra hL m E u M I k'
  rw [hlhs]
  change _ = _ + (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 I.length, ∑ x : Zd d L, ∑ y : Zd d L,
        LoopGenN_avg m E u M (I.σ.getD (k' - 1) false) x * SB d L g x y *
          loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k' y)
  rw [← hedge, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hFp]
  ring

/-- **`loopGenN`** (RBM2D `LoopGenN`, `Induction/LoopGenN.lean:484`; `eq:mainStoflow`, `1_2`, drift part
with `def_EwtG`): the band statement, unchanged, is the generic `loopGenNOf` at `m = mE E`
(`zt E u = ztOf (mE E) E u` and `mSigma E = PropSpin (mE E)` by unfolding; `0 < (mE E).im` is `mE_im_pos`).
At `(L, W, g) = (sz.L n, sz.W n, sz.lam n)` the two terms are `STllPairN` and `STegtM`
(`stLoopGenNForm_holds`). -/
theorem loopGenN (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E : ℝ) (hL : 3 ≤ L) (hE : |E| < 2)
    (u : ℝ) (hu1 : u < 1) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    genMat d L W g E u M (loopOf σ a) =
      (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 (loopOf σ a).length,
          ∑ l' ∈ Finset.Ioc k' (loopOf σ a).length, ∑ x : Zd d L, ∑ y : Zd d L,
        loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlueL k' l' x) * SB d L g x y *
          loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlueR k' l' y) +
        (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 (loopOf σ a).length, ∑ x : Zd d L, ∑ y : Zd d L,
          (loopL d L W (blockMat d L W M) (zt E u)
              ⟨[(loopOf σ a).σ.getD (k' - 1) false], [x]⟩ -
            mSigma E ((loopOf σ a).σ.getD (k' - 1) false)) * SB d L g x y *
          loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlue k' y) :=
  loopGenNOf d L W g (mE E) E hL (mE_im_pos hE) u hu1 M hM σ a


/-- **`STLoopGenNForm` holds** (DECISIONS §32; `eq:mainStoflow`, `1_2`, drift part, with
`def_EwtG`): `genMat(𝓛_{σ,a}) = STllPairN + STegtM` at `(L, W, g) = (sz.L n, sz.W n, sz.lam n)`,
from `loopGenN` and `3 ≤ sz.L n` (`Sizes.three_le_L`). -/
theorem stLoopGenNForm_holds (d : ℕ) : STLoopGenNForm d := by
  intro sz n E hE u hu0 hu1 M hM k hk σ a
  exact loopGenN d (sz.L n) (sz.W n) (sz.lam n) E (sz.three_le_L n) hE u hu1 M hM σ a

/-- **`hierarchyN` unconditional** (RBM2D `hierarchyN`, `Induction/HierarchyN.lean:31`): the
general-`n` hierarchy identity, from `hierarchyN_of_loopGenN` and `stLoopGenNForm_holds`. -/
theorem hierarchyN_holds (d : ℕ) : HierarchyN d :=
  hierarchyN_of_loopGenN d (stLoopGenNForm_holds d)

/-- **G1 (band statement unchanged)**: the merged `loopGenN` has the type `loopGenNOf` gives at `m = mE E`. -/
theorem recovers_loopGenN : type_of% @loopGenN :=
  fun d L W g _ _ E hL hE u hu1 M hM _ σ a =>
    loopGenNOf d L W g (mE E) E hL (mE_im_pos hE) u hu1 M hM σ a

/-! ## Compiled nonempty instances

`loopGenN` at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 1/2`, `u = 1/2`, the non-scalar Hermitian
`M = X_{(0,1,true)}`, the loop `(+,-,+)`, `a = (0,1,2)` of length `k = 3` (`Idx 3 3 2` has `216`
sites).  `stLoopGenNForm_holds` and `hierarchyN_holds` at the merged admissible sequence `sz0`
(`RBM.Gauss.SizesInst.sz0`: `d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`), size index `0`, `E = 0`,
`u = 1/2`, `M = 1`, `k = 3`.  No hypothesis is left open. -/

section Instances

open RBM.Gauss.SizesInst

/-- The non-scalar Hermitian test matrix `X_{(0,1,true)} + X_{(1,0,true)}` of `Idx 3 3 2` (exactly
one of the two summands is nonzero, according to `idxKey`; `LoopGenN_M0_apply`). -/
private noncomputable def LoopGenN_M0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  coordinateMatrix 3 3 2 ((0 : Idx 3 3 2), (1 : Idx 3 3 2), true) +
    coordinateMatrix 3 3 2 ((1 : Idx 3 3 2), (0 : Idx 3 3 2), true)

private theorem LoopGenN_M0_isHermitian : LoopGenN_M0.IsHermitian :=
  (coordinateMatrix_isHermitian 3 3 2 _).add (coordinateMatrix_isHermitian 3 3 2 _)

/-- `LoopGenN_M0` is not the zero matrix: its `(0, 1)` entry is `1`. -/
private theorem LoopGenN_M0_apply : LoopGenN_M0 (0 : Idx 3 3 2) (1 : Idx 3 3 2) = 1 := by
  have h01 : (0 : Idx 3 3 2) ≠ 1 := by decide
  change Xentry 3 3 2 (Pi.single ((0 : Idx 3 3 2), (1 : Idx 3 3 2), true) 1) 0 1 +
    Xentry 3 3 2 (Pi.single ((1 : Idx 3 3 2), (0 : Idx 3 3 2), true) 1) 0 1 = 1
  simp only [Xentry]
  rcases idxKey_lt_or_eq_or_lt 3 3 2 (0 : Idx 3 3 2) 1 with h | h | h
  · simp [h, h01, h01.symm]
  · exact absurd h h01
  · simp [h, not_lt.mpr h.le, h01, h01.symm]

/-- **`loopGenN` at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`**, a non-scalar Hermitian `M`, `k = 3`. -/
private theorem LoopGenN_check_loopGenN :
    genMat 3 3 2 (1 / 2) (1 / 2) (1 / 2) LoopGenN_M0
        (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]) =
      (((2 : ℕ) : ℂ) ^ 3) * ∑ k' ∈ Finset.Icc 1 (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).length,
          ∑ l' ∈ Finset.Ioc k' (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).length,
          ∑ x : Zd 3 3, ∑ y : Zd 3 3,
        loopL 3 3 2 (blockMat 3 3 2 LoopGenN_M0) (zt (1 / 2) (1 / 2))
            ((loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).cutGlueL k' l' x) *
          SB 3 3 (1 / 2) x y *
          loopL 3 3 2 (blockMat 3 3 2 LoopGenN_M0) (zt (1 / 2) (1 / 2))
            ((loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).cutGlueR k' l' y) +
        (((2 : ℕ) : ℂ) ^ 3) * ∑ k' ∈ Finset.Icc 1 (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).length,
          ∑ x : Zd 3 3, ∑ y : Zd 3 3,
          (loopL 3 3 2 (blockMat 3 3 2 LoopGenN_M0) (zt (1 / 2) (1 / 2))
              ⟨[(loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).σ.getD (k' - 1) false], [x]⟩ -
            mSigma (1 / 2) ((loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).σ.getD (k' - 1) false)) *
            SB 3 3 (1 / 2) x y *
          loopL 3 3 2 (blockMat 3 3 2 LoopGenN_M0) (zt (1 / 2) (1 / 2))
            ((loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]).cutGlue k' y) :=
  loopGenN 3 3 2 (1 / 2) (1 / 2) le_rfl (by norm_num [abs_of_pos]) (1 / 2) (by norm_num)
    LoopGenN_M0 LoopGenN_M0_isHermitian
    ![true, false, true] ![(0 : Zd 3 3), 1, 2]

/-- **`stLoopGenNForm_holds` at `sz0`**, `k = 3`, `σ = (+,-,+)`, `a = (0,1,2)`, `M = 1`:
`genMat(𝓛) = STllPairN + STegtM`, unconditionally. -/
theorem LoopGenN_check_stLoopGenNForm_sz0 :
    genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]) =
      sz0.STllPairN 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]) +
        sz0.STegtM 0 0 (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]) :=
  stLoopGenNForm_holds 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) _ _

/-- **`hierarchyN_holds` at `sz0`**, `k = 3`, `σ = (+,-,+)`, `a = (0,1,2)`, `M = 1`, unconditionally
(`HierarchyN_check_sz0` of `Induction/HierarchyN.lean` with its hypothesis `STLoopGenNForm 3`
discharged). -/
theorem LoopGenN_check_hierarchyN_sz0 :
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
  hierarchyN_holds 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) _ _

/-- **Generic non-band instance**: `loopGenNOf` at `m = i` (`0 < m.im`), `E = 3` (outside the band,
`|E| ≥ 2`, where `mE E` is not in the upper half-plane), `d = 3`, `L = 3`, `W = 2`, `g = 1/2`,
`u = 1/2`, the non-scalar Hermitian `LoopGenN_M0`, the loop `(+,-,+)`, `a = (0,1,2)`; no `BA/*` import. -/
example :=
  loopGenNOf 3 3 2 (1 / 2) Complex.I 3 le_rfl (by simp) (1 / 2) (by norm_num)
    LoopGenN_M0 LoopGenN_M0_isHermitian ![true, false, true] ![(0 : Zd 3 3), 1, 2]

/-- The generic theorem at the band value `m = mE (1/2)` (the instance of `loopGenN` above, through
`recovers_loopGenN`). -/
example :=
  loopGenNOf 3 3 2 (1 / 2) (mE (1 / 2)) (1 / 2) le_rfl (mE_im_pos (by norm_num [abs_of_pos])) (1 / 2)
    (by norm_num) LoopGenN_M0 LoopGenN_M0_isHermitian ![true, false, true] ![(0 : Zd 3 3), 1, 2]

end Instances

end RBM.Ind

end

#print axioms RBM.Ind.loopGenNOf
#print axioms RBM.Ind.loopGenN
#print axioms RBM.Ind.recovers_loopGenN
#print axioms RBM.Ind.genMat_eq_genMatOf
#print axioms RBM.Ind.stLoopGenNForm_holds
#print axioms RBM.Ind.hierarchyN_holds
