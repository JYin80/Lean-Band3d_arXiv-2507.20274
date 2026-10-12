/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BALocReg2
import RBM3D.Graph.BALocReg1B
import RBM3D.Graph.BAShapeO2B
import RBM3D.Graph.BAEngine

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.show false
set_option linter.style.openClassical false

/-!
# BA-L L3b2b (T2469), part 2: the path invariant at the shapes `e2`, `macroA`, `macroB`, the closed step and contract (1)-(5), the composed statement

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:172-199` (the band proof of (1)-(5)), `:363` (`lanlw`), `:376-387` (`lem_lweight`), `:393-405` (`GGGamma`), `:416` (the block Anderson model keeps the path properties).
Design: `docs/reports/T2387-design.md` §6 row L3b2, `docs/tickets/T2469.md` targets 1 (b)-(d), 2, 3, 4 (split `BALocReg2 | BALocReg2B`, CONTROL H257 (3)).
Part 1 is `Graph/BALocReg2.lean` (target 1 (a): the 18 term lemmas and the five list forms).

## Contents (namespace `RBM.Graph`; private helpers carry the stem `BALocReg2B_`, the instance data the namespace `BALocReg2BInst`)

1. **Outputs and tags**: the path form of the group lemma of `BAShapeO2B` (a group of outputs whose terms carry the invariant carries it to the packed outputs), and the tag lemmas (copies of the
   private helpers of `BAShapeO2B`, under the stem).
2. **Stage 2, target 1 (b)**: the intermediates `Γ.BAScost_trA p` (macro (a): the edge inside an atom becomes the blue loop `Ǧ_{ββ}`) and `Γ.BAScost_trB p q` (macro (b): `(y', a')`, `(a, y)` become
   `(y', β)`, `(β, y)`), each one replacement of the selected edges (`BALocReg2_pathAt_ext2`, `localReg2_VRepl.same`); then the terms of `tr.lw2`, `tr.lw4` (resp. `tr.gg2`, `tr.gg4`) at the
   transfer graph, route (β) (`BALocReg2B_macroA`, `BALocReg2B_macroB`: the path twins of `BAShapeO2B_macroA`, `_macroB`).
3. **Target 1 (c), (d)**: `baShapePath_e2_tn`, `baShapePath_macroA_tn`, `baShapePath_macroB_tn` and `baPathBinder_holds` (the hypothesis `hX` of `baPathStep_holds`, `baLocReg15_holds`).
4. **Target 2**: `baPathStep_closed`, `baLocReg15_closed` (no hypothesis).
5. **Target 3**: `baShapeLLBinder_holds` (the shape binder of `baEngine_assemble`, `ba_localregularX`, discharged with the three `baShapeLL_*_tn`), `baLocRegConcl_upto5` (any lists with `BALocRegConcl`
   carry (1)-(5)), `ba_localregular_upto5` (the engine statement with (1)-(5), no binder).
6. **Target 4, instances**: the moved shapes at the R1 witnesses; a weight step with an `e2` output at a start term (by a good renaming of the concrete start term); stage 2 at `P_B`, `P_C`; target 2 at the twisted `edge` step and at the reached locally standard graph; target 3 at the flow point.

C1: combinatorial except `ba_localregular_upto5` (data `BASelf`, `0 ≤ t < 1`, only through the merged `ba_localregularX`).  No `inductive`, no new `Prop` def.  No port from `../RBM1D`, `../RBM2D`.
-/

noncomputable section

namespace RBM.Graph

local macro "BALocReg2B_simp0" : tactic => `(tactic| simp only [SEdge.localReg2_cends_mk, SEdge.localReg2_cends_map, SEdge.localReg2_cends, Prod.map_apply, Sym2.map_mk,
  localReg2_mapMS, List.map_cons, List.map_nil, Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe,
  Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq, BALocReg2_cends_bpS, BALocReg2_bpS_σ, BALocReg2_bpS_src, BALocReg2_bpS_dst, SEdge.map])

local macro "BALocReg2B_msnorm" : tactic => `(tactic| (BALocReg2B_simp0; try abel))

/-! ## 1. Outputs and tags -/

section Outs

/-- **The path form of the group lemma** (`BAShapeO2B_group`, private there): a group of outputs of `outsT` whose terms carry the invariant of `P.g` carries it, at the image, to the packed outputs. -/
private theorem BALocReg2B_group {P : BAPGraph (Fin 2)} {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (sh : BAShape) (hTs : ∀ T ∈ Ts, ∀ (k : ℕ) (a b : P.E'), BALocReg1_PathAt P.g k a b → BALocReg1_PathAt T k a b)
    {Q : BAPGraph (Fin 2)} (hQ : (sh, Q) ∈ P.outsT tg Ts) : ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k := by
  obtain ⟨T, hT, T', hT', -, rfl⟩ := BASim_mem_outsT P tg Ts sh Q hQ
  intro k hk
  exact BALocReg1_pathInv2_pack P T (hTs T hT k _ _ hk) T'.packMerge (List.mem_map.2 ⟨T', hT', rfl⟩)

/-- a group none of whose tags is `sh` has no output tagged `sh` (copy of the private `BAShapeO2B_group_ne`) -/
private theorem BALocReg2B_group_ne {P : BAPGraph (Fin 2)} {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (sh : BAShape) (hne : ∀ T', tg T' ≠ sh) {Q : BAPGraph (Fin 2)} (hQ : (sh, Q) ∈ P.outsT tg Ts) : False := by
  obtain ⟨T, -, T', -, h, -⟩ := BASim_mem_outsT P tg Ts sh Q hQ
  exact hne T' h

private theorem BALocReg2B_tagStd_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (k : ℕ) (sh : BAShape)
    (h1 : sh ≠ BAShape.e2) (h2 : sh ≠ BAShape.band) (T' : BAGraph E (I ⊕ Fin k)) : Γ.tagStd k T' ≠ sh := by
  unfold BAGraph.tagStd
  split_ifs
  · exact fun h => h1 h.symm
  · exact fun h => h2 h.symm

private theorem BALocReg2B_tagT1_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (sh : BAShape)
    (h1 : sh ≠ BAShape.e1) (h2 : sh ≠ BAShape.band) (T' : BAGraph E (I ⊕ Fin 2)) : Γ.tagT1 T' ≠ sh := by
  unfold BAGraph.tagT1
  split_ifs
  · exact fun h => h1 h.symm
  · exact fun h => h2 h.symm

/-- the data of the `gg` and `ggSplit` constructors: the two edges are in the solid list (copy of the private `BAShapeO2B_mem_pq`) -/
private theorem BALocReg2B_mem_pq {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : p.1 ∈ Γ.solid ∧ q.1 ∈ Γ.solid := by
  have h := BAShapeO2_perm_pq Γ p q hp hq
  exact ⟨h.symm.subset (by simp), h.symm.subset (by simp)⟩

end Outs

/-! ## 2. Stage 2 (target 1 (b)) -/

section Stage2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The macro (a) intermediate** (`BAScostLL_macroA`, `BAScost:1057`): the edge `p.1 = Ǧ_{xy}` inside an atom (`[x] = [y]` after the two `M`-dots) is replaced by the loop `Ǧ_{ββ}` in the molecule of `x`;
one replacement of a loop by a loop (`localReg2_VRepl.same` with `D₁ = {p.1}`, `D₂ = {Ǧ_{ββ}}`). -/
theorem BALocReg2B_trA (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (Γ.BAScost_trA p) k a b := by
  intro k a b h
  obtain ⟨hσ, -⟩ := hp1
  unfold BAGraph.BAScost_trA
  refine BALocReg2_pathAt_ext2 Γ [p.1] p.2 (by simpa using lwSplit_perm Γ.solid p hp) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hy : μ (owxEmb 2 p.1.dst) = μ (owxEmb 2 p.1.src) :=
    ((hmd (bpM (bpv 0) (owxEmb 2 p.1.dst)) (by simp [hX, BAGraph.ext])).symm).trans hα
  refine localReg2_VRepl.same μ {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst))} 0 0 {(true, s(bpv 1, bpv 1))} ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Multiset.mem_singleton] at hs
    subst hs
    simp [Sym2.mk_isDiag_iff, hy]
  · intro s hs
    rw [Multiset.mem_singleton] at hs
    subst hs
    simp [Sym2.mk_isDiag_iff]
  · exact BALocReg2_cov _ true (bpv 1) (bpv 1) (μ (owxEmb 2 p.1.src)) hβ hβ ⟨(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), by simp, rfl, by simp⟩
  · rfl
  · BALocReg2B_simp0
    simp only [hσ]
  · BALocReg2B_simp0

/-- **The macro (b) intermediate** (`BAScostLL_macroB`, `BAScost:1237`): the pair `(a, y)` (`p.1`), `(y', a')` (`q.1`) with `[a] = [a']` becomes `(β, y)`, `(y', β)`, `β` in the molecule of `a`; the molecular
edges do not change (`localReg2_VRepl.same` with `D₁ = D₂ = 0`, the two edges read in the molecules agree). -/
theorem BALocReg2B_trB (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (Γ.BAScost_trB p q) k a b := by
  intro k a b h
  obtain ⟨hσp, -⟩ := hp1
  obtain ⟨hσq, -⟩ := hq1
  unfold BAGraph.BAScost_trB
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hx' : μ (owxEmb 2 q.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 0) (owxEmb 2 q.1.dst)) (by simp)).symm.trans hα
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 q.1.dst))}
    {(true, s(owxEmb 2 q.1.src, bpv 1)), (true, s(bpv 1, owxEmb 2 p.1.dst))} 0 (by simp) (by simp) (by simp) ?_ ?_ ?_
  · BALocReg2B_simp0
    simp only [hβ, hx']
    try abel
  · BALocReg2B_simp0
    simp only [hσp, hσq]
    try abel
  · BALocReg2B_simp0
    try abel

/-- **Stage 2 of macro step (a), route (β)** (`BAShapeO2B_macroA`): every term of `lw2`, `lw4` at the loop `Ǧ_{ββ}` of the transfer graph `tr` carries the invariant of `Γ`:
`BALocReg2B_trA` composed with the weight lists of `Graph/BALocReg2` at `Γ := tr`. -/
theorem BALocReg2B_macroA (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) :
    (∀ X ∈ (Γ.BAScost_trA p).lw2 (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))),
      ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b) ∧
    (∀ X ∈ (Γ.BAScost_trA p).lw4 (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))),
      ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b) := by
  have hrest : ∀ e ∈ p.2, e ∈ Γ.solid := fun e he => (lwSplit_perm Γ.solid p hp).symm.subset (List.mem_cons_of_mem _ he)
  have hNtr : (Γ.BAScost_trA p).Normal :=
    BAShapeO2B_ext_normal Γ hN p.2 hrest _ (by intro e he; simp at he; subst he; rfl) _ _
  have hpp : (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))) ∈ lwSplit (Γ.BAScost_trA p).solid :=
    BAShapeO2B_lwSplit_last (p.2.map (SEdge.map (owxEmb 2))) (bpS true (bpv 1) (bpv 1))
  have hpp1 : (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).σ = true ∧ (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).circ = true ∧
      (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).src = (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).dst := ⟨rfl, rfl, rfl⟩
  have hA := BALocReg2B_trA Γ p hp hp1
  exact ⟨fun X hX k a b h => BALocReg2_lw2 _ hNtr _ hpp hpp1 X hX k a b (hA k a b h),
    fun X hX k a b h => BALocReg2_lw4 _ hNtr _ hpp hpp1 X hX k a b (hA k a b h)⟩

/-- **Stage 2 of macro step (b), route (β)** (`BAShapeO2B_macroB`): the same for `gg2`, `gg4` at the pair `Ǧ_{βy}`, `Ǧ_{y'β}` of the transfer graph `tr`; `β` is an atom of its own. -/
theorem BALocReg2B_macroB (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    (∀ X ∈ (Γ.BAScost_trB p q).gg2 (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
      (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2))),
      ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b) ∧
    (∀ X ∈ (Γ.BAScost_trB p q).gg4 (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
      (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2))),
      ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b) := by
  have hperm0 := BAShapeO2_perm_pq Γ p q hp hq
  have hrest : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he => hperm0.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
  have hNtr : (Γ.BAScost_trB p q).Normal :=
    BAShapeO2B_ext_normal Γ hN q.2 hrest _ (by intro e he; simp at he; rcases he with rfl | rfl <;> rfl) _ _
  have hpp : (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) ∈
      lwSplit (Γ.BAScost_trB p q).solid := by
    have h := BAShapeO2B_lwSplit_last (q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) (bpS true (bpv 1) (owxEmb 2 p.1.dst))
    rw [List.append_assoc] at h
    exact h
  have hqq : (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2))) ∈
      lwSplit (q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) :=
    BAShapeO2B_lwSplit_last (q.2.map (SEdge.map (owxEmb 2))) (bpS true (owxEmb 2 q.1.src) (bpv 1))
  have hmdβ : ∀ m ∈ [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)], m.x ≠ (bpv 1 : E ⊕ (I ⊕ Fin 2)) ∧ m.y ≠ bpv 1 := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp [bpM, bpv, owxEmb] <;> (rcases p.1.src with a | a <;> rcases q.1.dst with b | b <;> simp [owxEmb])
  have hwfβ1 := BAShapeO2B_fresh_wf Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)] 1 hmdβ (w := owxEmb 2 p.1.dst) (by
      rcases p.1.dst with a | a <;> simp [owxEmb, bpv])
  have hwfβ2 := BAShapeO2B_fresh_wf Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)] 1 hmdβ (w := owxEmb 2 q.1.src) (by
      rcases q.1.src with a | a <;> simp [owxEmb, bpv])
  have hB := BALocReg2B_trB Γ p q hp hq hp1 hq1 hsame hwf1 hwf2
  have hp1' : (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (owxEmb 2 p.1.dst)).σ = true ∧ (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (owxEmb 2 p.1.dst)).circ = true := ⟨rfl, rfl⟩
  have hq1' : (bpS true (owxEmb 2 q.1.src : E ⊕ (I ⊕ Fin 2)) (bpv 1)).σ = true ∧ (bpS true (owxEmb 2 q.1.src : E ⊕ (I ⊕ Fin 2)) (bpv 1)).circ = true := ⟨rfl, rfl⟩
  exact ⟨fun X hX k a b h => BALocReg2_gg2 _ hNtr _ _ hpp hqq hp1' hq1' rfl hwfβ1.1 hwfβ2.2.1 hwfβ1.2.2 X hX k a b (hB k a b h),
    fun X hX k a b h => BALocReg2_gg4 _ hNtr _ _ hpp hqq hp1' hq1' rfl hwfβ1.1 hwfβ2.2.1 hwfβ1.2.2 X hX k a b (hB k a b h)⟩

end Stage2

/-! ## 3. Target 1 (c), (d): the shapes `e2`, `macroA`, `macroB` of `BAFrameStepTN` -/

section Shapes

/-- **Target 1 (c): `BAShapePath e2 BAFrameStepTN`.**  An `e2` output of a step is a packed term of the partition of a stage-1 builder term `X` of the step (the `tagT1` groups and the
constant-tag groups are never tagged `e2`); the term lemmas and the lists of `Graph/BALocReg2` carry the invariant from `P.g` to `X`, and `BALocReg1_pathInv2_pack` to the packed output. -/
theorem baShapePath_e2_tn : BAShapePath BAShape.e2 BAFrameStepTN := by
  rintro P LT ⟨hN, hF⟩ Q hQ
  cases hF with
  | weight p hp h =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BALocReg2B_group _ _ _ (BALocReg2_lw2 P.g hN p hp h) hQ
    · exact BALocReg2B_group _ _ _ (BALocReg2_lw4 P.g hN p hp h) hQ
  | within p hp h =>
    simp only [BAPGraph.withinOutsT, List.mem_append] at hQ
    rcases hQ with (hQ | hQ) | hQ
    · exact BALocReg2B_group _ _ _ (BALocReg2_within P.g hN p hp ⟨h.1, h.2.1⟩ h.2.2.2) hQ
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · refine BALocReg2B_group _ _ _ (fun X hX => ?_) hQ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
      exact BALocReg2_lanlwD P.g hN p hp h q hq
  | gg p hp q hq h x hx hwf hint hnb =>
    obtain ⟨hpm, hqm⟩ := BALocReg2B_mem_pq P.g p q hp hq
    have hxy : q.1.dst = p.1.src := by rw [hx.1, hx.2]
    have hint' : P.g.intAtom p.1.src = true := by rw [hx.1]; exact hint
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BALocReg2B_group _ _ _ (BALocReg2_gg2 P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hxy (hwf _ hpm) (hwf _ hqm) hint') hQ
    · exact BALocReg2B_group _ _ _ (BALocReg2_gg4 P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hxy (hwf _ hpm) (hwf _ hqm) hint') hQ
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    have hq : q ∈ lwSplit p.2 := List.mem_of_getElem? hj
    obtain ⟨hpm, hqm⟩ := BALocReg2B_mem_pq P.g p q hp hq
    have hsame' : P.g.sameAtom p.1.src q.1.dst = true := by rw [hx.1, hx.2]; exact hsame
    have hint' : P.g.intAtom p.1.src = true := by rw [hx.1]; exact hint
    simp only [BAPGraph.splitOutsT, List.mem_append] at hQ
    rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · refine BALocReg2B_group _ _ _ (fun X hX => ?_) hQ
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hX
      exact BALocReg2_lanlwD P.g hN p hp ⟨h.1, h.2.1⟩ q' (List.mem_of_mem_eraseIdx hq')
    · refine BALocReg2B_group _ _ _ (fun X hX => ?_) hQ
      rw [List.mem_singleton] at hX
      subst hX
      exact BALocReg2_ggSplitD1 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm) hint'
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim

/-- **Target 1 (c): `BAShapePath macroA BAFrameStepTN`.**  Only `within` tags `macroA`, all of it at stage 2: the outputs of `lw2`, `lw4` at the loop `Ǧ_{ββ}` of the transfer graph, route (β)
(`BALocReg2B_macroA`: `BALocReg2B_trA` composed with the weight lists at `Γ := tr`), packed by `BALocReg1_pathInv2_pack`. -/
theorem baShapePath_macroA_tn : BAShapePath BAShape.macroA BAFrameStepTN := by
  rintro P LT ⟨hN, hF⟩ Q hQ
  cases hF with
  | weight p hp h =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | within p hp h =>
    simp only [BAPGraph.withinOutsT, List.mem_append] at hQ
    rcases hQ with (hQ | hQ) | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact BALocReg2B_group _ _ _ (BALocReg2B_macroA P.g hN p hp ⟨h.1, h.2.1⟩).1 hQ
    · exact BALocReg2B_group _ _ _ (BALocReg2B_macroA P.g hN p hp ⟨h.1, h.2.1⟩).2 hQ
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | gg p hp q hq h x hx hwf hint hnb =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    simp only [BAPGraph.splitOutsT, List.mem_append] at hQ
    rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim

/-- **Target 1 (c): `BAShapePath macroB BAFrameStepTN`.**  Only `ggSplit` tags `macroB`: stage 1 is `d2`-`d4` (`BALocReg2_ggSplitD2`-`D4`), stage 2 is `gg2`, `gg4` at the pair of the
transfer graph (route (β), `BALocReg2B_macroB`). -/
theorem baShapePath_macroB_tn : BAShapePath BAShape.macroB BAFrameStepTN := by
  rintro P LT ⟨hN, hF⟩ Q hQ
  cases hF with
  | weight p hp h =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | within p hp h =>
    simp only [BAPGraph.withinOutsT, List.mem_append] at hQ
    rcases hQ with (hQ | hQ) | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | gg p hp q hq h x hx hwf hint hnb =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    have hq : q ∈ lwSplit p.2 := List.mem_of_getElem? hj
    obtain ⟨hpm, hqm⟩ := BALocReg2B_mem_pq P.g p q hp hq
    have hsame' : P.g.sameAtom p.1.src q.1.dst = true := by rw [hx.1, hx.2]; exact hsame
    simp only [BAPGraph.splitOutsT, List.mem_append] at hQ
    rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BALocReg2B_group_ne _ _ _ (BALocReg2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · refine BALocReg2B_group _ _ _ (fun X hX => ?_) hQ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl
      · exact BALocReg2_ggSplitD2 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)
      · exact BALocReg2_ggSplitD3 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)
      · exact BALocReg2_ggSplitD4 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)
    · exact BALocReg2B_group _ _ _ (BALocReg2B_macroB P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)).1 hQ
    · exact BALocReg2B_group _ _ _ (BALocReg2B_macroB P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)).2 hQ

/-- **Target 1 (d): the path binder** (the hypothesis `hX` of `baPathStep_holds` (`BALocReg1:631`) and of `baLocReg15_holds` (`BALocReg1B:264`), verbatim). -/
theorem baPathBinder_holds : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN := by
  rintro sh (rfl | rfl | rfl)
  · exact baShapePath_e2_tn
  · exact baShapePath_macroA_tn
  · exact baShapePath_macroB_tn

end Shapes

/-! ## 4. Target 2: the twin of `LocalRegular2`, closed -/

/-- **Target 2: the path step of the tagged BA step, no hypothesis** (band `pathInv2_locStep`, `LocalRegular2:1582`): `baPathStep_holds` at `baPathBinder_holds`. -/
theorem baPathStep_closed : BAPathStep (untag BALocStepT) := baPathStep_holds baPathBinder_holds

/-- **Target 2: the contract (1)-(5) of L3b1 with no hypothesis** (band `lw_localregular_upto5`, `LocalRegular2:1857`): `baLocReg15_holds` at `baPathBinder_holds`. -/
theorem baLocReg15_closed : BALocReg15 := baLocReg15_holds baPathBinder_holds

/-! ## 5. Target 3: the composed statement -/

/-- **Target 3 (a): the shape binder of `baEngine_assemble` and `ba_localregularX`** (`BAEngine:268, 335`), verbatim.  Discharged with `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn`
(the closing step inside `baLocReg6_holds`, `BAShapeO2B:356-359`). -/
theorem baShapeLLBinder_holds : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN := by
  rintro sh (rfl | rfl | rfl)
  · exact baShapeLL_e2_tn
  · exact baShapeLL_macroA_tn
  · exact baShapeLL_macroB_tn

/-- **Target 3 (b): any lists with `BALocRegConcl` carry (1)-(5)** (twin of `lw_localregular_upto5`, `LocalRegular2:1857`; DECISIONS §265 (4)): at every `Q ∈ outs ++ errs`, `PathInv2 p`, `n_M ≤ p`,
`LocReg2` on the image (conjunct (c) gives the start term `P0` and `BAReach`, then `baLocReg15_closed`); at every `Q ∈ outs` (locally standard by conjunct (a)) `LocReg1`, `LocReg345` on the image
and on the shadow. -/
theorem baLocRegConcl_upto5 : ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))), BALocRegConcl p c K0 d D outs errs →
    (∀ Q ∈ outs ++ errs, Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p) ∧
      ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p := by
  intro p c K0 d D outs errs hC
  have key : ∀ Q ∈ outs ++ errs, Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p ∧
      (Q.g.LocStd → PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p) := by
    intro Q hQ
    obtain ⟨P0, hP0, hreach, -⟩ := hC.2.2.1 Q hQ
    exact baLocReg15_closed p P0 hP0 _ Q hreach
  refine ⟨fun Q hQ => ⟨(key Q hQ).1, (key Q hQ).2.1, (key Q hQ).2.2.1⟩, fun Q hQ => ?_⟩
  exact (key Q (List.mem_append_left _ hQ)).2.2.2 (hC.1 Q hQ).1

/-- **Target 3 (c): the BA `lem:localregular` with (1)-(5), no binder** (twin of `lw_localregular_upto5`, `LocalRegular2:1857`): one pair of lists with `BALocRegConcl`, at least `p` black waved edges in
every graph (`ba_localregularX` at `baShapeLLBinder_holds`), and the conclusions of `baLocRegConcl_upto5`. -/
theorem ba_localregular_upto5 : ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ (∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)) ∧
      (∀ Q ∈ outs ++ errs, Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p) ∧
        ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p := by
  intro p c hc K0 d D
  obtain ⟨outs, errs, hC, hw⟩ := ba_localregularX baShapeLLBinder_holds p c hc K0 d D
  exact ⟨outs, errs, hC, hw, (baLocRegConcl_upto5 p c K0 d D outs errs hC).1, (baLocRegConcl_upto5 p c K0 d D outs errs hC).2⟩

/-! ## 6. Nonempty instances (target 4), every deterministic hypothesis discharged

The witnesses are those of R1 (`BASimInst`: `P_A` `gg`, `P_B` `within`, `P_C` `ggSplit`, `P_W` `weight`) and of L3b1 (`BALocReg1Inst.baPEr`, `edge`).  The invariant of the parent is satisfied, not assumed: `PathInv2 2` at `P_C` is
`BALocReg1Inst.pathInv2_C`, `PathInv2 1` at `baPEr` is `pathInv2_Er`, and the hand-built families at `P_A` (`k = 2`), `P_B` (`k = 1`) and the weight witness `baPL` (`k = 1`) are `BALocReg2Inst.pathInv2_A`, `_B`, `_L` of `Graph/BALocReg2`. -/

section Inst
open BASimInst

/-! ### A weight step with an `e2` output at a start term of `p = 2`

The outputs of a step at a start term live over the quotient types of `LGraph.merge`, on which `decide` does not run; as in `BALocReg1B_reach_locStd` the start term `P0 = D0.packMerge`
(`D0 = BALocReg1B_D0`, every solid edge circled) is a good renaming of the concrete graph `D0`, and the tag `e2` of the packed output is read on `D0` (`extraB` is invariant under a good renaming). -/

/-- `extraB` is invariant under a renaming of the vertices along an injective map (the tag `e2` of an output of a step) -/
private theorem BALocReg2B_extraB_map {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E'] [DecidableEq E']
    [Fintype I'] [DecidableEq I'] (φ : E ⊕ I → E' ⊕ I') (hφ : BALocReg1B_Good φ) (Γ : BAGraph E I) (T : BAGraph E (I ⊕ Fin 2)) :
    (BALocReg1B_mapG φ Γ).extraB (owxEmb 2) (BALocReg1B_mapG (BALocReg1B_extMap 2 φ) T) = Γ.extraB (owxEmb 2) T := by
  have hψ := BALocReg1B_extMap_injective 2 φ hφ.1
  unfold BAGraph.extraB
  change ((Γ.solid.map (SEdge.map φ)).any _) = _
  rw [List.any_map]
  congr 1
  funext e
  simp only [Function.comp_apply, SEdge.map]
  rw [BALocReg1B_sameAtom_map φ hφ.1, ← BALocReg1B_extMap_owxEmb 2 φ e.src, ← BALocReg1B_extMap_owxEmb 2 φ e.dst, BALocReg1B_sameAtom_map _ hψ]

/-- **One weight step with an `e2` output, read on a renamed graph**: if `P.g` is the renaming of `Γ` along a good map, the weight step at the loop `p` of `Γ` has the output `T'` of the derivative term
`lanlwD Γ p q`, renamed, tagged `e2` when `T` is extra for `Γ`. -/
private theorem BALocReg2B_weight_out_e2 (P : BAPGraph (Fin 2)) {E0 I0 : Type} [Fintype E0] [DecidableEq E0] [Fintype I0] [DecidableEq I0]
    (Γ : BAGraph E0 I0) (φ : E0 ⊕ I0 → P.E' ⊕ P.I') (hφ : BALocReg1B_Good φ) (hP : P.g = BALocReg1B_mapG φ Γ)
    (p q : SEdge (E0 ⊕ I0) × List (SEdge (E0 ⊕ I0))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hw : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst)
    (T : BAGraph E0 (I0 ⊕ Fin 2)) (hT : T ∈ (BAGraph.lanlwD Γ p q).splitG) (hx : Γ.extraB (owxEmb 2) T = true) :
    ∃ LT, BAFrameStepT P LT ∧ ∃ Q, (BAShape.e2, Q) ∈ LT := by
  set p' := BALocReg1B_pmap φ p with hp'def
  set q' := BALocReg1B_pmap φ q with hq'def
  have hp' : p' ∈ lwSplit P.g.solid := by
    rw [hP]
    change p' ∈ lwSplit (Γ.solid.map (SEdge.map φ))
    rw [BALocReg1B_lwSplit_map]
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  have hq' : q' ∈ lwSplit p'.2 := by
    change q' ∈ lwSplit (p.2.map (SEdge.map φ))
    rw [BALocReg1B_lwSplit_map]
    exact List.mem_map.2 ⟨q, hq, rfl⟩
  have hw' : p'.1.σ = true ∧ p'.1.circ = true ∧ p'.1.src = p'.1.dst := ⟨hw.1, hw.2.1, congrArg φ hw.2.2⟩
  have hL : BAGraph.lanlwD P.g p' q' = BALocReg1B_mapG (BALocReg1B_extMap 2 φ) (BAGraph.lanlwD Γ p q) := by
    rw [hP]; exact BALocReg1B_lanlwD_map φ Γ p q
  set T' := BALocReg1B_mapG (BALocReg1B_extMap 2 φ) T with hT'def
  have hT' : T' ∈ (BAGraph.lanlwD P.g p' q').splitG := by
    rw [hL, BALocReg1B_splitG_map]
    exact List.mem_map.2 ⟨T, hT, rfl⟩
  have hex : P.g.extraB (owxEmb 2) T' = true := by
    rw [hP, hT'def, BALocReg2B_extraB_map φ hφ]
    exact hx
  refine ⟨_, BAFrameStepT.weight P p' hp' hw', _, List.mem_append_left _ (?_ : (BAShape.e2, P.BASim_outOf T') ∈ P.outsT (P.g.tagStd 2) (P.g.lw2 p'))⟩
  have htag : P.g.tagStd 2 T' = BAShape.e2 := by
    unfold BAGraph.tagStd
    simp only [hex, ↓reduceIte]
  rw [← htag]
  unfold BAPGraph.outsT
  exact List.mem_flatMap.2 ⟨BAGraph.lanlwD P.g p' q', List.mem_cons_of_mem _ (List.mem_map.2 ⟨q', hq', rfl⟩), List.mem_map.2 ⟨T', hT', rfl⟩⟩

/-- **A weight step at a start term of `p = 2` with an `e2` output**: the weight step at the blue circled loop `Ǧ_{β₀β₀}` of `P0 = D0.packMerge` (`BALocReg1B_p1`), at a derivative term `lanlwD D0 p1 q`
with an extra `M`-split `T` (found by `decide +kernel` on the concrete `D0`) -/
private theorem BALocReg2B_start_weight_e2 : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ LT : List (BAShape × BAPGraph (Fin 2)),
    BAFrameStepT P0 LT ∧ ∃ Q, (BAShape.e2, Q) ∈ LT := by
  obtain ⟨q, hq, T, hT, hx, -⟩ : ∃ q ∈ lwSplit BALocReg1B_p1.2, ∃ T ∈ (BAGraph.lanlwD BALocReg1B_D0 BALocReg1B_p1 q).splitG,
      BALocReg1B_D0.extraB (owxEmb 2) T = true ∧ ∀ e ∈ T.dotted, e.eq = false := by decide +kernel
  have hD0d : ∀ e ∈ BALocReg1B_D0.dotted, e.eq = false := by decide
  have hw1 : BALocReg1B_p1.1.σ = true ∧ BALocReg1B_p1.1.circ = true ∧ BALocReg1B_p1.1.src = BALocReg1B_p1.1.dst := by decide
  set P0 := BALocReg1B_D0.packMerge with hP0def
  have hP0 : P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition := List.mem_map.2 ⟨_, List.getElem_mem _, rfl⟩
  obtain ⟨hm0, hg0⟩ := BALocReg1B_merge_map BALocReg1B_D0 hD0d
  obtain ⟨LT, hLT, Q, hQ⟩ := BALocReg2B_weight_out_e2 P0 BALocReg1B_D0 BALocReg1B_D0.toLGraph.vmap hg0 hm0 BALocReg1B_p1 q
    (List.getElem_mem _) hq hw1 T hT hx
  exact ⟨P0, hP0, LT, hLT, Q, hQ⟩



/-- (i) `within` at `P_B` (`hTB`; `PathInv2 1` at its image): targets 1 (c) at an `e2` and at a `macroA` output -/
example : (∃ Q, (BAShape.e2, Q) ∈ (baPG baPB).withinOutsT pB ∧ Q.img.PathInv2 1) ∧
    (∃ Q, (BAShape.macroA, Q) ∈ (baPG baPB).withinOutsT pB ∧ Q.img.PathInv2 1) := by
  obtain ⟨Q, hQ⟩ := tag_exists ((baPG baPB).withinOutsT pB) .e2 (by decide +kernel)
  obtain ⟨Q', hQ'⟩ := tag_exists ((baPG baPB).withinOutsT pB) .macroA (by decide +kernel)
  exact ⟨⟨Q, hQ, baShapePath_e2_tn _ _ ⟨by decide, hTB⟩ Q hQ 1 BALocReg2Inst.pathInv2_B⟩,
    ⟨Q', hQ', baShapePath_macroA_tn _ _ ⟨by decide, hTB⟩ Q' hQ' 1 BALocReg2Inst.pathInv2_B⟩⟩

/-- target 3 (a) at `P_B` (`hTB`, an `e2` and a `macroA` output; the cost bound is the crude one `-4`): the binder `baShapeLLBinder_holds` applied to the step, as `BAShapeO2B:367` applies the three shape theorems -/
example (far : Bool) : (∃ Q, (BAShape.e2, Q) ∈ (baPG baPB).withinOutsT pB ∧ locCostGeA far (-4) Q) ∧
    (∃ Q, (BAShape.macroA, Q) ∈ (baPG baPB).withinOutsT pB ∧ locCostGeA far (-4) Q) := by
  have hk : locCostGeA far (-4) (baPG baPB) := BAScost_locCostGeA_crude far (baPG baPB)
  obtain ⟨Q, hQ⟩ := tag_exists ((baPG baPB).withinOutsT pB) .e2 (by decide +kernel)
  obtain ⟨Q', hQ'⟩ := tag_exists ((baPG baPB).withinOutsT pB) .macroA (by decide +kernel)
  exact ⟨⟨Q, hQ, baShapeLLBinder_holds _ (Or.inl rfl) _ _ ⟨by decide, hTB⟩ Q hQ far (-4) hk⟩,
    ⟨Q', hQ', baShapeLLBinder_holds _ (Or.inr (Or.inl rfl)) _ _ ⟨by decide, hTB⟩ Q' hQ' far (-4) hk⟩⟩

/-- (ii) `ggSplit` at `P_C`, `j = 0` (`hTC`; `PathInv2 2` at its image, `BALocReg1Inst.pathInv2_C`): an `e2` output and a `macroB` output -/
example : (∃ Q, (BAShape.e2, Q) ∈ (baPG baPC).splitOutsT pC qC 0 ∧ Q.img.PathInv2 2) ∧
    (∃ Q, (BAShape.macroB, Q) ∈ (baPG baPC).splitOutsT pC qC 0 ∧ Q.img.PathInv2 2) := by
  obtain ⟨Q, hQ⟩ := tag_exists ((baPG baPC).splitOutsT pC qC 0) .e2 (by decide +kernel)
  obtain ⟨Q', hQ'⟩ := tag_exists ((baPG baPC).splitOutsT pC qC 0) .macroB (by decide +kernel)
  exact ⟨⟨Q, hQ, baShapePath_e2_tn _ _ ⟨by decide, hTC⟩ Q hQ 2 BALocReg1Inst.pathInv2_C⟩,
    ⟨Q', hQ', baShapePath_macroB_tn _ _ ⟨by decide, hTC⟩ Q' hQ' 2 BALocReg1Inst.pathInv2_C⟩⟩

/-- (ii), stages: a `macroB` output of stage 1 (the terms `d2`, `d3`, `d4`) and one of stage 2 (`tr.gg2` at the pair of `BAScost_trB`) of the same step; `baShapePath_macroB_tn` applies at both -/
example : (∃ Q, (BAShape.macroB, Q) ∈ (baPG baPC).outsT (fun _ => BAShape.macroB)
      [BAGraph.ext 2 baPC qC.2 [bpS true (owxEmb 2 qC.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (bpv 1) (owxEmb 2 pC.1.dst)],
       BAGraph.ext 2 baPC qC.2 [bpS true (bpv 1) (owxEmb 2 pC.1.dst)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (owxEmb 2 qC.1.src) (bpv 1)],
       BAGraph.ext 2 baPC qC.2 [] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (owxEmb 2 qC.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 pC.1.dst)]] ∧
      Q.img.PathInv2 2) ∧
    (∃ Q, (BAShape.macroB, Q) ∈ (baPG baPC).outsT (fun _ => BAShape.macroB)
      ((baPC.BAScost_trB pC qC).gg2 (bpS true (bpv 1) (owxEmb 2 pC.1.dst), qC.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 qC.1.src) (bpv 1)])
        (bpS true (owxEmb 2 qC.1.src) (bpv 1), qC.2.map (SEdge.map (owxEmb 2)))) ∧ Q.img.PathInv2 2) := by
  obtain ⟨Q, hQ⟩ := tag_exists ((baPG baPC).outsT (fun _ => BAShape.macroB)
      [BAGraph.ext 2 baPC qC.2 [bpS true (owxEmb 2 qC.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (bpv 1) (owxEmb 2 pC.1.dst)],
       BAGraph.ext 2 baPC qC.2 [bpS true (bpv 1) (owxEmb 2 pC.1.dst)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (owxEmb 2 qC.1.src) (bpv 1)],
       BAGraph.ext 2 baPC qC.2 [] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 pC.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 qC.1.dst), bpM (owxEmb 2 qC.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 pC.1.dst)]])
    .macroB (by decide +kernel)
  obtain ⟨Q', hQ'⟩ := tag_exists ((baPG baPC).outsT (fun _ => BAShape.macroB)
      ((baPC.BAScost_trB pC qC).gg2 (bpS true (bpv 1) (owxEmb 2 pC.1.dst), qC.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 qC.1.src) (bpv 1)])
        (bpS true (owxEmb 2 qC.1.src) (bpv 1), qC.2.map (SEdge.map (owxEmb 2))))) .macroB (by decide +kernel)
  exact ⟨⟨Q, hQ, baShapePath_macroB_tn _ _ ⟨by decide, hTC⟩ Q (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hQ))) 2 BALocReg1Inst.pathInv2_C⟩,
    ⟨Q', hQ', baShapePath_macroB_tn _ _ ⟨by decide, hTC⟩ Q' (List.mem_append_left _ (List.mem_append_right _ hQ')) 2 BALocReg1Inst.pathInv2_C⟩⟩

/-- (iii) `gg` at `P_A` (`hTA`, `ggFT`; `PathInv2 2` at its image, `BALocReg2Inst.pathInv2_A`): an `e2` output, so that the `gg2`/`gg4` lemmas run -/
example : ∃ Q, (BAShape.e2, Q) ∈ ggFT ∧ Q.img.PathInv2 2 := by
  obtain ⟨Q, hQ⟩ := tag_exists ggFT .e2 (by decide +kernel)
  exact ⟨Q, hQ, baShapePath_e2_tn _ _ ⟨by decide, hTA⟩ Q hQ 2 BALocReg2Inst.pathInv2_A⟩

/-- (iv) `edge` at the replacement witness `baPEr` (`hStepEr`, `normalEr`; `PathInv2 1` at its image, `pathInv2_Er`): an `e2` output (the terms `lanlwD`) -/
example : ∃ Q, (BAShape.e2, Q) ∈ BALocReg1Inst.outsEr ∧ Q.img.PathInv2 1 := by
  obtain ⟨Q, hQ⟩ := tag_exists BALocReg1Inst.outsEr .e2 BALocReg1Inst.tags_Er.2.2.1
  exact ⟨Q, hQ, baShapePath_e2_tn _ _ ⟨BALocReg1Inst.normalEr, BALocReg1Inst.hStepEr⟩ Q hQ 1 BALocReg1Inst.pathInv2_Er⟩

namespace BALocReg2BInst

/-- the tagged outputs of the `edge` step at `baPEr` (`BALocReg1Inst.outsEr`), twisted by `(true, true)` -/
def outsErT : List (BAShape × BAPGraph (Fin 2)) := BALocReg1Inst.outsEr.map fun x => (x.1, BAPGraph.twist true true x.2)

theorem stepErT : BALocStepT ((baPG BALocReg1Inst.baPEr).twist true true) outsErT :=
  ⟨(ba_twist_inv_out true true _).2.2.2.2.2 BALocReg1Inst.normalEr, true, true, _, by rw [BALvl1A_twist_invol]; exact BALocReg1Inst.hStepEr, rfl⟩

theorem pathInv2_ErT : ((baPG BALocReg1Inst.baPEr).twist true true).img.PathInv2 1 := (baPathTwist_holds true true _ 1).2 BALocReg1Inst.pathInv2_Er

end BALocReg2BInst

/-- target 2 (the path step with no hypothesis) at the twisted `edge` step at `baPEr`: every output, among them an `e2` output, carries the invariant of the parent (`PathInv2 1`, satisfied) -/
example : (∃ Q, (BAShape.e2, Q) ∈ BALocReg2BInst.outsErT ∧ Q.img.PathInv2 1) ∧ ∀ Q ∈ BALocReg2BInst.outsErT.map Prod.snd, Q.img.PathInv2 1 := by
  have hs := baPathStep_closed _ _ ⟨BALocReg2BInst.outsErT, BALocReg2BInst.stepErT, rfl⟩ 1 BALocReg2BInst.pathInv2_ErT
  obtain ⟨Q, hQ⟩ := tag_exists BALocReg1Inst.outsEr .e2 BALocReg1Inst.tags_Er.2.2.1
  have hQ' : (BAShape.e2, BAPGraph.twist true true Q) ∈ BALocReg2BInst.outsErT := List.mem_map.2 ⟨(BAShape.e2, Q), hQ, rfl⟩
  exact ⟨⟨_, hQ', hs _ (List.mem_map.2 ⟨_, hQ', rfl⟩)⟩, hs⟩

/-- (v) `weight` at a start term of `p = 2` (`PathInv2 2` at its image by `baPathInit_holds`): the weight step at the blue circled loop `Ǧ_{β₀β₀}` has an `e2` output, and `baShapePath_e2_tn` gives the invariant at it -/
example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (LT : List (BAShape × BAPGraph (Fin 2))) (Q : BAPGraph (Fin 2)),
    BAFrameStepTN P0 LT ∧ (BAShape.e2, Q) ∈ LT ∧ P0.img.PathInv2 2 ∧ Q.img.PathInv2 2 := by
  obtain ⟨P0, hP0, LT, hLT, Q, hQ⟩ := BALocReg2B_start_weight_e2
  exact ⟨P0, hP0, LT, Q, ⟨BAGraph.partition_normal _ P0 hP0, hLT⟩, hQ, baPathInit_holds 2 P0 hP0,
    baShapePath_e2_tn _ _ ⟨BAGraph.partition_normal _ P0 hP0, hLT⟩ Q hQ 2 (baPathInit_holds 2 P0 hP0)⟩

/-- (v′) `weight` at the hand-built weight witness `baPL` (`BALocReg2Inst`, a blue circled loop at the internal vertex; `PathInv2 1` at its image, `pathInv2_L`): the step `BAFrameStepT.weight` has an
`e2` output (kernel evaluation of `outsT`, `tagStd`), and `baShapePath_e2_tn` gives the invariant at it -/
example : ∃ Q, (BAShape.e2, Q) ∈ (baPG BALocReg2Inst.baPL).outsT (BALocReg2Inst.baPL.tagStd 2) (BALocReg2Inst.baPL.lw2 BALocReg2Inst.pL) ++
    (baPG BALocReg2Inst.baPL).outsT (BALocReg2Inst.baPL.tagStd 4) (BALocReg2Inst.baPL.lw4 BALocReg2Inst.pL) ∧ Q.img.PathInv2 1 := by
  obtain ⟨Q, hQ⟩ := tag_exists ((baPG BALocReg2Inst.baPL).outsT (BALocReg2Inst.baPL.tagStd 2) (BALocReg2Inst.baPL.lw2 BALocReg2Inst.pL) ++
    (baPG BALocReg2Inst.baPL).outsT (BALocReg2Inst.baPL.tagStd 4) (BALocReg2Inst.baPL.lw4 BALocReg2Inst.pL)) .e2 (by decide +kernel)
  exact ⟨Q, hQ, baShapePath_e2_tn _ _ ⟨by decide, BAFrameStepT.weight (baPG BALocReg2Inst.baPL) BALocReg2Inst.pL (List.mem_cons_self ..) (by decide)⟩ Q hQ 1
    BALocReg2Inst.pathInv2_L⟩

/-- (b) stage 2 at the witnesses: macro (a) at `P_B` (`BALocReg2B_trA`, `BALocReg2B_macroA`) and macro (b) at `P_C` (`BALocReg2B_trB`, `BALocReg2B_macroB`), with the invariant of the parent satisfied
(`PathInv2 1` at `P_B`, `PathInv2 2` at `P_C`) and every hypothesis discharged -/
example : BALocReg1_PathAt (baPB.BAScost_trA pB) 1 0 1 ∧
    (∀ X ∈ (baPB.BAScost_trA pB).lw2 (bpS true (bpv 1) (bpv 1), pB.2.map (SEdge.map (owxEmb 2))), BALocReg1_PathAt X 1 0 1) ∧
    (∀ X ∈ (baPB.BAScost_trA pB).lw4 (bpS true (bpv 1) (bpv 1), pB.2.map (SEdge.map (owxEmb 2))), BALocReg1_PathAt X 1 0 1) := by
  have hA := BALocReg2B_macroA baPB (by decide) pB (List.mem_cons_self ..) ⟨rfl, rfl⟩
  exact ⟨BALocReg2B_trA baPB pB (List.mem_cons_self ..) ⟨rfl, rfl⟩ 1 0 1 BALocReg2Inst.pathInv2_B, fun X hX => hA.1 X hX 1 0 1 BALocReg2Inst.pathInv2_B,
    fun X hX => hA.2 X hX 1 0 1 BALocReg2Inst.pathInv2_B⟩

example : BALocReg1_PathAt (baPC.BAScost_trB pC qC) 2 0 1 ∧
    (∀ X ∈ (baPC.BAScost_trB pC qC).gg2 (bpS true (bpv 1) (owxEmb 2 pC.1.dst), qC.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 qC.1.src) (bpv 1)])
      (bpS true (owxEmb 2 qC.1.src) (bpv 1), qC.2.map (SEdge.map (owxEmb 2))), BALocReg1_PathAt X 2 0 1) ∧
    (∀ X ∈ (baPC.BAScost_trB pC qC).gg4 (bpS true (bpv 1) (owxEmb 2 pC.1.dst), qC.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 qC.1.src) (bpv 1)])
      (bpS true (owxEmb 2 qC.1.src) (bpv 1), qC.2.map (SEdge.map (owxEmb 2))), BALocReg1_PathAt X 2 0 1) := by
  have hB := BALocReg2B_macroB baPC (by decide) pC qC (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide) (by decide) (by decide)
  exact ⟨BALocReg2B_trB baPC pC qC (List.mem_cons_self ..) (List.mem_cons_self ..) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide) (by decide) (by decide) 2 0 1 BALocReg1Inst.pathInv2_C,
    fun X hX => hB.1 X hX 2 0 1 BALocReg1Inst.pathInv2_C, fun X hX => hB.2 X hX 2 0 1 BALocReg1Inst.pathInv2_C⟩

/-- (vi) target 2 at a locally standard graph reached from a `p = 2` start term (`BALocReg1B_reach_locStd`: two weight steps; no start term is locally standard), with no hypothesis -/
example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q ∧ ¬ P0.g.LocStd ∧ Q.g.LocStd ∧
    Q.g.nM = 1 ∧ PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2 := by
  obtain ⟨P0, hP0, Q1, Q, L1, L2, K, -, -, -, -, hn0, -, hreach, hL, hnM, -⟩ := BALocReg1B_reach_locStd
  obtain ⟨-, -, -, h5⟩ := baLocReg15_closed 2 P0 hP0 K Q hreach
  exact ⟨P0, hP0, K, Q, hreach, hn0, hL, hnM, h5 hL⟩

/-- (vi), the step: the path step `baPathStep_closed` and the closed contract at the start term itself (`p = 2`) -/
example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, P0.g.nM ≤ 2 ∧ P0.img.PathInv2 2 ∧ PGraph.LocReg2 P0.img 2 ∧
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → Q.img.PathInv2 2 ∧ Q.g.nM ≤ 2 ∧ PGraph.LocReg2 Q.img 2 := by
  obtain ⟨P0, hP0⟩ := List.exists_mem_of_ne_nil _ (BALocReg1B_partition_ne 2 rfl)
  have h := baLocReg15_closed 2 P0 hP0
  obtain ⟨h1, h2, h3, -⟩ := h 0 P0 (BAReach.refl P0)
  exact ⟨P0, hP0, h2, h1, h3, fun K Q hQ => by obtain ⟨a, b, c, -⟩ := h K Q hQ; exact ⟨a, b, c⟩⟩

/-- target 3 (b) at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10`: the hypothesis `BALocRegConcl` is the conclusion of `ba_localregularX` at `baShapeLLBinder_holds` (the engine, proved), and the lists carry (1)-(5) -/
example : ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
    (∀ Q ∈ outs ++ errs, Q.img.PathInv2 2 ∧ Q.g.nM ≤ 2 ∧ PGraph.LocReg2 Q.img 2) ∧
      ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2 := by
  obtain ⟨outs, errs, hC, -⟩ := ba_localregularX baShapeLLBinder_holds 2 (1 / 4) (by norm_num) 2 3 10
  exact ⟨outs, errs, hC, baLocRegConcl_upto5 2 (1 / 4) 2 3 10 outs errs hC⟩

open MeasureTheory RBM.Gauss in
/-- (vii) target 3 (c) at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10` with the identity of expectations at the flow point of `BAEngineInst` (`d = 3`, `L = 4`, `W = 2`, `flowP_data`, `ℓ0`); no hypothesis -/
example : ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
    (∀ Q ∈ outs, Q.g.LocStd ∧ Q.g.nM ≤ 2 ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2) ∧
    ∫ ω, (BAGraph.ofLGraph (fxyPowGraph 2)).val
        (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
        BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val (outs ++ errs)
        (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
        BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) := by
  obtain ⟨outs, errs, h, -, h1, h2⟩ := ba_localregular_upto5 2 (1 / 4) (by norm_num) 2 3 10
  exact ⟨outs, errs, h, fun Q hQ => ⟨(h.1 Q hQ).1, (h1 Q (List.mem_append_left _ hQ)).2.1, (h2 Q hQ).2.1, (h2 Q hQ).2.2⟩,
    h.2.2.2 4 2 (by norm_num) RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P
      RBM.BA.CouplingWindowInst.flowP_data.2.2 RBM.BA.CouplingWindowInst.flowP_data.1.le RBM.BA.CouplingWindowInst.flowP_data.2.1 BASymm1Inst.ℓ0⟩

end Inst

end RBM.Graph

end
