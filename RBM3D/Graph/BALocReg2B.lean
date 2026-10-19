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
# The path invariant at the shapes `e2`, `macroA`, `macroB`, the closed contract (1)-(5), the composed statement (part 2)

Paper: Subappendix B.2 (the band proof of (1)-(5), (B.11) `eq:originGamma`); Lemma B.6
(`lanlw`); Lemma B.7 (`lem_lweight`); (B.20) `GGGamma`; Subappendix B.3 (the block Anderson model
keeps the path properties).  Part 1 is `Graph/BALocReg2.lean` (the 18 term lemmas and the five
list forms).

## Contents (namespace `RBM.Graph`; private helpers carry the stem `BALocReg2B_`)

1. **Outputs and tags**: the path form of the group lemma of `BAShapeO2B` (a group of outputs whose
   terms carry the invariant carries it to the packed outputs), and the tag lemmas (copies of the
   private helpers of `BAShapeO2B`, under the stem).
2. **Stage 2**: the intermediates `Γ.BAScost_trA p` (macro (a): the edge inside an atom becomes the
   blue loop `Ǧ_{ββ}`) and `Γ.BAScost_trB p q` (macro (b): `(y', a')`, `(a, y)` become
   `(y', β)`, `(β, y)`), each one replacement of the selected edges (`BALocReg2_pathAt_ext2`,
   `localReg2_VRepl.same`); then the terms of `tr.lw2`, `tr.lw4` (resp. `tr.gg2`, `tr.gg4`) at the
   transfer graph (`BALocReg2B_macroA`, `BALocReg2B_macroB`: the path counterparts of
   `BAShapeO2B_macroA`, `_macroB`).
3. `baShapePath_e2_tn`, `baShapePath_macroA_tn`, `baShapePath_macroB_tn` and `baPathBinder_holds`
   (the hypothesis `hX` of `baPathStep_holds`, `baLocReg15_holds`).
4. `baLocReg15_closed` (the contract (1)-(5) with no hypothesis).
5. `baLocRegConcl_upto5` (any lists with `BALocRegConcl` carry (1)-(5)).

Combinatorial.  No `inductive`, no new `Prop` def.
-/

noncomputable section

namespace RBM.Graph

local macro "BALocReg2B_simp0" : tactic => `(tactic| simp only [SEdge.localReg2_cends_mk, SEdge.localReg2_cends_map, SEdge.localReg2_cends, Prod.map_apply, Sym2.map_mk,
  localReg2_mapMS, List.map_cons, List.map_nil, Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe,
  Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq, BALocReg2_bpS_σ, BALocReg2_bpS_src, BALocReg2_bpS_dst, SEdge.map])

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

/-- a group none of whose tags is `sh` has no output tagged `sh` (as the private `BAShapeO2B_group_ne`) -/
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

/-- the data of the `gg` and `ggSplit` constructors: the two edges are in the solid list (as the private `BAShapeO2B_mem_pq`) -/
private theorem BALocReg2B_mem_pq {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : p.1 ∈ Γ.solid ∧ q.1 ∈ Γ.solid := by
  have h := BAShapeO2_perm_pq Γ p q hp hq
  exact ⟨h.symm.subset (by simp), h.symm.subset (by simp)⟩

end Outs

/-! ## 2. Stage 2 -/

section Stage2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The macro (a) intermediate** (`BAScostLL_macroA` in `Graph/BAScost.lean`): the edge `p.1 = Ǧ_{xy}` inside an atom (`[x] = [y]` after the two `M`-dots) is replaced by the loop `Ǧ_{ββ}` in the molecule of `x`;
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

/-- **The macro (b) intermediate** (`BAScostLL_macroB` in `Graph/BAScost.lean`): the pair `(a, y)` (`p.1`), `(y', a')` (`q.1`) with `[a] = [a']` becomes `(β, y)`, `(y', β)`, `β` in the molecule of `a`; the molecular
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

/-- **Stage 2 of macro step (a)** (`BAShapeO2B_macroA`): every term of `lw2`, `lw4` at the loop `Ǧ_{ββ}` of the transfer graph `tr` carries the invariant of `Γ`:
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

/-- **Stage 2 of macro step (b)** (`BAShapeO2B_macroB`): the same for `gg2`, `gg4` at the pair `Ǧ_{βy}`, `Ǧ_{y'β}` of the transfer graph `tr`; `β` is an atom of its own. -/
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

/-! ## 3. The shapes `e2`, `macroA`, `macroB` of `BAFrameStepTN` -/

section Shapes

/-- **`BAShapePath e2 BAFrameStepTN`.**  An `e2` output of a step is a packed term of the partition of a stage-1 builder term `X` of the step (the `tagT1` groups and the
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

/-- **`BAShapePath macroA BAFrameStepTN`.**  Only `within` tags `macroA`, all of it at stage 2: the outputs of `lw2`, `lw4` at the loop `Ǧ_{ββ}` of the transfer graph
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

/-- **`BAShapePath macroB BAFrameStepTN`.**  Only `ggSplit` tags `macroB`: stage 1 is `d₂`-`d₄` (`BALocReg2_ggSplitD2` to `BALocReg2_ggSplitD4`), stage 2 is `gg2`, `gg4` at the pair of the
transfer graph (`BALocReg2B_macroB`). -/
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

/-- **The path binder** (the hypothesis `hX` of `baPathStep_holds` (`Graph/BALocReg1.lean`) and of `baLocReg15_holds` (`Graph/BALocReg1B.lean`), verbatim). -/
theorem baPathBinder_holds : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN := by
  rintro sh (rfl | rfl | rfl)
  · exact baShapePath_e2_tn
  · exact baShapePath_macroA_tn
  · exact baShapePath_macroB_tn

end Shapes

/-! ## 4. The counterpart of `LocalRegular2`, closed -/

/-- **The contract (1)-(5) of `Graph/BALocReg1B.lean` with no hypothesis**: `baLocReg15_holds` at `baPathBinder_holds`. -/
theorem baLocReg15_closed : BALocReg15 := baLocReg15_holds baPathBinder_holds

/-! ## 5. The composed statement -/

/-- **Any lists with `BALocRegConcl` carry (1)-(5)** : at every `Q ∈ outs ++ errs`, `PathInv2 p`, `n_M ≤ p`,
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

end RBM.Graph

end
