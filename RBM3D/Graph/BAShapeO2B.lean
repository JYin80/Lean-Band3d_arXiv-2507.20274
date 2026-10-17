/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAShapeO2
import RBM3D.Graph.BAStepS

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

/-!
# BA-L L3b4'' `BAShapeO2`, part 2: the shapes `e2`, `macroA`, `macroB` of `BAFrameStepTN` and (6) along `BAReach` with no hypothesis (T2447)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex` (`deflvl1`, `lanlw`, `lem_lweight`, `GGGamma`).  `baLocReg6_reach` (`Graph/BAStepS:413`) is (6) along `BAReach` under the binder
`∀ sh, sh = e2 ∨ sh = macroA ∨ sh = macroB → BAShapeLL sh BAFrameStepTN`; this file proves the three shapes and the closed form `baLocReg6_holds` (no binder).

## Contents (namespace `RBM.Graph`; private helpers carry the stem `BAShapeO2B_`)

1. The outputs of a tagged step (`outsT`): a group of outputs whose terms satisfy the local lemma, the tags of the groups of `BAFrameStepT`.
2. **Stage 2, route (β)**: the transfer graph `tr` (`BAScost_trA`, `BAScost_trB`) is normal, the pair of the next step is a literal member of `lwSplit tr.solid`, its fresh vertex `β` is an
   atom of its own; `BAScostLL P.g X` is `BAScostLL_macroA` (resp. `_macroB`) composed with the term lemmas of `Graph/BAShapeO2` at `Γ := tr` (`BAShapeO2B_macroA`, `BAShapeO2B_macroB`).
3. **Targets 1-3**: `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn`.
4. **Target 4**: `baLocReg6_holds`.
5. **Instances**: `within` at `P_B`, `ggSplit` at `P_C`, `gg` at `P_A`, `p = 2`.
-/

noncomputable section

namespace RBM.Graph

/-! ## 1. Outputs and tags -/

section Outs

/-- a group of outputs whose terms satisfy the local lemma is a family of packed terms (the generic packed form of `baShapeLL_of_terms`) -/
private theorem BAShapeO2B_group {P : BAPGraph (Fin 2)} {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (sh : BAShape) (hTs : ∀ T ∈ Ts, BAScostLL P.g T) {Q : BAPGraph (Fin 2)} (hQ : (sh, Q) ∈ P.outsT tg Ts) :
    ∃ X : BAScost_Term P, BAScostLL P.g X.X ∧ ∃ Q0 ∈ X.X.partition, Q = BAScost_pack P Q0 := by
  obtain ⟨T, hT, T', hT', -, rfl⟩ := BASim_mem_outsT P tg Ts sh Q hQ
  exact ⟨⟨I', T⟩, hTs T hT, T'.packMerge, List.mem_map.2 ⟨T', hT', rfl⟩, rfl⟩

/-- a group none of whose tags is `sh` has no output tagged `sh` -/
private theorem BAShapeO2B_group_ne {P : BAPGraph (Fin 2)} {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (sh : BAShape) (hne : ∀ T', tg T' ≠ sh) {Q : BAPGraph (Fin 2)} (hQ : (sh, Q) ∈ P.outsT tg Ts) : False := by
  obtain ⟨T, -, T', -, h, -⟩ := BASim_mem_outsT P tg Ts sh Q hQ
  exact hne T' h

private theorem BAShapeO2B_tagStd_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (k : ℕ) (sh : BAShape)
    (h1 : sh ≠ BAShape.e2) (h2 : sh ≠ BAShape.band) (T' : BAGraph E (I ⊕ Fin k)) : Γ.tagStd k T' ≠ sh := by
  unfold BAGraph.tagStd
  split_ifs
  · exact fun h => h1 h.symm
  · exact fun h => h2 h.symm

private theorem BAShapeO2B_tagT1_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (sh : BAShape)
    (h1 : sh ≠ BAShape.e1) (h2 : sh ≠ BAShape.band) (T' : BAGraph E (I ⊕ Fin 2)) : Γ.tagT1 T' ≠ sh := by
  unfold BAGraph.tagT1
  split_ifs
  · exact fun h => h1 h.symm
  · exact fun h => h2 h.symm

end Outs

/-! ## 2. Stage 2 -/

section Stage2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the last edge of a list is a member of its `lwSplit` -/
theorem BAShapeO2B_lwSplit_last {κ : Type} (R : List κ) (e : κ) : (e, R) ∈ lwSplit (R ++ [e]) := by
  induction R with
  | nil => simp [lwSplit]
  | cons a R ih =>
    rw [List.cons_append, lwSplit]
    exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨(e, R), ih, rfl⟩)

/-- an extension by new circled edges of a normal graph, keeping a part of its solid edges, is normal -/
theorem BAShapeO2B_ext_normal {k : ℕ} (Γ : BAGraph E I) (hN : Γ.Normal) (rest : List (SEdge (E ⊕ I))) (hrest : ∀ e ∈ rest, e ∈ Γ.solid)
    (S : List (SEdge (E ⊕ (I ⊕ Fin k)))) (hS : ∀ e ∈ S, e.circ = true) (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    (BAGraph.ext k Γ rest S W md).Normal := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [BAGraph.ext, LGraph.owxExt, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact hN.1 e0 he0
  · intro e he
    simp only [BAGraph.ext, LGraph.owxExt, List.mem_append, List.mem_map] at he
    rcases he with ⟨e0, he0, rfl⟩ | he
    · exact hN.2 e0 (hrest e0 he0)
    · exact hS e he

/-- no `M`-dotted edge of the extension touches the fresh vertex `bpv j`: its atom is a singleton -/
theorem BAShapeO2B_atomAdj_fresh {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (S : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (j : Fin k)
    (hmd : ∀ m ∈ md, m.x ≠ bpv j ∧ m.y ≠ bpv j) (u v : E ⊕ (I ⊕ Fin k)) (h : u = bpv j ∨ v = bpv j) :
    (BAGraph.ext k Γ rest S W md).atomAdj u v = false := by
  have hemb : ∀ a : E ⊕ I, owxEmb k a ≠ bpv j := by
    intro a; rcases a with a | a <;> simp [owxEmb, bpv]
  rw [Bool.eq_false_iff]
  intro hc
  simp only [BAGraph.atomAdj, BAGraph.ext, LGraph.owxExt, Bool.or_eq_true, List.any_eq_true, List.mem_map, List.mem_append,
    decide_eq_true_eq, Bool.and_eq_true] at hc
  rcases hc with ((⟨_, ⟨a, ha, rfl⟩, h1, h2⟩ | ⟨_, ⟨a, ha, rfl⟩, h2⟩) | ⟨e, h1 | ⟨a, ha, rfl⟩, h2⟩)
  · simp only [DEdge.map] at h2
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases h with h | h <;> subst h <;> exact hemb _ (by assumption)
  · simp only [BAPsiEdge.map] at h2
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases h with h | h <;> subst h <;> exact hemb _ (by assumption)
  · obtain ⟨hx, hy⟩ := hmd e h1
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases h with h | h <;> subst h <;> simp_all
  · simp only [BAMEdge.map] at h2
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases h with h | h <;> subst h <;> exact hemb _ (by assumption)

/-- the atom of a fresh vertex with no `M`-dotted edge is itself -/
theorem BAShapeO2B_sameAtom_fresh {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (S : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (j : Fin k)
    (hmd : ∀ m ∈ md, m.x ≠ bpv j ∧ m.y ≠ bpv j) (w : E ⊕ (I ⊕ Fin k)) :
    (BAGraph.ext k Γ rest S W md).sameAtom (bpv j) w = true ↔ w = bpv j := by
  rw [BAGraph.BAAtomic_sameAtom_iff, BAGraph.mem_atom_iff]
  constructor
  · intro h
    rcases h.cases_head with h | ⟨c, hc, -⟩
    · exact h.symm
    · have := BAShapeO2B_atomAdj_fresh Γ rest S W md j hmd (bpv j) c (Or.inl rfl)
      simp [this] at hc
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-- the fresh vertex lies in no atom with another vertex, and its atom is internal -/
theorem BAShapeO2B_fresh_wf {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (S : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (j : Fin k)
    (hmd : ∀ m ∈ md, m.x ≠ bpv j ∧ m.y ≠ bpv j) {w : E ⊕ (I ⊕ Fin k)} (hw : w ≠ bpv j) :
    (BAGraph.ext k Γ rest S W md).sameAtom (bpv j) w = false ∧ (BAGraph.ext k Γ rest S W md).sameAtom w (bpv j) = false ∧
      (BAGraph.ext k Γ rest S W md).intAtom (bpv j) = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Bool.eq_false_iff]
    exact fun h => hw ((BAShapeO2B_sameAtom_fresh Γ rest S W md j hmd w).1 h)
  · rw [BAGraph.BAAtomic_sameAtom_comm, Bool.eq_false_iff]
    exact fun h => hw ((BAShapeO2B_sameAtom_fresh Γ rest S W md j hmd w).1 h)
  · rw [BAGraph.BAAtomic_intAtom_iff]
    intro w' hw'
    have := (BAShapeO2B_sameAtom_fresh Γ rest S W md j hmd w').1 ((BAGraph.BAAtomic_sameAtom_iff _ _ _).2 hw')
    subst this
    rfl

/-- **Stage 2 of macro step (a), route (β)** (`BASim:120-123`): every term of `lw2`, `lw4` at the loop `Ǧ_{ββ}` of the transfer graph `tr` satisfies the local lemma at `P.g`:
`BAScostLL_macroA` composed with the weight lemmas of `Graph/BAShapeO2` at `Γ := tr`. -/
theorem BAShapeO2B_macroA (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) :
    (∀ X ∈ (Γ.BAScost_trA p).lw2 (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))), BAScostLL Γ X) ∧
      (∀ X ∈ (Γ.BAScost_trA p).lw4 (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))), BAScostLL Γ X) := by
  have hrest : ∀ e ∈ p.2, e ∈ Γ.solid := fun e he => (lwSplit_perm Γ.solid p hp).symm.subset (List.mem_cons_of_mem _ he)
  have hNtr : (Γ.BAScost_trA p).Normal :=
    BAShapeO2B_ext_normal Γ hN p.2 hrest _ (by intro e he; simp at he; subst he; rfl) _ _
  have hpp : (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))) ∈ lwSplit (Γ.BAScost_trA p).solid :=
    BAShapeO2B_lwSplit_last (p.2.map (SEdge.map (owxEmb 2))) (bpS true (bpv 1) (bpv 1))
  have hpp1 : (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).σ = true ∧ (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).circ = true ∧
      (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).src = (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (bpv 1)).dst := ⟨rfl, rfl, rfl⟩
  have hLL := BAScostLL_macroA Γ p hp hp1
  exact ⟨fun X hX => hLL.trans (BAShapeO2_lw2 _ hNtr _ hpp hpp1 X hX), fun X hX => hLL.trans (BAShapeO2_lw4 _ hNtr _ hpp hpp1 X hX)⟩

/-- **Stage 2 of macro step (b), route (β)** (`BASim:130-136`): the same for `gg2`, `gg4` at the pair `Ǧ_{βy}`, `Ǧ_{y'β}` of the transfer graph `tr`; `β` is an atom of its own. -/
theorem BAShapeO2B_macroB (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    (∀ X ∈ (Γ.BAScost_trB p q).gg2 (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
      (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2))), BAScostLL Γ X) ∧
    (∀ X ∈ (Γ.BAScost_trB p q).gg4 (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
      (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2))), BAScostLL Γ X) := by
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
  have hLL := BAScostLL_macroB Γ p q hp hq hp1 hq1 hsame hwf1 hwf2
  have hp1' : (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (owxEmb 2 p.1.dst)).σ = true ∧ (bpS true (bpv 1 : E ⊕ (I ⊕ Fin 2)) (owxEmb 2 p.1.dst)).circ = true := ⟨rfl, rfl⟩
  have hq1' : (bpS true (owxEmb 2 q.1.src : E ⊕ (I ⊕ Fin 2)) (bpv 1)).σ = true ∧ (bpS true (owxEmb 2 q.1.src : E ⊕ (I ⊕ Fin 2)) (bpv 1)).circ = true := ⟨rfl, rfl⟩
  exact ⟨fun X hX => hLL.trans (BAShapeO2_gg2 _ hNtr _ _ hpp hqq hp1' hq1' rfl hwfβ1.1 hwfβ2.2.1 hwfβ1.2.2 X hX),
    fun X hX => hLL.trans (BAShapeO2_gg4 _ hNtr _ _ hpp hqq hp1' hq1' rfl hwfβ1.1 hwfβ2.2.1 hwfβ1.2.2 X hX)⟩

end Stage2

/-! ## 3. Targets 1-3: the shapes `e2`, `macroA`, `macroB` of `BAFrameStepTN` -/

section Shapes

/-- the data of the `gg` and `ggSplit` constructors: the two edges are in the solid list -/
private theorem BAShapeO2B_mem_pq {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : p.1 ∈ Γ.solid ∧ q.1 ∈ Γ.solid := by
  have h := BAShapeO2_perm_pq Γ p q hp hq
  exact ⟨h.symm.subset (by simp), h.symm.subset (by simp)⟩

/-- **Target 1: `BAShapeLL e2 BAFrameStepTN`.**  An `e2` output of a step is a packed term of `G = Ǧ + M` on a stage-1 builder term `X` of the step with `BAScostLL P.g X`
(the term lemmas of `Graph/BAShapeO2`; the `tagT1` groups and the constant-tag groups are never tagged `e2`); `baShapeLL_e2` (`BAScost2:96`). -/
theorem baShapeLL_e2_tn : BAShapeLL BAShape.e2 BAFrameStepTN := by
  refine baShapeLL_e2 ?_
  rintro P LT ⟨hN, hF⟩ Q hQ
  cases hF with
  | weight p hp h =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BAShapeO2B_group _ _ _ (BAShapeO2_lw2 P.g hN p hp h) hQ
    · exact BAShapeO2B_group _ _ _ (BAShapeO2_lw4 P.g hN p hp h) hQ
  | within p hp h =>
    simp only [BAPGraph.withinOutsT, List.mem_append] at hQ
    rcases hQ with (hQ | hQ) | hQ
    · exact BAShapeO2B_group _ _ _ (BAShapeO2_within P.g hN p hp ⟨h.1, h.2.1⟩ h.2.2.2) hQ
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · refine BAShapeO2B_group _ _ _ (fun X hX => ?_) hQ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
      exact BAShapeO2_lanlwD P.g hN p hp h q hq
  | gg p hp q hq h x hx hwf hint hnb =>
    obtain ⟨hpm, hqm⟩ := BAShapeO2B_mem_pq P.g p q hp hq
    have hxy : q.1.dst = p.1.src := by rw [hx.1, hx.2]
    have hint' : P.g.intAtom p.1.src = true := by rw [hx.1]; exact hint
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BAShapeO2B_group _ _ _ (BAShapeO2_gg2 P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hxy (hwf _ hpm) (hwf _ hqm) hint') hQ
    · exact BAShapeO2B_group _ _ _ (BAShapeO2_gg4 P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hxy (hwf _ hpm) (hwf _ hqm) hint') hQ
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    have hq : q ∈ lwSplit p.2 := List.mem_of_getElem? hj
    obtain ⟨hpm, hqm⟩ := BAShapeO2B_mem_pq P.g p q hp hq
    have hsame' : P.g.sameAtom p.1.src q.1.dst = true := by rw [hx.1, hx.2]; exact hsame
    have hint' : P.g.intAtom p.1.src = true := by rw [hx.1]; exact hint
    simp only [BAPGraph.splitOutsT, List.mem_append] at hQ
    rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · refine BAShapeO2B_group _ _ _ (fun X hX => ?_) hQ
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hX
      exact BAShapeO2_lanlwD P.g hN p hp ⟨h.1, h.2.1⟩ q' (List.mem_of_mem_eraseIdx hq')
    · refine BAShapeO2B_group _ _ _ (fun X hX => ?_) hQ
      rw [List.mem_singleton] at hX
      subst hX
      exact BAShapeO2_ggSplitD1 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm) hint'
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim

/-- **Target 2: `BAShapeLL macroA BAFrameStepTN`.**  Only `within` tags `macroA`, all of it at stage 2: the outputs of `lw2`, `lw4` at the loop `Ǧ_{ββ}` of the transfer graph, route (β)
(`BAShapeO2B_macroA`: `BAScostLL_macroA` composed with the weight lemmas at `Γ := tr`), packed by `baShapeLL_of_terms`. -/
theorem baShapeLL_macroA_tn : BAShapeLL BAShape.macroA BAFrameStepTN := by
  refine baShapeLL_of_terms ?_
  rintro P LT ⟨hN, hF⟩ Q hQ
  cases hF with
  | weight p hp h =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | within p hp h =>
    simp only [BAPGraph.withinOutsT, List.mem_append] at hQ
    rcases hQ with (hQ | hQ) | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact BAShapeO2B_group _ _ _ (BAShapeO2B_macroA P.g hN p hp ⟨h.1, h.2.1⟩).1 hQ
    · exact BAShapeO2B_group _ _ _ (BAShapeO2B_macroA P.g hN p hp ⟨h.1, h.2.1⟩).2 hQ
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | gg p hp q hq h x hx hwf hint hnb =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    simp only [BAPGraph.splitOutsT, List.mem_append] at hQ
    rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim

/-- **Target 3: `BAShapeLL macroB BAFrameStepTN`.**  Only `ggSplit` tags `macroB`: stage 1 is `d2`-`d4` (`BAShapeO2_ggSplitD2`-`D4`), stage 2 is `gg2`, `gg4` at the pair of the transfer graph
(route (β), `BAShapeO2B_macroB`); both are the second disjunct of `baShapeLL_macroB` (`BAScost2:114`). -/
theorem baShapeLL_macroB_tn : BAShapeLL BAShape.macroB BAFrameStepTN := by
  refine baShapeLL_macroB ?_
  rintro P LT ⟨hN, hF⟩ Q hQ
  refine Or.inr ?_
  cases hF with
  | weight p hp h =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | within p hp h =>
    simp only [BAPGraph.withinOutsT, List.mem_append] at hQ
    rcases hQ with (hQ | hQ) | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (fun _ => by decide) hQ).elim
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | gg p hp q hq h x hx hwf hint hnb =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    have hq : q ∈ lwSplit p.2 := List.mem_of_getElem? hj
    obtain ⟨hpm, hqm⟩ := BAShapeO2B_mem_pq P.g p q hp hq
    have hsame' : P.g.sameAtom p.1.src q.1.dst = true := by rw [hx.1, hx.2]; exact hsame
    simp only [BAPGraph.splitOutsT, List.mem_append] at hQ
    rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagT1_ne P.g _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · exact (BAShapeO2B_group_ne _ _ _ (BAShapeO2B_tagStd_ne P.g _ _ (by decide) (by decide)) hQ).elim
    · refine BAShapeO2B_group _ _ _ (fun X hX => ?_) hQ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl
      · exact BAShapeO2_ggSplitD2 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)
      · exact BAShapeO2_ggSplitD3 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)
      · exact BAShapeO2_ggSplitD4 P.g p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)
    · exact BAShapeO2B_group _ _ _ (BAShapeO2B_macroB P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)).1 hQ
    · exact BAShapeO2B_group _ _ _ (BAShapeO2B_macroB P.g hN p q hp hq ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩ hsame' (hwf _ hpm) (hwf _ hqm)).2 hQ

end Shapes

/-! ## 4. Target 4: (6) along `BAReach` with no hypothesis -/

/-! ## 5. Nonempty instances (target 7) -/

end RBM.Graph

end
