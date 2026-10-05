/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular6c

/-!
# LW-10c4: `lem:localregular`, property (6), part 4 (T2216)

The twists, the ten new term decompositions, the step lemma along `LocStep`, `CircIffLoop` along
`LocStep`, and the assembly `lw_localregular`: after this file every property (1)-(6) of
`lem:localregular` is a theorem.

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:786-821` (cited `7_8:line`;
`lem:localregular`, property (6) = `(eq:sizeGammamu)`, `7_8:815-818`) and
`paper/tex/B_graphical_lemmas.tex` (cited `B:line`): `strat_local` `B:135-157`, the proof of (6)
`B:200-278` (the edge and `GG` cases are omitted there, `B:272-275`), the remark `B:280-283`.
Design: DECISIONS §47, §55 (LW-10c is split into c1-c4: `LocalRegular6a` is c1, `6b` c2, `6c` c3,
this file c4); the mathematics is the Fable report
`docs/claude-team/fable/2026-10-05-localreg6-locallemma.md` (cited F).

## What is proved

* **Target 1** `LGraph.scost_twist` (F §2): `scost (lwSymmTwistG c t Γ) s = scost Γ s` for every
  setoid.  The twist maps the solid list by `lwSymmTwistS` (`lwSymmTwistG_solid`), keeps the waved
  list's length, and `skept` commutes with it (the circle is kept, the ends swap and `s` is
  symmetric); `sIntCls` does not depend on the graph; the half-edge pattern of a class is permuted
  (conjugation `(bi, bo, ri, ro) ↦ (ri, ro, bi, bo)`, transposition `↦ (bo, bi, ro, ri)`) and
  `lwElem` is invariant under both (`localReg6d_halfPat_twist`), so `sElemCls` is unchanged.
* **Target 2**, the transfers of the local lemma (`localReg6d_ll_twist`, `localReg6d_ll_perm`,
  `localReg6d_ll_frame`, `localReg6d_ll_frame2`): `ScostLL (twist Γ) T → ScostLL Γ (twist T)`;
  the source up to `List.Perm` of its solid list and equal waved length; the frame of Step 2 and
  of Step 3 (`lwSymmFrame`, `lwSymmFrame2`: the selected edges uncircled, then twisted; an
  uncircled selected edge is a permutation of the solid list, `lwSplit_perm`).
* **Target 3**, the ten new term lemmas `localReg6d_ll_T1`, `_T2`, `_T4`, `_P5`, `_P6`, `_R4`,
  `_R5`, `_R6`, `_R7`, `_R8` (F §3): each term is a composite of the primitives of c2/c3 (`T1` =
  `Loop`; `T2` = `MoveLoop` then `Loop`; `T4` = `MoveLoop` then `Dmove` at the fresh light-weight;
  `P5` = `MoveOut` then `AddLoop` (red); `P6`, `R5` = `MoveSC` then `AddLoop` (blue); `R4` =
  `MoveSC` then `Loop`; `R6` = `Loop` then `MoveSC`; `R7` = `Dmove`; `R8` = `MoveSC` then `Dmove`),
  composed by `LGraph.ScostLL.trans`; the two-fresh-vertex terms (`T2`, `T4`, `R4`, `R6`, `R8`) are
  relabelled by `φ = localReg6d_phi` (`I ⊕ Fin 1 ⊕ Fin 1 → I ⊕ Fin 2`, onto, fixing the external
  vertices, `φ ∘ owxEmb 1 ∘ owxEmb 1 = owxEmb 2`, the first fresh vertex goes to `inr (inr 0)`, the
  second to `inr (inr 1)`), and the solid list of the composite is a permutation of the term's
  (the waved edges of composite and term may differ in colour or end, e.g. `x - β` for `α - β` in
  `R6`; only their number enters `scost`).  The seven other terms are the merged theorems
  `localReg6c_inst_ET3` (`T3`), `localReg6b_inst_T1` (`Oe1xOwx`, `R3`), `localReg6c_inst_D`, `_P3`,
  `_P4`, `localReg6b_inst_R2`, used as they are.
* **Target 4**, the step: `localReg6d_locCostGe_term` (a term `T` with `ScostLL P.g T` carries
  `LocCostGe far k` to every packed output of `T.partition m`: `LGraph.scost_partition_ge` gives
  the vertex map, `ScostLL` at its pullback of `s` gives a merge of `P.g` that keeps `P.ext 0`,
  `P.ext 1` apart whenever `s` keeps their images apart), `localReg6d_circIffLoop_term` (circled
  edges of `T` are loops ⇒ `CircIffLoop` of every partition term, by induction on `lvl1Split`),
  `localReg6d_locStep_elim` (the case split of `pathInv2_locStep`: three constructors, the 17
  terms: every output of a `LocStep` comes from a term `T` of the input whose circled edges are
  loops and with `ScostLL P.g T`; the facts that the constructors supply are listed in the
  private lemmas `localReg6d_good_*`), and the three pins `circIffLoop_locStep`,
  `locCostGe_locStep`, `locReg6Inv_locStep`.  The hypothesis `P.g.Normal` of the first two is not
  used (it is a hypothesis of the pins); `locReg6Inv_locStep` uses `Normal` through
  `lvl1_step_good`.  `hbad`, `hnb`, the cutoff and `¬ LocStd` are not used.
* **Target 5** `lw_localregular`: the five conjuncts of the merged `lw_localregular_upto5`, the
  last one extended by (6) `2p ≤ ord` for every output and the far corollary `3p ≤ ord` when
  `Q.ext 0 ≠ Q.ext 1`; the invariant `PGraph.LocReg6Inv p` holds along `Lvl1Reach` from the starting
  graph (`lvl1_induction`, `fxyPowGraph_locReg6Inv`, `locReg6Inv_locStep`), and at a locally
  standard graph the trivial merge costs `ord` (`locReg6_of_locCostGe`,
  `locReg6far_of_locCostGe`).  No assumption `(eq:far_ab)` (`7_8:792`).
* **Compiled instances** `localReg6d_inst_*` (section 11): the twist `(true, true)` at `Γ_2`,
  `T2` at `p2Graph`, `locReg6Inv_locStep` at the merged Step 1 of `Γ_2`, the step lemma and
  `CircIffLoop` at the merged `LocStep` instances of Step 1 at an external vertex, Step 2 and
  Step 3 (every hypothesis but `LocCostGe` discharged, and at a concrete `k`),
  `lw_localregular` at `p = 2` with the data of the merged `localReg2_inst_expansion`, and the
  other nine new term lemmas and the four transfers at concrete graphs (`Γ_2`, `localReg6d_instG`),
  and the step lemma at a Step 2 and a Step 3 whose `LocStep` has every derivative term
  (`localReg6d_instEdgeG`: `P5`, `P3`, `P6`, `P4`, `D`; `localReg6d_instGGG`: `R7`, `R8`).

## Contents (namespace `RBM.Graph`; public: the targets, the shapes of check-file section 3,
the instances)

1. The twist and target 1.  2. The transfers.  3. The ten terms.  4. Circled edges are loops.
5. The weight terms of Step 1.  6. The edge terms of Step 2.  7. The `GG` terms of Step 3.
8. The step lemma and the case split.  9. The three pins.  10. The assembly.  11. Compiled
instances.

## Differences from the paper (delta candidates, numbered by the dispatcher)

* `T2216a`: `lem:localregular` (6) is proved for **every** output as `ord ≥ 2p` (`7_8:815-818`), and
  `ord ≥ 3p` when the two external vertices of the output differ, **without** the assumption
  `(eq:far_ab)` (`7_8:792`); the paper's route `ord ≥ 3p - n_dv/2 > 2p` (`B:268-277`) is replaced
  by the minimum over merges `Φ` of the local cost, monotone along `strat_local` (`T2151a`: the
  far assumption is not needed for (6); `T2151c`: the step claim of `B:275-277` is not used).
* `T2216b` (on `T2184c`, the edge and `GG` cases omitted at `B:272-275`): proved, through the
  composition, the twists and the step lemma; the per-case bookkeeping of `B:232-249` (`T2151b`) is
  not used.
* `T2216c`: the remark `B:280-283` (`ord ≥ 3p`) holds for the outputs whose two external vertices
  differ (`Q.ext 0 ≠ Q.ext 1`); the bound `2p` is attained when they are merged (the prove report
  (a): `p = 2`, minimum of `ord` over the locally standard states reached, `4`), so the strict
  inequality `> 2p` of `B:277` fails there.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.show false

noncomputable section

namespace RBM.Graph

/-! ## 1. The twist and target 1 -/

private theorem localReg6d_elem_perm (a b c d : ℕ) :
    lwElem (b, a, d, c) = lwElem (a, b, c, d) ∧ lwElem (c, d, a, b) = lwElem (a, b, c, d) ∧
      lwElem (d, c, b, a) = lwElem (a, b, c, d) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [lwElem, decide_eq_decide, Prod.mk.injEq] <;> omega

/-- **The pattern under a twist** (F §2): the twist of a solid list permutes the components of the half-edge pattern at every vertex set
(conjugation `(bi, bo, ri, ro) ↦ (ri, ro, bi, bo)`, transposition `↦ (bo, bi, ro, ri)`), and `lwElem` is invariant under both. -/
theorem localReg6d_halfPat_twist {V : Type*} (c t : Bool) (es : List (SEdge V)) (K : V → Prop) [DecidablePred K] :
    lwElem (lwHalfPat (es.map (lwSymmTwistS c t)) K) = lwElem (lwHalfPat es K) := by
  have e : ∀ (f : SEdge V → SEdge V), lwHalfPat (es.map f) K =
      (es.countP (fun e => (f e).σ && decide (K (f e).dst)), es.countP (fun e => (f e).σ && decide (K (f e).src)),
        es.countP (fun e => !(f e).σ && decide (K (f e).dst)), es.countP (fun e => !(f e).σ && decide (K (f e).src))) := by
    intro f
    simp only [lwHalfPat, List.countP_map, Function.comp_def]
  rw [e]
  have h := localReg6d_elem_perm (es.countP (fun e => e.σ && decide (K e.dst))) (es.countP (fun e => e.σ && decide (K e.src)))
    (es.countP (fun e => !e.σ && decide (K e.dst))) (es.countP (fun e => !e.σ && decide (K e.src)))
  unfold lwHalfPat
  cases c <;> cases t <;>
    simp only [lwSymmTwistS, SEdge.conj, SEdge.transpose, Bool.cond_true, Bool.cond_false, Bool.not_not]
  · rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

section Twist

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem localReg6d_twistG_waved (c t : Bool) (Γ : LGraph E I) :
    (lwSymmTwistG c t Γ).waved.length = Γ.waved.length := by
  cases c <;> cases t <;> simp [lwSymmTwistG, LGraph.conj, LGraph.transpose]

open Classical in
private theorem localReg6d_twistG_skept (c t : Bool) (Γ : LGraph E I) (s : Setoid (E ⊕ I)) :
    (lwSymmTwistG c t Γ).skept s = (Γ.skept s).map (lwSymmTwistS c t) := by
  unfold LGraph.skept
  rw [lwSymmTwistG_solid, List.filter_map]
  congr 1
  refine List.filter_congr fun e _ => ?_
  simp only [Function.comp, lwSymmTwistS_circ]
  have : decide (s (lwSymmTwistS c t e).src (lwSymmTwistS c t e).dst) = decide (s e.src e.dst) := by
    rw [lwSymmTwistS_eq]
    cases t
    · rfl
    · exact decide_eq_decide.2 ⟨fun h => s.symm h, fun h => s.symm h⟩
  rw [this]

open Classical in
private theorem localReg6d_twistG_sElemCls (c t : Bool) (Γ : LGraph E I) (s : Setoid (E ⊕ I)) :
    (lwSymmTwistG c t Γ).sElemCls s = Γ.sElemCls s := by
  unfold LGraph.sElemCls
  simp only [localReg6d_twistG_skept, localReg6d_halfPat_twist]

/-- **Target 1** (the pin `ScostTwistPin`, F §2): the twists `(c, t)` leave the cost of every merge unchanged.  The kept edges of the
twist are the twists of the kept edges, the internal classes do not depend on the graph, the number of waved edges is unchanged, and the
elementary classes are unchanged by `localReg6d_halfPat_twist`. -/
theorem LGraph.scost_twist (c t : Bool) (Γ : LGraph E I) (s : Setoid (E ⊕ I)) :
    LGraph.scost (lwSymmTwistG c t Γ) s = LGraph.scost Γ s := by
  unfold LGraph.scost
  rw [localReg6d_twistG_skept, List.length_map, localReg6d_twistG_waved, localReg6d_twistG_sElemCls]
  rfl

end Twist

/-! ## 2. The transfers of the local lemma -/

section Transfer

variable {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']

private theorem localReg6d_uncirc_eq {V : Type*} (e : SEdge V) (h : e.circ = false) : { e with circ := false } = e := by
  cases e with
  | mk σ c s d => simp only at h; subst h; rfl

/-- **Target 2 (a)**: the twist moves from the source to the term, `ScostLL (twist Γ) T → ScostLL Γ (twist T)` (`LGraph.scost_twist` on both
sides; F §2, last paragraph). -/
theorem localReg6d_ll_twist (c t : Bool) (Γ : LGraph E I) (T : LGraph E I') :
    LGraph.ScostLL (lwSymmTwistG c t Γ) T → LGraph.ScostLL Γ (lwSymmTwistG c t T) := by
  intro h s
  obtain ⟨s₀, hs₀, hc⟩ := h s
  refine ⟨s₀, hs₀, ?_⟩
  calc Γ.scost s₀ = (lwSymmTwistG c t Γ).scost s₀ := (LGraph.scost_twist c t Γ s₀).symm
    _ ≤ T.scost s := hc
    _ = (lwSymmTwistG c t T).scost s := (LGraph.scost_twist c t T s).symm

/-- **Target 2 (b)**: the source graph up to a permutation of its solid list and an equal number of waved edges (`LGraph.scost_perm`; the
merged `LGraph.ScostLL.of_perm` moves only the term). -/
theorem localReg6d_ll_perm (Γ Γ' : LGraph E I) (T : LGraph E I') (hS : Γ.solid.Perm Γ'.solid)
    (hW : Γ.waved.length = Γ'.waved.length) : LGraph.ScostLL Γ T → LGraph.ScostLL Γ' T := by
  intro h s
  obtain ⟨s₀, hs₀, hc⟩ := h s
  exact ⟨s₀, hs₀, (le_of_eq (LGraph.scost_perm Γ' Γ hS.symm hW.symm s₀)).trans hc⟩

/-- **Target 2 (c)**: the frame of Step 2.  `lwSymmFrame c t Γ p` is the graph with the selected edge `p.1` uncircled and put first, then
twisted; if `p.1` is uncircled, the solid list of the uncircled graph is a permutation of that of `Γ` (`lwSplit_perm`). -/
theorem localReg6d_ll_frame (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (T : LGraph E I')
    (hp : p ∈ lwSplit Γ.solid) (hc : p.1.circ = false) (h : LGraph.ScostLL (lwSymmFrame c t Γ p) T) :
    LGraph.ScostLL Γ (lwSymmTwistG c t T) := by
  have h1 : LGraph.ScostLL (lwSymmUncirc Γ p) (lwSymmTwistG c t T) := localReg6d_ll_twist c t _ _ h
  refine localReg6d_ll_perm (lwSymmUncirc Γ p) Γ _ ?_ rfl h1
  show ({ p.1 with circ := false } :: p.2).Perm Γ.solid
  rw [localReg6d_uncirc_eq p.1 hc]
  exact (lwSplit_perm Γ.solid p hp).symm

/-- **Target 2 (d)**: the frame of Step 3 (`lwSymmFrame2`: both selected edges `p.1`, `q.1` uncircled, then twisted). -/
theorem localReg6d_ll_frame2 (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (T : LGraph E I')
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hc : p.1.circ = false) (hc' : q.1.circ = false)
    (h : LGraph.ScostLL (lwSymmFrame2 c t Γ p q) T) : LGraph.ScostLL Γ (lwSymmTwistG c t T) := by
  have h1 : LGraph.ScostLL (lwSymmUncirc2 Γ p q) (lwSymmTwistG c t T) := localReg6d_ll_twist c t _ _ h
  refine localReg6d_ll_perm (lwSymmUncirc2 Γ p q) Γ _ ?_ rfl h1
  show ({ p.1 with circ := false } :: { q.1 with circ := false } :: q.2).Perm Γ.solid
  rw [localReg6d_uncirc_eq p.1 hc, localReg6d_uncirc_eq q.1 hc']
  exact ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)).symm

end Transfer

/-! ## 3. The ten new term decompositions (F §3) -/

section Terms

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the onto relabelling `I ⊕ Fin 1 ⊕ Fin 1 → I ⊕ Fin 2` of the two-fresh-vertex terms (the merged `localReg6b_phi` at a general `I`) -/
private def localReg6d_phi (E I : Type) : E ⊕ ((I ⊕ Fin 1) ⊕ Fin 1) → E ⊕ (I ⊕ Fin 2) :=
  Sum.map id ((Equiv.sumAssoc I (Fin 1) (Fin 1)).trans (Equiv.sumCongr (Equiv.refl I) finSumFinEquiv))

private theorem localReg6d_phi_surj : Function.Surjective (localReg6d_phi E I) :=
  Function.Surjective.sumMap Function.surjective_id
    ((Equiv.sumAssoc I (Fin 1) (Fin 1)).trans (Equiv.sumCongr (Equiv.refl I) finSumFinEquiv)).surjective

/-- `φ ∘ owxEmb 1 ∘ owxEmb 1 = owxEmb 2` -/
private theorem localReg6d_phi_emb (v : E ⊕ I) : localReg6d_phi E I (owxEmb 1 (owxEmb 1 v)) = owxEmb 2 v := by
  cases v <;> rfl

/-- the first fresh vertex goes to `inr (inr 0)` -/
private theorem localReg6d_phi_a : localReg6d_phi E I (owxEmb 1 (Sum.inr (Sum.inr 0))) = Sum.inr (Sum.inr 0) := rfl

/-- the second fresh vertex goes to `inr (inr 1)` -/
private theorem localReg6d_phi_b : localReg6d_phi E I (Sum.inr (Sum.inr 0)) = Sum.inr (Sum.inr 1) := rfl

/-- the edge map of the old edges: `φ ∘ owxEmb 1 ∘ owxEmb 1 = owxEmb 2` -/
private theorem localReg6d_map_phi : (SEdge.map (localReg6d_phi E I) ∘ SEdge.map (owxEmb 1) ∘ SEdge.map (owxEmb 1) :
    SEdge (E ⊕ I) → SEdge (E ⊕ (I ⊕ Fin 2))) = SEdge.map (owxEmb 2) := by
  funext e
  cases e
  simp only [Function.comp, SEdge.map, localReg6d_phi_emb]

/-- **Target 3, `T1`** (shape (g)): `T1 = owxET1 m Γ x` is `Loop(x)` at an arbitrary vertex `x : E ⊕ I`: `owxET1` and `lwPrimLoop` have the
same solid list and the same waved list, up to the coefficient. -/
theorem localReg6d_ll_T1 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) : LGraph.ScostLL Γ (owxET1 m Γ x) :=
  LGraph.ScostLL.of_perm Γ (lwPrimLoop Γ x true) (owxET1 m Γ x) (List.Perm.refl _) rfl (scostLL_loop Γ x true)

/-- **Target 3, `T2`** (shape (h)): `T2 = MoveLoop(x)` (the light-weight `⟨true, true, x, x⟩` removed, one at a fresh `α`) then `Loop(α)`, relabelled
to `I ⊕ Fin 2` by `localReg6d_phi`; the solid list of the composite is that of `owxET2` (equal lists). -/
theorem localReg6d_ll_T2 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : E ⊕ I)
    (h : Γ.solid.Perm (⟨true, true, x, x⟩ :: p.2)) : LGraph.ScostLL Γ (owxET2 m Γ p x) := by
  have h1 := scostLL_moveLoop Γ p.2 x true h
  have h2 := scostLL_loop (lwPrimMoveLoop Γ p.2 x true) (Sum.inr (Sum.inr 0)) true
  have h3 := LGraph.ScostLL.trans Γ _ _ h1 h2
  have h4 := LGraph.ScostLL.of_relabel Γ _ (localReg6d_phi E I) localReg6d_phi_surj (fun a => rfl) h3
  refine LGraph.ScostLL.of_perm Γ _ (owxET2 m Γ p x) ?_ ?_ h4
  · simp only [LGraph.relabel, lwPrimLoop, lwPrimMoveLoop, LGraph.owxExt, owxET2, List.map_append, List.map_map,
      List.map_cons, List.map_nil, localReg6d_map_phi, List.append_assoc]
    exact List.Perm.refl _
  · simp [LGraph.relabel, lwPrimLoop, lwPrimMoveLoop, owxET2, LGraph.owxExt]

private theorem localReg6d_emb_inj (k : ℕ) : Function.Injective (owxEmb k : E ⊕ I → E ⊕ (I ⊕ Fin k)) :=
  Function.Injective.sumMap Function.injective_id Sum.inl_injective

/-- the loop test is preserved by the embedding of the old vertices -/
private theorem localReg6d_emb_loop (k : ℕ) (e : SEdge (E ⊕ I)) :
    ((SEdge.map (owxEmb k) e).src = (SEdge.map (owxEmb k) e).dst ↔ e.src = e.dst) :=
  (localReg6d_emb_inj k).eq_iff

/-- the image of an edge given by its four fields -/
private theorem localReg6d_map_mk {V W : Type*} (f : V → W) (σ c : Bool) (a b : V) :
    SEdge.map f ⟨σ, c, a, b⟩ = ⟨σ, c, f a, f b⟩ := rfl

/-- the derivative edges commute with the relabelling of the old vertices -/
private theorem localReg6d_phi_owxDE_fst (e : SEdge (E ⊕ I)) :
    SEdge.map (localReg6d_phi E I)
        (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 (Sum.inr (Sum.inr 0)))
          (SEdge.map (owxEmb 1) (SEdge.map (owxEmb 1) e))).1 =
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) e)).1 := by
  cases e with
  | mk σ c s d =>
    cases σ <;> simp [owxDE, SEdge.map, localReg6d_phi_emb, localReg6d_phi_a, localReg6d_phi_b]

private theorem localReg6d_phi_owxDE_snd (e : SEdge (E ⊕ I)) :
    SEdge.map (localReg6d_phi E I)
        (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 (Sum.inr (Sum.inr 0)))
          (SEdge.map (owxEmb 1) (SEdge.map (owxEmb 1) e))).2 =
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) e)).2 := by
  cases e with
  | mk σ c s d =>
    cases σ <;> simp [owxDE, SEdge.map, localReg6d_phi_emb, localReg6d_phi_a, localReg6d_phi_b]

/-- **Target 3, `T4`** (shape (i)): `T4 = MoveLoop(x)` then `Dmove(α; lw_α, q)` (`z = v = α`, `cp = true`), relabelled; the derivative edges
commute with `φ` (`localReg6d_phi_owxDE_fst`, `_snd`). -/
theorem localReg6d_ll_T4 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q.1.src = q.1.dst ↔ q.1.circ = true) (h : Γ.solid.Perm (⟨true, true, x, x⟩ :: q.1 :: q.2)) :
    LGraph.ScostLL Γ (owxET4 m Γ x q) := by
  have h1 := scostLL_moveLoop Γ (q.1 :: q.2) x true h
  have hq1 : (SEdge.map (owxEmb 1) q.1).src = (SEdge.map (owxEmb 1) q.1).dst ↔ (SEdge.map (owxEmb 1) q.1).circ = true :=
    (localReg6d_emb_loop 1 q.1).trans hq
  have hp1 : (lwPrimMoveLoop Γ (q.1 :: q.2) x true).solid.Perm
      (⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ :: SEdge.map (owxEmb 1) q.1 ::
        q.2.map (SEdge.map (owxEmb 1))) := by
    show ((q.1 :: q.2).map (SEdge.map (owxEmb 1)) ++ [_]).Perm _
    exact List.perm_append_singleton _ _
  have h2 := scostLL_dmove (lwPrimMoveLoop Γ (q.1 :: q.2) x true) (q.2.map (SEdge.map (owxEmb 1)))
    (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)) true (SEdge.map (owxEmb 1) q.1) ⟨fun _ => rfl, fun _ => rfl⟩ hq1 hp1
  have h3 := LGraph.ScostLL.trans Γ _ _ h1 h2
  have h4 := LGraph.ScostLL.of_relabel Γ _ (localReg6d_phi E I) localReg6d_phi_surj (fun a => rfl) h3
  refine LGraph.ScostLL.of_perm Γ _ (owxET4 m Γ x q) ?_ ?_ h4
  · simp only [LGraph.relabel, lwPrimDmove, lwPrimMoveLoop, LGraph.owxExt, owxET4, List.map_append, List.map_map,
      List.map_cons, List.map_nil, localReg6d_map_phi, List.append_assoc, localReg6d_phi_owxDE_fst, localReg6d_phi_owxDE_snd]
    exact List.Perm.refl _
  · simp [LGraph.relabel, lwPrimDmove, lwPrimMoveLoop, owxET4, LGraph.owxExt]

/-- **Target 3, `P5`** (shape (j)): `P5 = oe1xP5` is `MoveOut(x; v, d)` then `AddLoop(x, red)` (the solid lists are permutations of each other). -/
theorem localReg6d_ll_P5 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (h1 : Sum.inr x ≠ v) (h2 : Sum.inr x ≠ q.1.dst)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨false, false, Sum.inr x, q.1.dst⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe1xP5 m Γ x v q) := by
  have h3 := LGraph.ScostLL.trans Γ _ _ (scostLL_moveOut Γ q.2 (Sum.inr x) v q.1.dst h1 h2 hperm)
    (scostLL_addLoop (lwPrimMoveOut Γ q.2 (Sum.inr x) v q.1.dst) (owxEmb 1 (Sum.inr x)) false)
  refine LGraph.ScostLL.of_perm Γ _ (oe1xP5 m Γ x v q) ?_ ?_ h3
  · simp only [lwPrimAddLoop, lwPrimMoveOut, LGraph.owxExt, oe1xP5]
    exact List.perm_middle.symm.trans (List.Perm.append_left _ (List.Perm.cons _ (List.Perm.swap _ _ _)))
  · simp [lwPrimAddLoop, lwPrimMoveOut, oe1xP5, LGraph.owxExt]

/-- **Target 3, `P6`** (shape (k)): `P6 = oe1xP6` is `MoveSC(x; s, v)` then `AddLoop(x, blue)`. -/
theorem localReg6d_ll_P6 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (h1 : q.1.src ≠ Sum.inr x) (h2 : Sum.inr x ≠ v)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨true, false, q.1.src, Sum.inr x⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe1xP6 m Γ x v q) := by
  have h3 := LGraph.ScostLL.trans Γ _ _ (scostLL_moveSC Γ q.2 (Sum.inr x) q.1.src v h1 h2 hperm)
    (scostLL_addLoop (lwPrimMoveSC Γ q.2 (Sum.inr x) q.1.src v) (owxEmb 1 (Sum.inr x)) true)
  refine LGraph.ScostLL.of_perm Γ _ (oe1xP6 m Γ x v q) ?_ ?_ h3
  · simp only [lwPrimAddLoop, lwPrimMoveSC, LGraph.owxExt, oe1xP6]
    exact List.perm_middle.symm.trans (List.Perm.append_left _ (List.Perm.swap _ _ _))
  · simp [lwPrimAddLoop, lwPrimMoveSC, oe1xP6, LGraph.owxExt]

/-- **Target 3, `R5`** (shape (m)): `R5 = oe2xR5` is `MoveSC(x; y', y)` then `AddLoop(x, blue)`. -/
theorem localReg6d_ll_R5 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I)
    (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe2xR5 m Γ q x y y') := by
  have h3 := LGraph.ScostLL.trans Γ _ _ (scostLL_moveSC Γ q.2 (Sum.inr x) y' y h1 h2 hperm)
    (scostLL_addLoop (lwPrimMoveSC Γ q.2 (Sum.inr x) y' y) (owxEmb 1 (Sum.inr x)) true)
  refine LGraph.ScostLL.of_perm Γ _ (oe2xR5 m Γ q x y y') ?_ ?_ h3
  · simp only [lwPrimAddLoop, lwPrimMoveSC, LGraph.owxExt, oe2xR5]
    exact List.perm_middle.symm.trans (List.Perm.append_left _ (List.Perm.cons _ (List.Perm.swap _ _ _)))
  · simp [lwPrimAddLoop, lwPrimMoveSC, oe2xR5, LGraph.owxExt]

/-- **Target 3, `R7`** (shape (o)): `R7 = oe2xR7` is `Dmove(x; x → y, q')` with `rest = ⟨true, false, y', x⟩ :: q'.2` (the removed and re-added
`G_{y'x}` cancel; the solid lists are permutations of each other). -/
theorem localReg6d_ll_R7 (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (h1 : Sum.inr x ≠ y) (hq : q'.1.src = q'.1.dst ↔ q'.1.circ = true)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q'.1 :: q'.2)) :
    LGraph.ScostLL Γ (oe2xR7 m Γ x y y' q') := by
  have hp : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: q'.1 :: ⟨true, false, y', Sum.inr x⟩ :: q'.2) :=
    hperm.trans (List.Perm.cons _ (List.Perm.swap _ _ _))
  have h2 := scostLL_dmove Γ (⟨true, false, y', Sum.inr x⟩ :: q'.2) (Sum.inr x) y false q'.1
    ⟨fun h => absurd h h1, fun h => by cases h⟩ hq hp
  refine LGraph.ScostLL.of_perm Γ _ (oe2xR7 m Γ x y y' q') ?_ ?_ h2
  · simp only [lwPrimDmove, LGraph.owxExt, oe2xR7, List.map_cons, List.cons_append]
    exact List.perm_middle.symm
  · simp [lwPrimDmove, oe2xR7, LGraph.owxExt]

/-- **Target 3, `R4`** (shape (l)): `R4 = oe2xR4` is `MoveSC(x; y', y)` then `Loop(α)`, relabelled to `I ⊕ Fin 2`. -/
theorem localReg6d_ll_R4 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I)
    (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe2xR4 m Γ q x y y') := by
  have h3 := LGraph.ScostLL.trans Γ _ _ (scostLL_moveSC Γ q.2 (Sum.inr x) y' y h1 h2 hperm)
    (scostLL_loop (lwPrimMoveSC Γ q.2 (Sum.inr x) y' y) (Sum.inr (Sum.inr 0)) true)
  have h4 := LGraph.ScostLL.of_relabel Γ _ (localReg6d_phi E I) localReg6d_phi_surj (fun a => rfl) h3
  refine LGraph.ScostLL.of_perm Γ _ (oe2xR4 m Γ q x y y') ?_ ?_ h4
  · simp only [LGraph.relabel, lwPrimLoop, lwPrimMoveSC, LGraph.owxExt, oe2xR4, List.map_append, List.map_map,
      List.map_cons, List.map_nil, localReg6d_map_phi, List.append_assoc, SEdge.map, localReg6d_phi_emb,
      localReg6d_phi_a, localReg6d_phi_b, List.cons_append, List.nil_append]
    exact List.Perm.append_left _ (List.Perm.swap _ _ _)
  · simp [LGraph.relabel, lwPrimLoop, lwPrimMoveSC, oe2xR4, LGraph.owxExt]

/-- **Target 3, `R6`** (shape (n)): `R6 = oe2xR6` is `Loop(x)` then `MoveSC(x; y', y)`, relabelled (the waved edges of the composite and of the
term differ in colour or end, e.g. the waved edge `α - β` of the term is `x - β` in the composite: only their number enters the cost). -/
theorem localReg6d_ll_R6 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I)
    (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe2xR6 m Γ q x y y') := by
  have hp : (lwPrimLoop Γ (Sum.inr x) true).solid.Perm
      (⟨true, false, owxEmb 1 (Sum.inr x), owxEmb 1 y⟩ :: ⟨true, false, owxEmb 1 y', owxEmb 1 (Sum.inr x)⟩ ::
        (q.2.map (SEdge.map (owxEmb 1)) ++ [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩])) := by
    show (Γ.solid.map (SEdge.map (owxEmb 1)) ++ [_]).Perm _
    exact (hperm.map (SEdge.map (owxEmb 1))).append_right _
  have hu : owxEmb 1 y' ≠ owxEmb 1 (Sum.inr x) := fun h => h1 ((localReg6d_emb_inj 1) h)
  have hv : owxEmb 1 (Sum.inr x) ≠ owxEmb 1 y := fun h => h2 ((localReg6d_emb_inj 1) h)
  have h3 := LGraph.ScostLL.trans Γ _ _ (scostLL_loop Γ (Sum.inr x) true)
    (scostLL_moveSC (lwPrimLoop Γ (Sum.inr x) true)
      (q.2.map (SEdge.map (owxEmb 1)) ++ [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩])
      (owxEmb 1 (Sum.inr x)) (owxEmb 1 y') (owxEmb 1 y) hu hv hp)
  have h4 := LGraph.ScostLL.of_relabel Γ _ (localReg6d_phi E I) localReg6d_phi_surj (fun a => rfl) h3
  refine LGraph.ScostLL.of_perm Γ _ (oe2xR6 m Γ q x y y') ?_ ?_ h4
  · simp only [LGraph.relabel, lwPrimLoop, lwPrimMoveSC, LGraph.owxExt, oe2xR6, List.map_append, List.map_map,
      List.map_cons, List.map_nil, localReg6d_map_phi, List.append_assoc, SEdge.map, localReg6d_phi_emb,
      localReg6d_phi_a, localReg6d_phi_b, List.cons_append, List.nil_append]
    exact List.Perm.append_left _ (List.Perm.cons _ (List.Perm.swap _ _ _))
  · simp [LGraph.relabel, lwPrimLoop, lwPrimMoveSC, oe2xR6, LGraph.owxExt]

/-- **Target 3, `R8`** (shape (p)): `R8 = oe2xR8` is `MoveSC(x; y', y)` then `Dmove(α; α → y, q')` (`z = α ≠ v = owxEmb 1 y`, `cp = false`),
relabelled. -/
theorem localReg6d_ll_R8 (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y) (hq : q'.1.src = q'.1.dst ↔ q'.1.circ = true)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q'.1 :: q'.2)) :
    LGraph.ScostLL Γ (oe2xR8 m Γ x y y' q') := by
  have hq1 : (SEdge.map (owxEmb 1) q'.1).src = (SEdge.map (owxEmb 1) q'.1).dst ↔
      (SEdge.map (owxEmb 1) q'.1).circ = true := (localReg6d_emb_loop 1 q'.1).trans hq
  have hcp : (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) = owxEmb 1 y ↔ false = true := by
    refine ⟨fun h => ?_, fun h => by cases h⟩
    cases y with
    | inl a => simp [owxEmb] at h
    | inr i => simp [owxEmb] at h
  have hp : (lwPrimMoveSC Γ (q'.1 :: q'.2) (Sum.inr x) y' y).solid.Perm
      (⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 y⟩ :: SEdge.map (owxEmb 1) q'.1 ::
        (q'.2.map (SEdge.map (owxEmb 1)) ++ [⟨true, false, owxEmb 1 y', Sum.inr (Sum.inr 0)⟩])) := by
    simp only [lwPrimMoveSC, LGraph.owxExt, List.map_cons, List.cons_append]
    refine List.Perm.trans (List.Perm.cons _ ?_) (List.Perm.swap _ _ _)
    exact (List.Perm.of_eq (List.append_assoc _ [_] [_]).symm).trans (List.perm_append_singleton _ _)
  have h3 := LGraph.ScostLL.trans Γ _ _ (scostLL_moveSC Γ (q'.1 :: q'.2) (Sum.inr x) y' y h1 h2 hperm)
    (scostLL_dmove (lwPrimMoveSC Γ (q'.1 :: q'.2) (Sum.inr x) y' y)
      (q'.2.map (SEdge.map (owxEmb 1)) ++ [⟨true, false, owxEmb 1 y', Sum.inr (Sum.inr 0)⟩])
      (Sum.inr (Sum.inr 0)) (owxEmb 1 y) false (SEdge.map (owxEmb 1) q'.1) hcp hq1 hp)
  have h4 := LGraph.ScostLL.of_relabel Γ _ (localReg6d_phi E I) localReg6d_phi_surj (fun a => rfl) h3
  refine LGraph.ScostLL.of_perm Γ _ (oe2xR8 m Γ x y y' q') ?_ ?_ h4
  · simp only [LGraph.relabel, lwPrimDmove, lwPrimMoveSC, LGraph.owxExt, oe2xR8, List.map_append, List.map_map,
      List.map_cons, List.map_nil, localReg6d_map_phi, List.append_assoc, localReg6d_map_mk, localReg6d_phi_emb,
      localReg6d_phi_a, localReg6d_phi_b, List.cons_append, List.nil_append, localReg6d_phi_owxDE_fst,
      localReg6d_phi_owxDE_snd]
    exact List.Perm.append_left _ (List.perm_append_singleton _ [_, _, _])
  · simp [LGraph.relabel, lwPrimDmove, lwPrimMoveSC, oe2xR8, LGraph.owxExt]

end Terms

/-! ## 4. Circled edges are loops, and the seventeen terms in the frame -/

section CircLoop

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the twist keeps "every circled edge is a loop" -/
private theorem localReg6d_cl_twistS {V : Type*} (c t : Bool) (l : List (SEdge V))
    (h : ∀ e ∈ l, e.circ = true → e.src = e.dst) : ∀ e ∈ l.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst := by
  intro e he hc
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  rw [lwSymmTwistS_circ] at hc
  exact (lwSymmTwistS_loop c t e0).2 (h e0 he0 hc)

private theorem localReg6d_cl_twistG (c t : Bool) (T : LGraph E I) (h : ∀ e ∈ T.solid, e.circ = true → e.src = e.dst) :
    ∀ e ∈ (lwSymmTwistG c t T).solid, e.circ = true → e.src = e.dst := by
  rw [lwSymmTwistG_solid]
  exact localReg6d_cl_twistS c t _ h

/-- the relabelling of the ends keeps "every circled edge is a loop" -/
private theorem localReg6d_cl_map {V W : Type*} (f : V → W) (l : List (SEdge V))
    (h : ∀ e ∈ l, e.circ = true → e.src = e.dst) : ∀ e ∈ l.map (SEdge.map f), e.circ = true → e.src = e.dst := by
  intro e he hc
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  show f e0.src = f e0.dst
  rw [h e0 he0 hc]

private theorem localReg6d_cl_owxExt {E' I' : Type} (Γ : LGraph E I) (emb : E ⊕ I → E' ⊕ I') (c : ℂ) (A : List (SEdge (E' ⊕ I')))
    (W : List (WEdge (E' ⊕ I'))) (h : ∀ e ∈ Γ.solid, e.circ = true → e.src = e.dst)
    (hA : ∀ e ∈ A, e.circ = true → e.src = e.dst) : ∀ e ∈ (Γ.owxExt emb c A W).solid, e.circ = true → e.src = e.dst := by
  intro e he hc
  rcases List.mem_append.1 he with he | he
  · exact localReg6d_cl_map emb _ h e he hc
  · exact hA e he hc

/-- the derivative edges are uncircled -/
private theorem localReg6d_owxDE_circ {V : Type*} (a w : V) (e : SEdge V) :
    (owxDE a w e).1.circ = false ∧ (owxDE a w e).2.circ = false := by
  unfold owxDE
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- every circled edge of a graph with `CircIffLoop` is a loop, after the twist -/
private theorem localReg6d_cl_of_circIff (c t : Bool) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) :
    ∀ e ∈ (lwSymmTwistG c t Γ).solid, e.circ = true → e.src = e.dst := by
  rw [lwSymmTwistG_solid]
  exact localReg6d_cl_twistS c t _ (fun e he hc => (hC e he).2 hc)

end CircLoop

/-! ## 5. The weight terms of Step 1 -/

section WeightGood

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the twisted graph in the frame of the light-weight: the weight and the rest -/
private theorem localReg6d_weight_perm1 (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) :
    (lwSymmTwistG c t Γ).solid.Perm (⟨true, true, x, x⟩ :: (lwSymmTwistP c t p).2) := by
  rw [lwSymmTwistG_solid, ← hx]
  exact (lwSplit_perm Γ.solid p hp).map (lwSymmTwistS c t)

private theorem localReg6d_weight_perm2 (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    (lwSymmTwistG c t Γ).solid.Perm (⟨true, true, x, x⟩ :: (lwSymmTwistP c t q).1 :: (lwSymmTwistP c t q).2) := by
  rw [lwSymmTwistG_solid, ← hx]
  exact (localReg_lwSplit_perm2 Γ.solid p hp q hq).map (lwSymmTwistS c t)

/-- `CircIffLoop` of the selected edge `q.1` after the twist -/
private theorem localReg6d_twistP_loop (c t : Bool) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (e : SEdge (E ⊕ I))
    (he : e ∈ Γ.solid) :
    (lwSymmTwistS c t e).src = (lwSymmTwistS c t e).dst ↔ (lwSymmTwistS c t e).circ = true := by
  rw [lwSymmTwistS_loop, lwSymmTwistS_circ]
  exact hC e he

/-- the rest of the weight split is circled-iff-loop, after the twist -/
private theorem localReg6d_cl_twistRest (c t : Bool) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (l : List (SEdge (E ⊕ I)))
    (hl : ∀ e ∈ l, e ∈ Γ.solid) : ∀ e ∈ l.map (lwSymmTwistS c t), e.circ = true → e.src = e.dst :=
  localReg6d_cl_twistS c t l fun e he hc => (hC e (hl e he)).2 hc

/-- **Step 1, term `T1`**: circled edges are loops, and the local lemma -/
private theorem localReg6d_good_wT1 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (x : E ⊕ I) (c t : Bool) :
    (∀ e ∈ (lwSymmOwxT1 c t m Γ x).solid, e.circ = true → e.src = e.dst) ∧ LGraph.ScostLL Γ (lwSymmOwxT1 c t m Γ x) := by
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_twist c t Γ _ (localReg6d_ll_T1 m _ x)⟩
  refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_of_circIff c t Γ hC) ?_
  intro e he hc
  simp only [List.mem_singleton] at he
  subst he
  rfl

/-- **Step 1, term `T2`** -/
private theorem localReg6d_good_wT2 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) :
    (∀ e ∈ (lwSymmOwxT2 c t m Γ p x).solid, e.circ = true → e.src = e.dst) ∧ LGraph.ScostLL Γ (lwSymmOwxT2 c t m Γ p x) := by
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_twist c t Γ _
    (localReg6d_ll_T2 m _ _ x (localReg6d_weight_perm1 c t Γ p hp x hx))⟩
  refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_twistRest c t Γ hC p.2 (lvl1_mem_split _ p hp)) ?_
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

/-- **Step 1, term `T3`** -/
private theorem localReg6d_good_wT3 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    (∀ e ∈ (lwSymmOwxT3 c t m Γ x q).solid, e.circ = true → e.src = e.dst) ∧ LGraph.ScostLL Γ (lwSymmOwxT3 c t m Γ x q) := by
  have hq1 : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_twist c t Γ _
    (localReg6c_inst_ET3 m _ x _ (localReg6d_twistP_loop c t Γ hC q.1 hq1) (localReg6d_weight_perm2 c t Γ p hp x hx q hq))⟩
  refine localReg6d_cl_owxExt _ _ _ _ _
    (localReg6d_cl_twistRest c t Γ hC q.2 fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) ?_
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · simp [(localReg6d_owxDE_circ _ _ _).1] at hc
  · simp [(localReg6d_owxDE_circ _ _ _).2] at hc
  · simp at hc

/-- **Step 1, term `T4`** -/
private theorem localReg6d_good_wT4 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    (∀ e ∈ (lwSymmOwxT4 c t m Γ x q).solid, e.circ = true → e.src = e.dst) ∧ LGraph.ScostLL Γ (lwSymmOwxT4 c t m Γ x q) := by
  have hq1 : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_twist c t Γ _
    (localReg6d_ll_T4 m _ x _ (localReg6d_twistP_loop c t Γ hC q.1 hq1) (localReg6d_weight_perm2 c t Γ p hp x hx q hq))⟩
  refine localReg6d_cl_owxExt _ _ _ _ _
    (localReg6d_cl_twistRest c t Γ hC q.2 fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) ?_
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · simp [(localReg6d_owxDE_circ _ _ _).1] at hc
  · simp [(localReg6d_owxDE_circ _ _ _).2] at hc
  · simp at hc

end WeightGood

/-! ## 6. The edge terms of Step 2 -/

section EdgeGood

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- an edge given by three of its fields -/
private theorem localReg6d_edge_eta {V : Type*} (e : SEdge V) (σ circ : Bool) (s : V) (h1 : e.σ = σ) (h2 : e.circ = circ)
    (h3 : e.src = s) : e = ⟨σ, circ, s, e.dst⟩ := by
  cases e
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- the same with the target given -/
private theorem localReg6d_edge_eta' {V : Type*} (e : SEdge V) (σ circ : Bool) (s : V) (h1 : e.σ = σ) (h2 : e.circ = circ)
    (h3 : e.dst = s) : e = ⟨σ, circ, e.src, s⟩ := by
  cases e
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- on a graph without loops `CircIffLoop` says that no edge is circled -/
private theorem localReg6d_uncirc_of_wf (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (e : SEdge (E ⊕ I)) (he : e ∈ Γ.solid) : e.circ = false := by
  cases hc : e.circ
  · rfl
  · exact absurd ((hC e he).2 hc) (hwf e he)

/-- the solid list of the frame of the selected edge `x → v` -/
private theorem localReg6d_frame_solid (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x v : E ⊕ I)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, x, v⟩) :
    (lwSymmFrame c t Γ p).solid = ⟨true, false, x, v⟩ :: p.2.map (lwSymmTwistS c t) := by
  rw [lwSymmFrame_solid, lwSymmFrameP_fst c t p _ _ hx]
  rfl

/-- circled edges of the frame are loops -/
private theorem localReg6d_cl_frame (c t : Bool) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x v : E ⊕ I)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, x, v⟩) :
    ∀ e ∈ (lwSymmFrame c t Γ p).solid, e.circ = true → e.src = e.dst := by
  rw [localReg6d_frame_solid c t Γ p x v hx]
  intro e he hc
  rcases List.mem_cons.1 he with rfl | he
  · simp at hc
  · exact localReg6d_cl_twistRest c t Γ hC p.2 (lvl1_mem_split _ p hp) e he hc

/-- the solid list of the frame, with a second selected edge -/
private theorem localReg6d_frame_perm (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x v : E ⊕ I)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, x, v⟩) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    (lwSymmFrame c t Γ p).solid.Perm
      (⟨true, false, x, v⟩ :: (lwSymmTwistP c t q).1 :: (lwSymmTwistP c t q).2) := by
  rw [localReg6d_frame_solid c t Γ p x v hx]
  exact ((lwSplit_perm p.2 q hq).map (lwSymmTwistS c t)).cons _

/-- **Step 2, term `Oe1xOwx`** -/
private theorem localReg6d_good_eOwx (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (c t : Bool)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) :
    (∀ e ∈ (lwSymmOe1xOwx c t m Γ p x).solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe1xOwx c t m Γ p x) := by
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame c t Γ p _ hp
    (localReg6d_uncirc_of_wf Γ hC hwf p.1 (lvl1_mem_split_fst _ p hp)) (localReg6b_inst_T1 m _ x)⟩
  refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_frame c t Γ hC p hp _ v hx) ?_
  intro e he hc
  simp only [List.mem_singleton] at he
  subst he
  rfl

/-- **Step 2, the derivative terms** (`P5`, `P3`; `P6`, `P4`; `D`) -/
private theorem localReg6d_good_eDs (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x)
    (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ lwSymmOe1xDs c t m Γ p x v q,
      (∀ e ∈ T.solid, e.circ = true → e.src = e.dst) ∧ LGraph.ScostLL Γ T := by
  intro T hT
  unfold lwSymmOe1xDs at hT
  obtain ⟨T0, hT0, rfl⟩ := List.mem_map.1 hT
  have hq1 : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hq1c : (lwSymmTwistP c t q).1.circ = false := by
    show (lwSymmTwistS c t q.1).circ = false
    rw [lwSymmTwistS_circ]
    exact localReg6d_uncirc_of_wf Γ hC hwf q.1 hq1
  have hq1n : (lwSymmTwistP c t q).1.src ≠ (lwSymmTwistP c t q).1.dst := fun h =>
    hwf q.1 hq1 ((lwSymmTwistS_loop c t q.1).1 h)
  have hrest : ∀ e ∈ (lwSymmTwistP c t q).2, e.circ = true → e.src = e.dst :=
    localReg6d_cl_twistRest c t Γ hC q.2 fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hperm := localReg6d_frame_perm c t Γ p (Sum.inr x) v hx q hq
  have hp1 : p.1.circ = false := localReg6d_uncirc_of_wf Γ hC hwf p.1 (lvl1_mem_split_fst _ p hp)
  suffices h : (∀ e ∈ T0.solid, e.circ = true → e.src = e.dst) ∧ LGraph.ScostLL (lwSymmFrame c t Γ p) T0 from
    ⟨localReg6d_cl_twistG c t _ h.1, localReg6d_ll_frame c t Γ p _ hp hp1 h.2⟩
  unfold oe1xDs at hT0
  split_ifs at hT0 with h1 h2
  · have e : (lwSymmTwistP c t q).1 = ⟨false, false, Sum.inr x, (lwSymmTwistP c t q).1.dst⟩ :=
      localReg6d_edge_eta _ _ _ _ h1.1 hq1c h1.2
    have hdst : (Sum.inr x : E ⊕ I) ≠ (lwSymmTwistP c t q).1.dst := fun h => hq1n (h1.2.trans h)
    have hperm' : (lwSymmFrame c t Γ p).solid.Perm (⟨true, false, Sum.inr x, v⟩ ::
        ⟨false, false, Sum.inr x, (lwSymmTwistP c t q).1.dst⟩ :: (lwSymmTwistP c t q).2) := by
      rw [← e]
      exact hperm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT0
    rcases hT0 with rfl | rfl
    · refine ⟨localReg6d_cl_owxExt _ _ _ _ _ hrest ?_, localReg6d_ll_P5 m _ x v _ hv.symm hdst hperm'⟩
      intro e he hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rfl
      · simp at hc
      · simp at hc
    · refine ⟨localReg6d_cl_owxExt _ _ _ _ _ hrest ?_, localReg6c_inst_P3 m _ x v _ hv.symm hdst hperm'⟩
      intro e he hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp at hc
      · simp at hc
  · have e : (lwSymmTwistP c t q).1 = ⟨true, false, (lwSymmTwistP c t q).1.src, Sum.inr x⟩ :=
      localReg6d_edge_eta' _ _ _ _ h2.1 hq1c h2.2
    have hsrc : (lwSymmTwistP c t q).1.src ≠ Sum.inr x := fun h => hq1n (h.trans h2.2.symm)
    have hperm' : (lwSymmFrame c t Γ p).solid.Perm (⟨true, false, Sum.inr x, v⟩ ::
        ⟨true, false, (lwSymmTwistP c t q).1.src, Sum.inr x⟩ :: (lwSymmTwistP c t q).2) := by
      rw [← e]
      exact hperm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT0
    rcases hT0 with rfl | rfl
    · refine ⟨localReg6d_cl_owxExt _ _ _ _ _ hrest ?_, localReg6d_ll_P6 m _ x v _ hsrc hv.symm hperm'⟩
      intro e he hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · simp at hc
      · rfl
      · simp at hc
    · refine ⟨localReg6d_cl_owxExt _ _ _ _ _ hrest ?_, localReg6c_inst_P4 m _ x v _ hsrc hv.symm hperm'⟩
      intro e he hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp at hc
      · simp at hc
  · simp only [List.mem_singleton] at hT0
    subst hT0
    refine ⟨localReg6d_cl_owxExt _ _ _ _ _ hrest ?_,
      localReg6c_inst_D m _ x v _ hv.symm (localReg6d_twistP_loop c t Γ hC q.1 hq1) hperm⟩
    intro e he hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp [(localReg6d_owxDE_circ _ _ _).1] at hc
    · simp [(localReg6d_owxDE_circ _ _ _).2] at hc
    · simp at hc

end EdgeGood

/-! ## 7. The `GG` terms of Step 3 -/

section GGGood

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the solid list of the frame of the selected pair `x → y`, `y' → x` -/
private theorem localReg6d_frame2_solid (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    (lwSymmFrame2 c t Γ p q).solid =
      ⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2.map (lwSymmTwistS c t) := by
  rw [lwSymmFrame2_solid]
  simp only [lwSymmFrame2P, lwSymmTwistS_with_circ, hp1, hq1]

/-- circled edges of the two-edge frame are loops -/
private theorem localReg6d_cl_frame2 (c t : Bool) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    ∀ e ∈ (lwSymmFrame2 c t Γ p q).solid, e.circ = true → e.src = e.dst := by
  rw [localReg6d_frame2_solid c t Γ p q x y y' hp1 hq1]
  intro e he hc
  rcases List.mem_cons.1 he with rfl | he
  · simp at hc
  rcases List.mem_cons.1 he with rfl | he
  · simp at hc
  · exact localReg6d_cl_twistRest c t Γ hC q.2
      (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) e he hc

/-- the rest of `q` is circled-iff-loop after the twist -/
private theorem localReg6d_cl_rest2 (c t : Bool) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ∀ e ∈ (lwSymmFrame2Q c t q).2, e.circ = true → e.src = e.dst :=
  localReg6d_cl_twistRest c t Γ hC q.2 (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))

/-- the facts the `gg` constructor gives: `y' ≠ x` from the absence of loops, and both selected edges are uncircled -/
private theorem localReg6d_gg_facts (c t : Bool) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ)
    (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    y' ≠ Sum.inr x ∧ p.1.circ = false ∧ q.1.circ = false := by
  have hpΓ : p.1 ∈ Γ.solid := lvl1_mem_split_fst _ p hp
  have hqΓ : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  refine ⟨fun h => hwf q.1 hqΓ ((lwSymmTwistS_loop c t q.1).1 (by rw [hq1]; exact h)),
    localReg6d_uncirc_of_wf Γ hC hwf p.1 hpΓ, localReg6d_uncirc_of_wf Γ hC hwf q.1 hqΓ⟩

/-- **Step 3, term `R2`** -/
private theorem localReg6d_good_gR2 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    (∀ e ∈ (lwSymmOe2xR2 c t m Γ p q x y y').solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe2xR2 c t m Γ p q x y y') := by
  obtain ⟨hy', hcp, hcq⟩ := localReg6d_gg_facts c t Γ hC hwf p q hp hq x y y' hq1
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame2 c t Γ p q _ hp hq hcp hcq
    (localReg6b_inst_R2 m _ _ x y y' hy' hy.symm ?_)⟩
  · refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_rest2 c t Γ hC p q hp hq) ?_
    intro e he hc
    simp only [List.mem_singleton] at he
    subst he
    simp at hc
  · rw [localReg6d_frame2_solid c t Γ p q x y y' hp1 hq1]
    exact List.Perm.refl _

/-- **Step 3, term `R3`** -/
private theorem localReg6d_good_gR3 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    (∀ e ∈ (lwSymmOe2xR3 c t m Γ p q x).solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe2xR3 c t m Γ p q x) := by
  obtain ⟨hy', hcp, hcq⟩ := localReg6d_gg_facts c t Γ hC hwf p q hp hq x y y' hq1
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame2 c t Γ p q _ hp hq hcp hcq (localReg6b_inst_T1 m _ x)⟩
  refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_frame2 c t Γ hC p q hp hq x y y' hp1 hq1) ?_
  intro e he hc
  simp only [List.mem_singleton] at he
  subst he
  rfl

/-- **Step 3, term `R4`** -/
private theorem localReg6d_good_gR4 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    (∀ e ∈ (lwSymmOe2xR4 c t m Γ p q x y y').solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe2xR4 c t m Γ p q x y y') := by
  obtain ⟨hy', hcp, hcq⟩ := localReg6d_gg_facts c t Γ hC hwf p q hp hq x y y' hq1
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame2 c t Γ p q _ hp hq hcp hcq
    (localReg6d_ll_R4 m _ _ x y y' hy' hy.symm ?_)⟩
  · refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_rest2 c t Γ hC p q hp hq) ?_
    intro e he hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp at hc
    · simp at hc
    · rfl
  · rw [localReg6d_frame2_solid c t Γ p q x y y' hp1 hq1]
    exact List.Perm.refl _

/-- **Step 3, term `R5`** -/
private theorem localReg6d_good_gR5 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    (∀ e ∈ (lwSymmOe2xR5 c t m Γ p q x y y').solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe2xR5 c t m Γ p q x y y') := by
  obtain ⟨hy', hcp, hcq⟩ := localReg6d_gg_facts c t Γ hC hwf p q hp hq x y y' hq1
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame2 c t Γ p q _ hp hq hcp hcq
    (localReg6d_ll_R5 m _ _ x y y' hy' hy.symm ?_)⟩
  · refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_rest2 c t Γ hC p q hp hq) ?_
    intro e he hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · rfl
    · simp at hc
    · simp at hc
  · rw [localReg6d_frame2_solid c t Γ p q x y y' hp1 hq1]
    exact List.Perm.refl _

/-- **Step 3, term `R6`** -/
private theorem localReg6d_good_gR6 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) :
    (∀ e ∈ (lwSymmOe2xR6 c t m Γ p q x y y').solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe2xR6 c t m Γ p q x y y') := by
  obtain ⟨hy', hcp, hcq⟩ := localReg6d_gg_facts c t Γ hC hwf p q hp hq x y y' hq1
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame2 c t Γ p q _ hp hq hcp hcq
    (localReg6d_ll_R6 m _ _ x y y' hy' hy.symm ?_)⟩
  · refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_rest2 c t Γ hC p q hp hq) ?_
    intro e he hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · rfl
    · simp at hc
    · simp at hc
  · rw [localReg6d_frame2_solid c t Γ p q x y y' hp1 hq1]
    exact List.Perm.refl _

/-- the perm of the two-edge frame with a third selected edge -/
private theorem localReg6d_frame2_perm (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq' : q' ∈ lwSplit q.2) :
    (lwSymmFrame2 c t Γ p q).solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ ::
      (lwSymmTwistP c t q').1 :: (lwSymmTwistP c t q').2) := by
  rw [localReg6d_frame2_solid c t Γ p q x y y' hp1 hq1]
  exact (((lwSplit_perm q.2 q' hq').map (lwSymmTwistS c t)).cons _).cons _

/-- **Step 3, term `R7`** -/
private theorem localReg6d_good_gR7 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq' : q' ∈ lwSplit q.2) :
    (∀ e ∈ (lwSymmOe2xR7 c t m Γ p q x y y' q').solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe2xR7 c t m Γ p q x y y' q') := by
  obtain ⟨hy', hcp, hcq⟩ := localReg6d_gg_facts c t Γ hC hwf p q hp hq x y y' hq1
  have hq'Γ : q'.1 ∈ Γ.solid :=
    lvl1_mem_split _ p hp q'.1 (lvl1_mem_split _ q hq q'.1 (lvl1_mem_split_fst _ q' hq'))
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame2 c t Γ p q _ hp hq hcp hcq
    (localReg6d_ll_R7 m _ x y y' _ hy.symm (localReg6d_twistP_loop c t Γ hC q'.1 hq'Γ)
      (localReg6d_frame2_perm c t Γ p q x y y' hp1 hq1 q' hq'))⟩
  refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_twistRest c t Γ hC q'.2 fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e (lvl1_mem_split _ q' hq' e he))) ?_
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp at hc
  · simp [(localReg6d_owxDE_circ _ _ _).1] at hc
  · simp [(localReg6d_owxDE_circ _ _ _).2] at hc
  · simp at hc

/-- **Step 3, term `R8`** -/
private theorem localReg6d_good_gR8 (m : ℂ) (Γ : LGraph E I) (hC : LGraph.CircIffLoop Γ) (hwf : ∀ e ∈ Γ.solid, e.src ≠ e.dst)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I)
    (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool) (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq' : q' ∈ lwSplit q.2) :
    (∀ e ∈ (lwSymmOe2xR8 c t m Γ p q x y y' q').solid, e.circ = true → e.src = e.dst) ∧
      LGraph.ScostLL Γ (lwSymmOe2xR8 c t m Γ p q x y y' q') := by
  obtain ⟨hy', hcp, hcq⟩ := localReg6d_gg_facts c t Γ hC hwf p q hp hq x y y' hq1
  have hq'Γ : q'.1 ∈ Γ.solid :=
    lvl1_mem_split _ p hp q'.1 (lvl1_mem_split _ q hq q'.1 (lvl1_mem_split_fst _ q' hq'))
  refine ⟨localReg6d_cl_twistG c t _ ?_, localReg6d_ll_frame2 c t Γ p q _ hp hq hcp hcq
    (localReg6d_ll_R8 m _ x y y' _ hy' hy.symm (localReg6d_twistP_loop c t Γ hC q'.1 hq'Γ)
      (localReg6d_frame2_perm c t Γ p q x y y' hp1 hq1 q' hq'))⟩
  refine localReg6d_cl_owxExt _ _ _ _ _ (localReg6d_cl_twistRest c t Γ hC q'.2 fun e he =>
    lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e (lvl1_mem_split _ q' hq' e he))) ?_
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp at hc
  · simp at hc
  · simp [(localReg6d_owxDE_circ _ _ _).1] at hc
  · simp [(localReg6d_owxDE_circ _ _ _).2] at hc

end GGGood

/-! ## 8. The step along `LocStep` -/

section StepLemma

/-- **(e) The step from a term to the packed outputs of its partition** (Lemma B and the local lemma; the general form of the merged
`localReg6b_inst_transfer`, the external vertices read through `P.ext`). -/
theorem localReg6d_locCostGe_term {I'' : Type} [Fintype I''] [DecidableEq I''] (m : ℂ) (P : PGraph (Fin 2))
    (T : LGraph P.E' I'') (far : Bool) (k : ℤ) (hLL : LGraph.ScostLL P.g T) (hk : PGraph.LocCostGe far k P) :
    ∀ Q0 ∈ T.partition m, PGraph.LocCostGe far k (Q0.lvl1Comp P.ext P.ext_surj) := by
  intro Q0 hQ0
  show ∀ s : Setoid (Q0.E' ⊕ Q0.I'),
    (far = true → ¬ s (Sum.inl (Q0.ext (P.ext 0))) (Sum.inl (Q0.ext (P.ext 1)))) → k ≤ LGraph.scost Q0.g s
  intro s hs
  obtain ⟨vm, hvl, hvm⟩ := LGraph.scost_partition_ge m T Q0 hQ0
  obtain ⟨s₀, hsep, hc⟩ := hLL (Setoid.comap vm s)
  have hfar : far = true → ¬ s₀ (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) := by
    intro hf
    apply hsep
    intro hc'
    apply hs hf
    have h' : (Setoid.comap vm s) (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) := hc'
    rw [Setoid.comap_rel, hvl, hvl] at h'
    exact h'
  exact (hk s₀ hfar).trans (hc.trans (hvm s))

/-- **(f) `CircIffLoop` of every partition term** from "circled ⇒ loop" of the term (`lvl1_part_struct`, induction on `lvl1Split`: a kept
edge is circled only if it is the image of a circled edge, hence a loop; an uncircled loop is circled or dropped). -/
theorem localReg6d_circIffLoop_term {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ)
    (T : LGraph E I) (Q0 : PGraph E) (hT : ∀ e ∈ T.solid, e.circ = true → e.src = e.dst) (hQ0 : Q0 ∈ T.partition m) :
    LGraph.CircIffLoop Q0.g := by
  obtain ⟨vm, d, -, -, -, -, -, hsplit⟩ := lvl1_part_struct m T Q0 hQ0
  have key : ∀ {es es' : List (SEdge (Q0.E' ⊕ Q0.I'))} {d : ℕ}, lvl1Split es es' d →
      (∀ e ∈ es, e.circ = true → e.src = e.dst) → ∀ e ∈ es', (e.src = e.dst ↔ e.circ = true) := by
    intro es es' d h
    induction h with
    | nil => intro _ e he; simp at he
    | keep e hne h ih =>
      intro hc e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · refine ⟨fun hl => ?_, hc e' List.mem_cons_self⟩
        cases hcirc : e'.circ
        · exact absurd ⟨hl, hcirc⟩ hne
        · rfl
      · exact ih (fun e he => hc e (List.mem_cons_of_mem _ he)) e' he'
    | circ e h1 h2 h ih =>
      intro hc e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact ⟨fun _ => rfl, fun _ => h1⟩
      · exact ih (fun e he => hc e (List.mem_cons_of_mem _ he)) e' he'
    | drop e h1 h2 h ih =>
      intro hc
      exact ih (fun e he => hc e (List.mem_cons_of_mem _ he))
  refine key hsplit ?_
  intro e he hc
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  show vm e0.src = vm e0.dst
  rw [hT e0 he0 hc]

end StepLemma

section LocStepCases

variable {E : Type}

/-- **Every output of a `LocStep` comes from a term with the two properties**: for every predicate `Z` of packed graphs that passes from a
term `T` of the input (circled edges are loops, `LGraph.ScostLL P.g T`) to the packed outputs of its dotted edge partition, `Z` holds at
every output of the step (the case split of `pathInv2_locStep`: three constructors, 17 terms). -/
theorem localReg6d_locStep_elim {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs)
    (hC : LGraph.CircIffLoop P.g) (Z : PGraph E → Prop)
    (hZ : ∀ {I'' : Type} [Fintype I''] [DecidableEq I''] (T : LGraph P.E' I''),
      (∀ e ∈ T.solid, e.circ = true → e.src = e.dst) → LGraph.ScostLL P.g T →
        ∀ Q0 ∈ T.partition m, Z (Q0.lvl1Comp P.ext P.ext_surj)) :
    ∀ B ∈ outs, Z B := by
  intro B hB
  cases hst with
  | weight p hp x c t hx =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1WeightOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with ((hQ | hQ) | ⟨q, hq, hQ⟩) | ⟨q, hq, hQ⟩
    · exact hZ _ (localReg6d_good_wT1 m P.g hC x c t).1 (localReg6d_good_wT1 m P.g hC x c t).2 Q0 hQ
    · exact hZ _ (localReg6d_good_wT2 m P.g hC p hp x c t hx).1 (localReg6d_good_wT2 m P.g hC p hp x c t hx).2 Q0 hQ
    · exact hZ _ (localReg6d_good_wT3 m P.g hC p hp x c t hx q hq).1 (localReg6d_good_wT3 m P.g hC p hp x c t hx q hq).2 Q0 hQ
    · exact hZ _ (localReg6d_good_wT4 m P.g hC p hp x c t hx q hq).1 (localReg6d_good_wT4 m P.g hC p hp x c t hx q hq).2 Q0 hQ
  | edge p hp x v hv c t hx hwf hbad =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1EdgeOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with hQ | ⟨q, hq, T, hT, hQ⟩
    · exact hZ _ (localReg6d_good_eOwx m P.g hC hwf p hp x v c t hx).1
        (localReg6d_good_eOwx m P.g hC hwf p hp x v c t hx).2 Q0 hQ
    · exact hZ T (localReg6d_good_eDs m P.g hC hwf p hp x v hv c t hx q hq T hT).1
        (localReg6d_good_eDs m P.g hC hwf p hp x v hv c t hx q hq T hT).2 Q0 hQ
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1GGOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with (((((hQ | hQ) | hQ) | hQ) | hQ) | ⟨q', hq', hQ⟩) | ⟨q', hq', hQ⟩
    · exact hZ _ (localReg6d_good_gR2 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).1
        (localReg6d_good_gR2 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).2 Q0 hQ
    · exact hZ _ (localReg6d_good_gR3 m P.g hC hwf p q hp hq x y y' c t hp1 hq1).1
        (localReg6d_good_gR3 m P.g hC hwf p q hp hq x y y' c t hp1 hq1).2 Q0 hQ
    · exact hZ _ (localReg6d_good_gR4 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).1
        (localReg6d_good_gR4 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).2 Q0 hQ
    · exact hZ _ (localReg6d_good_gR5 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).1
        (localReg6d_good_gR5 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).2 Q0 hQ
    · exact hZ _ (localReg6d_good_gR6 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).1
        (localReg6d_good_gR6 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1).2 Q0 hQ
    · exact hZ _ (localReg6d_good_gR7 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1 q' hq').1
        (localReg6d_good_gR7 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1 q' hq').2 Q0 hQ
    · exact hZ _ (localReg6d_good_gR8 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1 q' hq').1
        (localReg6d_good_gR8 m P.g hC hwf p q hp hq x y y' hy c t hp1 hq1 q' hq').2 Q0 hQ

end LocStepCases

/-! ## 9. The three step pins -/

section StepPins

/-- **The pin `CircIffLoopLocStepPin`**: `CircIffLoop` passes along every `LocStep`.  The hypothesis `P.g.Normal` is not used here (it is
a hypothesis of the pin; `locReg6Inv_locStep` uses it through `lvl1_step_good`). -/
theorem circIffLoop_locStep {E : Type} {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs)
    (hN : P.g.Normal) (hC : LGraph.CircIffLoop P.g) : ∀ Q ∈ outs, LGraph.CircIffLoop Q.g :=
  localReg6d_locStep_elim hst hC (fun Q => LGraph.CircIffLoop Q.g) fun T hT _ Q0 hQ0 =>
    localReg6d_circIffLoop_term m T Q0 hT hQ0

/-- **The pin `LocCostGeLocStepPin`**, the step lemma `Φ(Q') ≥ Φ(Q)` (F §2): the lower bound `k` on the cost of every merge (separating
the two external vertices if `far`) passes from the input of every `LocStep` to each of its outputs.  `P.g.Normal` is not used. -/
theorem locCostGe_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (hst : LocStep m P outs)
    (hN : P.g.Normal) (hC : LGraph.CircIffLoop P.g) (far : Bool) (k : ℤ) (hk : PGraph.LocCostGe far k P) :
    ∀ Q ∈ outs, PGraph.LocCostGe far k Q :=
  localReg6d_locStep_elim hst hC (fun Q => PGraph.LocCostGe far k Q) fun T _ hLL Q0 hQ0 =>
    localReg6d_locCostGe_term m P T far k hLL hk Q0 hQ0

/-- **The pin `LocReg6InvLocStepPin`**: the invariant of property (6) passes along every `LocStep` (`Normal` by `lvl1_step_good`, the
rest by the two theorems above). -/
theorem locReg6Inv_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (p : ℕ) (hst : LocStep m P outs)
    (hP : PGraph.LocReg6Inv p P) : ∀ Q ∈ outs, PGraph.LocReg6Inv p Q := by
  obtain ⟨hN, hC, h2, h3⟩ := hP
  intro Q hQ
  exact ⟨(lvl1_step_good hst hN Q hQ).1, circIffLoop_locStep hst hN hC Q hQ,
    locCostGe_locStep hst hN hC false (2 * (p : ℤ)) h2 Q hQ, locCostGe_locStep hst hN hC true (3 * (p : ℤ)) h3 Q hQ⟩

end StepPins

/-! ## 10. The assembly: `lem:localregular` in full -/

section Assembly

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- **`lem:localregular`, properties (1)-(6)** (`7_8:786-821`, proof `B:172-283`): the statement of the merged `lw_localregular_upto5`
(properties (1)-(5), the lists `outs`, `errs` of `lvl1_lemma_size`, the expectation identity `(eq:local_Gs)`) with the last conjunct extended
by (6) `2p ≤ ord` for every output, and the far corollary `3p ≤ ord` when the two external vertices of the output are different (remark
`B:280-283`; DECISIONS §55).  No assumption `(eq:far_ab)` (`7_8:792`) is made.  The invariant `PGraph.LocReg6Inv p` holds at the starting
graph (`fxyPowGraph_locReg6Inv`) and passes along every `LocStep` (`locReg6Inv_locStep`), hence holds at every output (`lvl1_induction`); at
a locally standard graph the cost of the trivial merge is `ord` (`locReg6_of_locCostGe`, `locReg6far_of_locCostGe`). -/
theorem lw_localregular (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
        (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
      (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧
        Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧
        (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW) ∧
      (∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
        (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
        (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
        (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : Fin 2 → Idx d (sz.L n) (sz.W n),
          ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
            (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
            (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧
      (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p ∧ Q.LocReg6 p ∧
        (Q.ext 0 ≠ Q.ext 1 → 3 * (p : ℤ) ≤ Q.g.scalingOrder)) := by
  obtain ⟨outs, errs, h1, h2, h3, h4, h5⟩ := lw_localregular_upto5 p m c hc K0 d D
  have hInv : ∀ Q ∈ outs ++ errs, Q.LocReg6Inv p := fun Q hQ =>
    lvl1_induction (h3 Q hQ).1 (fun Q : PGraph (Fin 2) => Q.LocReg6Inv p) (fxyPowGraph_locReg6Inv p)
      (fun A L hst hA B hB => locReg6Inv_locStep p hst hA B hB)
  refine ⟨outs, errs, h1, h2, h3, h4, fun Q hQ => ?_⟩
  obtain ⟨a, b, c'⟩ := h5 Q hQ
  have hI := hInv Q (List.mem_append_left _ hQ)
  exact ⟨a, b, c', locReg6_of_locCostGe (h1 Q hQ).1 hI.2.2.1,
    fun hxy => locReg6far_of_locCostGe (h1 Q hQ).1 hxy hI.2.2.2⟩

end Assembly

/-! ## 11. Compiled instances (CLAUDE.md §4 step 2) -/

section Instances

open Classical in
/-- the cost of a merge is at least `2 n_W - 2 |I|` (the kept edges and the elementary classes are counted `≥ 0`, and there are at most
`|I|` internal classes): the concrete value of `k` for the instances (4)-(6) below -/
theorem localReg6d_scost_ge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (s : Setoid (E ⊕ I)) : 2 * (Γ.waved.length : ℤ) - 2 * (Fintype.card I : ℤ) ≤ Γ.scost s := by
  have hI : (Γ.sIntCls s).card ≤ Fintype.card I := by
    unfold LGraph.sIntCls
    refine Finset.card_image_le.trans ?_
    calc _ ≤ ((Finset.univ : Finset I).map ⟨Sum.inr, Sum.inr_injective⟩).card := Finset.card_le_card ?_
      _ = Fintype.card I := by rw [Finset.card_map, Finset.card_univ]
    intro v hv
    rw [Finset.mem_filter] at hv
    cases v with
    | inl a => exact absurd (s.refl' _) (hv.2 a)
    | inr i => simp
  unfold LGraph.scost
  have h1 : (0 : ℤ) ≤ (Γ.skept s).length := by positivity
  have h2 : (0 : ℤ) ≤ (Γ.sElemCls s).card := by positivity
  have h3 : ((Γ.sIntCls s).card : ℤ) ≤ Fintype.card I := by exact_mod_cast hI
  omega

/-- Instance (1): target 1 at `Γ_2 = fxyPowGraph 2`, the twist `(c, t) = (true, true)` (conjugate and transpose), the trivial merge: the
cost is `6` (the merged `localReg6a_inst_bot2`). -/
theorem localReg6d_inst_twist : (lwSymmTwistG true true (fxyPowGraph 2)).scost ⊥ = 6 := by
  rw [LGraph.scost_twist]
  exact localReg6a_inst_bot2

/-- Instance (2): target 3, `T2 = owxET2` at `p2Graph = Γ_2`, the light-weight `β_0 = inr 1`, the selected pair `lvl1ExP2p` (the term of the merged
Step 1, the data of the merged `localReg6b_inst_T2_all`): the local lemma, through `MoveLoop(β_0)` then `Loop(α)` relabelled. -/
theorem localReg6d_inst_T2 : LGraph.ScostLL p2Graph (owxET2 (mE 0) p2Graph lvl1ExP2p (Sum.inr 1)) :=
  localReg6d_ll_T2 (mE 0) p2Graph lvl1ExP2p (Sum.inr 1) (List.Perm.refl _)

/-- Instance (3): `locReg6Inv_locStep` at the merged Step 1 of `Γ_2` (`lvl1_inst_locStep_weight`) and the starting invariant
`fxyPowGraph_locReg6Inv 2`: every output has `LocReg6Inv 2`. -/
theorem localReg6d_inst_step1 :
    ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false),
      B.LocReg6Inv 2 :=
  locReg6Inv_locStep 2 lvl1_inst_locStep_weight (fxyPowGraph_locReg6Inv 2)

/-- `lvl1ExLoopExt` is circled-iff-loop -/
theorem localReg6d_inst_circ_loopExt : LGraph.CircIffLoop lvl1ExLoopExt := by
  unfold LGraph.CircIffLoop
  decide

/-- `lvl1ExDeg1` is circled-iff-loop -/
theorem localReg6d_inst_circ_deg1 : LGraph.CircIffLoop lvl1ExDeg1 := by
  unfold LGraph.CircIffLoop
  decide

/-- `lvl1ExSame` is circled-iff-loop -/
theorem localReg6d_inst_circ_same : LGraph.CircIffLoop lvl1ExSame := by
  unfold LGraph.CircIffLoop
  decide

/-- Instance (4): Step 1 at the external vertex `a₀` of `lvl1ExLoopExt` with the conjugating selector (merged `lvl1_inst_locStep_weightExt`):
the step lemma and `CircIffLoop`, every hypothesis but `LocCostGe` discharged (`Normal` is `lvl1_inst_fail_loopExt`). -/
theorem localReg6d_inst_weightExt :
    ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExLoopExt.pack →
      ∀ B ∈ lvl1Pack lvl1ExLoopExt.pack
          (lvl1WeightOuts0 (mE 0) lvl1ExLoopExt lvl1ExLoopExtp (Sum.inl (0 : Fin 2)) true false),
        PGraph.LocCostGe far k B ∧ LGraph.CircIffLoop B.g := fun far k hk B hB =>
  ⟨locCostGe_locStep lvl1_inst_locStep_weightExt lvl1_inst_fail_loopExt.1 localReg6d_inst_circ_loopExt far k hk B hB,
    circIffLoop_locStep lvl1_inst_locStep_weightExt lvl1_inst_fail_loopExt.1 localReg6d_inst_circ_loopExt B hB⟩

/-- Instance (5): Step 2 at the degree-`1` vertex `α₀` of `lvl1ExDeg1` with the transposing selector (merged `lvl1_inst_locStep_edge`). -/
theorem localReg6d_inst_edge :
    ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExDeg1.pack →
      ∀ B ∈ lvl1Pack lvl1ExDeg1.pack
          (lvl1EdgeOuts0 (mE 0) lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true),
        PGraph.LocCostGe far k B ∧ LGraph.CircIffLoop B.g := fun far k hk B hB =>
  ⟨locCostGe_locStep lvl1_inst_locStep_edge lvl1_inst_fail_deg1.1 localReg6d_inst_circ_deg1 far k hk B hB,
    circIffLoop_locStep lvl1_inst_locStep_edge lvl1_inst_fail_deg1.1 localReg6d_inst_circ_deg1 B hB⟩

/-- Instance (6): Step 3 at the vertex `α₀` of `lvl1ExSame` (merged `lvl1_inst_locStep_gg`). -/
theorem localReg6d_inst_gg :
    ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExSame.pack →
      ∀ B ∈ lvl1Pack lvl1ExSame.pack
          (lvl1GGOuts0 (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))
            false true),
        PGraph.LocCostGe far k B ∧ LGraph.CircIffLoop B.g := fun far k hk B hB =>
  ⟨locCostGe_locStep lvl1_inst_locStep_gg lvl1_inst_fail_same.1 localReg6d_inst_circ_same far k hk B hB,
    circIffLoop_locStep lvl1_inst_locStep_gg lvl1_inst_fail_same.1 localReg6d_inst_circ_same B hB⟩

/-- Instance (4) at a concrete `k` (the lower bound `localReg6d_scost_ge` discharges `LocCostGe`): every output of Step 1 at the external vertex
`a₀` of `lvl1ExLoopExt` (`n_W = 1`, `|I| = 3`: `k = -4`) has `LocCostGe` at `k` for all merges and for the merges separating the external
vertices, and `CircIffLoop`. -/
theorem localReg6d_inst_weightExt_conc :
    ∀ B ∈ lvl1Pack lvl1ExLoopExt.pack
        (lvl1WeightOuts0 (mE 0) lvl1ExLoopExt lvl1ExLoopExtp (Sum.inl (0 : Fin 2)) true false),
      PGraph.LocCostGe false (-4) B ∧ PGraph.LocCostGe true (-4) B ∧ LGraph.CircIffLoop B.g := by
  have hk : ∀ far, PGraph.LocCostGe far (-4) lvl1ExLoopExt.pack := fun far s _ =>
    le_trans (le_of_eq (by simp [lvl1ExLoopExt, lvl1ExStd])) (localReg6d_scost_ge lvl1ExLoopExt s)
  intro B hB
  exact ⟨(localReg6d_inst_weightExt false (-4) (hk false) B hB).1, (localReg6d_inst_weightExt true (-4) (hk true) B hB).1,
    (localReg6d_inst_weightExt false (-4) (hk false) B hB).2⟩

/-- Instance (5) at a concrete `k`: Step 2 at `α₀` of `lvl1ExDeg1` (`n_W = 0`, `|I| = 3`: `k = -6`). -/
theorem localReg6d_inst_edge_conc :
    ∀ B ∈ lvl1Pack lvl1ExDeg1.pack
        (lvl1EdgeOuts0 (mE 0) lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true),
      PGraph.LocCostGe false (-6) B ∧ PGraph.LocCostGe true (-6) B ∧ LGraph.CircIffLoop B.g := by
  have hk : ∀ far, PGraph.LocCostGe far (-6) lvl1ExDeg1.pack := fun far s _ =>
    le_trans (le_of_eq (by simp [lvl1ExDeg1])) (localReg6d_scost_ge lvl1ExDeg1 s)
  intro B hB
  exact ⟨(localReg6d_inst_edge false (-6) (hk false) B hB).1, (localReg6d_inst_edge true (-6) (hk true) B hB).1,
    (localReg6d_inst_edge false (-6) (hk false) B hB).2⟩

/-- Instance (6) at a concrete `k`: Step 3 at `α₀` of `lvl1ExSame` (`n_W = 0`, `|I| = 3`: `k = -6`). -/
theorem localReg6d_inst_gg_conc :
    ∀ B ∈ lvl1Pack lvl1ExSame.pack
        (lvl1GGOuts0 (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))
          false true),
      PGraph.LocCostGe false (-6) B ∧ PGraph.LocCostGe true (-6) B ∧ LGraph.CircIffLoop B.g := by
  have hk : ∀ far, PGraph.LocCostGe far (-6) lvl1ExSame.pack := fun far s _ =>
    le_trans (le_of_eq (by simp [lvl1ExSame])) (localReg6d_scost_ge lvl1ExSame s)
  intro B hB
  exact ⟨(localReg6d_inst_gg false (-6) (hk false) B hB).1, (localReg6d_inst_gg true (-6) (hk true) B hB).1,
    (localReg6d_inst_gg false (-6) (hk false) B hB).2⟩

/-- Instance (8): `T1` at the external vertex `x = inl 0` of `Γ_2` (`Loop(x)` at an arbitrary vertex). -/
theorem localReg6d_inst_T1 : LGraph.ScostLL p2Graph (owxET1 (mE 0) p2Graph (Sum.inl 0)) :=
  localReg6d_ll_T1 (mE 0) p2Graph (Sum.inl 0)

/-- Instance (9): `T4` at `Γ_2`, the light-weight `β_0 = inr 1` and the edge `x → α_0` (`MoveLoop` then `Dmove`, relabelled). -/
theorem localReg6d_inst_T4 : LGraph.ScostLL p2Graph
    (owxET4 (mE 0) p2Graph (Sum.inr 1) (⟨true, false, Sum.inl 0, Sum.inr 0⟩,
      [⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩])) :=
  localReg6d_ll_T4 (mE 0) p2Graph (Sum.inr 1) _ (by decide) (List.Perm.refl _)

/-- Instance (10): `P6` at `Γ_2`, `x = α_0 = inr 0`, `v = y`, the blue in-edge `x → α_0` (`MoveSC` then `AddLoop`). -/
theorem localReg6d_inst_P6 : LGraph.ScostLL (fxyPowGraph 2)
    (oe1xP6 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (⟨true, false, Sum.inl 0, Sum.inr 0⟩,
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩])) :=
  localReg6d_ll_P6 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) _ (by decide) (by decide) localReg6b_inst_contractPerm

/-- Instance (11): `R4` at `Γ_2` (`MoveSC` then `Loop`, relabelled). -/
theorem localReg6d_inst_R4 : LGraph.ScostLL (fxyPowGraph 2)
    (oe2xR4 (mE 0) (fxyPowGraph 2) (⟨true, true, Sum.inr 1, Sum.inr 1⟩,
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) 0 (Sum.inl 1) (Sum.inl 0)) :=
  localReg6d_ll_R4 (mE 0) (fxyPowGraph 2) _ 0 (Sum.inl 1) (Sum.inl 0) (by decide) (by decide) localReg6b_inst_contractPerm

/-- Instance (12): `R5` at `Γ_2` (`MoveSC` then `AddLoop`); `x = α_0 = inr 0`, `y = inl 1`, `y' = inl 0`, `Γ_2.solid` is the permutation
`localReg6b_inst_contractPerm` of `α_0 → y :: x → α_0 :: rest`. -/
theorem localReg6d_inst_R5 : LGraph.ScostLL (fxyPowGraph 2)
    (oe2xR5 (mE 0) (fxyPowGraph 2) (⟨true, true, Sum.inr 1, Sum.inr 1⟩,
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) 0 (Sum.inl 1) (Sum.inl 0)) :=
  localReg6d_ll_R5 (mE 0) (fxyPowGraph 2) _ 0 (Sum.inl 1) (Sum.inl 0) (by decide) (by decide) localReg6b_inst_contractPerm

/-- Instance (13): `R6` at `Γ_2` (`Loop(x)` then `MoveSC`, relabelled). -/
theorem localReg6d_inst_R6 : LGraph.ScostLL (fxyPowGraph 2)
    (oe2xR6 (mE 0) (fxyPowGraph 2) (⟨true, true, Sum.inr 1, Sum.inr 1⟩,
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) 0 (Sum.inl 1) (Sum.inl 0)) :=
  localReg6d_ll_R6 (mE 0) (fxyPowGraph 2) _ 0 (Sum.inl 1) (Sum.inl 0) (by decide) (by decide) localReg6b_inst_contractPerm

/-- Instance (14): `R7` at `Γ_2`, the edge `q'.1` the light-weight `β_0` (`Dmove(x; x → y, q')`). -/
theorem localReg6d_inst_R7 : LGraph.ScostLL (fxyPowGraph 2)
    (oe2xR7 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (Sum.inl 0) (⟨true, true, Sum.inr 1, Sum.inr 1⟩,
      [⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩])) :=
  localReg6d_ll_R7 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (Sum.inl 0) _ (by decide) (by decide) localReg6b_inst_contractPerm

/-- Instance (15): `R8` at `Γ_2`, the edge `q'.1` the light-weight `β_0` (`MoveSC` then `Dmove`, relabelled). -/
theorem localReg6d_inst_R8 : LGraph.ScostLL (fxyPowGraph 2)
    (oe2xR8 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (Sum.inl 0) (⟨true, true, Sum.inr 1, Sum.inr 1⟩,
      [⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩])) :=
  localReg6d_ll_R8 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (Sum.inl 0) _ (by decide) (by decide) (by decide)
    localReg6b_inst_contractPerm

/-- a vertex `α` with a blue out-edge to `y` and a red out-edge to `x` (the data of the instance of `P5`) -/
def localReg6d_instG : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, false, Sum.inr 0, Sum.inl 0⟩]
  waved := []
  dotted := []
  coeff := 1

/-- Instance (16): `P5` at `localReg6d_instG` (`MoveOut(x; v, d)` then `AddLoop(x, red)`). -/
theorem localReg6d_inst_P5 : LGraph.ScostLL localReg6d_instG
    (oe1xP5 (mE 0) localReg6d_instG 0 (Sum.inl 1) (⟨false, false, Sum.inr 0, Sum.inl 0⟩, [])) :=
  localReg6d_ll_P5 (mE 0) localReg6d_instG 0 (Sum.inl 1) _ (by decide) (by decide) (List.Perm.refl _)

/-- Instance (17), the transfer (a): `Loop` at the external vertex `x` of the conjugate of `Γ_2` transfers to `Γ_2`. -/
theorem localReg6d_inst_ll_twist : LGraph.ScostLL (fxyPowGraph 2)
    (lwSymmTwistG true false (lwPrimLoop (lwSymmTwistG true false (fxyPowGraph 2)) (Sum.inl 0) true)) :=
  localReg6d_ll_twist true false (fxyPowGraph 2) _ (scostLL_loop _ (Sum.inl 0) true)

/-- Instance (18), the transfer (b): the source graph with the solid list reversed. -/
theorem localReg6d_inst_ll_perm : LGraph.ScostLL { fxyPowGraph 2 with solid := (fxyPowGraph 2).solid.reverse }
    (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) :=
  localReg6d_ll_perm (fxyPowGraph 2) _ _ (List.reverse_perm _).symm rfl (scostLL_loop _ (Sum.inl 0) true)

/-- Instance (19), the transfer (c): the frame of Step 2 at the red edge `α_1 → y` of `Γ_2`, twisted by `(true, true)`. -/
theorem localReg6d_inst_ll_frame : LGraph.ScostLL p2Graph
    (lwSymmTwistG true true (lwSymmFrame true true p2Graph (⟨false, false, Sum.inr 2, Sum.inl 1⟩,
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩,
        ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩]))) :=
  localReg6d_ll_frame true true p2Graph _ _ (lvl1_split_last _ _) rfl (scostLL_refl _)

/-- Instance (20), the transfer (d): the frame of Step 3 at the red edges `x → α_1`, `α_1 → y` of `Γ_2`, twisted by `(true, true)`. -/
theorem localReg6d_inst_ll_frame2 : LGraph.ScostLL p2Graph
    (lwSymmTwistG true true (lwSymmFrame2 true true p2Graph
      (⟨false, false, Sum.inr 2, Sum.inl 1⟩,
        [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩,
          ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩])
      (⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩,
          ⟨false, true, Sum.inr 3, Sum.inr 3⟩]))) :=
  localReg6d_ll_frame2 true true p2Graph _ _ _ (lvl1_split_last _ _) (lvl1_split_last _ _) rfl rfl (scostLL_refl _)

/-- the graph of the instance of Step 2 with all five derivative terms: the vertex `α_0 = inr 0` has the blue in-edge `G_{a_0 α_0}`
(selected), the red in-edge `Ḡ_{a_1 α_0}` (a red out-edge after the transposition: `P5`, `P3`), the blue out-edge `G_{α_0 β}` (a blue in-edge
after the transposition: `P6`, `P4`), and the blue edge `G_{β a_1}` does not meet `α_0` (`D`). -/
def localReg6d_instEdgeG : LGraph (Fin 2) (Fin 3) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨false, false, Sum.inl 1, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨true, false, Sum.inr 1, Sum.inl 1⟩]
  waved := []
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩, ⟨false, Sum.inl 1, Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inr 1⟩,
    ⟨false, Sum.inr 1, Sum.inl 1⟩]
  coeff := 1

/-- the selected edge `G_{a_0 α_0}` and the others, for `localReg6d_instEdgeG` -/
def localReg6d_instEdgep : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3)) :=
  (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [⟨false, false, Sum.inl 1, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨true, false, Sum.inr 1, Sum.inl 1⟩])

/-- Step 2 at `α_0` of `localReg6d_instEdgeG` as a `LocStep` (selector `(false, true)`, `v = a_0`; `hbad`: the degree of `α_0` is `3`). -/
theorem localReg6d_inst_locStep_edge3 : LocStep (mE 0) localReg6d_instEdgeG.pack
    (lvl1Pack localReg6d_instEdgeG.pack
      (lvl1EdgeOuts0 (mE 0) localReg6d_instEdgeG localReg6d_instEdgep (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true)) :=
  LocStep.edge localReg6d_instEdgeG.pack localReg6d_instEdgep List.mem_cons_self (0 : Fin 3)
    (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) (by decide : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) ≠ Sum.inr (0 : Fin 3)) false true rfl
    (by decide) (by decide)

/-- `localReg6d_instEdgeG` is normal -/
theorem localReg6d_inst_edge3_normal : localReg6d_instEdgeG.Normal := by decide

/-- `localReg6d_instEdgeG` is circled-iff-loop -/
theorem localReg6d_inst_edge3_circ : LGraph.CircIffLoop localReg6d_instEdgeG := by
  unfold LGraph.CircIffLoop
  decide

/-- the graph of the instance of Step 3 with `R7` and `R8`: the vertex `α_0 = inr 0` has the two blue edges `G_{a_0 α_0} G_{α_0 a_1}`
(selected, transposed by `(false, true)`), and the rest `f` has two edges between the external vertices (`q'.1` ranges over them). -/
def localReg6d_instGGG : LGraph (Fin 2) (Fin 3) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 1, Sum.inl 0⟩,
    ⟨false, false, Sum.inl 0, Sum.inl 1⟩]
  waved := []
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inl 1⟩, ⟨false, Sum.inl 1, Sum.inl 0⟩]
  coeff := 1

/-- the selected edge `G_{a_0 α_0}` and the others, for `localReg6d_instGGG` -/
def localReg6d_instGGp : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3)) :=
  (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 1, Sum.inl 0⟩,
    ⟨false, false, Sum.inl 0, Sum.inl 1⟩])

/-- the second selected edge `G_{α_0 a_1}` and the rest `f` -/
def localReg6d_instGGq : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3)) :=
  (⟨true, false, Sum.inr 0, Sum.inl 1⟩, [⟨true, false, Sum.inl 1, Sum.inl 0⟩, ⟨false, false, Sum.inl 0, Sum.inl 1⟩])

/-- Step 3 at `α_0` of `localReg6d_instGGG` as a `LocStep` (selector `(false, true)`, `y = a_0`, `y' = a_1`). -/
theorem localReg6d_inst_locStep_gg3 : LocStep (mE 0) localReg6d_instGGG.pack
    (lvl1Pack localReg6d_instGGG.pack
      (lvl1GGOuts0 (mE 0) localReg6d_instGGG localReg6d_instGGp localReg6d_instGGq (0 : Fin 3) (Sum.inl (0 : Fin 2))
        (Sum.inl (1 : Fin 2)) false true)) :=
  LocStep.gg localReg6d_instGGG.pack localReg6d_instGGp localReg6d_instGGq List.mem_cons_self List.mem_cons_self (0 : Fin 3)
    (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 3)
    (by decide : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) ≠ Sum.inr (0 : Fin 3)) false true rfl rfl (by decide) (by decide)

/-- `localReg6d_instGGG` is normal -/
theorem localReg6d_inst_gg3_normal : localReg6d_instGGG.Normal := by decide

/-- `localReg6d_instGGG` is circled-iff-loop -/
theorem localReg6d_inst_gg3_circ : LGraph.CircIffLoop localReg6d_instGGG := by
  unfold LGraph.CircIffLoop
  decide

/-- the derivative terms of `localReg6d_instEdgeG` at `(c, t) = (false, true)`: for the three edges of the rest `p.2`, the lists `[P5, P3]`,
`[P6, P4]` and `[D]` (lengths `2, 2, 1`) -/
theorem localReg6d_inst_edge3_terms :
    (lwSplit localReg6d_instEdgep.2).map (fun q => (lwSymmOe1xDs false true (mE 0) localReg6d_instEdgeG localReg6d_instEdgep 0
      (Sum.inl 0) q).length) = [2, 2, 1] := by decide

/-- the rest `f` of `localReg6d_instGGG` has two edges: `R7` and `R8` occur twice -/
theorem localReg6d_inst_gg3_terms : (lwSplit localReg6d_instGGq.2).length = 2 := by decide

/-- Instance (21): the step lemma and `CircIffLoop` at Step 2 with **all five derivative terms** (`P5`, `P3` from the red in-edge of `α_0`, `P6`,
`P4` from its blue out-edge, `D` from the edge not meeting `α_0`, besides `Oe1xOwx`): every output has `LocCostGe` at `k = -6` (`n_W = 0`,
`|I| = 3`, `localReg6d_scost_ge`), for all merges and for those separating the external vertices, and `CircIffLoop`. -/
theorem localReg6d_inst_edge3 :
    ∀ B ∈ lvl1Pack localReg6d_instEdgeG.pack
        (lvl1EdgeOuts0 (mE 0) localReg6d_instEdgeG localReg6d_instEdgep (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true),
      PGraph.LocCostGe false (-6) B ∧ PGraph.LocCostGe true (-6) B ∧ LGraph.CircIffLoop B.g := by
  have hk : ∀ far, PGraph.LocCostGe far (-6) localReg6d_instEdgeG.pack := fun far s _ =>
    le_trans (le_of_eq (by simp [localReg6d_instEdgeG])) (localReg6d_scost_ge localReg6d_instEdgeG s)
  intro B hB
  exact ⟨locCostGe_locStep localReg6d_inst_locStep_edge3 localReg6d_inst_edge3_normal localReg6d_inst_edge3_circ false (-6)
      (hk false) B hB,
    locCostGe_locStep localReg6d_inst_locStep_edge3 localReg6d_inst_edge3_normal localReg6d_inst_edge3_circ true (-6)
      (hk true) B hB,
    circIffLoop_locStep localReg6d_inst_locStep_edge3 localReg6d_inst_edge3_normal localReg6d_inst_edge3_circ B hB⟩

/-- Instance (22): the same at Step 3 with `R7`, `R8` (two edges in the rest `f`, besides `R2`-`R6`). -/
theorem localReg6d_inst_gg3 :
    ∀ B ∈ lvl1Pack localReg6d_instGGG.pack
        (lvl1GGOuts0 (mE 0) localReg6d_instGGG localReg6d_instGGp localReg6d_instGGq (0 : Fin 3) (Sum.inl (0 : Fin 2))
          (Sum.inl (1 : Fin 2)) false true),
      PGraph.LocCostGe false (-6) B ∧ PGraph.LocCostGe true (-6) B ∧ LGraph.CircIffLoop B.g := by
  have hk : ∀ far, PGraph.LocCostGe far (-6) localReg6d_instGGG.pack := fun far s _ =>
    le_trans (le_of_eq (by simp [localReg6d_instGGG])) (localReg6d_scost_ge localReg6d_instGGG s)
  intro B hB
  exact ⟨locCostGe_locStep localReg6d_inst_locStep_gg3 localReg6d_inst_gg3_normal localReg6d_inst_gg3_circ false (-6)
      (hk false) B hB,
    locCostGe_locStep localReg6d_inst_locStep_gg3 localReg6d_inst_gg3_normal localReg6d_inst_gg3_circ true (-6)
      (hk true) B hB,
    circIffLoop_locStep localReg6d_inst_locStep_gg3 localReg6d_inst_gg3_normal localReg6d_inst_gg3_circ B hB⟩

section InstExpansion

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- Instance (7): **`lw_localregular` at `p = 2`**, `d = 3`, `c = 1/4`, `K0 = 1` (`L^3 ≤ W`), `D = 10`, with the data of the merged
`localReg2_inst_expansion` (the regime is evaluated at `W = 27`, `L = 3`, `Ψ = 27^{-1/4}`; the expectation identity holds at the merged
instance data of `Graph/LWWeightExp.lean`: `d = 3`, `L = 3`, `W = 1`, `m = i`, `z = zt 0 (1/2)`, `u = 1/2`, every hypothesis discharged),
with the last conjunct read: every output of `outs` is locally standard with `(1)`-`(6)` at `p = 2` (`4 ≤ ord`), and `6 ≤ ord` if its two
external vertices differ. -/
theorem localReg6d_inst_expansion :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧
      ∫ ω, (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum ∧
      (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg345 2 ∧ Q.LocReg6 2 ∧
        (Q.ext 0 ≠ Q.ext 1 → (6 : ℤ) ≤ Q.g.scalingOrder)) := by
  obtain ⟨outs, errs, h1, h2, -, hid, h5⟩ :=
    lw_localregular 2 (mE 0) (1 / 4) (by norm_num) 1 3 10
  refine ⟨outs, errs, fun Q hQ => ?_, fun Q hQ => ?_, ?_, fun Q hQ => ?_⟩
  · obtain ⟨a, b⟩ := h1 Q hQ
    have e : (fxyPowGraph 2).pack.g.scalingOrder = 2 := fxyPowGraph_ord 2
    exact ⟨a, by rw [e] at b; exact b⟩
  · refine h2 Q hQ 27 3 _ (by norm_num) (by norm_num) (by norm_num) ?_ (le_refl _)
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · exact hid lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num) (lwWx_mE_ne 0 lwWx_inst_hE)
      (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 lwSymmInstL
  · obtain ⟨a, b, c, d, e⟩ := h5 Q hQ
    exact ⟨a, b, c, d, fun hxy => by have := e hxy; norm_num at this; exact this⟩

/-- Instance (7), the shape of the check file: `lw_localregular` at `p = 2` read through its last conjunct. -/
theorem localReg6d_inst_last :
    ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs ++ errs, Q.g.Normal) ∧
      ∀ Q ∈ outs, Q.LocStd ∧ Q.LocReg6 2 ∧ (Q.ext 0 ≠ Q.ext 1 → (6 : ℤ) ≤ Q.g.scalingOrder) := by
  obtain ⟨outs, errs, -, -, h3, -, h5⟩ := lw_localregular 2 (mE 0) (1 / 4) (by norm_num) 1 3 10
  refine ⟨outs, errs, fun Q hQ => (h3 Q hQ).2.1, fun Q hQ => ?_⟩
  obtain ⟨a, -, -, d, e⟩ := h5 Q hQ
  exact ⟨a, d, fun hxy => by have := e hxy; norm_num at this; exact this⟩

end InstExpansion

end Instances

end RBM.Graph

end
