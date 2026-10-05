/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular2

/-!
# LW-10c1: `lem:localregular`, property (6), part 1 (T2184)

The cost of a merge, Lemmas A and B, the final step, the initial values.

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:786-821` (cited `7_8:line`;
`lem:localregular`, property (6) = `(eq:sizeGammamu)`, `7_8:815-818`) and
`paper/tex/B_graphical_lemmas.tex` (cited `B:line`): `strat_local` `B:135-157`, the starting graph
`(eq:originGamma)` `B:172-176`, the proof of (6) `B:200-278` (the edge and `GG` cases are omitted
there, `B:272-275`), the remark `B:280-283`.
Design: DECISIONS §47, §55 (LW-10c is split into c1-c4: this file is c1, then
`LocalRegular6b`-`6d`); the mathematics is the Fable report
`docs/claude-team/fable/2026-10-05-localreg6-locallemma.md` (cited F).

## The route of (6): a local cost minimised over merges

The paper tracks `ord + n_dv + n_lw` along `strat_local` and asserts a monotone step (`B:275-277`);
that step assertion fails (DECISIONS §47).  F replaces it by the local cost `c = ord + #elem` of the
graph merged along an equivalence relation (a *merge*) `s` on its vertices, and the invariant
`Φ(Q) = min_s c_s(Q)`:

* `LGraph.scost Γ s` (`c_s`) is `#kept + 2 n_W - 2 #(internal classes) + #(elementary internal
  classes)`, written without building the merged graph: an edge is *kept* if it is circled or joins
  two classes; a class is *internal* if it has no external member; it is *elementary* if its
  half-edge pattern `(b-in, b-out, r-in, r-out)` (`lwHalfPat` of the kept edges at the members) is
  `(1, 1, 0, 0)` or `(0, 0, 1, 1)` (a lone light-weight or an SC vertex).  A merge is a
  `Setoid (E ⊕ I)`.
* `PGraph.LocCostGe far k P`: every merge (separating `x = P.ext 0`, `y = P.ext 1` when `far`)
  costs at least `k`; `PGraph.LocReg6Inv p` is
  `Normal ∧ CircIffLoop ∧ LocCostGe false (2p) ∧ LocCostGe true (3p)`.
* `LGraph.ScostLL Γ T` is the local lemma for a term `T` of `Γ`: every merge `s` of `T` is matched
  by a merge `s₀` of `Γ` that keeps apart every pair of external vertices that `s` keeps apart, at
  no higher cost.  The seven primitive moves (`lwPrim*`) are the pieces of the 17 output terms of
  `strat_local` (F §3).  Their local lemmas, the composition, the decompositions, the step lemma
  `Φ(Q') ≥ Φ(Q)` and the assembly are pinned in `docs/tickets/checks/T2184-check.lean` (section 4)
  and proved in c2-c4.

## At the end of the chain (this file)

* Lemma A (`scost_cons_loop_ge`): adding a circled loop never lowers the cost: `#kept` rises by
  one, the internal classes do not change, only the class of the loop's vertex changes its pattern,
  so `#elemCls` falls by at most one.
* Lemma B (`scost_le_of_lvl1Split`, `scost_partition_ge`): the weight split of the dotted edge
  partition circles or drops uncircled loops (an uncircled loop is never kept).  The induction on
  `lvl1Split` carries a prefix `b` of solid edges (`localReg6a_split_aux`:
  `scost (b ++ es) ≤ scost (b ++ es')`), because the cost of an edge list is not monotone under a
  common prefix (preflight finding F1, prove report (a)).  The pullback through the vertex map `vm`
  of the partition term is the exact identity `scost_relabel` (`[v] ↦ [vm v]` is a bijection of the
  quotients) followed by the split.
* The final step: `scost_bot` (`c_⊥ = ord + #elem` on a normal graph), `nElem_eq_zero_of_locStd` (a
  locally standard graph has no elementary internal vertex), hence `locReg6_of_locCostGe` (`k ≤ ord`
  from the all-merges bound) and `locReg6far_of_locCostGe` (from the bound for merges separating
  `x` and `y`).
* The initial values `fxyPowGraph_locCostGe`: for every merge `s` of `Γ_p`,
  `scost s + Σ_i (d_i + a_i + b_i) ≥ 5p` (`d_i` the dropped edges of the block `i`, `a_i`, `b_i` the
  indicators that `α_i`, `β_i` lie in an internal class), and per block `d_i + a_i + b_i ≤ 3`
  (`≤ 2` if `s` separates `x` and `y`); hence `Φ^all(Γ_p) ≥ 2p` and `Φ^far(Γ_p) ≥ 3p`;
  `fxyPowGraph_locReg6Inv` collects `Normal` and `CircIffLoop`.

## Contents (namespace `RBM.Graph`; helpers carry the prefix `localReg6a_`)

1. The pinned vocabulary of LW-10c, verbatim from the check file (19 definitions, written before
   any `open Classical`).
2. The pattern and class API.
3. Target 2: `LGraph.scost_perm`, `LGraph.scost_relabel`.
4. Targets 3-4: `LGraph.scost_cons_loop_ge`, `LGraph.scost_le_of_lvl1Split`,
   `LGraph.scost_partition_ge`.
5. Target 5: `LGraph.scost_bot`, `LGraph.nElem_eq_zero_of_locStd`, `locReg6_of_locCostGe`,
   `locReg6far_of_locCostGe`.
6. Target 6: `fxyPowGraph_locCostGe`, `fxyPowGraph_locReg6Inv`.
7. Compiled instances of every target (named theorems `localReg6a_inst*`: `fxyPowGraph 2`,
   `fxyPowGraph 3`, the instance graph `localReg6a_instXY` with `ord = 4`, where the far bound
   `4 ≤ ord` is sharp, and the merged locally standard graph `localReg2_inst_Q` with two internal
   vertices and `ord = 2`, where the final step gives the sharp bound `2 ≤ ord`).

## Differences from the paper (delta candidates, numbered by the dispatcher)

* `T2184a`: (6) is proved through the local cost `c = ord + #elem` minimised over merges, not
  through `ord + n_dv + n_lw` (`B:200-278`); the initial values `Φ^far(Γ_p) = 3p`,
  `Φ^all(Γ_p) = 2p` replace `3p - n_dv/2 > 2p`.
* `T2184b`: a merge is a setoid on the vertices; a class is external iff it contains an external
  vertex; an edge is kept iff it is circled or joins two classes.
* `T2184c`: the edge and `GG` cases omitted in `B:272-275` are supplied by c2-c4.
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

/-! ## 1. The pinned vocabulary of LW-10c (check file section 2, verbatim) -/

section Pattern

variable {V : Type*}

/-- **The half-edge pattern** `(b-in, b-out, r-in, r-out)` of the solid edges `es` at the vertex set `K` (Fable report §1):
an edge of colour `c` (blue `σ = true`, red `σ = false`) gives one `c-out` at its source and one `c-in` at its target; a
loop at a vertex of `K` gives both ((E5): a loop of colour `c` and a pair `{c-in, c-out}` are the same). -/
def lwHalfPat (es : List (SEdge V)) (K : V → Prop) [DecidablePred K] : ℕ × ℕ × ℕ × ℕ :=
  (es.countP (fun e => e.σ && decide (K e.dst)), es.countP (fun e => e.σ && decide (K e.src)),
    es.countP (fun e => !e.σ && decide (K e.dst)), es.countP (fun e => !e.σ && decide (K e.src)))

/-- **Elementary pattern** (Fable report §1): one `c-in` and one `c-out` of one colour `c` and nothing else (a lone
light-weight or an SC vertex). -/
def lwElem (h : ℕ × ℕ × ℕ × ℕ) : Bool := decide (h = (1, 1, 0, 0) ∨ h = (0, 0, 1, 1))

end Pattern

section Cost

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The half-edge pattern of `Γ` at the vertex `v`. -/
def LGraph.halfPat (Γ : LGraph E I) (v : E ⊕ I) : ℕ × ℕ × ℕ × ℕ := lwHalfPat Γ.solid (· = v)

/-- `#elem(Γ)`: the number of internal vertices with an elementary pattern. -/
def LGraph.nElem (Γ : LGraph E I) : ℕ :=
  (Finset.univ.filter fun i : I => lwElem (LGraph.halfPat Γ (Sum.inr i)) = true).card

open Classical in
/-- The solid edges **kept** when `Γ` is merged along `s` (Fable report §1, `M_π`): the circled edges and the edges
between different classes; an uncircled edge inside a class (an uncircled loop included) is dropped. -/
def LGraph.skept (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : List (SEdge (E ⊕ I)) :=
  Γ.solid.filter fun e => e.circ || !decide (s e.src e.dst)

open Classical in
/-- The **internal classes** of `s`: the classes without an external vertex. -/
def LGraph.sIntCls (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : Finset (Quotient s) :=
  (Finset.univ.filter fun v : E ⊕ I => ∀ a : E, ¬ s (Sum.inl a) v).image (Quotient.mk s)

open Classical in
/-- The **elementary internal classes** of `s`: internal classes whose pattern (the half-edges of the kept edges at the
members of the class) is elementary. -/
def LGraph.sElemCls (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : Finset (Quotient s) :=
  (Finset.univ.filter fun v : E ⊕ I =>
      (∀ a : E, ¬ s (Sum.inl a) v) ∧ lwElem (lwHalfPat (LGraph.skept Γ s) (fun w => s w v)) = true).image
    (Quotient.mk s)

/-- **The setoid cost** `c_s(Γ) = c(M_π Γ) = #kept + 2 n_W - 2 #(internal classes) + #(elementary internal classes)`
(Fable report §1; `c = ord + #elem` of the merged graph, written without a merged `LGraph`). -/
def LGraph.scost (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : ℤ :=
  ((LGraph.skept Γ s).length : ℤ) + 2 * ((Γ.waved.length : ℤ) - ((LGraph.sIntCls Γ s).card : ℤ)) +
    ((LGraph.sElemCls Γ s).card : ℤ)

/-- The standing hypothesis of the local lemma (Fable report §1): a solid edge is a loop if and only if it is circled. -/
def LGraph.CircIffLoop (Γ : LGraph E I) : Prop := ∀ e ∈ Γ.solid, (e.src = e.dst ↔ e.circ = true)

/-- **The local lemma (LL) for a term `T` of `Γ`** (Fable report §2, in the form the step lemma consumes): every setoid on
the vertices of `T` is matched by a setoid on those of `Γ` that keeps every pair of external vertices apart that `s`
keeps apart, at no higher cost.  (The report's "restriction, or a coarsening by at most two merges" is how `s₀` is
built; it is not part of the interface.) -/
def LGraph.ScostLL {I' : Type} [Fintype I'] [DecidableEq I'] (Γ : LGraph E I) (T : LGraph E I') : Prop :=
  ∀ s : Setoid (E ⊕ I'), ∃ s₀ : Setoid (E ⊕ I),
    (∀ a b : E, ¬ s (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧
      LGraph.scost Γ s₀ ≤ LGraph.scost T s

end Cost

/-- **The invariant** (Fable report §7): every merge (separating `x = P.ext 0`, `y = P.ext 1` if `far`) costs at least
`k`. -/
def PGraph.LocCostGe (far : Bool) (k : ℤ) (P : PGraph (Fin 2)) : Prop :=
  ∀ s : Setoid (P.E' ⊕ P.I'), (far = true → ¬ s (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1))) →
    k ≤ LGraph.scost P.g s

/-- **The invariant of property (6) carried along `strat_local`**: normal, circled iff loop, `Φ^all ≥ 2p`, `Φ^far ≥ 3p`. -/
def PGraph.LocReg6Inv (p : ℕ) (Q : PGraph (Fin 2)) : Prop :=
  Q.g.Normal ∧ LGraph.CircIffLoop Q.g ∧ PGraph.LocCostGe false (2 * (p : ℤ)) Q ∧
    PGraph.LocCostGe true (3 * (p : ℤ)) Q

section Prims

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-! The seven primitive moves (Fable report §3), in the frame (the expanded edge blue, out of `z`).  The fresh vertex is
`α = inr (inr 0)`; the old vertices enter through `owxEmb 1`; `rest` is the solid list after the removed edges; the
coefficient and the dotted edges do not enter `scost`. -/

/-- `Loop(z)`: a light-weight of colour `col` at a fresh `α`, the waved edge `z - α`. -/
def lwPrimLoop (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) : LGraph E (I ⊕ Fin 1) :=
  Γ.owxExt (owxEmb 1) 1 [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩]

/-- `AddLoop(z, col)`: a light-weight of colour `col` at `z`. -/
def lwPrimAddLoop (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) : LGraph E I :=
  { Γ with solid := ⟨col, true, z, z⟩ :: Γ.solid }

/-- `MoveLoop(z)`: the light-weight `⟨col, true, z, z⟩` removed (`rest`), one of colour `col` at a fresh `α`, `z - α`. -/
def lwPrimMoveLoop (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z : E ⊕ I) (col : Bool) : LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) 1
    [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩]

/-- `MoveSC(z; u, v)`: `z → v` and `u → z` (blue) removed (`rest`), `u → α`, `α → v` (blue) added, `z - α`. -/
def lwPrimMoveSC (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) : LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) 1
    [⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩]

/-- `MoveOut(z; v, d)`: `z → v` (blue) and `z → d` (red) removed (`rest`), `α → v` (blue), `α → d` (red) added, `z - α`. -/
def lwPrimMoveOut (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I) : LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) 1
    [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 d⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩]

/-- `Dmove(z; p, q)`: `p = z → v` (blue; the blue light-weight of `z` when `v = z`) and `q` removed (`rest`), the two
derivative edges `owxDE α z q` (blue `q = a → b`: `a → α`, `z → b`; red: `a → z`, `α → b`) and `α → v` (blue) added,
`z - α` (as `owxT3`, `LWWeightExp.lean:677`, with `z = v = x`). -/
def lwPrimDmove (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (q : SEdge (E ⊕ I)) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) 1
    [(owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 z) (SEdge.map (owxEmb 1) q)).1,
      (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 z) (SEdge.map (owxEmb 1) q)).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩]

/-- `Contract(z; u, v)`: `z → v` and `u → z` (blue) removed (`rest`), `u → v` (blue) added, one waved edge `z - v`; no new
vertex (as `oe2xR2`, `LWGGExp.lean:485`). -/
def lwPrimContract (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) : LGraph E I :=
  { Γ with solid := ⟨true, false, u, v⟩ :: rest, waved := ⟨false, true, z, v⟩ :: Γ.waved }

end Prims

/-! ## 2. The pattern and class API (helpers prefixed `localReg6a_`) -/

section PatternAPI

variable {V : Type*}

/-- the pattern depends only on the extension of the predicate -/
theorem localReg6a_halfPat_congr (es : List (SEdge V)) {K K' : V → Prop} [DecidablePred K] [DecidablePred K']
    (h : ∀ w, K w ↔ K' w) : lwHalfPat es K = lwHalfPat es K' := by
  have : ∀ w, decide (K w) = decide (K' w) := fun w => decide_eq_decide.2 (h w)
  simp only [lwHalfPat, this]

/-- the pattern is additive on lists -/
theorem localReg6a_halfPat_append (l₁ l₂ : List (SEdge V)) (K : V → Prop) [DecidablePred K] :
    lwHalfPat (l₁ ++ l₂) K = lwHalfPat l₁ K + lwHalfPat l₂ K := by
  simp [lwHalfPat, List.countP_append]

/-- the pattern is invariant under permutation of the edges -/
theorem localReg6a_halfPat_perm {l₁ l₂ : List (SEdge V)} (h : l₁.Perm l₂) (K : V → Prop) [DecidablePred K] :
    lwHalfPat l₁ K = lwHalfPat l₂ K := by
  simp only [lwHalfPat, h.countP_eq]

/-- the pattern of a relabelled list is the pattern of the list at the pulled-back predicate -/
theorem localReg6a_halfPat_map {W : Type*} (f : V → W) (es : List (SEdge V)) (K : W → Prop) [DecidablePred K] :
    lwHalfPat (es.map (SEdge.map f)) K = lwHalfPat es (fun v => K (f v)) := by
  simp only [lwHalfPat, List.countP_map, Function.comp_def, SEdge.map]
  rfl

/-- a loop outside the vertex set does not change the pattern -/
theorem localReg6a_halfPat_cons_loop (e : SEdge V) (es : List (SEdge V)) (K : V → Prop) [DecidablePred K]
    (he : e.src = e.dst) (hK : ¬ K e.src) : lwHalfPat (e :: es) K = lwHalfPat es K := by
  have h2 : ¬ K e.dst := he ▸ hK
  simp [lwHalfPat, List.countP_cons, hK, h2]

end PatternAPI

section ClassAPI

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
theorem localReg6a_mem_skept (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (e : SEdge (E ⊕ I)) :
    e ∈ Γ.skept s ↔ e ∈ Γ.solid ∧ (e.circ = true ∨ ¬ s e.src e.dst) := by
  simp [LGraph.skept]

open Classical in
theorem localReg6a_mem_sIntCls (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (c : Quotient s) :
    c ∈ Γ.sIntCls s ↔ ∃ v : E ⊕ I, (∀ a : E, ¬ s (Sum.inl a) v) ∧ Quotient.mk s v = c := by
  simp [LGraph.sIntCls]

open Classical in
theorem localReg6a_mem_sElemCls (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (c : Quotient s) :
    c ∈ Γ.sElemCls s ↔ ∃ v : E ⊕ I, (∀ a : E, ¬ s (Sum.inl a) v) ∧
      lwElem (lwHalfPat (Γ.skept s) (fun w => s w v)) = true ∧ Quotient.mk s v = c := by
  simp [LGraph.sElemCls, and_assoc]

open Classical in
theorem localReg6a_sElemCls_subset (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : Γ.sElemCls s ⊆ Γ.sIntCls s := by
  intro c hc
  obtain ⟨v, hv, -, rfl⟩ := (localReg6a_mem_sElemCls Γ s c).1 hc
  exact (localReg6a_mem_sIntCls Γ s _).2 ⟨v, hv, rfl⟩

end ClassAPI

/-! ## 3. Target 2: the cost API -/

section CostAPI

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **Target 2a**: the cost sees the solid edges up to order and only the number of waved edges. -/
theorem LGraph.scost_perm (Γ Γ' : LGraph E I) (hS : Γ.solid.Perm Γ'.solid)
    (hW : Γ.waved.length = Γ'.waved.length) (s : Setoid (E ⊕ I)) : Γ.scost s = Γ'.scost s := by
  classical
  have hk : (Γ.skept s).Perm (Γ'.skept s) := hS.filter _
  have hE : Γ.sElemCls s = Γ'.sElemCls s := by
    ext c
    rw [localReg6a_mem_sElemCls, localReg6a_mem_sElemCls]
    refine exists_congr fun v => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [localReg6a_halfPat_perm hk]
  unfold LGraph.scost
  rw [hk.length_eq, hW, hE]
  rfl

end CostAPI

section Relabel

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

/-- the map of the quotients induced by a vertex map `vm` (`[v] ↦ [vm v]`, from `comap vm s` to `s`) -/
def localReg6a_qmap {V W : Type} (vm : V → W) (s : Setoid W) : Quotient (Setoid.comap vm s) → Quotient s :=
  Quotient.map vm (fun _ _ h => h)

theorem localReg6a_qmap_mk {V W : Type} (vm : V → W) (s : Setoid W) (v : V) :
    localReg6a_qmap vm s (Quotient.mk _ v) = Quotient.mk s (vm v) := rfl

/-- `[v] ↦ [vm v]` is injective (`Setoid.comap_rel`) -/
theorem localReg6a_qmap_injective {V W : Type} (vm : V → W) (s : Setoid W) :
    Function.Injective (localReg6a_qmap vm s) := by
  intro c c' h
  obtain ⟨a, rfl⟩ := Quotient.exists_rep c
  obtain ⟨b, rfl⟩ := Quotient.exists_rep c'
  have h' : Quotient.mk s (vm a) = Quotient.mk s (vm b) := h
  have h'' : vm a ≈ vm b := Quotient.exact h'
  exact Quotient.sound h''

open Classical in
/-- the kept edges of a relabelled graph are the images of the kept edges at the pulled-back setoid -/
theorem localReg6a_skept_relabel (Δ : LGraph E I) (vm : E ⊕ I → E' ⊕ I') (s : Setoid (E' ⊕ I')) :
    (Δ.relabel vm).skept s = (Δ.skept (Setoid.comap vm s)).map (SEdge.map vm) := by
  unfold LGraph.skept LGraph.relabel
  simp only [List.filter_map]
  rfl

open Classical in
theorem localReg6a_sIntCls_relabel (Δ : LGraph E I) (ext : E → E') (hext : Function.Surjective ext)
    (vm : E ⊕ I → E' ⊕ I') (hvm : Function.Surjective vm) (hvl : ∀ a : E, vm (Sum.inl a) = Sum.inl (ext a))
    (s : Setoid (E' ⊕ I')) :
    (Δ.relabel vm).sIntCls s = (Δ.sIntCls (Setoid.comap vm s)).image (localReg6a_qmap vm s) := by
  ext c
  rw [localReg6a_mem_sIntCls, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, rfl⟩ := hvm w
    refine ⟨Quotient.mk _ v, (localReg6a_mem_sIntCls _ _ _).2 ⟨v, ?_, rfl⟩, rfl⟩
    intro a h
    exact hw (ext a) (by rw [← hvl]; exact h)
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨v, hv, rfl⟩ := (localReg6a_mem_sIntCls _ _ _).1 hc'
    refine ⟨vm v, ?_, rfl⟩
    intro a' h
    obtain ⟨a, rfl⟩ := hext a'
    exact hv a (by show s (vm (Sum.inl a)) (vm v); rw [hvl]; exact h)

open Classical in
theorem localReg6a_sElemCls_relabel (Δ : LGraph E I) (ext : E → E') (hext : Function.Surjective ext)
    (vm : E ⊕ I → E' ⊕ I') (hvm : Function.Surjective vm) (hvl : ∀ a : E, vm (Sum.inl a) = Sum.inl (ext a))
    (s : Setoid (E' ⊕ I')) :
    (Δ.relabel vm).sElemCls s = (Δ.sElemCls (Setoid.comap vm s)).image (localReg6a_qmap vm s) := by
  have hk := localReg6a_skept_relabel Δ vm s
  ext c
  rw [localReg6a_mem_sElemCls, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hel, rfl⟩
    obtain ⟨v, rfl⟩ := hvm w
    refine ⟨Quotient.mk _ v, (localReg6a_mem_sElemCls _ _ _).2 ⟨v, ?_, ?_, rfl⟩, rfl⟩
    · intro a h
      exact hw (ext a) (by rw [← hvl]; exact h)
    · rw [hk, localReg6a_halfPat_map] at hel
      exact hel
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨v, hv, hel, rfl⟩ := (localReg6a_mem_sElemCls _ _ _).1 hc'
    refine ⟨vm v, ?_, ?_, rfl⟩
    · intro a' h
      obtain ⟨a, rfl⟩ := hext a'
      exact hv a (by show s (vm (Sum.inl a)) (vm v); rw [hvl]; exact h)
    · rw [hk, localReg6a_halfPat_map]
      exact hel

/-- **Target 2b**: the exact pullback through a surjective vertex map sending the external vertices onto the external
vertices. -/
theorem LGraph.scost_relabel (Δ : LGraph E I) (ext : E → E') (hext : Function.Surjective ext)
    (vm : E ⊕ I → E' ⊕ I') (hvm : Function.Surjective vm) (hvl : ∀ a : E, vm (Sum.inl a) = Sum.inl (ext a))
    (s : Setoid (E' ⊕ I')) : LGraph.scost (Δ.relabel vm) s = LGraph.scost Δ (Setoid.comap vm s) := by
  classical
  unfold LGraph.scost
  rw [localReg6a_skept_relabel, List.length_map, localReg6a_sIntCls_relabel Δ ext hext vm hvm hvl s,
    localReg6a_sElemCls_relabel Δ ext hext vm hvm hvl s,
    Finset.card_image_of_injective _ (localReg6a_qmap_injective vm s),
    Finset.card_image_of_injective _ (localReg6a_qmap_injective vm s)]
  simp [LGraph.relabel]

end Relabel

/-! ## 4. Target 3 (Lemma A) and target 4 (Lemma B) -/

section LemmaAB

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem localReg6a_sElemCls_congr (Γ Γ' : LGraph E I) (s : Setoid (E ⊕ I)) (hk : Γ.skept s = Γ'.skept s) :
    Γ.sElemCls s = Γ'.sElemCls s := by
  unfold LGraph.sElemCls
  rw [hk]

/-- the cost depends on the graph only through its kept edges and the number of its waved edges -/
theorem localReg6a_scost_congr (Γ Γ' : LGraph E I) (s : Setoid (E ⊕ I)) (hk : Γ.skept s = Γ'.skept s)
    (hW : Γ.waved.length = Γ'.waved.length) : Γ.scost s = Γ'.scost s := by
  unfold LGraph.scost
  rw [hk, hW, localReg6a_sElemCls_congr Γ Γ' s hk]
  rfl

open Classical in
/-- **Target 3, Lemma A**: adding a circled loop never lowers the cost. -/
theorem LGraph.scost_cons_loop_ge (Γ : LGraph E I) (e : SEdge (E ⊕ I)) (he : e.src = e.dst)
    (hc : e.circ = true) (s : Setoid (E ⊕ I)) :
    Γ.scost s ≤ ({ Γ with solid := e :: Γ.solid } : LGraph E I).scost s := by
  set Γ' : LGraph E I := { Γ with solid := e :: Γ.solid } with hΓ'
  have hk : Γ'.skept s = e :: Γ.skept s := by
    simp [LGraph.skept, hΓ', List.filter_cons, hc]
  have hsub : (Γ.sElemCls s).erase (Quotient.mk s e.src) ⊆ Γ'.sElemCls s := by
    intro c hc'
    rw [Finset.mem_erase] at hc'
    obtain ⟨hne, hc'⟩ := hc'
    obtain ⟨v, hv, hel, rfl⟩ := (localReg6a_mem_sElemCls Γ s c).1 hc'
    refine (localReg6a_mem_sElemCls Γ' s _).2 ⟨v, hv, ?_, rfl⟩
    rw [hk, localReg6a_halfPat_cons_loop e _ _ he ?_]
    · exact hel
    · intro h
      exact hne (Quotient.sound (s.symm h))
  have hcard := Finset.pred_card_le_card_erase (s := Γ.sElemCls s) (a := Quotient.mk s e.src)
  have h2 := Finset.card_le_card hsub
  have hI : Γ'.sIntCls s = Γ.sIntCls s := rfl
  unfold LGraph.scost
  rw [hk, hI]
  have hW : Γ'.waved.length = Γ.waved.length := rfl
  rw [hW]
  simp only [List.length_cons]
  push_cast
  omega

open Classical in
/-- an uncircled loop is never kept -/
theorem localReg6a_scost_drop (Γ0 : LGraph E I) (s : Setoid (E ⊕ I)) (b es : List (SEdge (E ⊕ I)))
    (e : SEdge (E ⊕ I)) (h1 : e.src = e.dst) (h2 : e.circ = false) :
    ({ Γ0 with solid := b ++ e :: es } : LGraph E I).scost s = ({ Γ0 with solid := b ++ es } : LGraph E I).scost s := by
  refine localReg6a_scost_congr _ _ s ?_ rfl
  simp [LGraph.skept, List.filter_append, List.filter_cons, h2, h1, Setoid.refl']

/-- the auxiliary form of target 4a with a prefix `b` -/
theorem localReg6a_split_aux (Γ0 : LGraph E I) (s : Setoid (E ⊕ I)) {es es' : List (SEdge (E ⊕ I))} {d : ℕ}
    (h : lvl1Split es es' d) : ∀ b : List (SEdge (E ⊕ I)),
      ({ Γ0 with solid := b ++ es } : LGraph E I).scost s ≤ ({ Γ0 with solid := b ++ es' } : LGraph E I).scost s := by
  induction h with
  | nil => intro b; exact le_rfl
  | keep e hne h ih =>
    intro b
    have := ih (b ++ [e])
    simpa [List.append_assoc] using this
  | @circ e es0 es0' d0 h1 h2 h ih =>
    intro b
    rw [localReg6a_scost_drop Γ0 s b es0 e h1 h2]
    refine (ih b).trans ?_
    have hA := LGraph.scost_cons_loop_ge ({ Γ0 with solid := b ++ es0' } : LGraph E I) { e with circ := true } h1 rfl s
    refine hA.trans (le_of_eq (LGraph.scost_perm _ _ ?_ ?_ s))
    · exact List.perm_middle.symm
    · rfl
  | @drop e es0 es0' d0 h1 h2 h ih =>
    intro b
    rw [localReg6a_scost_drop Γ0 s b es0 e h1 h2]
    exact ih b

/-- **Target 4a**: the weight split of the partition (circle or drop uncircled loops) never lowers the cost. -/
theorem LGraph.scost_le_of_lvl1Split (Γ Γ' : LGraph E I) (d : ℕ) (hS : lvl1Split Γ.solid Γ'.solid d)
    (hW : Γ'.waved.length = Γ.waved.length) (s : Setoid (E ⊕ I)) : Γ.scost s ≤ Γ'.scost s := by
  have h := localReg6a_split_aux Γ s hS []
  simp only [List.nil_append] at h
  calc Γ.scost s = ({ Γ with solid := Γ.solid } : LGraph E I).scost s := rfl
    _ ≤ ({ Γ with solid := Γ'.solid } : LGraph E I).scost s := h
    _ = Γ'.scost s := LGraph.scost_perm ({ Γ with solid := Γ'.solid } : LGraph E I) Γ' (List.Perm.refl _) hW.symm s

/-- **Target 4b, Lemma B**: every term `P` of the dotted edge partition of `Δ` has a vertex map `vm` (externals to
externals) along which every setoid on `P` pulls back at no higher cost. -/
theorem LGraph.scost_partition_ge (m : ℂ) (Δ : LGraph E I) (P : PGraph E) (hP : P ∈ Δ.partition m) :
    ∃ vm : E ⊕ I → P.E' ⊕ P.I', (∀ a : E, vm (Sum.inl a) = Sum.inl (P.ext a)) ∧
      ∀ s : Setoid (P.E' ⊕ P.I'), LGraph.scost Δ (Setoid.comap vm s) ≤ LGraph.scost P.g s := by
  obtain ⟨vm, d, hsurj, hext, -, -, hw, hsplit⟩ := lvl1_part_struct m Δ P hP
  refine ⟨vm, hext, fun s => ?_⟩
  rw [← LGraph.scost_relabel Δ P.ext P.ext_surj vm hsurj hext s]
  exact LGraph.scost_le_of_lvl1Split (Δ.relabel vm) P.g d hsplit (by rw [hw]; rfl) s

end LemmaAB

/-! ## 5. Target 5: the final step -/

section FinalStep

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the quotient map of the trivial setoid is injective -/
theorem localReg6a_mk_bot_injective (V : Type) : Function.Injective (Quotient.mk (⊥ : Setoid V)) := by
  intro a b h
  exact Quotient.exact h

open Classical in
theorem localReg6a_sIntCls_bot_card (Γ : LGraph E I) : (Γ.sIntCls ⊥).card = Fintype.card I := by
  unfold LGraph.sIntCls
  rw [Finset.card_image_of_injective _ (localReg6a_mk_bot_injective _)]
  have : (Finset.univ.filter fun v : E ⊕ I => ∀ a : E, ¬ (⊥ : Setoid (E ⊕ I)) (Sum.inl a) v) =
      (Finset.univ : Finset I).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext v
    cases v with
    | inl a => simp
    | inr i => simp
  rw [this, Finset.card_map, Finset.card_univ]

open Classical in
theorem localReg6a_sElemCls_bot_card (Γ : LGraph E I) (hk : Γ.skept ⊥ = Γ.solid) :
    (Γ.sElemCls ⊥).card = Γ.nElem := by
  unfold LGraph.sElemCls LGraph.nElem
  rw [Finset.card_image_of_injective _ (localReg6a_mk_bot_injective _)]
  have : (Finset.univ.filter fun v : E ⊕ I => (∀ a : E, ¬ (⊥ : Setoid (E ⊕ I)) (Sum.inl a) v) ∧
        lwElem (lwHalfPat (Γ.skept ⊥) (fun w => (⊥ : Setoid (E ⊕ I)) w v)) = true) =
      (Finset.univ.filter fun i : I => lwElem (LGraph.halfPat Γ (Sum.inr i)) = true).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext v
    cases v with
    | inl a => simp
    | inr i =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk,
        Sum.inr.injEq, exists_eq_right]
      have hp : lwHalfPat (Γ.skept ⊥) (fun w => (⊥ : Setoid (E ⊕ I)) w (Sum.inr i)) = LGraph.halfPat Γ (Sum.inr i) := by
        rw [hk]
        exact localReg6a_halfPat_congr _ (fun w => Iff.rfl)
      rw [hp]
      simp
  rw [this, Finset.card_map]

open Classical in
/-- **Target 5a**: the trivial setoid gives `ord + #elem` on a normal graph. -/
theorem LGraph.scost_bot (Γ : LGraph E I) (hN : Γ.Normal) :
    LGraph.scost Γ ⊥ = ord Γ.counters + (LGraph.nElem Γ : ℤ) := by
  have hk : Γ.skept ⊥ = Γ.solid := by
    unfold LGraph.skept
    rw [List.filter_eq_self]
    intro e he
    by_cases h : e.src = e.dst
    · simp [hN.2.2 e he h]
    · simp [h]
  unfold LGraph.scost
  rw [hk, localReg6a_sIntCls_bot_card, localReg6a_sElemCls_bot_card Γ hk]
  simp only [ord, LGraph.counters, LGraph.nS, LGraph.nW, LGraph.nV]

/-- `countP` of a predicate that is the sum of two predicates (as `0/1` values) on the list -/
theorem localReg6a_countP_add {α : Type*} (p q r : α → Bool) (l : List α)
    (h : ∀ a ∈ l, (p a).toNat + (q a).toNat = (r a).toNat) : l.countP p + l.countP q = l.countP r := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;> simp [hp, hq, hr] at ha ⊢ <;> omega

/-- without loops, `b-in + b-out` at `v` is the number of blue edges at `v` -/
theorem localReg6a_halfPat_blue {V : Type} [DecidableEq V] (es : List (SEdge V)) (v : V)
    (hn : ∀ e ∈ es, e.src ≠ e.dst) :
    (lwHalfPat es (· = v)).1 + (lwHalfPat es (· = v)).2.1 =
      (es.filter fun e => e.lvl1IncAt v).countP SEdge.σ := by
  rw [List.countP_filter]
  refine localReg6a_countP_add _ _ _ es fun e he => ?_
  have h0 := hn e he
  by_cases h1 : e.dst = v <;> by_cases h2 : e.src = v <;> by_cases h3 : e.σ <;>
    simp_all [SEdge.lvl1IncAt]

/-- without loops, `r-in + r-out` at `v` is the number of red edges at `v` -/
theorem localReg6a_halfPat_red {V : Type} [DecidableEq V] (es : List (SEdge V)) (v : V)
    (hn : ∀ e ∈ es, e.src ≠ e.dst) :
    (lwHalfPat es (· = v)).2.2.1 + (lwHalfPat es (· = v)).2.2.2 =
      (es.filter fun e => e.lvl1IncAt v).countP (fun e => !e.σ) := by
  rw [List.countP_filter]
  refine localReg6a_countP_add _ _ _ es fun e he => ?_
  have h0 := hn e he
  by_cases h1 : e.dst = v <;> by_cases h2 : e.src = v <;> by_cases h3 : e.σ <;>
    simp_all [SEdge.lvl1IncAt]

theorem localReg6a_count_of_map {V : Type} (l : List (SEdge V))
    (h : l.map SEdge.σ = [true, false] ∨ l.map SEdge.σ = [false, true]) :
    l.countP SEdge.σ = 1 ∧ l.countP (fun e => !e.σ) = 1 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at h
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · simp at h

/-- **Target 5b**: a locally standard graph has no elementary internal vertex. -/
theorem LGraph.nElem_eq_zero_of_locStd (Γ : LGraph E I) (hL : Γ.LocStd) : Γ.nElem = 0 := by
  obtain ⟨-, hnl, hi⟩ := hL
  unfold LGraph.nElem
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hel
  have hb := localReg6a_halfPat_blue Γ.solid (Sum.inr i) hnl
  have hr := localReg6a_halfPat_red Γ.solid (Sum.inr i) hnl
  have hdef : LGraph.halfPat Γ (Sum.inr i) = lwHalfPat Γ.solid (· = Sum.inr i) := rfl
  rw [hdef] at hel
  have hel' : lwHalfPat Γ.solid (· = Sum.inr i) = (1, 1, 0, 0) ∨ lwHalfPat Γ.solid (· = Sum.inr i) = (0, 0, 1, 1) := by
    simpa [lwElem] using hel
  have hsolid : (Γ.solid.filter fun e => e.lvl1IncAt (Sum.inr i)) = Γ.lvl1SolidAt (Sum.inr i) := rfl
  rw [hsolid] at hb hr
  rcases hi i with hstd | hdeg
  · obtain ⟨hmap, -⟩ := hstd
    obtain ⟨c1, c2⟩ := localReg6a_count_of_map _ hmap
    rw [c1] at hb
    rw [c2] at hr
    rcases hel' with h | h <;> rw [h] at hb hr <;> simp at hb hr
  · have hnil : Γ.lvl1SolidAt (Sum.inr i) = [] := List.length_eq_zero_iff.1 hdeg
    rw [hnil] at hb hr
    rcases hel' with h | h <;> rw [h] at hb hr <;> simp at hb hr

end FinalStep

section FinalStepP

/-- **Target 5c**: a lower bound for every merge is a lower bound for the scaling order of a locally standard graph. -/
theorem locReg6_of_locCostGe {Q : PGraph (Fin 2)} {k : ℤ} (hQ : Q.LocStd) (h : Q.LocCostGe false k) :
    k ≤ Q.g.scalingOrder := by
  have hQ' : Q.g.LocStd := hQ
  have h1 := h ⊥ (fun hf => absurd hf (by decide))
  rw [LGraph.scost_bot Q.g hQ'.1, LGraph.nElem_eq_zero_of_locStd Q.g hQ'] at h1
  simpa [LGraph.scalingOrder] using h1

/-- **Target 5d**: the far form (`Q.ext 0 ≠ Q.ext 1`, so that the trivial setoid separates `x` and `y`). -/
theorem locReg6far_of_locCostGe {Q : PGraph (Fin 2)} {k : ℤ} (hQ : Q.LocStd) (hxy : Q.ext 0 ≠ Q.ext 1)
    (h : Q.LocCostGe true k) : k ≤ Q.g.scalingOrder := by
  have hQ' : Q.g.LocStd := hQ
  have h1 := h ⊥ (fun _ hb => by
    have hb' : (Sum.inl (Q.ext 0) : Q.E' ⊕ Q.I') = Sum.inl (Q.ext 1) := hb
    exact hxy (Sum.inl.inj hb'))
  rw [LGraph.scost_bot Q.g hQ'.1, LGraph.nElem_eq_zero_of_locStd Q.g hQ'] at h1
  simpa [LGraph.scalingOrder] using h1

end FinalStepP

/-! ## 6. Target 6: the initial values -/

section Counting

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- **The class count** (F §5 (c)): if every singleton internal class is elementary, then `2 #intCls ≤ #elemCls + #S`, `S`
the set of vertices of internal classes (each internal class `K` has `2 - [K elementary] ≤ |K|`). -/
theorem localReg6a_two_intCls_le (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (S : Finset (E ⊕ I))
    (hS : ∀ v, v ∈ S ↔ ∀ a : E, ¬ s (Sum.inl a) v)
    (hsing : ∀ v : E ⊕ I, (∀ a : E, ¬ s (Sum.inl a) v) → (∀ w, s w v → w = v) →
      lwElem (lwHalfPat (Γ.skept s) (fun w => s w v)) = true) :
    2 * (Γ.sIntCls s).card ≤ (Γ.sElemCls s).card + S.card := by
  have hImg : Γ.sIntCls s = S.image (Quotient.mk s) := by
    ext c
    rw [localReg6a_mem_sIntCls, Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (hS v).2 hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (hS v).1 hv, rfl⟩
  have hcard := Finset.card_eq_sum_card_image (Quotient.mk s) S
  have hcls : ∀ c ∈ Γ.sIntCls s,
      2 ≤ (if c ∈ Γ.sElemCls s then 1 else 0) + (S.filter fun v => Quotient.mk s v = c).card := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := (localReg6a_mem_sIntCls Γ s c).1 hc
    have hvS : v ∈ S.filter fun v' => Quotient.mk s v' = Quotient.mk s v := by
      exact Finset.mem_filter.2 ⟨(hS v).2 hv, rfl⟩
    have h1 : 1 ≤ (S.filter fun v' => Quotient.mk s v' = Quotient.mk s v).card :=
      Finset.card_pos.2 ⟨v, hvS⟩
    by_cases hel : Quotient.mk s v ∈ Γ.sElemCls s
    · simp only [hel, ↓reduceIte]
      omega
    · simp only [hel, ↓reduceIte, zero_add]
      by_contra hlt
      have h2 : (S.filter fun v' => Quotient.mk s v' = Quotient.mk s v).card ≤ 1 := by omega
      have hs1 : ∀ w, s w v → w = v := by
        intro w hw
        have hwS : w ∈ S.filter fun v' => Quotient.mk s v' = Quotient.mk s v := by
          exact Finset.mem_filter.2 ⟨(hS w).2 (fun a ha => hv a (s.trans ha hw)), Quotient.sound hw⟩
        exact Finset.card_le_one.1 h2 w hwS v hvS
      exact hel ((localReg6a_mem_sElemCls Γ s _).2 ⟨v, hv, hsing v hv hs1, rfl⟩)
  have hel_sum : ∑ c ∈ Γ.sIntCls s, (if c ∈ Γ.sElemCls s then 1 else 0) = (Γ.sElemCls s).card := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (localReg6a_sElemCls_subset Γ s)]
    simp
  calc 2 * (Γ.sIntCls s).card = ∑ c ∈ Γ.sIntCls s, 2 := by simp [mul_comm]
    _ ≤ ∑ c ∈ Γ.sIntCls s, ((if c ∈ Γ.sElemCls s then 1 else 0) + (S.filter fun v => Quotient.mk s v = c).card) :=
        Finset.sum_le_sum hcls
    _ = (Γ.sElemCls s).card + S.card := by
        rw [Finset.sum_add_distrib, hel_sum, hcard, hImg]

open Classical in
/-- in a singleton class `{v}` of a graph without uncircled loops the kept edges at `v` are all the edges at `v` -/
theorem localReg6a_halfPat_skept_singleton (Γ : LGraph E I) (s : Setoid (E ⊕ I))
    (hnl : ∀ e ∈ Γ.solid, e.src = e.dst → e.circ = true) (v : E ⊕ I) (hs : ∀ w, s w v → w = v) :
    lwHalfPat (Γ.skept s) (fun w => s w v) = Γ.halfPat v := by
  have hK : ∀ w, s w v ↔ w = v := fun w => ⟨hs w, fun h => h ▸ s.refl' _⟩
  rw [localReg6a_halfPat_congr _ hK]
  have hk : ∀ e ∈ Γ.solid, (e.src = v ∨ e.dst = v) → (e.circ || !decide (s e.src e.dst)) = true := by
    intro e he hev
    by_cases hc : e.circ = true
    · simp [hc]
    · have hc' : e.circ = false := by simpa using hc
      have hns : ¬ s e.src e.dst := by
        intro h
        have hl : e.src = e.dst := by
          rcases hev with h1 | h1
          · exact h1.trans (hs _ (h1 ▸ s.symm h)).symm
          · exact hs _ (h1 ▸ h) |>.trans h1.symm
        exact hc (hnl e he hl)
      simp [hc', hns]
  unfold LGraph.skept lwHalfPat LGraph.halfPat lwHalfPat
  simp only [List.countP_filter]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> refine List.countP_congr fun e he => ?_ <;>
    simp only [Bool.and_eq_true, decide_eq_true_eq] <;>
    exact ⟨fun h => h.1, fun h => ⟨h, hk e he (by tauto)⟩⟩

end Counting

section FxyPattern

/-- the pattern is additive on `flatMap` -/
theorem localReg6a_halfPat_flatMap {α V : Type*} (l : List α) (f : α → List (SEdge V)) (K : V → Prop)
    [DecidablePred K] : lwHalfPat (l.flatMap f) K = (l.map fun a => lwHalfPat (f a) K).sum := by
  induction l with
  | nil => simp [lwHalfPat]
  | cons a t ih => rw [List.flatMap_cons, localReg6a_halfPat_append, ih]; simp

/-- the pattern of the block `k` of the starting graph at `α_i` -/
theorem localReg6a_fxy_blockPat_alpha (p : ℕ) (k i : Fin p) :
    lwHalfPat (localReg_fxyBlock p k) (fun w => w = (Sum.inr (localReg_fxyAlpha i) : Fin 2 ⊕ Fin (2 * p))) =
      if k = i then ((decide (k.1 < p / 2)).toNat, (decide (k.1 < p / 2)).toNat, (!decide (k.1 < p / 2)).toNat,
        (!decide (k.1 < p / 2)).toNat) else 0 := by
  have h1 : localReg_fxyBeta k ≠ localReg_fxyAlpha i := (localReg_fxyAlpha_ne_beta i k).symm
  by_cases h : k = i
  · subst h
    simp only [lwHalfPat, localReg_fxyBlock, List.countP_cons, h1]
    by_cases hlt : (k : ℕ) < p / 2 <;> simp [hlt, h1]
  · have h2 : localReg_fxyAlpha k ≠ localReg_fxyAlpha i := fun he => h (localReg_fxyAlpha_inj he)
    simp [lwHalfPat, localReg_fxyBlock, List.countP_cons, h1, h2, h]

/-- the pattern of the block `k` of the starting graph at `β_i` -/
theorem localReg6a_fxy_blockPat_beta (p : ℕ) (k i : Fin p) :
    lwHalfPat (localReg_fxyBlock p k) (fun w => w = (Sum.inr (localReg_fxyBeta i) : Fin 2 ⊕ Fin (2 * p))) =
      if k = i then ((decide (k.1 < p / 2)).toNat, (decide (k.1 < p / 2)).toNat, (!decide (k.1 < p / 2)).toNat,
        (!decide (k.1 < p / 2)).toNat) else 0 := by
  have h1 : localReg_fxyAlpha k ≠ localReg_fxyBeta i := localReg_fxyAlpha_ne_beta k i
  by_cases h : k = i
  · subst h
    simp only [lwHalfPat, localReg_fxyBlock, List.countP_cons, h1]
    by_cases hlt : (k : ℕ) < p / 2 <;> simp [hlt, h1]
  · have h2 : localReg_fxyBeta k ≠ localReg_fxyBeta i := fun he => h (localReg_fxyBeta_inj he)
    simp [lwHalfPat, localReg_fxyBlock, List.countP_cons, h1, h2, h]

/-- every internal vertex of the starting graph has an elementary pattern: `α_i` (`{σ-in, σ-out}`, the two edges of the
block) and `β_i` (the light-weight) -/
theorem localReg6a_fxy_elem (p : ℕ) (j : Fin (2 * p)) :
    lwElem ((fxyPowGraph p).halfPat (Sum.inr j)) = true := by
  obtain ⟨i, hj⟩ : ∃ i : Fin p, j = localReg_fxyAlpha i ∨ j = localReg_fxyBeta i := by
    rcases Nat.even_or_odd' j.1 with ⟨k, hk | hk⟩
    · exact ⟨⟨k, by omega⟩, Or.inl (Fin.ext (by simp [localReg_fxyAlpha]; omega))⟩
    · exact ⟨⟨k, by omega⟩, Or.inr (Fin.ext (by simp [localReg_fxyBeta]; omega))⟩
  have hsolid : (fxyPowGraph p).solid = (List.finRange p).flatMap (localReg_fxyBlock p) := rfl
  unfold LGraph.halfPat
  rw [hsolid, localReg6a_halfPat_flatMap, ← Fin.sum_univ_def]
  rcases hj with rfl | rfl
  · simp only [localReg6a_fxy_blockPat_alpha, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases decide (i.1 < p / 2) <;> decide
  · simp only [localReg6a_fxy_blockPat_beta, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases decide (i.1 < p / 2) <;> decide

end FxyPattern

section FxyCost

open Classical in
/-- the number of dropped edges `x → α_i`, `α_i → y` of the block `i` (those inside a class of `s`) -/
def localReg6a_drop {p : ℕ} (s : Setoid (Fin 2 ⊕ Fin (2 * p))) (i : Fin p) : ℕ :=
  (if s (Sum.inl 0) (Sum.inr (localReg_fxyAlpha i)) then 1 else 0) +
    (if s (Sum.inr (localReg_fxyAlpha i)) (Sum.inl 1) then 1 else 0)

open Classical in
/-- `1` if `α_i` lies in an internal class of `s` -/
def localReg6a_intA {p : ℕ} (s : Setoid (Fin 2 ⊕ Fin (2 * p))) (i : Fin p) : ℕ :=
  if ∀ a : Fin 2, ¬ s (Sum.inl a) (Sum.inr (localReg_fxyAlpha i)) then 1 else 0

open Classical in
/-- `1` if `β_i` lies in an internal class of `s` -/
def localReg6a_intB {p : ℕ} (s : Setoid (Fin 2 ⊕ Fin (2 * p))) (i : Fin p) : ℕ :=
  if ∀ a : Fin 2, ¬ s (Sum.inl a) (Sum.inr (localReg_fxyBeta i)) then 1 else 0

/-- a sum over `Fin (2 p)` is the sum over the blocks of the values at `α_i` and `β_i` -/
theorem localReg6a_sum_fin2 {M : Type*} [AddCommMonoid M] (p : ℕ) (f : Fin (2 * p) → M) :
    ∑ j, f j = ∑ i : Fin p, (f (localReg_fxyAlpha i) + f (localReg_fxyBeta i)) := by
  rw [Finset.sum_add_distrib]
  have hA : (Finset.univ.image (localReg_fxyAlpha (p := p)) ∪ Finset.univ.image (localReg_fxyBeta (p := p)) :
      Finset (Fin (2 * p))) = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    rcases Nat.even_or_odd' j.1 with ⟨k, hk | hk⟩
    · exact Or.inl ⟨⟨k, by omega⟩, Fin.ext (by simp [localReg_fxyAlpha]; omega)⟩
    · exact Or.inr ⟨⟨k, by omega⟩, Fin.ext (by simp [localReg_fxyBeta]; omega)⟩
  have hD : Disjoint (Finset.univ.image (localReg_fxyAlpha (p := p))) (Finset.univ.image (localReg_fxyBeta (p := p))) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj hj'
    obtain ⟨i, rfl⟩ := hj
    obtain ⟨k, hk⟩ := hj'
    exact localReg_fxyAlpha_ne_beta i k hk.symm
  rw [← Finset.sum_image (f := f) (g := localReg_fxyAlpha) (fun i _ k _ h => localReg_fxyAlpha_inj h),
    ← Finset.sum_image (f := f) (g := localReg_fxyBeta) (fun i _ k _ h => localReg_fxyBeta_inj h),
    ← Finset.sum_union hD, hA]

open Classical in
/-- the kept edges of the block `i`: three, minus the dropped ones -/
theorem localReg6a_fxy_block_length {p : ℕ} (s : Setoid (Fin 2 ⊕ Fin (2 * p))) (i : Fin p) :
    ((localReg_fxyBlock p i).filter fun e => e.circ || !decide (s e.src e.dst)).length +
      localReg6a_drop s i = 3 := by
  simp only [localReg_fxyBlock, localReg6a_drop, List.filter_cons]
  by_cases h1 : s (Sum.inl 0) (Sum.inr (localReg_fxyAlpha i)) <;>
    by_cases h2 : s (Sum.inr (localReg_fxyAlpha i)) (Sum.inl 1) <;> simp [h1, h2]

open Classical in
/-- `#kept(Γ_p, s) + (number of dropped edges) = 3p` -/
theorem localReg6a_fxy_skept_length (p : ℕ) (s : Setoid (Fin 2 ⊕ Fin (2 * p))) :
    ((fxyPowGraph p).skept s).length + ∑ i : Fin p, localReg6a_drop s i = 3 * p := by
  have h : ((fxyPowGraph p).skept s).length = ∑ i : Fin p,
      ((localReg_fxyBlock p i).filter fun e => e.circ || !decide (s e.src e.dst)).length := by
    unfold LGraph.skept
    show (((List.finRange p).flatMap (localReg_fxyBlock p)).filter _).length = _
    rw [List.filter_flatMap, List.length_flatMap, Fin.sum_univ_def]
  rw [h, ← Finset.sum_add_distrib]
  calc ∑ i, (_ + _) = ∑ i : Fin p, 3 := Finset.sum_congr rfl (fun i _ => localReg6a_fxy_block_length s i)
    _ = 3 * p := by simp [mul_comm]

/-- the vertices of internal classes, counted block by block -/
theorem localReg6a_fxy_card_filter (p : ℕ) (P : Fin 2 ⊕ Fin (2 * p) → Prop) (instP : DecidablePred P)
    (hP : ∀ a : Fin 2, ¬ P (Sum.inl a)) :
    (Finset.univ.filter P).card = ∑ i : Fin p, (if P (Sum.inr (localReg_fxyAlpha i)) then 1 else 0) +
      ∑ i : Fin p, (if P (Sum.inr (localReg_fxyBeta i)) then 1 else 0) := by
  rw [Finset.card_filter, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  have h0 : ∑ a : Fin 2, (if P (Sum.inl a) then 1 else 0) = 0 := by
    simp [hP]
  rw [h0, zero_add, localReg6a_sum_fin2 p (fun j => if P (Sum.inr j) then 1 else 0)]

open Classical in
/-- the per-block inequality: the dropped edges and the vertices of internal classes of the block `i` are at most `3`
(`2` if `s` separates `x` and `y`) -/
theorem localReg6a_fxy_block_ineq {p : ℕ} (s : Setoid (Fin 2 ⊕ Fin (2 * p))) (i : Fin p) :
    localReg6a_drop s i + (localReg6a_intA s i + localReg6a_intB s i) ≤ 3 ∧
      (¬ s (Sum.inl 0) (Sum.inl 1) → localReg6a_drop s i + (localReg6a_intA s i + localReg6a_intB s i) ≤ 2) := by
  have hA23 : s (Sum.inr (localReg_fxyAlpha i)) (Sum.inl 1) ↔ s (Sum.inl 1) (Sum.inr (localReg_fxyAlpha i)) :=
    ⟨fun h => s.symm h, fun h => s.symm h⟩
  have htr : s (Sum.inl 0) (Sum.inr (localReg_fxyAlpha i)) → s (Sum.inl 1) (Sum.inr (localReg_fxyAlpha i)) →
      s (Sum.inl 0) (Sum.inl 1) := fun h h' => s.trans h (s.symm h')
  simp only [localReg6a_drop, localReg6a_intA, localReg6a_intB, Fin.forall_fin_two, hA23]
  refine ⟨?_, fun hfar => ?_⟩
  · by_cases a1 : s (Sum.inl 0) (Sum.inr (localReg_fxyAlpha i)) <;>
      by_cases a3 : s (Sum.inl 1) (Sum.inr (localReg_fxyAlpha i)) <;>
      by_cases b1 : s (Sum.inl 0) (Sum.inr (localReg_fxyBeta i)) <;>
      by_cases b2 : s (Sum.inl 1) (Sum.inr (localReg_fxyBeta i)) <;>
      simp [a1, a3, b1, b2]
  · by_cases a1 : s (Sum.inl 0) (Sum.inr (localReg_fxyAlpha i)) <;>
      by_cases a3 : s (Sum.inl 1) (Sum.inr (localReg_fxyAlpha i)) <;>
      by_cases b1 : s (Sum.inl 0) (Sum.inr (localReg_fxyBeta i)) <;>
      by_cases b2 : s (Sum.inl 1) (Sum.inr (localReg_fxyBeta i)) <;>
      first | exact absurd (htr a1 a3) hfar | simp [a1, a3, b1, b2]

open Classical in
/-- **The lower bound** (F §5 (a)-(d)): `scost(Γ_p, s) + Σ_i (dropped_i + internal_i) ≥ 5p` for every setoid `s`. -/
theorem localReg6a_fxy_scost_ge (p : ℕ) (s : Setoid (Fin 2 ⊕ Fin (2 * p))) :
    (5 * p : ℤ) ≤ (fxyPowGraph p).scost s +
      ∑ i : Fin p, ((localReg6a_drop s i + (localReg6a_intA s i + localReg6a_intB s i) : ℕ) : ℤ) := by
  have hnl := (fxyPowGraph_normal p).2.2
  have hsing : ∀ v : Fin 2 ⊕ Fin (2 * p), (∀ a : Fin 2, ¬ s (Sum.inl a) v) → (∀ w, s w v → w = v) →
      lwElem (lwHalfPat ((fxyPowGraph p).skept s) (fun w => s w v)) = true := by
    intro v hv hs
    rw [localReg6a_halfPat_skept_singleton _ s hnl v hs]
    rcases v with a | j
    · exact absurd (s.refl' _) (hv a)
    · exact localReg6a_fxy_elem p j
  set P : Fin 2 ⊕ Fin (2 * p) → Prop := fun v => ∀ a : Fin 2, ¬ s (Sum.inl a) v with hP
  set S : Finset (Fin 2 ⊕ Fin (2 * p)) := Finset.univ.filter P with hSdef
  have hS : ∀ v, v ∈ S ↔ ∀ a : Fin 2, ¬ s (Sum.inl a) v := fun v => by simp [hSdef, hP]
  have h2 := localReg6a_two_intCls_le (fxyPowGraph p) s S hS hsing
  have h3 := localReg6a_fxy_skept_length p s
  have h4 : S.card = ∑ i : Fin p, localReg6a_intA s i + ∑ i : Fin p, localReg6a_intB s i := by
    rw [hSdef, localReg6a_fxy_card_filter p P _ (fun a h => h a (s.refl' _))]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => if_congr Iff.rfl rfl rfl)
      (Finset.sum_congr rfl fun i _ => if_congr Iff.rfl rfl rfl)
  have hW : (fxyPowGraph p).waved.length = p := by simp [fxyPowGraph]
  have h5 : ∑ i : Fin p, ((localReg6a_drop s i + (localReg6a_intA s i + localReg6a_intB s i) : ℕ) : ℤ) =
      ((∑ i : Fin p, localReg6a_drop s i : ℕ) : ℤ) + ((∑ i : Fin p, localReg6a_intA s i : ℕ) : ℤ) +
        ((∑ i : Fin p, localReg6a_intB s i : ℕ) : ℤ) := by
    push_cast
    simp only [Finset.sum_add_distrib]
    ring
  unfold LGraph.scost
  rw [hW, h5]
  omega

/-- **Target 6a**: `Φ^all(Γ_p) ≥ 2p` and `Φ^far(Γ_p) ≥ 3p`. -/
theorem fxyPowGraph_locCostGe (p : ℕ) :
    (fxyPowGraph p).pack.LocCostGe false (2 * (p : ℤ)) ∧ (fxyPowGraph p).pack.LocCostGe true (3 * (p : ℤ)) := by
  have hsum : ∀ (s : Setoid (Fin 2 ⊕ Fin (2 * p))) (c : ℕ), (∀ i : Fin p,
      localReg6a_drop s i + (localReg6a_intA s i + localReg6a_intB s i) ≤ c) →
      ∑ i : Fin p, ((localReg6a_drop s i + (localReg6a_intA s i + localReg6a_intB s i) : ℕ) : ℤ) ≤ (c : ℤ) * p := by
    intro s c h
    calc ∑ i : Fin p, ((localReg6a_drop s i + (localReg6a_intA s i + localReg6a_intB s i) : ℕ) : ℤ)
        ≤ ∑ i : Fin p, (c : ℤ) := Finset.sum_le_sum fun i _ => by exact_mod_cast h i
      _ = (c : ℤ) * p := by simp [mul_comm]
  refine ⟨fun (s : Setoid (Fin 2 ⊕ Fin (2 * p))) _ => ?_, fun (s : Setoid (Fin 2 ⊕ Fin (2 * p))) hs => ?_⟩
  · have h1 := localReg6a_fxy_scost_ge p s
    have h2 := hsum s 3 fun i => (localReg6a_fxy_block_ineq s i).1
    show 2 * (p : ℤ) ≤ (fxyPowGraph p).scost s
    omega
  · have hfar : ¬ s (Sum.inl 0) (Sum.inl 1) := hs rfl
    have h1 := localReg6a_fxy_scost_ge p s
    have h2 := hsum s 2 fun i => (localReg6a_fxy_block_ineq s i).2 hfar
    show 3 * (p : ℤ) ≤ (fxyPowGraph p).scost s
    omega

/-- the starting graph: a solid edge is a loop if and only if it is circled (the light-weights `β_i → β_i`; the edges
`x → α_i`, `α_i → y` are uncircled non-loops) -/
theorem localReg6a_fxy_circIffLoop (p : ℕ) : LGraph.CircIffLoop (fxyPowGraph p) := by
  intro e he
  obtain ⟨i, hi⟩ := (localReg_fxy_mem_solid e).1 he
  simp only [localReg_fxyBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp

/-- **Target 6b**: the starting graph carries the invariant of property (6). -/
theorem fxyPowGraph_locReg6Inv (p : ℕ) : (fxyPowGraph p).pack.LocReg6Inv p :=
  ⟨fxyPowGraph_normal p, localReg6a_fxy_circIffLoop p, (fxyPowGraph_locCostGe p).1, (fxyPowGraph_locCostGe p).2⟩

end FxyCost

/-! ## 7. Compiled instances (CLAUDE.md §4 step 2) -/

section Instances

/-- Instance (1), `scost_perm` at `fxyPowGraph 2` and its reversed solid list (`s = ⊥`). -/
theorem localReg6a_inst_perm : (fxyPowGraph 2).scost ⊥ =
    ({ fxyPowGraph 2 with solid := (fxyPowGraph 2).solid.reverse } : LGraph (Fin 2) (Fin (2 * 2))).scost ⊥ :=
  LGraph.scost_perm (fxyPowGraph 2) { fxyPowGraph 2 with solid := (fxyPowGraph 2).solid.reverse }
    (List.reverse_perm _).symm rfl ⊥

/-- Instance (2), `scost_relabel` at `fxyPowGraph 2`, `ext = id`, `vm = Sum.map id (Equiv.swap 0 1)`. -/
theorem localReg6a_inst_relabel (s : Setoid (Fin 2 ⊕ Fin (2 * 2))) :
    ((fxyPowGraph 2).relabel (Sum.map id (Equiv.swap (0 : Fin (2 * 2)) 1))).scost s =
      (fxyPowGraph 2).scost (Setoid.comap (Sum.map id (Equiv.swap (0 : Fin (2 * 2)) 1)) s) :=
  LGraph.scost_relabel (fxyPowGraph 2) id Function.surjective_id (Sum.map id (Equiv.swap (0 : Fin (2 * 2)) 1))
    (Function.Surjective.sumMap Function.surjective_id (Equiv.swap _ _).surjective) (fun _ => rfl) s

/-- Instance (3), Lemma A at `fxyPowGraph 2` with the circled loop `G̊_{xx}` at `x`, `s = ⊥`. -/
theorem localReg6a_inst_consLoop : (fxyPowGraph 2).scost ⊥ ≤
    ({ fxyPowGraph 2 with solid := (⟨true, true, Sum.inl 0, Sum.inl 0⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) ::
      (fxyPowGraph 2).solid } : LGraph (Fin 2) (Fin (2 * 2))).scost ⊥ :=
  LGraph.scost_cons_loop_ge (fxyPowGraph 2) ⟨true, true, Sum.inl 0, Sum.inl 0⟩ rfl rfl ⊥

/-- the graph on `Fin 2 ⊕ Fin 1` with one uncircled loop `G_{αα}` -/
def localReg6a_instSplit0 : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, false, .inr 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1

/-- the graph on `Fin 2 ⊕ Fin 1` with one circled loop `(G-M)_{αα}` -/
def localReg6a_instSplit1 : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, true, .inr 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1

/-- Instance (4), the weight split `lvl1Split.circ` (the weight is circled). -/
theorem localReg6a_inst_splitCirc (s : Setoid (Fin 2 ⊕ Fin 1)) :
    localReg6a_instSplit0.scost s ≤ localReg6a_instSplit1.scost s :=
  LGraph.scost_le_of_lvl1Split localReg6a_instSplit0 localReg6a_instSplit1 0
    (lvl1Split.circ _ rfl rfl lvl1Split.nil) rfl s

/-- Instance (4), the weight split `lvl1Split.drop` (the weight is dropped). -/
theorem localReg6a_inst_splitDrop (s : Setoid (Fin 2 ⊕ Fin 1)) :
    localReg6a_instSplit0.scost s ≤ ({ localReg6a_instSplit0 with solid := [] } : LGraph (Fin 2) (Fin 1)).scost s :=
  LGraph.scost_le_of_lvl1Split localReg6a_instSplit0 { localReg6a_instSplit0 with solid := [] } 1
    (lvl1Split.drop _ rfl rfl lvl1Split.nil) rfl s

/-- Instance (5), `scost_partition_ge` at the one-term partition of `fxyPowGraph 2`, `m = 1`. -/
theorem localReg6a_inst_partition : ∃ P : PGraph (Fin 2), P ∈ (fxyPowGraph 2).partition 1 ∧
    ∃ vm : Fin 2 ⊕ Fin (2 * 2) → P.E' ⊕ P.I', (∀ a, vm (Sum.inl a) = Sum.inl (P.ext a)) ∧
      ∀ s : Setoid (P.E' ⊕ P.I'), (fxyPowGraph 2).scost (Setoid.comap vm s) ≤ P.g.scost s := by
  obtain ⟨P, hP, -⟩ := LGraph.partition_of_normal 1 (fxyPowGraph 2) (fxyPowGraph_normal 2) (by decide)
  have hmem : P ∈ (fxyPowGraph 2).partition 1 := by rw [hP]; exact List.mem_singleton_self P
  exact ⟨P, hmem, LGraph.scost_partition_ge 1 (fxyPowGraph 2) P hmem⟩

/-- `#elem(Γ_2) = 4` -/
theorem localReg6a_inst_nElem2 : (fxyPowGraph 2).nElem = 4 := by decide +kernel

/-- `#elem(Γ_3) = 6` -/
theorem localReg6a_inst_nElem3 : (fxyPowGraph 3).nElem = 6 := by decide +kernel

/-- Instance (6), `scost_bot` at `p = 2`: `scost(Γ_2, ⊥) = 6 = 3p` (the far bound of target 6 is attained). -/
theorem localReg6a_inst_bot2 : (fxyPowGraph 2).scost ⊥ = 6 := by
  have h1 : ord (fxyPowGraph 2).counters = 2 := by simpa using fxyPowGraph_ord 2
  rw [LGraph.scost_bot _ (fxyPowGraph_normal 2), h1, localReg6a_inst_nElem2]
  norm_num

/-- Instance (6), `scost_bot` at `p = 3`: `scost(Γ_3, ⊥) = 9 = 3p`. -/
theorem localReg6a_inst_bot3 : (fxyPowGraph 3).scost ⊥ = 9 := by
  have h1 : ord (fxyPowGraph 3).counters = 3 := by simpa using fxyPowGraph_ord 3
  rw [LGraph.scost_bot _ (fxyPowGraph_normal 3), h1, localReg6a_inst_nElem3]
  norm_num

/-- Instance (7), `nElem_eq_zero_of_locStd` at the merged locally standard graph `localReg2_inst_Q`. -/
theorem localReg6a_inst_nElemLocStd : localReg2_inst_Q.nElem = 0 := LGraph.nElem_eq_zero_of_locStd _ localReg2_inst_Q_locStd

/-- Instance (8), `fxyPowGraph_locCostGe` at `p = 2` (`4`, `6`). -/
theorem localReg6a_inst_cost2 :
    (fxyPowGraph 2).pack.LocCostGe false 4 ∧ (fxyPowGraph 2).pack.LocCostGe true 6 := by
  have h := fxyPowGraph_locCostGe 2
  norm_num at h
  exact h

/-- Instance (8), `fxyPowGraph_locCostGe` at `p = 3` (`6`, `9`). -/
theorem localReg6a_inst_cost3 :
    (fxyPowGraph 3).pack.LocCostGe false 6 ∧ (fxyPowGraph 3).pack.LocCostGe true 9 := by
  have h := fxyPowGraph_locCostGe 3
  norm_num at h
  exact h

/-- Instance (8), `fxyPowGraph_locReg6Inv` at `p = 2`. -/
theorem localReg6a_inst_inv2 : (fxyPowGraph 2).pack.LocReg6Inv 2 := fxyPowGraph_locReg6Inv 2

/-- Instance (8), `fxyPowGraph_locReg6Inv` at `p = 3`. -/
theorem localReg6a_inst_inv3 : (fxyPowGraph 3).pack.LocReg6Inv 3 := fxyPowGraph_locReg6Inv 3

/-- The graph of instance (9) (the data of the merged `auxGraph_instXY`, copied; `AuxGraph` is not imported): two external
vertices, the solid edges `G_{xy}`, `Ḡ_{xy}`, the coloured waved edge `S⁺_{xy}`, one `×`-dotted edge `x ≠ y`; no internal
vertex, `ord = 4`. -/
def localReg6a_instXY : LGraph (Fin 2) (Fin 0) where
  solid := [⟨true, false, .inl 0, .inl 1⟩, ⟨false, false, .inl 0, .inl 1⟩]
  waved := [⟨true, true, .inl 0, .inl 1⟩]
  dotted := [⟨false, .inl 0, .inl 1⟩]
  coeff := 1

theorem localReg6a_instXY_locStd : localReg6a_instXY.pack.LocStd := by decide

theorem localReg6a_instXY_ord : localReg6a_instXY.pack.g.scalingOrder = 4 := by decide

open Classical in
theorem localReg6a_instXY_sIntCls (s : Setoid (Fin 2 ⊕ Fin 0)) : localReg6a_instXY.sIntCls s = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
  obtain ⟨v, hv, -⟩ := (localReg6a_mem_sIntCls _ s c).1 hc
  rcases v with a | i
  · exact hv a (s.refl' _)
  · exact i.elim0

open Classical in
theorem localReg6a_instXY_sElemCls (s : Setoid (Fin 2 ⊕ Fin 0)) : localReg6a_instXY.sElemCls s = ∅ :=
  Finset.subset_empty.1 (by simpa [localReg6a_instXY_sIntCls] using localReg6a_sElemCls_subset localReg6a_instXY s)

/-- the far bound `Φ^far ≥ 4` at the instance graph (no internal class; both solid edges are kept iff `¬ s x y`) -/
theorem localReg6a_instXY_far : localReg6a_instXY.pack.LocCostGe true 4 := by
  classical
  intro (s : Setoid (Fin 2 ⊕ Fin 0)) hs
  have hs' : ¬ s (Sum.inl 0) (Sum.inl 1) := hs rfl
  have hk : localReg6a_instXY.skept s = localReg6a_instXY.solid := by
    simp [LGraph.skept, localReg6a_instXY, hs']
  show (4 : ℤ) ≤ localReg6a_instXY.scost s
  unfold LGraph.scost
  rw [hk, localReg6a_instXY_sIntCls, localReg6a_instXY_sElemCls]
  simp [localReg6a_instXY]

/-- the all bound `Φ^all ≥ 2` at the instance graph -/
theorem localReg6a_instXY_all : localReg6a_instXY.pack.LocCostGe false 2 := by
  classical
  intro (s : Setoid (Fin 2 ⊕ Fin 0)) _
  show (2 : ℤ) ≤ localReg6a_instXY.scost s
  unfold LGraph.scost
  rw [localReg6a_instXY_sIntCls, localReg6a_instXY_sElemCls]
  simp only [Finset.card_empty, Nat.cast_zero, sub_zero, add_zero]
  have h0 : (0 : ℤ) ≤ ((localReg6a_instXY.skept s).length : ℤ) := Int.natCast_nonneg _
  have hW : localReg6a_instXY.waved.length = 1 := rfl
  rw [hW]
  push_cast
  omega

/-- Instance (9), `locReg6far_of_locCostGe`: `4 ≤ ord` at the instance graph (sharp: `ord = 4`). -/
theorem localReg6a_instXY_far_ord : (4 : ℤ) ≤ localReg6a_instXY.pack.g.scalingOrder :=
  locReg6far_of_locCostGe localReg6a_instXY_locStd (by decide) localReg6a_instXY_far

/-- Instance (9), `locReg6_of_locCostGe`: `2 ≤ ord` at the instance graph. -/
theorem localReg6a_instXY_all_ord : (2 : ℤ) ≤ localReg6a_instXY.pack.g.scalingOrder :=
  locReg6_of_locCostGe localReg6a_instXY_locStd localReg6a_instXY_all

/-! Instance (10): the final step at a locally standard graph with internal vertices.  `localReg2_inst_Q` (merged, `LocalRegular2`) has the
external vertices `x = inl 0`, `y = inl 1`, the internal vertices `α = inr 0`, `β = inr 1` joined by one waved edge, and the solid edges
`G_{xα}`, `Ḡ_{xα}`, `G_{βy}`, `Ḡ_{βy}`; it is locally standard and `ord = 2`. -/

open Classical in
/-- the internal classes of a merge of `localReg2_inst_Q` (`x = inl 0`, `y = inl 1`, `α = inr 0`, `β = inr 1`): the class of
`α` is internal only if `¬ s x α`, that of `β` only if `¬ s β y` -/
theorem localReg6a_instQ_int_card (s : Setoid (Fin 2 ⊕ Fin 2)) :
    (localReg2_inst_Q.sIntCls s).card + (if s (Sum.inl 0) (Sum.inr 0) then (1 : ℕ) else 0) +
      (if s (Sum.inr 1) (Sum.inl 1) then (1 : ℕ) else 0) ≤ 2 := by
  have hsub : localReg2_inst_Q.sIntCls s ⊆ (if s (Sum.inl 0) (Sum.inr 0) then ∅ else {Quotient.mk s (Sum.inr 0)}) ∪
      (if s (Sum.inr 1) (Sum.inl 1) then ∅ else {Quotient.mk s (Sum.inr 1)}) := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := (localReg6a_mem_sIntCls _ s c).1 hc
    rcases v with a | j
    · exact absurd (s.refl' _) (hv a)
    · fin_cases j
      · have h1 : ¬ s (Sum.inl 0) (Sum.inr 0) := hv 0
        simp [h1]
      · have h2 : ¬ s (Sum.inr 1) (Sum.inl 1) := fun h => hv 1 (s.symm h)
        simp [h2]
  have hcard := Finset.card_le_card hsub
  have h2 : ({Quotient.mk s (Sum.inr 0), Quotient.mk s (Sum.inr 1)} : Finset (Quotient s)).card ≤ 2 :=
    Finset.card_le_two
  by_cases h1 : s (Sum.inl 0) (Sum.inr 0) <;> by_cases h2' : s (Sum.inr 1) (Sum.inl 1) <;>
    simp [h1, h2'] at hcard ⊢ <;> omega

open Classical in
/-- the kept edges of `localReg2_inst_Q`: four, minus the two edges `x → α` (resp. `β → y`) if `s x α` (resp. `s β y`) -/
theorem localReg6a_instQ_kept (s : Setoid (Fin 2 ⊕ Fin 2)) :
    (localReg2_inst_Q.skept s).length + 2 * (if s (Sum.inl 0) (Sum.inr 0) then (1 : ℕ) else 0) +
      2 * (if s (Sum.inr 1) (Sum.inl 1) then (1 : ℕ) else 0) = 4 := by
  by_cases h1 : s (Sum.inl 0) (Sum.inr 0) <;> by_cases h2 : s (Sum.inr 1) (Sum.inl 1) <;>
    simp [LGraph.skept, localReg2_inst_Q, List.filter_cons, h1, h2]

open Classical in
/-- the all bound `Φ^all ≥ 2` at the locally standard graph `localReg2_inst_Q` (two internal vertices `α`, `β`, `ord = 2`) -/
theorem localReg6a_instQ_all : localReg2_inst_Q.pack.LocCostGe false 2 := by
  intro (s : Setoid (Fin 2 ⊕ Fin 2)) _
  show (2 : ℤ) ≤ localReg2_inst_Q.scost s
  have hk := localReg6a_instQ_kept s
  have hI := localReg6a_instQ_int_card s
  have hW : localReg2_inst_Q.waved.length = 1 := rfl
  have hE : (0 : ℤ) ≤ (localReg2_inst_Q.sElemCls s).card := Nat.cast_nonneg _
  unfold LGraph.scost
  rw [hW]
  generalize (if s (Sum.inl 0) (Sum.inr 0) then (1 : ℕ) else 0) = a at hI hk
  generalize (if s (Sum.inr 1) (Sum.inl 1) then (1 : ℕ) else 0) = b at hI hk
  push_cast
  omega

/-- `localReg2_inst_Q` is a locally standard packed graph -/
theorem localReg6a_instQ_locStd : localReg2_inst_Q.pack.LocStd := localReg2_inst_Q_locStd

/-- `ord = 2` at `localReg2_inst_Q`, so the bounds below are sharp -/
theorem localReg6a_instQ_ord : localReg2_inst_Q.pack.g.scalingOrder = 2 := by decide

/-- Instance (10), `locReg6_of_locCostGe` at a locally standard graph with two internal vertices: `2 ≤ ord`. -/
theorem localReg6a_instQ_all_ord : (2 : ℤ) ≤ localReg2_inst_Q.pack.g.scalingOrder :=
  locReg6_of_locCostGe localReg6a_instQ_locStd localReg6a_instQ_all

/-- Instance (10), `locReg6far_of_locCostGe` at the same graph (`x ≠ y`): `2 ≤ ord`. -/
theorem localReg6a_instQ_far_ord : (2 : ℤ) ≤ localReg2_inst_Q.pack.g.scalingOrder :=
  locReg6far_of_locCostGe localReg6a_instQ_locStd (by decide)
    (fun s _ => localReg6a_instQ_all s (fun h => absurd h (by decide)))

end Instances

end RBM.Graph

end
