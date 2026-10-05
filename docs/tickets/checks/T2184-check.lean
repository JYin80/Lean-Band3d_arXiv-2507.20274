/-
Release check for T2184 (dispatcher V1, Mon Oct  5 06:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §20, §45 O2, §47, §55).
LW-10c1: property (6) of `lem:localregular` (`7_8:815-818`, proof `B:200-278`), first of four tickets (DECISIONS §55; Fable
report `docs/claude-team/fable/2026-10-05-localreg6-locallemma.md`).  Section 1: the merged names it builds on (LW-03
`Graph/LWVocab`, `Graph/ScalingOrder`, LW-04 `Graph/LWStein`, LW-05 `Graph/LWWeightExp`, LW-08 `Graph/LWLvl1`, LW-08a
`Graph/LWSymm`, LW-10a `Graph/LocalRegular`, LW-10b `Graph/LocalRegular2`) and the Mathlib names of the setoid API.
Section 2: the pinned vocabulary of all of LW-10c (the cost `scost` of a graph merged along a setoid, the invariant
`LocCostGe`, the local lemma `ScostLL`, the seven primitive moves, the invariant `LocReg6Inv`), in namespace
`RBM.Graph.T2184Check` here; T2184 defines it in `RBM.Graph` verbatim.  Section 3: the statements T2184 proves (targets
2-6).  Section 4: the statements LW-10c2, c3, c4 will prove (pinned now, not proved by T2184).
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2184-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, `Graph/ScalingOrder`): records, counters, packed graphs, relabelling, normal graphs, partition
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.nS
#check @RBM.Graph.LGraph.nW
#check @RBM.Graph.LGraph.nV
#check @RBM.Graph.LGraph.counters
#check @RBM.Graph.Counters
#check @RBM.Graph.ord
#check @RBM.Graph.LGraph.scalingOrder
#check @RBM.Graph.LGraph.relabel
#check @RBM.Graph.SEdge.map
#check @RBM.Graph.PGraph
#check @RBM.Graph.LGraph.pack
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.DotWF
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.partition_of_normal
-- LW-04 (`Graph/LWStein`), LW-05 (`Graph/LWWeightExp`): splits, the vertex embedding, the term builder, the derivative edges
#check @RBM.Graph.lwSplit
#check @RBM.Graph.owxEmb
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.owxDE
#check @RBM.Graph.owxT1
#check @RBM.Graph.owxT2
#check @RBM.Graph.owxT3
#check @RBM.Graph.owxT4
-- LW-06/07 (`Graph/LWEdgeExp`, `Graph/LWGGExp`): terms the primitives decompose (LW-10c4)
#check @RBM.Graph.oe1xD
#check @RBM.Graph.oe1xP6
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.oe2xR8
#check @RBM.Graph.lwSymmOe1xOwx
#check @RBM.Graph.lwSymmOe2xR3
-- LW-08a (`Graph/LWSymm`): twists
#check @RBM.Graph.lwSymmTwistS
#check @RBM.Graph.lwSymmTwistG
#check @RBM.Graph.SEdge.conj
#check @RBM.Graph.SEdge.transpose
-- LW-08 (`Graph/LWLvl1`): the weight split, the structure of a partition term, local standardness, steps, induction
#check @RBM.Graph.lvl1Split
#check @RBM.Graph.lvl1_part_struct
#check @RBM.Graph.SEdge.lvl1IncAt
#check @RBM.Graph.LGraph.lvl1SolidAt
#check @RBM.Graph.LGraph.lvl1DegAt
#check @RBM.Graph.LGraph.StdNeutral
#check @RBM.Graph.LGraph.LocStd
#check @RBM.Graph.PGraph.LocStd
#check @RBM.Graph.PGraph.lvl1Comp
#check @RBM.Graph.lvl1Pack
#check @RBM.Graph.LocStep
#check @RBM.Graph.Lvl1Reach
#check @RBM.Graph.lvl1_step_good
#check @RBM.Graph.lvl1_induction
#check @RBM.Graph.lvl1_lemma_induction
#check @RBM.Graph.lvl1_lemma_size
#check @RBM.Graph.lvl1Cutoff
-- LW-10a (`Graph/LocalRegular`): the starting graph, its counters, the predicates (1)-(6)
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.localReg_fxyAlpha
#check @RBM.Graph.localReg_fxyBeta
#check @RBM.Graph.localReg_fxyBlock
#check @RBM.Graph.localReg_fxyAlpha_inj
#check @RBM.Graph.localReg_fxyAlpha_ne_beta
#check @RBM.Graph.localReg_fxyBeta_inj
#check @RBM.Graph.localReg_fxy_mem_solid
#check @RBM.Graph.fxyPowGraph_normal
#check @RBM.Graph.fxyPowGraph_counters
#check @RBM.Graph.fxyPowGraph_ord
#check @RBM.Graph.PGraph.LocReg1
#check @RBM.Graph.PGraph.LocReg2
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.PGraph.LocReg6
#check @RBM.Graph.pathInv_locStep
-- LW-10b (`Graph/LocalRegular2`): the assembly (1)-(5) that LW-10c4 extends, the instance graph
#check @RBM.Graph.PGraph.PathInv2
#check @RBM.Graph.pathInv2_locStep
#check @RBM.Graph.fxyPowGraph_pathInv2
#check @RBM.Graph.PGraph.PathInv2.locReg345
#check @RBM.Graph.lw_localregular_upto5
#check @RBM.Graph.localReg2_inst_Q
#check @RBM.Graph.localReg2_inst_Q_locStd
-- LW-11a (`Graph/AuxGraph`): the data copied for instance (9) (not imported by T2184)
#check @RBM.Graph.auxGraph_instXY
-- downstream consumer of (6) (`7_8:945-948`)
#check @RBM.Gauss.Sizes.LWMoment
-- Mathlib: the setoid API the cost is written in
#check @Setoid.comap
#check @Setoid.comap_rel
#check @Setoid.bot_def
#check @Setoid.ker
#check @Setoid.ker_def
#check @Quotient.eq
#check @Finset.card_eq_sum_card_image

/-! ## 2. Pinned vocabulary of LW-10c (T2184 target 1; defined in `RBM.Graph` verbatim) -/

noncomputable section

namespace RBM.Graph.T2184Check

open RBM RBM.Graph

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

/-! ## 3. The statements T2184 proves (targets 2-6; theorem names in brackets, namespace `RBM.Graph`) -/

/-- Target 2a [`LGraph.scost_perm`]: the cost sees the solid edges up to order and only the number of waved edges. -/
def ScostPermPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ Γ' : LGraph E I),
    Γ.solid.Perm Γ'.solid → Γ.waved.length = Γ'.waved.length → ∀ s : Setoid (E ⊕ I),
      LGraph.scost Γ s = LGraph.scost Γ' s

/-- Target 2b [`LGraph.scost_relabel`]: the exact pullback through a surjective vertex map sending the external vertices
onto the external vertices. -/
def ScostRelabelPin : Prop :=
  ∀ {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E'] [DecidableEq E']
    [Fintype I'] [DecidableEq I'] (Δ : LGraph E I) (ext : E → E'), Function.Surjective ext →
    ∀ vm : E ⊕ I → E' ⊕ I', Function.Surjective vm → (∀ a : E, vm (Sum.inl a) = Sum.inl (ext a)) →
      ∀ s : Setoid (E' ⊕ I'), LGraph.scost (Δ.relabel vm) s = LGraph.scost Δ (Setoid.comap vm s)

/-- Target 3 [`LGraph.scost_cons_loop_ge`], **Lemma A** (Fable report §2): adding a circled loop never lowers the cost. -/
def ScostConsLoopPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) (e : SEdge (E ⊕ I)),
    e.src = e.dst → e.circ = true → ∀ s : Setoid (E ⊕ I),
      LGraph.scost Γ s ≤ LGraph.scost ({ Γ with solid := e :: Γ.solid } : LGraph E I) s

/-- Target 4a [`LGraph.scost_le_of_lvl1Split`]: the weight split of the partition (circle or drop uncircled loops) never
lowers the cost. -/
def ScostSplitPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ Γ' : LGraph E I) (d : ℕ),
    lvl1Split Γ.solid Γ'.solid d → Γ'.waved.length = Γ.waved.length → ∀ s : Setoid (E ⊕ I),
      LGraph.scost Γ s ≤ LGraph.scost Γ' s

/-- Target 4b [`LGraph.scost_partition_ge`], **Lemma B** (Fable report §2): every term `P` of the dotted edge partition
of `Δ` has a vertex map `vm` (externals to externals) along which every setoid on `P` pulls back at no higher cost. -/
def ScostPartitionPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (Δ : LGraph E I) (P : PGraph E),
    P ∈ Δ.partition m → ∃ vm : E ⊕ I → P.E' ⊕ P.I', (∀ a : E, vm (Sum.inl a) = Sum.inl (P.ext a)) ∧
      ∀ s : Setoid (P.E' ⊕ P.I'), LGraph.scost Δ (Setoid.comap vm s) ≤ LGraph.scost P.g s

/-- Target 5a [`LGraph.scost_bot`]: the trivial setoid gives `ord + #elem` on a normal graph. -/
def ScostBotPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I), Γ.Normal →
    LGraph.scost Γ ⊥ = ord Γ.counters + (LGraph.nElem Γ : ℤ)

/-- Target 5b [`LGraph.nElem_eq_zero_of_locStd`]: a locally standard graph has no elementary internal vertex. -/
def NElemLocStdPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I), Γ.LocStd →
    LGraph.nElem Γ = 0

/-- Target 5c [`locReg6_of_locCostGe`]. -/
def LocReg6OfLocCostGePin : Prop :=
  ∀ (Q : PGraph (Fin 2)) (k : ℤ), Q.LocStd → PGraph.LocCostGe false k Q → k ≤ Q.g.scalingOrder

/-- Target 5d [`locReg6far_of_locCostGe`]. -/
def LocReg6FarOfLocCostGePin : Prop :=
  ∀ (Q : PGraph (Fin 2)) (k : ℤ), Q.LocStd → Q.ext 0 ≠ Q.ext 1 → PGraph.LocCostGe true k Q → k ≤ Q.g.scalingOrder

/-- Target 6a [`fxyPowGraph_locCostGe`], the initial values (Fable report §5): `Φ^all(Γ_p) ≥ 2p`, `Φ^far(Γ_p) ≥ 3p`. -/
def FxyLocCostGePin : Prop :=
  ∀ p : ℕ, PGraph.LocCostGe false (2 * (p : ℤ)) (fxyPowGraph p).pack ∧
    PGraph.LocCostGe true (3 * (p : ℤ)) (fxyPowGraph p).pack

/-- Target 6b [`fxyPowGraph_locReg6Inv`]: the starting graph carries the invariant. -/
def FxyLocReg6InvPin : Prop := ∀ p : ℕ, PGraph.LocReg6Inv p (fxyPowGraph p).pack

/-! ## 4. The statements of LW-10c2, c3, c4 (pinned here; not proved by T2184) -/

/-- c2 [`LGraph.ScostLL.trans`], the composition lemma (Fable report §3). -/
def ScostLLTransPin : Prop :=
  ∀ {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I') (U : LGraph E I''),
    LGraph.ScostLL Γ T → LGraph.ScostLL T U → LGraph.ScostLL Γ U

/-- c2 [`LGraph.ScostLL.of_perm`]. -/
def ScostLLPermPin : Prop :=
  ∀ {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (Γ : LGraph E I) (T T' : LGraph E I'), T.solid.Perm T'.solid → T.waved.length = T'.waved.length →
    LGraph.ScostLL Γ T → LGraph.ScostLL Γ T'

/-- c2 [`LGraph.ScostLL.of_relabel`]. -/
def ScostLLRelabelPin : Prop :=
  ∀ {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I') (φ : E ⊕ I' → E ⊕ I''),
    Function.Surjective φ → (∀ a : E, φ (Sum.inl a) = Sum.inl a) → LGraph.ScostLL Γ T →
      LGraph.ScostLL Γ (T.relabel φ)

/-- c2 [`scostLL_loop`]. -/
def ScostLLLoopPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) (z : E ⊕ I) (col : Bool),
    LGraph.ScostLL Γ (lwPrimLoop Γ z col)

/-- c2 [`scostLL_addLoop`]. -/
def ScostLLAddLoopPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) (z : E ⊕ I) (col : Bool),
    LGraph.ScostLL Γ (lwPrimAddLoop Γ z col)

/-- c2 [`scostLL_moveLoop`]. -/
def ScostLLMoveLoopPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z : E ⊕ I) (col : Bool),
    Γ.solid.Perm (⟨col, true, z, z⟩ :: rest) → LGraph.ScostLL Γ (lwPrimMoveLoop Γ rest z col)

/-- c2 [`scostLL_contract`]. -/
def ScostLLContractPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I), u ≠ z → z ≠ v →
    Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest) →
      LGraph.ScostLL Γ (lwPrimContract Γ rest z u v)

/-- c3 [`scostLL_moveSC`]. -/
def ScostLLMoveSCPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I), u ≠ z → z ≠ v →
    Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest) →
      LGraph.ScostLL Γ (lwPrimMoveSC Γ rest z u v)

/-- c3 [`scostLL_moveOut`]. -/
def ScostLLMoveOutPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I), z ≠ v → z ≠ d →
    Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨false, false, z, d⟩ :: rest) →
      LGraph.ScostLL Γ (lwPrimMoveOut Γ rest z v d)

/-- c3 [`scostLL_dmove`]. -/
def ScostLLDmovePin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I)
    (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp : Bool) (q : SEdge (E ⊕ I)),
    (z = v ↔ cp = true) → (q.src = q.dst ↔ q.circ = true) →
    Γ.solid.Perm (⟨true, cp, z, v⟩ :: q :: rest) → LGraph.ScostLL Γ (lwPrimDmove Γ rest z v q)

/-- c4 [`LGraph.scost_twist`]: the twists `(c, t)` leave the cost unchanged. -/
def ScostTwistPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (c t : Bool) (Γ : LGraph E I)
    (s : Setoid (E ⊕ I)), LGraph.scost (lwSymmTwistG c t Γ) s = LGraph.scost Γ s

/-- c4 [`circIffLoop_locStep`]. -/
def CircIffLoopLocStepPin : Prop :=
  ∀ {E : Type} {m : ℂ} {P : PGraph E} {outs : List (PGraph E)}, LocStep m P outs → P.g.Normal →
    LGraph.CircIffLoop P.g → ∀ Q ∈ outs, LGraph.CircIffLoop Q.g

/-- c4 [`locCostGe_locStep`], the step lemma `Φ(Q') ≥ Φ(Q)` (Fable report §2). -/
def LocCostGeLocStepPin : Prop :=
  ∀ {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))}, LocStep m P outs → P.g.Normal →
    LGraph.CircIffLoop P.g → ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k P → ∀ Q ∈ outs, PGraph.LocCostGe far k Q

/-- c4 [`locReg6Inv_locStep`]. -/
def LocReg6InvLocStepPin : Prop :=
  ∀ {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (p : ℕ), LocStep m P outs →
    PGraph.LocReg6Inv p P → ∀ Q ∈ outs, PGraph.LocReg6Inv p Q

section Assembly

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- c4 [`lw_localregular`]: `lem:localregular` in full (`7_8:786-821`): the statement of the merged
`lw_localregular_upto5` (`LocalRegular2.lean:1857`) with the last conjunct extended by (6) `2p ≤ ord` for every output
and the far corollary `3p ≤ ord` when `x ≠ y` (DECISIONS §55). -/
def LwLocalRegularPin : Prop :=
  ∀ (p : ℕ) (m : ℂ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
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
        (Q.ext 0 ≠ Q.ext 1 → 3 * (p : ℤ) ≤ Q.g.scalingOrder))

end Assembly

end RBM.Graph.T2184Check

end
