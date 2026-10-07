/-
Release check for T2287 (dispatcher V1, Tue Oct  6 10:55 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1),
§90, §68, §58, §57 (1), §29, §24, §20, §17, §16).
BA-L1 (block Anderson graph vocabulary; T2161 split P.9, `docs/reports/T2161-portmap.md:1044`, `:1102`; T2040 row
`docs/reports/T2040-inventory.md:352`): `RBM3D/Graph/BAVocab.lean`, the `Ψ`- and `M`-dotted edges, atoms, the BA
normal graphs, the `G = Ǧ + M` partition and `def scalingBA` (`paper/tex/B_graphical_lemmas.tex:286-356`, cited `B:line`).
Section 1: the merged names the file uses (exact namespaces from the enclosing `namespace … end` blocks; file:line, last
commit on `main` b39ac53), and the BA model names BA-L2 will plug into `BALData` (not imported by the target).
Section 2: the vocabulary, in the temporary namespace `RBM.Graph.T2287Check`; T2287 copies it verbatim into namespace
`RBM.Graph` (it may add `attribute [instance] BAPGraph.instFE BAPGraph.instDE BAPGraph.instFI BAPGraph.instDI`, as
`LWVocab.lean:665` does for `PGraph`; the `letI` lines below stay).
Section 3: the statements of the public theorems as `T2287_<name> : Prop`; T2287 proves each in `RBM.Graph` as
`BAGraph.<name>` (or the name given in the docstring), binders in this order.
Section 4: concrete graphs (vocabulary) and Prop-valued examples (no proof obligation): the instances of the ticket.
Statements, definitions and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2287-check.lean`.
-/
import RBM3D.Graph.LWVocab
import RBM3D.Gauss.BlockAnderson
import RBM3D.Loop.GLoopFlow
import Mathlib.Logic.Relation

/-! ## 1. Merged names -/

-- T2050 (LW-03, 37db678): `RBM3D/Graph/LWVocab.lean`, namespace `RBM.Graph` (`:67-2559`)
#check @RBM.Graph.LData                       -- :73
#check @RBM.Graph.SEdge                       -- :82
#check @RBM.Graph.WEdge                       -- :89
#check @RBM.Graph.DEdge                       -- :96
#check @RBM.Graph.LGraph                      -- :104
#check @RBM.Graph.SEdge.val                   -- :115
#check @RBM.Graph.WEdge.val                   -- :120
#check @RBM.Graph.DEdge.val                   -- :125
#check @RBM.Graph.LGraph.term                 -- :129
#check @RBM.Graph.LGraph.val                  -- :135
#check @RBM.Graph.LGraph.adj                  -- :157
#check @RBM.Graph.LGraph.step                 -- :162
#check @RBM.Graph.LGraph.mol                  -- :167
#check @RBM.Graph.LGraph.nS                   -- :171
#check @RBM.Graph.LGraph.nW                   -- :173
#check @RBM.Graph.LGraph.nV                   -- :175
#check @RBM.Graph.LGraph.nM                   -- :177
#check @RBM.Graph.LGraph.counters             -- :182
#check @RBM.Graph.p2Graph                     -- :191
#check @RBM.Graph.p2Graph_ord                 -- :243
#check @RBM.Graph.figGraph                    -- :253
#check @RBM.Graph.figGraph_ord                -- :269
#check @RBM.Graph.SEdge.map                   -- :412
#check @RBM.Graph.WEdge.map                   -- :415
#check @RBM.Graph.DEdge.map                   -- :418
#check @RBM.Graph.LGraph.molGraph             -- :491
#check @RBM.Graph.LGraph.mem_mol_iff          -- :551
#check @RBM.Graph.PGraph                      -- :653
#check @RBM.Graph.PGraph.val                  -- :673
#check @RBM.Graph.PGraph.val_of_factor        -- :678
#check @RBM.Graph.PGraph.val_of_not           -- :688
#check @RBM.Graph.LComb.val                   -- :709
#check @RBM.Graph.LGraph.EqRel                -- :728
#check @RBM.Graph.LGraph.eqSetoid             -- :732
#check @RBM.Graph.LGraph.Cls                  -- :735
#check @RBM.Graph.LGraph.cls                  -- :738
#check @RBM.Graph.LGraph.IsExtCls             -- :741
#check @RBM.Graph.LGraph.ExtCls               -- :744
#check @RBM.Graph.LGraph.IntCls               -- :747
#check @RBM.Graph.LGraph.vmap                 -- :768
#check @RBM.Graph.LGraph.merge                -- :778
#check @RBM.Graph.LGraph.extMap               -- :785
#check @RBM.Graph.LGraph.extMap_surj          -- :788
#check @RBM.Graph.LGraph.mergeP               -- :793
#check @RBM.Graph.LGraph.Good                 -- :808
#check @RBM.Graph.LGraph.val_eq_merge_val     -- :881
#check @RBM.Graph.LGraph.mergeP_val           -- :938
#check @RBM.Graph.LGraph.Normal               -- :990
#check @RBM.Graph.LGraph.partition            -- :1303
#check @RBM.Graph.LGraph.val_eq_partition     -- :1339
#check @RBM.Graph.LGraph.partition_normal     -- :1591
#check @RBM.Graph.Counters.scalingSize        -- :1619
#check @RBM.Graph.Counters.scalingSize_eq     -- :1623
#check @RBM.Graph.LGraph.scalingSize          -- :1667
#check @RBM.Graph.LGraph.scalingOrder         -- :1672
#check @RBM.Graph.LGraph.scalingOrderG        -- :1681
#check @RBM.Graph.LGraph.le_scalingOrderG_iff -- :1685
#check @RBM.Graph.LGraph.val_of_isEmpty       -- :1721
#check @RBM.Graph.LGraph.counters_relabel_equiv -- :2114
#check @RBM.Graph.LGraph.partition_of_normal  -- :2268
#check @RBM.Graph.LGraph.scalingOrderG_of_normal -- :2306
-- `RBM3D/Graph/ScalingOrder.lean` (3c07bc8), namespace `RBM.Graph`
#check @RBM.Graph.Counters                    -- :49
#check @RBM.Graph.ord                         -- :65
-- BA model data for BA-L2 (not imported by `Graph/BAVocab`): `RBM3D/Gauss/BlockAnderson.lean` (868b3b4),
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4), namespace `RBM.Gauss`
#check @RBM.Gauss.PsiB                        -- BlockAnderson :45
#check @RBM.Gauss.PsiI                        -- BlockAnderson :52
#check @RBM.Gauss.PsiI_isHermitian            -- BlockAnderson :65
#check @RBM.Gauss.Gres                        -- GLoopFlow :74
#check @RBM.Gauss.Mres                        -- GLoopFlow :81
-- Mathlib
#check @Relation.ReflTransGen
#check @Function.Surjective

/-! ## 2. The vocabulary (copied verbatim into `RBM3D/Graph/BAVocab.lean`, namespace `RBM.Graph`) -/

namespace RBM.Graph.T2287Check

/-- The matrices a block Anderson graph reads: those of `LData` (`M` is the matrix
`Mres ((g : ℂ) • PsiI d L W) z m`, not `m I`) and `gPsi`, the matrix `ilambda Ψ` of `(eq:Psi3D)`
(`1_2:614-616`): a `Ψ`-dotted edge `x — y` is the factor `gPsi x y` (`B:293`). -/
structure BALData (ι : Type*) extends RBM.Graph.LData ι where
  gPsi : Matrix ι ι ℂ

/-- A `Ψ`-dotted edge (`B:293`): the factor `ilambda Ψ_{xy}`. -/
structure BAPsiEdge (V : Type*) where
  x : V
  y : V

/-- An `M`-dotted edge (`B:295`): blue (`σ = true`) `M_{xy}`, red (`σ = false`) `M̄_{xy}`. -/
structure BAMEdge (V : Type*) where
  σ : Bool
  x : V
  y : V

/-- A **block Anderson graph** (`B:290-297`): a graph of `def_graph1` (the merged record) with
`Ψ`-dotted and `M`-dotted edges. -/
structure BAGraph (E I : Type*) extends RBM.Graph.LGraph E I where
  psi : List (BAPsiEdge (E ⊕ I))
  mdot : List (BAMEdge (E ⊕ I))

def BAPsiEdge.map {V W : Type*} (f : V → W) (e : BAPsiEdge V) : BAPsiEdge W := ⟨f e.x, f e.y⟩

def BAMEdge.map {V W : Type*} (f : V → W) (e : BAMEdge V) : BAMEdge W := ⟨e.σ, f e.x, f e.y⟩

/-- The factor of a `Ψ`-dotted edge at the labelling `ℓ`. -/
def BAPsiEdge.val {ι V : Type*} (D : BALData ι) (ℓ : V → ι) (e : BAPsiEdge V) : ℂ :=
  D.gPsi (ℓ e.x) (ℓ e.y)

/-- The factor of an `M`-dotted edge at the labelling `ℓ`. -/
noncomputable def BAMEdge.val {ι V : Type*} (D : BALData ι) (ℓ : V → ι) (e : BAMEdge V) : ℂ :=
  if e.σ then D.M (ℓ e.x) (ℓ e.y) else star (D.M (ℓ e.x) (ℓ e.y))

/-- The product of all edge factors and the coefficient at a labelling of all vertices. -/
noncomputable def BAGraph.term {ι E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓ : E ⊕ I → ι) : ℂ :=
  Γ.toLGraph.term D.toLData ℓ * (Γ.psi.map (BAPsiEdge.val D ℓ)).prod *
    (Γ.mdot.map (BAMEdge.val D ℓ)).prod

/-- `ValG` (`7_8:159-164`) for block Anderson graphs: the internal labels are summed. -/
noncomputable def BAGraph.val {ι E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι) : ℂ :=
  ∑ ℓi : I → ι, Γ.term D (Sum.elim ℓe ℓi)

/-- A graph of `def_graph1` read as a block Anderson graph (no `Ψ`- or `M`-dotted edges). -/
def BAGraph.ofLGraph {E I : Type*} (Γ : RBM.Graph.LGraph E I) : BAGraph E I :=
  BAGraph.mk Γ [] []

/-- `Γ` with one more `M`-dotted edge. -/
def BAGraph.addM {E I : Type*} (Γ : BAGraph E I) (e : BAMEdge (E ⊕ I)) : BAGraph E I :=
  BAGraph.mk Γ.toLGraph Γ.psi (e :: Γ.mdot)

/-- `u`, `v` are joined by a `=`-dotted, a `Ψ`-dotted or an `M`-dotted edge (`def_atom`, `B:303`; the
`×`-dotted edges do not join atoms, delta candidate T2287a). -/
def BAGraph.atomAdj {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (u v : E ⊕ I) : Bool :=
  Γ.dotted.any (fun e => e.eq && decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) ||
  Γ.psi.any (fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) ||
  Γ.mdot.any (fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)))

/-- One step of the atom closure. -/
def BAGraph.atomStep {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (s : Finset (E ⊕ I)) : Finset (E ⊕ I) :=
  s ∪ Finset.univ.filter (fun w => ∃ v ∈ s, Γ.atomAdj v w = true)

/-- **The atom of `v`** (`def_atom`, `B:302-304`): the closure of `{v}` under the dotted edges of the
three kinds (`|E ⊕ I|` steps reach the fixed point). -/
def BAGraph.atom {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (v : E ⊕ I) : Finset (E ⊕ I) :=
  (Γ.atomStep)^[Fintype.card (E ⊕ I)] {v}

/-- `n_A`: the number of internal atoms (atoms without an external vertex; `B:304`, `B:351`). -/
def BAGraph.nA {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : ℕ :=
  ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)).image Γ.atom).card

/-- Molecules of a block Anderson graph (`def_poly`, `7_8:172`, "remain the same", `B:299`): waved
edges and dotted edges of all three kinds (delta candidate T2287b). -/
def BAGraph.adj {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (u v : E ⊕ I) : Bool :=
  Γ.toLGraph.adj u v || Γ.atomAdj u v

def BAGraph.step {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (s : Finset (E ⊕ I)) : Finset (E ⊕ I) :=
  s ∪ Finset.univ.filter (fun w => ∃ v ∈ s, Γ.adj v w = true)

/-- The molecule of `v`. -/
def BAGraph.mol {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (v : E ⊕ I) : Finset (E ⊕ I) :=
  (Γ.step)^[Fintype.card (E ⊕ I)] {v}

/-- `n_M`: the number of internal molecules. -/
def BAGraph.nM {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : ℕ :=
  ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.mol v, w.isRight = true)).image Γ.mol).card

/-- `n_S`: solid edges (light-weights included). -/
def BAGraph.nS {E I : Type*} (Γ : BAGraph E I) : ℕ := Γ.solid.length

/-- `n_W`: waved edges. -/
def BAGraph.nW {E I : Type*} (Γ : BAGraph E I) : ℕ := Γ.waved.length

/-- The counters of `def scalingBA` (`B:349-353`) in the merged `Counters`: the slot `nV` holds `n_A`. -/
def BAGraph.counters {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : RBM.Graph.Counters :=
  ⟨Γ.nS, Γ.nW, Γ.nA, Γ.nM, 0, 0⟩

/-- `(eq:ordG_BA)` (`B:353`): `ord(Γ) = n_S + 2 (n_W - n_A)`, the merged `ord` of the counters. -/
def BAGraph.scalingOrder {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : ℤ :=
  RBM.Graph.ord Γ.counters

/-- `(eq_defsize_BA)` (`B:349-350`): `size(Γ) = (L^d)^{n_M} Ψ^{n_S} W^{-d (n_W - n_A)}`. -/
noncomputable def BAGraph.scalingSize {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  Γ.counters.scalingSize Ψ W d L

/-- **Normal** (`defn_normalBA`, `B:331-343`): (ii) no `=`-dotted edge (`Ψ`-, `M`- and `×`-dotted edges
allowed; reading of "regular dotted", delta candidate T2287a); (iii) every solid edge carries a circle.
(i) is not a property of a record (as `LGraph.Normal`, `LWVocab.lean:981-989`). -/
def BAGraph.Normal {E I : Type*} (Γ : BAGraph E I) : Prop :=
  (∀ e ∈ Γ.dotted, e.eq = false) ∧ (∀ e ∈ Γ.solid, e.circ = true)

/-- `G_{xy} = Ǧ_{xy} + M_{xy}` (resp. `Ḡ_{xy} = \overline{Ǧ_{xy}} + M̄_{xy}`) on every solid edge without a
circle (`B:339-340`): the list of (solid edges, new `M`-dotted edges) of the terms. -/
def baSplitSolid {V : Type*} : List (RBM.Graph.SEdge V) → List (List (RBM.Graph.SEdge V) × List (BAMEdge V))
  | [] => [([], [])]
  | e :: es => (baSplitSolid es).flatMap fun r =>
      if e.circ then [(e :: r.1, r.2)]
      else [(RBM.Graph.SEdge.mk e.σ true e.src e.dst :: r.1, r.2), (r.1, BAMEdge.mk e.σ e.src e.dst :: r.2)]

/-- The terms of the `G = Ǧ + M` expansion of `Γ` (`B:339-340`). -/
def BAGraph.splitG {E I : Type*} (Γ : BAGraph E I) : List (BAGraph E I) :=
  (baSplitSolid Γ.solid).map fun r =>
    BAGraph.mk (RBM.Graph.LGraph.mk r.1 Γ.waved Γ.dotted Γ.coeff) Γ.psi (r.2 ++ Γ.mdot)

/-- A block Anderson graph with its own vertex types and the map of the external vertices (the BA
twin of the merged `PGraph`, `LWVocab.lean:653`). -/
structure BAPGraph (E : Type) where
  E' : Type
  I' : Type
  [instFE : Fintype E']
  [instDE : DecidableEq E']
  [instFI : Fintype I']
  [instDI : DecidableEq I']
  ext : E → E'
  ext_surj : Function.Surjective ext
  g : BAGraph E' I'

/-- The value of a packed graph (as `PGraph.val`, `LWVocab.lean:673`). -/
noncomputable def BAPGraph.val {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E)
    (D : BALData ι) (ℓe : E → ι) : ℂ :=
  letI := P.instFI
  letI := P.instDI
  open Classical in
  if h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext then P.g.val D h.choose else 0

/-- The counters of a packed graph. -/
noncomputable def BAPGraph.counters {E : Type} (P : BAPGraph E) : RBM.Graph.Counters :=
  letI := P.instFE
  letI := P.instDE
  letI := P.instFI
  letI := P.instDI
  P.g.counters

noncomputable def BAPGraph.scalingOrder {E : Type} (P : BAPGraph E) : ℤ := RBM.Graph.ord P.counters

noncomputable def BAPGraph.scalingSize {E : Type} (P : BAPGraph E) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  P.counters.scalingSize Ψ W d L

/-- The value of a linear combination of packed graphs. -/
noncomputable def BAComb.val {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (L : List (BAPGraph E))
    (D : BALData ι) (ℓe : E → ι) : ℂ :=
  (L.map fun P => P.val D ℓe).sum

/-- Merging the vertices joined by `=`-dotted edges (`B:340`; the merged `LGraph.merge`, `LWVocab.lean:778`,
on the underlying graph; the `Ψ`- and `M`-dotted edges are carried along `vmap`). -/
noncomputable def BAGraph.merge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : BAGraph Γ.toLGraph.ExtCls Γ.toLGraph.IntCls :=
  BAGraph.mk Γ.toLGraph.merge (Γ.psi.map (BAPsiEdge.map Γ.toLGraph.vmap))
    (Γ.mdot.map (BAMEdge.map Γ.toLGraph.vmap))

noncomputable def BAGraph.packMerge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : BAPGraph E where
  E' := Γ.toLGraph.ExtCls
  I' := Γ.toLGraph.IntCls
  ext := Γ.toLGraph.extMap
  ext_surj := Γ.toLGraph.extMap_surj
  g := Γ.merge

/-- **The BA partition** (`B:339-341`): the terms of `G = Ǧ + M`, each with the `=`-dotted classes merged. -/
noncomputable def BAGraph.partition {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : List (BAPGraph E) :=
  Γ.splitG.map BAGraph.packMerge

/-- `ord` of a general graph (`B:354-355`): the minimum over the partition (`⊤` if empty). -/
noncomputable def BAGraph.scalingOrderG {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : WithTop ℤ :=
  (Γ.partition.map fun P => ((P.scalingOrder : ℤ) : WithTop ℤ)).foldr min ⊤

/-- `size` of a general graph (`B:354`, `(eq_defsizemax)`): the maximum over the partition (`0` if empty). -/
noncomputable def BAGraph.scalingSizeG {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  (Γ.partition.map fun P => P.scalingSize Ψ W d L).foldr max 0

/-! ## 3. The public theorems (statements) -/

/-- `BAGraph.val_ofLGraph`. -/
def T2287_val_ofLGraph : Prop :=
  ∀ {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : RBM.Graph.LGraph E I) (D : BALData ι) (ℓe : E → ι),
    (BAGraph.ofLGraph Γ).val D ℓe = Γ.val D.toLData ℓe

/-- `BAGraph.term_addM`. -/
def T2287_term_addM : Prop :=
  ∀ {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (e : BAMEdge (E ⊕ I)) (D : BALData ι) (ℓ : E ⊕ I → ι),
    (Γ.addM e).term D ℓ = Γ.term D ℓ * e.val D ℓ

/-- `BAGraph.mem_atom_iff`. -/
def T2287_mem_atom_iff : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (v w : E ⊕ I),
    w ∈ Γ.atom v ↔ Relation.ReflTransGen (fun a b => Γ.atomAdj a b = true) v w

/-- `BAGraph.mem_mol_iff`. -/
def T2287_mem_mol_iff : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (v w : E ⊕ I),
    w ∈ Γ.mol v ↔ Relation.ReflTransGen (fun a b => Γ.adj a b = true) v w

/-- `BAGraph.atom_subset_mol` (atoms lie inside molecules, `B:299`). -/
def T2287_atom_subset_mol : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (v : E ⊕ I),
    Γ.atom v ⊆ Γ.mol v

/-- `BAGraph.nA_le_card`. -/
def T2287_nA_le_card : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    Γ.nA ≤ Fintype.card I

/-- `BAGraph.nM_le_nA`. -/
def T2287_nM_le_nA : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    Γ.nM ≤ Γ.nA

/-- `BAGraph.counters_ofLGraph` (atoms are vertices when there are no `=`-dotted edges, `B:318-320`). -/
def T2287_counters_ofLGraph : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : RBM.Graph.LGraph E I),
    (∀ e ∈ Γ.dotted, e.eq = false) → (BAGraph.ofLGraph Γ).counters = Γ.counters

/-- `BAGraph.scalingOrder_ofLGraph`. -/
def T2287_scalingOrder_ofLGraph : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : RBM.Graph.LGraph E I),
    (∀ e ∈ Γ.dotted, e.eq = false) → (BAGraph.ofLGraph Γ).scalingOrder = Γ.scalingOrder

/-- `BAGraph.scalingSize_eq` (the identity of `7_8:274-275` with `n_A` for `n_V`). -/
def T2287_scalingSize_eq : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) {Ψ : ℝ}
    (W d L : ℕ), Ψ ≠ 0 →
    Γ.scalingSize Ψ W d L =
      ((L : ℝ) ^ d) ^ Γ.nM * Ψ ^ Γ.scalingOrder * ((W : ℝ) ^ d * Ψ ^ 2) ^ ((Γ.nA : ℤ) - Γ.nW)

/-- `BAGraph.val_splitG` (`G = Ǧ + M`, `B:339-340`; no hypothesis on `D`). -/
def T2287_val_splitG : Prop :=
  ∀ {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι),
    (Γ.splitG.map fun Δ => Δ.val D ℓe).sum = Γ.val D ℓe

/-- `BAGraph.splitG_circ`. -/
def T2287_splitG_circ : Prop :=
  ∀ {E I : Type} (Γ : BAGraph E I), ∀ Δ ∈ Γ.splitG, ∀ e ∈ Δ.solid, e.circ = true

/-- `BAGraph.splitG_edges` (the edge counts of a term: one solid or one `M`-dotted edge per solid edge). -/
def T2287_splitG_edges : Prop :=
  ∀ {E I : Type} (Γ : BAGraph E I), ∀ Δ ∈ Γ.splitG,
    Δ.nW = Γ.nW ∧ Δ.dotted = Γ.dotted ∧ Δ.psi = Γ.psi ∧ Δ.nS + Δ.mdot.length = Γ.nS + Γ.mdot.length

/-- `BAGraph.val_eq_partition` (`B:339-341`; no hypothesis on `D`, unlike `LGraph.val_eq_partition`). -/
def T2287_val_eq_partition : Prop :=
  ∀ {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι),
    Γ.val D ℓe = BAComb.val Γ.partition D ℓe

/-- `BAGraph.partition_normal`. -/
def T2287_partition_normal : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    ∀ P ∈ Γ.partition, P.g.Normal

/-- `BAGraph.partition_of_normal` (no `DotWF` hypothesis: BA normal graphs have no `×`-iff-solid clause). -/
def T2287_partition_of_normal : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    Γ.Normal → ∃ P : BAPGraph E, Γ.partition = [P] ∧ P.counters = Γ.counters

/-- `BAGraph.le_scalingOrderG_iff`. -/
def T2287_le_scalingOrderG_iff : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (k : ℤ),
    ((k : ℤ) : WithTop ℤ) ≤ Γ.scalingOrderG ↔ ∀ P ∈ Γ.partition, k ≤ P.scalingOrder

/-- `BAGraph.scalingOrderG_of_normal`. -/
def T2287_scalingOrderG_of_normal : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
    Γ.Normal → Γ.scalingOrderG = ((Γ.scalingOrder : ℤ) : WithTop ℤ)

/-! ## 4. Instances (vocabulary data and Prop-valued examples; compiled as theorems in `RBM.Graph.BAVocabInst`) -/

/-- `Ǧ_{y'x} Ǧ_{xy}`, the left side of `GGGamma` (`B:395`): `y', y = inl 0, inl 1`, `x = inr 0`. -/
def baGGLhs : BAGraph (Fin 2) (Fin 1) where
  solid := [⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inr 0, .inl 1⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

/-- The first sum of `GGGamma` with the D402 coefficient, one term: `M_{xu} M_{ux} S⁺_{uβ} M_{βy} M_{y'β}`
(`x, u, β = inr 0, inr 1, inr 2`). -/
def baGGT1 : BAGraph (Fin 2) (Fin 3) where
  solid := []
  waved := [⟨true, true, .inr 1, .inr 2⟩]
  dotted := []
  coeff := 1
  psi := []
  mdot := [⟨true, .inr 0, .inr 1⟩, ⟨true, .inr 1, .inr 0⟩, ⟨true, .inr 2, .inl 1⟩, ⟨true, .inl 0, .inr 2⟩]

/-- The `δ_{xy}` part of the first term of `lem_lweight` (`B:380`): `M_{xα} S_{αβ} Ǧ_{αx} Ǧ_{ββ}`
(`x, α, β = inr 0, inr 1, inr 2`). -/
def baLWT1 : BAGraph (Fin 0) (Fin 3) where
  solid := [⟨true, true, .inr 1, .inr 0⟩, ⟨true, true, .inr 2, .inr 2⟩]
  waved := [⟨false, true, .inr 1, .inr 2⟩]
  dotted := []
  coeff := 1
  psi := []
  mdot := [⟨true, .inr 0, .inr 1⟩]

/-- One `G` edge `G_{ax}` (`a = inl 0`, `x = inr 0`): its partition has two terms, `Ǧ_{ax}` and `M_{ax}`. -/
def baGedge : BAGraph (Fin 1) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

example : Prop := baGGLhs.counters = ⟨2, 0, 1, 1, 0, 0⟩
example : Prop := baGGLhs.scalingOrder = 0
example : Prop := baGGT1.counters = ⟨0, 1, 1, 0, 0, 0⟩
example : Prop := baGGT1.scalingOrder = 0
example : Prop := baLWT1.counters = ⟨2, 1, 2, 1, 0, 0⟩
example : Prop := baLWT1.scalingOrder = 0
example : Prop := baGedge.scalingOrder = -1
example : Prop := baGedge.splitG.length = 2
example : Prop := baGedge.scalingOrderG = (((-1 : ℤ)) : WithTop ℤ)
example : Prop := (BAGraph.ofLGraph RBM.Graph.p2Graph).scalingOrder = 2
example : Prop := (BAGraph.ofLGraph RBM.Graph.figGraph).scalingOrder = 4
example : Prop := T2287_val_splitG
example : Prop := T2287_val_eq_partition

end RBM.Graph.T2287Check
