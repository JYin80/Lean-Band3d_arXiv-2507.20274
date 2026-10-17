/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BALocReg1
import RBM3D.Graph.BAShapeO2

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
# BA-L L3b2a (T2469), part 1: the path invariant through every builder term of the BA-only shapes `e2`, `macroA`, `macroB`

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:172-199` (the band proof of (1)-(5)), `:302-313` (the atomic image), `:363` (`lanlw`), `:376-387` (`lem_lweight`), `:393-405` (`GGGamma`).
Design: `docs/reports/T2387-design.md` §6 row L3b2, `docs/tickets/T2469.md` target 1 (a) (split `BALocReg2 | BALocReg2B`, CONTROL H257 (3)).

For every builder term `X` of the tagged frame step (the 17 rows of `docs/reports/T2447-prove.md:9-28` and `A1` of `gg2`), the invariant of the atomic image passes from `Γ` to `X`:
`BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b`, under the hypotheses of the constructor of `BAFrameStepT` that builds `X` (the same hypotheses as the cost twins
`BAShapeO2_*`, `Graph/BAShapeO2.lean`, whose signatures the term lemmas below follow, so that file 2 of the row consumes them in the same way).  Band originals: `LocalRegular2` §3
(`localReg2_pathFam_owxT1`-`T4`, `oe1xOwx`, `oe1xD`, `oe2xR2`-`R8`), whose replacement lemmas `localReg2_VRepl.same` / `.deriv` (LR2:852, 882) are used at the vertex map `owxEmb n`
of the extension `BAGraph.ext n Γ rest S W md`.

## Contents (namespace `RBM.Graph`; helpers carry the stem `BALocReg2_`, the instance data the namespace `BALocReg2Inst`)

1. **Tools**: the family of `Γ` read in the molecules of an extension (`BALocReg2_pathAt_map_fam`, the first half of `BALocReg1_pathAt_map`, LR2:616 along `owxEmb n`), the coloured
   edges of an atomic image (`BALocReg2_edgeMS_eq`), the molecular identifications by `M`-dotted and waved edges (`BALocReg2_mu_md`, `_mu_wav`), and the extension lemma
   `BALocReg2_pathAt_ext`: the invariant passes from `Γ` to `ext n Γ rest S W md` under a replacement `localReg2_VRepl` of the selected edges of `Γ` by the new edges.
2. **The weight terms**: `lanlwD`, the heads of `lw2`, `lw4`, `within`, the tail of `lw4`.
3. **The `GGGamma` terms**: `A1`-`A5`, `AD` of `gg2`; `B1`, `B2`, `BD` of `gg4`.
4. **The `ggSplit` terms** `d1`-`d4`.
5. **The term lists**: `BALocReg2_lw2`, `_lw4`, `_within`, `_gg2`, `_gg4`.
6. **Compiled instances** (`example`s) at the R1 witnesses `P_W`, `P_B`, `P_A`, `P_C`, with every constructor hypothesis discharged; with the invariant of the parent satisfied (not assumed) at `P_C`,
   `baPEr` (`BALocReg1Inst`: `pathInv2_C`, `pathInv2_Er`) and at `P_A`, `P_B` and a weight witness `baPL` (hand-built families moved along `BALocReg1_pathAt_map`: `BALocReg2Inst.pathInv2_A`, `_B`, `_L`).

C1: combinatorial; no data.  No `inductive`, no new `Prop` def.  No port from `../RBM1D`, `../RBM2D` (the d = 3 invariants are the band's `LocalRegular2`, applied to the atomic image).
-/

noncomputable section

namespace RBM.Graph

/-! ## 1. Tools -/

section Tools

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E'] [DecidableEq E']
  [Fintype I'] [DecidableEq I']

/-- the coloured molecular edges of the atomic image of a BA graph, as the list of its solid edges read at `BALocReg1_mu` -/
theorem BALocReg2_edgeMS_eq (Γ' : BAGraph E' I') :
    (promoteC Γ').merge.localReg2_edgeMS =
      ((Γ'.solid.map fun e => (e.σ, s(BALocReg1_mu Γ' e.src, BALocReg1_mu Γ' e.dst)) : List _) : Multiset _) := by
  unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS localReg2_mapMS
  simp only [Multiset.map_coe]
  rw [show (promoteC Γ').merge.solid = (promoteC Γ').solid.map (SEdge.map (promoteC Γ').vmap) from rfl, BAAtomic_promoteC_solid]
  simp only [List.map_map]
  rfl

/-- **The family of `Γ` read in the molecules of `Γ'`** (the first half of `BALocReg1_pathAt_map`, with no budget moved): along a vertex map `ψ` that respects the atoms, is onto up to
molecules and maps waved edges into molecules, the family of `Γ` is a family of the same number of walks with the budget `Γ.solid` read at `ψ` in the molecules of `Γ'`. -/
theorem BALocReg2_pathAt_map_fam (Γ : BAGraph E I) (Γ' : BAGraph E' I') (ψ : E ⊕ I → E' ⊕ I') (f : E → E')
    (hψ : ∀ a, ψ (Sum.inl a) = Sum.inl (f a))
    (hatom : ∀ u v, v ∈ Γ.atom u → ψ v ∈ Γ'.atom (ψ u))
    (hsurj : ∀ w, ∃ u, ψ u ∈ Γ'.mol w)
    (hwav : ∀ e ∈ Γ.waved, ψ e.y ∈ Γ'.mol (ψ e.x))
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Γ k a b) :
    localReg2_Fam k ((promoteC Γ').merge.molOf (Sum.inl ((promoteC Γ').extMap (f a))))
      ((promoteC Γ').merge.molOf (Sum.inl ((promoteC Γ').extMap (f b)))) (fun c => ¬ (promoteC Γ').merge.IsExtMol c)
      ((Γ.solid.map fun e => (e.σ, s(BALocReg1_mu Γ' (ψ e.src), BALocReg1_mu Γ' (ψ e.dst))) : List _) : Multiset _) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : (promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls → E ⊕ I, ∀ w, (promoteC Γ).vmap (g w) = w :=
    ⟨Function.surjInv (BAAtomic_vmap_surjective (promoteC Γ)), Function.surjInv_eq (BAAtomic_vmap_surjective (promoteC Γ))⟩
  have hφ : ∀ u, (promoteC Γ').vmap (ψ (g ((promoteC Γ).vmap u))) = (promoteC Γ').vmap (ψ u) := by
    intro u
    have h1 : g ((promoteC Γ).vmap u) ∈ Γ.atom u := (BAAtomic_promoteC_vmap_eq_atom Γ u _).1 (hg _).symm
    exact ((BAAtomic_promoteC_vmap_eq_atom Γ' _ _).2 (hatom _ _ h1)).symm
  have hφl : ∀ a, (promoteC Γ').vmap (ψ (g (Sum.inl ((promoteC Γ).extMap a)))) = Sum.inl ((promoteC Γ').extMap (f a)) := by
    intro a
    have := hφ (Sum.inl a)
    rw [BAAtomic_vmap_inl, hψ, BAAtomic_vmap_inl] at this
    exact this
  have key := LGraph.localReg2_pathFam_map (promoteC Γ).merge (promoteC Γ').merge
    (fun w => (promoteC Γ').vmap (ψ (g w)))
    (by
      rintro ⟨q, a, rfl⟩
      exact ⟨_, hφl a⟩)
    (by
      intro v'
      obtain ⟨u', rfl⟩ := BAAtomic_vmap_surjective (promoteC Γ') v'
      obtain ⟨u, hu⟩ := hsurj u'
      refine ⟨(promoteC Γ).vmap u, ?_⟩
      rw [hφ u]
      exact (SimpleGraph.ConnectedComponent.eq (G := (promoteC Γ').merge.molGraph)).1 ((Γ'.img_molOf_eq_iff u' (ψ u)).2 hu))
    (by
      intro u v huv
      obtain ⟨e0, he0, h0 | h0⟩ := (BAAtomic_merge_adj_iff Γ u v).1 huv
      · rw [← h0.1, ← h0.2, hφ, hφ]
        exact (SimpleGraph.ConnectedComponent.eq (G := (promoteC Γ').merge.molGraph)).1 ((Γ'.img_molOf_eq_iff _ _).2 (hwav e0 he0))
      · rw [← h0.1, ← h0.2, hφ, hφ]
        exact ((SimpleGraph.ConnectedComponent.eq (G := (promoteC Γ').merge.molGraph)).1 ((Γ'.img_molOf_eq_iff _ _).2 (hwav e0 he0))).symm)
    h
  rw [hφl, hφl] at key
  have hB1 : localReg2_mapMS (fun v => (promoteC Γ').merge.molOf ((promoteC Γ').vmap (ψ (g v)))) (promoteC Γ).merge.localReg2_cendsMS =
      ((Γ.solid.map fun e => (e.σ, s(BALocReg1_mu Γ' (ψ e.src), BALocReg1_mu Γ' (ψ e.dst))) : List _) : Multiset _) := by
    unfold LGraph.localReg2_cendsMS localReg2_mapMS
    simp only [Multiset.map_coe]
    rw [show (promoteC Γ).merge.solid = (promoteC Γ).solid.map (SEdge.map (promoteC Γ).vmap) from rfl, BAAtomic_promoteC_solid]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp [SEdge.localReg2_cends, SEdge.map, Sym2.map_mk, hφ, BALocReg1_mu]
  rw [hB1] at key
  exact key

/-- an `M`-dotted edge identifies its ends in the molecules -/
theorem BALocReg2_mu_md (X : BAGraph E I) {m : BAMEdge (E ⊕ I)} (hm : m ∈ X.mdot) : BALocReg1_mu X m.x = BALocReg1_mu X m.y :=
  (BALocReg1_mu_eq_iff _ _ _).2 (BALocReg1_mol_of_atom _ (BAScost_atomSetoid_of_mdot X m hm))

/-- a waved edge identifies its ends in the molecules -/
theorem BALocReg2_mu_wav (X : BAGraph E I) {w : WEdge (E ⊕ I)} (hw : w ∈ X.waved) : BALocReg1_mu X w.x = BALocReg1_mu X w.y :=
  (BALocReg1_mu_eq_iff _ _ _).2 (BALocReg1_mem_mol_waved X hw)

/-- the atom relation of `Γ` identifies the embedded vertices in the molecules of an extension -/
theorem BALocReg2_mu_atom {k : ℕ} (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (S : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (W : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) {u v : E ⊕ I} (h : Γ.sameAtom u v = true) :
    BALocReg1_mu (BAGraph.ext k Γ rest S W md) (owxEmb k u) = BALocReg1_mu (BAGraph.ext k Γ rest S W md) (owxEmb k v) :=
  (BALocReg1_mu_eq_iff _ _ _).2 (BALocReg1_mol_of_atom _ (BAScost_atomSetoid_ext Γ rest S W md
    ((BAAtomic_atomSetoid_iff Γ _ _).2 ((Γ.BAAtomic_sameAtom_iff _ _).1 h))))

/-- **The extension lemma**: the invariant passes from `Γ` to `ext n Γ rest S W md` when the selected edges `sel` of `Γ` (`Γ.solid ~ sel ++ rest`), embedded by `owxEmb n`, are
replaced by the new edges `S`, read in the molecules of the extension, by a replacement `localReg2_VRepl` (`localReg2_VRepl.same`, `.deriv`; the edges `rest` are kept), and every fresh
vertex lies in the molecule of an old one. -/
theorem BALocReg2_pathAt_ext (n : ℕ) (Γ : BAGraph E I) (sel rest : List (SEdge (E ⊕ I))) (hperm : Γ.solid.Perm (sel ++ rest))
    (S : List (SEdge (E ⊕ (I ⊕ Fin n)))) (W : List (WEdge (E ⊕ (I ⊕ Fin n)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin n))))
    (hnew : ∀ i : Fin n, ∃ u : E ⊕ I, BALocReg1_mu (BAGraph.ext n Γ rest S W md) (owxEmb n u) =
      BALocReg1_mu (BAGraph.ext n Γ rest S W md) (Sum.inr (Sum.inr i)))
    (hrepl : localReg2_VRepl (BALocReg1_mu (BAGraph.ext n Γ rest S W md))
      ((sel.map fun e => (SEdge.map (owxEmb n) e).localReg2_cends : List (Bool × Sym2 (E ⊕ (I ⊕ Fin n)))) : Multiset _)
      ((S.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ (I ⊕ Fin n)))) : Multiset _))
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Γ k a b) : BALocReg1_PathAt (BAGraph.ext n Γ rest S W md) k a b := by
  classical
  set X : BAGraph E (I ⊕ Fin n) := BAGraph.ext n Γ rest S W md with hX
  set μ := BALocReg1_mu X with hμ
  have key := BALocReg2_pathAt_map_fam Γ X (owxEmb n) id (fun _ => rfl)
    (fun u v hv => (BAAtomic_atomSetoid_iff _ _ _).1 (BAScost_atomSetoid_ext Γ rest S W md ((BAAtomic_atomSetoid_iff Γ u v).2 hv)))
    (fun w => by
      rcases w with a | i | j
      · exact ⟨Sum.inl a, BALocReg1_mem_mol_self _ _⟩
      · exact ⟨Sum.inr i, BALocReg1_mem_mol_self _ _⟩
      · obtain ⟨u, hu⟩ := hnew j
        exact ⟨u, (BALocReg1_mu_eq_iff X _ _).1 hu.symm⟩)
    (fun e he => BALocReg1_mem_mol_waved X (e0 := WEdge.map (owxEmb n) e) (List.mem_append_left _ (List.mem_map.2 ⟨e, he, rfl⟩))) h
  set F : SEdge (E ⊕ I) → Bool × Sym2 (promoteC X).merge.Mol := fun e => (e.σ, s(μ (owxEmb n e.src), μ (owxEmb n e.dst))) with hF
  have hrem : ((Γ.solid.map F : List _) : Multiset _) = ((rest.map F : List _) : Multiset _) +
      localReg2_mapMS μ ((sel.map fun e => (SEdge.map (owxEmb n) e).localReg2_cends : List _) : Multiset _) := by
    rw [Multiset.coe_eq_coe.2 (hperm.map F), List.map_append, ← Multiset.coe_add, add_comm]
    congr 1
    unfold localReg2_mapMS
    rw [Multiset.map_coe, List.map_map]
    rfl
  have hadd : ((X.solid.map fun e => (e.σ, s(μ e.src, μ e.dst)) : List _) : Multiset _) = ((rest.map F : List _) : Multiset _) +
      localReg2_mapMS μ ((S.map SEdge.localReg2_cends : List _) : Multiset _) := by
    rw [show X.solid = rest.map (SEdge.map (owxEmb n)) ++ S from rfl, List.map_append, ← Multiset.coe_add, List.map_map]
    congr 1
    unfold localReg2_mapMS
    rw [Multiset.map_coe, List.map_map]
    rfl
  rw [hrem] at key
  have key2 := hrepl (((rest.map F : List _) : Multiset _)) k _ _ _ key
  unfold BALocReg1_PathAt LGraph.localReg2_PathFam
  rw [BALocReg2_edgeMS_eq, hadd]
  exact key2

theorem BALocReg2_bpS_σ {V : Type} (c : Bool) (a b : V) : (bpS c a b).σ = true := rfl

theorem BALocReg2_bpS_src {V : Type} (c : Bool) (a b : V) : (bpS c a b).src = a := rfl

theorem BALocReg2_bpS_dst {V : Type} (c : Bool) (a b : V) : (bpS c a b).dst = b := rfl

/-- the covering clause of `localReg2_VRepl.same`, `.deriv` for one added diagonal edge `(σ, {w, w'})` whose molecule `c` is an end of a kept edge of the colour `σ` -/
theorem BALocReg2_cov {V N' : Type*} (μ : V → N') (σ : Bool) (w w' : V) {M : Multiset (Bool × Sym2 V)} (c : N') (hw : μ w = c) (hw' : μ w' = c)
    (hm : ∃ s' ∈ M, s'.1 = σ ∧ c ∈ Sym2.map μ s'.2) :
    ∀ s ∈ ({(σ, s(w, w'))} : Multiset (Bool × Sym2 V)), ∀ C ∈ Sym2.map μ s.2, ∃ s' ∈ M, s'.1 = s.1 ∧ C ∈ Sym2.map μ s'.2 := by
  intro s hs C hC
  rw [Multiset.mem_singleton] at hs
  subst hs
  obtain ⟨s', hs', h1, h2⟩ := hm
  simp only [Sym2.map_mk, Sym2.mem_iff] at hC
  refine ⟨s', hs', h1, ?_⟩
  rcases hC with rfl | rfl
  · rw [hw]; exact h2
  · rw [hw']; exact h2

/-- **The extension lemma for `n = 2`** (the shape of `lw2`, `within`, `lanlwD`, `gg2`, `ggSplit`): one waved edge `α ~ β`, an `M`-dotted edge `x ~ α`; the molecule facts are handed to the replacement:
`μ` is the molecule map of the extension, constant on the ends of every `M`-dotted edge, and `α`, `β` lie in the molecule of `x`. -/
theorem BALocReg2_pathAt_ext2 (Γ : BAGraph E I) (sel rest : List (SEdge (E ⊕ I))) (hperm : Γ.solid.Perm (sel ++ rest))
    (S : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (c : Bool) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I)
    (h0 : bpM (owxEmb 2 x) (bpv 0) ∈ md)
    (hrepl : ∀ X : BAGraph E (I ⊕ Fin 2), X = BAGraph.ext 2 Γ rest S [bpW c (bpv 0) (bpv 1)] md →
      ∀ μ : E ⊕ (I ⊕ Fin 2) → (promoteC X).merge.Mol, μ = BALocReg1_mu X → (∀ m ∈ md, μ m.x = μ m.y) →
      μ (bpv 0) = μ (owxEmb 2 x) → μ (bpv 1) = μ (owxEmb 2 x) →
      localReg2_VRepl μ ((sel.map fun e => (SEdge.map (owxEmb 2) e).localReg2_cends : List (Bool × Sym2 (E ⊕ (I ⊕ Fin 2)))) : Multiset _)
        ((S.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ (I ⊕ Fin 2)))) : Multiset _))
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Γ k a b) :
    BALocReg1_PathAt (BAGraph.ext 2 Γ rest S [bpW c (bpv 0) (bpv 1)] md) k a b := by
  classical
  set X : BAGraph E (I ⊕ Fin 2) := BAGraph.ext 2 Γ rest S [bpW c (bpv 0) (bpv 1)] md with hX
  have hmd : ∀ m ∈ md, BALocReg1_mu X m.x = BALocReg1_mu X m.y := fun m hm => BALocReg2_mu_md X (by simp [hX, BAGraph.ext, hm])
  have hα : BALocReg1_mu X (bpv 0) = BALocReg1_mu X (owxEmb 2 x) := (hmd _ h0).symm
  have hβ : BALocReg1_mu X (bpv 1) = BALocReg1_mu X (owxEmb 2 x) :=
    (BALocReg2_mu_wav X (w := bpW c (bpv 0) (bpv 1)) (by simp [hX, BAGraph.ext, LGraph.owxExt])).symm.trans hα
  refine BALocReg2_pathAt_ext 2 Γ sel rest hperm S _ md (fun i => ?_) (hrepl X rfl _ rfl hmd hα hβ) h
  fin_cases i
  exacts [⟨x, hα.symm⟩, ⟨x, hβ.symm⟩]

/-- **The extension lemma for `n = 4`** (the shape of `lw4`, `gg4`): waved edges `0 ~ 1`, `2 ~ 3` and `M`-dotted edges `x ~ 0`, `0 ~ x`, `1 ~ 2`; all four fresh vertices lie in the molecule of `x`. -/
theorem BALocReg2_pathAt_ext4 (Γ : BAGraph E I) (sel rest : List (SEdge (E ⊕ I))) (hperm : Γ.solid.Perm (sel ++ rest))
    (S : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I)
    (hrepl : ∀ X : BAGraph E (I ⊕ Fin 4), X = BAGraph.ext 4 Γ rest S [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 x) (bpv 0), bpM (bpv 0) (owxEmb 4 x), bpM (bpv 1) (bpv 2)] →
      ∀ μ : E ⊕ (I ⊕ Fin 4) → (promoteC X).merge.Mol, μ = BALocReg1_mu X →
      μ (bpv 0) = μ (owxEmb 4 x) → μ (bpv 1) = μ (owxEmb 4 x) → μ (bpv 2) = μ (owxEmb 4 x) → μ (bpv 3) = μ (owxEmb 4 x) →
      localReg2_VRepl μ ((sel.map fun e => (SEdge.map (owxEmb 4) e).localReg2_cends : List (Bool × Sym2 (E ⊕ (I ⊕ Fin 4)))) : Multiset _)
        ((S.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ (I ⊕ Fin 4)))) : Multiset _))
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Γ k a b) :
    BALocReg1_PathAt (BAGraph.ext 4 Γ rest S [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
      [bpM (owxEmb 4 x) (bpv 0), bpM (bpv 0) (owxEmb 4 x), bpM (bpv 1) (bpv 2)]) k a b := by
  classical
  set X : BAGraph E (I ⊕ Fin 4) := BAGraph.ext 4 Γ rest S [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 x) (bpv 0), bpM (bpv 0) (owxEmb 4 x), bpM (bpv 1) (bpv 2)] with hX
  have h0 : BALocReg1_mu X (bpv 0) = BALocReg1_mu X (owxEmb 4 x) :=
    (BALocReg2_mu_md X (m := bpM (owxEmb 4 x) (bpv 0)) (by simp [hX, BAGraph.ext])).symm
  have h1 : BALocReg1_mu X (bpv 1) = BALocReg1_mu X (owxEmb 4 x) :=
    (BALocReg2_mu_wav X (w := bpW true (bpv 0) (bpv 1)) (by simp [hX, BAGraph.ext, LGraph.owxExt])).symm.trans h0
  have h2 : BALocReg1_mu X (bpv 2) = BALocReg1_mu X (owxEmb 4 x) :=
    (BALocReg2_mu_md X (m := bpM (bpv 1) (bpv 2)) (by simp [hX, BAGraph.ext])).symm.trans h1
  have h3 : BALocReg1_mu X (bpv 3) = BALocReg1_mu X (owxEmb 4 x) :=
    (BALocReg2_mu_wav X (w := bpW false (bpv 2) (bpv 3)) (by simp [hX, BAGraph.ext, LGraph.owxExt])).symm.trans h2
  refine BALocReg2_pathAt_ext 4 Γ sel rest hperm S _ _ (fun i => ?_) (hrepl X rfl _ rfl h0 h1 h2 h3) h
  fin_cases i
  exacts [⟨x, h0.symm⟩, ⟨x, h1.symm⟩, ⟨x, h2.symm⟩, ⟨x, h3.symm⟩]

end Tools

/-! ## 2. The weight terms -/

local macro "BALocReg2_simp0" : tactic => `(tactic| simp only [SEdge.localReg2_cends_mk, SEdge.localReg2_cends_map, SEdge.localReg2_cends, Prod.map_apply, Sym2.map_mk,
  localReg2_mapMS, List.map_cons, List.map_nil, Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe,
  Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq, BALocReg2_bpS_σ, BALocReg2_bpS_src, BALocReg2_bpS_dst, SEdge.map])

local macro "BALocReg2_msnorm" : tactic => `(tactic| (BALocReg2_simp0; try abel))

section Weight

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]


/-- **`lw2` head** (`BAWeightOp:69`): `p.1` a blue loop `Ǧ_{xx}`; the extension has the loops `Ǧ_{αx}` and `Ǧ_{ββ}` in the molecule of `x` (the band's `owxT1`, LR2:1027). -/
theorem BALocReg2_lw2Head (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 2 Γ p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0)]) k a b := by
  intro k a b h
  obtain ⟨hσ, -, hxy⟩ := hp1
  refine BALocReg2_pathAt_ext2 Γ [p.1] p.2 (by simpa using lwSplit_perm Γ.solid p hp) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.src))} {(true, s(bpv 0, owxEmb 2 p.1.src))}
    {(true, s(bpv 1, bpv 1))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff]
  · exact BALocReg2_cov _ true (bpv 1) (bpv 1) (μ (owxEmb 2 p.1.src)) hβ hβ ⟨(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.src)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [hα]
  · BALocReg2_simp0
    simp only [hσ, hxy]
    try abel
  · BALocReg2_simp0
    simp only [hxy]
    try abel

/-- **`lanlwD`** (the derivative term of `lanlw`, the tail of `lw2`, of the `within` stage 1, of `edge`, of `ggSplit`; `BAExpandW:133`): `p.1 = Ǧ_{xy}` becomes `G_{βy}` in the molecule of `x`
and the edge `q.1` is rerouted through the molecule of `x` (the band's `oe1xD`, LR2:1165). -/
theorem BALocReg2_lanlwD (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGraph.lanlwD Γ p q) k a b := by
  intro k a b h
  have hD : BAGraph.lanlwD Γ p q = BAGraph.ext 2 Γ q.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).1,
      (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)] := rfl
  rw [hD]
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  refine localReg2_VRepl.deriv μ (bpv 1) (bpv 0) (hβ.trans hα.symm) (SEdge.map (owxEmb 2) q.1) 0
    {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst))} {(true, s(bpv 1, owxEmb 2 p.1.dst))} 0 (by simp) (by simp) (by simp) ?_ ?_ ?_
  · BALocReg2_simp0
    simp only [hα, hβ]
  · BALocReg2_simp0
    simp only [hp1.1]
    abel
  · BALocReg2_simp0
    abel

/-- **`lw4` head** (`BAWeightOp:74`): `p.1` a blue loop `Ǧ_{xx}`; the four fresh vertices `z, y, α, β = bpv 0..3` lie in the molecule of `x`, so the new edges `Ǧ_{αy}`, `Ǧ_{ββ}` are loops there (the band's `owxT2`, LR2:1052). -/
theorem BALocReg2_lw4Head (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 4 Γ p.2 [bpS true (bpv 2) (bpv 1), bpS true (bpv 3) (bpv 3)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) k a b := by
  intro k a b h
  obtain ⟨hσ, -, hxy⟩ := hp1
  refine BALocReg2_pathAt_ext4 Γ [p.1] p.2 (by simpa using lwSplit_perm Γ.solid p hp) _ p.1.src ?_ h
  intro X hX μ hμ h0 h1 h2 h3
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.src))} {(true, s(bpv 2, bpv 1))}
    {(true, s(bpv 3, bpv 3))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff]
  · exact BALocReg2_cov _ true (bpv 3) (bpv 3) (μ (owxEmb 4 p.1.src)) h3 h3 ⟨(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.src)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [h1, h2]
  · BALocReg2_simp0
    simp only [hσ, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`lw4` tail** (`BAWeightOp:75`, the derivative terms at the solid edges `q.1` of `f`): the loop `p.1` is dropped and `q.1` is rerouted through the molecule of `x`, a loop is added
(the band's `owxT4`, LR2:1088). -/
theorem BALocReg2_lw4Tail (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 4 Γ q.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1, (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2,
        bpS false (bpv 3) (bpv 1)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
        [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]) k a b := by
  intro k a b h
  obtain ⟨hσ, -, hxy⟩ := hp1
  refine BALocReg2_pathAt_ext4 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ p.1.src ?_ h
  intro X hX μ hμ h0 h1 h2 h3
  refine localReg2_VRepl.deriv μ (bpv 3) (bpv 2) (h3.trans h2.symm) (SEdge.map (owxEmb 4) q.1)
    {(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.src))} 0 0 {(true, s(bpv 3, bpv 1))} ?_ ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff]
  · simp [Sym2.mk_isDiag_iff, h1, h3]
  · exact BALocReg2_cov _ true (bpv 3) (bpv 1) (μ (owxEmb 4 p.1.src)) h3 h1 ⟨(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.src)), by simp, rfl, by simp⟩
  · simp
  · BALocReg2_simp0
    simp only [hσ, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`within` head** (`BASim:122`): `p.1 = Ǧ_{xy}` becomes `Ǧ_{αy}` in the molecule of `x`, and the loop `Ǧ_{ββ}` is added there (the band's `oe1xOwx`, LR2:1143). -/
theorem BALocReg2_withinHead (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hsame : Γ.sameAtom p.1.src p.1.dst = true) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0)]) k a b := by
  intro k a b h
  obtain ⟨hσ, -⟩ := hp1
  refine BALocReg2_pathAt_ext2 Γ [p.1] p.2 (by simpa using lwSplit_perm Γ.solid p hp) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst))} {(true, s(bpv 0, owxEmb 2 p.1.dst))}
    {(true, s(bpv 1, bpv 1))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff]
  · exact BALocReg2_cov _ true (bpv 1) (bpv 1) (μ (owxEmb 2 p.1.src)) hβ hβ ⟨(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [hα]
  · BALocReg2_simp0
    simp only [hσ]
    try abel
  · BALocReg2_msnorm

end Weight

/-! ## 3. The `GGGamma` terms -/

section GG

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`gg2` head `A1`** (`BAGGOp_A1`, `Σ M_{xu} M_{ux} S⁺_{uβ} M_{βy} M_{y'β} f`, the first sum): the atoms of `x`, `y`, `y'` merge, the pair `p`, `q` becomes two loops (`BAScostLL_S1`'s path twin;
stage 2 of macro (b) reads every term of `tr.gg2`). -/
theorem BALocReg2_ggA1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_A1 Γ p q) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ true _ p.1.src (by simp [BAGGOp_A1]) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hy : μ (owxEmb 2 p.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp [BAGGOp_A1])).symm.trans hβ
  have hy' : μ (owxEmb 2 q.1.src) = μ (owxEmb 2 p.1.src) := (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp [BAGGOp_A1])).trans hβ
  refine localReg2_VRepl.same μ {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))} 0 0 0 ?_
    (by simp) (by simp) (by simp) ?_ ?_
  · intro s hs
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [Sym2.mk_isDiag_iff, hy, hy']
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
  · BALocReg2_simp0

/-- **`gg2` head `A2`** (`BAGGOp_A2`, `Σ M_{xu} M_{ux} S⁺_{uβ} Ǧ_{βy} M_{y'β} f`; the band's `R2`, LR2:1330, whose selector is the exchanged pair `BASim:196-198`; no exchange is needed here): `y'` joins the molecule of `x`, `q.1 = (y', x)` becomes a loop,
`p.1 = (x, y)` becomes `(β, y)`. -/
theorem BALocReg2_ggA2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_A2 Γ p q) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ true _ p.1.src (by simp [BAGGOp_A2]) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hy' : μ (owxEmb 2 q.1.src) = μ (owxEmb 2 p.1.src) := (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp [BAGGOp_A2])).trans hβ
  refine localReg2_VRepl.same μ {(true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))} {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst))}
    {(true, s(bpv 1, owxEmb 2 p.1.dst))} 0 ?_ (by simp) (by simp) ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff, hy']
  · BALocReg2_simp0
    simp only [hβ]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`gg2` head `A3`** (`BAGGOp_A3`, `Σ M_{xu} M_{ux} S⁺_{uβ} M_{βy} Ǧ_{y'β} f`; the band's `R2`): `y` joins the molecule of `x`, `p.1 = (x, y)` becomes a loop, `q.1 = (y', x)` becomes `(y', β)`. -/
theorem BALocReg2_ggA3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_A3 Γ p q) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ true _ p.1.src (by simp [BAGGOp_A3]) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hy : μ (owxEmb 2 p.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp [BAGGOp_A3])).symm.trans hβ
  refine localReg2_VRepl.same μ {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst))} {(true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))}
    {(true, s(owxEmb 2 q.1.src, bpv 1))} 0 ?_ (by simp) (by simp) ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff, hy]
  · BALocReg2_simp0
    simp only [hβ]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`gg2` head `A4`** (`BAGGOp_A4`, `Σ M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'x} f`; the band's `R3`, LR2:1352): `p.1 = (x, y)` becomes `(α, y)` in the molecule of `x`, `q.1` is kept, a loop is added. -/
theorem BALocReg2_ggA4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_A4 Γ p q) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp [BAGGOp_A4]) ?_ h
  intro X hX μ hμ hmd hα hβ
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))}
    {(true, s(bpv 0, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))} {(true, s(bpv 1, bpv 1))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff]
  · exact BALocReg2_cov _ true (bpv 1) (bpv 1) (μ (owxEmb 2 p.1.src)) hβ hβ ⟨(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [hα]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`gg2` head `A5`** (`BAGGOp_A5`, `Σ M_{xα} S_{αβ} Ǧ_{αx} G_{βy} G_{y'β} f`; the band's `R5`, LR2:1410): the edges `(x, y)`, `(y', x)` move to `(β, y)`, `(y', β)` in the molecule of `x`, a loop is added. -/
theorem BALocReg2_ggA5 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_A5 Γ p q) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp [BAGGOp_A5]) ?_ h
  intro X hX μ hμ hmd hα hβ
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))}
    {(true, s(bpv 1, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, bpv 1))} {(true, s(bpv 0, owxEmb 2 p.1.src))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff, hα]
  · exact BALocReg2_cov _ true (bpv 0) (owxEmb 2 p.1.src) (μ (owxEmb 2 p.1.src)) hα rfl ⟨(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [hβ]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`gg2` tail `AD`** (`BAGGOp_AD`, the derivative terms at the solid edges `r.1` of `f`; the band's `R7`, LR2:1481): `(x, y)` becomes `(β, y)`, `(y', x)` stays, `r.1` is rerouted through the molecule of `x`. -/
theorem BALocReg2_ggAD (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true)
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hr : r ∈ lwSplit q.2) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_AD Γ p q r) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1, r.1] r.2 (BAShapeO2_perm_pqr Γ p q r hp hq hr) _ false _ p.1.src (by simp [BAGGOp_AD]) ?_ h
  intro X hX μ hμ hmd hα hβ
  refine localReg2_VRepl.deriv μ (bpv 1) (bpv 0) (hβ.trans hα.symm) (SEdge.map (owxEmb 2) r.1) 0
    {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))}
    {(true, s(bpv 1, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 p.1.src))} 0 (by simp) (by simp) (by simp) ?_ ?_ ?_
  · BALocReg2_simp0
    simp only [hα, hβ]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_simp0
    abel

/-- **`gg4` head `B1`** (`BAGGOp_B1`; the band's `R4`, LR2:1374): `(x, y)`, `(y', x)` move to `(2, y)`, `(y', 1)` in the molecule of `x`, a loop at `3` is added. -/
theorem BALocReg2_ggB1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_B1 Γ p q) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext4 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ p.1.src ?_ h
  intro X hX μ hμ h0 h1 h2 h3
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.dst)), (true, s(owxEmb 4 q.1.src, owxEmb 4 p.1.src))}
    {(true, s(bpv 2, owxEmb 4 p.1.dst)), (true, s(owxEmb 4 q.1.src, bpv 1))} {(true, s(bpv 3, bpv 3))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff]
  · exact BALocReg2_cov _ true (bpv 3) (bpv 3) (μ (owxEmb 4 p.1.src)) h3 h3 ⟨(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.dst)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [h1, h2]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`gg4` head `B2`** (`BAGGOp_B2`; the band's `R6`, LR2:1444): `(x, y)`, `(y', x)` move to `(3, y)`, `(y', 3)` in the molecule of `x`, a loop at `(2, 1)` is added. -/
theorem BALocReg2_ggB2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_B2 Γ p q) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext4 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ p.1.src ?_ h
  intro X hX μ hμ h0 h1 h2 h3
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.dst)), (true, s(owxEmb 4 q.1.src, owxEmb 4 p.1.src))}
    {(true, s(bpv 3, owxEmb 4 p.1.dst)), (true, s(owxEmb 4 q.1.src, bpv 3))} {(true, s(bpv 2, bpv 1))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff, h1, h2]
  · exact BALocReg2_cov _ true (bpv 2) (bpv 1) (μ (owxEmb 4 p.1.src)) h2 h1 ⟨(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.dst)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [h3]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_msnorm

/-- **`gg4` tail `BD`** (`BAGGOp_BD`; the band's `R8`, LR2:1510): `(x, y)`, `(y', x)` move to `(3, y)`, `(y', 1)`, `r.1` is rerouted through the molecule of `x`. -/
theorem BALocReg2_ggBD (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true)
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hr : r ∈ lwSplit q.2) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (BAGGOp_BD Γ p q r) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext4 Γ [p.1, q.1, r.1] r.2 (BAShapeO2_perm_pqr Γ p q r hp hq hr) _ p.1.src ?_ h
  intro X hX μ hμ h0 h1 h2 h3
  refine localReg2_VRepl.deriv μ (bpv 3) (bpv 2) (h3.trans h2.symm) (SEdge.map (owxEmb 4) r.1) 0
    {(true, s(owxEmb 4 p.1.src, owxEmb 4 p.1.dst)), (true, s(owxEmb 4 q.1.src, owxEmb 4 p.1.src))}
    {(true, s(bpv 3, owxEmb 4 p.1.dst)), (true, s(owxEmb 4 q.1.src, bpv 1))} 0 (by simp) (by simp) (by simp) ?_ ?_ ?_
  · BALocReg2_simp0
    simp only [h1, h3]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1, hxy]
    try abel
  · BALocReg2_simp0
    abel

end GG

/-! ## 4. The `ggSplit` terms -/

section GGSplit

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`ggSplit` term `d1`** (`BASim:132`, `dq [G_{y'β}, Ǧ_{αa'}, G_{βy}] []`; the band's `R5` at `x := a`, LR2:1410): `[a] = [a']` (`hsame`), `(a, y)`, `(y', a')` move to `(β, y)`, `(y', β)`, a loop is added. -/
theorem BALocReg2_ggSplitD1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 2 Γ q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)]
        [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hsm : μ (owxEmb 2 q.1.dst) = μ (owxEmb 2 p.1.src) := by
    rw [hμ, hX]; exact (BALocReg2_mu_atom Γ _ _ _ _ hsame).symm
  refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 q.1.dst))}
    {(true, s(bpv 1, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, bpv 1))} {(true, s(bpv 0, owxEmb 2 q.1.dst))} (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff, hα, hsm]
  · exact BALocReg2_cov _ true (bpv 0) (owxEmb 2 q.1.dst) (μ (owxEmb 2 p.1.src)) hα hsm ⟨(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), by simp, rfl, by simp⟩
  · BALocReg2_simp0
    simp only [hβ, hsm]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1]
    try abel
  · BALocReg2_msnorm

/-- **`ggSplit` term `d2`** (`dq [Ǧ_{y'β}] [M_{αa'}, M_{βy}]`; the band's `R2`): `y` joins the molecule of `a`, `p.1` becomes a loop, `q.1 = (y', a')` becomes `(y', β)`. -/
theorem BALocReg2_ggSplitD2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)]) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hy : μ (owxEmb 2 p.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp)).symm.trans hβ
  have hx' : μ (owxEmb 2 q.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 0) (owxEmb 2 q.1.dst)) (by simp)).symm.trans hα
  refine localReg2_VRepl.same μ {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst))} {(true, s(owxEmb 2 q.1.src, owxEmb 2 q.1.dst))}
    {(true, s(owxEmb 2 q.1.src, bpv 1))} 0 ?_ (by simp) (by simp) ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff, hy]
  · BALocReg2_simp0
    simp only [hβ, hx']
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1]
    try abel
  · BALocReg2_msnorm

/-- **`ggSplit` term `d3`** (`dq [Ǧ_{βy}] [M_{αa'}, M_{y'β}]`; the band's `R2`): `y'` joins the molecule of `a`, `q.1` becomes a loop, `p.1 = (a, y)` becomes `(β, y)`. -/
theorem BALocReg2_ggSplitD3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hy' : μ (owxEmb 2 q.1.src) = μ (owxEmb 2 p.1.src) := (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp)).trans hβ
  have hx' : μ (owxEmb 2 q.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 0) (owxEmb 2 q.1.dst)) (by simp)).symm.trans hα
  refine localReg2_VRepl.same μ {(true, s(owxEmb 2 q.1.src, owxEmb 2 q.1.dst))} {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst))}
    {(true, s(bpv 1, owxEmb 2 p.1.dst))} 0 ?_ (by simp) (by simp) ?_ ?_ ?_
  · simp [Sym2.mk_isDiag_iff, hy', hx']
  · BALocReg2_simp0
    simp only [hβ]
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1]
    try abel
  · BALocReg2_msnorm

/-- **`ggSplit` term `d4`** (`dq [] [M_{αa'}, M_{y'β}, M_{βy}]`; the band's `R2` twice): `y`, `y'` join the molecule of `a`, `p.1` and `q.1` become loops. -/
theorem BALocReg2_ggSplitD4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) :
    ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt
      (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]) k a b := by
  intro k a b h
  refine BALocReg2_pathAt_ext2 Γ [p.1, q.1] q.2 (BAShapeO2_perm_pq Γ p q hp hq) _ false _ p.1.src (by simp) ?_ h
  intro X hX μ hμ hmd hα hβ
  have hy : μ (owxEmb 2 p.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp)).symm.trans hβ
  have hy' : μ (owxEmb 2 q.1.src) = μ (owxEmb 2 p.1.src) := (hmd (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp)).trans hβ
  have hx' : μ (owxEmb 2 q.1.dst) = μ (owxEmb 2 p.1.src) := (hmd (bpM (bpv 0) (owxEmb 2 q.1.dst)) (by simp)).symm.trans hα
  refine localReg2_VRepl.same μ {(true, s(owxEmb 2 p.1.src, owxEmb 2 p.1.dst)), (true, s(owxEmb 2 q.1.src, owxEmb 2 q.1.dst))} 0 0 0 ?_
    (by simp) (by simp) (by simp) ?_ ?_
  · intro s hs
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [Sym2.mk_isDiag_iff, hy, hy', hx']
  · BALocReg2_simp0
    simp only [hp1.1, hq1.1]
  · BALocReg2_simp0

end GGSplit

/-! ## 5. The term lists -/

section Lists

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The `weight` step, `lw2`** (`BASim:139`): the invariant passes from `Γ` to every term of `lw2` at a blue circled loop `p.1` -/
theorem BALocReg2_lw2 (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
    ∀ X ∈ Γ.lw2 p, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact BALocReg2_lw2Head Γ p hp hp1
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
    exact BALocReg2_lanlwD Γ hN p hp ⟨hp1.1, hp1.2.1⟩ q hq

/-- **The `weight` step, `lw4`** -/
theorem BALocReg2_lw4 (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
    ∀ X ∈ Γ.lw4 p, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact BALocReg2_lw4Head Γ p hp hp1
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
    exact BALocReg2_lw4Tail Γ hN p hp hp1 q hq

/-- **The `within` step, stage 1** (`BASim:122`): the head and the terms `lanlwD` -/
theorem BALocReg2_within (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hsame : Γ.sameAtom p.1.src p.1.dst = true) :
    ∀ X ∈ BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0)] :: (lwSplit p.2).map (BAGraph.lanlwD Γ p),
      ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact BALocReg2_withinHead Γ p hp hp1 hsame
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
    exact BALocReg2_lanlwD Γ hN p hp hp1 q hq

/-- **The `gg` step, `gg2`** (`BASim:149`): `A1`-`A5` and the terms `AD` -/
theorem BALocReg2_gg2 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ X ∈ Γ.gg2 p q, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b := by
  intro X hX
  rw [BAGGOp_gg2_eq] at hX
  rcases List.mem_append.1 hX with hX | hX
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · exact BALocReg2_ggA1 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BALocReg2_ggA2 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BALocReg2_ggA3 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BALocReg2_ggA4 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2
    · exact BALocReg2_ggA5 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2 hint
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact BALocReg2_ggAD Γ hN p q hp hq hp1 hq1 hxy hwf1 hwf2 hint r hr

/-- **The `gg` step, `gg4`**: `B1`, `B2` and the terms `BD` -/
theorem BALocReg2_gg4 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src)
    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) :
    ∀ X ∈ Γ.gg4 p q, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b := by
  intro X hX
  rw [BAGGOp_gg4_eq] at hX
  rcases List.mem_append.1 hX with hX | hX
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact BALocReg2_ggB1 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2 hint
    · exact BALocReg2_ggB2 Γ p q hp hq hp1 hq1 hxy hwf1 hwf2 hint
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact BALocReg2_ggBD Γ hN p q hp hq hp1 hq1 hxy hwf1 hwf2 hint r hr

end Lists

/-! ## 6. Nonempty instances: the term lemmas at the R1 witnesses (`BASim3:1877-1905`), every hypothesis discharged -/

/-! ### The invariant at the witnesses `P_A`, `P_B` and a weight witness (hand-built families, moved along `BALocReg1_pathAt_map`) -/

end RBM.Graph

end
