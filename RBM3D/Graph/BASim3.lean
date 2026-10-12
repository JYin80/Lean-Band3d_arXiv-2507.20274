/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASim2

/-!
# BA-L R1 `BASim`: the matching of a BA step with a band `LocStep` at the atomic image (T2423), part 3

The stage 1 of macro (b) (`BAFrameStepT.ggSplit`) and `baMatch_holds : BAMatch m`; Lemma E (`baExtraGood_holds : BAExtraGood`); the macro outputs and
`baSim'_holds : BAsim' m`; the compiled instances.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open private lwExists_mem_dedupPairs lwMem_of_mem_dedupPairs from RBM3D.Graph.LWVocab
open private BAVocab_vmap_injective BAVocab_vmap_surjective BAVocab_merge_atomAdj BAVocab_merge_dotted_eq from RBM3D.Graph.BAVocab
open private BAAtomic_solidAt BAAtomic_charge BAAtomic_fm BAAtomic_exists_inr_vmap from RBM3D.Graph.BAAtomic
open private BAWeightOp_packMerge_counters BAWeightOp_nExt_add_nA BAWeightOp_atom_subset BAWeightOp_nA_le from RBM3D.Graph.BAWeightOp
open private BAVocab_atom_eq_of_mem BAVocab_self_mem_atom from RBM3D.Graph.BAVocab
open private lwVmap_isRight from RBM3D.Graph.LWVocab
open private BAExpandWOrd_ext BAExpandWOrd_ext_ge from RBM3D.Graph.BAExpandWOrd

noncomputable section

namespace RBM.Graph

open RBM

section GGSplit
variable {E : Type}

/-- the pairs of `lwSplit l` other than the `j`-th: the edge `q'.1` is an edge of the rest of the `j`-th pair `q`, and `q'.2` is the rest of `q` without it, with `q.1` -/
theorem BASim_split_erase {κ : Type*} (l : List κ) : ∀ (j : ℕ) (q : κ × List κ), (lwSplit l)[j]? = some q →
    ∀ q' ∈ (lwSplit l).eraseIdx j, ∃ r ∈ lwSplit q.2, r.1 = q'.1 ∧ q'.2.Perm (q.1 :: r.2) := by
  induction l with
  | nil => intro j q hj; simp [lwSplit] at hj
  | cons a l ih =>
    intro j q hj q' hq'
    cases j with
    | zero =>
      simp only [lwSplit, List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [lwSplit, List.eraseIdx_cons_zero, List.mem_map] at hq'
      obtain ⟨q0, hq0, rfl⟩ := hq'
      exact ⟨q0, hq0, rfl, List.Perm.refl _⟩
    | succ j0 =>
      simp only [lwSplit, List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q0, hq0, rfl⟩ := hj
      simp only [lwSplit, List.eraseIdx_cons_succ, List.mem_cons, List.eraseIdx_map, List.mem_map] at hq'
      rcases hq' with rfl | ⟨q1, hq1, rfl⟩
      · refine ⟨(a, q0.2), by simp [lwSplit], rfl, ?_⟩
        exact lwSplit_perm l q0 (List.mem_of_getElem? hq0)
      · obtain ⟨r0, hr0, h1, h2⟩ := ih j0 q0 hq0 q1 hq1
        refine ⟨(r0.1, a :: r0.2), ?_, h1, ?_⟩
        · simp only [lwSplit, List.mem_cons, List.mem_map]
          exact Or.inr ⟨r0, hr0, rfl⟩
        · exact (h2.cons a).trans (List.Perm.swap _ _ _)


/-- **`X.L1`** (`lanlwT1`, the first term of the stage 1 of macro (b)) at the band's `R3` of the frame -/
def BASim_B_XL1 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') (hσ : p.1.σ = true) (hqc : (BAScost_imgE P.g q.1).circ = false) :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)]
    ({ BAScost_imgE P.g p.1 with circ := false } :: { BAScost_imgE P.g q.1 with circ := false } :: q.2.map (BAScost_imgE P.g))
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩]
    [{ BAScost_imgE P.g p.1 with circ := false }]
    (fun e he => lvl1_mem_split _ p hp e he)
    (by
      have h1 : ({ BAScost_imgE P.g q.1 with circ := false } : SEdge _) = BAScost_imgE P.g q.1 := by
        cases hc : BAScost_imgE P.g q.1; simp_all
      rw [h1]
      refine List.Perm.cons _ ?_
      exact ((lwSplit_perm p.2 q hq).map (BAScost_imgE P.g)).symm)
    (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      refine List.Perm.trans ?_ (List.Perm.swap _ _ _)
      simp [BASim_phiE, bpS, SEdge.map, BAScost_imgE, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _),
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx', hσ, BASim_owxEmb1_inr])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx',
        BASim_owxEmb1_inr])


/-- **`X.LD`** (the derivative term `lanlwD` of the stage 1 at an edge `q'.1` of `f` other than `q.1`) at the band's `R7` for the edge of `r`, `q'.2 ~ q.1 :: r.2`:
the edge `q.1` of the term is the band's new edge `G_{ȳ'x̄}` -/
def BASim_B_XLD (P : BAPGraph E) {p q q' r : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq' : q' ∈ lwSplit p.2)
    (hr1 : r.1 = q'.1) (hr2 : q'.2.Perm (q.1 :: r.2)) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hx2 : (promoteC P.g).vmap q.1.dst = Sum.inr x') (hσ : q.1.σ = true) (hqc : (BAScost_imgE P.g q.1).circ = false) :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21x P p.1.src q'.2
    [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q'.1)).1, (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q'.1)).2,
      bpS false (bpv 1) (owxEmb 2 p.1.dst)]
    [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]
    (r.2.map (BAScost_imgE P.g))
    [⟨true, false, owxEmb 1 ((promoteC P.g).vmap q.1.src), Sum.inr (Sum.inl x')⟩,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE P.g r.1))).1,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE P.g r.1))).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC P.g).vmap p.1.dst)⟩]
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩] [] [BAScost_imgE P.g q.1]
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q' hq' e he))
    (by
      refine (List.perm_append_singleton _ _).trans ?_
      exact (hr2.map (BAScost_imgE P.g)).symm)
    (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      have hd := BASim_phiE_owxDE (BASim_phi21 P p.1.src) (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q'.1)
      have hc : owxDE (BASim_phi21 P p.1.src (bpv 1)) (BASim_phi21 P p.1.src (bpv 0)) (SEdge.map (BASim_phi21 P p.1.src) (SEdge.map (owxEmb 2) q'.1)) =
          owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE P.g r.1)) := by
        rw [BASim_phi21_alpha, BASim_phi21_beta, hx', hr1]
        exact BASim_owxDE_congr _ _ rfl (by simp [SEdge.map, BASim_phi21_emb, BAScost_imgE]) (by simp [SEdge.map, BASim_phi21_emb, BAScost_imgE])
      rw [hc] at hd
      simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append]
      rw [← hd.1, ← hd.2]
      have hq1 : SEdge.map (owxEmb 1) (BAScost_imgE P.g q.1) = ⟨true, false, owxEmb 1 ((promoteC P.g).vmap q.1.src), Sum.inr (Sum.inl x')⟩ := by
        simp [SEdge.map, BAScost_imgE, hσ, hx2, BASim_owxEmb1_inr]
        simpa [BAScost_imgE] using hqc
      rw [hq1]
      simp only [BASim_phiE, bpS, BASim_phi21_emb, BASim_phi21_alpha, BASim_phi21_beta, hx', decide_true, Bool.and_true, Bool.false_and,
        BASim_owxEmb1_inr]
      exact List.Perm.refl _)
    (List.Forall₂.cons (Or.inl (by simp [WEdge.map, bpW, BASim_phi21_alpha, BASim_phi21_beta, hx', BASim_owxEmb1_inr])) List.Forall₂.nil)

/-- **`X.d1`** (`G_{y'β}`, `Ǧ_{αa'}`, `G_{βy}`: `α ↦ x̄`, `β ↦ n0`; `Ǧ_{αa'}` is a loop at `x̄`) at the band's `R5` -/
def BASim_B_Xd1 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') (hx2 : (promoteC P.g).vmap q.1.dst = Sum.inr x') :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2
    [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)]
    [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]
    (q.2.map (BAScost_imgE P.g))
    [⟨true, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inl x')⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC P.g).vmap p.1.dst)⟩,
      ⟨true, false, owxEmb 1 ((promoteC P.g).vmap q.1.src), Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    (by simp)
    (by simp) (fun m' hm' => by
      rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append, BASim_phiE, bpS, BASim_phi21_emb, BASim_phi21_alpha,
        BASim_phi21_beta, hx', hx2, decide_true, Bool.and_true, Bool.false_and, BASim_owxEmb1_inr]
      exact (List.perm_append_singleton _ [_, _]))
    (List.Forall₂.cons (Or.inl (by simp [WEdge.map, bpW, BASim_phi21_alpha, BASim_phi21_beta, hx', BASim_owxEmb1_inr])) List.Forall₂.nil)


/-- **`BAMatch` for the stage 1 of macro (b)** (`BAFrameStepT.ggSplit`): the band-tagged outputs of `lanlwT1`, of the derivative terms and of `X.d1` are matched with the outputs
of the band step at the image of the pair (`R3`, `R7`, `R5`) -/
theorem BASim_matchLT_ggSplit (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (j : ℕ) (hj : (lwSplit p.2)[j]? = some q)
    (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) (a a' : P.I') (hx : p.1.src = Sum.inr a ∧ q.1.dst = Sum.inr a')
    (hsame : P.g.sameAtom (Sum.inr a) (Sum.inr a') = true) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
    (hint : P.g.intAtom (Sum.inr a) = true)
    (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
      ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0))
    {Q : BAPGraph E} (hQ : (BAShape.band, Q) ∈ P.splitOutsT p q j) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img := by
  have hq : q ∈ lwSplit p.2 := List.mem_of_getElem? hj
  obtain ⟨x', hx1, hx2, hy, hy', hnat, -⟩ := BASim_locStep_gg P m hp hq ⟨h.1, h.2.2.1⟩ a a' hx hsame hwf hint hnb
  have hqe : q.1 ∈ P.g.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hqc : (BAScost_imgE P.g q.1).circ = false := by simp [BAScost_imgE, hwf q.1 hqe]
  unfold BAPGraph.splitOutsT at hQ
  simp only [List.mem_append] at hQ
  rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    have hne := BASim_tagT1_band P.g T' htag
    rw [List.mem_singleton] at hT
    subst hT
    obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_XL1 P hp hq x' hx1 h.1 hqc).toData hN m) m hT' hne
    exact ⟨_, hnat, R, BASim_pack_mono P.img (L := (lwSymmOe2xR3 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x').partition m)
      (BASim_ggOuts_R3 _ _ _ _ _ _ _ _ _) hR, hRE⟩
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    have hne := BASim_tagStd_band P.g 2 T' htag
    obtain ⟨q', hq'e, rfl⟩ := List.mem_map.1 hT
    obtain ⟨r, hr, hr1, hr2⟩ := BASim_split_erase p.2 j q hj q' hq'e
    have hq' : q' ∈ lwSplit p.2 := List.mem_of_mem_eraseIdx hq'e
    obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_XLD P hp hq' hr1 hr2 x' hx1 hx2 h.2.2.1 hqc).toData hN m) m hT' hne
    refine ⟨_, hnat, R, BASim_pack_mono P.img (L := (lwSymmOe2xR7 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _ (BASim_imgP P r)).partition m)
      (BASim_ggOuts_R7 _ _ _ _ _ _ _ _ _ (BASim_imgP_mem2 P hr)) ?_, hRE⟩
    exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
      (BASim_R7_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) (BASim_imgP P r))).mpr hR
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    have hne := BASim_tagStd_band P.g 2 T' htag
    rw [List.mem_singleton] at hT
    subst hT
    obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_Xd1 P hp hq x' hx1 hx2).toData hN m) m hT' hne
    refine ⟨_, hnat, R, BASim_pack_mono P.img (L := (lwSymmOe2xR5 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _).partition m)
      (BASim_ggOuts_R5 _ _ _ _ _ _ _ _ _) ?_, hRE⟩
    exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
      (BASim_R5_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src))).mpr hR
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    exact absurd htag (by simp)
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    exact absurd htag (by simp)
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    exact absurd htag (by simp)


/-- **Item 1 (frame level): `BAMatch m`** -- every `band`-tagged output of a tagged frame step at a normal graph equals, up to `BAEquiv`, an output of a band `LocStep` at the atomic image -/
theorem baMatch_holds (m : ℂ) : BAMatch m := by
  intro E P LT hst hN Q hQ
  cases hst with
  | weight p hp h => exact BASim_matchLT_weight P hN m hp h Q hQ
  | within p hp h => exact BASim_matchLT_within P hN m hp h Q hQ
  | edge p hp h x hx hwf hv hint hbad => exact BASim_matchLT_edge P hN m hp h x hx hwf hv hint hbad Q hQ
  | gg p hp q hq h x hx hwf hint hnb => exact BASim_matchLT_gg P hN m hp hq h x hx hwf hint hnb hQ
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb => exact BASim_matchLT_ggSplit P hN m hp j hj h a a' hx hsame hwf hint hnb hQ

end GGSplit


section ExtraE
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Tt` is `T` with one more `M`-dotted edge `d` (the same underlying band graph and `Ψ`-dotted edges) -/
def BASim_ExtraDot (T Tt : BAGraph E I) (d : BAMEdge (E ⊕ I)) : Prop :=
  Tt.toLGraph = T.toLGraph ∧ Tt.psi = T.psi ∧ ∀ x, x ∈ Tt.mdot ↔ x ∈ T.mdot ∨ x = d

/-- the terms of `G = Ǧ + M` of `Tt` are those of `T` with the same extra `M`-dotted edge -/
theorem BASim_extraDot_split {T Tt : BAGraph E I} {d : BAMEdge (E ⊕ I)} (h : BASim_ExtraDot T Tt d) :
    ∀ T' ∈ T.splitG, ∃ Tt' ∈ Tt.splitG, BASim_ExtraDot T' Tt' d := by
  intro T' hT'
  obtain ⟨⟨s, w, dd, c⟩, p, m⟩ := T
  obtain ⟨⟨s', w', dd', c'⟩, p', m'⟩ := Tt
  obtain ⟨h1, h2, h3⟩ := h
  simp only [LGraph.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
  simp only at h2
  subst h2
  simp only [BAGraph.splitG, List.mem_map] at hT' ⊢
  obtain ⟨r, hr, rfl⟩ := hT'
  refine ⟨_, ⟨r, hr, rfl⟩, rfl, rfl, fun x => ?_⟩
  simp only [List.mem_append]
  have := h3 x
  simp only at this
  tauto

private theorem BASim_rtg_sub {α : Type*} {r r' : α → α → Prop} (h : ∀ a b, r a b → Relation.ReflTransGen r' a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen r' a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

/-- two graphs with the same band graph and the same atoms have the same atoms and molecules, hence the same counters and `nExt` -/
theorem BASim_atoms_congr {T₁ T₂ : BAGraph E I} (hL : T₁.toLGraph = T₂.toLGraph)
    (h12 : ∀ u v, T₁.atomAdj u v = true → T₂.sameAtom u v = true) (h21 : ∀ u v, T₂.atomAdj u v = true → T₁.sameAtom u v = true) :
    (∀ v, T₁.atom v = T₂.atom v) ∧ (∀ v, T₁.mol v = T₂.mol v) := by
  have hs : ∀ (A B : BAGraph E I), (∀ u v, A.atomAdj u v = true → B.sameAtom u v = true) →
      ∀ u v, Relation.ReflTransGen (fun a b => A.atomAdj a b = true) u v → Relation.ReflTransGen (fun a b => B.atomAdj a b = true) u v := by
    intro A B h u v huv
    refine BASim_rtg_sub (fun a b hab => ?_) huv
    have := h a b hab
    simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff] at this
    exact this
  refine ⟨fun v => Finset.ext fun w => ?_, fun v => Finset.ext fun w => ?_⟩
  · rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
    exact ⟨hs _ _ h12 v w, hs _ _ h21 v w⟩
  · rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
    have hm : ∀ (A B : BAGraph E I), A.toLGraph = B.toLGraph → (∀ u v, A.atomAdj u v = true → B.sameAtom u v = true) →
        ∀ u v, Relation.ReflTransGen (fun a b => A.adj a b = true) u v → Relation.ReflTransGen (fun a b => B.adj a b = true) u v := by
      intro A B hAB h u v huv
      refine BASim_rtg_sub (fun a b hab => ?_) huv
      simp only [BAGraph.adj, Bool.or_eq_true] at hab
      rcases hab with hab | hab
      · refine Relation.ReflTransGen.single ?_
        simp [BAGraph.adj, ← hAB, hab]
      · have := h a b hab
        simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff] at this
        refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ this
        simp [BAGraph.adj, hxy]
    exact ⟨hm _ _ hL h12 v w, hm _ _ hL.symm h21 v w⟩

theorem BASim_counters_congr {T₁ T₂ : BAGraph E I} (hL : T₁.toLGraph = T₂.toLGraph)
    (h12 : ∀ u v, T₁.atomAdj u v = true → T₂.sameAtom u v = true) (h21 : ∀ u v, T₂.atomAdj u v = true → T₁.sameAtom u v = true) :
    T₁.counters = T₂.counters ∧ T₁.nExt = T₂.nExt := by
  obtain ⟨ha, hm⟩ := BASim_atoms_congr hL h12 h21
  have hS : T₁.nS = T₂.nS := congrArg (fun L => L.solid.length) hL
  have hW : T₁.nW = T₂.nW := congrArg (fun L => L.waved.length) hL
  have ha' : T₁.atom = T₂.atom := funext ha
  have hm' : T₁.mol = T₂.mol := funext hm
  have hA : T₁.nA = T₂.nA := by unfold BAGraph.nA; rw [ha']
  have hM : T₁.nM = T₂.nM := by unfold BAGraph.nM; rw [hm']
  refine ⟨?_, ?_⟩
  · unfold BAGraph.counters; rw [hS, hW, hA, hM]
  · unfold BAGraph.nExt; rw [ha']


theorem BASim_extraDot_ext (k : ℕ) (Γ : BAGraph E I) (e : BAMEdge (E ⊕ I)) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    BASim_ExtraDot (BAGraph.ext k Γ rest s w md) (BAGraph.ext k (Γ.addM e) rest s w md) (BAMEdge.map (owxEmb k) e) :=
  ⟨rfl, rfl, fun x => by simp [BAGraph.ext, BAGraph.addM]; aesop⟩

theorem BASim_extraDot_lanlwExt (Γ : BAGraph E I) (e : BAMEdge (E ⊕ I)) (rest : List (SEdge (E ⊕ I))) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) :
    BASim_ExtraDot (BAGraph.lanlwExt Γ rest c s w md) (BAGraph.lanlwExt (Γ.addM e) rest c s w md) (BAMEdge.map (owxEmb 2) e) :=
  ⟨rfl, rfl, fun x => by simp [BAGraph.lanlwExt, BAGraph.addM]; aesop⟩

/-! ### Counting atoms under a coarsening -/

/-- the number of values of a coarser labelling on a finite set is at most that of a finer one, strictly if two classes of the finer are one of the coarser -/
theorem BASim_card_image_le {V W W' : Type*} [DecidableEq W] [DecidableEq W'] (S : Finset V) (f : V → W) (g : V → W')
    (h : ∀ u ∈ S, ∀ v ∈ S, f u = f v → g u = g v) :
    (S.image g).card ≤ (S.image f).card ∧ ((∃ u ∈ S, ∃ v ∈ S, f u ≠ f v ∧ g u = g v) → (S.image g).card < (S.image f).card) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
  · simp
  set H : W → W' := fun w => if hw : ∃ x ∈ S, f x = w then g hw.choose else g u0 with hH
  have hHf : ∀ x ∈ S, H (f x) = g x := by
    intro x hx
    have hw : ∃ y ∈ S, f y = f x := ⟨x, hx, rfl⟩
    simp only [hH, hw, ↓reduceDIte]
    exact h _ hw.choose_spec.1 x hx hw.choose_spec.2
  have himg : S.image g = (S.image f).image H := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, hHf x hx⟩
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hHf x hx).symm⟩
  refine ⟨by rw [himg]; exact Finset.card_image_le, fun ⟨u, hu, v, hv, hne, heq⟩ => ?_⟩
  rw [himg]
  refine lt_of_le_of_ne Finset.card_image_le fun hc => ?_
  have hinj := Finset.card_image_iff.1 hc
  have := hinj (Finset.mem_coe.2 (Finset.mem_image_of_mem f hu)) (Finset.mem_coe.2 (Finset.mem_image_of_mem f hv))
    (by rw [hHf u hu, hHf v hv]; exact heq)
  exact hne this


/-- an atom of `Γ` lies in an atom of a graph that contains its dotted edges -/
theorem BASim_sameAtom_of_mem {k : ℕ} (Γ : BAGraph E I) (T' : BAGraph E (I ⊕ Fin k))
    (hco : ∀ u v, Γ.atomAdj u v = true → T'.sameAtom (owxEmb k u) (owxEmb k v) = true) {u v : E ⊕ I} (h : v ∈ Γ.atom u) :
    T'.sameAtom (owxEmb k u) (owxEmb k v) = true := by
  rw [BAGraph.mem_atom_iff] at h
  simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    have := hco _ _ hbc
    simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff] at this
    exact ih.trans this

/-- **A coarsening of the atoms does not increase `nExt`**, and lowers it if two atoms of external vertices are joined -/
theorem BASim_nExt_le {k : ℕ} (Γ : BAGraph E I) (T' : BAGraph E (I ⊕ Fin k))
    (hco : ∀ u v, Γ.atomAdj u v = true → T'.sameAtom (owxEmb k u) (owxEmb k v) = true) :
    T'.nExt ≤ Γ.nExt ∧ ((∃ u v : E, Γ.atom (Sum.inl u) ≠ Γ.atom (Sum.inl v) ∧
      T'.sameAtom (owxEmb k (Sum.inl u)) (owxEmb k (Sum.inl v)) = true) → T'.nExt < Γ.nExt) := by
  classical
  set S : Finset (E ⊕ I) := Finset.univ.filter fun v => v.isLeft = true with hS
  have himg : (Finset.univ.filter fun v : E ⊕ (I ⊕ Fin k) => v.isLeft = true).image T'.atom = S.image (fun v => T'.atom (owxEmb k v)) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hS]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases w with a | b
      · exact ⟨Sum.inl a, rfl, rfl⟩
      · simp at hw
    · rintro ⟨v, hv, rfl⟩
      rcases v with a | b
      · exact ⟨Sum.inl a, rfl, rfl⟩
      · simp at hv
  have key := BASim_card_image_le S Γ.atom (fun v => T'.atom (owxEmb k v)) (fun u _ v _ h => by
    have hv : v ∈ Γ.atom u := by rw [h]; exact BAVocab_self_mem_atom Γ v
    exact (BAVocab_atom_eq_of_mem T' (show owxEmb k v ∈ T'.atom (owxEmb k u) by
      simpa [BAGraph.sameAtom] using BASim_sameAtom_of_mem Γ T' hco hv)).symm)
  have e1 : T'.nExt = (S.image (fun v => T'.atom (owxEmb k v))).card := by unfold BAGraph.nExt; rw [himg]
  have e2 : Γ.nExt = (S.image Γ.atom).card := rfl
  rw [e1, e2]
  refine ⟨key.1, fun ⟨u, v, hne, hs⟩ => key.2 ⟨Sum.inl u, by simp [hS], Sum.inl v, by simp [hS], hne, ?_⟩⟩
  exact (BAVocab_atom_eq_of_mem T' (show owxEmb k (Sum.inl v) ∈ T'.atom (owxEmb k (Sum.inl u)) by
      simpa [BAGraph.sameAtom] using hs)).symm


theorem BASim_atomAdj_addM (Γ : BAGraph E I) (d : BAMEdge (E ⊕ I)) (a b : E ⊕ I) (h : (Γ.addM d).atomAdj a b = true) :
    Γ.atomAdj a b = true ∨ (d.x = a ∧ d.y = b) ∨ (d.x = b ∧ d.y = a) := by
  by_cases hd : (decide ((d.x = a ∧ d.y = b) ∨ (d.x = b ∧ d.y = a))) = true
  · right; simpa using hd
  · left
    have hd' : decide ((d.x = a ∧ d.y = b) ∨ (d.x = b ∧ d.y = a)) = false := by simpa using hd
    simp only [BAGraph.atomAdj, BAGraph.addM, List.any_cons, hd', Bool.false_or] at h ⊢
    exact h

theorem BASim_atomAdj_addM' (Γ : BAGraph E I) (d : BAMEdge (E ⊕ I)) (a b : E ⊕ I) (h : Γ.atomAdj a b = true) :
    (Γ.addM d).atomAdj a b = true := by
  simp only [BAGraph.atomAdj, BAGraph.addM, List.any_cons] at h ⊢
  cases hd : decide ((d.x = a ∧ d.y = b) ∨ (d.x = b ∧ d.y = a)) <;> simp_all

theorem BASim_atomAdj_addM_d (Γ : BAGraph E I) (d : BAMEdge (E ⊕ I)) : (Γ.addM d).atomAdj d.x d.y = true := by
  simp [BAGraph.atomAdj, BAGraph.addM, List.any_cons]

/-- the atoms of `Γ` with one more `M`-dotted edge joining `u` and `v`: those of `Γ`, and the union of the atoms of `u` and `v` -/
theorem BASim_atom_addM (Γ : BAGraph E I) (u v : E ⊕ I) (d : BAMEdge (E ⊕ I)) (hd : d.x = u ∧ d.y = v) (a w : E ⊕ I) :
    w ∈ (Γ.addM d).atom a ↔ w ∈ Γ.atom a ∨ ((w ∈ Γ.atom u ∨ w ∈ Γ.atom v) ∧ (a ∈ Γ.atom u ∨ a ∈ Γ.atom v)) := by
  have hco : ∀ a b, b ∈ Γ.atom a → b ∈ (Γ.addM d).atom a := fun a b hab =>
    BAWeightOp_atom_subset Γ (Γ.addM d) (fun x y h => BASim_atomAdj_addM' Γ d x y h) a hab
  have hAS : ∀ x y, y ∈ Γ.atom x ↔ atomSetoid Γ x y := fun x y => (BAAtomic_atomSetoid_iff Γ x y).symm
  have hAS' : ∀ x y, y ∈ (Γ.addM d).atom x ↔ atomSetoid (Γ.addM d) x y := fun x y => (BAAtomic_atomSetoid_iff _ x y).symm
  simp only [hAS, hAS']
  have huv : atomSetoid (Γ.addM d) u v := by
    rw [← hAS']
    rw [BAGraph.mem_atom_iff]
    exact Relation.ReflTransGen.single (by rw [← hd.1, ← hd.2]; exact BASim_atomAdj_addM_d Γ d)
  have hc : ∀ x y, atomSetoid Γ x y → atomSetoid (Γ.addM d) x y := fun x y h => by
    rw [← hAS'] ; exact hco x y ((hAS x y).2 h)
  have sΓ := (atomSetoid Γ)
  constructor
  · intro h
    rw [← hAS', BAGraph.mem_atom_iff] at h
    induction h with
    | refl => exact Or.inl ((atomSetoid Γ).refl _)
    | @tail b c _ hbc ih =>
      rcases BASim_atomAdj_addM Γ d b c hbc with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h1' : atomSetoid Γ b c := by rw [← hAS, BAGraph.mem_atom_iff]; exact Relation.ReflTransGen.single h1
        rcases ih with ih | ⟨ih1, ih2⟩
        · exact Or.inl ((atomSetoid Γ).trans ih h1')
        · exact Or.inr ⟨ih1.imp (fun h => (atomSetoid Γ).trans h h1') (fun h => (atomSetoid Γ).trans h h1'), ih2⟩
      · have hb : b = u := h1.symm.trans hd.1
        have hc' : c = v := h2.symm.trans hd.2
        subst hb; subst hc'
        rcases ih with ih | ⟨ih1, ih2⟩
        · exact Or.inr ⟨Or.inr ((atomSetoid Γ).refl _), Or.inl ((atomSetoid Γ).symm ih)⟩
        · exact Or.inr ⟨Or.inr ((atomSetoid Γ).refl _), ih2⟩
      · have hb : b = v := h2.symm.trans hd.2
        have hc' : c = u := h1.symm.trans hd.1
        subst hb; subst hc'
        rcases ih with ih | ⟨ih1, ih2⟩
        · exact Or.inr ⟨Or.inl ((atomSetoid Γ).refl _), Or.inr ((atomSetoid Γ).symm ih)⟩
        · exact Or.inr ⟨Or.inl ((atomSetoid Γ).refl _), ih2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact hc _ _ h
    · have e2 : ∀ x, (atomSetoid Γ u x ∨ atomSetoid Γ v x) → atomSetoid (Γ.addM d) u x := fun x hx => by
        rcases hx with h | h
        · exact hc _ _ h
        · exact (atomSetoid (Γ.addM d)).trans huv (hc _ _ h)
      have ha := e2 a h2
      have hw := e2 w h1
      exact (atomSetoid (Γ.addM d)).trans ((atomSetoid (Γ.addM d)).symm ha) hw


/-- **Joining two different atoms, at least one internal, lowers `n_A`** -/
theorem BASim_nA_addM (Γ : BAGraph E I) (u v : E ⊕ I) (d : BAMEdge (E ⊕ I)) (hd : d.x = u ∧ d.y = v) (hne : Γ.sameAtom u v = false)
    (hint : (∀ w ∈ Γ.atom u, w.isRight = true) ∨ (∀ w ∈ Γ.atom v, w.isRight = true)) : (Γ.addM d).nA + 1 ≤ Γ.nA := by
  classical
  set Γ' := Γ.addM d with hΓ'
  have hco : ∀ a b, b ∈ Γ.atom a → b ∈ Γ'.atom a := fun a b hab =>
    BAWeightOp_atom_subset Γ Γ' (fun x y h => BASim_atomAdj_addM' Γ d x y h) a hab
  have hch := BASim_atom_addM Γ u v d hd
  have hat : ∀ a b, b ∈ Γ'.atom a → Γ'.atom b = Γ'.atom a := fun a b h => BAVocab_atom_eq_of_mem Γ' h
  have hin : ∀ a b c, b ∈ Γ'.atom a → c ∈ Γ'.atom b → c ∈ Γ'.atom a := fun a b c hab hbc => (hat a b hab) ▸ hbc
  have huv : v ∈ Γ'.atom u := by
    rw [hΓ', hch]; exact Or.inr ⟨Or.inr (BAVocab_self_mem_atom Γ v), Or.inl (BAVocab_self_mem_atom Γ u)⟩
  have hne' : v ∉ Γ.atom u := by
    intro h; simp [BAGraph.sameAtom, h] at hne
  set S : Finset (E ⊕ I) := Finset.univ.filter fun a => ∀ w ∈ Γ'.atom a, w.isRight = true with hS
  set S0 : Finset (E ⊕ I) := Finset.univ.filter fun a => ∀ w ∈ Γ.atom a, w.isRight = true with hS0
  have hSS0 : S ⊆ S0 := fun a ha => by
    simp only [hS, hS0, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact fun w hw => ha w (hco a w hw)
  have key := BASim_card_image_le S Γ.atom Γ'.atom (fun x _ y _ h => by
    have hy : y ∈ Γ.atom x := by rw [h]; exact BAVocab_self_mem_atom Γ y
    exact (hat x y (hco x y hy)).symm)
  have hA' : Γ'.nA = (S.image Γ'.atom).card := rfl
  have hA : Γ.nA = (S0.image Γ.atom).card := rfl
  have hle : (S.image Γ.atom).card ≤ (S0.image Γ.atom).card := Finset.card_le_card (Finset.image_subset_image hSS0)
  have one : ∀ x y : E ⊕ I, ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) → (∀ w ∈ Γ.atom x, w.isRight = true) →
      ¬ (∀ w ∈ Γ.atom y, w.isRight = true) → Γ'.nA + 1 ≤ Γ.nA := by
    intro x y hxy hx hy
    have hyx : y ∈ Γ'.atom x := by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · rw [hΓ', hch]; exact Or.inr ⟨Or.inl (BAVocab_self_mem_atom Γ y), Or.inr (BAVocab_self_mem_atom Γ x)⟩
    have hxS0 : x ∈ S0 := by simp only [hS0, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
    have hxS : x ∉ S := by
      intro hxS
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hxS
      push Not at hy
      obtain ⟨w0, hw0, hw0'⟩ := hy
      have := hxS w0 (hin x y w0 hyx (hco y w0 hw0))
      simp [this] at hw0'
    have hsub : S.image Γ.atom ⊆ (S0.image Γ.atom).erase (Γ.atom x) := by
      intro A hA
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hA
      refine Finset.mem_erase.2 ⟨fun heq => hxS ?_, Finset.mem_image_of_mem _ (hSS0 ha)⟩
      have hxa : x ∈ Γ.atom a := by rw [heq]; exact BAVocab_self_mem_atom Γ x
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      intro w hw
      exact ha w ((hat a x (hco a x hxa)) ▸ hw)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_of_mem (Finset.mem_image_of_mem Γ.atom hxS0)
    have h3 : 0 < (S0.image Γ.atom).card := Finset.card_pos.2 ⟨_, Finset.mem_image_of_mem Γ.atom hxS0⟩
    omega
  by_cases hu : ∀ w ∈ Γ.atom u, w.isRight = true <;> by_cases hv : ∀ w ∈ Γ.atom v, w.isRight = true
  · -- both internal
    have huS : u ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro w hw
      rcases (hch u w).1 hw with hw | ⟨hw, _⟩
      · exact hu w hw
      · exact hw.elim (hu w) (hv w)
    have hvS : v ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro w hw
      rcases (hch v w).1 hw with hw | ⟨hw, _⟩
      · exact hv w hw
      · exact hw.elim (hu w) (hv w)
    have hlt := key.2 ⟨u, huS, v, hvS, fun h => hne' (by rw [h]; exact BAVocab_self_mem_atom Γ v), (hat u v huv).symm⟩
    omega
  · exact one u v (Or.inl ⟨rfl, rfl⟩) hu hv
  · exact one v u (Or.inr ⟨rfl, rfl⟩) hv hu
  · rcases hint with h | h
    · exact absurd h hu
    · exact absurd h hv


/-! ### Terms that extend a graph -/

/-- `T` extends `Γ` by `k` new vertices: it carries the dotted, `Ψ`-dotted and `M`-dotted edges of `Γ`, renamed by `owxEmb k` -/
def BASim_Ext (Γ : BAGraph E I) (k : ℕ) (T : BAGraph E (I ⊕ Fin k)) : Prop :=
  T.dotted = Γ.dotted.map (DEdge.map (owxEmb k)) ∧ T.psi = Γ.psi.map (BAPsiEdge.map (owxEmb k)) ∧
    ∀ x ∈ Γ.mdot, BAMEdge.map (owxEmb k) x ∈ T.mdot

theorem BASim_Ext_ext (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) : BASim_Ext Γ k (BAGraph.ext k Γ rest s w md) :=
  ⟨rfl, rfl, fun x hx => by simp [BAGraph.ext]; exact Or.inr ⟨x, hx, rfl⟩⟩

theorem BASim_Ext_lanlwExt (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) : BASim_Ext Γ 2 (BAGraph.lanlwExt Γ rest c s w md) :=
  ⟨rfl, rfl, fun x hx => by simp [BAGraph.lanlwExt]; exact Or.inr ⟨x, hx, rfl⟩⟩

theorem BASim_Ext_split {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} (h : BASim_Ext Γ k T) :
    ∀ T' ∈ T.splitG, BASim_Ext Γ k T' := by
  intro T' hT'
  obtain ⟨h1, h2, h3⟩ := h
  simp only [BAGraph.splitG, List.mem_map] at hT'
  obtain ⟨r, hr, rfl⟩ := hT'
  exact ⟨h1, h2, fun x hx => List.mem_append_right _ (h3 x hx)⟩

/-- the atom edges of `Γ` are atom edges of an extension (between the embedded vertices) -/
theorem BASim_Ext_atomAdj {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} (h : BASim_Ext Γ k T) (u v : E ⊕ I)
    (huv : Γ.atomAdj u v = true) : T.atomAdj (owxEmb k u) (owxEmb k v) = true := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at huv ⊢
  rcases huv with (⟨e, he, hh1, hh⟩ | ⟨e, he, hh⟩) | ⟨e, he, hh⟩
  · left; left
    refine ⟨DEdge.map (owxEmb k) e, by rw [h1]; exact List.mem_map_of_mem he, hh1, ?_⟩
    simp only [DEdge.map]
    rcases hh with ⟨a, b⟩ | ⟨a, b⟩
    · left; exact ⟨by rw [a], by rw [b]⟩
    · right; exact ⟨by rw [a], by rw [b]⟩
  · left; right
    refine ⟨BAPsiEdge.map (owxEmb k) e, by rw [h2]; exact List.mem_map_of_mem he, ?_⟩
    simp only [BAPsiEdge.map]
    rcases hh with ⟨a, b⟩ | ⟨a, b⟩
    · left; exact ⟨by rw [a], by rw [b]⟩
    · right; exact ⟨by rw [a], by rw [b]⟩
  · right
    refine ⟨BAMEdge.map (owxEmb k) e, h3 e he, ?_⟩
    simp only [BAMEdge.map]
    rcases hh with ⟨a, b⟩ | ⟨a, b⟩
    · left; exact ⟨by rw [a], by rw [b]⟩
    · right; exact ⟨by rw [a], by rw [b]⟩

theorem BASim_Ext_sameAtom {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} (h : BASim_Ext Γ k T) {u v : E ⊕ I}
    (huv : v ∈ Γ.atom u) : T.sameAtom (owxEmb k u) (owxEmb k v) = true :=
  BASim_sameAtom_of_mem Γ T (fun a b hab => by
    simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff]
    exact Relation.ReflTransGen.single (BASim_Ext_atomAdj h a b hab)) huv

theorem BASim_splitG_normal {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} (h : BASim_Ext Γ k T) (hN : Γ.Normal) :
    ∀ T' ∈ T.splitG, T'.Normal := by
  intro T' hT'
  refine ⟨?_, BAGraph.splitG_circ T T' hT'⟩
  rw [(BAGraph.splitG_edges T T' hT').2.1, h.1]
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  exact hN.1 e0 he0


theorem BASim_sameAtom_of_adj (A : BAGraph E I) {u v : E ⊕ I} (h : A.atomAdj u v = true) : A.sameAtom u v = true := by
  simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff]; exact Relation.ReflTransGen.single h

theorem BASim_extraDot_atomAdj {T Tt : BAGraph E I} {d : BAMEdge (E ⊕ I)} (h : BASim_ExtraDot T Tt d) (hd : T.sameAtom d.x d.y = true) :
    (∀ u v, Tt.atomAdj u v = true → T.sameAtom u v = true) ∧ (∀ u v, T.atomAdj u v = true → Tt.sameAtom u v = true) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hdo : Tt.dotted = T.dotted := congrArg LGraph.dotted h1
  have hAS : ∀ (A : BAGraph E I) x y, A.sameAtom x y = true ↔ atomSetoid A x y := BASim_sameAtom_iff
  refine ⟨fun u v huv => ?_, fun u v huv => ?_⟩
  · simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, hdo, h2] at huv
    rcases huv with (huv | huv) | ⟨x, hx, hxy⟩
    · have : T.atomAdj u v = true := by
        simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact Or.inl (Or.inl huv)
      exact BASim_sameAtom_of_adj _ this
    · have : T.atomAdj u v = true := by
        simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact Or.inl (Or.inr huv)
      exact BASim_sameAtom_of_adj _ this
    · rcases (h3 x).1 hx with hx | rfl
      · have : T.atomAdj u v = true := by
          simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          exact Or.inr ⟨x, hx, hxy⟩
        exact BASim_sameAtom_of_adj _ this
      · rw [hAS] at hd ⊢
        rcases hxy with ⟨a, b⟩ | ⟨a, b⟩
        · rw [← a, ← b]; exact hd
        · rw [← a, ← b]; exact (atomSetoid T).symm hd
  · have : Tt.atomAdj u v = true := by
      simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, hdo, h2] at huv ⊢
      rcases huv with (huv | huv) | ⟨x, hx, hxy⟩
      · exact Or.inl (Or.inl huv)
      · exact Or.inl (Or.inr huv)
      · exact Or.inr ⟨x, (h3 x).2 (Or.inl hx), hxy⟩
    exact BASim_sameAtom_of_adj _ this


/-- **Lemma E for a family of terms** (E, the pinned `BAExtraGood` at one family): an `M`-split `T'` of a term of the family at a normal graph `Γ` that is extra for `Γ` has a higher order than `Γ`, or fewer atoms with an
external vertex.  The proof joins the two atoms of `Γ` by an `M`-dotted edge: `Γ̃`; `T'` is then an `M`-split of the term at `Γ̃` with the same atoms; `ord Γ̃ ≤ ord T'` (the merged lemmas, `hmono`) and
`ord Γ̃ = ord Γ + 2 (n_A Γ - n_A Γ̃)`; if both atoms have an external vertex, `nExt` falls. -/
theorem BASim_extra_E {k : ℕ} (Γ : BAGraph E I) (hN : Γ.Normal) (F : BAGraph E I → List (BAGraph E (I ⊕ Fin k)))
    (hF : ∀ (Γ' : BAGraph E I) (d : BAMEdge (E ⊕ I)), ∀ T ∈ F Γ', ∃ Tt ∈ F (Γ'.addM d), BASim_ExtraDot T Tt (BAMEdge.map (owxEmb k) d))
    (hExt : ∀ (Γ' : BAGraph E I), ∀ T ∈ F Γ', BASim_Ext Γ' k T)
    (hmono : ∀ Γ' : BAGraph E I, Γ'.Normal → Γ'.solid = Γ.solid → ∀ T ∈ F Γ', ((Γ'.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)
    {T : BAGraph E (I ⊕ Fin k)} (hT : T ∈ F Γ) {T' : BAGraph E (I ⊕ Fin k)} (hT' : T' ∈ T.splitG)
    (hex : Γ.extraB (owxEmb k) T' = true) :
    Γ.scalingOrder < T'.scalingOrder ∨ T'.nExt < Γ.nExt := by
  classical
  have hExtT := hExt Γ T hT
  have hExtT' := BASim_Ext_split hExtT T' hT'
  simp only [BAGraph.extraB, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hex
  obtain ⟨e, he, hne, hsame⟩ := hex
  set d : BAMEdge (E ⊕ I) := bpM e.src e.dst with hd
  set Γt := Γ.addM d with hΓt
  have hNt : Γt.Normal := hN
  obtain ⟨Tt, hTt, hdot⟩ := hF Γ d T hT
  obtain ⟨Tt', hTt', hdot'⟩ := BASim_extraDot_split hdot T' hT'
  have hm := (BAGraph.le_scalingOrderG_iff Tt Γt.scalingOrder).1 (hmono Γt hNt rfl Tt hTt) Tt'.packMerge
    (List.mem_map.2 ⟨Tt', hTt', rfl⟩)
  have hNTt' : Tt'.Normal := BASim_splitG_normal (hExt Γt Tt hTt) hNt Tt' hTt'
  have hpm : Tt'.packMerge.counters = Tt'.counters := BAWeightOp_packMerge_counters Tt' hNTt'
  obtain ⟨hA1, hA2⟩ := BASim_extraDot_atomAdj hdot' (by simpa [hd, bpM, BAMEdge.map] using hsame)
  have hcong := (BASim_counters_congr hdot'.1 hA1 hA2).1
  have hord : Γt.scalingOrder ≤ T'.scalingOrder := by
    have : Tt'.packMerge.scalingOrder = ord Tt'.packMerge.counters := rfl
    unfold BAGraph.scalingOrder
    have h2 : Tt'.packMerge.scalingOrder = ord T'.counters := by rw [this, hpm, hcong]
    rw [← h2]; exact hm
  by_cases hint : (∀ w ∈ Γ.atom e.src, w.isRight = true) ∨ (∀ w ∈ Γ.atom e.dst, w.isRight = true)
  · left
    have hA : Γt.nA + 1 ≤ Γ.nA := BASim_nA_addM Γ e.src e.dst d ⟨rfl, rfl⟩ hne hint
    have e1 : Γt.nS = Γ.nS := rfl
    have e2 : Γt.nW = Γ.nW := rfl
    have h1 : Γt.scalingOrder = (Γ.nS : ℤ) + 2 * ((Γ.nW : ℤ) - Γt.nA) := by
      simp only [BAGraph.scalingOrder, BAGraph.counters, ord, e1, e2]
    have h2 : Γ.scalingOrder = (Γ.nS : ℤ) + 2 * ((Γ.nW : ℤ) - Γ.nA) := by
      simp only [BAGraph.scalingOrder, BAGraph.counters, ord]
    omega
  · right
    push Not at hint
    obtain ⟨⟨w1, hw1, hw1'⟩, ⟨w2, hw2, hw2'⟩⟩ := hint
    obtain ⟨a, rfl⟩ : ∃ a : E, w1 = Sum.inl a := by
      rcases w1 with a | b
      · exact ⟨a, rfl⟩
      · simp at hw1'
    obtain ⟨b, rfl⟩ : ∃ b : E, w2 = Sum.inl b := by
      rcases w2 with a | b
      · exact ⟨a, rfl⟩
      · simp at hw2'
    have hco : ∀ u v, Γ.atomAdj u v = true → T'.sameAtom (owxEmb k u) (owxEmb k v) = true := fun u v h =>
      BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj hExtT' u v h)
    refine (BASim_nExt_le Γ T' hco).2 ⟨a, b, ?_, ?_⟩
    · intro heq
      have h1 : Γ.atom e.src = Γ.atom (Sum.inl a) := (BAVocab_atom_eq_of_mem Γ hw1).symm
      have h2 : Γ.atom e.dst = Γ.atom (Sum.inl b) := (BAVocab_atom_eq_of_mem Γ hw2).symm
      have : e.dst ∈ Γ.atom e.src := by rw [h1, heq, ← h2]; exact BAVocab_self_mem_atom Γ e.dst
      simp [BAGraph.sameAtom, this] at hne
    · have s1 := BASim_Ext_sameAtom hExtT' hw1
      have s2 := BASim_Ext_sameAtom hExtT' hw2
      have hAS : ∀ (A : BAGraph E (I ⊕ Fin k)) x y, A.sameAtom x y = true ↔ atomSetoid A x y := BASim_sameAtom_iff
      rw [hAS] at s1 s2 hsame ⊢
      exact (atomSetoid T').trans ((atomSetoid T').symm s1) ((atomSetoid T').trans hsame s2)


/-- the merge of a graph without `=`-dotted edges has the atoms with an external vertex of the graph (the merge is a relabelling) -/
theorem BASim_merge_nExt (T : BAGraph E I) (hT : ∀ e ∈ T.dotted, e.eq = false) : T.merge.nExt = T.nExt := by
  classical
  have hinj := BAVocab_vmap_injective T.toLGraph hT
  have hsurj := BAVocab_vmap_surjective T.toLGraph
  have hat : ∀ v, T.merge.atom (T.toLGraph.vmap v) = (T.atom v).image T.toLGraph.vmap := by
    intro v
    ext w'
    obtain ⟨w, rfl⟩ := hsurj w'
    rw [Finset.mem_image]
    have key : T.toLGraph.vmap w ∈ T.merge.atom (T.toLGraph.vmap v) ↔ w ∈ T.atom v := by
      have := BASim_merge_sameAtom T hT v w
      simp only [BAGraph.sameAtom] at this
      exact decide_eq_decide.1 this
    constructor
    · intro h; exact ⟨w, key.1 h, rfl⟩
    · rintro ⟨x, hx, hxw⟩
      rw [key]
      rwa [← hinj hxw]
  have hS : (Finset.univ.filter fun w : T.toLGraph.ExtCls ⊕ T.toLGraph.IntCls => w.isLeft = true) =
      (Finset.univ.filter fun v : E ⊕ I => v.isLeft = true).image T.toLGraph.vmap := by
    ext w'
    obtain ⟨w, rfl⟩ := hsurj w'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    have h1 := lwVmap_isRight T.toLGraph hT w
    constructor
    · intro h
      refine ⟨w, ?_, rfl⟩
      rcases hvm : T.toLGraph.vmap w with x | y <;> rw [hvm] at h h1 <;> rcases w with a | b <;> simp_all
    · rintro ⟨v, hv, hvw⟩
      obtain rfl := hinj hvw
      rcases hvm : T.toLGraph.vmap v with x | y <;> rw [hvm] at h1 <;> rcases v with a | b <;> simp_all
  unfold BAGraph.nExt
  rw [hS, Finset.image_image]
  have : (T.merge.atom ∘ T.toLGraph.vmap) = (Finset.image T.toLGraph.vmap) ∘ T.atom := funext fun v => by
    simp only [Function.comp_apply, hat]
  rw [this, ← Finset.image_image]
  exact Finset.card_image_of_injective _ (Finset.image_injective hinj)


/-- the invariants of the output `P.outOf T'` of a normal term: those of `T'` (the merge of a graph without `=`-dotted edges is a relabelling) -/
theorem BASim_outOf_inv {E0 : Type} (P : BAPGraph E0) {I' : Type} [Fintype I'] [DecidableEq I'] (T' : BAGraph P.E' I') (hN : T'.Normal) :
    (P.outOf T').g.scalingOrder = T'.scalingOrder ∧ (P.outOf T').g.nExt = T'.nExt := by
  refine ⟨?_, BASim_merge_nExt T' hN.1⟩
  have h := BAWeightOp_packMerge_counters T' hN
  change ord (T'.merge.counters) = ord (T'.counters)
  exact congrArg ord h

/-- the three facts about a family of terms `F` at `Γ` that Lemma E uses: the extra `M`-dot transfers, the terms extend the graph, `ord Γ' ≤ ordG T` at every normal graph with the same solid edges -/
structure BASim_Fam {E0 I0 : Type} [Fintype E0] [DecidableEq E0] [Fintype I0] [DecidableEq I0] (Γ : BAGraph E0 I0) (k : ℕ)
    (F : BAGraph E0 I0 → List (BAGraph E0 (I0 ⊕ Fin k))) : Prop where
  hF : ∀ (Γ' : BAGraph E0 I0) (d : BAMEdge (E0 ⊕ I0)), ∀ T ∈ F Γ', ∃ Tt ∈ F (Γ'.addM d), BASim_ExtraDot T Tt (BAMEdge.map (owxEmb k) d)
  hExt : ∀ (Γ' : BAGraph E0 I0), ∀ T ∈ F Γ', BASim_Ext Γ' k T
  hmono : ∀ Γ' : BAGraph E0 I0, Γ'.Normal → Γ'.solid = Γ.solid → ∀ T ∈ F Γ', ((Γ'.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG

/-- **Lemma E for the outputs of one kind of term**: an output tagged `e1`/`e2` (extra for the parent) rises in order or loses an external atom -/
theorem BASim_extra_out {E0 : Type} (P : BAPGraph E0) (hN : P.g.Normal) {k : ℕ} {F : BAGraph P.E' P.I' → List (BAGraph P.E' (P.I' ⊕ Fin k))}
    (hFam : BASim_Fam P.g k F)
    (tg : BAGraph P.E' (P.I' ⊕ Fin k) → BAShape) (htg : ∀ T', (tg T' = BAShape.e1 ∨ tg T' = BAShape.e2) → P.g.extraB (owxEmb k) T' = true)
    (Ts : List (BAGraph P.E' (P.I' ⊕ Fin k))) (hTs : ∀ T ∈ Ts, T ∈ F P.g) {t : BAShape} {Q : BAPGraph E0} (ht : t = BAShape.e1 ∨ t = BAShape.e2)
    (hQ : (t, Q) ∈ P.outsT tg Ts) : P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt := by
  obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P tg Ts t Q hQ
  have hex := htg T' (htag ▸ ht)
  have hNT' := BASim_splitG_normal (hFam.hExt P.g T (hTs T hT)) hN T' hT'
  rw [(BASim_outOf_inv P T' hNT').1, (BASim_outOf_inv P T' hNT').2]
  exact BASim_extra_E P.g hN F hFam.hF hFam.hExt hFam.hmono (hTs T hT) hT' hex

/-- an output of a term whose tag is not `e1`/`e2` is not an output of Lemma E -/
theorem BASim_tag_const {E0 : Type} (P : BAPGraph E0) {I' : Type} [Fintype I'] [DecidableEq I'] (sh : BAShape) (hsh : sh ≠ BAShape.e1 ∧ sh ≠ BAShape.e2)
    (Ts : List (BAGraph P.E' I')) {t : BAShape} {Q : BAPGraph E0} (ht : t = BAShape.e1 ∨ t = BAShape.e2)
    (hQ : (t, Q) ∈ P.outsT (fun _ => sh) Ts) : False := by
  obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P (fun _ => sh) Ts t Q hQ
  rcases ht with h | h <;> subst h
  · exact hsh.1 htag
  · exact hsh.2 htag

theorem BASim_htg_std {E0 I0 : Type} [Fintype E0] [DecidableEq E0] [Fintype I0] [DecidableEq I0] (Γ : BAGraph E0 I0) (k : ℕ) (T' : BAGraph E0 (I0 ⊕ Fin k))
    (h : Γ.tagStd k T' = BAShape.e1 ∨ Γ.tagStd k T' = BAShape.e2) : Γ.extraB (owxEmb k) T' = true := by
  by_contra hc
  have hc' : Γ.extraB (owxEmb k) T' = false := by simpa using hc
  simp [BAGraph.tagStd, hc'] at h

theorem BASim_htg_T1 {E0 I0 : Type} [Fintype E0] [DecidableEq E0] [Fintype I0] [DecidableEq I0] (Γ : BAGraph E0 I0) (T' : BAGraph E0 (I0 ⊕ Fin 2))
    (h : Γ.tagT1 T' = BAShape.e1 ∨ Γ.tagT1 T' = BAShape.e2) : Γ.extraB (owxEmb 2) T' = true := by
  by_contra hc
  have hc' : Γ.extraB (owxEmb 2) T' = false := by simpa using hc
  simp [BAGraph.tagT1, hc'] at h


/-! ### The families of terms -/

theorem BASim_hcirc {Γ : BAGraph E I} (hN : Γ.Normal) {p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid) :
    ∀ e ∈ p.2, e.circ = true := fun e he => hN.2 e ((lwSplit_perm Γ.solid p hp).mem_iff.2 (List.mem_cons_of_mem _ he))

/-- the family of the first group of a weight step: `lw2` -/
theorem BASim_fam_lw2 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (h1 : p.1.σ = true)
    (h2 : p.1.circ = true) : BASim_Fam Γ 2 (fun Γ' => Γ'.lw2 p) where
  hF := fun Γ' d T hT => by
    simp only [BAGraph.lw2, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact ⟨_, by simp [BAGraph.lw2], BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
    · exact ⟨BAGraph.lanlwD (Γ'.addM d) p q, by simp only [BAGraph.lw2, List.mem_cons, List.mem_map]; exact Or.inr ⟨q, hq, rfl⟩,
        BASim_extraDot_lanlwExt Γ' d q.2 1 _ _ _⟩
  hExt := fun Γ' T hT => by
    simp only [BAGraph.lw2, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact BASim_Ext_ext 2 Γ' _ _ _ _
    · exact BASim_Ext_lanlwExt Γ' q.2 1 _ _ _
  hmono := fun Γ' hN' hsol T hT => (lw_scalingOrderG Γ' p (hsol ▸ hp) h1 h2 hN').1 T hT

/-- `lw4` -/
theorem BASim_fam_lw4 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (h1 : p.1.σ = true)
    (h2 : p.1.circ = true) : BASim_Fam Γ 4 (fun Γ' => Γ'.lw4 p) where
  hF := fun Γ' d T hT => by
    simp only [BAGraph.lw4, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact ⟨_, by simp [BAGraph.lw4], BASim_extraDot_ext 4 Γ' d _ _ _ _⟩
    · exact ⟨_, by simp only [BAGraph.lw4, List.mem_cons, List.mem_map]; exact Or.inr ⟨q, hq, rfl⟩, BASim_extraDot_ext 4 Γ' d _ _ _ _⟩
  hExt := fun Γ' T hT => by
    simp only [BAGraph.lw4, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact BASim_Ext_ext 4 Γ' _ _ _ _
    · exact BASim_Ext_ext 4 Γ' _ _ _ _
  hmono := fun Γ' hN' hsol T hT => (lw_scalingOrderG Γ' p (hsol ▸ hp) h1 h2 hN').2 T hT

/-- the terms of `lanlw`: `T1` and the derivative terms -/
theorem BASim_fam_lanlw (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (h1 : p.1.σ = true)
    (h2 : p.1.circ = true) : BASim_Fam Γ 2 (fun Γ' => BAGraph.lanlwTerms Γ' p) where
  hF := fun Γ' d T hT => by
    simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact ⟨BAGraph.lanlwT1 (Γ'.addM d) p, by simp [BAGraph.lanlwTerms], BASim_extraDot_lanlwExt Γ' d p.2 1 _ _ _⟩
    · exact ⟨BAGraph.lanlwD (Γ'.addM d) p q, by simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map]; exact Or.inr ⟨q, hq, rfl⟩,
        BASim_extraDot_lanlwExt Γ' d q.2 1 _ _ _⟩
  hExt := fun Γ' T hT => by
    simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact BASim_Ext_lanlwExt Γ' p.2 1 _ _ _
    · exact BASim_Ext_lanlwExt Γ' q.2 1 _ _ _
  hmono := fun Γ' hN' hsol T hT => lanlw_scalingOrderG Γ' p (hsol ▸ hp) h1 h2 hN' T hT

/-- `gg2`, `gg4` -/
theorem BASim_fam_gg2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    BASim_Fam Γ 2 (fun Γ' => Γ'.gg2 p q) where
  hF := fun Γ' d T hT => by
    rw [BAGGOp_gg2_eq] at hT
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
    rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, hr, rfl⟩
    · exact ⟨BAGGOp_A1 (Γ'.addM d) p q, by rw [BAGGOp_gg2_eq]; simp, BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
    · exact ⟨BAGGOp_A2 (Γ'.addM d) p q, by rw [BAGGOp_gg2_eq]; simp, BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
    · exact ⟨BAGGOp_A3 (Γ'.addM d) p q, by rw [BAGGOp_gg2_eq]; simp, BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
    · exact ⟨BAGGOp_A4 (Γ'.addM d) p q, by rw [BAGGOp_gg2_eq]; simp, BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
    · exact ⟨BAGGOp_A5 (Γ'.addM d) p q, by rw [BAGGOp_gg2_eq]; simp, BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
    · exact ⟨BAGGOp_AD (Γ'.addM d) p q r, by rw [BAGGOp_gg2_eq]; simp only [List.mem_append, List.mem_map]; exact Or.inr ⟨r, hr, rfl⟩,
        BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
  hExt := fun Γ' T hT => by
    rw [BAGGOp_gg2_eq] at hT
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
    rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, hr, rfl⟩ <;> exact BASim_Ext_ext 2 Γ' _ _ _ _
  hmono := fun Γ' hN' hsol T hT => (gg_scalingOrderG Γ' p q (hsol ▸ hp) hq hN').1 T hT

theorem BASim_fam_gg4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    BASim_Fam Γ 4 (fun Γ' => Γ'.gg4 p q) where
  hF := fun Γ' d T hT => by
    rw [BAGGOp_gg4_eq] at hT
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
    rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩
    · exact ⟨BAGGOp_B1 (Γ'.addM d) p q, by rw [BAGGOp_gg4_eq]; simp, BASim_extraDot_ext 4 Γ' d _ _ _ _⟩
    · exact ⟨BAGGOp_B2 (Γ'.addM d) p q, by rw [BAGGOp_gg4_eq]; simp, BASim_extraDot_ext 4 Γ' d _ _ _ _⟩
    · exact ⟨BAGGOp_BD (Γ'.addM d) p q r, by rw [BAGGOp_gg4_eq]; simp only [List.mem_append, List.mem_map]; exact Or.inr ⟨r, hr, rfl⟩,
        BASim_extraDot_ext 4 Γ' d _ _ _ _⟩
  hExt := fun Γ' T hT => by
    rw [BAGGOp_gg4_eq] at hT
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
    rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩ <;> exact BASim_Ext_ext 4 Γ' _ _ _ _
  hmono := fun Γ' hN' hsol T hT => (gg_scalingOrderG Γ' p q (hsol ▸ hp) hq hN').2 T hT


private theorem BASim_ordG_of_split {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (T : BAGraph E' I') (k : ℤ)
    (h : ∀ Δs ∈ T.splitG, Δs.Normal ∧ k ≤ ord Δs.counters) : ((k : ℤ) : WithTop ℤ) ≤ T.scalingOrderG := by
  rw [BAGraph.le_scalingOrderG_iff]
  intro P hP
  simp only [BAGraph.partition, List.mem_map] at hP
  obtain ⟨Δs, hΔs, rfl⟩ := hP
  obtain ⟨hNs, hge⟩ := h Δs hΔs
  change k ≤ ord Δs.packMerge.counters
  rw [BAWeightOp_packMerge_counters Δs hNs]
  exact hge

/-- the first group of the within-atom edge step: the leaf and the derivative terms (`W.first`, `W.D`) -/
def BASim_Fwithin (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (Γ : BAGraph E I) : List (BAGraph E (I ⊕ Fin 2)) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] ::
    (lwSplit p.2).map (BAGraph.lanlwD Γ p)

theorem BASim_fam_within (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (h1 : p.1.σ = true)
    (h2 : p.1.circ = true) : BASim_Fam Γ 2 (BASim_Fwithin p) where
  hF := fun Γ' d T hT => by
    simp only [BASim_Fwithin, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact ⟨_, by simp [BASim_Fwithin], BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
    · exact ⟨BAGraph.lanlwD (Γ'.addM d) p q, by simp only [BASim_Fwithin, List.mem_cons, List.mem_map]; exact Or.inr ⟨q, hq, rfl⟩,
        BASim_extraDot_lanlwExt Γ' d q.2 1 _ _ _⟩
  hExt := fun Γ' T hT => by
    simp only [BASim_Fwithin, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · exact BASim_Ext_ext 2 Γ' _ _ _ _
    · exact BASim_Ext_lanlwExt Γ' q.2 1 _ _ _
  hmono := fun Γ' hN' hsol T hT => by
    have hp' : p ∈ lwSplit Γ'.solid := hsol ▸ hp
    simp only [BASim_Fwithin, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, hq, rfl⟩
    · have hl := lwSplit_snd_length Γ'.solid p hp'
      refine BASim_ordG_of_split _ _ (BAExpandWOrd_ext_ge Γ' hN' p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] p.1.src
        (BASim_hcirc hN' hp') (by simp only [BAGraph.nS]; simp; omega) ?_)
      intro r hr
      simp [baSplitSolid, bpS] at hr
      subst hr
      exact Or.inl (by simp)
    · exact lanlw_scalingOrderG Γ' p hp' h1 h2 hN' _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hq))

/-- the `M`-splits of the shape `X.d1`: `G_{y'β}`, a circled edge, `G_{βy}` -/
private theorem BASim_hs_d1 {V : Type} (e1 a e3 : SEdge V) (h1 : e1.circ = false) (ha : a.circ = true) (h3 : e3.circ = false) (b : V)
    (hb1 : (e1.src = b ∧ e1.dst ≠ b) ∨ (e1.dst = b ∧ e1.src ≠ b)) :
    ∀ r ∈ baSplitSolid [e1, a, e3], r.2.length ≤ 1 ∨ (r.2.length ≤ 3 ∧ ∃ m ∈ r.2, (m.x = b ∧ m.y ≠ b) ∨ (m.y = b ∧ m.x ≠ b)) := by
  intro r hr
  simp only [baSplitSolid, ha, h1, h3, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · left; simp
  · left; simp
  · left; simp
  · right
    refine ⟨by simp, _, List.mem_cons_self, ?_⟩
    simpa using hb1

/-- the stage-1 term `X.d1` of macro (b) -/
def BASim_Fd1 (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (Γ : BAGraph E I) : List (BAGraph E (I ⊕ Fin 2)) :=
  [BAGraph.ext 2 Γ q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)]
    [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]]

theorem BASim_fam_d1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    BASim_Fam Γ 2 (BASim_Fd1 p q) where
  hF := fun Γ' d T hT => by
    simp only [BASim_Fd1, List.mem_singleton] at hT
    subst hT
    exact ⟨_, by simp [BASim_Fd1], BASim_extraDot_ext 2 Γ' d _ _ _ _⟩
  hExt := fun Γ' T hT => by
    simp only [BASim_Fd1, List.mem_singleton] at hT
    subst hT
    exact BASim_Ext_ext 2 Γ' _ _ _ _
  hmono := fun Γ' hN' hsol T hT => by
    have hp' : p ∈ lwSplit Γ'.solid := hsol ▸ hp
    simp only [BASim_Fd1, List.mem_singleton] at hT
    subst hT
    have hl := lwSplit_snd_length Γ'.solid p hp'
    have hl' := lwSplit_snd_length p.2 q hq
    have hcirc' : ∀ e ∈ q.2, e.circ = true := fun e he =>
      BASim_hcirc hN' hp' e ((lwSplit_perm p.2 q hq).mem_iff.2 (List.mem_cons_of_mem _ he))
    refine BASim_ordG_of_split _ _ (BAExpandWOrd_ext_ge Γ' hN' q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst),
      bpS false (bpv 1) (owxEmb 2 p.1.dst)] p.1.src hcirc' (by simp only [BAGraph.nS]; simp; omega) ?_)
    intro r hr
    exact BASim_hs_d1 _ _ _ rfl rfl rfl (bpv 1) (Or.inr ⟨rfl, fun h => lwSymm_emb_ne q.1.src 2 1 h.symm⟩) r hr


/-- **Item 4, Lemma E at graph level: `BAExtraGood`** -- an output tagged `e1`/`e2` (extra for the parent, `extraB`) of a tagged frame step at a normal graph has a higher order or fewer external atoms -/
theorem baExtraGood_holds : BAExtraGood := by
  intro E0 P LT hst hN Q hQ
  obtain ⟨t, ht, hQ⟩ : ∃ t, (t = BAShape.e1 ∨ t = BAShape.e2) ∧ (t, Q) ∈ LT := by
    rcases hQ with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hmacro : ∀ sh : BAShape, (sh ≠ BAShape.e1 ∧ sh ≠ BAShape.e2) → ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')),
      (t, Q) ∈ P.outsT (fun _ => sh) Ts → P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt := fun sh hsh I' _ _ Ts h =>
    (BASim_tag_const P sh hsh Ts ht h).elim
  cases hst with
  | weight p hp h =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BASim_extra_out P hN (BASim_fam_lw2 P.g p hp h.1 h.2.1) _ (BASim_htg_std P.g 2) _ (fun T hT => hT) ht hQ
    · exact BASim_extra_out P hN (BASim_fam_lw4 P.g p hp h.1 h.2.1) _ (BASim_htg_std P.g 4) _ (fun T hT => hT) ht hQ
  | within p hp h =>
    unfold BAPGraph.withinOutsT at hQ
    rcases List.mem_append.1 hQ with hQ | hQ
    · rcases List.mem_append.1 hQ with hQ | hQ
      · exact BASim_extra_out P hN (BASim_fam_within P.g p hp h.1 h.2.1) _ (BASim_htg_std P.g 2) _ (fun T hT => hT) ht hQ
      · exact hmacro BAShape.macroA (by simp) _ hQ
    · exact hmacro BAShape.macroA (by simp) _ hQ
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BASim_extra_out P hN (BASim_fam_lanlw P.g p hp h.1 h.2) _ (BASim_htg_T1 P.g) _
        (fun T hT => by rw [List.mem_singleton] at hT; subst hT; exact List.mem_cons_self) ht hQ
    · exact BASim_extra_out P hN (BASim_fam_lanlw P.g p hp h.1 h.2) _ (BASim_htg_std P.g 2) _
        (fun T hT => List.mem_cons_of_mem _ hT) ht hQ
  | gg p hp q hq h x hx hwf hint hnb =>
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BASim_extra_out P hN (BASim_fam_gg2 P.g p q hp hq) _ (BASim_htg_std P.g 2) _ (fun T hT => hT) ht hQ
    · exact BASim_extra_out P hN (BASim_fam_gg4 P.g p q hp hq) _ (BASim_htg_std P.g 4) _ (fun T hT => hT) ht hQ
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    have hq : q ∈ lwSplit p.2 := List.mem_of_getElem? hj
    unfold BAPGraph.splitOutsT at hQ
    simp only [List.mem_append] at hQ
    rcases hQ with ((((hQ | hQ) | hQ) | hQ) | hQ) | hQ
    · exact BASim_extra_out P hN (BASim_fam_lanlw P.g p hp h.1 h.2.1) _ (BASim_htg_T1 P.g) _
        (fun T hT => by rw [List.mem_singleton] at hT; subst hT; exact List.mem_cons_self) ht hQ
    · exact BASim_extra_out P hN (BASim_fam_lanlw P.g p hp h.1 h.2.1) _ (BASim_htg_std P.g 2) _
        (fun T hT => by
          obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hT
          exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_mem_eraseIdx hq'))) ht hQ
    · exact BASim_extra_out P hN (BASim_fam_d1 P.g p q hp hq) _ (BASim_htg_std P.g 2) _ (fun T hT => hT) ht hQ
    · exact hmacro BAShape.macroB (by simp) _ hQ
    · exact hmacro BAShape.macroB (by simp) _ hQ
    · exact hmacro BAShape.macroB (by simp) _ hQ

end ExtraE

end RBM.Graph

end
