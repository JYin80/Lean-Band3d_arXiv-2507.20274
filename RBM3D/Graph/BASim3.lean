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

end RBM.Graph

end
