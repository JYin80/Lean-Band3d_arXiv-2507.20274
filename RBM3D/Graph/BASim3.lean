/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASim2

/-!
# BA-L R1 `BASim` (T2423), part 3: a BA step matched with a band `LocStep` at the image

Stage 1 of macro (b) (`BAFrameStepT.ggSplit`) and `baMatch_holds : BAMatch m`; Lemma E at graph
level (`baExtraGood_holds : BAExtraGood`: the families of terms, `BASim_extra_E`); the
conservative extensions and the invariants of the transfer graphs of the macro steps
(`BASim_Cons`, `BASim_inv_trA`, `BASim_trB_facts`); the terms `d2`, `d3`, `d4` and stage 2 of the
macro steps (`BASim_macroA`, `BASim_macroB1`, `BASim_macroB2`); `baSim'_holds : BAsim' m`; the
compiled instances of `baMatch_holds`, `baExtraGood_holds` and `baSim'_holds`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open private lwExists_mem_dedupPairs lwMem_of_mem_dedupPairs from RBM3D.Graph.LWVocab
open private BAVocab_vmap_injective BAVocab_vmap_surjective BAVocab_merge_atomAdj BAVocab_merge_dotted_eq from RBM3D.Graph.BAVocab
open private BAAtomic_solidAt BAAtomic_charge BAAtomic_fm BAAtomic_exists_inr_vmap from RBM3D.Graph.BAAtomic
open private BAWeightOp_packMerge_counters BAWeightOp_nExt_add_nA BAWeightOp_atom_subset BAWeightOp_nA_le from RBM3D.Graph.BAWeightOp
open private BAVocab_atom_eq_of_mem BAVocab_self_mem_atom from RBM3D.Graph.BAVocab
open private lwVmap_isRight from RBM3D.Graph.LWVocab
open private BAExpandWOrd_ext BAExpandWOrd_ext_ge from RBM3D.Graph.BAExpandWOrd

open private BAWeightOp_ext_atomAdj BAWeightOp_ext_normal BAWeightOp_splitG_of_circ from RBM3D.Graph.BAWeightOp
open private BAExpandWOrd_ext_counters from RBM3D.Graph.BAExpandWOrd
open private BAAtomic_pairs_eq BAAtomic_share_eq from RBM3D.Graph.BAAtomic
open private BASim_rtg_sub from RBM3D.Graph.BASim2

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

section Cons
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **A conservative extension** `T` of `Γ` by new internal vertices: `ρ` retracts the vertices of `T` onto those of `Γ` and every atom edge of `T` is read by `ρ` inside an atom of `Γ` -/
structure BASim_Cons (Γ : BAGraph E I) (k : ℕ) (T : BAGraph E (I ⊕ Fin k)) (ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I) : Prop where
  hρ : ∀ a, ρ (owxEmb k a) = a
  hext : ∀ u v, Γ.atomAdj u v = true → T.sameAtom (owxEmb k u) (owxEmb k v) = true
  hret : ∀ u' v', T.atomAdj u' v' = true → Γ.sameAtom (ρ u') (ρ v') = true

theorem BASim_Cons.atom_ret {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ)
    (x : E ⊕ I) {w : E ⊕ (I ⊕ Fin k)} (hw : w ∈ T.atom (owxEmb k x)) : ρ w ∈ Γ.atom x := by
  rw [BAGraph.mem_atom_iff] at hw
  induction hw with
  | refl => rw [h.hρ]; exact BAVocab_self_mem_atom Γ x
  | tail _ hbc ih =>
    have := h.hret _ _ hbc
    simp only [BAGraph.sameAtom, decide_eq_true_eq] at this
    exact (BAVocab_atom_eq_of_mem Γ ih) ▸ this

theorem BASim_Cons.sameAtom {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ)
    (x y : E ⊕ I) : T.sameAtom (owxEmb k x) (owxEmb k y) = Γ.sameAtom x y := by
  rw [Bool.eq_iff_iff]
  simp only [BAGraph.sameAtom, decide_eq_true_eq]
  constructor
  · intro hy
    have := h.atom_ret x hy
    rwa [h.hρ] at this
  · intro hy
    have := BASim_sameAtom_of_mem Γ T h.hext hy
    simpa [BAGraph.sameAtom] using this

/-- the atom of an old vertex of a conservative extension is internal iff it is internal in `Γ` (the new vertices are internal) -/
theorem BASim_Cons.intAtom {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ)
    (hnew : ∀ w : E ⊕ (I ⊕ Fin k), (∃ a, w = owxEmb k a) ∨ w.isRight = true) (x : E ⊕ I) :
    (∀ w ∈ T.atom (owxEmb k x), w.isRight = true) ↔ (∀ y ∈ Γ.atom x, y.isRight = true) := by
  constructor
  · intro hT y hy
    have := hT (owxEmb k y) (by
      have := BASim_sameAtom_of_mem Γ T h.hext hy
      simpa [BAGraph.sameAtom] using this)
    rcases y with a | b <;> simpa [owxEmb] using this
  · intro hΓ w hw
    rcases hnew w with ⟨a, rfl⟩ | hr
    · have := h.atom_ret x hw
      rw [h.hρ] at this
      have := hΓ a this
      rcases a with a | b <;> simpa [owxEmb] using this
    · exact hr

/-- the number of atoms with an external vertex is that of `Γ` -/
theorem BASim_Cons.nExt {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ) :
    T.nExt = Γ.nExt := by
  classical
  have hco := h.hext
  refine le_antisymm (BASim_nExt_le Γ T hco).1 ?_
  set S : Finset (E ⊕ I) := Finset.univ.filter fun v => v.isLeft = true with hS
  have himg : (Finset.univ.filter fun v : E ⊕ (I ⊕ Fin k) => v.isLeft = true).image T.atom = S.image (fun v => T.atom (owxEmb k v)) := by
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
  have key := BASim_card_image_le S (fun v => T.atom (owxEmb k v)) Γ.atom (fun u _ v _ hh => by
    have hv : owxEmb k v ∈ T.atom (owxEmb k u) := by rw [hh]; exact BAVocab_self_mem_atom T _
    have := h.atom_ret u hv
    rw [h.hρ] at this
    exact (BAVocab_atom_eq_of_mem Γ this).symm)
  have e1 : T.nExt = (S.image (fun v => T.atom (owxEmb k v))).card := by unfold BAGraph.nExt; rw [himg]
  rw [e1]
  exact key.1

theorem BASim_hnew (k : ℕ) : ∀ w : E ⊕ (I ⊕ Fin k), (∃ a, w = owxEmb k a) ∨ w.isRight = true := by
  rintro (a | i | j)
  · exact Or.inl ⟨Sum.inl a, rfl⟩
  · exact Or.inl ⟨Sum.inr i, rfl⟩
  · exact Or.inr rfl

theorem BASim_sameAtom_symm' (Γ : BAGraph E I) {u v : E ⊕ I} (h : Γ.sameAtom u v = true) : Γ.sameAtom v u = true := by
  rw [BASim_sameAtom_iff] at h ⊢; exact (atomSetoid Γ).symm h

/-- the extension of `Γ` by `α`, joined to `x` and `y` (in one atom of `Γ`) by `M`-dotted edges, and `β`, joined to nothing: the transfer graphs of the macro steps -/
def BASim_tr2 (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (x y : E ⊕ I) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ rest s w [bpM (owxEmb 2 x) (bpv 0), bpM (bpv 0) (owxEmb 2 y)]

theorem BASim_rho2_alpha (x y : E ⊕ I) : BAScost_rho2 x y (bpv 0 : E ⊕ (I ⊕ Fin 2)) = x := by simp [BAScost_rho2, bpv]

/-- **A conservative extension from its `M`-dotted edges**: `ρ` retracts the new vertices onto old ones, every new `M`-dotted edge is read by `ρ` inside an atom of `Γ'` (`Γ'` is `Γ` with some of its atoms joined) -/
theorem BASim_cons_of_md (Γ Γ' : BAGraph E I) {k : ℕ} (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I) (hρ : ∀ a, ρ (owxEmb k a) = a)
    (hΓ : ∀ a b, Γ.atomAdj a b = true → Γ'.sameAtom a b = true)
    (hΓ' : ∀ a b, Γ'.atomAdj a b = true → (BAGraph.ext k Γ rest s w md).sameAtom (owxEmb k a) (owxEmb k b) = true)
    (hmd : ∀ e ∈ md, Γ'.sameAtom (ρ e.x) (ρ e.y) = true) : BASim_Cons Γ' k (BAGraph.ext k Γ rest s w md) ρ where
  hρ := hρ
  hext := hΓ'
  hret := fun u' v' h => by
    rcases (BAWeightOp_ext_atomAdj k Γ rest s w md u' v').1 h with ⟨a, b, rfl, rfl, hab⟩ | ⟨e, he, hev⟩
    · rw [hρ, hρ]; exact hΓ a b hab
    · rcases hev with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hmd e he
      · exact BASim_sameAtom_symm' Γ' (hmd e he)

theorem BASim_Cons.nA_le {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ)
    (hatt : ∀ w : E ⊕ (I ⊕ Fin k), ∃ v, T.sameAtom (owxEmb k v) w = true) : T.nA ≤ Γ.nA := by
  classical
  set S : Finset (E ⊕ I) := Finset.univ.filter fun v => ∀ x ∈ Γ.atom v, x.isRight = true with hS
  have key := BASim_card_image_le S Γ.atom (fun v => T.atom (owxEmb k v)) (fun u _ v _ hh => by
    have hv : v ∈ Γ.atom u := by rw [hh]; exact BAVocab_self_mem_atom Γ v
    have := BASim_sameAtom_of_mem Γ T h.hext hv
    exact (BAVocab_atom_eq_of_mem T (by simpa [BAGraph.sameAtom] using this)).symm)
  have hsub : (Finset.univ.filter fun w : E ⊕ (I ⊕ Fin k) => ∀ x ∈ T.atom w, x.isRight = true).image T.atom ⊆ S.image (fun v => T.atom (owxEmb k v)) := by
    intro A hA
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨v, hv⟩ := hatt w
    have hv' : w ∈ T.atom (owxEmb k v) := by simpa [BAGraph.sameAtom] using hv
    have hat := BAVocab_atom_eq_of_mem T hv'
    refine Finset.mem_image.2 ⟨v, ?_, hat.symm⟩
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    have := hw (owxEmb k x) (by
      rw [hat]
      simpa [BAGraph.sameAtom] using BASim_sameAtom_of_mem Γ T h.hext hx)
    rcases x with a | b <;> simpa [owxEmb] using this
  exact (Finset.card_le_card hsub).trans key.1

theorem BASim_cons_tr2 (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (x y : E ⊕ I) (hxy : Γ.sameAtom x y = true) : BASim_Cons Γ 2 (BASim_tr2 Γ rest s w x y) (BAScost_rho2 x x) :=
  BASim_cons_of_md Γ Γ rest s w _ _ (BAScost_rho2_emb x x) (fun a b h => BASim_sameAtom_of_adj _ h)
    (fun a b h => BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj (BASim_Ext_ext 2 Γ rest s w _) a b h)) (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp only [bpM, BAScost_rho2_emb, BASim_rho2_alpha]; exact BAScost_sameAtom_self Γ x
      · simp only [bpM, BAScost_rho2_emb, BASim_rho2_alpha]; exact hxy)

/-- `β` is isolated in the transfer graph -/
theorem BASim_tr2_iso (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (x y : E ⊕ I) (v : E ⊕ (I ⊕ Fin 2)) : (BASim_tr2 Γ rest s w x y).atomAdj (bpv 1) v = false := by
  by_contra hc
  have hc' : (BASim_tr2 Γ rest s w x y).atomAdj (bpv 1) v = true := by simpa using hc
  rcases (BAWeightOp_ext_atomAdj 2 Γ rest s w _ _ _).1 hc' with ⟨a, b, h1, -, -⟩ | ⟨e, he, hev⟩
  · exact lwSymm_emb_ne a 2 1 h1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rcases hev with ⟨h, -⟩ | ⟨-, h⟩
      · exact lwSymm_emb_ne x 2 1 h.symm
      · simp [bpM, bpv] at h
    · rcases hev with ⟨h, -⟩ | ⟨-, h⟩
      · simp [bpM, bpv] at h
      · exact lwSymm_emb_ne y 2 1 h.symm

/-- the invariants `(ord, n_M, n_A - n_W, loops, n_S, pairs, nExt)` of a BA graph (`BAPGraph.baInv` of a packed graph) -/
def BASim_inv (T : BAGraph E I) : ℤ × ℕ × ℤ × ℕ × ℕ × ℕ × ℕ :=
  (T.scalingOrder, T.nM, (T.nA : ℤ) - T.nW, T.nLoops, T.nS, T.nPairs, T.nExt)

theorem BASim_pairsAux_perm (Γ : BAGraph E I) {l l' : List (SEdge (E ⊕ I))} (h : l.Perm l') : Γ.pairsAux l = Γ.pairsAux l' := by
  rw [← BAAtomic_pairs_eq, ← BAAtomic_pairs_eq]
  exact lvl1Pairs_perm _ (h.map _)

theorem BASim_nShare_comm (Γ : BAGraph E I) (e e' : SEdge (E ⊕ I)) : Γ.nShare e e' = Γ.nShare e' e := by
  rw [← BAAtomic_share_eq Γ e e', ← BAAtomic_share_eq Γ e' e]
  exact lvl1Share_comm _ _ _

/-- a loop (an edge inside an atom) shares nothing -/
theorem BASim_nShare_loop (Γ : BAGraph E I) (e e' : SEdge (E ⊕ I)) (h : Γ.sameAtom e'.src e'.dst = true) : Γ.nShare e e' = 0 := by
  unfold BAGraph.nShare; simp [h]

theorem BASim_pairsAux_append_loop (Γ : BAGraph E I) (e' : SEdge (E ⊕ I)) (h : Γ.sameAtom e'.src e'.dst = true) :
    ∀ l : List (SEdge (E ⊕ I)), Γ.pairsAux (l ++ [e']) = Γ.pairsAux l
  | [] => by simp [BAGraph.pairsAux]
  | a :: l => by
    simp only [List.cons_append, BAGraph.pairsAux, BASim_pairsAux_append_loop Γ e' h l, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, BASim_nShare_loop Γ a e' h]
    simp

theorem BASim_pairsAux_cons_loop (Γ : BAGraph E I) (e : SEdge (E ⊕ I)) (h : Γ.sameAtom e.src e.dst = true) (l : List (SEdge (E ⊕ I))) :
    Γ.pairsAux (e :: l) = Γ.pairsAux l := by
  have : (l.map (Γ.nShare e)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨e2, _, rfl⟩ := List.mem_map.1 hx
    unfold BAGraph.nShare; simp [h]
  simp [BAGraph.pairsAux, this]

theorem BASim_Cons.intAtom_eq {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ)
    (hnew : ∀ w : E ⊕ (I ⊕ Fin k), (∃ a, w = owxEmb k a) ∨ w.isRight = true) (x : E ⊕ I) : T.intAtom (owxEmb k x) = Γ.intAtom x := by
  unfold BAGraph.intAtom
  exact decide_eq_decide.2 (h.intAtom hnew x)

theorem BASim_Cons.pairsAux {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ)
    (hnew : ∀ w : E ⊕ (I ⊕ Fin k), (∃ a, w = owxEmb k a) ∨ w.isRight = true) :
    ∀ l : List (SEdge (E ⊕ I)), T.pairsAux (l.map (SEdge.map (owxEmb k))) = Γ.pairsAux l
  | [] => rfl
  | e :: l => by
    have hsh : ∀ e' : SEdge (E ⊕ I), T.nShare (SEdge.map (owxEmb k) e) (SEdge.map (owxEmb k) e') = Γ.nShare e e' := fun e' => by
      unfold BAGraph.nShare
      simp only [SEdge.map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, h.sameAtom, h.intAtom_eq hnew]
      split_ifs <;> simp
    simp only [List.map_cons, BAGraph.pairsAux, BASim_Cons.pairsAux h hnew l, List.map_map, Function.comp_def, hsh]

theorem BASim_Cons.nLoops_cnt {Γ : BAGraph E I} {k : ℕ} {T : BAGraph E (I ⊕ Fin k)} {ρ : E ⊕ (I ⊕ Fin k) → E ⊕ I} (h : BASim_Cons Γ k T ρ)
    (l : List (SEdge (E ⊕ I))) :
    (l.map (SEdge.map (owxEmb k))).countP (fun e => T.sameAtom e.src e.dst) = l.countP (fun e => Γ.sameAtom e.src e.dst) := by
  rw [List.countP_map]
  congr 1
  funext e
  simp only [Function.comp_apply, SEdge.map, h.sameAtom]

/-- the counters of the transfer graph of a macro step: those of the extension by `α`, `β` of `lanlw` (the dot `M_{αy}` joins what is joined) -/
theorem BASim_counters_tr2 (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (x y : E ⊕ I)
    (hxy : Γ.sameAtom x y = true) :
    (BASim_tr2 Γ rest s [bpW false (bpv 0) (bpv 1)] x y).counters = ⟨rest.length + s.length, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩ := by
  have hT0 : BASim_ExtraDot (BAExpandWOrd_ext Γ rest s x) (BASim_tr2 Γ rest s [bpW false (bpv 0) (bpv 1)] x y) (bpM (bpv 0) (owxEmb 2 y)) :=
    ⟨rfl, rfl, fun z => by simp [BASim_tr2, BAGraph.ext, BAExpandWOrd_ext, BAGraph.lanlwExt, bpM]; aesop⟩
  have hd : (BAExpandWOrd_ext Γ rest s x).sameAtom (bpM (bpv 0) (owxEmb 2 y)).x (bpM (bpv 0) (owxEmb 2 y)).y = true := by
    have h1 : atomSetoid (BAExpandWOrd_ext Γ rest s x) (owxEmb 2 x) (bpv 0) :=
      BAScost_atomSetoid_ext_md Γ rest s [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 x) (bpv 0)] (bpM (owxEmb 2 x) (bpv 0)) (by simp)
    have h2 : (BAExpandWOrd_ext Γ rest s x).sameAtom (owxEmb 2 x) (owxEmb 2 y) = true :=
      BASim_Ext_sameAtom (BASim_Ext_lanlwExt Γ rest 1 s _ _) (by simpa [BAGraph.sameAtom] using hxy)
    rw [BASim_sameAtom_iff] at h2 ⊢
    exact (atomSetoid _).trans ((atomSetoid _).symm h1) h2
  obtain ⟨h12, h21⟩ := BASim_extraDot_atomAdj hT0 hd
  have := (BASim_counters_congr hT0.1 h12 h21).1
  rw [this]
  exact BAExpandWOrd_ext_counters Γ rest s x

/-- **The invariants of the transfer graph of macro (a)** are those of `Γ` (`(M3)`): the edge `p.1` inside an atom is replaced by the loop `Ǧ_{ββ}` -/
theorem BASim_inv_trA (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hxy : Γ.sameAtom p.1.src p.1.dst = true) : BASim_inv (BAGraph.BAScost_trA Γ p) = BASim_inv Γ := by
  have hC := BASim_cons_tr2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)] p.1.src p.1.dst hxy
  have hnew := BASim_hnew (E := E) (I := I) 2
  have hl := lwSplit_snd_length Γ.solid p hp
  have hcnt := BASim_counters_tr2 Γ p.2 [bpS true (bpv 1) (bpv 1)] p.1.src p.1.dst hxy
  change BASim_inv (BASim_tr2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)] p.1.src p.1.dst) = BASim_inv Γ
  set tr := BASim_tr2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)] p.1.src p.1.dst with htr
  have hS : tr.nS = Γ.nS := by
    have := congrArg Counters.nS hcnt
    simp only [BAGraph.counters, List.length_singleton] at this
    simp only [BAGraph.nS] at this ⊢
    omega
  have hW : tr.nW = Γ.nW + 1 := congrArg Counters.nW hcnt
  have hA : tr.nA = Γ.nA + 1 := congrArg Counters.nV hcnt
  have hM : tr.nM = Γ.nM := congrArg Counters.nM hcnt
  have hLoops : tr.nLoops = Γ.nLoops := by
    have h1 : tr.nLoops = (p.2.map (SEdge.map (owxEmb 2))).countP (fun e => tr.sameAtom e.src e.dst) + 1 := by
      unfold BAGraph.nLoops
      change ((p.2.map (SEdge.map (owxEmb 2))) ++ [bpS true (bpv 1) (bpv 1)]).countP _ = _
      rw [List.countP_append]
      simp [bpS, BAScost_sameAtom_self]
    have h2 : Γ.nLoops = 1 + p.2.countP (fun e => Γ.sameAtom e.src e.dst) := by
      unfold BAGraph.nLoops
      rw [(lwSplit_perm Γ.solid p hp).countP_eq, List.countP_cons]
      simp [hxy]
      omega
    rw [h1, h2, hC.nLoops_cnt]
    omega
  have hPairs : tr.nPairs = Γ.nPairs := by
    have h1 : tr.nPairs = tr.pairsAux (p.2.map (SEdge.map (owxEmb 2))) := by
      unfold BAGraph.nPairs
      change tr.pairsAux ((p.2.map (SEdge.map (owxEmb 2))) ++ [bpS true (bpv 1) (bpv 1)]) = _
      exact BASim_pairsAux_append_loop tr _ (by simp [bpS, BAScost_sameAtom_self]) _
    rw [h1]
    unfold BAGraph.nPairs
    rw [hC.pairsAux hnew, BASim_pairsAux_perm Γ (lwSplit_perm Γ.solid p hp), BASim_pairsAux_cons_loop Γ p.1 hxy]
  have hExt := hC.nExt
  have hord : tr.scalingOrder = Γ.scalingOrder := by
    simp only [BAGraph.scalingOrder, BAGraph.counters, ord, hS, hW, hA]
    push_cast
    ring
  simp only [BASim_inv, Prod.mk.injEq]
  refine ⟨hord, hM, ?_, hLoops, hS, hPairs, hExt⟩
  rw [hA, hW]
  push_cast
  ring

/-! ### The transfer graph of macro (b): the invariants, `hwf`, `hint`, `hnb` of the step at `β` -/

/-- the contribution of the ends of an edge to `nShare` at the vertex `u` -/
def BASim_C (Γ : BAGraph E I) (u s d : E ⊕ I) : ℕ :=
  (if Γ.sameAtom u s = true ∧ Γ.intAtom u = true then 1 else 0) + (if Γ.sameAtom u d = true ∧ Γ.intAtom u = true then 1 else 0)

theorem BASim_nShare_eq (Γ : BAGraph E I) (e e' : SEdge (E ⊕ I)) :
    Γ.nShare e e' = if Γ.sameAtom e.src e.dst = true ∨ Γ.sameAtom e'.src e'.dst = true then 0 else
      BASim_C Γ e.src e'.src e'.dst + BASim_C Γ e.dst e'.src e'.dst := by
  unfold BAGraph.nShare BASim_C
  simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, List.sum_cons, List.sum_nil]
  split_ifs <;> simp_all

theorem BASim_pairsAux_append2 (Γ : BAGraph E I) (a b : SEdge (E ⊕ I)) :
    ∀ l : List (SEdge (E ⊕ I)), Γ.pairsAux (l ++ [a, b]) = Γ.pairsAux l + (l.map fun x => Γ.nShare x a + Γ.nShare x b).sum + Γ.nShare a b
  | [] => by simp [BAGraph.pairsAux]
  | x :: l => by
    simp only [List.cons_append, BAGraph.pairsAux, BASim_pairsAux_append2 Γ a b l, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.map_cons, List.sum_cons]
    ring

theorem BASim_sa_trans (Γ : BAGraph E I) {u v w : E ⊕ I} (h1 : Γ.sameAtom u v = true) (h2 : Γ.sameAtom v w = true) : Γ.sameAtom u w = true := by
  rw [BASim_sameAtom_iff] at *; exact (atomSetoid Γ).trans h1 h2

theorem BASim_intAtom_of_same (Γ : BAGraph E I) {u v : E ⊕ I} (h : Γ.sameAtom u v = true) : Γ.intAtom u = Γ.intAtom v := by
  unfold BAGraph.intAtom
  have : Γ.atom v = Γ.atom u := BAVocab_atom_eq_of_mem Γ (by simpa [BAGraph.sameAtom] using h)
  rw [this]

theorem BASim_tr2_beta (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (x y : E ⊕ I) (v : E ⊕ (I ⊕ Fin 2)) (hv : v ≠ bpv 1) :
    (BASim_tr2 Γ rest s w x y).sameAtom (bpv 1) v = false ∧ (BASim_tr2 Γ rest s w x y).sameAtom v (bpv 1) = false := by
  have key : ∀ u : E ⊕ (I ⊕ Fin 2), u ≠ bpv 1 → (BASim_tr2 Γ rest s w x y).sameAtom (bpv 1) u = false := by
    intro u hu
    by_contra hc
    have hc' : (BASim_tr2 Γ rest s w x y).sameAtom (bpv 1) u = true := by simpa using hc
    simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff] at hc'
    rcases Relation.ReflTransGen.cases_head hc' with h | ⟨c, hc1, -⟩
    · exact hu h.symm
    · rw [BASim_tr2_iso] at hc1; exact Bool.noConfusion hc1
  refine ⟨key v hv, ?_⟩
  by_contra hc
  have hc' : (BASim_tr2 Γ rest s w x y).sameAtom v (bpv 1) = true := by simpa using hc
  have := key v hv
  rw [BASim_sameAtom_symm' _ hc'] at this
  exact Bool.noConfusion this

/-- **The invariants of the transfer graph of macro (b)** are those of `Γ`: the pair `Ǧ_{ay}`, `Ǧ_{y'a'}` at the internal atom `[a] = [a']` (of degree 2) is replaced by the path `y' → β → y`;
`hRa`: no other edge of `Γ` has an end in `[a]` -/
theorem BASim_trB_facts (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hσ : p.1.σ = true ∧ q.1.σ = true) (hsame : Γ.sameAtom p.1.src q.1.dst = true) (hwf : ∀ e ∈ Γ.solid, Γ.sameAtom e.src e.dst = false) (hint : Γ.intAtom p.1.src = true)
    (hRa : ∀ e ∈ q.2, Γ.sameAtom p.1.src e.src = false ∧ Γ.sameAtom p.1.src e.dst = false)
    (hnb : ∀ i : I, Γ.intAtom (Sum.inr i) = true → (Γ.atEdges (Sum.inr i)).length = 0 ∨ ((Γ.atEdges (Sum.inr i)).length = 2 ∧ Γ.atCharge (Sum.inr i) = 0)) :
    BASim_inv (BAGraph.BAScost_trB Γ p q) = BASim_inv Γ ∧
    (∀ e ∈ (BAGraph.BAScost_trB Γ p q).solid, (BAGraph.BAScost_trB Γ p q).sameAtom e.src e.dst = false) ∧
      (BAGraph.BAScost_trB Γ p q).intAtom (Sum.inr (Sum.inr 1)) = true ∧
      ∀ i : I ⊕ Fin 2, (BAGraph.BAScost_trB Γ p q).intAtom (Sum.inr i) = true →
        ((BAGraph.BAScost_trB Γ p q).atEdges (Sum.inr i)).length = 0 ∨
          (((BAGraph.BAScost_trB Γ p q).atEdges (Sum.inr i)).length = 2 ∧ (BAGraph.BAScost_trB Γ p q).atCharge (Sum.inr i) = 0) := by
  have hC := BASim_cons_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] p.1.src q.1.dst hsame
  have hnew := BASim_hnew (E := E) (I := I) 2
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hcnt := BASim_counters_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] p.1.src q.1.dst hsame
  rw [show BAGraph.BAScost_trB Γ p q = BASim_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] p.1.src q.1.dst from rfl]
  set tr := BASim_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] p.1.src q.1.dst with htr
  have hpe : p.1 ∈ Γ.solid := lvl1_mem_split_fst _ p hp
  have hqe : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hRe : ∀ e ∈ q.2, e ∈ Γ.solid := fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)
  have hwf1 := hwf p.1 hpe
  have hwf2 := hwf q.1 hqe
  have hwfR : ∀ e ∈ q.2, Γ.sameAtom e.src e.dst = false := fun e he => hwf e (hRe e he)
  have hsame' := BASim_sameAtom_symm' Γ hsame
  have hay' : Γ.sameAtom p.1.src q.1.src = false := by
    by_contra hc
    have : Γ.sameAtom q.1.src q.1.dst = true := BASim_sa_trans Γ (BASim_sameAtom_symm' Γ (by simpa using hc)) hsame
    rw [hwf2] at this; exact Bool.noConfusion this
  have hya' : Γ.sameAtom p.1.dst q.1.dst = false := by
    by_contra hc
    have : Γ.sameAtom p.1.src p.1.dst = true := BASim_sa_trans Γ hsame (BASim_sameAtom_symm' Γ (by simpa using hc))
    rw [hwf1] at this; exact Bool.noConfusion this
  have hRa' : ∀ e ∈ q.2, Γ.sameAtom q.1.dst e.src = false ∧ Γ.sameAtom q.1.dst e.dst = false := fun e he => by
    obtain ⟨h1, h2⟩ := hRa e he
    refine ⟨?_, ?_⟩
    · by_contra hc
      have := BASim_sa_trans Γ hsame (by simpa using hc)
      rw [h1] at this; exact Bool.noConfusion this
    · by_contra hc
      have := BASim_sa_trans Γ hsame (by simpa using hc)
      rw [h2] at this; exact Bool.noConfusion this
  have hβ : ∀ v, v ≠ bpv 1 → tr.sameAtom (bpv 1) v = false ∧ tr.sameAtom v (bpv 1) = false := fun v hv => BASim_tr2_beta Γ _ _ _ _ _ v hv
  have hββ : tr.sameAtom (bpv 1) (bpv 1) = true := BAScost_sameAtom_self tr _
  have hβint : tr.intAtom (bpv 1) = true := by
    unfold BAGraph.intAtom
    simp only [decide_eq_true_eq]
    intro w hw
    by_contra hwn
    have hw' : tr.sameAtom (bpv 1) w = true := by simpa [BAGraph.sameAtom] using hw
    have hwb : w = bpv 1 := by
      by_contra hne
      rw [(hβ w hne).1] at hw'; exact Bool.noConfusion hw'
    subst hwb
    simp [bpv] at hwn
  have hembβ : ∀ v : E ⊕ I, owxEmb 2 v ≠ (bpv 1 : E ⊕ (I ⊕ Fin 2)) := fun v h => lwSymm_emb_ne v 2 1 h.symm
  have hnS : tr.nS = Γ.nS := by
    have := congrArg Counters.nS hcnt
    simp only [BAGraph.counters, List.length_cons, List.length_nil] at this
    simp only [BAGraph.nS] at this ⊢
    omega
  have hW : tr.nW = Γ.nW + 1 := congrArg Counters.nW hcnt
  have hA : tr.nA = Γ.nA + 1 := congrArg Counters.nV hcnt
  have hM : tr.nM = Γ.nM := congrArg Counters.nM hcnt
  have hLoops : tr.nLoops = Γ.nLoops := by
    have h1 : tr.nLoops = (q.2.map (SEdge.map (owxEmb 2))).countP (fun e => tr.sameAtom e.src e.dst) := by
      unfold BAGraph.nLoops
      change ((q.2.map (SEdge.map (owxEmb 2))) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)]).countP _ = _
      rw [List.countP_append]
      simp [bpS, (hβ _ (hembβ _)).2, (hβ _ (hembβ _)).1]
    have h2 : Γ.nLoops = q.2.countP (fun e => Γ.sameAtom e.src e.dst) := by
      unfold BAGraph.nLoops
      rw [((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)).countP_eq]
      simp [List.countP_cons, hwf1, hwf2]
    rw [h1, h2, hC.nLoops_cnt]
  have hs1 : ∀ x ∈ q.2, tr.nShare (SEdge.map (owxEmb 2) x) (bpS true (owxEmb 2 q.1.src) (bpv 1)) = Γ.nShare q.1 x := by
    intro x hx
    rw [BASim_nShare_comm, BASim_nShare_eq, BASim_nShare_eq]
    simp [bpS, BASim_C, SEdge.map, (hβ _ (hembβ _)).2, (hβ _ (hembβ _)).1, hC.sameAtom, hC.intAtom_eq hnew, hwf2, hwfR x hx, (hRa' x hx).1, (hRa' x hx).2]
  have hs2 : ∀ x ∈ q.2, tr.nShare (SEdge.map (owxEmb 2) x) (bpS true (bpv 1) (owxEmb 2 p.1.dst)) = Γ.nShare p.1 x := by
    intro x hx
    rw [BASim_nShare_comm, BASim_nShare_eq, BASim_nShare_eq]
    simp [bpS, BASim_C, SEdge.map, (hβ _ (hembβ _)).2, (hβ _ (hembβ _)).1, hC.sameAtom, hC.intAtom_eq hnew, hwf1, hwfR x hx, (hRa x hx).1, (hRa x hx).2]
  have hs3 : tr.nShare (bpS true (owxEmb 2 q.1.src) (bpv 1)) (bpS true (bpv 1) (owxEmb 2 p.1.dst)) = Γ.nShare p.1 q.1 := by
    rw [BASim_nShare_eq, BASim_nShare_eq]
    simp [bpS, BASim_C, SEdge.map, (hβ _ (hembβ _)).2, (hβ _ (hembβ _)).1, hC.sameAtom, hC.intAtom_eq hnew, hwf1, hwf2, hββ, hβint, hay', hya', hsame, hint]
    by_cases h : Γ.sameAtom p.1.dst q.1.src = true
    · have h' := BASim_sameAtom_symm' Γ h
      have := BASim_intAtom_of_same Γ h'
      simp [h, h', this]
      omega
    · have h' : Γ.sameAtom q.1.src p.1.dst = false := by
        by_contra hc; exact h (BASim_sameAtom_symm' Γ (by simpa using hc))
      simp [h, h']
  have hPairs : tr.nPairs = Γ.nPairs := by
    unfold BAGraph.nPairs
    rw [show tr.solid = q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] from rfl,
      BASim_pairsAux_append2, hC.pairsAux hnew, BASim_pairsAux_perm Γ ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1))]
    simp only [BAGraph.pairsAux, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    have e1 : (q.2.map fun x => tr.nShare (SEdge.map (owxEmb 2) x) (bpS true (owxEmb 2 q.1.src) (bpv 1)) +
        tr.nShare (SEdge.map (owxEmb 2) x) (bpS true (bpv 1) (owxEmb 2 p.1.dst))).sum =
        (q.2.map (Γ.nShare q.1)).sum + (q.2.map (Γ.nShare p.1)).sum := by
      rw [← List.sum_map_add]
      congr 1
      exact List.map_congr_left fun x hx => by rw [hs1 x hx, hs2 x hx]
    rw [e1, hs3]
    ring
  have hExt := hC.nExt
  have hord : tr.scalingOrder = Γ.scalingOrder := by
    simp only [BAGraph.scalingOrder, BAGraph.counters, ord, hnS, hW, hA]
    push_cast
    ring
  have hinv : BASim_inv tr = BASim_inv Γ := by
    simp only [BASim_inv, Prod.mk.injEq]
    refine ⟨hord, hM, ?_, hLoops, hnS, hPairs, hExt⟩
    rw [hA, hW]
    push_cast
    ring
  have hwf_tr : ∀ e ∈ tr.solid, tr.sameAtom e.src e.dst = false := by
    intro e he
    change e ∈ q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨x, hx, rfl⟩ | rfl | rfl
    · simp only [SEdge.map, hC.sameAtom]; exact hwfR x hx
    · simp [bpS, (hβ _ (hembβ _)).2]
    · simp [bpS, (hβ _ (hembβ _)).1]
  refine ⟨hinv, hwf_tr, hβint, ?_⟩
  have hat : ∀ v : E ⊕ I, tr.atEdges (owxEmb 2 v) =
      (q.2.filter (fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst)).map (SEdge.map (owxEmb 2)) ++
        ((if Γ.sameAtom v q.1.src = true then [bpS true (owxEmb 2 q.1.src) (bpv 1)] else []) ++
          (if Γ.sameAtom v p.1.dst = true then [bpS true (bpv 1) (owxEmb 2 p.1.dst)] else [])) := by
    intro v
    unfold BAGraph.atEdges
    change ((q.2.map (SEdge.map (owxEmb 2))) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)]).filter _ = _
    rw [List.filter_append, List.filter_map]
    congr 1
    · congr 1
      exact List.filter_congr (fun e _ => by simp [Function.comp_def, SEdge.map, hC.sameAtom])
    · simp [List.filter_cons, bpS, (hβ _ (hembβ _)).2, (hβ _ (hembβ _)).1, hC.sameAtom]
      split_ifs <;> simp
  have hαa : tr.sameAtom (bpv 0) (owxEmb 2 p.1.src) = true := by
    have h1 : atomSetoid tr (owxEmb 2 p.1.src) (bpv 0) :=
      BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp [BASim_tr2, bpM])
    rw [BASim_sameAtom_iff]; exact (atomSetoid tr).symm h1
  have hαv : ∀ v : E ⊕ I, tr.sameAtom (bpv 0) (owxEmb 2 v) = Γ.sameAtom p.1.src v := fun v => by
    rw [← hC.sameAtom]
    by_cases h : tr.sameAtom (owxEmb 2 p.1.src) (owxEmb 2 v) = true
    · rw [h]; exact BASim_sa_trans tr hαa h
    · have h' : tr.sameAtom (owxEmb 2 p.1.src) (owxEmb 2 v) = false := by simpa using h
      rw [h']
      by_contra hc
      have hc' : tr.sameAtom (bpv 0) (owxEmb 2 v) = true := by simpa using hc
      rw [BASim_sa_trans tr (BASim_sameAtom_symm' tr hαa) hc'] at h'
      exact Bool.noConfusion h'
  intro i hi
  rcases i with i0 | j
  · have hv : Γ.intAtom (Sum.inr i0) = true := by
      have := hC.intAtom_eq hnew (Sum.inr i0)
      rw [← this]; exact hi
    have hvv : (Sum.inr (Sum.inl i0) : E ⊕ (I ⊕ Fin 2)) = owxEmb 2 (Sum.inr i0) := rfl
    rw [hvv]
    set v : E ⊕ I := Sum.inr i0 with hvdef
    by_cases hva : Γ.sameAtom v p.1.src = true
    · left
      rw [hat v]
      have hva1 := BASim_sameAtom_symm' Γ hva
      have e1 : Γ.sameAtom v q.1.src = false := by
        by_contra hc
        have := BASim_sa_trans Γ hva1 (by simpa using hc)
        rw [hay'] at this; exact Bool.noConfusion this
      have e2 : Γ.sameAtom v p.1.dst = false := by
        by_contra hc
        have := BASim_sa_trans Γ hva1 (by simpa using hc)
        rw [hwf1] at this; exact Bool.noConfusion this
      have e3 : q.2.filter (fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        have h1 : Γ.sameAtom v e.src = false := by
          by_contra hc
          have := BASim_sa_trans Γ hva1 (by simpa using hc)
          rw [(hRa e he).1] at this; exact Bool.noConfusion this
        have h2 : Γ.sameAtom v e.dst = false := by
          by_contra hc
          have := BASim_sa_trans Γ hva1 (by simpa using hc)
          rw [(hRa e he).2] at this; exact Bool.noConfusion this
        simp [h1, h2]
      simp [e1, e2, e3]
    · have hva' : Γ.sameAtom v p.1.src = false := by simpa using hva
      have hva2 : Γ.sameAtom v q.1.dst = false := by
        by_contra hc
        exact hva (BASim_sa_trans Γ (by simpa using hc) hsame')
      have hΓp : (Γ.atEdges v).Perm ((p.1 :: q.1 :: q.2).filter (fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst)) :=
        ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)).filter _
      have hexp : (p.1 :: q.1 :: q.2).filter (fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst) =
          (if Γ.sameAtom v p.1.dst = true then [p.1] else []) ++ ((if Γ.sameAtom v q.1.src = true then [q.1] else []) ++
            q.2.filter (fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst)) := by
        simp only [List.filter_cons, hva', hva2]
        split_ifs <;> simp_all
      have hlen : (tr.atEdges (owxEmb 2 v)).length = (Γ.atEdges v).length := by
        rw [hat v, hΓp.length_eq, hexp]
        simp only [List.length_append, List.length_map]
        split_ifs <;> simp <;> omega
      have hch : tr.atCharge (owxEmb 2 v) = Γ.atCharge v := by
        have hsum := (hΓp.map (fun e : SEdge (E ⊕ I) => if Γ.sameAtom v e.src = true then (if e.σ then (-1 : ℤ) else 1) else (if e.σ then 1 else -1))).sum_eq
        unfold BAGraph.atCharge
        rw [hat v, hsum, hexp]
        have hRc : ∀ e ∈ q.2, (fun e' : SEdge (E ⊕ (I ⊕ Fin 2)) => if tr.sameAtom (owxEmb 2 v) e'.src = true then (if e'.σ then (-1 : ℤ) else 1) else (if e'.σ then 1 else -1)) (SEdge.map (owxEmb 2) e) =
            (fun e : SEdge (E ⊕ I) => if Γ.sameAtom v e.src = true then (if e.σ then (-1 : ℤ) else 1) else (if e.σ then 1 else -1)) e := fun e he => by
          simp only [SEdge.map, hC.sameAtom]
          rfl
        simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
        have hR : (((q.2.filter (fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst)).map fun e => (fun e' : SEdge (E ⊕ (I ⊕ Fin 2)) =>
            if tr.sameAtom (owxEmb 2 v) e'.src = true then (if e'.σ then (-1 : ℤ) else 1) else (if e'.σ then 1 else -1)) (SEdge.map (owxEmb 2) e))).sum =
            (((q.2.filter (fun e => Γ.sameAtom v e.src != Γ.sameAtom v e.dst)).map fun e => (fun e : SEdge (E ⊕ I) =>
            if Γ.sameAtom v e.src = true then (if e.σ then (-1 : ℤ) else 1) else (if e.σ then 1 else -1)) e)).sum := by
          congr 1
          exact List.map_congr_left fun e he => hRc e (List.mem_of_mem_filter he)
        rw [hR]
        split_ifs with h1 h2 h2 <;> simp [bpS, hC.sameAtom, hva', (hβ _ (hembβ _)).1, (hβ _ (hembβ _)).2, hσ.1, hσ.2, h1, h2] <;> omega
      rcases hnb i0 hv with h | ⟨h1, h2⟩
      · left; rw [hlen]; exact h
      · right; exact ⟨by rw [hlen]; exact h1, by rw [hch]; exact h2⟩
  · fin_cases j
    · left
      change (tr.atEdges (bpv 0)).length = 0
      unfold BAGraph.atEdges
      change (List.filter _ ((q.2.map (SEdge.map (owxEmb 2))) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)])).length = 0
      simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil, List.filter_map, List.length_map]
      have hR : List.filter ((fun e => tr.sameAtom (bpv 0) e.src != tr.sameAtom (bpv 0) e.dst) ∘ SEdge.map (owxEmb 2)) q.2 = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        simp [Function.comp_def, SEdge.map, hαv, (hRa e he).1, (hRa e he).2]
      have hαβ : tr.sameAtom (bpv 0) (bpv 1) = false := (hβ (bpv 0) (by simp [bpv])).2
      simp [hR, bpS, hαv, hαβ, (hβ _ (hembβ _)).1, (hβ _ (hembβ _)).2, hay', hwf1]
    · right
      change (tr.atEdges (bpv 1)).length = 2 ∧ tr.atCharge (bpv 1) = 0
      have hed : tr.atEdges (bpv 1) = [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] := by
        unfold BAGraph.atEdges
        change List.filter _ ((q.2.map (SEdge.map (owxEmb 2))) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)]) = _
        have hR : List.filter (fun e : SEdge (E ⊕ (I ⊕ Fin 2)) => tr.sameAtom (bpv 1) e.src != tr.sameAtom (bpv 1) e.dst) (q.2.map (SEdge.map (owxEmb 2))) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
          simp [SEdge.map, (hβ _ (hembβ _)).1]
        rw [List.filter_append, hR]
        simp [bpS, (hβ _ (hembβ _)).1, hββ]
      rw [hed]
      refine ⟨rfl, ?_⟩
      simp [BAGraph.atCharge, hed, bpS, (hβ _ (hembβ _)).1, hββ]

/-- the internal atom of degree 2 at the pair of a split step carries no other edge of `Γ` -/
theorem BASim_Ra (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hwf : ∀ e ∈ Γ.solid, Γ.sameAtom e.src e.dst = false) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
    (hdeg : (Γ.atEdges p.1.src).length = 2) : ∀ e ∈ q.2, Γ.sameAtom p.1.src e.src = false ∧ Γ.sameAtom p.1.src e.dst = false := by
  have hpe : p.1 ∈ Γ.solid := lvl1_mem_split_fst _ p hp
  have hqe : q.1 ∈ Γ.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hwf1 := hwf p.1 hpe
  have hwf2 := hwf q.1 hqe
  have hay' : Γ.sameAtom p.1.src q.1.src = false := by
    by_contra hc
    have := BASim_sa_trans Γ (BASim_sameAtom_symm' Γ (by simpa using hc)) hsame
    rw [hwf2] at this; exact Bool.noConfusion this
  have hΓp : (Γ.atEdges p.1.src).Perm ((p.1 :: q.1 :: q.2).filter (fun e => Γ.sameAtom p.1.src e.src != Γ.sameAtom p.1.src e.dst)) :=
    ((lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)).filter _
  have hlen := hΓp.length_eq
  rw [hdeg] at hlen
  simp only [List.filter_cons, BAScost_sameAtom_self, hwf1, hay', hsame, bne_iff_ne, ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
    List.length_cons, Bool.true_eq_false, not_true_eq_false] at hlen
  have h0 : (q.2.filter (fun e => Γ.sameAtom p.1.src e.src != Γ.sameAtom p.1.src e.dst)) = [] := by
    rw [← List.length_eq_zero_iff]; omega
  rw [List.filter_eq_nil_iff] at h0
  intro e he
  have h3 : Γ.sameAtom p.1.src e.src = Γ.sameAtom p.1.src e.dst := by simpa using h0 e he
  have hwe := hwf e (lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
  cases h1 : Γ.sameAtom p.1.src e.src
  · rw [h1] at h3; exact ⟨rfl, h3.symm⟩
  · rw [h1] at h3
    exfalso
    have := BASim_sa_trans Γ (BASim_sameAtom_symm' Γ h1) h3.symm
    rw [hwe] at this; exact Bool.noConfusion this

end Cons

section MergeInv
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BASim_merge_atom (T : BAGraph E I) (hT : ∀ e ∈ T.dotted, e.eq = false) (v : E ⊕ I) :
    T.merge.atom (T.toLGraph.vmap v) = (T.atom v).image T.toLGraph.vmap := by
  classical
  have hinj := BAVocab_vmap_injective T.toLGraph hT
  have hsurj := BAVocab_vmap_surjective T.toLGraph
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

/-- the invariants of the packed merge of a normal term are those of the term -/
theorem BASim_outOf_baInv {E0 : Type} (P : BAPGraph E0) {I' : Type} [Fintype I'] [DecidableEq I'] (T : BAGraph P.E' I') (hN : T.Normal) :
    (P.outOf T).baInv = BASim_inv T := by
  have hT := hN.1
  have hinj := BAVocab_vmap_injective T.toLGraph hT
  have hc := BAWeightOp_packMerge_counters T hN
  have hS := congrArg Counters.nS hc
  have hW := congrArg Counters.nW hc
  have hA := congrArg Counters.nV hc
  have hM := congrArg Counters.nM hc
  have hL : T.merge.nLoops = T.nLoops := by
    unfold BAGraph.nLoops
    change (T.solid.map (SEdge.map T.toLGraph.vmap)).countP _ = _
    rw [List.countP_map]
    congr 1
    funext e
    simp only [Function.comp_apply, SEdge.map, BASim_merge_sameAtom T hT]
  have hI : ∀ u, T.merge.intAtom (T.toLGraph.vmap u) = T.intAtom u := fun u => by
    unfold BAGraph.intAtom
    rw [BASim_merge_atom T hT]
    refine decide_eq_decide.2 ⟨fun h w hw => ?_, fun h w' hw' => ?_⟩
    · have := h (T.toLGraph.vmap w) (Finset.mem_image_of_mem _ hw)
      have h2 := lwVmap_isRight T.toLGraph hT w
      rw [h2] at this; exact this
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hw'
      have h2 := lwVmap_isRight T.toLGraph hT w
      rw [h2]; exact h w hw
  have hP : T.merge.nPairs = T.nPairs := by
    unfold BAGraph.nPairs
    change T.merge.pairsAux (T.solid.map (SEdge.map T.toLGraph.vmap)) = _
    induction T.solid with
    | nil => rfl
    | cons e l ih =>
      simp only [List.map_cons, BAGraph.pairsAux, ih, List.map_map, Function.comp_def]
      congr 1
      refine congrArg List.sum (List.map_congr_left fun e' _ => ?_)
      unfold BAGraph.nShare
      simp only [SEdge.map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, BASim_merge_sameAtom T hT, hI]
      split_ifs <;> simp
  have hE := BASim_merge_nExt T hT
  change (T.merge.scalingOrder, T.merge.nM, (T.merge.nA : ℤ) - T.merge.nW, T.merge.nLoops, T.merge.nS, T.merge.nPairs, T.merge.nExt) = BASim_inv T
  simp only [BASim_inv, Prod.mk.injEq, BAGraph.scalingOrder, BAGraph.counters, ord]
  have hS' : T.merge.nS = T.nS := hS
  have hW' : T.merge.nW = T.nW := hW
  have hA' : T.merge.nA = T.nA := hA
  have hM' : T.merge.nM = T.nM := hM
  rw [hS', hW', hA', hM', hL, hP, hE]
  simp

/-- two graphs with the same solid edges, waved edges up to colour, and the same atoms have the same invariants -/
theorem BASim_inv_congr (T₁ T₂ : BAGraph E I) (hs : T₁.solid = T₂.solid) (hw : T₁.waved.length = T₂.waved.length)
    (hadj : ∀ u v, T₁.toLGraph.adj u v = T₂.toLGraph.adj u v)
    (h12 : ∀ u v, T₁.atomAdj u v = true → T₂.sameAtom u v = true) (h21 : ∀ u v, T₂.atomAdj u v = true → T₁.sameAtom u v = true) :
    BASim_inv T₁ = BASim_inv T₂ := by
  have hrt : ∀ (A B : BAGraph E I), (∀ u v, A.atomAdj u v = true → B.sameAtom u v = true) →
      ∀ u v, Relation.ReflTransGen (fun a b => A.atomAdj a b = true) u v → Relation.ReflTransGen (fun a b => B.atomAdj a b = true) u v := by
    intro A B h u v huv
    refine BASim_rtg_sub (fun a b hab => ?_) huv
    have := h a b hab
    simpa [BAGraph.sameAtom, BAGraph.mem_atom_iff] using this
  have ha : ∀ v, T₁.atom v = T₂.atom v := fun v => Finset.ext fun w => by
    rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]; exact ⟨hrt _ _ h12 v w, hrt _ _ h21 v w⟩
  have hm : ∀ v, T₁.mol v = T₂.mol v := by
    have hm1 : ∀ (A B : BAGraph E I), (∀ u v, A.toLGraph.adj u v = B.toLGraph.adj u v) → (∀ u v, A.atomAdj u v = true → B.sameAtom u v = true) →
        ∀ u v, Relation.ReflTransGen (fun a b => A.adj a b = true) u v → Relation.ReflTransGen (fun a b => B.adj a b = true) u v := by
      intro A B hAB h u v huv
      refine BASim_rtg_sub (fun a b hab => ?_) huv
      simp only [BAGraph.adj, Bool.or_eq_true] at hab
      rcases hab with hab | hab
      · exact Relation.ReflTransGen.single (by simp [BAGraph.adj, ← hAB, hab])
      · have := h a b hab
        simp only [BAGraph.sameAtom, decide_eq_true_eq, BAGraph.mem_atom_iff] at this
        exact Relation.ReflTransGen.mono (fun x y hxy => by simp [BAGraph.adj, hxy]) _ _ this
    intro v
    exact Finset.ext fun w => by
      rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
      exact ⟨hm1 _ _ hadj h12 v w, hm1 _ _ (fun u v => (hadj u v).symm) h21 v w⟩
  have ha' : T₁.atom = T₂.atom := funext ha
  have hm' : T₁.mol = T₂.mol := funext hm
  have hsame : ∀ u v, T₁.sameAtom u v = T₂.sameAtom u v := fun u v => by unfold BAGraph.sameAtom; rw [ha]
  have hint : ∀ u, T₁.intAtom u = T₂.intAtom u := fun u => by unfold BAGraph.intAtom; rw [ha]
  have hS : T₁.nS = T₂.nS := congrArg List.length hs
  have hA : T₁.nA = T₂.nA := by unfold BAGraph.nA; rw [ha']
  have hM : T₁.nM = T₂.nM := by unfold BAGraph.nM; rw [hm']
  have hL : T₁.nLoops = T₂.nLoops := by unfold BAGraph.nLoops; rw [hs]; simp only [hsame]
  have hE : T₁.nExt = T₂.nExt := by unfold BAGraph.nExt; rw [ha']
  have hP : T₁.nPairs = T₂.nPairs := by
    unfold BAGraph.nPairs; rw [hs]
    have : ∀ l : List (SEdge (E ⊕ I)), T₁.pairsAux l = T₂.pairsAux l := fun l => by
      induction l with
      | nil => rfl
      | cons e l ih => simp only [BAGraph.pairsAux, ih]; congr 1; refine congrArg List.sum (List.map_congr_left fun e' _ => ?_); simp only [BAGraph.nShare, hsame, hint]
    exact this _
  have hW' : T₁.nW = T₂.nW := hw
  simp only [BASim_inv, BAGraph.scalingOrder, BAGraph.counters, ord, hS, hW', hA, hM, hL, hP, hE]

end MergeInv

section Dterms
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BASim_ord_ext (Γ : BAGraph E I) (k : ℕ) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    (BAGraph.ext k Γ rest s w md).scalingOrder = ((rest.length + s.length : ℕ) : ℤ) + 2 * (((Γ.nW + w.length : ℕ) : ℤ) - (BAGraph.ext k Γ rest s w md).nA) := by
  simp [BAGraph.scalingOrder, BAGraph.counters, ord, BAGraph.nS, BAGraph.nW, BAGraph.ext, LGraph.owxExt]

/-- the terms `d2`, `d3` of macro (b) (`ΔnS = -1`, `ΔnW = +1`, no new atom) have a higher order than `Γ` -/
theorem BASim_ord_d23 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (hs : s.length = 1) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2))))
    (ρ : E ⊕ (I ⊕ Fin 2) → E ⊕ I) (hρ : ∀ a, ρ (owxEmb 2 a) = a) (hmd : ∀ e ∈ md, Γ.sameAtom (ρ e.x) (ρ e.y) = true)
    (hatt : ∀ w, ∃ v, (BAGraph.ext 2 Γ q.2 s [bpW false (bpv 0) (bpv 1)] md).sameAtom (owxEmb 2 v) w = true) :
    Γ.scalingOrder < (BAGraph.ext 2 Γ q.2 s [bpW false (bpv 0) (bpv 1)] md).scalingOrder := by
  have hC := BASim_cons_of_md Γ Γ q.2 s [bpW false (bpv 0) (bpv 1)] md ρ hρ (fun a b h => BASim_sameAtom_of_adj _ h)
    (fun a b h => BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj (BASim_Ext_ext 2 Γ _ _ _ _) a b h)) hmd
  have hA := hC.nA_le hatt
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hS : Γ.nS = q.2.length + 2 := by simp only [BAGraph.nS]; omega
  rw [BASim_ord_ext]
  simp only [BAGraph.scalingOrder, BAGraph.counters, ord, hS]
  simp only [List.length_singleton, hs]
  omega

/-- an extension that joins two different atoms with an external vertex has fewer atoms with an external vertex (`BASim_nExt_le`) -/
theorem BASim_nExt_lt {k : ℕ} {Γ : BAGraph E I} {T : BAGraph E (I ⊕ Fin k)} (hExt : BASim_Ext Γ k T) {u v : E ⊕ I} (hne : Γ.sameAtom u v = false)
    (hsame : T.sameAtom (owxEmb k u) (owxEmb k v) = true) (hu : ¬ ∀ w ∈ Γ.atom u, w.isRight = true) (hv : ¬ ∀ w ∈ Γ.atom v, w.isRight = true) :
    T.nExt < Γ.nExt := by
  classical
  push Not at hu hv
  obtain ⟨w1, hw1, hw1'⟩ := hu
  obtain ⟨w2, hw2, hw2'⟩ := hv
  obtain ⟨a, rfl⟩ : ∃ a : E, w1 = Sum.inl a := by rcases w1 with a | b; exacts [⟨a, rfl⟩, by simp at hw1']
  obtain ⟨b, rfl⟩ : ∃ b : E, w2 = Sum.inl b := by rcases w2 with a | b; exacts [⟨a, rfl⟩, by simp at hw2']
  have hco : ∀ x y, Γ.atomAdj x y = true → T.sameAtom (owxEmb k x) (owxEmb k y) = true := fun x y h => BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj hExt x y h)
  refine (BASim_nExt_le Γ T hco).2 ⟨a, b, ?_, ?_⟩
  · intro heq
    have h1 : Γ.atom u = Γ.atom (Sum.inl a) := (BAVocab_atom_eq_of_mem Γ hw1).symm
    have h2 : Γ.atom v = Γ.atom (Sum.inl b) := (BAVocab_atom_eq_of_mem Γ hw2).symm
    have : v ∈ Γ.atom u := by rw [h1, heq, ← h2]; exact BAVocab_self_mem_atom Γ v
    simp [BAGraph.sameAtom, this] at hne
  · have s1 := BASim_Ext_sameAtom hExt hw1
    have s2 := BASim_Ext_sameAtom hExt hw2
    rw [BASim_sameAtom_iff] at s1 s2 hsame ⊢
    exact (atomSetoid T).trans ((atomSetoid T).symm s1) ((atomSetoid T).trans hsame s2)

theorem BASim_sameAtom_addM (Γ : BAGraph E I) (d : BAMEdge (E ⊕ I)) {u v : E ⊕ I} (h : Γ.sameAtom u v = true) : (Γ.addM d).sameAtom u v = true := by
  simp only [BAGraph.sameAtom, decide_eq_true_eq] at h ⊢
  exact BAWeightOp_atom_subset Γ (Γ.addM d) (fun x y h => BASim_atomAdj_addM' Γ d x y h) u h

theorem BASim_rho2_beta (x y : E ⊕ I) : BAScost_rho2 x y (bpv 1 : E ⊕ (I ⊕ Fin 2)) = y := by simp [BAScost_rho2, bpv]

/-- the term `d4` of macro (b) when `[y] ≠ [y']`: the order rises or `nExt` falls -/
theorem BASim_d4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) (hne : Γ.sameAtom p.1.dst q.1.src = false) :
    Γ.scalingOrder < (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]).scalingOrder ∨
    (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]).nExt < Γ.nExt := by
  classical
  set md : List (BAMEdge (E ⊕ (I ⊕ Fin 2))) := [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)] with hmd
  set T := BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] md with hT
  have hne' : Γ.sameAtom q.1.src p.1.dst = false := by
    by_contra hc
    have hc' : Γ.sameAtom q.1.src p.1.dst = true := by simpa using hc
    exact absurd (BASim_sameAtom_symm' Γ hc') (by simp [hne])
  have h3 : atomSetoid T (owxEmb 2 q.1.src) (bpv 1) := BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp [hmd])
  have h4 : atomSetoid T (bpv 1) (owxEmb 2 p.1.dst) := BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp [hmd])
  have hyy : T.sameAtom (owxEmb 2 q.1.src) (owxEmb 2 p.1.dst) = true := by
    rw [BASim_sameAtom_iff]
    exact (atomSetoid T).trans h3 h4
  by_cases hint : (∀ w ∈ Γ.atom q.1.src, w.isRight = true) ∨ (∀ w ∈ Γ.atom p.1.dst, w.isRight = true)
  · left
    set d : BAMEdge (E ⊕ I) := bpM q.1.src p.1.dst with hd
    have hA : (Γ.addM d).nA + 1 ≤ Γ.nA := BASim_nA_addM Γ q.1.src p.1.dst d ⟨rfl, rfl⟩ hne' hint
    have hC := BASim_cons_of_md Γ (Γ.addM d) q.2 [] [bpW false (bpv 0) (bpv 1)] md (BAScost_rho2 p.1.src q.1.src) (BAScost_rho2_emb _ _)
      (fun a b h => BASim_sameAtom_of_adj _ (BASim_atomAdj_addM' Γ d a b h))
      (fun a b h => by
        rcases BASim_atomAdj_addM Γ d a b h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj (BASim_Ext_ext 2 Γ _ _ _ _) a b h)
        · simp only [hd, bpM] at h1 h2; rw [← h1, ← h2]; exact hyy
        · simp only [hd, bpM] at h1 h2; rw [← h1, ← h2]; exact BASim_sameAtom_symm' T hyy)
      (fun e he => by
        simp only [hmd, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> simp only [bpM, BAScost_rho2_emb, BASim_rho2_alpha, BASim_rho2_beta]
        · exact BAScost_sameAtom_self _ _
        · exact BASim_sameAtom_addM Γ d hsame
        · exact BAScost_sameAtom_self _ _
        · exact BASim_sameAtom_of_adj _ (BASim_atomAdj_addM_d Γ d))
    have hatt : ∀ w : E ⊕ (I ⊕ Fin 2), ∃ v, T.sameAtom (owxEmb 2 v) w = true := by
      rintro (a | i | j)
      · exact ⟨Sum.inl a, BAScost_sameAtom_self _ _⟩
      · exact ⟨Sum.inr i, BAScost_sameAtom_self _ _⟩
      · fin_cases j
        · refine ⟨p.1.src, ?_⟩
          rw [BASim_sameAtom_iff]
          exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp [hmd])
        · refine ⟨q.1.src, ?_⟩
          rw [BASim_sameAtom_iff]
          exact h3
    have hA' := hC.nA_le hatt
    have hl := lwSplit_snd_length Γ.solid p hp
    have hl' := lwSplit_snd_length p.2 q hq
    have hS : Γ.nS = q.2.length + 2 := by simp only [BAGraph.nS]; omega
    rw [hT, BASim_ord_ext]
    simp only [BAGraph.scalingOrder, BAGraph.counters, ord, hS, List.length_nil, List.length_singleton]
    omega
  · right
    obtain ⟨hu, hv⟩ := not_or.1 hint
    exact BASim_nExt_lt (BASim_Ext_ext 2 Γ _ _ _ _) hne' hyy hu hv

theorem BASim_ord_d2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) :
    Γ.scalingOrder < (BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)]).scalingOrder := by
  refine BASim_ord_d23 Γ p q hp hq hsame _ rfl _ (BAScost_rho2 p.1.src p.1.dst) (BAScost_rho2_emb _ _) ?_ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp only [bpM, BAScost_rho2_emb, BASim_rho2_alpha, BASim_rho2_beta]
    · exact BAScost_sameAtom_self _ _
    · exact hsame
    · exact BAScost_sameAtom_self _ _
  · rintro (a | i | j)
    · exact ⟨Sum.inl a, BAScost_sameAtom_self _ _⟩
    · exact ⟨Sum.inr i, BAScost_sameAtom_self _ _⟩
    · fin_cases j
      · exact ⟨p.1.src, by rw [BASim_sameAtom_iff]; exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)⟩
      · exact ⟨p.1.dst, by rw [BASim_sameAtom_iff]; exact (atomSetoid _).symm (BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp))⟩

theorem BASim_ord_d3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) :
    Γ.scalingOrder < (BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]).scalingOrder := by
  refine BASim_ord_d23 Γ p q hp hq hsame _ rfl _ (BAScost_rho2 p.1.src q.1.src) (BAScost_rho2_emb _ _) ?_ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp only [bpM, BAScost_rho2_emb, BASim_rho2_alpha, BASim_rho2_beta]
    · exact BAScost_sameAtom_self _ _
    · exact hsame
    · exact BAScost_sameAtom_self _ _
  · rintro (a | i | j)
    · exact ⟨Sum.inl a, BAScost_sameAtom_self _ _⟩
    · exact ⟨Sum.inr i, BAScost_sameAtom_self _ _⟩
    · fin_cases j
      · exact ⟨p.1.src, by rw [BASim_sameAtom_iff]; exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)⟩
      · exact ⟨q.1.src, by rw [BASim_sameAtom_iff]; exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp)⟩

/-- the term `d4` with `[y] = [y']` has the invariants of the band's `A1` (`S` against `S⁺`: the colour of a waved edge is not read) -/
theorem BASim_inv_d4_A1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hsame : Γ.sameAtom p.1.src q.1.dst = true) :
    BASim_inv (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]) = BASim_inv (BAGGOp_A1 Γ p q) := by
  set md₁ : List (BAMEdge (E ⊕ (I ⊕ Fin 2))) := [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst),
    bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)] with hmd₁
  set T₁ := BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] md₁ with hT₁
  set md₂ : List (BAMEdge (E ⊕ (I ⊕ Fin 2))) := [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src),
    bpM (bpv 1) (owxEmb 2 p.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)] with hmd₂
  set T₂ := BAGraph.ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)] md₂ with hT₂
  have hA1 : BAGGOp_A1 Γ p q = T₂ := rfl
  rw [hA1]
  have hExt1 : BASim_Ext Γ 2 T₁ := BASim_Ext_ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] md₁
  have hExt2 : BASim_Ext Γ 2 T₂ := BASim_Ext_ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)] md₂
  have a1 : atomSetoid T₁ (owxEmb 2 p.1.src) (bpv 0) := BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp [hmd₁])
  have a2 : atomSetoid T₂ (owxEmb 2 p.1.src) (bpv 0) := BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp [hmd₂])
  have hs12 : T₂.sameAtom (owxEmb 2 p.1.src) (owxEmb 2 q.1.dst) = true :=
    BASim_Ext_sameAtom hExt2 (by simpa [BAGraph.sameAtom] using hsame)
  have m1 : ∀ e ∈ md₁, atomSetoid T₂ e.x e.y := by
    intro e he
    simp only [hmd₁, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact a2
    · exact (atomSetoid T₂).trans ((atomSetoid T₂).symm a2) ((BASim_sameAtom_iff T₂ _ _).1 hs12)
    · exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp [hmd₂])
    · exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp [hmd₂])
  have m2 : ∀ e ∈ md₂, atomSetoid T₁ e.x e.y := by
    intro e he
    simp only [hmd₂, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact a1
    · exact (atomSetoid T₁).symm a1
    · exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp [hmd₁])
    · exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp [hmd₁])
  refine BASim_inv_congr _ _ rfl (by simp [hT₁, hT₂, BAGraph.ext, LGraph.owxExt]) (fun u v => ?_) (fun u v h => ?_) (fun u v h => ?_)
  · simp [hT₁, hT₂, LGraph.adj, BAGraph.ext, LGraph.owxExt, bpW, List.any_append]
  · rcases (BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ u v).1 h with ⟨a, b, rfl, rfl, hab⟩ | ⟨e, he, hev⟩
    · exact BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj hExt2 a b hab)
    · rcases hev with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (BASim_sameAtom_iff T₂ _ _).2 (m1 e he)
      · exact (BASim_sameAtom_iff T₂ _ _).2 ((atomSetoid T₂).symm (m1 e he))
  · rcases (BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ u v).1 h with ⟨a, b, rfl, rfl, hab⟩ | ⟨e, he, hev⟩
    · exact BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj hExt1 a b hab)
    · rcases hev with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (BASim_sameAtom_iff T₁ _ _).2 (m2 e he)
      · exact (BASim_sameAtom_iff T₁ _ _).2 ((atomSetoid T₁).symm (m2 e he))

end Dterms

section Macro
variable {E : Type}

/-- the conclusion of `BAsim'` for one output `Q` of a step at `P` -/
def BASim_Goal (m : ℂ) (P Q : BAPGraph E) : Prop :=
  (∃ (T : BAPGraph E) (L' : List (PGraph E)), T.g.Normal ∧ T.baInv = P.baInv ∧ LocStep m T.img L' ∧ ∃ Q0 ∈ L', Q0.baInv = Q.baInv) ∨
    P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt

/-- the packed transfer graph: the graph `g` over the external vertices of `P` and new internal vertices -/
def BASim_Ttr (P : BAPGraph E) (g : BAGraph P.E' (P.I' ⊕ Fin 2)) : BAPGraph E where
  E' := P.E'
  I' := P.I' ⊕ Fin 2
  instFE := P.instFE
  instDE := P.instDE
  instFI := inferInstance
  instDI := inferInstance
  ext := P.ext
  ext_surj := P.ext_surj
  g := g

theorem BASim_outsT_mem (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape) {Ts : List (BAGraph P.E' I')}
    {T : BAGraph P.E' I'} (hT : T ∈ Ts) {T' : BAGraph P.E' I'} (hT' : T' ∈ T.splitG) : (tg T', P.outOf T') ∈ P.outsT tg Ts := by
  unfold BAPGraph.outsT
  exact List.mem_flatMap.2 ⟨T, hT, List.mem_map.2 ⟨T', hT', rfl⟩⟩

/-- **Stage 2 of a macro step** (and the case `T = P`): an output of a tagged step at a normal graph `T` with the invariants of `P`, tagged `band`, `e1` or `e2`, satisfies the conclusion of `BAsim'` -/
theorem BASim_goal_of_step (m : ℂ) (P T : BAPGraph E) (hN : T.g.Normal) (hinv : T.baInv = P.baInv) {LT : List (BAShape × BAPGraph E)} (hst : BAFrameStepT T LT)
    {t : BAShape} {Q : BAPGraph E} (hmem : (t, Q) ∈ LT) (ht : t = BAShape.band ∨ t = BAShape.e1 ∨ t = BAShape.e2) : BASim_Goal m P Q := by
  have hf : T.g.scalingOrder = P.g.scalingOrder := congrArg Prod.fst hinv
  have hl : T.g.nExt = P.g.nExt := congrArg (fun x => x.2.2.2.2.2.2) hinv
  rcases ht with rfl | rfl | rfl
  · obtain ⟨L', hL, R, hR, hRE⟩ := baMatch_holds m T LT hst hN Q hmem
    exact Or.inl ⟨T, L', hN, hinv, hL, R, hR, (BASim_baInv_of_equiv hRE).trans (BASim_img_baInv Q)⟩
  · rcases baExtraGood_holds T LT hst hN Q (Or.inl hmem) with h | h <;> [exact Or.inr (Or.inl (hf ▸ h)); exact Or.inr (Or.inr (hl ▸ h))]
  · rcases baExtraGood_holds T LT hst hN Q (Or.inr hmem) with h | h <;> [exact Or.inr (Or.inl (hf ▸ h)); exact Or.inr (Or.inr (hl ▸ h))]

theorem BASim_tagStd_cases {E0 I0 : Type} [Fintype E0] [DecidableEq E0] [Fintype I0] [DecidableEq I0] (Γ : BAGraph E0 I0) (k : ℕ) (T' : BAGraph E0 (I0 ⊕ Fin k)) :
    Γ.tagStd k T' = BAShape.band ∨ Γ.tagStd k T' = BAShape.e1 ∨ Γ.tagStd k T' = BAShape.e2 := by
  unfold BAGraph.tagStd; split_ifs <;> simp

theorem BASim_tagT1_cases {E0 I0 : Type} [Fintype E0] [DecidableEq E0] [Fintype I0] [DecidableEq I0] (Γ : BAGraph E0 I0) (T' : BAGraph E0 (I0 ⊕ Fin 2)) :
    Γ.tagT1 T' = BAShape.band ∨ Γ.tagT1 T' = BAShape.e1 ∨ Γ.tagT1 T' = BAShape.e2 := by
  unfold BAGraph.tagT1; split_ifs <;> simp

/-- the stage-2 outputs of a macro step are outputs of a tagged step at the transfer graph `g` (the tag is irrelevant to `outsT`, which reads only `ext`): `band` ones are matched, `e1`/`e2` ones rise -/
theorem BASim_macro_out (m : ℂ) (P : BAPGraph E) (g : BAGraph P.E' (P.I' ⊕ Fin 2)) (hNg : g.Normal) (hinv : (BASim_Ttr P g).baInv = P.baInv)
    {LT2 : List (BAShape × BAPGraph E)} (hst : BAFrameStepT (BASim_Ttr P g) LT2) {k : ℕ} (Ts : List (BAGraph P.E' ((P.I' ⊕ Fin 2) ⊕ Fin k)))
    (hsub : ∀ t Q, (t, Q) ∈ (BASim_Ttr P g).outsT (g.tagStd k) Ts → (t, Q) ∈ LT2) (sh : BAShape) {t : BAShape} {Q : BAPGraph E}
    (hQ : (t, Q) ∈ P.outsT (fun _ => sh) Ts) : BASim_Goal m P Q := by
  obtain ⟨T, hT, T', hT', -, rfl⟩ := BASim_mem_outsT P _ Ts t Q hQ
  exact BASim_goal_of_step m P (BASim_Ttr P g) hNg hinv hst (hsub _ _ (BASim_outsT_mem (BASim_Ttr P g) (g.tagStd k) hT hT')) (BASim_tagStd_cases g k T')

/-- **Macro (a), stage 2** -/
theorem BASim_macroA (m : ℂ) (P : BAPGraph E) (hN : P.g.Normal) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hσ : p.1.σ = true ∧ p.1.circ = true) (hxy : P.g.sameAtom p.1.src p.1.dst = true) {t : BAShape} {Q : BAPGraph E}
    (hQ : (t, Q) ∈ P.outsT (fun _ => BAShape.macroA) ((BAGraph.BAScost_trA P.g p).lw2 (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2)))) ∨
      (t, Q) ∈ P.outsT (fun _ => BAShape.macroA) ((BAGraph.BAScost_trA P.g p).lw4 (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))))) :
    BASim_Goal m P Q := by
  have hNg : (BAGraph.BAScost_trA P.g p).Normal :=
    BAWeightOp_ext_normal 2 P.g hN _ _ _ _ (BASim_hcirc hN hp) (by simp [bpS])
  have hinv : (BASim_Ttr P (BAGraph.BAScost_trA P.g p)).baInv = P.baInv := BASim_inv_trA P.g p hp hxy
  have hpp : (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))) ∈ lwSplit (BASim_Ttr P (BAGraph.BAScost_trA P.g p)).g.solid :=
    lvl1_split_last _ _
  have hst := BAFrameStepT.weight (BASim_Ttr P (BAGraph.BAScost_trA P.g p)) _ hpp ⟨rfl, rfl, rfl⟩
  rcases hQ with hQ | hQ
  · exact BASim_macro_out m P _ hNg hinv hst _ (fun t Q h => List.mem_append_left _ h) _ hQ
  · exact BASim_macro_out m P _ hNg hinv hst _ (fun t Q h => List.mem_append_right _ h) _ hQ

/-- **Macro (b), stage 2** (`GGGamma` at the transferred pair at `β`) -/
theorem BASim_macroB2 (m : ℂ) (P : BAPGraph E) (hN : P.g.Normal) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (hσ : p.1.σ = true ∧ q.1.σ = true) (a a' : P.I') (hx : p.1.src = Sum.inr a ∧ q.1.dst = Sum.inr a')
    (hsame : P.g.sameAtom (Sum.inr a) (Sum.inr a') = true) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
    (hint : P.g.intAtom (Sum.inr a) = true)
    (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨ ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0))
    {t : BAShape} {Q : BAPGraph E}
    (hQ : (t, Q) ∈ P.outsT (fun _ => BAShape.macroB) ((BAGraph.BAScost_trB P.g p q).gg2 (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
        (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2)))) ∨
      (t, Q) ∈ P.outsT (fun _ => BAShape.macroB) ((BAGraph.BAScost_trB P.g p q).gg4 (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
        (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2))))) : BASim_Goal m P Q := by
  have hsame' : P.g.sameAtom p.1.src q.1.dst = true := by rw [hx.1, hx.2]; exact hsame
  have hint' : P.g.intAtom p.1.src = true := by rw [hx.1]; exact hint
  have hpe : p.1 ∈ P.g.solid := lvl1_mem_split_fst _ p hp
  have hdeg : (P.g.atEdges p.1.src).length = 2 := by
    rw [hx.1]
    rcases hnb a hint with h | ⟨h, -⟩
    · exfalso
      have hm : p.1 ∈ P.g.atEdges (Sum.inr a) := by
        unfold BAGraph.atEdges
        rw [List.mem_filter]
        refine ⟨hpe, ?_⟩
        have := hwf p.1 hpe
        rw [hx.1] at this
        simp [BAScost_sameAtom_self, hx.1, this]
      exact absurd h (List.length_pos_of_mem hm).ne'
    · exact h
  have hRa := BASim_Ra P.g p q hp hq hwf hsame' hdeg
  obtain ⟨hinv, hwf', hint2, hnb'⟩ := BASim_trB_facts P.g p q hp hq hσ hsame' hwf hint' hRa hnb
  have hNg : (BAGraph.BAScost_trB P.g p q).Normal :=
    BAWeightOp_ext_normal 2 P.g hN _ _ _ _ (fun e he => BASim_hcirc hN hp e (lvl1_mem_split _ q hq e he)) (by simp [bpS])
  have hp2 : (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) ∈
      lwSplit (BASim_Ttr P (BAGraph.BAScost_trB P.g p q)).g.solid := by
    have := lvl1_split_last (q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) (bpS true (bpv 1) (owxEmb 2 p.1.dst))
    rwa [List.append_assoc] at this
  have hst := BAFrameStepT.gg (BASim_Ttr P (BAGraph.BAScost_trB P.g p q)) _ hp2 _ (lvl1_split_last _ _) ⟨rfl, rfl, rfl, rfl⟩ (Sum.inr 1) ⟨rfl, rfl⟩ hwf' hint2 hnb'
  rcases hQ with hQ | hQ
  · exact BASim_macro_out m P _ hNg hinv hst _ (fun t Q h => List.mem_append_left _ h) _ hQ
  · exact BASim_macro_out m P _ hNg hinv hst _ (fun t Q h => List.mem_append_right _ h) _ hQ

/-- the outputs of a list of normal terms with only circled solid edges: the packed merges of the terms themselves -/
theorem BASim_outsT_circ (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape) {Ts : List (BAGraph P.E' I')}
    (hTs : ∀ T ∈ Ts, T.Normal) {t : BAShape} {Q : BAPGraph E} (hQ : (t, Q) ∈ P.outsT tg Ts) : ∃ T ∈ Ts, Q = P.outOf T := by
  obtain ⟨T, hT, T', hT', -, rfl⟩ := BASim_mem_outsT P tg Ts t Q hQ
  rw [BAWeightOp_splitG_of_circ T (hTs T hT).2, List.mem_singleton] at hT'
  exact ⟨T, hT, by rw [hT']⟩

/-- **The term `d4` with `[y] = [y']` is simulated by the band's gg step at `P.img`** (at `A1`) -/
theorem BASim_d4_band (m : ℂ) (P : BAPGraph E) (hN : P.g.Normal) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ q.1.σ = true) (a a' : P.I')
    (hx : p.1.src = Sum.inr a ∧ q.1.dst = Sum.inr a') (hsame : P.g.sameAtom (Sum.inr a) (Sum.inr a') = true)
    (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) (hint : P.g.intAtom (Sum.inr a) = true)
    (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
      ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0))
    (hyy : P.g.sameAtom p.1.dst q.1.src = true) :
    ∃ L' : List (PGraph E), LocStep m P.img L' ∧ ∃ Q0 ∈ L', Q0.baInv = BASim_inv (BAGraph.ext 2 P.g q.2 [] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]) := by
  have hsame0 : P.g.sameAtom p.1.src q.1.dst = true := by rw [hx.1, hx.2]; exact hsame
  obtain ⟨x', hxa, hxq, hy, hy', hloc, -⟩ := BASim_locStep_gg P m hp hq h a a' hx hsame hwf hint hnb
  have hcirc : ∀ e ∈ q.2, e.circ = true := fun e he => BASim_hcirc hN hp e (lvl1_mem_split _ q hq e he)
  have hNA : (BAGGOp_A1 P.g p q).Normal := BAWeightOp_ext_normal 2 P.g hN _ _ _ _ hcirc (by simp)
  have hspl : (BAGGOp_A1 P.g p q).splitG = [BAGGOp_A1 P.g p q] := BAWeightOp_splitG_of_circ _ hNA.2
  have hC : BASim_Cons P.g 2 (BAGGOp_A1 P.g p q) (BAScost_rho2 p.1.src q.1.src) :=
    BASim_cons_of_md P.g P.g q.2 [] [bpW true (bpv 0) (bpv 1)] _ _ (BAScost_rho2_emb _ _)
      (fun a b h => BASim_sameAtom_of_adj _ h)
      (fun a b h => BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj (BASim_Ext_ext 2 P.g _ _ _ _) a b h))
      (fun e he => by
        simp only [BAGGOp_A1, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> simp only [bpM, BAScost_rho2_emb, BASim_rho2_alpha, BASim_rho2_beta]
        · exact BAScost_sameAtom_self _ _
        · exact BAScost_sameAtom_self _ _
        · exact BASim_sameAtom_symm' _ hyy
        · exact BAScost_sameAtom_self _ _)
  have hne : P.g.extraB (owxEmb 2) (BAGGOp_A1 P.g p q) = false := by
    unfold BAGraph.extraB
    rw [List.any_eq_false]
    intro e he
    simp [hC.sameAtom, hwf e he]
  obtain ⟨R, hR, hRE⟩ := BASim_match_A1 P hN m hp hq x' hxa (T' := BAGGOp_A1 P.g p q) (by rw [hspl]; exact List.mem_singleton_self _) hne
  refine ⟨_, hloc, R, hR, ?_⟩
  rw [BASim_baInv_of_equiv hRE, BASim_img_baInv, BASim_outOf_baInv P _ hNA, BASim_inv_d4_A1 P.g p q hsame0]

/-- **Macro (b), the transfer-family terms `d2, d3, d4`**: the order rises (`d2`, `d3`; `d4` with `[y] ≠ [y']`: or `nExt` falls), or (`d4` with `[y] = [y']`) the term is `A1` of the band's gg step -/
theorem BASim_macroB1 (m : ℂ) (P : BAPGraph E) (hN : P.g.Normal) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (hσ : p.1.σ = true ∧ q.1.σ = true) (a a' : P.I')
    (hx : p.1.src = Sum.inr a ∧ q.1.dst = Sum.inr a') (hsame : P.g.sameAtom (Sum.inr a) (Sum.inr a') = true)
    (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) (hint : P.g.intAtom (Sum.inr a) = true)
    (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
      ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0))
    {t : BAShape} {Q : BAPGraph E}
    (hQ : (t, Q) ∈ P.outsT (fun _ => BAShape.macroB)
      [BAGraph.ext 2 P.g q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)],
       BAGraph.ext 2 P.g q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)],
       BAGraph.ext 2 P.g q.2 [] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]]) :
    BASim_Goal m P Q := by
  have hsame0 : P.g.sameAtom p.1.src q.1.dst = true := by rw [hx.1, hx.2]; exact hsame
  have hcirc : ∀ e ∈ q.2, e.circ = true := fun e he => BASim_hcirc hN hp e (lvl1_mem_split _ q hq e he)
  obtain ⟨T, hT, rfl⟩ := BASim_outsT_circ P _ (fun T hT => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl <;> exact BAWeightOp_ext_normal 2 P.g hN _ _ _ _ hcirc (by simp [bpS])) hQ
  have hNT : T.Normal := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl <;> exact BAWeightOp_ext_normal 2 P.g hN _ _ _ _ hcirc (by simp [bpS])
  have hinv := BASim_outOf_inv P T hNT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  · exact Or.inr (Or.inl (hinv.1 ▸ BASim_ord_d2 P.g p q hp hq hsame0))
  · exact Or.inr (Or.inl (hinv.1 ▸ BASim_ord_d3 P.g p q hp hq hsame0))
  · by_cases hyy : P.g.sameAtom p.1.dst q.1.src = true
    · obtain ⟨L', hL, Q0, hQ0, hQ0'⟩ := BASim_d4_band m P hN hp hq hσ a a' hx hsame hwf hint hnb hyy
      refine Or.inl ⟨P, L', hN, rfl, hL, Q0, hQ0, ?_⟩
      rw [hQ0', BASim_outOf_baInv P _ hNT]
    · have hyy' : P.g.sameAtom p.1.dst q.1.src = false := by simpa using hyy
      rcases BASim_d4 P.g p q hp hq hsame0 hyy' with h | h
      · exact Or.inr (Or.inl (hinv.1 ▸ h))
      · exact Or.inr (Or.inr (hinv.2 ▸ h))

theorem BASim_tag_ok (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (htg : ∀ T', tg T' = BAShape.band ∨ tg T' = BAShape.e1 ∨ tg T' = BAShape.e2) {Ts : List (BAGraph P.E' I')} {t : BAShape} {Q : BAPGraph E}
    (hQ : (t, Q) ∈ P.outsT tg Ts) : t = BAShape.band ∨ t = BAShape.e1 ∨ t = BAShape.e2 := by
  obtain ⟨T, hT, T', hT', rfl, -⟩ := BASim_mem_outsT P tg Ts t Q hQ
  exact htg T'

/-- **`BAsim'`** (T2423 (a) T2): the simulation at a BA graph with the invariants of `P`. -/
theorem baSim'_holds (m : ℂ) : BAsim' m := by
  intro E P outs hst hN Q hQ
  obtain ⟨LT, hLT, rfl⟩ := (baFrameStepT_untag_holds P outs).1 hst
  obtain ⟨⟨t, Q'⟩, hmem, rfl⟩ := List.mem_map.1 hQ
  change BASim_Goal m P Q'
  have key : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape) (Ts : List (BAGraph P.E' I')),
      (∀ T', tg T' = BAShape.band ∨ tg T' = BAShape.e1 ∨ tg T' = BAShape.e2) → (t, Q') ∈ P.outsT tg Ts → BASim_Goal m P Q' :=
    fun tg Ts htg h => BASim_goal_of_step m P P hN rfl hLT hmem (BASim_tag_ok P tg htg h)
  have kstd : ∀ (k : ℕ) (Ts : List (BAGraph P.E' (P.I' ⊕ Fin k))), (t, Q') ∈ P.outsT (P.g.tagStd k) Ts → BASim_Goal m P Q' :=
    fun k Ts h => key (P.g.tagStd k) Ts (BASim_tagStd_cases P.g k) h
  have kT1 : ∀ (Ts : List (BAGraph P.E' (P.I' ⊕ Fin 2))), (t, Q') ∈ P.outsT P.g.tagT1 Ts → BASim_Goal m P Q' :=
    fun Ts h => key P.g.tagT1 Ts (BASim_tagT1_cases P.g) h
  cases hLT with
  | weight p hp h =>
    rcases List.mem_append.1 hmem with h' | h'
    · exact kstd _ _ h'
    · exact kstd _ _ h'
  | within p hp h =>
    unfold BAPGraph.withinOutsT at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (h' | h') | h'
    · exact kstd _ _ h'
    · exact BASim_macroA m P hN hp ⟨h.1, h.2.1⟩ h.2.2.2 (Or.inl h')
    · exact BASim_macroA m P hN hp ⟨h.1, h.2.1⟩ h.2.2.2 (Or.inr h')
  | edge p hp h x hx hwf hv hint hbad =>
    rcases List.mem_append.1 hmem with h' | h'
    · exact kT1 _ h'
    · exact kstd _ _ h'
  | gg p hp q hq h x hx hwf hint hnb =>
    rcases List.mem_append.1 hmem with h' | h'
    · exact kstd _ _ h'
    · exact kstd _ _ h'
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    have hq : q ∈ lwSplit p.2 := (List.mem_of_getElem? hj : q ∈ lwSplit p.2)
    unfold BAPGraph.splitOutsT at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with ((((h' | h') | h') | h') | h') | h'
    · exact kT1 _ h'
    · exact kstd _ _ h'
    · exact kstd _ _ h'
    · exact BASim_macroB1 m P hN hp hq ⟨h.1, h.2.2.1⟩ a a' hx hsame hwf hint hnb h'
    · exact BASim_macroB2 m P hN hp hq ⟨h.1, h.2.2.1⟩ a a' hx hsame hwf hint hnb (Or.inl h')
    · exact BASim_macroB2 m P hN hp hq ⟨h.1, h.2.2.1⟩ a a' hx hsame hwf hint hnb (Or.inr h')

end Macro

/-! ## Compiled instances (T2423 (a) (ii)): the data `P_A` (`gg`, in `BASim.lean`), `P_B` (`within`), `P_C` (`ggSplit`), `P_W` (`weight`), `P_E` (`edge`) -/
namespace BASimInst
/-- `P_B` (macro (a)): solid `2→3` inside the atom `{2,3}`, `0→2`, `1→4`; the `within` step at `p = 2→3`. -/
def baPB : BAGraph (Fin 2) (Fin 3) :=
  ⟨⟨[⟨true, true, .inr 0, .inr 1⟩, ⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inr 2⟩], [⟨false, true, .inr 2, .inr 1⟩], [], 1⟩, [], [⟨true, .inr 0, .inr 1⟩]⟩
def pB : Ed × List Ed := (⟨true, true, .inr 0, .inr 1⟩, [⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inr 2⟩])
/-- `P_C` (macro (b)): solid `2→1`, `0→3`, `1→0`, the pair `p = 2→1`, `q = 0→3` at the two vertices `2, 3` of one atom. -/
def baPC : BAGraph (Fin 2) (Fin 3) :=
  ⟨⟨[⟨true, true, .inr 0, .inl 1⟩, ⟨true, true, .inl 0, .inr 1⟩, ⟨true, true, .inl 1, .inl 0⟩], [⟨false, true, .inr 2, .inr 1⟩], [], 1⟩, [], [⟨true, .inr 0, .inr 1⟩]⟩
def pC : Ed × List Ed := (⟨true, true, .inr 0, .inl 1⟩, [⟨true, true, .inl 0, .inr 1⟩, ⟨true, true, .inl 1, .inl 0⟩])
def qC : Ed × List Ed := (⟨true, true, .inl 0, .inr 1⟩, [⟨true, true, .inl 1, .inl 0⟩])
/-- `P_W`: a self-loop at the internal vertex `0` and an edge `x → 1` (the `weight` step); `P_E`: a degree-3 internal vertex (the `edge` step). -/
def baPW : BAGraph (Fin 1) (Fin 2) := ⟨⟨[⟨true, true, .inr 0, .inr 0⟩, ⟨true, true, .inl 0, .inr 1⟩], [], [], 1⟩, [], []⟩
def pW : SEdge (Fin 1 ⊕ Fin 2) × List (SEdge (Fin 1 ⊕ Fin 2)) := (⟨true, true, .inr 0, .inr 0⟩, [⟨true, true, .inl 0, .inr 1⟩])
def baPE : BAGraph (Fin 2) (Fin 1) := ⟨⟨[⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inr 0, .inl 0⟩, ⟨true, true, .inl 1, .inr 0⟩,
  ⟨false, true, .inl 0, .inl 1⟩], [], [], 1⟩, [], []⟩
def pE : SEdge (Fin 2 ⊕ Fin 1) × List (SEdge (Fin 2 ⊕ Fin 1)) := (⟨true, true, .inr 0, .inl 0⟩, [⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inl 1, .inr 0⟩, ⟨false, true, .inl 0, .inl 1⟩])
/-- the tagged outputs of the `gg` step at `P_A` -/
def ggFT := (baPG baPA).outsT (baPA.tagStd 2) (baPA.gg2 pA qA) ++ (baPG baPA).outsT (baPA.tagStd 4) (baPA.gg4 pA qA)
theorem hTA : BAFrameStepT (baPG baPA) ggFT :=
  BAFrameStepT.gg (baPG baPA) pA (List.mem_cons_self ..) qA (List.mem_cons_self ..) (by decide) (0 : Fin 3) (by decide) (by decide) (by decide) (by decide)
theorem hTB : BAFrameStepT (baPG baPB) ((baPG baPB).withinOutsT pB) := BAFrameStepT.within (baPG baPB) pB (List.mem_cons_self ..) (by decide)
theorem hTC : BAFrameStepT (baPG baPC) ((baPG baPC).splitOutsT pC qC 0) :=
  BAFrameStepT.ggSplit (baPG baPC) pC (List.mem_cons_self ..) qC 0 rfl (by decide) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide : (0 : Fin 3) ≠ 1)
    (by decide) (by decide) (by decide) (by decide)
theorem hTW : BAFrameStepT (baPG baPW) ((baPG baPW).outsT (baPW.tagStd 2) (baPW.lw2 pW) ++ (baPG baPW).outsT (baPW.tagStd 4) (baPW.lw4 pW)) :=
  BAFrameStepT.weight (baPG baPW) pW (List.mem_cons_self ..) (by decide)
theorem hTE : BAFrameStepT (baPG baPE) ((baPG baPE).outsT baPE.tagT1 [BAGraph.lanlwT1 baPE pE] ++
    (baPG baPE).outsT (baPE.tagStd 2) ((lwSplit pE.2).map (BAGraph.lanlwD baPE pE))) :=
  BAFrameStepT.edge (baPG baPE) pE (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩)) (by decide) (0 : Fin 1) (by decide)
    (by decide) (by decide) (by decide) (by decide)
theorem tag_exists (l : List (BAShape × BAPGraph (Fin 2))) (t : BAShape) (h : t ∈ l.map Prod.fst) : ∃ Q, (t, Q) ∈ l := by
  obtain ⟨⟨t', Q⟩, hm, rfl⟩ := List.mem_map.1 h; exact ⟨Q, hm⟩
/-- **`baMatch_holds` and `baExtraGood_holds` at the data**: the `gg` step at `P_A` has `band`-tagged and `e2`-tagged outputs (kernel evaluation of `outsT`, `tagStd`); the `ggSplit` step at `P_C` has `band` and `e1` outputs; every deterministic hypothesis is discharged. -/
example (m : ℂ) :
    (∃ Q, (BAShape.band, Q) ∈ ggFT ∧ ∃ L' : List (PGraph (Fin 2)), LocStep m (baPG baPA).img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img) ∧
    (∃ Q, (BAShape.e2, Q) ∈ ggFT ∧ ((baPG baPA).g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < (baPG baPA).g.nExt)) ∧
    (∃ Q, (BAShape.band, Q) ∈ (baPG baPC).splitOutsT pC qC 0 ∧ ∃ L' : List (PGraph (Fin 2)), LocStep m (baPG baPC).img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img) ∧
    (∃ Q, (BAShape.e1, Q) ∈ (baPG baPC).splitOutsT pC qC 0 ∧ ((baPG baPC).g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < (baPG baPC).g.nExt)) := by
  obtain ⟨Q, hQ⟩ := tag_exists ggFT .band (by decide +kernel)
  obtain ⟨Q', hQ'⟩ := tag_exists ggFT .e2 (by decide +kernel)
  obtain ⟨R, hR⟩ := tag_exists ((baPG baPC).splitOutsT pC qC 0) .band (by decide +kernel)
  obtain ⟨R', hR'⟩ := tag_exists ((baPG baPC).splitOutsT pC qC 0) .e1 (by decide +kernel)
  exact ⟨⟨Q, hQ, baMatch_holds m _ _ hTA (by decide) Q hQ⟩, ⟨Q', hQ', baExtraGood_holds _ _ hTA (by decide) Q' (Or.inr hQ')⟩,
    ⟨R, hR, baMatch_holds m _ _ hTC (by decide) R hR⟩, ⟨R', hR', baExtraGood_holds _ _ hTC (by decide) R' (Or.inl hR')⟩⟩
/-- **`baSim'_holds` at the five steps** (`gg` at `P_A`, `within` at `P_B`, `ggSplit` at `P_C`, `weight` at `P_W`, `edge` at `P_E`; each has outputs): every output has the conclusion of `BAsim'`. -/
example (m : ℂ) :
    (∃ Q ∈ ggF, BASim_Goal m (baPG baPA) Q) ∧ (∃ Q ∈ (baPG baPB).withinOuts pB, BASim_Goal m (baPG baPB) Q) ∧
    (∃ Q ∈ (baPG baPC).splitOuts pC qC 0, BASim_Goal m (baPG baPC) Q) ∧
    (∃ Q ∈ (baPG baPW).outsOf (baPW.lw2 pW) ++ (baPG baPW).outsOf (baPW.lw4 pW), BASim_Goal m (baPG baPW) Q) ∧
    (∃ Q ∈ (baPG baPE).outsOf (BAGraph.lanlwTerms baPE pE), BASim_Goal m (baPG baPE) Q) := by
  have hF : ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal → 0 < outs.length → ∃ Q ∈ outs, BASim_Goal m P Q :=
    fun P outs h hN hl => by
      obtain ⟨Q, hQ⟩ := List.exists_mem_of_length_pos hl
      exact ⟨Q, hQ, baSim'_holds m P outs h hN Q hQ⟩
  refine ⟨hF _ _ (BAFrameStep.gg (baPG baPA) pA (List.mem_cons_self ..) qA (List.mem_cons_self ..) (by decide) (0 : Fin 3) (by decide) (by decide) (by decide) (by decide))
      (by decide) (by decide +kernel), hF _ _ (BAFrameStep.within (baPG baPB) pB (List.mem_cons_self ..) (by decide)) (by decide) (by decide +kernel),
    hF _ _ (BAFrameStep.ggSplit (baPG baPC) pC (List.mem_cons_self ..) qC 0 rfl (by decide) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide : (0 : Fin 3) ≠ 1)
      (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide +kernel),
    hF _ _ (BAFrameStep.weight (baPG baPW) pW (List.mem_cons_self ..) (by decide)) (by decide) (by decide +kernel),
    hF _ _ (BAFrameStep.edge (baPG baPE) pE (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩)) (by decide) (0 : Fin 1) (by decide)
      (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide +kernel)⟩
end BASimInst

end RBM.Graph

end
