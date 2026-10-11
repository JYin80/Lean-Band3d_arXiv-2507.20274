/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASim

/-!
# BA-L R1 `BASim`: the matching of a BA step with a band `LocStep` at the atomic image (T2423), part 2

Scratch skeleton (families).
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

section Weight
variable {E : Type}

/-- the first term of `lw2`: `M_{xα} S_{αβ} Ǧ_{αx} Ǧ_{ββ} f` -/
def BASim_leaf2 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I') (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph E' (I' ⊕ Fin 2) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]


/-- **`lw2.leaf` ↔ `owxT1`** (the table of T2423 (a) (i): `α ↦ x̄`, `β ↦ n0`); the edge `p.1` is a circled blue edge inside one atom (a weight, or the within-atom edge of macro (a)) -/
def BASim_B_leaf2 (P : BAPGraph E) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true) : BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)] (promoteC P.g).merge.solid [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, owxEmb 1 ((promoteC P.g).vmap p.1.src), Sum.inr (Sum.inr 0)⟩] [BAScost_imgE P.g p.1]
    (fun e he => lvl1_mem_split _ p hp e he) (BASim_restH_perm P hp) (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      have hv : (promoteC P.g).vmap p.1.dst = (promoteC P.g).vmap p.1.src :=
        ((BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _).2 h.2.2).symm
      have hsa' := h.2.2
      simp [BASim_phiE, bpS, SEdge.map, BAScost_imgE, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _),
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hv, h.1, h.2.1, hsa'])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _)])

/-- **The matching of the terms of `lw2.leaf`** with the first term `owxT1` of the weight step at the image -/
theorem BASim_match_leaf2 (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true)
    {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BASim_leaf2 P.g p).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_leaf2 P hp h).toData hN m) m hT' hne
  refine ⟨_, BASim_locStep_weight P m hp h, R, ?_, hRE⟩
  refine BASim_pack_mono P.img (L := (lwSymmOwxT1 false false m P.img.g ((promoteC P.g).vmap p.1.src)).partition m) ?_ hR
  intro Q hQ
  unfold lvl1WeightOuts0
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl hQ))


/-! ### The terms with four new vertices (`lw4`, `GGGamma` fourth sum): `z ↦ ā`, `y2, α ↦ n0`, `β ↦ n1` -/

/-- the derivative term of `lanlw` (`lw2.D`, the within-atom derivative): `lanlwD` with the new edges listed -/
def BASim_D2 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph E' (I' ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).1, (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).2,
    bpS false (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

theorem BASim_lanlwD_eq {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph.lanlwD Γ p q = BASim_D2 Γ p q := rfl

/-- **The derivative terms ↔ `oe1xD`/`owxT3`** (`α ↦ x̄ = x`, `β ↦ n0`; the third edge `G_{βy}` goes to `n0 → v`, `v` the image of the other end of the selected edge) -/
def BASim_B_Dgen (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (x v : (BASimX P) ⊕ (BASimY P)) (hx : x = (promoteC P.g).vmap p.1.src) (hv : v = (promoteC P.g).vmap p.1.dst) :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).1, (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).2,
      bpS false (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]
    (BASim_imgP P q).2
    [(owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 x) (SEdge.map (owxEmb 1) (BASim_imgP P q).1)).1,
      (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 x) (SEdge.map (owxEmb 1) (BASim_imgP P q).1)).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, owxEmb 1 x, Sum.inr (Sum.inr 0)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) (by simp [BASim_imgP]) (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      subst hx hv
      cases hσ : q.1.σ <;>
      simp [BASim_phiE, bpS, owxDE, SEdge.map, BASim_imgP, BAScost_imgE, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _),
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hσ])
    (by
      subst hx
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _)])

/-- **`lw2.D` ↔ `owxT3 q̄`**: the edge `q.1` of `f` is replaced by the two edges of its derivative (`α ↦ x̄`, `β ↦ n0`) -/
def BASim_B_D2 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true) :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_B_Dgen P hp hq _ _ rfl ((BAAtomic_promoteC_vmap_eq_sameAtom P.g p.1.src p.1.dst).2 h.2.2)

/-- **The matching of the terms of `lw2.D`** with the terms `owxT3 q̄` of the weight step at the image -/
theorem BASim_match_D2 (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true)
    {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BASim_D2 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_D2 P hp hq h).toData hN m) m hT' hne
  refine ⟨_, BASim_locStep_weight P m hp h, R, ?_, hRE⟩
  refine BASim_pack_mono P.img (L := (owxET3 m P.img.g ((promoteC P.g).vmap p.1.src) (BASim_imgP P q)).partition m) ?_ hR
  intro Q hQ
  refine (congrArg (fun l => Q ∈ l) (BASim_weightOuts0_ff m P.img.g (BASim_imgP P p) ((promoteC P.g).vmap p.1.src))).mpr ?_
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨BASim_imgP P q, BASim_imgP_mem2 P hq, hQ⟩)


/-! ### `lw4` ↔ `owxT2`, `owxT4` -/

/-- the new edges of the terms of `lw4`: the waved edges and the `M`-dotted edges (`B:376-387`, `BAWeightOp.lean:71-76`) -/
def BASim_w4 {V : Type} (z y α β : V) : List (WEdge V) := [bpW true z y, bpW false α β]
def BASim_md4 {V : Type} (x z y α : V) : List (BAMEdge V) := [bpM x z, bpM z x, bpM y α]

/-- the first term of `lw4`: `z, y2, α, β = bpv 0 .. bpv 3` -/
def BASim_leaf4 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph E' (I' ⊕ Fin 4) :=
  BAGraph.ext 4 Γ p.2 [bpS true (bpv 2) (bpv 1), bpS true (bpv 3) (bpv 3)] (BASim_w4 (bpv 0) (bpv 1) (bpv 2) (bpv 3))
    (BASim_md4 (owxEmb 4 p.1.src) (bpv 0) (bpv 1) (bpv 2))

/-- the derivative terms of `lw4` -/
def BASim_D4 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph E' (I' ⊕ Fin 4) :=
  BAGraph.ext 4 Γ q.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1, (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2,
    bpS false (bpv 3) (bpv 1)] (BASim_w4 (bpv 0) (bpv 1) (bpv 2) (bpv 3)) (BASim_md4 (owxEmb 4 p.1.src) (bpv 0) (bpv 1) (bpv 2))

theorem BASim_lw4_eq {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : Γ.lw4 p = BASim_leaf4 Γ p :: (lwSplit p.2).map (BASim_D4 Γ p) := rfl

theorem BASim_lw2_eq {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : Γ.lw2 p = BASim_leaf2 Γ p :: (lwSplit p.2).map (BASim_D2 Γ p) := rfl

/-- **`lw4.leaf` ↔ `owxT2`** (`z ↦ x̄`, `y2, α ↦ n0`, `β ↦ n1`) -/
def BASim_B_leaf4 (P : BAPGraph E) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) :
    BASimExt P 4 ((BASimY P) ⊕ Fin 2) (owxEmb 2) :=
  BASim_mk42 P p.1.src p.2 [bpS true (bpv 2) (bpv 1), bpS true (bpv 3) (bpv 3)] (BASim_w4 (bpv 0) (bpv 1) (bpv 2) (bpv 3))
    (BASim_md4 (owxEmb 4 p.1.src) (bpv 0) (bpv 1) (bpv 2)) (BASim_imgP P p).2
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩, ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩]
    [⟨true, true, owxEmb 2 ((promoteC P.g).vmap p.1.src), Sum.inr (Sum.inr 0)⟩, ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩] []
    (fun e he => lvl1_mem_split _ p hp e he) (by simp [BASim_imgP]) (by simp [BASim_md4]) (by simp [BASim_md4])
    (fun m' hm' => by simp only [BASim_md4, List.mem_cons, List.not_mem_nil, or_false] at hm'; rcases hm' with rfl | rfl | rfl; exacts [Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))])
    (by
      simp [BASim_phiE, bpS, SEdge.map, BASim_phi42_one, BASim_phi42_two, BASim_phi42_three])
    (by
      refine List.Forall₂.cons (Or.inl ?_) (List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil)
      · simp only [WEdge.map, bpW, BASim_w4, BASim_phi42_zero, BASim_phi42_one]
      · simp only [WEdge.map, bpW, BASim_w4, BASim_phi42_two, BASim_phi42_three])

/-- **`lw4.D` ↔ `owxT4 q̄`** -/
def BASim_B_D4 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) : BASimExt P 4 ((BASimY P) ⊕ Fin 2) (owxEmb 2) :=
  BASim_mk42 P p.1.src q.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1, (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2,
      bpS false (bpv 3) (bpv 1)] (BASim_w4 (bpv 0) (bpv 1) (bpv 2) (bpv 3))
    (BASim_md4 (owxEmb 4 p.1.src) (bpv 0) (bpv 1) (bpv 2)) (BASim_imgP P q).2
    [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BASim_imgP P q).1)).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BASim_imgP P q).1)).2,
      ⟨true, false, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 0)⟩]
    [⟨true, true, owxEmb 2 ((promoteC P.g).vmap p.1.src), Sum.inr (Sum.inr 0)⟩, ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) (by simp [BASim_imgP]) (by simp [BASim_md4]) (by simp [BASim_md4])
    (fun m' hm' => by simp only [BASim_md4, List.mem_cons, List.not_mem_nil, or_false] at hm'; rcases hm' with rfl | rfl | rfl; exacts [Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))])
    (by
      cases hσ : q.1.σ <;>
      simp [BASim_phiE, bpS, owxDE, SEdge.map, BASim_imgP, BAScost_imgE, BASim_phi_emb, BASim_phi42_zero, BASim_phi42_one, BASim_phi42_two,
        BASim_phi42_three, hσ])
    (by
      refine List.Forall₂.cons (Or.inl ?_) (List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil)
      · simp only [WEdge.map, bpW, BASim_w4, BASim_phi42_zero, BASim_phi42_one]
      · simp only [WEdge.map, bpW, BASim_w4, BASim_phi42_two, BASim_phi42_three])


/-- **The matching of the terms of `lw4.leaf`** with the second term `owxT2` of the weight step -/
theorem BASim_match_leaf4 (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true)
    {T' : BAGraph P.E' (P.I' ⊕ Fin 4)} (hT' : T' ∈ (BASim_leaf4 P.g p).splitG) (hne : P.g.extraB (owxEmb 4) T' = false) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_leaf4 P hp).toData hN (m ^ 3)) m hT' hne
  refine ⟨_, BASim_locStep_weight P m hp h, R, ?_, hRE⟩
  refine BASim_pack_mono P.img (L := (owxET2 m P.img.g (BASim_imgP P p) ((promoteC P.g).vmap p.1.src)).partition m) ?_ hR
  intro Q hQ
  refine (congrArg (fun l => Q ∈ l) (BASim_weightOuts0_ff m P.img.g (BASim_imgP P p) ((promoteC P.g).vmap p.1.src))).mpr ?_
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr hQ))

/-- **The matching of the terms of `lw4.D`** with the terms `owxT4 q̄` -/
theorem BASim_match_D4 (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true)
    {T' : BAGraph P.E' (P.I' ⊕ Fin 4)} (hT' : T' ∈ (BASim_D4 P.g p q).splitG) (hne : P.g.extraB (owxEmb 4) T' = false) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_D4 P hp hq).toData hN (m ^ 3)) m hT' hne
  refine ⟨_, BASim_locStep_weight P m hp h, R, ?_, hRE⟩
  refine BASim_pack_mono P.img (L := (owxET4 m P.img.g ((promoteC P.g).vmap p.1.src) (BASim_imgP P q)).partition m) ?_ hR
  intro Q hQ
  refine (congrArg (fun l => Q ∈ l) (BASim_weightOuts0_ff m P.img.g (BASim_imgP P p) ((promoteC P.g).vmap p.1.src))).mpr ?_
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨BASim_imgP P q, BASim_imgP_mem2 P hq, hQ⟩

/-- **Weight (`lem_lweight`): the band-tagged outputs are matched** with the outputs of the weight step at the image -/
theorem BASim_matchLT_weight (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) (Q : BAPGraph E)
    (hQ : (BAShape.band, Q) ∈ P.outsT (P.g.tagStd 2) (P.g.lw2 p) ++ P.outsT (P.g.tagStd 4) (P.g.lw4 p)) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img := by
  have hsa : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true :=
    ⟨h.1, h.2.1, by rw [← h.2.2]; exact BAScost_sameAtom_self _ _⟩
  rcases List.mem_append.1 hQ with hQ | hQ
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT _ _ _ _ _ hQ
    have hne := BASim_tagStd_band _ _ _ htag
    rw [BASim_lw2_eq] at hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact BASim_match_leaf2 P hN m hp hsa hT' hne
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT
      exact BASim_match_D2 P hN m hp hq hsa hT' hne
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT _ _ _ _ _ hQ
    have hne := BASim_tagStd_band _ _ _ htag
    rw [BASim_lw4_eq] at hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact BASim_match_leaf4 P hN m hp hsa hT' hne
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT
      exact BASim_match_D4 P hN m hp hq hsa hT' hne

/-! ### Macro step (a), stage 1: the within-atom edge (`BAPGraph.withinOutsT`) -/

/-- the first term of the stage 1 of macro step (a): `lanlw` at `Ǧ_{xy}`, `[x] = [y]`, with `G_{αy}` circled (the new loop `Ǧ_{ββ}` listed first) -/
def BASim_Wfirst {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph E' (I' ⊕ Fin 2) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- **`W.first` ↔ `owxT1`** -/
def BASim_B_Wfirst (P : BAPGraph E) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true) : BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)] (promoteC P.g).merge.solid [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, owxEmb 1 ((promoteC P.g).vmap p.1.src), Sum.inr (Sum.inr 0)⟩] [BAScost_imgE P.g p.1]
    (fun e he => lvl1_mem_split _ p hp e he) (BASim_restH_perm P hp) (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      have hv : (promoteC P.g).vmap p.1.dst = (promoteC P.g).vmap p.1.src :=
        ((BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _).2 h.2.2).symm
      have hsa' := h.2.2
      refine List.Perm.trans ?_ (List.Perm.swap _ _ _)
      simp [BASim_phiE, bpS, SEdge.map, BAScost_imgE, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _),
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hv, h.1, h.2.1, hsa'])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _)])

theorem BASim_match_Wfirst (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true)
    {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BASim_Wfirst P.g p).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_Wfirst P hp h).toData hN m) m hT' hne
  refine ⟨_, BASim_locStep_weight P m hp h, R, ?_, hRE⟩
  refine BASim_pack_mono P.img (L := (owxET1 m P.img.g ((promoteC P.g).vmap p.1.src)).partition m) ?_ hR
  intro Q hQ
  refine (congrArg (fun l => Q ∈ l) (BASim_weightOuts0_ff m P.img.g (BASim_imgP P p) ((promoteC P.g).vmap p.1.src))).mpr ?_
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl hQ))

/-- **Macro step (a), stage 1: the band-tagged outputs are matched** with the outputs of the weight step at the image (the stage 2 outputs are tagged `macroA`) -/
theorem BASim_matchLT_within (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src ≠ p.1.dst ∧ P.g.sameAtom p.1.src p.1.dst = true)
    (Q : BAPGraph E) (hQ : (BAShape.band, Q) ∈ P.withinOutsT p) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img := by
  have hsa : p.1.σ = true ∧ p.1.circ = true ∧ P.g.sameAtom p.1.src p.1.dst = true := ⟨h.1, h.2.1, h.2.2.2⟩
  unfold BAPGraph.withinOutsT at hQ
  rcases List.mem_append.1 hQ with hQ | hQ
  · rcases List.mem_append.1 hQ with hQ | hQ
    · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT _ _ _ _ _ hQ
      have hne := BASim_tagStd_band _ _ _ htag
      rcases List.mem_cons.1 hT with rfl | hT
      · exact BASim_match_Wfirst P hN m hp hsa hT' hne
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT
        exact BASim_match_D2 P hN m hp hq hsa hT' hne
    · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT _ _ _ _ _ hQ
      exact BAShape.noConfusion htag
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT _ _ _ _ _ hQ
    exact BAShape.noConfusion htag

end Weight

/-! ## The step at an internal vertex (`BAFrameStepT.edge`): the loop of the derivative terms -/

section Edge
variable {E : Type}

/-- `T'` is a term of `G = Ǧ + M` on `T` with the split `r`, up to the order of the `M`-dotted edges -/
structure BASim_IsSplit {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (T : BAGraph E' I')
    (r : List (SEdge (E' ⊕ I')) × List (BAMEdge (E' ⊕ I'))) (T' : BAGraph E' I') : Prop where
  hsolid : T'.solid = r.1
  hwaved : T'.waved = T.waved
  hdotted : T'.dotted = T.dotted
  hpsi : T'.psi = T.psi
  hmdot : ∀ m', m' ∈ T'.mdot ↔ m' ∈ r.2 ++ T.mdot

theorem BASim_baSplit_append_circ {V : Type*} (A B : List (SEdge V)) (hA : ∀ e ∈ A, e.circ = true) :
    ∀ r ∈ baSplitSolid (A ++ B), ∃ rB ∈ baSplitSolid B, r = (A ++ rB.1, rB.2) := by
  induction A with
  | nil => intro r hr; exact ⟨r, hr, by simp⟩
  | cons e A ih =>
    intro r hr
    simp only [List.cons_append, baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    obtain ⟨rB, hrB, rfl⟩ := ih (fun e' he' => hA e' (List.mem_cons_of_mem _ he')) r' hr'
    simp only [hA e List.mem_cons_self, ↓reduceIte, List.mem_singleton] at hr
    exact ⟨rB, hrB, by rw [hr]; simp⟩

theorem BASim_baSplit_append_circ' {V : Type*} (A B : List (SEdge V)) (hA : ∀ e ∈ A, e.circ = true) :
    ∀ rB ∈ baSplitSolid B, (A ++ rB.1, rB.2) ∈ baSplitSolid (A ++ B) := by
  induction A with
  | nil => intro r hr; simpa using hr
  | cons e A ih =>
    intro rB hrB
    simp only [List.cons_append, baSplitSolid, List.mem_flatMap]
    refine ⟨(A ++ rB.1, rB.2), ih (fun e' he' => hA e' (List.mem_cons_of_mem _ he')) rB hrB, ?_⟩
    simp only [hA e List.mem_cons_self, ↓reduceIte, List.mem_singleton]

theorem BASim_baSplit_cons_unc {V : Type*} (e : SEdge V) (es : List (SEdge V)) (he : e.circ = false) :
    ∀ r ∈ baSplitSolid (e :: es), (∃ r' ∈ baSplitSolid es, r = ({ e with circ := true } :: r'.1, r'.2)) ∨
      (∃ r' ∈ baSplitSolid es, r = (r'.1, BAMEdge.mk e.σ e.src e.dst :: r'.2)) := by
  intro r hr
  simp only [baSplitSolid, List.mem_flatMap] at hr
  obtain ⟨r', hr', hr⟩ := hr
  simp only [he, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inl ⟨r', hr', rfl⟩
  · exact Or.inr ⟨r', hr', rfl⟩

theorem BASim_baSplit_cons_circ' {V : Type*} (e : SEdge V) (es : List (SEdge V)) (he : e.circ = true) :
    ∀ r' ∈ baSplitSolid es, (e :: r'.1, r'.2) ∈ baSplitSolid (e :: es) := by
  intro r' hr'
  simp only [baSplitSolid, List.mem_flatMap]
  exact ⟨r', hr', by simp [he]⟩

theorem BASim_baSplit_cons_unc' {V : Type*} (e : SEdge V) (es : List (SEdge V)) (he : e.circ = false) :
    (∀ r' ∈ baSplitSolid es, ({ e with circ := true } :: r'.1, r'.2) ∈ baSplitSolid (e :: es)) ∧
      ∀ r' ∈ baSplitSolid es, (r'.1, BAMEdge.mk e.σ e.src e.dst :: r'.2) ∈ baSplitSolid (e :: es) := by
  refine ⟨fun r' hr' => ?_, fun r' hr' => ?_⟩ <;>
  · simp only [baSplitSolid, List.mem_flatMap]
    refine ⟨r', hr', ?_⟩
    simp [he]

theorem BASim_baSplit_append {V : Type*} (A B : List (SEdge V)) :
    ∀ r ∈ baSplitSolid (A ++ B), ∃ rA ∈ baSplitSolid A, ∃ rB ∈ baSplitSolid B, r = (rA.1 ++ rB.1, rA.2 ++ rB.2) := by
  induction A with
  | nil => intro r hr; exact ⟨([], []), by simp [baSplitSolid], r, hr, by simp⟩
  | cons e A ih =>
    intro r hr
    simp only [List.cons_append, baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    obtain ⟨rA, hrA, rB, hrB, rfl⟩ := ih r' hr'
    by_cases hc : e.circ = true
    · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      refine ⟨(e :: rA.1, rA.2), ?_, rB, hrB, by simp⟩
      simp only [baSplitSolid, List.mem_flatMap]
      exact ⟨rA, hrA, by simp [hc]⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨({ e with circ := true } :: rA.1, rA.2), ?_, rB, hrB, by simp⟩
        simp only [baSplitSolid, List.mem_flatMap]
        exact ⟨rA, hrA, by simp [hc]⟩
      · refine ⟨(rA.1, BAMEdge.mk e.σ e.src e.dst :: rA.2), ?_, rB, hrB, by simp⟩
        simp only [baSplitSolid, List.mem_flatMap]
        exact ⟨rA, hrA, by simp [hc]⟩

theorem BASim_baSplit_append' {V : Type*} (A B : List (SEdge V)) :
    ∀ rA ∈ baSplitSolid A, ∀ rB ∈ baSplitSolid B, (rA.1 ++ rB.1, rA.2 ++ rB.2) ∈ baSplitSolid (A ++ B) := by
  induction A with
  | nil =>
    intro rA hrA rB hrB
    simp only [baSplitSolid, List.mem_singleton] at hrA
    subst hrA
    simpa using hrB
  | cons e A ih =>
    intro rA hrA rB hrB
    simp only [baSplitSolid, List.mem_flatMap] at hrA
    obtain ⟨rA', hrA', hrA⟩ := hrA
    have := ih rA' hrA' rB hrB
    simp only [List.cons_append, baSplitSolid, List.mem_flatMap]
    refine ⟨_, this, ?_⟩
    by_cases hc : e.circ = true
    · simp only [hc, ↓reduceIte, List.mem_singleton] at hrA ⊢
      subst hrA
      simp
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hrA ⊢
      rcases hrA with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)

/-- **The loop of a derivative term**: a term of the `M`-splits of `T` (with the uncircled edge `e` among the new edges, `s = s₀ ++ e :: s₁`) is a term of the `M`-splits of
`T_c` (`e` circled) or of `T_m` (`e` an `M`-dotted edge) -/
theorem BASim_split_loop {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] {k : ℕ} (Γ : BAGraph E' I')
    (rest : List (SEdge (E' ⊕ I'))) (hrest : ∀ e ∈ rest, e.circ = true) (s0 : List (SEdge (E' ⊕ (I' ⊕ Fin k)))) (e : SEdge (E' ⊕ (I' ⊕ Fin k)))
    (he : e.circ = false) (s1 : List (SEdge (E' ⊕ (I' ⊕ Fin k)))) (w : List (WEdge (E' ⊕ (I' ⊕ Fin k)))) (md : List (BAMEdge (E' ⊕ (I' ⊕ Fin k))))
    {T' : BAGraph E' (I' ⊕ Fin k)} {r : List (SEdge (E' ⊕ (I' ⊕ Fin k))) × List (BAMEdge (E' ⊕ (I' ⊕ Fin k)))}
    (hr : r ∈ baSplitSolid (BAGraph.ext k Γ rest (s0 ++ e :: s1) w md).solid)
    (hT' : BASim_IsSplit (BAGraph.ext k Γ rest (s0 ++ e :: s1) w md) r T') :
    (∃ r' ∈ baSplitSolid (BAGraph.ext k Γ rest (s0 ++ { e with circ := true } :: s1) w md).solid,
      BASim_IsSplit (BAGraph.ext k Γ rest (s0 ++ { e with circ := true } :: s1) w md) r' T') ∨
    (∃ r' ∈ baSplitSolid (BAGraph.ext k Γ rest (s0 ++ s1) w (BAMEdge.mk e.σ e.src e.dst :: md)).solid,
      BASim_IsSplit (BAGraph.ext k Γ rest (s0 ++ s1) w (BAMEdge.mk e.σ e.src e.dst :: md)) r' T') := by
  have hA : ∀ e ∈ rest.map (SEdge.map (owxEmb k)), e.circ = true := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hrest e0 he0
  change r ∈ baSplitSolid (rest.map (SEdge.map (owxEmb k)) ++ (s0 ++ e :: s1)) at hr
  obtain ⟨rB, hrB, rfl⟩ := BASim_baSplit_append_circ _ _ hA r hr
  obtain ⟨r0, hr0, rC, hrC, rfl⟩ := BASim_baSplit_append _ _ rB hrB
  rcases BASim_baSplit_cons_unc e s1 he rC hrC with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
  · left
    refine ⟨(rest.map (SEdge.map (owxEmb k)) ++ (r0.1 ++ ({ e with circ := true } :: r'.1)), r0.2 ++ r'.2), ?_, ?_⟩
    · exact BASim_baSplit_append_circ' _ _ hA _ (BASim_baSplit_append' _ _ r0 hr0 _ (BASim_baSplit_cons_circ' _ _ rfl r' hr'))
    · refine ⟨hT'.hsolid, hT'.hwaved, hT'.hdotted, hT'.hpsi, fun m' => ?_⟩
      rw [hT'.hmdot]
      change (m' ∈ (r0.2 ++ r'.2) ++ (md ++ Γ.mdot.map (BAMEdge.map (owxEmb k)))) ↔ (m' ∈ (r0.2 ++ r'.2) ++ (md ++ Γ.mdot.map (BAMEdge.map (owxEmb k))))
      exact Iff.rfl
  · right
    refine ⟨(rest.map (SEdge.map (owxEmb k)) ++ (r0.1 ++ r'.1), r0.2 ++ r'.2), ?_, ?_⟩
    · exact BASim_baSplit_append_circ' _ _ hA _ (BASim_baSplit_append' _ _ r0 hr0 _ hr')
    · refine ⟨hT'.hsolid, hT'.hwaved, hT'.hdotted, hT'.hpsi, fun m' => ?_⟩
      rw [hT'.hmdot]
      change (m' ∈ (r0.2 ++ (BAMEdge.mk e.σ e.src e.dst :: r'.2)) ++ (md ++ Γ.mdot.map (BAMEdge.map (owxEmb k)))) ↔
        (m' ∈ (r0.2 ++ r'.2) ++ ((BAMEdge.mk e.σ e.src e.dst :: md) ++ Γ.mdot.map (BAMEdge.map (owxEmb k))))
      simp only [List.mem_append, List.mem_cons]
      tauto

/-- the outputs of the edge step at the selector `(0, 0)`: the frame is the graph with the selected edge uncircled -/
theorem BASim_edgeOuts0_ff {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (v : E' ⊕ I') :
    lvl1EdgeOuts0 m Γ p x v false false = (owxT1 m (lwSymmUncirc Γ p) x).partition m ++
      (lwSplit p.2).flatMap (fun q => (oe1xDs m (lwSymmUncirc Γ p) x v q).flatMap (fun T => T.partition m)) := by
  have h1 : lwSymmTwistG false false = (id : LGraph E' (I' ⊕ Fin 1) → LGraph E' (I' ⊕ Fin 1)) := funext fun _ => rfl
  simp only [lvl1EdgeOuts0, lwSymmOe1xOwx, lwSymmOe1xDs, lwSymmFrame, BASim_twistP_ff, h1, List.map_id]
  rfl

/-- **The band step at the image of an edge at an internal vertex** (`LocStep.edge` at `(0, 0)`): the image of the internal atom of `x` is an internal vertex `x'` whose degree
or charge is bad -/
theorem BASim_locStep_edge (P : BAPGraph E) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true) (x : P.I') (hx : p.1.src = Sum.inr x)
    (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) (hv : P.g.sameAtom p.1.src p.1.dst = false)
    (hint : P.g.intAtom (Sum.inr x) = true)
    (hbad : P.g.atEdges (Sum.inr x) ≠ [] ∧ ((P.g.atEdges (Sum.inr x)).length ≠ 2 ∨ P.g.atCharge (Sum.inr x) ≠ 0)) :
    ∃ x' : BASimY P, (promoteC P.g).vmap (Sum.inr x) = Sum.inr x' ∧
      LocStep m P.img (lvl1Pack P.img (lvl1EdgeOuts0 m P.img.g (BASim_imgP P p) x' ((promoteC P.g).vmap p.1.dst) false false)) := by
  have hR := (BAAtomic_promoteC_vmap_isRight P.g (Sum.inr x)).2 hint
  obtain ⟨x', hx'⟩ : ∃ x' : BASimY P, (promoteC P.g).vmap (Sum.inr x) = Sum.inr x' := by
    rcases hvm : (promoteC P.g).vmap (Sum.inr x) with a | x'
    · rw [hvm] at hR; exact absurd hR (by simp)
    · exact ⟨x', rfl⟩
  refine ⟨x', hx', ?_⟩
  have hne : (promoteC P.g).vmap p.1.dst ≠ Sum.inr x' := by
    intro hc
    rw [← hx', ← hx] at hc
    have := (BAAtomic_promoteC_vmap_eq_sameAtom P.g p.1.src p.1.dst).1 hc.symm
    rw [hv] at this
    exact Bool.noConfusion this
  refine LocStep.edge P.img (BASim_imgP P p) (BASim_imgP_mem P hp) x' ((promoteC P.g).vmap p.1.dst) hne false false ?_ ?_ ?_
  · show BAScost_imgE P.g p.1 = ⟨true, (BAScost_imgE P.g p.1).circ, Sum.inr x', (promoteC P.g).vmap p.1.dst⟩
    simp only [BAScost_imgE, h.1, hx, hx']
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 (show e ∈ P.g.solid.map (BAScost_imgE P.g) by rw [← BAScost_img_solid]; exact he)
    intro hc
    have := (BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _).1 hc
    rw [hwf e0 he0] at this
    exact Bool.noConfusion this
  · have hdeg : (promoteC P.g).merge.lvl1DegAt (Sum.inr x') = (P.g.atEdges (Sum.inr x)).length := by
      rw [← hx']
      unfold LGraph.lvl1DegAt
      rw [BAAtomic_solidAt, List.length_map]
    have hch : (promoteC P.g).merge.lvl1ChargeAt (Sum.inr x') = P.g.atCharge (Sum.inr x) := by
      rw [← hx']
      exact BAAtomic_charge P.g _
    have hnil : (P.g.atEdges (Sum.inr x)).length ≠ 0 := fun h0 => hbad.1 (List.length_eq_zero_iff.1 h0)
    show (promoteC P.g).merge.lvl1DegAt (Sum.inr x') ≠ 0 ∧ ((promoteC P.g).merge.lvl1DegAt (Sum.inr x') ≠ 2 ∨ (promoteC P.g).merge.lvl1ChargeAt (Sum.inr x') ≠ 0)
    rw [hdeg, hch]
    exact ⟨hnil, hbad.2⟩

/-! ### `lanlw`, term 1: `L1` ↔ `owxT1` at the frame -/

theorem BASim_owxEmb1_inr {E' I' : Type} (x : I') : (owxEmb 1 (Sum.inr x) : E' ⊕ (I' ⊕ Fin 1)) = Sum.inr (Sum.inl x) := rfl

/-- the first term of `lanlw` (`B:363`): `M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} f` -/
def BASim_L1 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph E' (I' ⊕ Fin 2) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

theorem BASim_lanlwT1_eq {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I')
    (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : BAGraph.lanlwT1 Γ p = BASim_L1 Γ p := rfl

/-- **`L1` ↔ `owxT1` at the frame** (`α ↦ x̄`, `β ↦ n0`; the frame has the selected edge uncircled) -/
def BASim_B_L1 (P : BAPGraph E) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hσ : p.1.σ = true) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') : BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)] ({ (BASim_imgP P p).1 with circ := false } :: (BASim_imgP P p).2)
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩]
    [{ (BASim_imgP P p).1 with circ := false }]
    (fun e he => lvl1_mem_split _ p hp e he) (by simp [BASim_imgP]) (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      refine List.Perm.trans ?_ (List.Perm.swap _ _ _)
      simp [BASim_phiE, bpS, SEdge.map, BASim_imgP, BAScost_imgE, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _),
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx', hσ, BASim_owxEmb1_inr])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx',
        BASim_owxEmb1_inr])

/-! ### The derivative terms with a loop at `x`: `oe1xP5`, `oe1xP3` (red out-edge of `x`), `oe1xP6`, `oe1xP4` (blue in-edge of `x`) -/

/-- the new solid edges of a derivative term of `lanlw` (`B:363`): the two edges of `owxDE β α` and `G_{βy}` -/
def BASim_dE1 {E' I' : Type} (q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : SEdge (E' ⊕ (I' ⊕ Fin 2)) :=
  (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).1
def BASim_dE2 {E' I' : Type} (q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : SEdge (E' ⊕ (I' ⊕ Fin 2)) :=
  (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q.1)).2
def BASim_dE3 {E' I' : Type} (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) : SEdge (E' ⊕ (I' ⊕ Fin 2)) :=
  bpS false (bpv 1) (owxEmb 2 p.1.dst)

/-- **`LD` with the red loop kept ↔ `oe1xP5`** (`q.1 = Ḡ_{s d}`, `s` in the atom of `x`: the first new edge is the loop `Ḡ_{sα}`, circled) -/
def BASim_B_P5 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (hσ : q.1.σ = false) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hqs : (promoteC P.g).vmap q.1.src = Sum.inr x') : BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2 ({ BASim_dE1 q with circ := true } :: [BASim_dE2 q, BASim_dE3 p]) [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)] (BASim_imgP P q).2
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inl x')⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 (BASim_imgP P q).1.dst⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC P.g).vmap p.1.dst)⟩]
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) (by simp [BASim_imgP]) (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      simp [BASim_dE1, BASim_dE2, BASim_dE3, BASim_phiE, bpS, owxDE, SEdge.map, BASim_imgP, BAScost_imgE, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _),
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hσ, hx', hqs, BASim_owxEmb1_inr])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx',
        BASim_owxEmb1_inr])

/-- **`LD` with the red loop dropped ↔ `oe1xP3`** (the loop `Ḡ_{sα}` is the `M`-dotted edge `M̄_{sα}`) -/
def BASim_B_P3 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (hσ : q.1.σ = false) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hqs : (promoteC P.g).vmap q.1.src = Sum.inr x') : BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2 [BASim_dE2 q, BASim_dE3 p] [bpW false (bpv 0) (bpv 1)]
    [BAMEdge.mk (BASim_dE1 q).σ (BASim_dE1 q).src (BASim_dE1 q).dst, bpM (owxEmb 2 p.1.src) (bpv 0)] (BASim_imgP P q).2
    [⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 (BASim_imgP P q).1.dst⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC P.g).vmap p.1.dst)⟩]
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) (by simp [BASim_imgP])
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (fun m' hm' => by
      rcases List.mem_cons.1 hm' with rfl | hm'
      · simp only [BASim_dE1, owxDE, hσ, SEdge.map, Bool.false_eq_true, ↓reduceIte, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _)]
        rw [hqs, hx']
      · rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      simp [BASim_dE2, BASim_dE3, BASim_phiE, bpS, owxDE, SEdge.map, BASim_imgP, BAScost_imgE, BASim_phi_emb,
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hσ])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx',
        BASim_owxEmb1_inr])

/-- **`LD` with the blue loop kept ↔ `oe1xP6`** (`q.1 = G_{s d}`, `d` in the atom of `x`: the second new edge is the loop `G_{αd}`, circled) -/
def BASim_B_P6 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (hσ : q.1.σ = true) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hqd : (promoteC P.g).vmap q.1.dst = Sum.inr x') : BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2 [BASim_dE1 q, { BASim_dE2 q with circ := true }, BASim_dE3 p] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)] (BASim_imgP P q).2
    [⟨true, false, owxEmb 1 (BASim_imgP P q).1.src, Sum.inr (Sum.inr 0)⟩, ⟨true, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inl x')⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC P.g).vmap p.1.dst)⟩]
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) (by simp [BASim_imgP]) (List.mem_singleton_self _)
    (fun m' hm' => by rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      simp [BASim_dE1, BASim_dE2, BASim_dE3, BASim_phiE, bpS, owxDE, SEdge.map, BASim_imgP, BAScost_imgE, BASim_phi_emb,
        BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hσ, hx', hqd, BASim_owxEmb1_inr])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx',
        BASim_owxEmb1_inr])

/-- **`LD` with the blue loop dropped ↔ `oe1xP4`** -/
def BASim_B_P4 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (hσ : q.1.σ = true) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hqd : (promoteC P.g).vmap q.1.dst = Sum.inr x') : BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2 [BASim_dE1 q, BASim_dE3 p] [bpW false (bpv 0) (bpv 1)]
    [BAMEdge.mk (BASim_dE2 q).σ (BASim_dE2 q).src (BASim_dE2 q).dst, bpM (owxEmb 2 p.1.src) (bpv 0)] (BASim_imgP P q).2
    [⟨true, false, owxEmb 1 (BASim_imgP P q).1.src, Sum.inr (Sum.inr 0)⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC P.g).vmap p.1.dst)⟩]
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he)) (by simp [BASim_imgP])
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (fun m' hm' => by
      rcases List.mem_cons.1 hm' with rfl | hm'
      · simp only [BASim_dE2, owxDE, hσ, SEdge.map, ↓reduceIte, BASim_phi_emb, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _)]
        rw [hqd, hx']
      · rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      simp [BASim_dE1, BASim_dE3, BASim_phiE, bpS, owxDE, SEdge.map, BASim_imgP, BAScost_imgE, BASim_phi_emb,
        BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hσ])
    (by
      refine List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil
      simp only [WEdge.map, bpW, BASim_phi_some _ _ _ _ 0 p.1.src (BASim_anch2_zero _), BASim_phi_none _ _ _ _ 1 (BASim_anch2_one _), hx',
        BASim_owxEmb1_inr])

/-! ### The matching of the outputs of the edge step -/

theorem BASim_IsSplit.toD {P : BAPGraph E} {k : ℕ} {J' : Type} [Fintype J'] [DecidableEq J'] {emb' : (BASimX P) ⊕ (BASimY P) → (BASimX P) ⊕ J'}
    {D : BASimData P k J' emb'} {r : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin k))) × List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin k)))}
    {T' : BAGraph P.E' (P.I' ⊕ Fin k)} (h : BASim_IsSplit D.T r T') : BASimSplit D r T' :=
  ⟨h.hsolid, h.hwaved, h.hdotted, h.hpsi, h.hmdot⟩

/-- the edge step's outputs at `(0, 0)` contain the first term and the derivative terms -/
theorem BASim_edgeOuts_T1 (P : BAPGraph E) (m : ℂ) (p) (x' : BASimY P) (v : (BASimX P) ⊕ (BASimY P)) {R : PGraph (BASimX P)}
    (hR : R ∈ (owxT1 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x').partition m) :
    R ∈ lvl1EdgeOuts0 m P.img.g (BASim_imgP P p) x' v false false := by
  refine (congrArg (fun l => R ∈ l) (BASim_edgeOuts0_ff m P.img.g (BASim_imgP P p) x' v)).mpr ?_
  exact List.mem_append_left _ hR

theorem BASim_edgeOuts_Ds (P : BAPGraph E) (m : ℂ) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (x' : BASimY P) (v : (BASimX P) ⊕ (BASimY P))
    {q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hq : q ∈ lwSplit p.2) {R : PGraph (BASimX P)}
    (hR : ∃ T ∈ oe1xDs m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' v (BASim_imgP P q), R ∈ T.partition m) :
    R ∈ lvl1EdgeOuts0 m P.img.g (BASim_imgP P p) x' v false false := by
  refine (congrArg (fun l => R ∈ l) (BASim_edgeOuts0_ff m P.img.g (BASim_imgP P p) x' v)).mpr ?_
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨BASim_imgP P q, BASim_imgP_mem2 P hq, ?_⟩)
  obtain ⟨T, hT, hRT⟩ := hR
  exact List.mem_flatMap.2 ⟨T, hT, hRT⟩

/-- **`L1`: the matching** (`lanlw`, term 1, with the extra output `M_{αy}` excluded by `tagT1`) -/
theorem BASim_match_L1 (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hσ : p.1.σ = true) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BASim_L1 P.g p).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1EdgeOuts0 m P.img.g (BASim_imgP P p) x' ((promoteC P.g).vmap p.1.dst) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_L1 P hp hσ x' hx').toData hN m) m hT' hne
  exact ⟨R, BASim_pack_mono P.img (L := (owxT1 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x').partition m)
    (fun Q hQ => BASim_edgeOuts_T1 P m p x' _ hQ) hR, hRE⟩

theorem BASim_oe1xDs_D {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I') (x : I')
    (v : E' ⊕ I') (q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (hc1 : ¬ (q.1.σ = false ∧ q.1.src = Sum.inr x))
    (hc2 : ¬ (q.1.σ = true ∧ q.1.dst = Sum.inr x)) : oe1xDs m Γ x v q = [oe1xD m Γ x v q] := by
  simp [oe1xDs, hc1, hc2]

theorem BASim_oe1xDs_red {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I') (x : I')
    (v : E' ⊕ I') (q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (hc1 : q.1.σ = false ∧ q.1.src = Sum.inr x) :
    oe1xDs m Γ x v q = [oe1xP5 m Γ x v q, oe1xP3 m Γ x v q] := by
  simp [oe1xDs, hc1]

theorem BASim_oe1xDs_blue {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I') (x : I')
    (v : E' ⊕ I') (q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (hc1 : ¬ (q.1.σ = false ∧ q.1.src = Sum.inr x))
    (hc2 : q.1.σ = true ∧ q.1.dst = Sum.inr x) : oe1xDs m Γ x v q = [oe1xP6 m Γ x v q, oe1xP4 m Γ x v q] := by
  simp [oe1xDs, hc1, hc2]

/-- **`LD` away from the loops: the matching with `oe1xD`** -/
theorem BASim_match_Dedge (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hc1 : ¬ ((BASim_imgP P q).1.σ = false ∧ (BASim_imgP P q).1.src = Sum.inr x'))
    (hc2 : ¬ ((BASim_imgP P q).1.σ = true ∧ (BASim_imgP P q).1.dst = Sum.inr x'))
    {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BASim_D2 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1EdgeOuts0 m P.img.g (BASim_imgP P p) x' ((promoteC P.g).vmap p.1.dst) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_Dgen P hp hq (Sum.inr x') ((promoteC P.g).vmap p.1.dst) hx'.symm rfl).toData hN m) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (oe1xD m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q)).partition m)
    (fun Q hQ => BASim_edgeOuts_Ds P m p x' _ hq ⟨_, ?_, hQ⟩) hR, hRE⟩
  exact (congrArg (fun l => oe1xD m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q) ∈ l)
    (BASim_oe1xDs_D m _ x' _ _ hc1 hc2)).mpr (List.mem_singleton_self _)

theorem BASim_rest_circ (P : BAPGraph E) (hN : P.g.Normal) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) : ∀ e ∈ q.2, e.circ = true :=
  fun e he => hN.2 e (lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))

/-- **`LD` at a red out-edge of `x`: the matching with `oe1xP5` (loop kept) and `oe1xP3` (loop dropped)** -/
theorem BASim_match_Dred (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hσ : q.1.σ = false) (hqs : (promoteC P.g).vmap q.1.src = Sum.inr x')
    {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BASim_D2 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1EdgeOuts0 m P.img.g (BASim_imgP P p) x' ((promoteC P.g).vmap p.1.dst) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨r, hr, hT'eq⟩ := List.mem_map.1 hT'
  subst hT'eq
  have he1 : (BASim_dE1 q).circ = false := by simp [BASim_dE1, owxDE, hσ, SEdge.map]
  have hSp : BASim_IsSplit (BASim_D2 P.g p q) r
      (BAGraph.mk (LGraph.mk r.1 (BASim_D2 P.g p q).waved (BASim_D2 P.g p q).dotted (BASim_D2 P.g p q).coeff) (BASim_D2 P.g p q).psi
        (r.2 ++ (BASim_D2 P.g p q).mdot)) := ⟨rfl, rfl, rfl, rfl, fun _ => Iff.rfl⟩
  have hc1 : (BASim_imgP P q).1.σ = false ∧ (BASim_imgP P q).1.src = Sum.inr x' := by
    refine ⟨?_, ?_⟩
    · exact hσ
    · exact hqs
  rcases BASim_split_loop P.g q.2 (BASim_rest_circ P hN hp hq) [] (BASim_dE1 q) he1 [BASim_dE2 q, BASim_dE3 p] _ _ hr hSp with
    ⟨r', hr', hS'⟩ | ⟨r', hr', hS'⟩
  · obtain ⟨R, hR, hRE⟩ := BASim_match' ((BASim_B_P5 P hp hq hσ x' hx' hqs).toData hN m) m ⟨r', hr', hS'.toD⟩ hne
    refine ⟨R, BASim_pack_mono P.img (L := (oe1xP5 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q)).partition m)
      (fun Q hQ => BASim_edgeOuts_Ds P m p x' _ hq ⟨_, ?_, hQ⟩) hR, hRE⟩
    exact (congrArg (fun l => oe1xP5 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q) ∈ l)
      (BASim_oe1xDs_red m _ x' _ _ hc1)).mpr (List.mem_cons_self ..)
  · obtain ⟨R, hR, hRE⟩ := BASim_match' ((BASim_B_P3 P hp hq hσ x' hx' hqs).toData hN (m * star m)) m ⟨r', hr', hS'.toD⟩ hne
    refine ⟨R, BASim_pack_mono P.img (L := (oe1xP3 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q)).partition m)
      (fun Q hQ => BASim_edgeOuts_Ds P m p x' _ hq ⟨_, ?_, hQ⟩) hR, hRE⟩
    exact (congrArg (fun l => oe1xP3 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q) ∈ l)
      (BASim_oe1xDs_red m _ x' _ _ hc1)).mpr (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- **`LD` at a blue in-edge of `x`: the matching with `oe1xP6` (loop kept) and `oe1xP4` (loop dropped)** -/
theorem BASim_match_Dblue (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
    (hσ : q.1.σ = true) (hqd : (promoteC P.g).vmap q.1.dst = Sum.inr x')
    (hc1 : ¬ ((BASim_imgP P q).1.σ = false ∧ (BASim_imgP P q).1.src = Sum.inr x'))
    {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BASim_D2 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1EdgeOuts0 m P.img.g (BASim_imgP P p) x' ((promoteC P.g).vmap p.1.dst) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨r, hr, hT'eq⟩ := List.mem_map.1 hT'
  subst hT'eq
  have he2 : (BASim_dE2 q).circ = false := by simp [BASim_dE2, owxDE, hσ, SEdge.map]
  have hSp : BASim_IsSplit (BASim_D2 P.g p q) r
      (BAGraph.mk (LGraph.mk r.1 (BASim_D2 P.g p q).waved (BASim_D2 P.g p q).dotted (BASim_D2 P.g p q).coeff) (BASim_D2 P.g p q).psi
        (r.2 ++ (BASim_D2 P.g p q).mdot)) := ⟨rfl, rfl, rfl, rfl, fun _ => Iff.rfl⟩
  have hc2 : (BASim_imgP P q).1.σ = true ∧ (BASim_imgP P q).1.dst = Sum.inr x' := ⟨hσ, hqd⟩
  rcases BASim_split_loop P.g q.2 (BASim_rest_circ P hN hp hq) [BASim_dE1 q] (BASim_dE2 q) he2 [BASim_dE3 p] _ _ hr hSp with
    ⟨r', hr', hS'⟩ | ⟨r', hr', hS'⟩
  · obtain ⟨R, hR, hRE⟩ := BASim_match' ((BASim_B_P6 P hp hq hσ x' hx' hqd).toData hN m) m ⟨r', hr', hS'.toD⟩ hne
    refine ⟨R, BASim_pack_mono P.img (L := (oe1xP6 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q)).partition m)
      (fun Q hQ => BASim_edgeOuts_Ds P m p x' _ hq ⟨_, ?_, hQ⟩) hR, hRE⟩
    exact (congrArg (fun l => oe1xP6 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q) ∈ l)
      (BASim_oe1xDs_blue m _ x' _ _ hc1 hc2)).mpr (List.mem_cons_self ..)
  · obtain ⟨R, hR, hRE⟩ := BASim_match' ((BASim_B_P4 P hp hq hσ x' hx' hqd).toData hN (m * m)) m ⟨r', hr', hS'.toD⟩ hne
    refine ⟨R, BASim_pack_mono P.img (L := (oe1xP4 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q)).partition m)
      (fun Q hQ => BASim_edgeOuts_Ds P m p x' _ hq ⟨_, ?_, hQ⟩) hR, hRE⟩
    exact (congrArg (fun l => oe1xP4 m (lwSymmUncirc P.img.g (BASim_imgP P p)) x' ((promoteC P.g).vmap p.1.dst) (BASim_imgP P q) ∈ l)
      (BASim_oe1xDs_blue m _ x' _ _ hc1 hc2)).mpr (List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem BASim_tagT1_band {E' I : Type} [Fintype E'] [DecidableEq E'] [Fintype I] [DecidableEq I] (Γ : BAGraph E' I)
    (T' : BAGraph E' (I ⊕ Fin 2)) (h : Γ.tagT1 T' = BAShape.band) : Γ.extraB (owxEmb 2) T' = false := by
  by_contra hc
  have hc' : Γ.extraB (owxEmb 2) T' = true := by simpa using hc
  simp [BAGraph.tagT1, hc'] at h

/-- **The edge step (`lanlw`): the band-tagged outputs are matched** with the outputs of the edge step at the image -/
theorem BASim_matchLT_edge (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true) (x : P.I') (hx : p.1.src = Sum.inr x)
    (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) (hv : P.g.sameAtom p.1.src p.1.dst = false)
    (hint : P.g.intAtom (Sum.inr x) = true)
    (hbad : P.g.atEdges (Sum.inr x) ≠ [] ∧ ((P.g.atEdges (Sum.inr x)).length ≠ 2 ∨ P.g.atCharge (Sum.inr x) ≠ 0)) (Q : BAPGraph E)
    (hQ : (BAShape.band, Q) ∈ P.outsT P.g.tagT1 [BAGraph.lanlwT1 P.g p] ++ P.outsT (P.g.tagStd 2) ((lwSplit p.2).map (BAGraph.lanlwD P.g p))) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img := by
  obtain ⟨x', hxv, hstep⟩ := BASim_locStep_edge P m hp h x hx hwf hv hint hbad
  have hx' : (promoteC P.g).vmap p.1.src = Sum.inr x' := by rw [hx]; exact hxv
  refine ⟨_, hstep, ?_⟩
  rcases List.mem_append.1 hQ with hQ | hQ
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT _ _ _ _ _ hQ
    have hne := BASim_tagT1_band _ _ htag
    rw [List.mem_singleton] at hT
    subst hT
    exact BASim_match_L1 P hN m hp h.1 x' hx' hT' hne
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT _ _ _ _ _ hQ
    have hne := BASim_tagStd_band _ _ _ htag
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT
    rw [BASim_lanlwD_eq] at hT'
    by_cases hc1 : (BASim_imgP P q).1.σ = false ∧ (BASim_imgP P q).1.src = Sum.inr x'
    · exact BASim_match_Dred P hN m hp hq x' hx' hc1.1 hc1.2 hT' hne
    · by_cases hc2 : (BASim_imgP P q).1.σ = true ∧ (BASim_imgP P q).1.dst = Sum.inr x'
      · exact BASim_match_Dblue P hN m hp hq x' hx' hc2.1 hc2.2 hc1 hT' hne
      · exact BASim_match_Dedge P hN m hp hq x' hx' hc1 hc2 hT' hne

end Edge

/-! ## The step at a pair of edges at an internal vertex (`BAFrameStepT.gg`) -/

section GG
variable {E : Type}

/-- the anchor table of the terms with two anchored new vertices (`GGGamma`, first sums): `u = bpv 0 ↦ a`, `β = bpv 1 ↦ b` -/
def BASim_anch20 {α : Type} (a b : α) : Fin 2 → Option α := fun j => if j = 0 then some a else some b
theorem BASim_anch20_zero {α : Type} (a b : α) : BASim_anch20 a b 0 = some a := by simp [BASim_anch20]
theorem BASim_anch20_one {α : Type} (a b : α) : BASim_anch20 a b 1 = some b := by simp [BASim_anch20]

abbrev BASim_phi20 (P : BAPGraph E) (x' : BASimY P) (a b : P.E' ⊕ P.I') : P.E' ⊕ (P.I' ⊕ Fin 2) → (BASimX P) ⊕ (BASimY P) :=
  BASim_phi P id (BASim_anch20 a b) (fun _ => x')

/-- **The specification of a term with two anchored new vertices** (`u ↦ ā`, `β ↦ b̄`; the band term has no new vertex, `emb' = id`) -/
def BASim_mk20 (P : BAPGraph E) (x' : BASimY P) (a b : P.E' ⊕ P.I') (rest : List (SEdge (P.E' ⊕ P.I')))
    (s : List (SEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) (w : List (WEdge (P.E' ⊕ (P.I' ⊕ Fin 2)))) (md : List (BAMEdge (P.E' ⊕ (P.I' ⊕ Fin 2))))
    (restH : List (SEdge ((BASimX P) ⊕ (BASimY P)))) (sH : List (SEdge ((BASimX P) ⊕ (BASimY P)))) (wH : List (WEdge ((BASimX P) ⊕ (BASimY P))))
    (hd X : List (SEdge ((BASimX P) ⊕ (BASimY P))))
    (hrest : ∀ e ∈ rest, e ∈ P.g.solid) (hrestH : restH.Perm (hd ++ rest.map (BAScost_imgE P.g)))
    (hma : bpM (owxEmb 2 a) (bpv 0) ∈ md ∨ bpM (bpv 0) (owxEmb 2 a) ∈ md) (hmb : bpM (bpv 1) (owxEmb 2 b) ∈ md ∨ bpM (owxEmb 2 b) (bpv 1) ∈ md)
    (hmd : ∀ m' ∈ md, BASim_phi20 P x' a b m'.x = BASim_phi20 P x' a b m'.y ∨ ∃ h ∈ X,
      (h.src = BASim_phi20 P x' a b m'.x ∧ h.dst = BASim_phi20 P x' a b m'.y) ∨ (h.src = BASim_phi20 P x' a b m'.y ∧ h.dst = BASim_phi20 P x' a b m'.x))
    (hX0 : ∀ h ∈ X, h.circ = false)
    (hX1 : ∀ h ∈ X, ∃ u v, BASim_phi20 P x' a b u = h.src ∧ BASim_phi20 P x' a b v = h.dst ∧
      (BAGraph.ext 2 P.g rest s w md).sameAtom u v = true)
    (hs : (hd.map (SEdge.map id) ++ sH).Perm (s.map (BASim_phiE (BASim_phi20 P x' a b)) ++ X))
    (hw : List.Forall₂ (fun h w => WEdge.sameRev h (WEdge.map (BASim_phi20 P x' a b) w)) wH w) :
    BASimExt P 2 (BASimY P) id where
  hemb := fun y => rfl
  hinj := Function.injective_id
  anchor := BASim_anch20 a b
  fresh := fun _ => x'
  rest := rest
  s := s
  w := w
  md := md
  restH := restH
  sH := sH
  wH := wH
  hd := hd
  ex := []
  X := X
  hrest := hrest
  hrestH := by simpa using hrestH
  hfresh := fun j hj => by
    fin_cases j
    · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, BASim_anch20_zero] at hj; cases hj
    · rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, BASim_anch20_one] at hj; cases hj
  hsurj := fun z hz => by
    exfalso
    obtain ⟨v, hv⟩ := BAAtomic_vmap_surjective (promoteC P.g) (Sum.inr z)
    exact hz v hv
  hanch := fun j a' ha => by
    fin_cases j
    · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, BASim_anch20_zero] at ha
      cases ha
      rcases hma with h | h
      · exact BASim_sameAtom_symm ((BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext_md P.g rest _ _ _ _ h))
      · exact (BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext_md P.g rest _ _ _ _ h)
    · rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, BASim_anch20_one] at ha
      cases ha
      rcases hmb with h | h
      · exact (BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext_md P.g rest _ _ _ _ h)
      · exact BASim_sameAtom_symm ((BASim_sameAtom_iff _ _ _).2 (BAScost_atomSetoid_ext_md P.g rest _ _ _ _ h))
  hfr := fun j j' hj _ _ => by
    fin_cases j
    · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, BASim_anch20_zero] at hj; cases hj
    · rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, BASim_anch20_one] at hj; cases hj
  hmd := hmd
  hX0 := hX0
  hX1 := hX1
  hs := by simpa using hs
  hw := hw

theorem BASim_lwSplit_swap {κ : Type*} (l : List κ) : ∀ p ∈ lwSplit l, ∀ q ∈ lwSplit p.2,
    ∃ p' ∈ lwSplit l, ∃ q' ∈ lwSplit p'.2, p'.1 = q.1 ∧ q'.1 = p.1 ∧ q'.2 = q.2 := by
  induction l with
  | nil => intro p hp; simp [lwSplit] at hp
  | cons a l ih =>
    intro p hp q hq
    simp only [lwSplit, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨p0, hp0, rfl⟩
    · refine ⟨(q.1, a :: q.2), ?_, (a, q.2), ?_, rfl, rfl, rfl⟩
      · simp only [lwSplit, List.mem_cons, List.mem_map]
        exact Or.inr ⟨q, hq, rfl⟩
      · simp [lwSplit]
    · simp only [lwSplit, List.mem_cons, List.mem_map] at hq
      rcases hq with rfl | ⟨q0, hq0, rfl⟩
      · refine ⟨(a, l), by simp [lwSplit], p0, hp0, rfl, rfl, rfl⟩
      · obtain ⟨p', hp', q', hq', h1, h2, h3⟩ := ih p0 hp0 q0 hq0
        refine ⟨(p'.1, a :: p'.2), ?_, (q'.1, a :: q'.2), ?_, h1, h2, by simp [h3]⟩
        · simp only [lwSplit, List.mem_cons, List.mem_map]
          exact Or.inr ⟨p', hp', rfl⟩
        · simp only [lwSplit, List.mem_cons, List.mem_map]
          exact Or.inr ⟨q', hq', rfl⟩

theorem BASim_img_deg (P : BAPGraph E) (v : P.E' ⊕ P.I') :
    (promoteC P.g).merge.lvl1DegAt ((promoteC P.g).vmap v) = (P.g.atEdges v).length := by
  unfold LGraph.lvl1DegAt
  rw [BAAtomic_solidAt, List.length_map]

theorem BASim_img_charge (P : BAPGraph E) (v : P.E' ⊕ P.I') :
    (promoteC P.g).merge.lvl1ChargeAt ((promoteC P.g).vmap v) = P.g.atCharge v := BAAtomic_charge P.g v

theorem BASim_img_wf (P : BAPGraph E) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) :
    ∀ e ∈ P.img.g.solid, e.src ≠ e.dst := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 (show e ∈ P.g.solid.map (BAScost_imgE P.g) by rw [← BAScost_img_solid]; exact he)
  intro hc
  have := (BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _).1 hc
  rw [hwf e0 he0] at this
  exact Bool.noConfusion this

/-- the image of the neighbour condition: every internal vertex of the image has degree `0`, or `2` and charge `0` -/
theorem BASim_img_nb (P : BAPGraph E)
    (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
      ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0)) :
    ∀ i : BASimY P, (promoteC P.g).merge.lvl1DegAt (Sum.inr i) = 0 ∨
      ((promoteC P.g).merge.lvl1DegAt (Sum.inr i) = 2 ∧ (promoteC P.g).merge.lvl1ChargeAt (Sum.inr i) = 0) := by
  intro i
  obtain ⟨b, hb⟩ := BAAtomic_exists_inr_vmap P.g i
  have hint : P.g.intAtom (Sum.inr b) = true := by
    rw [← BAAtomic_promoteC_vmap_isRight, hb]; rfl
  rw [← hb, BASim_img_deg, BASim_img_charge]
  exact hnb b hint

/-- the image of an internal vertex with an internal atom is an internal vertex -/
theorem BASim_exists_inr (P : BAPGraph E) (x : P.I') (hint : P.g.intAtom (Sum.inr x) = true) :
    ∃ x' : BASimY P, (promoteC P.g).vmap (Sum.inr x) = Sum.inr x' := by
  have hR := (BAAtomic_promoteC_vmap_isRight P.g (Sum.inr x)).2 hint
  rcases hvm : (promoteC P.g).vmap (Sum.inr x) with a | x'
  · rw [hvm] at hR; exact absurd hR (by simp)
  · exact ⟨x', rfl⟩

/-- **The band step at the image of a pair** (`LocStep.gg` at `(0, 0)`, and at `(0, 1)` with the two edges exchanged): the ends `a`, `a'` of the pair at the internal atom
have one image, an internal vertex `x'`, and the ends `y`, `y'` of the pair have other images -/
theorem BASim_locStep_gg (P : BAPGraph E) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ q.1.σ = true) (a a' : P.I')
    (hx : p.1.src = Sum.inr a ∧ q.1.dst = Sum.inr a') (hsame : P.g.sameAtom (Sum.inr a) (Sum.inr a') = true)
    (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
    (hint : P.g.intAtom (Sum.inr a) = true)
    (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
      ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0)) :
    ∃ x' : BASimY P, (promoteC P.g).vmap p.1.src = Sum.inr x' ∧ (promoteC P.g).vmap q.1.dst = Sum.inr x' ∧
      (promoteC P.g).vmap p.1.dst ≠ Sum.inr x' ∧ (promoteC P.g).vmap q.1.src ≠ Sum.inr x' ∧
      LocStep m P.img (lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst)
        ((promoteC P.g).vmap q.1.src) false false)) ∧
      ∃ p' ∈ lwSplit P.g.solid, ∃ q' ∈ lwSplit p'.2, p'.1 = q.1 ∧ q'.1 = p.1 ∧ q'.2 = q.2 ∧
        LocStep m P.img (lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p') (BASim_imgP P q') x' ((promoteC P.g).vmap q.1.src)
          ((promoteC P.g).vmap p.1.dst) false true)) := by
  obtain ⟨x', hx'⟩ := BASim_exists_inr P a hint
  have hpe : p.1 ∈ P.g.solid := lvl1_mem_split_fst _ p hp
  have hqe : q.1 ∈ P.g.solid := lvl1_mem_split _ p hp q.1 (lvl1_mem_split_fst _ q hq)
  have hxa : (promoteC P.g).vmap p.1.src = Sum.inr x' := by rw [hx.1]; exact hx'
  have hxq : (promoteC P.g).vmap q.1.dst = Sum.inr x' := by
    rw [hx.2, ← ((BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _).2 hsame)]; exact hx'
  have hy : (promoteC P.g).vmap p.1.dst ≠ Sum.inr x' := by
    intro hc
    have := (BAAtomic_promoteC_vmap_eq_sameAtom P.g p.1.src p.1.dst).1 (hxa.trans hc.symm)
    rw [hwf p.1 hpe] at this
    exact Bool.noConfusion this
  have hy' : (promoteC P.g).vmap q.1.src ≠ Sum.inr x' := by
    intro hc
    have := (BAAtomic_promoteC_vmap_eq_sameAtom P.g q.1.src q.1.dst).1 (hc.trans hxq.symm)
    rw [hwf q.1 hqe] at this
    exact Bool.noConfusion this
  have hwf' := BASim_img_wf P hwf
  have hnb' := BASim_img_nb P hnb
  refine ⟨x', hxa, hxq, hy, hy', ?_, ?_⟩
  · refine LocStep.gg P.img (BASim_imgP P p) (BASim_imgP P q) (BASim_imgP_mem P hp) (BASim_imgP_mem2 P hq) x' _ _ hy false false ?_ ?_ hwf' hnb'
    · show BAScost_imgE P.g p.1 = ⟨true, (BAScost_imgE P.g p.1).circ, Sum.inr x', (promoteC P.g).vmap p.1.dst⟩
      simp only [BAScost_imgE, h.1, hxa]
    · show BAScost_imgE P.g q.1 = ⟨true, (BAScost_imgE P.g q.1).circ, (promoteC P.g).vmap q.1.src, Sum.inr x'⟩
      simp only [BAScost_imgE, h.2, hxq]
  · obtain ⟨p', hp', q', hq', h1, h2, h3⟩ := BASim_lwSplit_swap _ p hp q hq
    refine ⟨p', hp', q', hq', h1, h2, h3, ?_⟩
    refine LocStep.gg P.img (BASim_imgP P p') (BASim_imgP P q') (BASim_imgP_mem P hp') (BASim_imgP_mem2 P hq') x' _ _ hy' false true ?_ ?_ hwf' hnb'
    · show lwSymmTwistS false true (BAScost_imgE P.g p'.1) = ⟨true, (BAScost_imgE P.g p'.1).circ, Sum.inr x', (promoteC P.g).vmap q.1.src⟩
      simp only [lwSymmTwistS, h1, BAScost_imgE, h.2, hxq, SEdge.transpose]
      rfl
    · show lwSymmTwistS false true (BAScost_imgE P.g q'.1) = ⟨true, (BAScost_imgE P.g q'.1).circ, (promoteC P.g).vmap p.1.dst, Sum.inr x'⟩
      simp only [lwSymmTwistS, h2, BAScost_imgE, h.1, hxa, SEdge.transpose]
      rfl

theorem BASim_twistS_ff {V : Type} (e : SEdge V) : lwSymmTwistS false false e = e := rfl

theorem BASim_frame2Q_ff {E' I' : Type} (q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) :
    lwSymmFrame2Q false false q = ({ q.1 with circ := false }, q.2) := by
  have h : lwSymmTwistS false false = (id : SEdge (E' ⊕ I') → SEdge (E' ⊕ I')) := funext fun e => rfl
  simp [lwSymmFrame2Q, h]

/-- the form `R2` at the selector `(0, 0)` -/
theorem BASim_R2_ff {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
    (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (y y' : E' ⊕ I') :
    lwSymmOe2xR2 false false m Γ p q x y y' =
      ({ Γ with solid := q.2 } : LGraph E' I').owxExt id (m ^ 3) [⟨true, false, y', y⟩] [⟨true, true, Sum.inr x, y⟩] := by
  unfold lwSymmOe2xR2
  rw [BASim_frame2Q_ff]
  rfl


theorem BASim_R2_ft {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
    (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (y y' : E' ⊕ I') :
    lwSymmOe2xR2 false true m Γ p q x y y' =
      ({ Γ with solid := q.2 } : LGraph E' I').owxExt id (m ^ 3) [⟨true, false, y, y'⟩] [⟨true, true, y, Sum.inr x⟩] := by
  have hS : SEdge.map (id : E' ⊕ I' → E' ⊕ I') = id := funext fun e => rfl
  have hW : WEdge.map (id : E' ⊕ I' → E' ⊕ I') = id := funext fun e => rfl
  unfold lwSymmOe2xR2 oe2xR2 lwSymmFrame2 lwSymmUncirc2 lwSymmFrame2Q
  simp only [lwSymmTwistG, lwSymmTwistS, Bool.cond_true, Bool.cond_false, LGraph.transpose, LGraph.owxExt, hS, hW, List.map_id,
    List.map_map, List.map_append, List.map_cons, List.map_nil, Function.comp_def, id_eq, lwSymm_sedge_tr_tr, lwSymm_wedge_tr_tr, List.map_id']
  rfl


/-- `h'` is `h`, or the circled version of an uncircled loop `h` -/
def BASim_loopRel {V : Type*} (h' h : SEdge V) : Prop :=
  h' = h ∨ (h.src = h.dst ∧ h.circ = false ∧ h' = { h with circ := true })

theorem BASim_loopRel_ends {V : Type*} {h' h : SEdge V} (r : BASim_loopRel h' h) : h'.src = h.src ∧ h'.dst = h.dst := by
  rcases r with rfl | ⟨_, _, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem BASim_loopRel_map {V W : Type*} (f : V → W) {h' h : SEdge V} (r : BASim_loopRel h' h) :
    BASim_loopRel (SEdge.map f h') (SEdge.map f h) := by
  rcases r with rfl | ⟨h1, h2, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by simp [SEdge.map, h1], h2, rfl⟩

theorem BASim_splitLoops_mono {V : Type*} [DecidableEq V] (m : ℂ) {s' s : List (SEdge V)} (hs : List.Forall₂ BASim_loopRel s' s) :
    ∀ r ∈ lwSplitLoops m s', r ∈ lwSplitLoops m s := by
  induction hs with
  | nil => exact fun r hr => hr
  | @cons h' h s' s hrel hs ih =>
    intro r hr
    simp only [lwSplitLoops, List.mem_flatMap] at hr ⊢
    obtain ⟨r0, hr0, hr⟩ := hr
    refine ⟨r0, ih r0 hr0, ?_⟩
    rcases hrel with rfl | ⟨h1, h2, rfl⟩
    · exact hr
    · simp only [h1, h2, and_self, ite_true, ite_false, Bool.true_eq_false, and_false, List.mem_cons, List.mem_nil_iff, or_false] at hr ⊢
      exact Or.inl hr

theorem BASim_forall₂_filter_map {V : Type*} {s' s : List (SEdge V)} (hs : List.Forall₂ BASim_loopRel s' s) (p : V → V → Bool) {β : Type*}
    (f : V → V → β) :
    (s'.filter fun e => p e.src e.dst).map (fun e => f e.src e.dst) = (s.filter fun e => p e.src e.dst).map (fun e => f e.src e.dst) := by
  induction hs with
  | nil => rfl
  | @cons h' h s' s hrel hs ih =>
    obtain ⟨e1, e2⟩ := BASim_loopRel_ends hrel
    simp only [List.filter_cons, e1, e2]
    split_ifs
    · simp [ih, e1, e2]
    · exact ih

theorem BASim_loopRel_mem {V : Type*} {s' s : List (SEdge V)} (hs : List.Forall₂ BASim_loopRel s' s) :
    (∀ e ∈ s', ∃ e0 ∈ s, BASim_loopRel e e0) ∧ (∀ e0 ∈ s, ∃ e ∈ s', BASim_loopRel e e0) := by
  induction hs with
  | nil => simp
  | @cons h' h s' s hr hs ih =>
    refine ⟨fun e he => ?_, fun e0 he0 => ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨e0, h0, h⟩ := ih.1 e he
        exact ⟨e0, List.mem_cons_of_mem _ h0, h⟩
    · rcases List.mem_cons.1 he0 with rfl | he0
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨e, h0, h⟩ := ih.2 e0 he0
        exact ⟨e, List.mem_cons_of_mem _ h0, h⟩


section PartFix
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem BASim_sbetween_iff (H : LGraph X Y) (s' : List (SEdge (X ⊕ Y))) (hs : List.Forall₂ BASim_loopRel s' H.solid) (u v : X ⊕ Y) :
    ({ H with solid := s' } : LGraph X Y).SBetween u v ↔ H.SBetween u v := by
  unfold LGraph.SBetween
  show (∃ e ∈ s', _) ↔ (∃ e ∈ H.solid, _)
  constructor
  · rintro ⟨e, he, hne, hu⟩
    obtain ⟨e0, he0, hr⟩ := (BASim_loopRel_mem hs).1 e he
    obtain ⟨h1, h2⟩ := BASim_loopRel_ends hr
    exact ⟨e0, he0, by rw [← h1, ← h2]; exact hne, by rw [← h1, ← h2]; exact hu⟩
  · rintro ⟨e0, he0, hne, hu⟩
    obtain ⟨e, he, hr⟩ := (BASim_loopRel_mem hs).2 e0 he0
    obtain ⟨h1, h2⟩ := BASim_loopRel_ends hr
    exact ⟨e, he, by rw [h1, h2]; exact hne, by rw [h1, h2]; exact hu⟩

theorem BASim_mergeSplit_fix (m : ℂ) (Δ : LGraph X Y) (s' : List (SEdge (X ⊕ Y))) (hs : List.Forall₂ BASim_loopRel s' Δ.solid) :
    ({ Δ with solid := s' } : LGraph X Y).mergeSplitP m ⊆ Δ.mergeSplitP m := by
  intro P hP
  unfold LGraph.mergeSplitP at hP ⊢
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hP
  refine List.mem_map.2 ⟨g, ?_, rfl⟩
  unfold LGraph.splitWeights at hg ⊢
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
  refine List.mem_map.2 ⟨r, ?_, rfl⟩
  refine BASim_splitLoops_mono m ?_ r hr
  show List.Forall₂ BASim_loopRel (s'.map (SEdge.map Δ.vmap)) (Δ.solid.map (SEdge.map Δ.vmap))
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hs.imp fun a b r => BASim_loopRel_map _ r

theorem BASim_partition_fix (m : ℂ) (H : LGraph X Y) (s' : List (SEdge (X ⊕ Y))) (hs : List.Forall₂ BASim_loopRel s' H.solid) :
    ({ H with solid := s' } : LGraph X Y).partition m ⊆ H.partition m := by
  classical
  set Γ' : LGraph X Y := { H with solid := s' } with hΓ'
  have hA : Γ'.aPairs = H.aPairs := by
    unfold LGraph.aPairs
    congr 1
    exact BASim_forall₂_filter_map hs (fun u v => decide (u ≠ v ∧ ¬ H.XBetween u v)) (fun u v => (u, v))
  have hI : ∀ e : DEdge (X ⊕ Y), Γ'.isB e = H.isB e := fun e => by
    unfold LGraph.isB
    exact decide_eq_decide.2 (and_congr Iff.rfl (not_congr (BASim_sbetween_iff H s' hs _ _)))
  have hB : Γ'.bEdges = H.bEdges := by
    unfold LGraph.bEdges
    exact List.filter_congr fun e _ => hI e
  have hdb : Γ'.dotBase = H.dotBase := by
    unfold LGraph.dotBase
    exact List.filter_congr fun e _ => by rw [hI e]
  have hdc : Γ'.dotChoices = H.dotChoices := by
    unfold LGraph.dotChoices LGraph.dotAtoms
    rw [hA, hB]
  intro P hP
  unfold LGraph.partition at hP ⊢
  obtain ⟨Δ', hΔ', hP⟩ := List.mem_flatMap.1 hP
  unfold LGraph.partitionTerms at hΔ'
  obtain ⟨hΔ'm, hcons⟩ := List.mem_filter.1 hΔ'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hΔ'm
  have hc' : c ∈ H.dotChoices := by rw [← hdc]; exact hc
  have hΔeq : Γ'.withDots c = ({ H.withDots c with solid := s' } : LGraph X Y) := by
    unfold LGraph.withDots
    rw [hdb]
  refine List.mem_flatMap.2 ⟨H.withDots c, ?_, ?_⟩
  · unfold LGraph.partitionTerms
    refine List.mem_filter.2 ⟨List.mem_map.2 ⟨c, hc', rfl⟩, ?_⟩
    rw [hΔeq] at hcons
    exact hcons
  · rw [hΔeq] at hP
    exact BASim_mergeSplit_fix m (H.withDots c) s' hs hP

end PartFix

end GG

section GG2
variable {E : Type}

theorem BASim_loopRel_fix {V : Type*} [DecidableEq V] (e : SEdge V) : BASim_loopRel (BASim_fix e) e := by
  by_cases h : e.src = e.dst ∧ e.circ = false
  · exact Or.inr ⟨h.1, h.2, by simp [BASim_fix, h]⟩
  · exact Or.inl (by simp [BASim_fix, h])

/-- the band term with the loops of the new solid edges circled is in the partition of the band term (the weight split) -/
theorem BASim_partition_owxExt_fix {X Y X' Y' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y']
    (m c : ℂ) (Γ : LGraph X Y) (emb : X ⊕ Y → X' ⊕ Y') (s : List (SEdge (X' ⊕ Y'))) (w : List (WEdge (X' ⊕ Y'))) :
    (Γ.owxExt emb c (s.map BASim_fix) w).partition m ⊆ (Γ.owxExt emb c s w).partition m := by
  refine BASim_partition_fix m (Γ.owxExt emb c s w) (Γ.owxExt emb c (s.map BASim_fix) w).solid ?_
  show List.Forall₂ _ (Γ.solid.map (SEdge.map emb) ++ s.map BASim_fix) (Γ.solid.map (SEdge.map emb) ++ s)
  refine List.rel_append (List.forall₂_same.2 fun e _ => (Or.inl rfl : BASim_loopRel e e)) ?_
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.2 fun e _ => BASim_loopRel_fix e

theorem BASim_phi20_emb (P : BAPGraph E) (x' : BASimY P) (a b v : P.E' ⊕ P.I') :
    BASim_phi20 P x' a b (owxEmb 2 v) = (promoteC P.g).vmap v := BASim_phi_emb P id _ _ v
theorem BASim_phi20_u (P : BAPGraph E) (x' : BASimY P) (a b : P.E' ⊕ P.I') :
    BASim_phi20 P x' a b (bpv 0) = (promoteC P.g).vmap a := BASim_phi_some _ _ _ _ 0 a (BASim_anch20_zero a b)
theorem BASim_phi20_b (P : BAPGraph E) (x' : BASimY P) (a b : P.E' ⊕ P.I') :
    BASim_phi20 P x' a b (bpv 1) = (promoteC P.g).vmap b := BASim_phi_some _ _ _ _ 1 b (BASim_anch20_one a b)


/-- **`A3`** (`S⁺_{uβ}`, `M_{βy}`, `Ǧ_{y'β}`: `u ↦ x̄`, `β ↦ ȳ`) at the band's `R2` (nat) -/
def BASim_B_A3 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') : BASimExt P 2 (BASimY P) id :=
  BASim_mk20 P x' p.1.src p.1.dst q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst)]
    (q.2.map (BAScost_imgE P.g)) ([⟨true, false, (promoteC P.g).vmap q.1.src, (promoteC P.g).vmap p.1.dst⟩].map BASim_fix)
    [⟨true, true, Sum.inr x', (promoteC P.g).vmap p.1.dst⟩] [] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    (by simp)
    (Or.inl (by simp)) (Or.inl (by simp))
    (fun m' hm' => by
      left
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl <;> simp [bpM, BASim_phi20_emb, BASim_phi20_u, BASim_phi20_b])
    (by simp) (by simp)
    (by
      by_cases h : (promoteC P.g).vmap q.1.src = (promoteC P.g).vmap p.1.dst
      · simp [BASim_fix, BASim_phiE, bpS, BASim_phi20_emb, BASim_phi20_b, h]
      · simp [BASim_fix, BASim_phiE, bpS, BASim_phi20_emb, BASim_phi20_b, h])
    (List.Forall₂.cons (Or.inl (by simp [WEdge.map, bpW, BASim_phi20_u, BASim_phi20_b, hx'])) List.Forall₂.nil)


/-- **`A2`** (`S⁺_{uβ}`, `Ǧ_{βy}`, `M_{y'β}`: `u ↦ x̄`, `β ↦ ȳ'`) at the band's `R2` at the selector `(0, 1)` -/
def BASim_B_A2 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') : BASimExt P 2 (BASimY P) id :=
  BASim_mk20 P x' p.1.src q.1.src q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (owxEmb 2 q.1.src) (bpv 1)]
    (q.2.map (BAScost_imgE P.g)) ([⟨true, false, (promoteC P.g).vmap q.1.src, (promoteC P.g).vmap p.1.dst⟩].map BASim_fix)
    [⟨true, true, (promoteC P.g).vmap q.1.src, Sum.inr x'⟩] [] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    (by simp)
    (Or.inl (by simp)) (Or.inr (by simp))
    (fun m' hm' => by
      left
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl <;> simp [bpM, BASim_phi20_emb, BASim_phi20_u, BASim_phi20_b])
    (by simp) (by simp)
    (by
      by_cases h : (promoteC P.g).vmap q.1.src = (promoteC P.g).vmap p.1.dst
      · simp [BASim_fix, BASim_phiE, bpS, BASim_phi20_emb, BASim_phi20_b, h]
      · simp [BASim_fix, BASim_phiE, bpS, BASim_phi20_emb, BASim_phi20_b, h])
    (List.Forall₂.cons (Or.inr (by simp [WEdge.map, WEdge.transpose, bpW, BASim_phi20_u, BASim_phi20_b, hx'])) List.Forall₂.nil)

/-- **`A1`** (`S⁺_{uβ}`, `M_{βy}`, `M_{y'β}`: `u ↦ x̄`, `β ↦ ȳ`; the band's edge `G_{ȳ'ȳ}` has no edge of the term: it is a phantom) at the band's `R2` (nat) -/
def BASim_B_A1 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') : BASimExt P 2 (BASimY P) id :=
  BASim_mk20 P x' p.1.src p.1.dst q.2 [] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]
    (q.2.map (BAScost_imgE P.g)) [⟨true, false, (promoteC P.g).vmap q.1.src, (promoteC P.g).vmap p.1.dst⟩]
    [⟨true, true, Sum.inr x', (promoteC P.g).vmap p.1.dst⟩] [] [⟨true, false, (promoteC P.g).vmap q.1.src, (promoteC P.g).vmap p.1.dst⟩]
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    (by simp)
    (Or.inl (by simp)) (Or.inl (by simp))
    (fun m' hm' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl | rfl
      · left; simp [bpM, BASim_phi20_emb, BASim_phi20_u, BASim_phi20_b]
      · left; simp [bpM, BASim_phi20_emb, BASim_phi20_u, BASim_phi20_b]
      · left; simp [bpM, BASim_phi20_emb, BASim_phi20_u, BASim_phi20_b]
      · right
        exact ⟨_, List.mem_cons_self, Or.inl ⟨by simp [bpM, BASim_phi20_emb], by simp [bpM, BASim_phi20_b]⟩⟩)
    (by simp)
    (fun h hh => by
      rw [List.mem_singleton] at hh
      subst hh
      refine ⟨owxEmb 2 q.1.src, owxEmb 2 p.1.dst, by simp [BASim_phi20_emb], by simp [BASim_phi20_emb], ?_⟩
      have h1 := (BASim_sameAtom_iff (BAGraph.ext 2 P.g q.2 [] [bpW true (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]) _ _).2
        (BAScost_atomSetoid_ext_md P.g q.2 _ _ _ (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp))
      have h2 := (BASim_sameAtom_iff (BAGraph.ext 2 P.g q.2 [] [bpW true (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]) _ _).2
        (BAScost_atomSetoid_ext_md P.g q.2 _ _ _ (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp))
      exact BASim_sameAtom_trans h1 h2)
    (by simp)
    (List.Forall₂.cons (Or.inl (by simp [WEdge.map, bpW, BASim_phi20_u, BASim_phi20_b, hx'])) List.Forall₂.nil)


/-! ### The outputs of the pair step: membership of the partition of each form -/

section Mem
variable {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
  (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (y y' : E' ⊕ I') (c t : Bool)

theorem BASim_ggOuts_R2 : (lwSymmOe2xR2 c t m Γ p q x y y').partition m ⊆ lvl1GGOuts0 m Γ p q x y y' c t := fun Q hQ => by
  unfold lvl1GGOuts0; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hQ)))))
theorem BASim_ggOuts_R3 : (lwSymmOe2xR3 c t m Γ p q x).partition m ⊆ lvl1GGOuts0 m Γ p q x y y' c t := fun Q hQ => by
  unfold lvl1GGOuts0; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hQ)))))
theorem BASim_ggOuts_R4 : (lwSymmOe2xR4 c t m Γ p q x y y').partition m ⊆ lvl1GGOuts0 m Γ p q x y y' c t := fun Q hQ => by
  unfold lvl1GGOuts0; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hQ))))
theorem BASim_ggOuts_R5 : (lwSymmOe2xR5 c t m Γ p q x y y').partition m ⊆ lvl1GGOuts0 m Γ p q x y y' c t := fun Q hQ => by
  unfold lvl1GGOuts0; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hQ)))
theorem BASim_ggOuts_R6 : (lwSymmOe2xR6 c t m Γ p q x y y').partition m ⊆ lvl1GGOuts0 m Γ p q x y y' c t := fun Q hQ => by
  unfold lvl1GGOuts0; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hQ))
theorem BASim_ggOuts_R7 {q' : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))} (hq' : q' ∈ lwSplit q.2) :
    (lwSymmOe2xR7 c t m Γ p q x y y' q').partition m ⊆ lvl1GGOuts0 m Γ p q x y y' c t := fun Q hQ => by
  unfold lvl1GGOuts0; simp only [List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inr ⟨q', hq', hQ⟩)
theorem BASim_ggOuts_R8 {q' : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))} (hq' : q' ∈ lwSplit q.2) :
    (lwSymmOe2xR8 c t m Γ p q x y y' q').partition m ⊆ lvl1GGOuts0 m Γ p q x y y' c t := fun Q hQ => by
  unfold lvl1GGOuts0; simp only [List.mem_append, List.mem_flatMap]; exact Or.inr ⟨q', hq', hQ⟩

end Mem

section MatchR2
variable (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
  (hq : q ∈ lwSplit p.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
include hN hp hq hx'

/-- **`A3` ↔ `R2`** at the selector `(0, 0)` -/
theorem BASim_match_A3 {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BAGGOp_A3 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_A3 P hp hq x' hx').toData hN (m ^ 3)) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR2 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _).partition m)
    (BASim_ggOuts_R2 _ _ _ _ _ _ _ _ _) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R2_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src))).mpr
    (BASim_pack_mono P.img (BASim_partition_owxExt_fix m (m ^ 3) _ id _ _) hR)

/-- **`A1` ↔ `R2`** at the selector `(0, 0)` (the `=`-dotted branch of `{ȳ', ȳ}`, with the loop dropped) -/
theorem BASim_match_A1 {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BAGGOp_A1 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_A1 P hp hq x' hx').toData hN (m ^ 3)) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR2 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _).partition m)
    (BASim_ggOuts_R2 _ _ _ _ _ _ _ _ _) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R2_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src))).mpr hR

/-- **`A2` ↔ `R2`** at the selector `(0, 1)` (the pair exchanged: `p' = (q.1, ·)`, `q' = (p.1, q.2)`) -/
theorem BASim_match_A2 {p' q' : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (h3 : q'.2 = q.2) {T' : BAGraph P.E' (P.I' ⊕ Fin 2)}
    (hT' : T' ∈ (BAGGOp_A2 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p') (BASim_imgP P q') x' ((promoteC P.g).vmap q.1.src) ((promoteC P.g).vmap p.1.dst) false true),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨q'1, q'2⟩ := q'
  dsimp only at h3
  subst h3
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_A2 P hp hq x' hx').toData hN (m ^ 3)) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR2 false true m P.img.g (BASim_imgP P p') (BASim_imgP P (q'1, q.2)) x' _ _).partition m)
    (BASim_ggOuts_R2 _ _ _ _ _ _ _ _ _) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R2_ft m P.img.g (BASim_imgP P p') (BASim_imgP P (q'1, q.2)) x' ((promoteC P.g).vmap q.1.src) ((promoteC P.g).vmap p.1.dst))).mpr
    (BASim_pack_mono P.img (BASim_partition_owxExt_fix m (m ^ 3) _ id _ _) hR)

end MatchR2


/-! ### The terms with one anchored and one fresh new vertex: `A4`, `A5`, `AD` (sum 3, `W = 1`) -/

/-- **`A4`** (`M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'x}`: `α ↦ x̄`, `β ↦ n0`) at the band's `R3 = owxT1` of the frame (both selected edges uncircled) -/
def BASim_B_A4 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') (hx2 : (promoteC P.g).vmap q.1.dst = Sum.inr x')
    (hσ : p.1.σ = true ∧ q.1.σ = true) (hy' : (promoteC P.g).vmap q.1.src ≠ Sum.inr x') :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2
    [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst), bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)]
    [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]
    ({ BAScost_imgE P.g p.1 with circ := false } :: { BAScost_imgE P.g q.1 with circ := false } :: q.2.map (BAScost_imgE P.g))
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩]
    [{ BAScost_imgE P.g p.1 with circ := false }, { BAScost_imgE P.g q.1 with circ := false }]
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    (List.Perm.refl _)
    (by simp) (fun m' hm' => by
      rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      have hne1 : owxEmb 1 ((promoteC P.g).vmap q.1.src) ≠ owxEmb 1 (Sum.inr x') := fun h => hy' (lvl1_owxEmb_inj 1 h)
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BASim_phiE, bpS, SEdge.map, BAScost_imgE, BASim_phi21_emb,
        BASim_phi21_alpha, BASim_phi21_beta, hx', hx2, hσ.1, hσ.2]
      simp only [decide_true, Bool.and_true, Bool.false_and, decide_eq_false hne1, Bool.and_false]
      exact List.perm_append_singleton _ [_, _])
    (List.Forall₂.cons (Or.inl (by simp [WEdge.map, bpW, BASim_phi21_alpha, BASim_phi21_beta, hx', BASim_owxEmb1_inr])) List.Forall₂.nil)


/-- **`A5`** (`M_{xα} S_{αβ} Ǧ_{αx} G_{βy} G_{y'β}`: `α ↦ x̄`, `β ↦ n0`) at the band's `R5` -/
def BASim_B_A5 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src q.2
    [bpS true (bpv 0) (owxEmb 2 p.1.src), bpS false (bpv 1) (owxEmb 2 p.1.dst), bpS false (owxEmb 2 q.1.src) (bpv 1)]
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
        BASim_phi21_beta, hx', decide_true, Bool.and_true, Bool.false_and, BASim_owxEmb1_inr]
      exact List.Perm.refl _)
    (List.Forall₂.cons (Or.inl (by simp [WEdge.map, bpW, BASim_phi21_alpha, BASim_phi21_beta, hx', BASim_owxEmb1_inr])) List.Forall₂.nil)

/-- the derivative edges of a term read at a vertex map (the circle is not read) -/
theorem BASim_owxDE_congr {V : Type*} (a w : V) {e e' : SEdge V} (h1 : e.σ = e'.σ) (h2 : e.src = e'.src) (h3 : e.dst = e'.dst) :
    owxDE a w e = owxDE a w e' := by
  unfold owxDE; rw [h1, h2, h3]

theorem BASim_phiE_owxDE {V W : Type} [DecidableEq W] (φ : V → W) (a w : V) (e : SEdge V) :
    ((owxDE (φ a) (φ w) (SEdge.map φ e)).1 = BASim_phiE φ (owxDE a w e).1) ∧ ((owxDE (φ a) (φ w) (SEdge.map φ e)).2 = BASim_phiE φ (owxDE a w e).2) := by
  unfold owxDE
  cases h : e.σ <;> simp [BASim_phiE, SEdge.map, h]


/-- **`AD`** (the derivative of `gg2` at the edge `r.1` of `f`: `α ↦ x̄`, `β ↦ n0`) at the band's `R7` for the edge `r̄.1` -/
def BASim_B_AD (P : BAPGraph E) {p q r : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (hr : r ∈ lwSplit q.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') (hx2 : (promoteC P.g).vmap q.1.dst = Sum.inr x')
    (hσ : p.1.σ = true ∧ q.1.σ = true) (hy' : (promoteC P.g).vmap q.1.src ≠ Sum.inr x') :
    BASimExt P 2 ((BASimY P) ⊕ Fin 1) (owxEmb 1) :=
  BASim_mk21 P p.1.src r.2
    [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1, (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2,
      bpS false (bpv 1) (owxEmb 2 p.1.dst), bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)]
    [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]
    (r.2.map (BAScost_imgE P.g))
    [⟨true, false, owxEmb 1 ((promoteC P.g).vmap q.1.src), Sum.inr (Sum.inl x')⟩,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE P.g r.1))).1,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE P.g r.1))).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 ((promoteC P.g).vmap p.1.dst)⟩]
    [⟨false, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e (lvl1_mem_split _ r hr e he)))
    (by simp)
    (by simp) (fun m' hm' => by
      rw [List.mem_singleton] at hm'; subst hm'; exact BASim_phi21_anchor_dot P _)
    (by
      have hd := BASim_phiE_owxDE (BASim_phi21 P p.1.src) (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)
      have hc : owxDE (BASim_phi21 P p.1.src (bpv 1)) (BASim_phi21 P p.1.src (bpv 0)) (SEdge.map (BASim_phi21 P p.1.src) (SEdge.map (owxEmb 2) r.1)) =
          owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x')) (SEdge.map (owxEmb 1) (BAScost_imgE P.g r.1)) := by
        rw [BASim_phi21_alpha, BASim_phi21_beta, hx']
        exact BASim_owxDE_congr _ _ rfl (by simp [SEdge.map, BASim_phi21_emb, BAScost_imgE]) (by simp [SEdge.map, BASim_phi21_emb, BAScost_imgE])
      rw [hc] at hd
      have hne1 : owxEmb 1 ((promoteC P.g).vmap q.1.src) ≠ Sum.inr (Sum.inl x') :=
        fun h => hy' (lvl1_owxEmb_inj 1 (h.trans (BASim_owxEmb1_inr x').symm))
      simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append]
      rw [← hd.1, ← hd.2]
      simp only [BASim_phiE, bpS, BASim_phi21_emb, BASim_phi21_alpha, BASim_phi21_beta, hx', decide_true, Bool.and_true, Bool.false_and,
        BASim_owxEmb1_inr, decide_eq_false hne1, Bool.and_false]
      exact (List.perm_append_singleton _ [_, _, _]).symm)
    (List.Forall₂.cons (Or.inl (by simp [WEdge.map, bpW, BASim_phi21_alpha, BASim_phi21_beta, hx', BASim_owxEmb1_inr])) List.Forall₂.nil)


/-! ### The forms of the pair step at the selector `(0, 0)` -/

section FF
variable {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (m : ℂ) (Γ : LGraph E' I')
  (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (y y' : E' ⊕ I')

theorem BASim_R4_ff : lwSymmOe2xR4 false false m Γ p q x y y' = oe2xR4 m (lwSymmUncirc2 Γ p q) ({ q.1 with circ := false }, q.2) x y y' := by
  unfold lwSymmOe2xR4; rw [BASim_frame2Q_ff]; rfl
theorem BASim_R5_ff : lwSymmOe2xR5 false false m Γ p q x y y' = oe2xR5 m (lwSymmUncirc2 Γ p q) ({ q.1 with circ := false }, q.2) x y y' := by
  unfold lwSymmOe2xR5; rw [BASim_frame2Q_ff]; rfl
theorem BASim_R6_ff : lwSymmOe2xR6 false false m Γ p q x y y' = oe2xR6 m (lwSymmUncirc2 Γ p q) ({ q.1 with circ := false }, q.2) x y y' := by
  unfold lwSymmOe2xR6; rw [BASim_frame2Q_ff]; rfl
theorem BASim_R7_ff (q' : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) :
    lwSymmOe2xR7 false false m Γ p q x y y' q' = oe2xR7 m (lwSymmUncirc2 Γ p q) x y y' q' := by
  unfold lwSymmOe2xR7; rw [BASim_twistP_ff]; rfl
theorem BASim_R8_ff (q' : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) :
    lwSymmOe2xR8 false false m Γ p q x y y' q' = oe2xR8 m (lwSymmUncirc2 Γ p q) x y y' q' := by
  unfold lwSymmOe2xR8; rw [BASim_twistP_ff]; rfl

end FF

section MatchR3
variable (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
  (hq : q ∈ lwSplit p.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') (hx2 : (promoteC P.g).vmap q.1.dst = Sum.inr x')
  (hσ : p.1.σ = true ∧ q.1.σ = true) (hy' : (promoteC P.g).vmap q.1.src ≠ Sum.inr x')
include hN hp hq hx' hx2 hσ hy'

/-- **`A4` ↔ `R3`** at the selector `(0, 0)` -/
theorem BASim_match_A4 {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BAGGOp_A4 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_A4 P hp hq x' hx' hx2 hσ hy').toData hN m) m hT' hne
  exact ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR3 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x').partition m)
    (BASim_ggOuts_R3 _ _ _ _ _ _ _ _ _) hR, hRE⟩

/-- **`A5` ↔ `R5`** at the selector `(0, 0)` -/
theorem BASim_match_A5 {T' : BAGraph P.E' (P.I' ⊕ Fin 2)} (hT' : T' ∈ (BAGGOp_A5 P.g p q).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_A5 P hp hq x' hx').toData hN m) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR5 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _).partition m)
    (BASim_ggOuts_R5 _ _ _ _ _ _ _ _ _) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R5_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src))).mpr hR

/-- **`AD` ↔ `R7`** at the selector `(0, 0)` -/
theorem BASim_match_AD {r : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hr : r ∈ lwSplit q.2) {T' : BAGraph P.E' (P.I' ⊕ Fin 2)}
    (hT' : T' ∈ (BAGGOp_AD P.g p q r).splitG) (hne : P.g.extraB (owxEmb 2) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_AD P hp hq hr x' hx' hx2 hσ hy').toData hN m) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR7 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _ (BASim_imgP P r)).partition m)
    (BASim_ggOuts_R7 _ _ _ _ _ _ _ _ _ (BASim_imgP_mem2 P hr)) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R7_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) (BASim_imgP P r))).mpr hR

end MatchR3


/-! ### The terms with four new vertices: `B1`, `B2`, `BD` (sum 3, `W - 1`) -/

theorem BASim_phi42_emb (P : BAPGraph E) (a v : P.E' ⊕ P.I') :
    BASim_phi42 P a (owxEmb 4 v) = owxEmb 2 ((promoteC P.g).vmap v) := BASim_phi_emb _ _ _ _ v

theorem BASim_owxEmb2_inr {E' I' : Type} (x : I') : (owxEmb 2 (Sum.inr x) : E' ⊕ (I' ⊕ Fin 2)) = Sum.inr (Sum.inl x) := rfl

/-- **`B1`** (`u ↦ x̄`, `w, α ↦ n0`, `β ↦ n1`) at the band's `R4` -/
def BASim_B_B1 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') : BASimExt P 4 ((BASimY P) ⊕ Fin 2) (owxEmb 2) :=
  BASim_mk42 P p.1.src q.2
    [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) (owxEmb 4 p.1.dst), bpS true (owxEmb 4 q.1.src) (bpv 1)]
    [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]
    (q.2.map (BAScost_imgE P.g))
    [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 ((promoteC P.g).vmap p.1.dst)⟩, ⟨true, false, owxEmb 2 ((promoteC P.g).vmap q.1.src), Sum.inr (Sum.inr 0)⟩,
      ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩]
    [⟨true, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩, ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    (by simp)
    (by simp) (by simp)
    (fun m' hm' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (by
      have hne1 : owxEmb 2 ((promoteC P.g).vmap q.1.src) ≠ (Sum.inr (Sum.inr 0) : (BASimX P) ⊕ ((BASimY P) ⊕ Fin 2)) := (lwSymm_emb_ne _ 2 0).symm
      simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append, BASim_phiE, bpS, BASim_phi42_emb, BASim_phi42_one,
        BASim_phi42_two, BASim_phi42_three, BASim_phi42_zero, decide_true, Bool.and_true, Bool.false_and, decide_eq_false hne1, Bool.and_false]
      exact List.perm_append_singleton _ [_, _])
    (by
      refine List.Forall₂.cons (Or.inl ?_) (List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil)
      · simp [WEdge.map, bpW, BASim_phi42_zero, BASim_phi42_one, hx', BASim_owxEmb2_inr]
      · simp [WEdge.map, bpW, BASim_phi42_two, BASim_phi42_three])


/-- **`B2`** at the band's `R6` -/
def BASim_B_B2 (P : BAPGraph E) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') : BASimExt P 4 ((BASimY P) ⊕ Fin 2) (owxEmb 2) :=
  BASim_mk42 P p.1.src q.2
    [bpS true (bpv 2) (bpv 1), bpS false (bpv 3) (owxEmb 4 p.1.dst), bpS false (owxEmb 4 q.1.src) (bpv 3)]
    [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]
    (q.2.map (BAScost_imgE P.g))
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 ((promoteC P.g).vmap p.1.dst)⟩,
      ⟨true, false, owxEmb 2 ((promoteC P.g).vmap q.1.src), Sum.inr (Sum.inr 1)⟩]
    [⟨true, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩, ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e he))
    (by simp)
    (by simp) (by simp)
    (fun m' hm' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (by
      simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append, BASim_phiE, bpS, BASim_phi42_emb, BASim_phi42_one,
        BASim_phi42_two, BASim_phi42_three, BASim_phi42_zero, decide_true, Bool.and_true, Bool.false_and]
      exact List.Perm.refl _)
    (by
      refine List.Forall₂.cons (Or.inl ?_) (List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil)
      · simp [WEdge.map, bpW, BASim_phi42_zero, BASim_phi42_one, hx', BASim_owxEmb2_inr]
      · simp [WEdge.map, bpW, BASim_phi42_two, BASim_phi42_three])

/-- **`BD`** (the derivative of `gg4` at the edge `r.1`) at the band's `R8` -/
def BASim_B_BD (P : BAPGraph E) {p q r : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2)
    (hr : r ∈ lwSplit q.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x') : BASimExt P 4 ((BASimY P) ⊕ Fin 2) (owxEmb 2) :=
  BASim_mk42 P p.1.src r.2
    [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1, (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2,
      bpS false (bpv 3) (owxEmb 4 p.1.dst), bpS true (owxEmb 4 q.1.src) (bpv 1)]
    [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]
    (r.2.map (BAScost_imgE P.g))
    [⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 ((promoteC P.g).vmap p.1.dst)⟩, ⟨true, false, owxEmb 2 ((promoteC P.g).vmap q.1.src), Sum.inr (Sum.inr 0)⟩,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BAScost_imgE P.g r.1))).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BAScost_imgE P.g r.1))).2]
    [⟨true, true, Sum.inr (Sum.inl x'), Sum.inr (Sum.inr 0)⟩, ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩] []
    (fun e he => lvl1_mem_split _ p hp e (lvl1_mem_split _ q hq e (lvl1_mem_split _ r hr e he)))
    (by simp)
    (by simp) (by simp)
    (fun m' hm' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (by
      have hd := BASim_phiE_owxDE (BASim_phi42 P p.1.src) (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)
      have hc : owxDE (BASim_phi42 P p.1.src (bpv 3)) (BASim_phi42 P p.1.src (bpv 2)) (SEdge.map (BASim_phi42 P p.1.src) (SEdge.map (owxEmb 4) r.1)) =
          owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) (BAScost_imgE P.g r.1)) := by
        simp only [BASim_phi42_two, BASim_phi42_three]
        exact BASim_owxDE_congr _ _ rfl (by simp [SEdge.map, BASim_phi42_emb, BAScost_imgE]) (by simp [SEdge.map, BASim_phi42_emb, BAScost_imgE])
      rw [hc] at hd
      have hne1 : owxEmb 2 ((promoteC P.g).vmap q.1.src) ≠ (Sum.inr (Sum.inr 0) : (BASimX P) ⊕ ((BASimY P) ⊕ Fin 2)) := (lwSymm_emb_ne _ 2 0).symm
      simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append]
      rw [← hd.1, ← hd.2]
      simp only [BASim_phiE, bpS, BASim_phi42_emb, BASim_phi42_one, BASim_phi42_two, BASim_phi42_three, BASim_phi42_zero, decide_true,
        Bool.and_true, Bool.false_and, decide_eq_false hne1, Bool.and_false]
      exact List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _]))
    (by
      refine List.Forall₂.cons (Or.inl ?_) (List.Forall₂.cons (Or.inl ?_) List.Forall₂.nil)
      · simp [WEdge.map, bpW, BASim_phi42_zero, BASim_phi42_one, hx', BASim_owxEmb2_inr]
      · simp [WEdge.map, bpW, BASim_phi42_two, BASim_phi42_three])


section MatchR4
variable (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
  (hq : q ∈ lwSplit p.2) (x' : BASimY P) (hx' : (promoteC P.g).vmap p.1.src = Sum.inr x')
include hN hp hq hx'

/-- **`B1` ↔ `R4`** at the selector `(0, 0)` -/
theorem BASim_match_B1 {T' : BAGraph P.E' (P.I' ⊕ Fin 4)} (hT' : T' ∈ (BAGGOp_B1 P.g p q).splitG) (hne : P.g.extraB (owxEmb 4) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_B1 P hp hq x' hx').toData hN (m ^ 3)) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR4 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _).partition m)
    (BASim_ggOuts_R4 _ _ _ _ _ _ _ _ _) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R4_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src))).mpr hR

/-- **`B2` ↔ `R6`** at the selector `(0, 0)` -/
theorem BASim_match_B2 {T' : BAGraph P.E' (P.I' ⊕ Fin 4)} (hT' : T' ∈ (BAGGOp_B2 P.g p q).splitG) (hne : P.g.extraB (owxEmb 4) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_B2 P hp hq x' hx').toData hN (m ^ 3)) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR6 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _).partition m)
    (BASim_ggOuts_R6 _ _ _ _ _ _ _ _ _) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R6_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src))).mpr hR

/-- **`BD` ↔ `R8`** at the selector `(0, 0)` -/
theorem BASim_match_BD {r : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hr : r ∈ lwSplit q.2) {T' : BAGraph P.E' (P.I' ⊕ Fin 4)}
    (hT' : T' ∈ (BAGGOp_BD P.g p q r).splitG) (hne : P.g.extraB (owxEmb 4) T' = false) :
    ∃ R ∈ lvl1Pack P.img (lvl1GGOuts0 m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) false false),
      R.BAEquiv (P.outOf T').img := by
  obtain ⟨R, hR, hRE⟩ := BASim_match ((BASim_B_BD P hp hq hr x' hx').toData hN (m ^ 3)) m hT' hne
  refine ⟨R, BASim_pack_mono P.img (L := (lwSymmOe2xR8 false false m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' _ _ (BASim_imgP P r)).partition m)
    (BASim_ggOuts_R8 _ _ _ _ _ _ _ _ _ (BASim_imgP_mem2 P hr)) ?_, hRE⟩
  exact (congrArg (fun g => R ∈ lvl1Pack P.img (LGraph.partition m g))
    (BASim_R8_ff m P.img.g (BASim_imgP P p) (BASim_imgP P q) x' ((promoteC P.g).vmap p.1.dst) ((promoteC P.g).vmap q.1.src) (BASim_imgP P r))).mpr hR

end MatchR4


/-- **`BAMatch` for the step at a pair of edges** (`BAFrameStepT.gg`): every `band`-tagged output equals an output of the band step at the image (`nat`, and `swap` for `A2`) -/
theorem BASim_matchLT_gg (P : BAPGraph E) (hN : P.g.Normal) (m : ℂ) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))}
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) (x : P.I')
    (hx : p.1.src = Sum.inr x ∧ q.1.dst = Sum.inr x) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
    (hint : P.g.intAtom (Sum.inr x) = true)
    (hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
      ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0))
    {Q : BAPGraph E} (hQ : (BAShape.band, Q) ∈ P.outsT (P.g.tagStd 2) (P.g.gg2 p q) ++ P.outsT (P.g.tagStd 4) (P.g.gg4 p q)) :
    ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img := by
  obtain ⟨x', hx1, hx2, hy, hy', hnat, p', hp', q', hq', h1, h2, h3, hswap⟩ :=
    BASim_locStep_gg P m hp hq ⟨h.1, h.2.2.1⟩ x x hx ((BAAtomic_promoteC_vmap_eq_sameAtom P.g _ _).1 rfl) hwf hint hnb
  have hσ : p.1.σ = true ∧ q.1.σ = true := ⟨h.1, h.2.2.1⟩
  rcases List.mem_append.1 hQ with hQ | hQ
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    have hne := BASim_tagStd_band P.g 2 T' htag
    rw [BAGGOp_gg2_eq] at hT
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hT
    rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, hr, rfl⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_A1 P hN m hp hq x' hx1 hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_A2 P hN m hp hq x' hx1 h3 hT' hne
      exact ⟨_, hswap, R, hR, hRE⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_A3 P hN m hp hq x' hx1 hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_A4 P hN m hp hq x' hx1 hx2 hσ hy' hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_A5 P hN m hp hq x' hx1 hx2 hσ hy' hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_AD P hN m hp hq x' hx1 hx2 hσ hy' hr hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩
  · obtain ⟨T, hT, T', hT', htag, rfl⟩ := BASim_mem_outsT P _ _ _ _ hQ
    have hne := BASim_tagStd_band P.g 4 T' htag
    rw [BAGGOp_gg4_eq] at hT
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hT
    rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_B1 P hN m hp hq x' hx1 hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_B2 P hN m hp hq x' hx1 hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩
    · obtain ⟨R, hR, hRE⟩ := BASim_match_BD P hN m hp hq x' hx1 hr hT' hne
      exact ⟨_, hnat, R, hR, hRE⟩

end GG2

end RBM.Graph

end
