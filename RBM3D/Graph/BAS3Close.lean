/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAG5Leaf
import RBM3D.Graph.BALvl1B

/-!
# BA-L L4d2b (T2450), part A: the S3 roots, their expansion identity, the stuck catalogue

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:66-121`; design
`docs/claude-team/fable/2026-10-12-s3-fold-A.md` §1, §4, supervisor `2026-10-12-0851.md` Q2,
S3A-C5.
Roots: `docs/reports/T2433-prove.md` §(a⁗) (a).  Twin of `Graph/BAExpandId.lean` §6.

## Contents (namespace `RBM.Graph`; private prefix `BAS3Close_`)

1. The roots `baS3RootM` (`MERGED = T3C-tr_0 + D1X`), `baS3Root1` (`T3C-tr_1`), `baS3RootD`
   (`D2X`) at the
   tail charge `s`, the root lists `BAS3expandRoot`, the identity `BAS3Identity`,
   `baS3Identity_holds`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

open private BAExpandId_integral_partition BAExpandId_flat_sum BAExpandId_lwSplit_map BAExpandId_pcomp_val
  from RBM3D.Graph.BAExpandId
open private BAVocab_closure_equiv BAVocab_cnt_equiv BAVocab_vmap_injective BAVocab_vmap_surjective BAVocab_vmap_isRight
  BAVocab_vmap_inl BAVocab_val_of_factor BAVocab_val_of_not BAVocab_packMerge_val BAVocab_cls_eq_iff
  BAVocab_dotted_any_false BAVocab_merge_dotted_eq BAVocab_vmap_inr_int BAVocab_exists_inr_of_int BAVocab_adj_comm
  BAVocab_mol_eq_of_mem BAVocab_self_mem_mol BAVocab_self_mem_atom
  from RBM3D.Graph.BAVocab
open private BAWeightOp_packMerge_counters from RBM3D.Graph.BAWeightOp

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

/-! ## 1. The roots, the root lists, the identity (target 1) -/

/-- **Root `MERGED`** (`T3C-tr_0 + D1X`, T2433-prove `:170-177`; `x = inl 0`, `y = inl 1`, `iJ = inr J`; `i0..i3 = w, γ, δ, v`):
`G(x,i0) G(i2,y) G(i3,i2) G(i1,i3)` and the tail `G(y,x)` (`s = true`) or `Ḡ(x,y)` (`s = false`), all uncircled; black `S(i1,i2)`,
`S(i0,i3)` (the block identity `W^{-d} 1[v ∈ [w]] = S_{wv}/t`); `M(i0,i1)`; coefficient `1` (root value `= t ×` S3 integrand). -/
def baS3RootM (s : Bool) : BAGraph (Fin 2) (Fin 4) :=
  { solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 2) (Sum.inl 1),
      SEdge.mk true false (Sum.inr 3) (Sum.inr 2), SEdge.mk true false (Sum.inr 1) (Sum.inr 3),
      if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
    waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 2), WEdge.mk false false (Sum.inr 0) (Sum.inr 3)],
    dotted := [], coeff := 1, psi := [],
    mdot := [BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)] }

/-- **Root `T3C-tr_1`** (`i0..i5 = α, b, w, γ, δ, v`): `Ǧ(x,i2)` circled, `G(i4,y) G(i5,i4) G(i3,i5)`, the tail; `S⁺(i1,i2)`
(coloured), black `S(i3,i4)`, `S(i0,i5)`; `M(i0,i1) M(i1,i0)` (`M⁺`), `M(i2,i3)`; coefficient `1`. -/
def baS3Root1 (s : Bool) : BAGraph (Fin 2) (Fin 6) :=
  { solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 2), SEdge.mk true false (Sum.inr 4) (Sum.inl 1),
      SEdge.mk true false (Sum.inr 5) (Sum.inr 4), SEdge.mk true false (Sum.inr 3) (Sum.inr 5),
      if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
    waved := [WEdge.mk true true (Sum.inr 1) (Sum.inr 2), WEdge.mk false false (Sum.inr 3) (Sum.inr 4),
      WEdge.mk false false (Sum.inr 0) (Sum.inr 5)],
    dotted := [], coeff := 1, psi := [],
    mdot := [BAMEdge.mk true (Sum.inr 0) (Sum.inr 1), BAMEdge.mk true (Sum.inr 1) (Sum.inr 0),
      BAMEdge.mk true (Sum.inr 2) (Sum.inr 3)] }

/-- **Root `D2X`** (`i0..i3 = α, α', v, β`): `G(i3,i0) G(i2,i3) G(i1,i2)`, the tail; black `S(i1,i3)`, `S(i0,i2)`; `M(x,i1)`, `M(i0,y)`;
coefficient `1`. -/
def baS3RootD (s : Bool) : BAGraph (Fin 2) (Fin 4) :=
  { solid := [SEdge.mk true false (Sum.inr 3) (Sum.inr 0), SEdge.mk true false (Sum.inr 2) (Sum.inr 3),
      SEdge.mk true false (Sum.inr 1) (Sum.inr 2),
      if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
    waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 3), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)],
    dotted := [], coeff := 1, psi := [],
    mdot := [BAMEdge.mk true (Sum.inl 0) (Sum.inr 1), BAMEdge.mk true (Sum.inr 0) (Sum.inl 1)] }

/-- **The root lists** (twin of `BAexpandRoot`, `BAExpandId.lean:379`): index `0 = MERGED`, `1 = T3C-tr_1`, `2 = D2X`; the partition of
the root, each term expanded, the exponent pairs dropped. -/
def BAS3expandRoot (sel : BASel) (fuel : ℕ) : Fin 3 → Bool → List (BAPGraph (Fin 2))
  | 0, s => (baS3RootM s).partition.flatMap fun P => (BAexpand sel fuel P).map Prod.snd
  | 1, s => (baS3Root1 s).partition.flatMap fun P => (BAexpand sel fuel P).map Prod.snd
  | 2, s => (baS3RootD s).partition.flatMap fun P => (BAexpand sel fuel P).map Prod.snd

/-- **The identity statement** (twin of `BAG5Identity`, `BAExpandId.lean:89`): for lists `Ls r s`, the expectation identity
`𝔼 root = Σ_μ 𝔼 Γ_μ` at `BAlwData` over `PF d L W 0`, `BASelf`, `0 ≤ t < 1`, for the three roots. -/
def BAS3Identity (d : ℕ) (Ls : Fin 3 → Bool → List (BAPGraph (Fin 2))) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (s : Bool) (x y : Idx d L W),
      (∫ ω, (baS3RootM s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
          ((Ls 0 s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum) ∧
        (∫ ω, (baS3Root1 s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
          ((Ls 1 s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum) ∧
        (∫ ω, (baS3RootD s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
          ((Ls 2 s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum)

/-- The identity for one root `R` (any internal type): `baExpandIdentity_holds` with `baG5Graph k s` replaced by `R`. -/
private theorem BAS3Close_root_identity (d : ℕ) (sel : BASel) (fuel : ℕ) {I : Type} [Fintype I] [DecidableEq I]
    (R : BAGraph (Fin 2) I) (L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : Idx d L W) :
    ∫ ω, R.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
      ((R.partition.flatMap fun P => (BAexpand sel fuel P).map Prod.snd).map fun q =>
        ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum := by
  have hexp := expandG_sum (BAstep sel) (fun P : BAPGraph (Fin 2) => P.g.Normal)
    (fun P => ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)) (fun _ => 1) rfl
    (fun _ _ _ _ => (one_mul (1 : ℂ)).symm)
    (by
      intro P l hP hst
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hst
      refine ⟨c.kids_normal, ?_⟩
      simp only [one_mul]
      exact BARCand.kids_identity hL g0 E t m hSelf ht0 ht1 c x y) fuel
  rw [BAExpandId_integral_partition hL g0 E t m hSelf ht0 ht1 R ![x, y]]
  exact (BAExpandId_flat_sum (fun P : BAPGraph (Fin 2) => ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0))
    R.partition (fun P => BAexpand sel fuel P) (by
      intro P _
      have := (hexp P (BAGraph.partition_normal _ P ‹_›)).1
      simpa [BAexpand] using this)).symm

/-- **The identity half of the S3 expansion, for every selection rule and every fuel** (target 1): the three root lists satisfy the
expectation identity.  `expandG_sum` with the invariant `Normal`, the weight `1`, and the step lemma `kids_normal` + `kids_identity`. -/
theorem baS3Identity_holds (d : ℕ) (sel : BASel) (fuel : ℕ) : BAS3Identity d (BAS3expandRoot sel fuel) := by
  intro L W _ _ hL g0 E t m hSelf ht0 ht1 s x y
  exact ⟨BAS3Close_root_identity d sel fuel (baS3RootM s) L W hL g0 E t m hSelf ht0 ht1 x y,
    BAS3Close_root_identity d sel fuel (baS3Root1 s) L W hL g0 E t m hSelf ht0 ht1 x y,
    BAS3Close_root_identity d sel fuel (baS3RootD s) L W hL g0 E t m hSelf ht0 ht1 x y⟩


/-! ## 2. Relabelling of BA graphs and isomorphism of packed graphs

`BAS3Close_rel f Γ` renames every vertex reference of `Γ` along `f`.  Along a bijection that keeps external and internal vertices
apart it keeps the value, the counters, the atoms and the molecules (`BAS3Close_val_rel`, `_counters_rel`, `_atom_rel`).  Two packed
graphs are *isomorphic* if such a bijection carries one to the other and respects the external map. -/

section Rel

variable {E I E' I' : Type}

/-- All vertex references of `Γ` renamed along `f`. -/
private def BAS3Close_rel (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) : BAGraph E' I' where
  solid := Γ.solid.map (SEdge.map f)
  waved := Γ.waved.map (WEdge.map f)
  dotted := Γ.dotted.map (DEdge.map f)
  coeff := Γ.coeff
  psi := Γ.psi.map (BAPsiEdge.map f)
  mdot := Γ.mdot.map (BAMEdge.map f)

private theorem BAS3Close_rel_comp {E'' I'' : Type} (g : E' ⊕ I' → E'' ⊕ I'') (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) :
    BAS3Close_rel g (BAS3Close_rel f Γ) = BAS3Close_rel (g ∘ f) Γ := by
  simp only [BAS3Close_rel, List.map_map]
  rfl

private theorem BAS3Close_rel_id (Γ : BAGraph E I) : BAS3Close_rel (id : E ⊕ I → E ⊕ I) Γ = Γ := by
  obtain ⟨⟨s, w, d, c⟩, p, m⟩ := Γ
  have h1 : ∀ e : SEdge (E ⊕ I), SEdge.map id e = e := fun e => by cases e; rfl
  have h2 : ∀ e : WEdge (E ⊕ I), WEdge.map id e = e := fun e => by cases e; rfl
  have h3 : ∀ e : DEdge (E ⊕ I), DEdge.map id e = e := fun e => by cases e; rfl
  have h4 : ∀ e : BAPsiEdge (E ⊕ I), BAPsiEdge.map id e = e := fun e => by cases e; rfl
  have h5 : ∀ e : BAMEdge (E ⊕ I), BAMEdge.map id e = e := fun e => by cases e; rfl
  have e1 : SEdge.map (id : E ⊕ I → E ⊕ I) = id := funext h1
  have e2 : WEdge.map (id : E ⊕ I → E ⊕ I) = id := funext h2
  have e3 : DEdge.map (id : E ⊕ I → E ⊕ I) = id := funext h3
  have e4 : BAPsiEdge.map (id : E ⊕ I → E ⊕ I) = id := funext h4
  have e5 : BAMEdge.map (id : E ⊕ I → E ⊕ I) = id := funext h5
  simp only [BAS3Close_rel, e1, e2, e3, e4, e5, List.map_id]

end Rel

section RelVal

variable {E I E' I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem BAS3Close_term_rel (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) (D : BALData ι) (ℓ : E' ⊕ I' → ι) :
    (BAS3Close_rel f Γ).term D ℓ = Γ.term D (ℓ ∘ f) := by
  have h1 := LGraph.term_relabel Γ.toLGraph f D.toLData ℓ
  have h2 : (BAS3Close_rel f Γ).toLGraph = Γ.toLGraph.relabel f := rfl
  unfold BAGraph.term
  rw [h2, h1]
  simp only [BAS3Close_rel, List.map_map]
  rfl

/-- **The value under a renaming of the vertices by bijections** of the external and the internal vertices. -/
private theorem BAS3Close_val_rel (eE : E ≃ E') (eI : I ≃ I') (Γ : BAGraph E I) (D : BALData ι) (ℓe' : E' → ι) :
    (BAS3Close_rel (Equiv.sumCongr eE eI) Γ).val D ℓe' = Γ.val D (ℓe' ∘ eE) := by
  unfold BAGraph.val
  refine Fintype.sum_equiv (Equiv.arrowCongr eI.symm (Equiv.refl ι)) _ _ fun ℓi' => ?_
  rw [BAS3Close_term_rel]
  congr 1
  funext v
  rcases v with a | b <;> simp [Equiv.arrowCongr]

end RelVal

section RelAtom

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E'] [DecidableEq E']
  [Fintype I'] [DecidableEq I']

private theorem BAS3Close_atomAdj_rel (ψ : E ⊕ I ≃ E' ⊕ I') (Γ : BAGraph E I) (u v : E ⊕ I) :
    (BAS3Close_rel ψ Γ).atomAdj (ψ u) (ψ v) = Γ.atomAdj u v := by
  unfold BAGraph.atomAdj
  simp only [BAS3Close_rel, List.any_map, Function.comp_def, BAPsiEdge.map, BAMEdge.map, DEdge.map, ψ.injective.eq_iff]

private theorem BAS3Close_adj_rel (ψ : E ⊕ I ≃ E' ⊕ I') (Γ : BAGraph E I) (u v : E ⊕ I) :
    (BAS3Close_rel ψ Γ).adj (ψ u) (ψ v) = Γ.adj u v := by
  unfold BAGraph.adj RBM.Graph.LGraph.adj
  rw [← BAS3Close_atomAdj_rel ψ Γ u v]
  simp only [BAS3Close_rel, List.any_map, Function.comp_def, WEdge.map, DEdge.map, ψ.injective.eq_iff]

/-- The atoms of the renamed graph are the images of the atoms. -/
private theorem BAS3Close_atom_rel (ψ : E ⊕ I ≃ E' ⊕ I') (Γ : BAGraph E I) (v : E ⊕ I) :
    (BAS3Close_rel ψ Γ).atom (ψ v) = (Γ.atom v).map ψ.toEmbedding :=
  BAVocab_closure_equiv (fun a b => Γ.atomAdj a b) (fun a b => (BAS3Close_rel ψ Γ).atomAdj a b) ψ
    (fun u w => BAS3Close_atomAdj_rel ψ Γ u w) v

/-- The molecules of the renamed graph are the images of the molecules. -/
private theorem BAS3Close_mol_rel (ψ : E ⊕ I ≃ E' ⊕ I') (Γ : BAGraph E I) (v : E ⊕ I) :
    (BAS3Close_rel ψ Γ).mol (ψ v) = (Γ.mol v).map ψ.toEmbedding :=
  BAVocab_closure_equiv (fun a b => Γ.adj a b) (fun a b => (BAS3Close_rel ψ Γ).adj a b) ψ
    (fun u w => BAS3Close_adj_rel ψ Γ u w) v

/-- The counters are invariant under a renaming by a bijection that keeps external and internal vertices apart. -/
private theorem BAS3Close_counters_rel (ψ : E ⊕ I ≃ E' ⊕ I') (hψ : ∀ v, (ψ v).isRight = v.isRight) (Γ : BAGraph E I) :
    (BAS3Close_rel ψ Γ).counters = Γ.counters := by
  have hnS : (BAS3Close_rel ψ Γ).nS = Γ.nS := by simp [BAGraph.nS, BAS3Close_rel]
  have hnW : (BAS3Close_rel ψ Γ).nW = Γ.nW := by simp [BAGraph.nW, BAS3Close_rel]
  have hnA : (BAS3Close_rel ψ Γ).nA = Γ.nA := by
    unfold BAGraph.nA
    exact BAVocab_cnt_equiv ψ hψ Γ.atom (BAS3Close_rel ψ Γ).atom fun v => BAS3Close_atom_rel ψ Γ v
  have hnM : (BAS3Close_rel ψ Γ).nM = Γ.nM := by
    unfold BAGraph.nM
    exact BAVocab_cnt_equiv ψ hψ Γ.mol (BAS3Close_rel ψ Γ).mol fun v => BAS3Close_mol_rel ψ Γ v
  unfold BAGraph.counters
  rw [hnS, hnW, hnA, hnM]

private theorem BAS3Close_normal_rel (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) :
    (BAS3Close_rel f Γ).Normal ↔ Γ.Normal := by
  unfold BAGraph.Normal
  simp only [BAS3Close_rel, List.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun e he => by simpa [DEdge.map] using h1 _ ⟨e, he, rfl⟩,
      fun e he => by simpa [SEdge.map] using h2 _ ⟨e, he, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      simpa [DEdge.map] using h1 e he
    · rintro _ ⟨e, he, rfl⟩
      simpa [SEdge.map] using h2 e he

end RelAtom

section Iso

/-- Two packed graphs are *isomorphic* if bijections of the external and of the internal vertices carry the graph of the first to the
graph of the second and respect the external maps. -/
private def BAS3Close_Iso (P Q : BAPGraph (Fin 2)) : Prop :=
  ∃ (eE : P.E' ≃ Q.E') (eI : P.I' ≃ Q.I'), (∀ a, eE (P.ext a) = Q.ext a) ∧
    Q.g = BAS3Close_rel (Equiv.sumCongr eE eI) P.g

private theorem BAS3Close_iso_symm {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : BAS3Close_Iso Q P := by
  obtain ⟨eE, eI, hext, hg⟩ := h
  refine ⟨eE.symm, eI.symm, fun a => by rw [← hext a]; simp, ?_⟩
  rw [hg, BAS3Close_rel_comp]
  have : ((Equiv.sumCongr eE.symm eI.symm) ∘ (Equiv.sumCongr eE eI) : P.E' ⊕ P.I' → P.E' ⊕ P.I') = id := by
    funext v; rcases v with a | b <;> simp
  rw [this, BAS3Close_rel_id]

private theorem BAS3Close_iso_trans {P Q R : BAPGraph (Fin 2)} (h1 : BAS3Close_Iso P Q) (h2 : BAS3Close_Iso Q R) :
    BAS3Close_Iso P R := by
  obtain ⟨eE, eI, hext, hg⟩ := h1
  obtain ⟨eE', eI', hext', hg'⟩ := h2
  refine ⟨eE.trans eE', eI.trans eI', fun a => by simp [hext a, hext' a], ?_⟩
  rw [hg', hg, BAS3Close_rel_comp]
  have : ((Equiv.sumCongr eE' eI') ∘ (Equiv.sumCongr eE eI) : P.E' ⊕ P.I' → R.E' ⊕ R.I') =
      (Equiv.sumCongr (eE.trans eE') (eI.trans eI') : P.E' ⊕ P.I' → R.E' ⊕ R.I') := by
    funext v; rcases v with a | b <;> simp
  rw [this]

/-- The isomorphism as an equivalence of vertex sets that keeps external and internal vertices apart. -/
private theorem BAS3Close_isRight_sumCongr {E I E' I' : Type} (eE : E ≃ E') (eI : I ≃ I') (v : E ⊕ I) :
    ((Equiv.sumCongr eE eI) v).isRight = v.isRight := by
  rcases v with a | b <;> simp

/-- Isomorphic packed graphs have the same counters. -/
private theorem BAS3Close_iso_counters {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : Q.counters = P.counters := by
  obtain ⟨eE, eI, hext, hg⟩ := h
  change Q.g.counters = P.g.counters
  rw [hg]
  exact BAS3Close_counters_rel _ (BAS3Close_isRight_sumCongr eE eI) P.g

private theorem BAS3Close_iso_normal {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : Q.g.Normal ↔ P.g.Normal := by
  obtain ⟨eE, eI, hext, hg⟩ := h
  rw [hg]
  exact BAS3Close_normal_rel _ _

/-- Isomorphic packed graphs have the same value, at every datum and every external labelling. -/
private theorem BAS3Close_iso_val {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : BALData ι) (ℓ : Fin 2 → ι) : Q.val D ℓ = P.val D ℓ := by
  obtain ⟨eE, eI, hext, hg⟩ := h
  by_cases hf : ∃ ℓ' : P.E' → ι, ℓ = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    have hℓ2 : ℓ = (ℓ' ∘ eE.symm) ∘ Q.ext := by
      funext a
      simp [Function.comp, ← hext a, hℓ]
    rw [BAVocab_val_of_factor P D hℓ, BAVocab_val_of_factor Q D hℓ2, hg, BAS3Close_val_rel]
    congr 1
    funext a
    simp
  · rw [BAVocab_val_of_not P D hf, BAVocab_val_of_not]
    rintro ⟨ℓq, hℓq⟩
    exact hf ⟨ℓq ∘ eE, by funext a; simp only [Function.comp, hext a]; exact congrFun hℓq a⟩

private theorem BAS3Close_iso_nM {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : Q.g.nM = P.g.nM :=
  congrArg Counters.nM (BAS3Close_iso_counters h)

private theorem BAS3Close_iso_nW {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : Q.g.nW = P.g.nW :=
  congrArg Counters.nW (BAS3Close_iso_counters h)

private theorem BAS3Close_iso_order {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : Q.scalingOrder = P.scalingOrder := by
  unfold BAPGraph.scalingOrder
  rw [BAS3Close_iso_counters h]

/-- `x ~ y` (the external vertices lie in one atom) is invariant. -/
private theorem BAS3Close_iso_xy {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) :
    (Q.g.atom (Sum.inl (Q.ext 0)) = Q.g.atom (Sum.inl (Q.ext 1))) ↔
      (P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1))) := by
  obtain ⟨eE, eI, hext, hg⟩ := h
  have h0 : Sum.inl (Q.ext 0) = (Equiv.sumCongr eE eI) (Sum.inl (P.ext 0)) := by simp [hext 0]
  have h1 : Sum.inl (Q.ext 1) = (Equiv.sumCongr eE eI) (Sum.inl (P.ext 1)) := by simp [hext 1]
  rw [hg, h0, h1, BAS3Close_atom_rel, BAS3Close_atom_rel]
  exact Finset.map_inj

private theorem BAS3Close_iso_tgt {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : BAG5Tgt Q ↔ BAG5Tgt P := by
  unfold BAG5Tgt
  rw [BAS3Close_iso_order h]
  have hxy := BAS3Close_iso_xy h
  by_cases hx : P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1))
  · simp [hx, hxy.2 hx]
  · have hx' : ¬ (Q.g.atom (Sum.inl (Q.ext 0)) = Q.g.atom (Sum.inl (Q.ext 1))) := fun hh => hx (hxy.1 hh)
    simp [hx, hx']

private theorem BAS3Close_iso_leaf {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : BAG5Leaf Q ↔ BAG5Leaf P := by
  unfold BAG5Leaf
  rw [BAS3Close_iso_tgt h, BAS3Close_iso_nM h, BAS3Close_iso_nW h]

/-- The unmerged packed graph of `Δ` over the base `P`: the graph `Δ` itself, the external vertices read through `P.ext`. -/
private def BAS3Close_up (P : BAPGraph (Fin 2)) {I2 : Type} [Fintype I2] [DecidableEq I2] (Δ : BAGraph P.E' I2) :
    BAPGraph (Fin 2) :=
  { E' := P.E', I' := I2, ext := P.ext, ext_surj := P.ext_surj, g := Δ }

section Merge

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Without `=`-dotted edges the external map of the merge is a bijection. -/
private def BAS3Close_extEquiv (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) : E ≃ Γ.toLGraph.ExtCls :=
  Equiv.ofBijective Γ.toLGraph.extMap ⟨fun a b hab => by
    have h1 : Γ.toLGraph.vmap (Sum.inl a) = Γ.toLGraph.vmap (Sum.inl b) := by
      rw [BAVocab_vmap_inl, BAVocab_vmap_inl, hab]
    exact Sum.inl_injective (BAVocab_vmap_injective Γ.toLGraph h h1), Γ.toLGraph.extMap_surj⟩

private theorem BAS3Close_not_ext (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (b : I) :
    ¬ Γ.toLGraph.IsExtCls (Γ.toLGraph.cls (Sum.inr b)) := by
  rintro ⟨a, ha⟩
  exact absurd ((BAVocab_cls_eq_iff Γ.toLGraph h _ _).1 ha) (by simp)

/-- Without `=`-dotted edges the internal vertices of the merge are the internal vertices. -/
private def BAS3Close_intEquiv (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) : I ≃ Γ.toLGraph.IntCls :=
  Equiv.ofBijective (fun b => ⟨Γ.toLGraph.cls (Sum.inr b), BAS3Close_not_ext Γ h b⟩)
    ⟨fun a b hab => by
      have := congrArg Subtype.val hab
      exact Sum.inr_injective ((BAVocab_cls_eq_iff Γ.toLGraph h _ _).1 this),
     fun q => by
      obtain ⟨b, hb⟩ := BAVocab_exists_inr_of_int Γ.toLGraph q
      exact ⟨b, Subtype.ext hb⟩⟩

private theorem BAS3Close_vmap_eq (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (v : E ⊕ I) :
    Γ.toLGraph.vmap v = (Equiv.sumCongr (BAS3Close_extEquiv Γ h) (BAS3Close_intEquiv Γ h)) v := by
  rcases v with a | b
  · rw [BAVocab_vmap_inl]
    rfl
  · rw [BAVocab_vmap_inr_int Γ.toLGraph b (BAS3Close_not_ext Γ h b)]
    rfl

/-- **Without `=`-dotted edges the merge is a renaming**: `Δ.merge = rel vmap Δ`. -/
private theorem BAS3Close_merge_eq (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) :
    Γ.merge = BAS3Close_rel Γ.toLGraph.vmap Γ := by
  have hd : (Γ.dotted.filter fun e => !e.eq) = Γ.dotted := by
    refine List.filter_eq_self.2 fun e he => ?_
    simp [h e he]
  simp only [BAGraph.merge, RBM.Graph.LGraph.merge, BAS3Close_rel, hd]

end Merge

/-- **The packed merge of a graph without `=`-dotted edges is isomorphic to the unmerged pack** (target of the closure: the kids of a
candidate are `pcomp P (packMerge Δ)`). -/
private theorem BAS3Close_iso_merge (P : BAPGraph (Fin 2)) {I2 : Type} [Fintype I2] [DecidableEq I2] (Δ : BAGraph P.E' I2)
    (h : ∀ e ∈ Δ.dotted, e.eq = false) :
    BAS3Close_Iso (BAS3Close_up P Δ) (BAExpandId_pcomp P Δ.packMerge) := by
  refine ⟨BAS3Close_extEquiv Δ h, BAS3Close_intEquiv Δ h, fun a => rfl, ?_⟩
  change Δ.merge = BAS3Close_rel _ Δ
  rw [BAS3Close_merge_eq Δ h]
  congr 1
  funext v
  exact BAS3Close_vmap_eq Δ h v

end Iso

/-! ## 3. Naturality of the `GG` step under renamings -/

section Natural

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E'] [DecidableEq E']
  [Fintype I'] [DecidableEq I']

/-- The renaming `f` extended to the `k` new vertices of an extension (identity on them). -/
private def BAS3Close_lift (k : ℕ) (f : E ⊕ I → E' ⊕ I') : E ⊕ (I ⊕ Fin k) → E' ⊕ (I' ⊕ Fin k)
  | Sum.inl a => owxEmb k (f (Sum.inl a))
  | Sum.inr (Sum.inl b) => owxEmb k (f (Sum.inr b))
  | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr i)

private theorem BAS3Close_lift_emb (k : ℕ) (f : E ⊕ I → E' ⊕ I') (v : E ⊕ I) :
    BAS3Close_lift k f (owxEmb k v) = owxEmb k (f v) := by
  rcases v with a | b <;> rfl

private theorem BAS3Close_lift_bpv (k : ℕ) (f : E ⊕ I → E' ⊕ I') (i : Fin k) :
    BAS3Close_lift k f (bpv i) = bpv i := rfl

/-- The renaming of a pair `(edge, rest)` of `lwSplit`. -/
private def BAS3Close_mapP {V W : Type} (f : V → W) (p : SEdge V × List (SEdge V)) : SEdge W × List (SEdge W) :=
  (SEdge.map f p.1, p.2.map (SEdge.map f))

private theorem BAS3Close_lift_sumCongr (k : ℕ) (eE : E ≃ E') (eI : I ≃ I') (v : E ⊕ (I ⊕ Fin k)) :
    BAS3Close_lift k (Equiv.sumCongr eE eI) v = (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin k)))) v := by
  rcases v with a | b | i <;> rfl

/-- **Naturality of the extension.** -/
private theorem BAS3Close_rel_ext (k : ℕ) (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    BAS3Close_rel (BAS3Close_lift k f) (BAGraph.ext k Γ rest s w md) =
      BAGraph.ext k (BAS3Close_rel f Γ) (rest.map (SEdge.map f)) (s.map (SEdge.map (BAS3Close_lift k f)))
        (w.map (WEdge.map (BAS3Close_lift k f))) (md.map (BAMEdge.map (BAS3Close_lift k f))) := by
  have hf : ∀ v, BAS3Close_lift k f (owxEmb k v) = owxEmb k (f v) := BAS3Close_lift_emb k f
  simp only [BAS3Close_rel, BAGraph.ext, LGraph.owxExt, List.map_append, List.map_map]
  have e1 : (SEdge.map (BAS3Close_lift k f) ∘ SEdge.map (owxEmb k) : SEdge (E ⊕ I) → SEdge (E' ⊕ (I' ⊕ Fin k))) =
      SEdge.map (owxEmb k) ∘ SEdge.map f := by
    funext e; simp [SEdge.map, hf]
  have e2 : (WEdge.map (BAS3Close_lift k f) ∘ WEdge.map (owxEmb k) : WEdge (E ⊕ I) → WEdge (E' ⊕ (I' ⊕ Fin k))) =
      WEdge.map (owxEmb k) ∘ WEdge.map f := by
    funext e; simp [WEdge.map, hf]
  have e3 : (DEdge.map (BAS3Close_lift k f) ∘ DEdge.map (owxEmb k) : DEdge (E ⊕ I) → DEdge (E' ⊕ (I' ⊕ Fin k))) =
      DEdge.map (owxEmb k) ∘ DEdge.map f := by
    funext e; simp [DEdge.map, hf]
  have e4 : (BAPsiEdge.map (BAS3Close_lift k f) ∘ BAPsiEdge.map (owxEmb k) : BAPsiEdge (E ⊕ I) → BAPsiEdge (E' ⊕ (I' ⊕ Fin k))) =
      BAPsiEdge.map (owxEmb k) ∘ BAPsiEdge.map f := by
    funext e; simp [BAPsiEdge.map, hf]
  have e5 : (BAMEdge.map (BAS3Close_lift k f) ∘ BAMEdge.map (owxEmb k) : BAMEdge (E ⊕ I) → BAMEdge (E' ⊕ (I' ⊕ Fin k))) =
      BAMEdge.map (owxEmb k) ∘ BAMEdge.map f := by
    funext e; simp [BAMEdge.map, hf]
  simp only [e1, e2, e3, e4, e5, List.map_map]

private theorem BAS3Close_owxDE_map {V W : Type} (g : V → W) (a w : V) (e : SEdge V) :
    owxDE (g a) (g w) (SEdge.map g e) = (SEdge.map g (owxDE a w e).1, SEdge.map g (owxDE a w e).2) := by
  obtain ⟨σ, c, x, y⟩ := e
  cases σ <;> rfl

private theorem BAS3Close_owxDE_lift (k : ℕ) (f : E ⊕ I → E' ⊕ I') (a w : Fin k) (e : SEdge (E ⊕ I)) :
    owxDE (bpv a : E' ⊕ (I' ⊕ Fin k)) (bpv w) (SEdge.map (owxEmb k) (SEdge.map f e)) =
      (SEdge.map (BAS3Close_lift k f) (owxDE (bpv a : E ⊕ (I ⊕ Fin k)) (bpv w) (SEdge.map (owxEmb k) e)).1,
        SEdge.map (BAS3Close_lift k f) (owxDE (bpv a : E ⊕ (I ⊕ Fin k)) (bpv w) (SEdge.map (owxEmb k) e)).2) := by
  have h1 : SEdge.map (owxEmb k) (SEdge.map f e) = SEdge.map (BAS3Close_lift k f) (SEdge.map (owxEmb k) e) := by
    simp [SEdge.map, BAS3Close_lift_emb]
  rw [h1]
  exact BAS3Close_owxDE_map (BAS3Close_lift k f) (bpv a) (bpv w) (SEdge.map (owxEmb k) e)

private theorem BAS3Close_rel_gg2 (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (BAS3Close_rel f Γ).gg2 (BAS3Close_mapP f p) (BAS3Close_mapP f q) =
      (Γ.gg2 p q).map (BAS3Close_rel (BAS3Close_lift 2 f)) := by
  have hl : lwSplit (q.2.map (SEdge.map f)) = (lwSplit q.2).map (BAS3Close_mapP f) := BAExpandId_lwSplit_map _ _
  unfold BAGraph.gg2
  simp only [BAS3Close_mapP, hl, List.map_cons, List.map_append, List.map_nil, List.map_map, BAS3Close_rel_ext]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · simp only [BAMEdge.map, bpM, SEdge.map, bpS, WEdge.map, bpW, BAS3Close_lift_emb, BAS3Close_lift_bpv]
  · refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply, BAS3Close_rel_ext, BAS3Close_mapP, BAS3Close_owxDE_lift]
    simp only [List.map_cons, List.map_nil, BAMEdge.map, bpM, SEdge.map, bpS, WEdge.map, bpW, BAS3Close_lift_emb,
      BAS3Close_lift_bpv]

private theorem BAS3Close_rel_gg4 (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (BAS3Close_rel f Γ).gg4 (BAS3Close_mapP f p) (BAS3Close_mapP f q) =
      (Γ.gg4 p q).map (BAS3Close_rel (BAS3Close_lift 4 f)) := by
  have hl : lwSplit (q.2.map (SEdge.map f)) = (lwSplit q.2).map (BAS3Close_mapP f) := BAExpandId_lwSplit_map _ _
  unfold BAGraph.gg4
  simp only [BAS3Close_mapP, hl, List.map_cons, List.map_append, List.map_nil, List.map_map, BAS3Close_rel_ext]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · simp only [BAMEdge.map, bpM, SEdge.map, bpS, WEdge.map, bpW, BAS3Close_lift_emb, BAS3Close_lift_bpv]
  · refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply, BAS3Close_rel_ext, BAS3Close_mapP, BAS3Close_owxDE_lift]
    simp only [List.map_cons, List.map_nil, BAMEdge.map, bpM, SEdge.map, bpS, WEdge.map, bpW, BAS3Close_lift_emb,
      BAS3Close_lift_bpv]

private theorem BAS3Close_baSplitSolid_map {V W : Type} (g : V → W) (es : List (SEdge V)) :
    baSplitSolid (es.map (SEdge.map g)) =
      (baSplitSolid es).map (fun r => (r.1.map (SEdge.map g), r.2.map (BAMEdge.map g))) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨σ, c, x, y⟩ := e
    cases c <;> simp [baSplitSolid, ih, List.flatMap_map, List.map_flatMap, SEdge.map, BAMEdge.map]

/-- **Naturality of the `G = Ǧ + M` split.** -/
private theorem BAS3Close_rel_splitG (f : E ⊕ I → E' ⊕ I') (Γ : BAGraph E I) :
    (BAS3Close_rel f Γ).splitG = Γ.splitG.map (BAS3Close_rel f) := by
  unfold BAGraph.splitG
  simp only [BAS3Close_rel, BAS3Close_baSplitSolid_map, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [Function.comp, List.map_append, BAS3Close_rel]

/-- Every term of `gg2` is an extension: its `=`-dotted edges are those of `Γ`, embedded. -/
private theorem BAS3Close_gg2_dotted (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.gg2 p q, T.dotted = Γ.dotted.map (DEdge.map (owxEmb 2)) := by
  intro T hT
  unfold BAGraph.gg2 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, _, rfl⟩ <;> rfl

private theorem BAS3Close_gg4_dotted (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.gg4 p q, T.dotted = Γ.dotted.map (DEdge.map (owxEmb 4)) := by
  intro T hT
  unfold BAGraph.gg4 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, _, rfl⟩ <;> rfl

end Natural

section Cand

/-- The kids of a blue candidate are the packed partitions of the terms of `gg2` and `gg4`. -/
private theorem BAS3Close_kids_blue {P : BAPGraph (Fin 2)} (c : BARCand P) (hσ : c.σ = true) :
    c.kids = BAExpandId_outsOf P (P.g.gg2 c.p c.q) ++ BAExpandId_outsOf P (P.g.gg4 c.p c.q) := by
  simp [BARCand.kids, BAExpandId_ggL2, BAExpandId_ggL4, hσ]

/-- **The packed partitions of corresponding term lists correspond** (the engine of the iso-naturality of the kids). -/
private theorem BAS3Close_outs_iso {P Q : BAPGraph (Fin 2)} (eE : P.E' ≃ Q.E') (hext : ∀ a, eE (P.ext a) = Q.ext a)
    {I2 I2' : Type} [Fintype I2] [DecidableEq I2] [Fintype I2'] [DecidableEq I2'] (eI2 : I2 ≃ I2')
    (Ts : List (BAGraph P.E' I2)) (Ts' : List (BAGraph Q.E' I2'))
    (hT : Ts' = Ts.map (BAS3Close_rel (Equiv.sumCongr eE eI2))) (hd : ∀ T ∈ Ts, ∀ e ∈ T.dotted, e.eq = false) :
    ∀ r ∈ BAExpandId_outsOf P Ts, ∃ r' ∈ BAExpandId_outsOf Q Ts', BAS3Close_Iso r.2 r'.2 ∧ r.1 = r'.1 := by
  intro r hr
  unfold BAExpandId_outsOf at hr
  obtain ⟨T, hTm, hr⟩ := List.mem_flatMap.1 hr
  obtain ⟨Qm, hQm, rfl⟩ := List.mem_map.1 hr
  have hQm' : Qm ∈ T.splitG.map BAGraph.packMerge := hQm
  obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hQm'
  have hdΔ : ∀ e ∈ Δ.dotted, e.eq = false := by
    have := (BAGraph.splitG_edges T Δ hΔ).2.1
    rw [this]; exact hd T hTm
  set φ := Equiv.sumCongr eE eI2 with hφ
  have hT' : BAS3Close_rel φ T ∈ Ts' := by rw [hT]; exact List.mem_map_of_mem hTm
  have hΔ' : BAS3Close_rel φ Δ ∈ (BAS3Close_rel φ T).splitG := by
    rw [BAS3Close_rel_splitG]; exact List.mem_map_of_mem hΔ
  have hdΔ' : ∀ e ∈ (BAS3Close_rel φ Δ).dotted, e.eq = false := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    simpa [DEdge.map] using hdΔ e0 he0
  refine ⟨((0, 0), BAExpandId_pcomp Q (BAS3Close_rel φ Δ).packMerge), ?_, ?_, rfl⟩
  · unfold BAExpandId_outsOf
    refine List.mem_flatMap.2 ⟨BAS3Close_rel φ T, hT', List.mem_map.2 ⟨(BAS3Close_rel φ Δ).packMerge, ?_, rfl⟩⟩
    change _ ∈ (BAS3Close_rel φ T).splitG.map BAGraph.packMerge
    exact List.mem_map_of_mem hΔ'
  · -- `pcomp P (packMerge Δ) ≅ up P Δ ≅ up Q (rel φ Δ) ≅ pcomp Q (packMerge (rel φ Δ))`
    refine BAS3Close_iso_trans (BAS3Close_iso_symm (BAS3Close_iso_merge P Δ hdΔ)) ?_
    refine BAS3Close_iso_trans ?_ (BAS3Close_iso_merge Q (BAS3Close_rel φ Δ) hdΔ')
    exact ⟨eE, eI2, hext, rfl⟩

/-- The graph-level conditions of `BACtx` at `v`, `y`, `y'` (H0-H3 of `BACtx`, `Graph/BAG5Leaf.lean:108`), as a predicate of the graph and three
vertices: decidable on concrete graphs. -/
private def BAS3Close_CtxG {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (v y y' : E ⊕ I) : Prop :=
  Γ.Normal ∧ (∀ w ∈ Γ.atom v, w.isRight = true) ∧
    (Γ.solid.filter fun e => decide (e.src ∈ Γ.atom v ∨ e.dst ∈ Γ.atom v)).length = 2 ∧
    Γ.atom v ≠ Γ.atom y ∧ Γ.atom v ≠ Γ.atom y' ∧ Γ.atom y' ≠ Γ.atom y ∧
    ((∀ w ∈ Γ.atom y', w.isRight = true) ∨ (∀ w ∈ Γ.atom y, w.isRight = true))

private theorem BAS3Close_ctx_iff {P : BAPGraph (Fin 2)} (c : BARCand P) :
    BACtx c ↔ BAS3Close_CtxG P.g c.v c.p.1.dst c.q.1.src := Iff.rfl

/-- `BAS3Close_CtxG` is invariant under a renaming by a bijection that keeps external and internal vertices apart. -/
private theorem BAS3Close_ctxG_rel {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E']
    [DecidableEq E'] [Fintype I'] [DecidableEq I'] (ψ : E ⊕ I ≃ E' ⊕ I') (hψ : ∀ v, (ψ v).isRight = v.isRight)
    (Γ : BAGraph E I) (v y y' : E ⊕ I) :
    BAS3Close_CtxG (BAS3Close_rel ψ Γ) (ψ v) (ψ y) (ψ y') ↔ BAS3Close_CtxG Γ v y y' := by
  unfold BAS3Close_CtxG
  rw [BAS3Close_normal_rel, BAS3Close_atom_rel, BAS3Close_atom_rel, BAS3Close_atom_rel]
  have hmap : ∀ (A : Finset (E ⊕ I)), (∀ w ∈ A.map ψ.toEmbedding, w.isRight = true) ↔ ∀ w ∈ A, w.isRight = true := by
    intro A
    constructor
    · intro h w hw
      have := h (ψ w) (Finset.mem_map_of_mem _ hw)
      rwa [hψ] at this
    · intro h w hw
      obtain ⟨w0, hw0, rfl⟩ := Finset.mem_map.1 hw
      rw [Equiv.coe_toEmbedding, hψ]
      exact h w0 hw0
  have hlen : ((BAS3Close_rel ψ Γ).solid.filter fun e => decide (e.src ∈ (Γ.atom v).map ψ.toEmbedding ∨
      e.dst ∈ (Γ.atom v).map ψ.toEmbedding)).length =
      (Γ.solid.filter fun e => decide (e.src ∈ Γ.atom v ∨ e.dst ∈ Γ.atom v)).length := by
    simp only [BAS3Close_rel]
    rw [List.filter_map, List.length_map]
    congr 2
    funext e
    simp [SEdge.map, Finset.mem_map_equiv]
  rw [hlen, hmap, hmap, hmap]
  have hne : ∀ A B : Finset (E ⊕ I), A.map ψ.toEmbedding ≠ B.map ψ.toEmbedding ↔ A ≠ B := by
    intro A B
    rw [Ne, Ne, Finset.map_inj]
  rw [hne, hne, hne]

/-- **Iso-naturality of a blue candidate and its kids**: an isomorphism of packed graphs carries a blue candidate to a blue candidate
with the same `BACtx` status, and every kid to an isomorphic kid. -/
private theorem BAS3Close_iso_cand {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) (hdP : ∀ e ∈ P.g.dotted, e.eq = false)
    (c : BARCand P) (hσ : c.σ = true) :
    ∃ c' : BARCand Q, c'.σ = true ∧ (BACtx c' ↔ BACtx c) ∧
      ∀ r ∈ c.kids, ∃ r' ∈ c'.kids, BAS3Close_Iso r.2 r'.2 ∧ r.1 = r'.1 := by
  obtain ⟨eE, eI, hext, hg⟩ := h
  set ψ : P.E' ⊕ P.I' ≃ Q.E' ⊕ Q.I' := Equiv.sumCongr eE eI with hψ
  have hsol : Q.g.solid = P.g.solid.map (SEdge.map ψ) := by rw [hg]; rfl
  let c' : BARCand Q :=
    { σ := true
      v := ψ c.v
      p := BAS3Close_mapP ψ c.p
      q := BAS3Close_mapP ψ c.q
      hp := by rw [hsol, BAExpandId_lwSplit_map]; exact List.mem_map_of_mem c.hp
      hq := by
        have : (BAS3Close_mapP ψ c.p).2 = c.p.2.map (SEdge.map ψ) := rfl
        rw [this, BAExpandId_lwSplit_map]; exact List.mem_map_of_mem c.hq
      hpσ := c.hpσ.trans hσ
      hpc := c.hpc
      hqσ := c.hqσ.trans hσ
      hqc := c.hqc
      hpv := congrArg ψ c.hpv
      hqv := congrArg ψ c.hqv }
  refine ⟨c', rfl, ?_, ?_⟩
  · rw [BAS3Close_ctx_iff, BAS3Close_ctx_iff]
    have := BAS3Close_ctxG_rel ψ (BAS3Close_isRight_sumCongr eE eI) P.g c.v c.p.1.dst c.q.1.src
    rw [← hg] at this
    exact this
  · intro r hr
    rw [BAS3Close_kids_blue c hσ] at hr
    rw [BAS3Close_kids_blue c' rfl]
    have hl2 : BAS3Close_lift 2 ψ = (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 2))) :
        P.E' ⊕ (P.I' ⊕ Fin 2) → Q.E' ⊕ (Q.I' ⊕ Fin 2)) := funext (BAS3Close_lift_sumCongr 2 eE eI)
    have hl4 : BAS3Close_lift 4 ψ = (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 4))) :
        P.E' ⊕ (P.I' ⊕ Fin 4) → Q.E' ⊕ (Q.I' ⊕ Fin 4)) := funext (BAS3Close_lift_sumCongr 4 eE eI)
    rcases List.mem_append.1 hr with hr | hr
    · have hT : Q.g.gg2 c'.p c'.q = (P.g.gg2 c.p c.q).map
          (BAS3Close_rel (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 2))))) := by
        rw [hg, ← hl2]; exact BAS3Close_rel_gg2 ψ P.g c.p c.q
      obtain ⟨r', hr', hiso, h1⟩ := BAS3Close_outs_iso eE hext (Equiv.sumCongr eI (Equiv.refl (Fin 2)))
        (P.g.gg2 c.p c.q) (Q.g.gg2 c'.p c'.q) hT (fun T hT e he => by
          rw [BAS3Close_gg2_dotted P.g c.p c.q T hT] at he
          obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
          simpa [DEdge.map] using hdP e0 he0) r hr
      exact ⟨r', List.mem_append_left _ hr', hiso, h1⟩
    · have hT : Q.g.gg4 c'.p c'.q = (P.g.gg4 c.p c.q).map
          (BAS3Close_rel (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 4))))) := by
        rw [hg, ← hl4]; exact BAS3Close_rel_gg4 ψ P.g c.p c.q
      obtain ⟨r', hr', hiso, h1⟩ := BAS3Close_outs_iso eE hext (Equiv.sumCongr eI (Equiv.refl (Fin 4)))
        (P.g.gg4 c.p c.q) (Q.g.gg4 c'.p c'.q) hT (fun T hT e he => by
          rw [BAS3Close_gg4_dotted P.g c.p c.q T hT] at he
          obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
          simpa [DEdge.map] using hdP e0 he0) r hr
      exact ⟨r', List.mem_append_right _ hr', hiso, h1⟩

end Cand

/-! ## 4. The invariants `Even` and `Conn` (T2433a: attachment of the leaves)

`Even Γ`: every colouring of the vertices that is constant on atoms is crossed by an even number of solid edges (every set of atoms
meets an even number of solid half-edges).  `Conn Γ`: every colouring that is constant along solid edges and molecule edges is constant.
Then an internal molecule is crossed by an even and positive number of solid edges, i.e. at least two: `BAG5Attached`.  Both are kept by
every candidate step (`gg2`, `gg4`: the new edges replace `p`, `q`, ... by edges with the same boundary modulo the new `M`-dotted ties),
by the `M`-split and by renaming. -/

section Inv

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The number of solid edges whose ends receive different colours. -/
private def BAS3Close_cross {V : Type} (b : V → Bool) (es : List (SEdge V)) : ℕ :=
  (es.map fun e => if b e.src = b e.dst then 0 else 1).sum

private def BAS3Close_Even (Γ : BAGraph E I) : Prop :=
  ∀ b : E ⊕ I → Bool, (∀ u v, Γ.atomAdj u v = true → b u = b v) → BAS3Close_cross b Γ.solid % 2 = 0

private def BAS3Close_Conn (Γ : BAGraph E I) : Prop :=
  ∀ b : E ⊕ I → Bool, (∀ e ∈ Γ.solid, b e.src = b e.dst) → (∀ u v, Γ.adj u v = true → b u = b v) → ∀ u v, b u = b v

private instance BAS3Close_Even_dec (Γ : BAGraph E I) : Decidable (BAS3Close_Even Γ) := by
  unfold BAS3Close_Even
  infer_instance

private instance BAS3Close_Conn_dec (Γ : BAGraph E I) : Decidable (BAS3Close_Conn Γ) := by
  unfold BAS3Close_Conn
  infer_instance

private theorem BAS3Close_cross_append {V : Type} (b : V → Bool) (l1 l2 : List (SEdge V)) :
    BAS3Close_cross b (l1 ++ l2) = BAS3Close_cross b l1 + BAS3Close_cross b l2 := by
  simp [BAS3Close_cross, List.map_append, List.sum_append]

private theorem BAS3Close_cross_perm {V : Type} (b : V → Bool) {l1 l2 : List (SEdge V)} (h : l1.Perm l2) :
    BAS3Close_cross b l1 = BAS3Close_cross b l2 :=
  (h.map _).sum_eq

private theorem BAS3Close_cross_map {V W : Type} (f : V → W) (b : W → Bool) (l : List (SEdge V)) :
    BAS3Close_cross b (l.map (SEdge.map f)) = BAS3Close_cross (b ∘ f) l := by
  simp only [BAS3Close_cross, List.map_map, Function.comp_def, SEdge.map]
  rfl

private theorem BAS3Close_cross_map' {V W : Type} (f : V → W) (b : W → Bool) (l : List (SEdge V)) :
    BAS3Close_cross b (l.map (SEdge.map f)) = BAS3Close_cross (fun x => b (f x)) l :=
  BAS3Close_cross_map f b l

/-- `Even` is invariant under a renaming by a bijection. -/
private theorem BAS3Close_even_rel {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (ψ : E ⊕ I ≃ E' ⊕ I') (Γ : BAGraph E I) : BAS3Close_Even (BAS3Close_rel ψ Γ) ↔ BAS3Close_Even Γ := by
  constructor
  · intro h b hb
    have := h (b ∘ ψ.symm) (fun u v huv => by
      obtain ⟨u0, rfl⟩ := ψ.surjective u
      obtain ⟨v0, rfl⟩ := ψ.surjective v
      rw [BAS3Close_atomAdj_rel] at huv
      simpa using hb u0 v0 huv)
    rw [show (BAS3Close_rel ψ Γ).solid = Γ.solid.map (SEdge.map ψ) from rfl, BAS3Close_cross_map] at this
    simpa [Function.comp_def] using this
  · intro h b hb
    have := h (b ∘ ψ) (fun u v huv => hb _ _ ((BAS3Close_atomAdj_rel ψ Γ u v).symm ▸ huv))
    rw [show (BAS3Close_rel ψ Γ).solid = Γ.solid.map (SEdge.map ψ) from rfl, BAS3Close_cross_map]
    exact this

/-- `Conn` is invariant under a renaming by a bijection. -/
private theorem BAS3Close_conn_rel {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (ψ : E ⊕ I ≃ E' ⊕ I') (Γ : BAGraph E I) : BAS3Close_Conn (BAS3Close_rel ψ Γ) ↔ BAS3Close_Conn Γ := by
  constructor
  · intro h b hs ha u v
    have := h (b ∘ ψ.symm) (fun e he => by
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      simpa [SEdge.map] using hs e0 he0) (fun u v huv => by
      obtain ⟨u0, rfl⟩ := ψ.surjective u
      obtain ⟨v0, rfl⟩ := ψ.surjective v
      rw [BAS3Close_adj_rel] at huv
      simpa using ha u0 v0 huv) (ψ u) (ψ v)
    simpa using this
  · intro h b hs ha u v
    have := h (b ∘ ψ) (fun e he => hs (SEdge.map ψ e) (List.mem_map_of_mem he))
      (fun u v huv => ha _ _ ((BAS3Close_adj_rel ψ Γ u v).symm ▸ huv))
    obtain ⟨u0, rfl⟩ := ψ.surjective u
    obtain ⟨v0, rfl⟩ := ψ.surjective v
    exact this u0 v0

end Inv

section InvSplit

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAS3Close_split_cross {V : Type} (b : V → Bool) :
    ∀ (es : List (SEdge V)), ∀ r ∈ baSplitSolid es, (∀ m ∈ r.2, b m.x = b m.y) →
      BAS3Close_cross b es = BAS3Close_cross b r.1
  | [] => by
    intro r hr _
    simp only [baSplitSolid, List.mem_singleton] at hr
    subst hr; rfl
  | e :: es => by
    intro r hr hm
    simp only [baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    cases hc : e.circ
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := BAS3Close_split_cross b es r' hr' (fun m hm' => hm m hm')
        simp only [BAS3Close_cross, List.map_cons, List.sum_cons] at this ⊢
        rw [this]
      · have h1 := hm (BAMEdge.mk e.σ e.src e.dst) (List.mem_cons_self)
        have := BAS3Close_split_cross b es r' hr' (fun m hm' => hm m (List.mem_cons_of_mem _ hm'))
        simp only [BAS3Close_cross, List.map_cons, List.sum_cons] at this ⊢
        rw [this]
        simp [h1]
    · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      have := BAS3Close_split_cross b es r' hr' (fun m hm' => hm m hm')
      simp only [BAS3Close_cross, List.map_cons, List.sum_cons] at this ⊢
      rw [this]

private theorem BAS3Close_split_cover {V : Type} :
    ∀ (es : List (SEdge V)), ∀ r ∈ baSplitSolid es, ∀ e ∈ es,
      (∃ e' ∈ r.1, e'.src = e.src ∧ e'.dst = e.dst) ∨ (∃ m ∈ r.2, m.x = e.src ∧ m.y = e.dst)
  | [] => by intro r _ e he; simp at he
  | e0 :: es => by
    intro r hr e he
    simp only [baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    have ih := BAS3Close_split_cover es r' hr'
    rcases List.mem_cons.1 he with rfl | he
    · cases hc : e.circ
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Or.inl ⟨_, List.mem_cons_self, rfl, rfl⟩
        · exact Or.inr ⟨_, List.mem_cons_self, rfl, rfl⟩
      · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
        subst hr
        exact Or.inl ⟨e, List.mem_cons_self, rfl, rfl⟩
    · have h := ih e he
      cases hc : e0.circ
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rcases h with ⟨e', he', h1, h2⟩ | ⟨m, hm, h1, h2⟩
          · exact Or.inl ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩
          · exact Or.inr ⟨m, hm, h1, h2⟩
        · rcases h with ⟨e', he', h1, h2⟩ | ⟨m, hm, h1, h2⟩
          · exact Or.inl ⟨e', he', h1, h2⟩
          · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, h1, h2⟩
      · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
        subst hr
        rcases h with ⟨e', he', h1, h2⟩ | ⟨m, hm, h1, h2⟩
        · exact Or.inl ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩
        · exact Or.inr ⟨m, hm, h1, h2⟩

/-- A term of the split has the edges of the parent besides the solid ones and more `M`-dotted ones. -/
private theorem BAS3Close_split_mono (T : BAGraph E I) {Δ : BAGraph E I} (hΔ : Δ ∈ T.splitG) :
    (∀ u v, T.atomAdj u v = true → Δ.atomAdj u v = true) ∧ (∀ u v, T.adj u v = true → Δ.adj u v = true) := by
  obtain ⟨hw, hd, hp, hm⟩ := BALvl1B_splitG_struct T Δ hΔ
  have := BALvl1B_adj_mono (BAWeightOp_circ T) Δ hw.symm hd.symm hp.symm hm
  exact ⟨this.1, this.2⟩

private theorem BAS3Close_split_new {T : BAGraph E I} {Δ : BAGraph E I} (hΔ : Δ ∈ T.splitG) :
    ∃ r ∈ baSplitSolid T.solid, Δ.solid = r.1 ∧ (∀ m ∈ r.2, m ∈ Δ.mdot) := by
  simp only [BAGraph.splitG, List.mem_map] at hΔ
  obtain ⟨r, hr, rfl⟩ := hΔ
  exact ⟨r, hr, rfl, fun m hm => List.mem_append_left _ hm⟩

/-- `Even` is kept by the split. -/
private theorem BAS3Close_even_split {T : BAGraph E I} (hT : BAS3Close_Even T) {Δ : BAGraph E I} (hΔ : Δ ∈ T.splitG) :
    BAS3Close_Even Δ := by
  obtain ⟨r, hr, hs, hm⟩ := BAS3Close_split_new hΔ
  obtain ⟨hA, -⟩ := BAS3Close_split_mono T hΔ
  intro b hb
  have hbm : ∀ m ∈ r.2, b m.x = b m.y := fun m hm' => by
    refine hb _ _ ?_
    have := hm m hm'
    simp only [BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨m, this, Or.inl ⟨rfl, rfl⟩⟩
  have h1 := hT b (fun u v huv => hb u v (hA u v huv))
  rw [BAS3Close_split_cross b T.solid r hr hbm] at h1
  rw [hs]; exact h1

/-- `Conn` is kept by the split. -/
private theorem BAS3Close_conn_split {T : BAGraph E I} (hT : BAS3Close_Conn T) {Δ : BAGraph E I} (hΔ : Δ ∈ T.splitG) :
    BAS3Close_Conn Δ := by
  obtain ⟨r, hr, hs, hm⟩ := BAS3Close_split_new hΔ
  obtain ⟨-, hA⟩ := BAS3Close_split_mono T hΔ
  intro b hbs hba
  refine hT b (fun e he => ?_) (fun u v huv => hba u v ?_)
  · rcases BAS3Close_split_cover T.solid r hr e he with ⟨e', he', h1, h2⟩ | ⟨m, hm', h1, h2⟩
    · rw [← h1, ← h2]; exact hbs e' (hs ▸ he')
    · rw [← h1, ← h2]
      refine hba _ _ ?_
      have := hm m hm'
      simp only [BAGraph.adj, BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr (Or.inr ⟨m, this, Or.inl ⟨rfl, rfl⟩⟩)
  · exact hA u v huv

end InvSplit

section InvExt

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- An extension has the atom and molecule edges of the base, renamed. -/
private theorem BAS3Close_ext_adj (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (u v : E ⊕ I) (h : Γ.adj u v = true) :
    (BAGraph.ext k Γ rest s w md).adj (owxEmb k u) (owxEmb k v) = true := by
  have hA := BASim_Ext_atomAdj (BASim_Ext_ext k Γ rest s w md) u v
  simp only [BAGraph.adj, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · left
    simp only [RBM.Graph.LGraph.adj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨e, he, h2⟩ | ⟨e, he, h1, h2⟩
    · left
      refine ⟨WEdge.map (owxEmb k) e, ?_, ?_⟩
      · simp only [BAGraph.ext, LGraph.owxExt, List.mem_append, List.mem_map]
        exact Or.inl ⟨e, he, rfl⟩
      · simp only [WEdge.map]
        rcases h2 with ⟨a, b⟩ | ⟨a, b⟩
        · exact Or.inl ⟨by rw [a], by rw [b]⟩
        · exact Or.inr ⟨by rw [a], by rw [b]⟩
    · right
      refine ⟨DEdge.map (owxEmb k) e, ?_, h1, ?_⟩
      · simp only [BAGraph.ext, LGraph.owxExt, List.mem_map]
        exact ⟨e, he, rfl⟩
      · simp only [DEdge.map]
        rcases h2 with ⟨a, b⟩ | ⟨a, b⟩
        · exact Or.inl ⟨by rw [a], by rw [b]⟩
        · exact Or.inr ⟨by rw [a], by rw [b]⟩
  · exact Or.inr (hA h)

/-- The frame of the invariant `Even` for an extension: the removed edges `extra` (all of `Γ.solid` except `rest`) are replaced by `s`
with the same boundary modulo the new `M`-dotted ties `md`. -/
private theorem BAS3Close_even_ext (k : ℕ) (Γ : BAGraph E I) (extra rest : List (SEdge (E ⊕ I)))
    (hperm : Γ.solid.Perm (extra ++ rest)) (hE : BAS3Close_Even Γ)
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (hshape : ∀ b : E ⊕ (I ⊕ Fin k) → Bool, (∀ m ∈ md, b m.x = b m.y) →
      (BAS3Close_cross b s + BAS3Close_cross (fun x => b (owxEmb k x)) extra) % 2 = 0) :
    BAS3Close_Even (BAGraph.ext k Γ rest s w md) := by
  intro b' hb
  have hAc : ∀ u v, Γ.atomAdj u v = true → (fun x => b' (owxEmb k x)) u = (fun x => b' (owxEmb k x)) v := fun u v huv =>
    hb _ _ (BASim_Ext_atomAdj (BASim_Ext_ext k Γ rest s w md) u v huv)
  have hmd : ∀ m ∈ md, b' m.x = b' m.y := fun m hm => by
    refine hb _ _ ?_
    simp only [BAGraph.ext, BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨m, List.mem_append_left _ hm, Or.inl ⟨rfl, rfl⟩⟩
  have h1 := hE (fun x => b' (owxEmb k x)) hAc
  rw [BAS3Close_cross_perm _ hperm, BAS3Close_cross_append] at h1
  have h2 := hshape b' hmd
  have h3 : BAS3Close_cross b' (BAGraph.ext k Γ rest s w md).solid =
      BAS3Close_cross (fun x => b' (owxEmb k x)) rest + BAS3Close_cross b' s := by
    change BAS3Close_cross b' ((rest.map (SEdge.map (owxEmb k))) ++ s) = _
    rw [BAS3Close_cross_append, BAS3Close_cross_map']
  rw [h3]
  omega

/-- The frame of the invariant `Conn` for an extension. -/
private theorem BAS3Close_conn_ext (k : ℕ) (Γ : BAGraph E I) (extra rest : List (SEdge (E ⊕ I)))
    (hperm : Γ.solid.Perm (extra ++ rest)) (hC : BAS3Close_Conn Γ) (z : E ⊕ I)
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k))))
    (hS : ∀ b : E ⊕ (I ⊕ Fin k) → Bool, (∀ e ∈ s, b e.src = b e.dst) → (∀ m ∈ md, b m.x = b m.y) →
      (∀ e ∈ w, b e.x = b e.y) → ∀ e ∈ extra, b (owxEmb k e.src) = b (owxEmb k e.dst))
    (hN : ∀ b : E ⊕ (I ⊕ Fin k) → Bool, (∀ e ∈ s, b e.src = b e.dst) → (∀ m ∈ md, b m.x = b m.y) →
      (∀ e ∈ w, b e.x = b e.y) → ∀ i : Fin k, b (bpv i) = b (owxEmb k z)) :
    BAS3Close_Conn (BAGraph.ext k Γ rest s w md) := by
  intro b' hs ha
  have hs' : ∀ e ∈ s, b' e.src = b' e.dst := fun e he =>
    hs e (by simp only [BAGraph.ext, LGraph.owxExt, List.mem_append]; exact Or.inr he)
  have hm' : ∀ m ∈ md, b' m.x = b' m.y := fun m hm => by
    refine ha _ _ ?_
    simp only [BAGraph.adj, BAGraph.ext, BAGraph.atomAdj, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr (Or.inr ⟨m, List.mem_append_left _ hm, Or.inl ⟨rfl, rfl⟩⟩)
  have hw' : ∀ e ∈ w, b' e.x = b' e.y := fun e he => by
    refine ha _ _ ?_
    simp only [BAGraph.adj, RBM.Graph.LGraph.adj, BAGraph.ext, LGraph.owxExt, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inl ⟨e, List.mem_append_right _ he, Or.inl ⟨rfl, rfl⟩⟩)
  have hex := hS b' hs' hm' hw'
  have hconn := hC (b' ∘ owxEmb k) (fun e he => by
    have he' : e ∈ extra ++ rest := hperm.mem_iff.1 he
    rcases List.mem_append.1 he' with h | h
    · exact hex e h
    · exact hs (SEdge.map (owxEmb k) e) (by
        simp only [BAGraph.ext, LGraph.owxExt, List.mem_append, List.mem_map]
        exact Or.inl ⟨e, h, rfl⟩)) (fun u v huv => ha _ _ (BAS3Close_ext_adj k Γ rest s w md u v huv))
  have hall : ∀ u : E ⊕ (I ⊕ Fin k), b' u = b' (owxEmb k z) := by
    intro u
    rcases u with a | bb | i
    · exact hconn (Sum.inl a) z
    · exact hconn (Sum.inr bb) z
    · exact hN b' hs' hm' hw' i
  intro u v
  rw [hall u, hall v]

end InvExt

section InvShapes

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAS3Close_perm2 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) : Γ.solid.Perm ([p.1, q.1] ++ q.2) :=
  (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)

private theorem BAS3Close_perm3 (Γ : BAGraph E I) {p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hr : r ∈ lwSplit q.2) : Γ.solid.Perm ([p.1, q.1, r.1] ++ r.2) :=
  (BAS3Close_perm2 Γ hp hq).trans (((lwSplit_perm q.2 r hr).cons q.1).cons p.1)

/-- **`Even` and `Conn` for `A1`** (the `M⁺S⁺` chain `x - u - β - y, y'`) -/
private theorem BAS3Close_inv_A1 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_A1 Γ p q) ∧ BAS3Close_Conn (BAGGOp_A1 Γ p q) := by
  refine ⟨BAS3Close_even_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hE _ _ _ ?_,
    BAS3Close_conn_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    simp [h0, h1, h2, h3, h4] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · grind
    · rw [← hv]; grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for `A2` -/
private theorem BAS3Close_inv_A2 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_A2 Γ p q) ∧ BAS3Close_Conn (BAGGOp_A2 Γ p q) := by
  refine ⟨BAS3Close_even_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hE _ _ _ ?_,
    BAS3Close_conn_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    simp [h0, h1, h2, h3, h4] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · grind
    · rw [← hv]; grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for `A3` -/
private theorem BAS3Close_inv_A3 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_A3 Γ p q) ∧ BAS3Close_Conn (BAGGOp_A3 Γ p q) := by
  refine ⟨BAS3Close_even_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hE _ _ _ ?_,
    BAS3Close_conn_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    simp [h0, h1, h2, h3, h4] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · grind
    · rw [← hv]; grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for `A4` -/
private theorem BAS3Close_inv_A4 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_A4 Γ p q) ∧ BAS3Close_Conn (BAGGOp_A4 Γ p q) := by
  refine ⟨BAS3Close_even_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hE _ _ _ ?_,
    BAS3Close_conn_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    simp [h0, h1, h2, h3, h4] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · grind
    · rw [← hv]; grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for `A5` -/
private theorem BAS3Close_inv_A5 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_A5 Γ p q) ∧ BAS3Close_Conn (BAGGOp_A5 Γ p q) := by
  refine ⟨BAS3Close_even_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hE _ _ _ ?_,
    BAS3Close_conn_ext 2 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    simp [h0, h1, h2, h3, h4] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · grind
    · rw [← hv]; grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for the derivative terms `AD` -/
private theorem BAS3Close_inv_AD (Γ : BAGraph E I) {p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hr : r ∈ lwSplit q.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_AD Γ p q r) ∧ BAS3Close_Conn (BAGGOp_AD Γ p q r) := by
  refine ⟨BAS3Close_even_ext 2 Γ [p.1, q.1, r.1] r.2 (BAS3Close_perm3 Γ hp hq hr) hE _ _ _ ?_,
    BAS3Close_conn_ext 2 Γ [p.1, q.1, r.1] r.2 (BAS3Close_perm3 Γ hp hq hr) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases hσ : r.1.σ with _ | _ <;> simp only [owxDE, SEdge.map, hσ, Bool.false_eq_true, ↓reduceIte] <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 r.1.src)) with h5 | h5 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 2 r.1.dst)) with h6 | h6 <;>
    simp [h0, h1, h2, h3, h4, h5, h6] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · grind
    · rw [← hv]; grind
    · rcases hσ : r.1.σ with _ | _ <;> simp only [owxDE, SEdge.map, hσ, Bool.false_eq_true, ↓reduceIte] at hs <;> grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    rcases hσ : r.1.σ with _ | _ <;> simp only [owxDE, SEdge.map, hσ, Bool.false_eq_true, ↓reduceIte] at hs <;>
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for `B1` -/
private theorem BAS3Close_inv_B1 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_B1 Γ p q) ∧ BAS3Close_Conn (BAGGOp_B1 Γ p q) := by
  refine ⟨BAS3Close_even_ext 4 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hE _ _ _ ?_,
    BAS3Close_conn_ext 4 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 2)) with h5 | h5 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 3)) with h6 | h6 <;>
    simp [h0, h1, h2, h3, h4, h5, h6] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · grind
    · rw [← hv]; grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for `B2` -/
private theorem BAS3Close_inv_B2 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_B2 Γ p q) ∧ BAS3Close_Conn (BAGGOp_B2 Γ p q) := by
  refine ⟨BAS3Close_even_ext 4 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hE _ _ _ ?_,
    BAS3Close_conn_ext 4 Γ [p.1, q.1] q.2 (BAS3Close_perm2 Γ hp hq) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 2)) with h5 | h5 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 3)) with h6 | h6 <;>
    simp [h0, h1, h2, h3, h4, h5, h6] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · grind
    · rw [← hv]; grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    fin_cases i <;> simp <;> grind

/-- `Even`, `Conn` for the derivative terms `BD` -/
private theorem BAS3Close_inv_BD (Γ : BAGraph E I) {p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hr : r ∈ lwSplit q.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    BAS3Close_Even (BAGGOp_BD Γ p q r) ∧ BAS3Close_Conn (BAGGOp_BD Γ p q r) := by
  refine ⟨BAS3Close_even_ext 4 Γ [p.1, q.1, r.1] r.2 (BAS3Close_perm3 Γ hp hq hr) hE _ _ _ ?_,
    BAS3Close_conn_ext 4 Γ [p.1, q.1, r.1] r.2 (BAS3Close_perm3 Γ hp hq hr) hC p.1.src _ _ _ ?_ ?_⟩
  · intro b hm
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM] at hm
    simp only [BAS3Close_cross, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bpS]
    rw [← hv]
    rcases hσ : r.1.σ with _ | _ <;> simp only [owxDE, SEdge.map, hσ, Bool.false_eq_true, ↓reduceIte] <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 p.1.src)) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 p.1.dst)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 q.1.src)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 0)) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 1)) with h4 | h4 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 2)) with h5 | h5 <;>
    rcases Bool.eq_false_or_eq_true (b (bpv 3)) with h6 | h6 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 r.1.src)) with h7 | h7 <;>
    rcases Bool.eq_false_or_eq_true (b (owxEmb 4 r.1.dst)) with h8 | h8 <;>
    simp [h0, h1, h2, h3, h4, h5, h6, h7, h8] at hm ⊢
  · intro b hs hm hw e he
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · grind
    · rw [← hv]; grind
    · rcases hσ : r.1.σ with _ | _ <;> simp only [owxDE, SEdge.map, hσ, Bool.false_eq_true, ↓reduceIte] at hs <;> grind
  · intro b hs hm hw i
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, bpM,
      bpW, bpS] at hs hm hw
    rcases hσ : r.1.σ with _ | _ <;> simp only [owxDE, SEdge.map, hσ, Bool.false_eq_true, ↓reduceIte] at hs <;>
    fin_cases i <;> simp <;> grind

/-- **`Even` and `Conn` are kept by every term of `gg2`** (the nine term kinds). -/
private theorem BAS3Close_inv_gg2 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    ∀ T ∈ Γ.gg2 p q, BAS3Close_Even T ∧ BAS3Close_Conn T := by
  intro T hT
  rw [BAGGOp_gg2_eq] at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, hr, rfl⟩
  · exact BAS3Close_inv_A1 Γ hp hq hv hE hC
  · exact BAS3Close_inv_A2 Γ hp hq hv hE hC
  · exact BAS3Close_inv_A3 Γ hp hq hv hE hC
  · exact BAS3Close_inv_A4 Γ hp hq hv hE hC
  · exact BAS3Close_inv_A5 Γ hp hq hv hE hC
  · exact BAS3Close_inv_AD Γ hp hq hr hv hE hC

private theorem BAS3Close_inv_gg4 (Γ : BAGraph E I) {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hv : p.1.src = q.1.dst) (hE : BAS3Close_Even Γ) (hC : BAS3Close_Conn Γ) :
    ∀ T ∈ Γ.gg4 p q, BAS3Close_Even T ∧ BAS3Close_Conn T := by
  intro T hT
  rw [BAGGOp_gg4_eq] at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩
  · exact BAS3Close_inv_B1 Γ hp hq hv hE hC
  · exact BAS3Close_inv_B2 Γ hp hq hv hE hC
  · exact BAS3Close_inv_BD Γ hp hq hr hv hE hC

end InvShapes

section KidsInv

/-- The merge of a graph without `=`-dotted edges keeps `Even` and `Conn`. -/
private theorem BAS3Close_inv_merge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Δ : BAGraph E I)
    (hd : ∀ e ∈ Δ.dotted, e.eq = false) (hE : BAS3Close_Even Δ) (hC : BAS3Close_Conn Δ) :
    BAS3Close_Even Δ.merge ∧ BAS3Close_Conn Δ.merge := by
  have h : Δ.merge = BAS3Close_rel (Equiv.sumCongr (BAS3Close_extEquiv Δ hd) (BAS3Close_intEquiv Δ hd)) Δ := by
    rw [BAS3Close_merge_eq Δ hd]
    congr 1
    funext v
    exact BAS3Close_vmap_eq Δ hd v
  rw [h]
  exact ⟨(BAS3Close_even_rel _ Δ).2 hE, (BAS3Close_conn_rel _ Δ).2 hC⟩

/-- **`Even` and `Conn` are kept by the kids of a blue candidate.** -/
private theorem BAS3Close_kids_inv {P : BAPGraph (Fin 2)} (hdP : ∀ e ∈ P.g.dotted, e.eq = false)
    (hE : BAS3Close_Even P.g) (hC : BAS3Close_Conn P.g) (c : BARCand P) (hσ : c.σ = true) :
    ∀ r ∈ c.kids, BAS3Close_Even r.2.g ∧ BAS3Close_Conn r.2.g := by
  have hv : c.p.1.src = c.q.1.dst := c.hpv.trans c.hqv.symm
  intro r hr
  rw [BAS3Close_kids_blue c hσ] at hr
  have key : ∀ {I2 : Type} [Fintype I2] [DecidableEq I2] (Ts : List (BAGraph P.E' I2)),
      (∀ T ∈ Ts, BAS3Close_Even T ∧ BAS3Close_Conn T) → (∀ T ∈ Ts, ∀ e ∈ T.dotted, e.eq = false) →
      ∀ r ∈ BAExpandId_outsOf P Ts, BAS3Close_Even r.2.g ∧ BAS3Close_Conn r.2.g := by
    intro I2 _ _ Ts hTs hd r hr
    unfold BAExpandId_outsOf at hr
    obtain ⟨T, hTm, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨Qm, hQm, rfl⟩ := List.mem_map.1 hr
    have hQm' : Qm ∈ T.splitG.map BAGraph.packMerge := hQm
    obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hQm'
    have hdΔ : ∀ e ∈ Δ.dotted, e.eq = false := by
      have := (BAGraph.splitG_edges T Δ hΔ).2.1
      rw [this]; exact hd T hTm
    exact BAS3Close_inv_merge Δ hdΔ (BAS3Close_even_split (hTs T hTm).1 hΔ) (BAS3Close_conn_split (hTs T hTm).2 hΔ)
  rcases List.mem_append.1 hr with hr | hr
  · exact key _ (BAS3Close_inv_gg2 P.g c.hp c.hq hv hE hC) (fun T hT e he => by
      rw [BAS3Close_gg2_dotted P.g c.p c.q T hT] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      simpa [DEdge.map] using hdP e0 he0) r hr
  · exact key _ (BAS3Close_inv_gg4 P.g c.hp c.hq hv hE hC) (fun T hT e he => by
      rw [BAS3Close_gg4_dotted P.g c.p c.q T hT] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      simpa [DEdge.map] using hdP e0 he0) r hr

end KidsInv

section Attach

private theorem BAS3Close_cross_eq_length {V : Type} (b : V → Bool) (l : List (SEdge V)) (q : SEdge V → Prop) [DecidablePred q]
    (h : ∀ e ∈ l, q e ↔ b e.src ≠ b e.dst) :
    BAS3Close_cross b l = (l.filter fun e => decide (q e)).length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have ih' := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    simp only [BAS3Close_cross, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', List.filter_cons]
    by_cases hq : q e
    · have : b e.src ≠ b e.dst := he.1 hq
      simp [hq, this, add_comm]
    · have : ¬ b e.src ≠ b e.dst := fun hh => hq (he.2 hh)
      simp only [not_not] at this
      simp [hq, this]

/-- **Attachment from `Even` and `Conn`** (T2433a): an internal molecule is crossed by an even number of solid edges, and by at least one
(connectedness), hence by at least two. -/
private theorem BAS3Close_attached (P : BAPGraph (Fin 2)) (hE : BAS3Close_Even P.g) (hC : BAS3Close_Conn P.g) :
    BAG5Attached P := by
  classical
  intro v hv
  set M := P.g.mol (Sum.inr v) with hM
  let b : P.E' ⊕ P.I' → Bool := fun u => decide (u ∈ M)
  have hclosed : ∀ u w, P.g.adj u w = true → (u ∈ M ↔ w ∈ M) := by
    have hfwd : ∀ u w, P.g.adj u w = true → u ∈ M → w ∈ M := by
      intro u w huw hu
      rw [hM, BAGraph.mem_mol_iff] at hu ⊢
      exact hu.tail huw
    intro u w huw
    exact ⟨hfwd u w huw, hfwd w u (by rw [BAVocab_adj_comm]; exact huw)⟩
  have hb_adj : ∀ u w, P.g.adj u w = true → b u = b w := fun u w h => by
    simp only [b, decide_eq_decide]; exact hclosed u w h
  have hb_atom : ∀ u w, P.g.atomAdj u w = true → b u = b w := fun u w h =>
    hb_adj u w (by simp [BAGraph.adj, h])
  have hev := hE b hb_atom
  have hq : ∀ e ∈ P.g.solid, (P.g.mol e.src ≠ P.g.mol e.dst ∧ (P.g.mol e.src = M ∨ P.g.mol e.dst = M)) ↔
      b e.src ≠ b e.dst := by
    intro e _
    have hs := BAVocab_self_mem_mol P.g e.src
    have hd := BAVocab_self_mem_mol P.g e.dst
    simp only [b, ne_eq, decide_eq_decide]
    constructor
    · rintro ⟨hne, hM1 | hM1⟩
      · have h1 : e.src ∈ M := hM1 ▸ hs
        have h2 : e.dst ∉ M := fun h2 => hne (by rw [hM1]; exact (BAVocab_mol_eq_of_mem P.g h2).symm ▸ rfl)
        tauto
      · have h1 : e.dst ∈ M := hM1 ▸ hd
        have h2 : e.src ∉ M := fun h2 => hne (by rw [hM1]; exact BAVocab_mol_eq_of_mem P.g h2)
        tauto
    · intro hne
      by_cases h1 : e.src ∈ M
      · have h2 : e.dst ∉ M := fun h2 => hne (iff_of_true h1 h2)
        refine ⟨?_, Or.inl (BAVocab_mol_eq_of_mem P.g h1)⟩
        intro hh
        apply h2
        have h3 : e.dst ∈ P.g.mol e.src := hh ▸ hd
        rw [BAVocab_mol_eq_of_mem P.g h1] at h3
        exact h3
      · have h2 : e.dst ∈ M := by
          by_contra h2; exact hne (iff_of_false h1 h2)
        refine ⟨?_, Or.inr (BAVocab_mol_eq_of_mem P.g h2)⟩
        intro hh
        apply h1
        have h3 : e.src ∈ P.g.mol e.dst := hh ▸ hs
        rw [BAVocab_mol_eq_of_mem P.g h2] at h3
        exact h3
  have hlen := BAS3Close_cross_eq_length b P.g.solid
    (fun e => P.g.mol e.src ≠ P.g.mol e.dst ∧ (P.g.mol e.src = M ∨ P.g.mol e.dst = M)) hq
  unfold BAS3Close_cross at hlen hev
  have hpos : 0 < (P.g.solid.map fun e => if b e.src = b e.dst then 0 else 1).sum := by
    by_contra h0
    have h0' : (P.g.solid.map fun e => if b e.src = b e.dst then 0 else 1).sum = 0 := by omega
    rw [List.sum_eq_zero_iff] at h0'
    have hsolid : ∀ e ∈ P.g.solid, b e.src = b e.dst := by
      intro e he
      have := h0' _ (List.mem_map_of_mem he)
      by_contra hne
      simp [hne] at this
    have hconst := hC b hsolid hb_adj
    have hin : (Sum.inr v : P.E' ⊕ P.I') ∈ M := BAVocab_self_mem_mol P.g _
    have hout : (Sum.inl (P.ext 0) : P.E' ⊕ P.I') ∉ M := fun h => by simpa using hv _ h
    have := hconst (Sum.inl (P.ext 0)) (Sum.inr v)
    simp [b, hin, hout] at this
  omega

end Attach

/-! ## 5. Lemma A: the kids of a `BACtx` step from a node with the invariants -/

section LemmaA

/-- The invariants carried along the tree: normal, `n_M ≤ 1`, a waved edge, `Even`, `Conn`. -/
private abbrev BAS3Close_Inv (P : BAPGraph (Fin 2)) : Prop :=
  P.g.Normal ∧ P.g.nM ≤ 1 ∧ 1 ≤ P.g.nW ∧ BAS3Close_Even P.g ∧ BAS3Close_Conn P.g

private theorem BAS3Close_Inv.normal {P : BAPGraph (Fin 2)} (h : BAS3Close_Inv P) : P.g.Normal := h.1
private theorem BAS3Close_Inv.nM {P : BAPGraph (Fin 2)} (h : BAS3Close_Inv P) : P.g.nM ≤ 1 := h.2.1
private theorem BAS3Close_Inv.nW {P : BAPGraph (Fin 2)} (h : BAS3Close_Inv P) : 1 ≤ P.g.nW := h.2.2.1
private theorem BAS3Close_Inv.even {P : BAPGraph (Fin 2)} (h : BAS3Close_Inv P) : BAS3Close_Even P.g := h.2.2.2.1
private theorem BAS3Close_Inv.conn {P : BAPGraph (Fin 2)} (h : BAS3Close_Inv P) : BAS3Close_Conn P.g := h.2.2.2.2

private theorem BAS3Close_gg2_ext {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : ∀ T ∈ Γ.gg2 p q, BASim_Ext Γ 2 T := by
  intro T hT
  unfold BAGraph.gg2 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, _, rfl⟩ <;> exact BASim_Ext_ext _ _ _ _ _ _

private theorem BAS3Close_gg4_ext {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : ∀ T ∈ Γ.gg4 p q, BASim_Ext Γ 4 T := by
  intro T hT
  unfold BAGraph.gg4 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, _, rfl⟩ <;> exact BASim_Ext_ext _ _ _ _ _ _

/-- The waved edges of a term of `gg2`: one more than the parent. -/
private theorem BAS3Close_gg2_nW {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ Γ.gg2 p q, T.nW = Γ.nW + 1 := by
  obtain ⟨⟨-, a1, -, -⟩, h23, h45, -⟩ := gg_counters Γ p q hp hq
  intro T hT
  rw [BAGGOp_gg2_eq] at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, hr, rfl⟩
  · exact a1
  · exact (h23 _ (by simp)).2.1
  · exact (h23 _ (by simp)).2.1
  · exact congrArg Counters.nW (h45 _ (by simp))
  · exact congrArg Counters.nW (h45 _ (by simp))
  · have hmem : BAGGOp_AD Γ p q r ∈ [BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++ (lwSplit q.2).map (BAGGOp_AD Γ p q) :=
      List.mem_append_right _ (List.mem_map_of_mem hr)
    exact congrArg Counters.nW (h45 _ hmem)

private theorem BAS3Close_gg4_nW {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    {p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))} (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ Γ.gg4 p q, T.nW = Γ.nW + 2 := by
  obtain ⟨-, -, -, h4⟩ := gg_counters Γ p q hp hq
  intro T hT
  exact congrArg Counters.nW (h4 T hT)

/-- **Structure of a kid**: a split term of an extension of `P.g`, merged. -/
private theorem BAS3Close_kid_struct {P : BAPGraph (Fin 2)} (c : BARCand P) (hσ : c.σ = true) :
    ∀ r ∈ c.kids, ∃ (k : ℕ) (T Δ : BAGraph P.E' (P.I' ⊕ Fin k)), BASim_Ext P.g k T ∧ Δ ∈ T.splitG ∧
      r.2 = BAExpandId_pcomp P Δ.packMerge ∧ P.g.nW + 1 ≤ T.nW ∧ (BAWeightOp_circ T).nM ≤ P.g.nM := by
  intro r hr
  rw [BAS3Close_kids_blue c hσ] at hr
  have hmono := gg_mono P.g c.p c.q c.hp c.hq
  rcases List.mem_append.1 hr with hr | hr
  · unfold BAExpandId_outsOf at hr
    obtain ⟨T, hT, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨Qm, hQm, rfl⟩ := List.mem_map.1 hr
    have hQm' : Qm ∈ T.splitG.map BAGraph.packMerge := hQm
    obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hQm'
    exact ⟨2, T, Δ, BAS3Close_gg2_ext P.g c.p c.q T hT, hΔ, rfl,
      (BAS3Close_gg2_nW P.g c.hp c.hq T hT).ge, (hmono.1 T hT).1⟩
  · unfold BAExpandId_outsOf at hr
    obtain ⟨T, hT, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨Qm, hQm, rfl⟩ := List.mem_map.1 hr
    have hQm' : Qm ∈ T.splitG.map BAGraph.packMerge := hQm
    obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hQm'
    exact ⟨4, T, Δ, BAS3Close_gg4_ext P.g c.p c.q T hT, hΔ, rfl,
      by have := (BAS3Close_gg4_nW P.g c.hp c.hq T hT); omega, (hmono.2 T hT).1⟩

/-- **Lemma A.** The kids of a `BACtx` blue step from a node with the invariants have the invariants, one more waved edge, order at least
`ord + 1` (`baG5CtxKids_holds`), and keep `x ~ y`. -/
private theorem BAS3Close_kids_props {P : BAPGraph (Fin 2)} (hI : BAS3Close_Inv P) (c : BARCand P) (hσ : c.σ = true)
    (hc : BACtx c) :
    ∀ r ∈ c.kids, BAS3Close_Inv r.2 ∧ P.g.nW + 1 ≤ r.2.g.nW ∧ P.scalingOrder + 1 ≤ r.2.scalingOrder ∧
      ((P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1))) →
        (r.2.g.atom (Sum.inl (r.2.ext 0)) = r.2.g.atom (Sum.inl (r.2.ext 1)))) := by
  intro r hr
  obtain ⟨k, T, Δ, hExt, hΔ, hrr, hnW, hnM⟩ := BAS3Close_kid_struct c hσ r hr
  have hdΔ : ∀ e ∈ Δ.dotted, e.eq = false := by
    rw [(BAGraph.splitG_edges T Δ hΔ).2.1, hExt.1]
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    simpa [DEdge.map] using hI.normal.1 e0 he0
  have hiso : BAS3Close_Iso r.2 (BAS3Close_up P Δ) := by
    rw [hrr]; exact BAS3Close_iso_symm (BAS3Close_iso_merge P Δ hdΔ)
  have hpart := BALvl1B_part_struct P P.g hExt hI.normal Δ hΔ
  obtain ⟨-, -, hW, -, hM, -⟩ := hpart
  have hnW' : r.2.g.nW = Δ.nW := (BAS3Close_iso_nW hiso).symm
  have hnM' : r.2.g.nM = Δ.nM := (BAS3Close_iso_nM hiso).symm
  have hnWT : Δ.nW = T.nW := hW
  refine ⟨⟨c.kids_normal r hr, ?_, ?_, (BAS3Close_kids_inv hI.normal.1 hI.even hI.conn c hσ r hr).1,
    (BAS3Close_kids_inv hI.normal.1 hI.even hI.conn c hσ r hr).2⟩, ?_, baG5CtxKids_holds P c hc r hr, ?_⟩
  · rw [hnM']; exact hM.trans (hnM.trans hI.nM)
  · rw [hnW', hnWT]; omega
  · rw [hnW', hnWT]; exact hnW
  · intro hxy
    refine (BAS3Close_iso_xy hiso).1 ?_
    change Δ.atom (Sum.inl (P.ext 0)) = Δ.atom (Sum.inl (P.ext 1))
    have h1 : (Sum.inl (P.ext 1) : P.E' ⊕ P.I') ∈ P.g.atom (Sum.inl (P.ext 0)) := by
      rw [hxy]; exact BAVocab_self_mem_atom P.g _
    have h2 := BASim_Ext_sameAtom hExt h1
    simp only [BAGraph.sameAtom, decide_eq_true_eq] at h2
    have h3 : (Sum.inl (P.ext 1) : P.E' ⊕ (P.I' ⊕ Fin k)) ∈ Δ.atom (Sum.inl (P.ext 0)) := by
      rw [BAGraph.mem_atom_iff] at h2 ⊢
      exact Relation.ReflTransGen.mono (fun a b hab => (BAS3Close_split_mono T hΔ).1 a b hab) _ _ h2
    exact (BALvl1B_atom_eq_of_mem Δ h3).symm

end LemmaA

/-! ## 6. The abstract closure: from the classification of the nodes to the outputs of the expansion -/

section Closure

/-- `ord + 2·1[x ~ y]`: the target `BAG5Tgt` is `5 ≤ M`. -/
private def BAS3Close_M (P : BAPGraph (Fin 2)) : ℤ :=
  P.scalingOrder + (if P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1)) then 2 else 0)

private theorem BAS3Close_tgt_iff (P : BAPGraph (Fin 2)) : BAG5Tgt P ↔ 5 ≤ BAS3Close_M P := Iff.rfl

private theorem BAS3Close_M_kid {P Q : BAPGraph (Fin 2)} (hord : P.scalingOrder + 1 ≤ Q.scalingOrder)
    (hxy : (P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1))) →
      (Q.g.atom (Sum.inl (Q.ext 0)) = Q.g.atom (Sum.inl (Q.ext 1)))) :
    BAS3Close_M P + 1 ≤ BAS3Close_M Q := by
  unfold BAS3Close_M
  by_cases h1 : P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1))
  · have h2 := hxy h1
    simp only [h1, h2, ↓reduceIte]; omega
  · by_cases h2 : Q.g.atom (Sum.inl (Q.ext 0)) = Q.g.atom (Sum.inl (Q.ext 1))
    · simp only [h1, h2, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; omega

/-- A node with the invariants and a leaf: all five properties. -/
private theorem BAS3Close_lp_of_leaf {P : BAPGraph (Fin 2)} (hI : BAS3Close_Inv P) (hl : BAG5Leaf P) :
    BAG5LeafProps (fun _ _ => [P]) := by
  intro k s q hq
  obtain rfl := List.mem_singleton.1 hq
  exact ⟨hI.normal, hl.2.1, hl.2.2, BAS3Close_attached q hI.even hI.conn, hl.1⟩

private theorem BAS3Close_expand_none (P : BAPGraph (Fin 2)) (h : BAselStar P = none) (n : ℕ) :
    BAexpand BAselStar n P = [((0, 0), P)] := by
  cases n <;> simp [BAexpand, expandG, BAstep, h]

private theorem BAS3Close_expand_some (P : BAPGraph (Fin 2)) (c : BARCand P) (h : BAselStar P = some c) (n : ℕ) :
    BAexpand BAselStar (n + 1) P =
      c.kids.flatMap fun r => (BAexpand BAselStar n r.2).map fun t => ((r.1.1 + t.1.1, r.1.2 + t.1.2), t.2) := by
  simp [BAexpand, expandG, BAstep, h]

/-- **A leaf with the invariants is an output.** -/
private theorem BAS3Close_out_leaf {P : BAPGraph (Fin 2)} (hI : BAS3Close_Inv P) (hl : BAG5Leaf P) (n : ℕ) :
    ∀ t ∈ BAexpand BAselStar n P, BAG5LeafProps (fun _ _ => [t.2]) := by
  intro t ht
  rw [BAS3Close_expand_none P ((baselStar_eq_none_iff P).2 (Or.inl hl))] at ht
  obtain rfl := List.mem_singleton.1 ht
  exact BAS3Close_lp_of_leaf hI hl

/-- **A node at margin `≥ -1` with a blue `BACtx` candidate has leaves for kids** (Lemma A and the target). -/
private theorem BAS3Close_kids_leaf {P : BAPGraph (Fin 2)} (hI : BAS3Close_Inv P) (hm : 4 ≤ BAS3Close_M P) (c : BARCand P)
    (hσ : c.σ = true) (hc : BACtx c) : ∀ r ∈ c.kids, BAS3Close_Inv r.2 ∧ BAG5Leaf r.2 := by
  intro r hr
  obtain ⟨hI', hnW, hord, hxy⟩ := BAS3Close_kids_props hI c hσ hc r hr
  refine ⟨hI', ?_, hI'.nM, ?_⟩
  · rw [BAS3Close_tgt_iff]
    have := BAS3Close_M_kid hord hxy
    omega
  · have := hI.nW; omega

/-- **A non-leaf at margin `≥ -1` with a blue `BACtx` candidate**: every output is a leaf with the five properties. -/
private theorem BAS3Close_out_ctx {P : BAPGraph (Fin 2)} (hI : BAS3Close_Inv P) (hm : 4 ≤ BAS3Close_M P)
    (hnl : ¬ BAG5Leaf P) (hex : ∃ c : BARCand P, c.σ = true ∧ BACtx c) (n : ℕ) :
    ∀ t ∈ BAexpand BAselStar (n + 1) P, BAG5LeafProps (fun _ _ => [t.2]) := by
  intro t ht
  rcases h : BAselStar P with _ | c
  · exfalso
    rcases (baselStar_eq_none_iff P).1 h with hl | hno
    · exact hnl hl
    · exact hno hex
  · obtain ⟨-, hσ, hc⟩ := baselStar_spec P c h
    rw [BAS3Close_expand_some P c h] at ht
    obtain ⟨r, hr, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    obtain ⟨hI', hl'⟩ := BAS3Close_kids_leaf hI hm c hσ hc r hr
    exact BAS3Close_out_leaf hI' hl' n t' ht'

/-- **A node with no blue `BACtx` candidate that is not a leaf is its own output.** -/
private theorem BAS3Close_out_stuck {P : BAPGraph (Fin 2)} (hnl : ¬ BAG5Leaf P)
    (hno : ¬ ∃ c : BARCand P, c.σ = true ∧ BACtx c) (n : ℕ) : BAexpand BAselStar n P = [((0, 0), P)] :=
  BAS3Close_expand_none P ((baselStar_eq_none_iff P).2 (Or.inr hno)) n

/-- **The classification gives the outputs** (margin `≥ -1`): a leaf, a node with a candidate, or a catalogued stuck node. -/
private theorem BAS3Close_out_ge1 (Cat : BAPGraph (Fin 2) → Prop) {P : BAPGraph (Fin 2)} (hI : BAS3Close_Inv P)
    (hm : 4 ≤ BAS3Close_M P)
    (htri : BAG5Leaf P ∨ (∃ c : BARCand P, c.σ = true ∧ BACtx c) ∨ Cat P) (n : ℕ) :
    ∀ t ∈ BAexpand BAselStar (n + 1) P, BAG5LeafProps (fun _ _ => [t.2]) ∨ Cat t.2 := by
  intro t ht
  by_cases hl : BAG5Leaf P
  · exact Or.inl (BAS3Close_out_leaf hI hl _ t ht)
  · by_cases hex : ∃ c : BARCand P, c.σ = true ∧ BACtx c
    · exact Or.inl (BAS3Close_out_ctx hI hm hl hex n t ht)
    · rw [BAS3Close_out_stuck hl hex] at ht
      obtain rfl := List.mem_singleton.1 ht
      rcases htri with h | h | h
      · exact absurd h hl
      · exact absurd h hex
      · exact Or.inr h

/-- **Margin `-2` at the root**: a node of margin `≥ -2` with a blue `BACtx` candidate whose kids are all classified. -/
private theorem BAS3Close_out_ord3 (Cat : BAPGraph (Fin 2) → Prop) {P : BAPGraph (Fin 2)} (hI : BAS3Close_Inv P)
    (hm : 3 ≤ BAS3Close_M P) (hnl : ¬ BAG5Leaf P) (hex : ∃ c : BARCand P, c.σ = true ∧ BACtx c)
    (hkids : ∀ c : BARCand P, c.σ = true → BACtx c → ∀ r ∈ c.kids,
      BAG5Leaf r.2 ∨ (∃ c' : BARCand r.2, c'.σ = true ∧ BACtx c') ∨ Cat r.2) :
    ∀ t ∈ BAexpand BAselStar 2 P, BAG5LeafProps (fun _ _ => [t.2]) ∨ Cat t.2 := by
  intro t ht
  rcases h : BAselStar P with _ | c
  · exfalso
    rcases (baselStar_eq_none_iff P).1 h with hl | hno
    · exact hnl hl
    · exact hno hex
  · obtain ⟨-, hσ, hc⟩ := baselStar_spec P c h
    rw [BAS3Close_expand_some P c h] at ht
    obtain ⟨r, hr, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    obtain ⟨hI', hnW, hord, hxy⟩ := BAS3Close_kids_props hI c hσ hc r hr
    have hm' : 4 ≤ BAS3Close_M r.2 := by
      have := BAS3Close_M_kid hord hxy
      omega
    exact BAS3Close_out_ge1 Cat hI' hm' (hkids c hσ hc r hr) 0 t' ht'

end Closure

/-! ## 7. Concrete graphs: the trivial pack, the root terms, the classification of the kids -/

section Conc

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The trivial pack of a concrete graph (external vertices `Fin 2`, `ext = id`). -/
private def BAS3Close_pk (Γ : BAGraph (Fin 2) I) : BAPGraph (Fin 2) :=
  { E' := Fin 2, I' := I, ext := id, ext_surj := Function.surjective_id, g := Γ }

/-- The empty base: `pcomp base (packMerge Γ) = packMerge Γ`. -/
private def BAS3Close_base : BAPGraph (Fin 2) :=
  { E' := Fin 2, I' := Fin 0, ext := id, ext_surj := Function.surjective_id,
    g := { solid := [], waved := [], dotted := [], coeff := 1, psi := [], mdot := [] } }

/-- **A root term is its trivial pack** (up to isomorphism). -/
private theorem BAS3Close_iso_root (Γ : BAGraph (Fin 2) I) (hd : ∀ e ∈ Γ.dotted, e.eq = false) :
    BAS3Close_Iso (BAS3Close_pk Γ) Γ.packMerge :=
  BAS3Close_iso_merge BAS3Close_base Γ hd

private def BAS3Close_MC (Γ : BAGraph (Fin 2) I) : ℤ :=
  Γ.scalingOrder + (if Γ.atom (Sum.inl 0) = Γ.atom (Sum.inl 1) then 2 else 0)

/-- The leaf conditions on a concrete graph. -/
private def BAS3Close_LeafC (Γ : BAGraph (Fin 2) I) : Prop := 5 ≤ BAS3Close_MC Γ ∧ Γ.nM ≤ 1 ∧ 2 ≤ Γ.nW

private theorem BAS3Close_leaf_pk (Γ : BAGraph (Fin 2) I) : BAG5Leaf (BAS3Close_pk Γ) ↔ BAS3Close_LeafC Γ := Iff.rfl

/-- The invariants on a concrete graph. -/
private def BAS3Close_InvC (Γ : BAGraph (Fin 2) I) : Prop :=
  Γ.Normal ∧ Γ.nM ≤ 1 ∧ 1 ≤ Γ.nW ∧ BAS3Close_Even Γ ∧ BAS3Close_Conn Γ

private theorem BAS3Close_inv_pk {Γ : BAGraph (Fin 2) I} (h : BAS3Close_InvC Γ) : BAS3Close_Inv (BAS3Close_pk Γ) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The invariants pass along an isomorphism. -/
private theorem BAS3Close_inv_iso {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) (hQ : BAS3Close_Inv Q) : BAS3Close_Inv P := by
  have hn := BAS3Close_iso_normal h
  have hM := BAS3Close_iso_nM h
  have hW := BAS3Close_iso_nW h
  obtain ⟨eE, eI, hext, hg⟩ := h
  refine ⟨hn.1 hQ.normal, ?_, ?_, ?_, ?_⟩
  · rw [← hM]; exact hQ.nM
  · rw [← hW]; exact hQ.nW
  · have := hQ.even; rw [hg] at this; exact (BAS3Close_even_rel _ _).1 this
  · have := hQ.conn; rw [hg] at this; exact (BAS3Close_conn_rel _ _).1 this

/-- The concrete form of a blue `BACtx` candidate. -/
private def BAS3Close_CandC (Γ : BAGraph (Fin 2) I) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) : Prop :=
  p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true ∧ p.1.src = q.1.dst ∧
    BAS3Close_CtxG Γ p.1.src p.1.dst q.1.src

/-- The existence of a blue `BACtx` candidate on a concrete graph. -/
private def BAS3Close_CtxExD (Γ : BAGraph (Fin 2) I) : Prop :=
  ∃ p ∈ lwSplit Γ.solid, ∃ q ∈ lwSplit p.2, BAS3Close_CandC Γ p q

/-- A blue candidate of a trivial pack is concrete candidate data with the `BACtx` conditions, and conversely. -/
private theorem BAS3Close_ctxEx_pk (Γ : BAGraph (Fin 2) I) :
    BAS3Close_CtxExD Γ ↔ ∃ c : BARCand (BAS3Close_pk Γ), c.σ = true ∧ BACtx c := by
  constructor
  · rintro ⟨p, hp, q, hq, h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨true, p.1.src, p, q, hp, hq, h1, h2, h3, h4, rfl, h5.symm⟩, rfl, h6⟩
  · rintro ⟨c, hσ, hc⟩
    refine ⟨c.p, c.hp, c.q, c.hq, c.hpσ.trans hσ, c.hpc, c.hqσ.trans hσ, c.hqc, c.hpv.trans c.hqv.symm, ?_⟩
    have : c.v = c.p.1.src := c.hpv.symm
    rw [BAS3Close_ctx_iff, this] at hc
    exact hc

/-- The packed terms of `gg2` and `gg4` of a concrete graph. -/
private def BAS3Close_Kids2 (Γ : BAGraph (Fin 2) I) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) :
    List (BAGraph (Fin 2) (I ⊕ Fin 2)) := (Γ.gg2 p q).flatMap BAGraph.splitG

private def BAS3Close_Kids4 (Γ : BAGraph (Fin 2) I) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) :
    List (BAGraph (Fin 2) (I ⊕ Fin 4)) := (Γ.gg4 p q).flatMap BAGraph.splitG

/-- **The kids of a blue candidate of a trivial pack are the trivial packs of the terms of the split lists.** -/
private theorem BAS3Close_kids_pk (Γ : BAGraph (Fin 2) I) (hd : ∀ e ∈ Γ.dotted, e.eq = false) (c : BARCand (BAS3Close_pk Γ))
    (hσ : c.σ = true) :
    ∀ r ∈ c.kids, (∃ Δ ∈ BAS3Close_Kids2 Γ c.p c.q, BAS3Close_Iso r.2 (BAS3Close_pk Δ)) ∨
      (∃ Δ ∈ BAS3Close_Kids4 Γ c.p c.q, BAS3Close_Iso r.2 (BAS3Close_pk Δ)) := by
  intro r hr
  rw [BAS3Close_kids_blue c hσ] at hr
  rcases List.mem_append.1 hr with hr | hr
  · left
    unfold BAExpandId_outsOf at hr
    obtain ⟨T, hT, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨Qm, hQm, rfl⟩ := List.mem_map.1 hr
    have hQm' : Qm ∈ T.splitG.map BAGraph.packMerge := hQm
    obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hQm'
    have hdΔ : ∀ e ∈ Δ.dotted, e.eq = false := by
      rw [(BAGraph.splitG_edges T Δ hΔ).2.1, BAS3Close_gg2_dotted _ c.p c.q T hT]
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      simpa [DEdge.map] using hd e0 he0
    exact ⟨Δ, List.mem_flatMap.2 ⟨T, hT, hΔ⟩, BAS3Close_iso_symm (BAS3Close_iso_merge (BAS3Close_pk Γ) Δ hdΔ)⟩
  · right
    unfold BAExpandId_outsOf at hr
    obtain ⟨T, hT, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨Qm, hQm, rfl⟩ := List.mem_map.1 hr
    have hQm' : Qm ∈ T.splitG.map BAGraph.packMerge := hQm
    obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hQm'
    have hdΔ : ∀ e ∈ Δ.dotted, e.eq = false := by
      rw [(BAGraph.splitG_edges T Δ hΔ).2.1, BAS3Close_gg4_dotted _ c.p c.q T hT]
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      simpa [DEdge.map] using hd e0 he0
    exact ⟨Δ, List.mem_flatMap.2 ⟨T, hT, hΔ⟩, BAS3Close_iso_symm (BAS3Close_iso_merge (BAS3Close_pk Γ) Δ hdΔ)⟩

/-- The dotted edges of the terms of the split lists have no `=` edge (if the graph has none). -/
private theorem BAS3Close_kids_dotted2 (Γ : BAGraph (Fin 2) I) (hd : ∀ e ∈ Γ.dotted, e.eq = false)
    (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) : ∀ Δ ∈ BAS3Close_Kids2 Γ p q, ∀ e ∈ Δ.dotted, e.eq = false := by
  intro Δ hΔ
  obtain ⟨T, hT, hΔ⟩ := List.mem_flatMap.1 hΔ
  rw [(BAGraph.splitG_edges T Δ hΔ).2.1, BAS3Close_gg2_dotted _ p q T hT]
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  simpa [DEdge.map] using hd e0 he0

private theorem BAS3Close_kids_dotted4 (Γ : BAGraph (Fin 2) I) (hd : ∀ e ∈ Γ.dotted, e.eq = false)
    (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) : ∀ Δ ∈ BAS3Close_Kids4 Γ p q, ∀ e ∈ Δ.dotted, e.eq = false := by
  intro Δ hΔ
  obtain ⟨T, hT, hΔ⟩ := List.mem_flatMap.1 hΔ
  rw [(BAGraph.splitG_edges T Δ hΔ).2.1, BAS3Close_gg4_dotted _ p q T hT]
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  simpa [DEdge.map] using hd e0 he0

/-- The coefficients of the terms of the split lists are that of the graph (`1 * coeff`). -/
private theorem BAS3Close_kids_coeff2 (Γ : BAGraph (Fin 2) I) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) :
    ∀ Δ ∈ BAS3Close_Kids2 Γ p q, Δ.coeff = Γ.coeff := by
  intro Δ hΔ
  obtain ⟨T, hT, hΔ⟩ := List.mem_flatMap.1 hΔ
  simp only [BAGraph.splitG, List.mem_map] at hΔ
  obtain ⟨r, -, rfl⟩ := hΔ
  unfold BAGraph.gg2 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r', _, rfl⟩ <;> simp [BAGraph.ext, LGraph.owxExt]

private theorem BAS3Close_kids_coeff4 (Γ : BAGraph (Fin 2) I) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) :
    ∀ Δ ∈ BAS3Close_Kids4 Γ p q, Δ.coeff = Γ.coeff := by
  intro Δ hΔ
  obtain ⟨T, hT, hΔ⟩ := List.mem_flatMap.1 hΔ
  simp only [BAGraph.splitG, List.mem_map] at hΔ
  obtain ⟨r, -, rfl⟩ := hΔ
  unfold BAGraph.gg4 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r', _, rfl⟩ <;> simp [BAGraph.ext, LGraph.owxExt]

end Conc

section RootThm

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem BAS3Close_M_iso {P Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso P Q) : BAS3Close_M Q = BAS3Close_M P := by
  have hxy := BAS3Close_iso_xy h
  have ho := BAS3Close_iso_order h
  unfold BAS3Close_M
  rw [ho]
  by_cases hx : P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1))
  · simp [hx, hxy.2 hx]
  · have hx' : ¬ (Q.g.atom (Sum.inl (Q.ext 0)) = Q.g.atom (Sum.inl (Q.ext 1))) := fun hh => hx (hxy.1 hh)
    simp [hx, hx']

/-- **Classification transfer**: a node isomorphic to the trivial pack of `Δ` is a leaf, has a blue `BACtx` candidate, or is catalogued,
as soon as `Δ` is. -/
private theorem BAS3Close_tri_sound (Cat : BAPGraph (Fin 2) → Prop)
    (hCatIso : ∀ Q Q' : BAPGraph (Fin 2), BAS3Close_Iso Q Q' → Cat Q' → Cat Q)
    {J : Type} [Fintype J] [DecidableEq J] (Δ : BAGraph (Fin 2) J) (hdΔ : ∀ e ∈ Δ.dotted, e.eq = false)
    {Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso Q (BAS3Close_pk Δ))
    (htri : BAS3Close_LeafC Δ ∨ BAS3Close_CtxExD Δ ∨ Cat (BAS3Close_pk Δ)) :
    BAG5Leaf Q ∨ (∃ c : BARCand Q, c.σ = true ∧ BACtx c) ∨ Cat Q := by
  rcases htri with hl | hex | hc
  · exact Or.inl ((BAS3Close_iso_leaf h).1 ((BAS3Close_leaf_pk Δ).2 hl))
  · right; left
    obtain ⟨c, hσ, hctx⟩ := (BAS3Close_ctxEx_pk Δ).1 hex
    obtain ⟨c', hσ', hctx', -⟩ := BAS3Close_iso_cand (BAS3Close_iso_symm h) hdΔ c hσ
    exact ⟨c', hσ', hctx'.2 hctx⟩
  · exact Or.inr (Or.inr (hCatIso Q _ h hc))

/-- The target alone (the other two leaf conditions of a kid come from Lemma A). -/
private def BAS3Close_LeafT (Γ : BAGraph (Fin 2) I) : Prop := 5 ≤ BAS3Close_MC Γ

/-- **Classification transfer for a kid** (`n_M ≤ 1` and `2 ≤ n_W` are given by Lemma A). -/
private theorem BAS3Close_tri_sound_kid (Cat : BAPGraph (Fin 2) → Prop)
    (hCatIso : ∀ Q Q' : BAPGraph (Fin 2), BAS3Close_Iso Q Q' → Cat Q' → Cat Q)
    {J : Type} [Fintype J] [DecidableEq J] (Δ : BAGraph (Fin 2) J) (hdΔ : ∀ e ∈ Δ.dotted, e.eq = false)
    {Q : BAPGraph (Fin 2)} (h : BAS3Close_Iso Q (BAS3Close_pk Δ)) (hM : Q.g.nM ≤ 1) (hW : 2 ≤ Q.g.nW)
    (htri : BAS3Close_LeafT Δ ∨ BAS3Close_CtxExD Δ ∨ Cat (BAS3Close_pk Δ)) :
    BAG5Leaf Q ∨ (∃ c : BARCand Q, c.σ = true ∧ BACtx c) ∨ Cat Q := by
  rcases htri with hl | hex | hc
  · refine Or.inl ?_
    have : BAG5Leaf (BAS3Close_pk Δ) ↔ BAS3Close_LeafC Δ := BAS3Close_leaf_pk Δ
    have hT : BAG5Tgt (BAS3Close_pk Δ) := hl
    exact ((BAS3Close_iso_leaf h).1 ⟨hT, by rw [← BAS3Close_iso_nM h] at hM; exact hM,
      by rw [← BAS3Close_iso_nW h] at hW; exact hW⟩)
  · right; left
    obtain ⟨c, hσ, hctx⟩ := (BAS3Close_ctxEx_pk Δ).1 hex
    obtain ⟨c', hσ', hctx', -⟩ := BAS3Close_iso_cand (BAS3Close_iso_symm h) hdΔ c hσ
    exact ⟨c', hσ', hctx'.2 hctx⟩
  · exact Or.inr (Or.inr (hCatIso Q _ h hc))

/-- **A root term at margin `≥ -1`.** -/
private theorem BAS3Close_root_ge1 (Cat : BAPGraph (Fin 2) → Prop)
    (hCatIso : ∀ Q Q' : BAPGraph (Fin 2), BAS3Close_Iso Q Q' → Cat Q' → Cat Q)
    (Γ : BAGraph (Fin 2) I) (hd : ∀ e ∈ Γ.dotted, e.eq = false) (hI : BAS3Close_InvC Γ) (hm : 4 ≤ BAS3Close_MC Γ)
    (htri : BAS3Close_LeafC Γ ∨ BAS3Close_CtxExD Γ ∨ Cat (BAS3Close_pk Γ)) (n : ℕ) :
    ∀ t ∈ BAexpand BAselStar (n + 1) Γ.packMerge, BAG5LeafProps (fun _ _ => [t.2]) ∨ Cat t.2 := by
  have h := BAS3Close_iso_root Γ hd
  have hI' : BAS3Close_Inv Γ.packMerge := BAS3Close_inv_iso (BAS3Close_iso_symm h) (BAS3Close_inv_pk hI)
  have hm' : 4 ≤ BAS3Close_M Γ.packMerge := by
    rw [BAS3Close_M_iso h]; exact hm
  exact BAS3Close_out_ge1 Cat hI' hm' (BAS3Close_tri_sound Cat hCatIso Γ hd (BAS3Close_iso_symm h) htri) n

/-- **A root term at margin `-2`** (the order-`3` term): every blue `BACtx` candidate has classified kids. -/
private theorem BAS3Close_root_ord3 (Cat : BAPGraph (Fin 2) → Prop)
    (hCatIso : ∀ Q Q' : BAPGraph (Fin 2), BAS3Close_Iso Q Q' → Cat Q' → Cat Q)
    (Tri2 : BAGraph (Fin 2) (I ⊕ Fin 2) → Prop) (Tri4 : BAGraph (Fin 2) (I ⊕ Fin 4) → Prop)
    (Γ : BAGraph (Fin 2) I)
    (hT2 : ∀ p q, ∀ Δ ∈ BAS3Close_Kids2 Γ p q, Tri2 Δ → BAS3Close_LeafT Δ ∨ BAS3Close_CtxExD Δ ∨ Cat (BAS3Close_pk Δ))
    (hT4 : ∀ p q, ∀ Δ ∈ BAS3Close_Kids4 Γ p q, Tri4 Δ → BAS3Close_LeafT Δ ∨ BAS3Close_CtxExD Δ ∨ Cat (BAS3Close_pk Δ)) (hd : ∀ e ∈ Γ.dotted, e.eq = false) (hI : BAS3Close_InvC Γ) (hm : 3 ≤ BAS3Close_MC Γ)
    (hex : BAS3Close_CtxExD Γ)
    (hkids : ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, BAS3Close_CandC Γ p q →
      (∀ Δ ∈ BAS3Close_Kids2 Γ p q, Tri2 Δ) ∧ (∀ Δ ∈ BAS3Close_Kids4 Γ p q, Tri4 Δ)) :
    ∀ t ∈ BAexpand BAselStar 2 Γ.packMerge, BAG5LeafProps (fun _ _ => [t.2]) ∨ Cat t.2 := by
  have h := BAS3Close_iso_root Γ hd
  have hI' : BAS3Close_Inv Γ.packMerge := BAS3Close_inv_iso (BAS3Close_iso_symm h) (BAS3Close_inv_pk hI)
  have hm' : 3 ≤ BAS3Close_M Γ.packMerge := by
    rw [BAS3Close_M_iso h]; exact hm
  by_cases hl : BAG5Leaf Γ.packMerge
  · intro t ht
    exact Or.inl (BAS3Close_out_leaf hI' hl 2 t ht)
  have hnl' : ¬ BAG5Leaf Γ.packMerge := hl
  have hex' : ∃ c : BARCand Γ.packMerge, c.σ = true ∧ BACtx c := by
    obtain ⟨c, hσ, hctx⟩ := (BAS3Close_ctxEx_pk Γ).1 hex
    obtain ⟨c', hσ', hctx', -⟩ := BAS3Close_iso_cand h hd c hσ
    exact ⟨c', hσ', hctx'.2 hctx⟩
  refine BAS3Close_out_ord3 Cat hI' hm' hnl' hex' ?_
  intro c hσ hc r hr
  have hdP : ∀ e ∈ Γ.packMerge.g.dotted, e.eq = false := BAVocab_merge_dotted_eq Γ
  obtain ⟨c0, hσ0, hctx0, hk0⟩ := BAS3Close_iso_cand (BAS3Close_iso_symm h) hdP c hσ
  have hc0 : BACtx c0 := hctx0.2 hc
  obtain ⟨r0, hr0, hiso, -⟩ := hk0 r hr
  have hcand : BAS3Close_CandC Γ c0.p c0.q := by
    refine ⟨c0.hpσ.trans hσ0, c0.hpc, c0.hqσ.trans hσ0, c0.hqc, c0.hpv.trans c0.hqv.symm, ?_⟩
    have hv : c0.v = c0.p.1.src := c0.hpv.symm
    rw [BAS3Close_ctx_iff, hv] at hc0
    exact hc0
  obtain ⟨hk2, hk4⟩ := hkids c0.p c0.hp c0.q c0.hq hcand
  obtain ⟨hIr, hnWr, -, -⟩ := BAS3Close_kids_props hI' c hσ hc r hr
  have hW2 : 2 ≤ r.2.g.nW := by have := hI'.nW; omega
  rcases BAS3Close_kids_pk Γ hd c0 hσ0 r0 hr0 with ⟨Δ, hΔ, hisoΔ⟩ | ⟨Δ, hΔ, hisoΔ⟩
  · exact BAS3Close_tri_sound_kid Cat hCatIso Δ (BAS3Close_kids_dotted2 Γ hd _ _ Δ hΔ)
      (BAS3Close_iso_trans hiso hisoΔ) hIr.nM hW2 (hT2 c0.p c0.q Δ hΔ (hk2 Δ hΔ))
  · exact BAS3Close_tri_sound_kid Cat hCatIso Δ (BAS3Close_kids_dotted4 Γ hd _ _ Δ hΔ)
      (BAS3Close_iso_trans hiso hisoΔ) hIr.nM hW2 (hT4 c0.p c0.q Δ hΔ (hk4 Δ hΔ))

end RootThm

end RBM.Graph

end
