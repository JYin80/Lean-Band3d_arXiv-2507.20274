/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAEngine
import RBM3D.Graph.BAAtom
import RBM3D.Graph.LWProv

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

/-!
# The BA provenance engine, part 1

Paper: Lemma 7.2 (`lem:LW_moment_exp`) and its proof (Subsection 7.5, the domains `D_{>ℓ}`,
`D_{≤ℓ}`); Subappendix B.3 (the proof of Lemma B.7).  This is the BA counterpart of
`Graph/LWProv.lean` (Sections 1-4), namespace `RBM.Graph`, private stem `BAProv_`.

## Contents

1. Weighted values: `BAGraph.valW`, `BAPGraph.valW`, `_one`, `_of_factor`, `_of_not`.
2. Provenance outputs: `BAProvOut`, `ExtOK`, `Molecular`, `comp`, `BACoverBy`.
3. The weighted expansion `BAWExp` at `BAlwData`: `.refl`, `.comp`, `.prod`.
4. Molecular maps: the extension lemma on the shadow, the five frame kinds, the twist, `splitG`,
   `merge`, `outsOf`, the start terms.
5. The weighted partition.
6. The domain form of `f_xy` and the bridge.

Shadow molecules: a molecule of a BA graph is a connected component of `BAGraph.shadow` (waved,
`=`-, `Ψ`- and `M`-dotted edges join, `Graph/BAAtom.lean`).
-/

open private BAVocab_merge_adj BAVocab_vmap_surjective BAVocab_term_merge BAVocab_term_zero BAVocab_good_eq_of_cls BAVocab_exists_inr_of_int
  BAVocab_vmap_inr_int BAVocab_vmap_inr_ext BAVocab_split_val from RBM3D.Graph.BAVocab
open private BAWeightOp_ext_adj from RBM3D.Graph.BAWeightOp

noncomputable section
open MeasureTheory RBM RBM.Gauss RBM.BA

namespace RBM.Graph

/-! ## 1. Weighted values -/

/-- the value of a BA graph with a **real weight on the labellings of all its vertices** (as `valW` in `Graph/LWProv.lean`; the weight `1` is `BAGraph.val`) -/
def BAGraph.valW {ι E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι)
    (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) : ℂ :=
  ∑ ℓi : I → ι, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)

/-- the weighted value of a packed BA graph (as `pvalW` in `Graph/LWProv.lean`; the packing literal of `BAPGraph.val`, `Graph/BAVocab.lean`) -/
def BAPGraph.valW {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (D : BALData ι) (Wt : (P.E' ⊕ P.I' → ι) → ℝ)
    (ℓe : E → ι) : ℂ :=
  letI := P.instFI
  letI := P.instDI
  open Classical in
  if h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext then P.g.valW D Wt h.choose else 0

theorem BAGraph.valW_one {ι E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι)
    (ℓe : E → ι) : Γ.valW D (fun _ => 1) ℓe = Γ.val D ℓe := by simp [BAGraph.valW, BAGraph.val]

theorem BAPGraph.valW_one {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (D : BALData ι) (ℓe : E → ι) :
    P.valW D (fun _ => 1) ℓe = P.val D ℓe := by
  unfold BAPGraph.valW BAPGraph.val
  split_ifs <;> simp [BAGraph.valW_one]

theorem BAPGraph.valW_of_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (D : BALData ι)
    (Wt : (P.E' ⊕ P.I' → ι) → ℝ) {ℓe : E → ι} {ℓ' : P.E' → ι} (h : ℓe = ℓ' ∘ P.ext) : P.valW D Wt ℓe = P.g.valW D Wt ℓ' := by
  classical
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', h⟩
  simp only [BAPGraph.valW, hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans h

theorem BAPGraph.valW_of_not {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (D : BALData ι)
    (Wt : (P.E' ⊕ P.I' → ι) → ℝ) {ℓe : E → ι} (h : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : P.valW D Wt ℓe = 0 := by
  classical
  simp only [BAPGraph.valW, h, ↓reduceDIte]

/-! ## 2. Provenance outputs -/

/-- an output `Q` of a step from `P`, with its **provenance map** `π` (old vertex ↦ vertex of the output); no tags (`ProvOutX` has no BA counterpart) -/
structure BAProvOut (P : BAPGraph (Fin 2)) where
  Q : BAPGraph (Fin 2)
  π : P.E' ⊕ P.I' → Q.E' ⊕ Q.I'

/-- the external vertices go to the external vertices -/
def BAProvOut.ExtOK {P : BAPGraph (Fin 2)} (o : BAProvOut P) : Prop := ∀ i : Fin 2, o.π (Sum.inl (P.ext i)) = Sum.inl (o.Q.ext i)

/-- `π` is **molecular** on the shadow: a molecule goes into a molecule, and every internal molecule of the output is the image of an internal molecule
of the input (no new molecule: every new vertex is joined to an old one, the joining edges of the input are kept) -/
def BAProvOut.Molecular {P : BAPGraph (Fin 2)} (o : BAProvOut P) : Prop :=
  (∀ v w, P.g.shadow.molOf v = P.g.shadow.molOf w → o.Q.g.shadow.molOf (o.π v) = o.Q.g.shadow.molOf (o.π w)) ∧
    ∀ c : o.Q.g.shadow.Mol, ¬ o.Q.g.shadow.IsExtMol c → ∃ v, ¬ P.g.shadow.IsExtMol (P.g.shadow.molOf v) ∧ o.Q.g.shadow.molOf (o.π v) = c

def BAProvOut.comp {P : BAPGraph (Fin 2)} (o : BAProvOut P) (o' : BAProvOut o.Q) : BAProvOut P := ⟨o'.Q, o'.π ∘ o.π⟩

theorem BAProvOut.Molecular.comp {P : BAPGraph (Fin 2)} {o : BAProvOut P} {o' : BAProvOut o.Q} (h : o.Molecular) (h' : o'.Molecular) :
    (o.comp o').Molecular := by
  refine ⟨fun v w hvw => h'.1 _ _ (h.1 v w hvw), fun c hc => ?_⟩
  obtain ⟨v', hv', hc'⟩ := h'.2 c hc
  obtain ⟨v, hv, hvv⟩ := h.2 _ hv'
  exact ⟨v, hv, (h'.1 _ _ hvv).trans hc'⟩

theorem BAProvOut.ExtOK.comp {P : BAPGraph (Fin 2)} {o : BAProvOut P} {o' : BAProvOut o.Q} (h : o.ExtOK) (h' : o'.ExtOK) :
    (o.comp o').ExtOK := fun i => by
  change o'.π (o.π (Sum.inl (P.ext i))) = _
  rw [h i, h' i]
  rfl

/-- every internal molecule of `P` (on the shadow) contains a vertex of the family `β` -/
def BACoverBy {P : BAPGraph (Fin 2)} {κ : Type} (β : κ → P.E' ⊕ P.I') : Prop :=
  ∀ c : LGraph.AuxIMol P.g.shadow, ∃ k, P.g.shadow.molOf (β k) = c.1

/-- **molecule coverage propagates** (as `CoverBy.comp` in `Graph/LWProv.lean`): the images of the initial `β^{(k)}` cover the internal molecules of every output -/
theorem BACoverBy.comp {P : BAPGraph (Fin 2)} {κ : Type} {β : κ → P.E' ⊕ P.I'} (h : BACoverBy β) {o : BAProvOut P} (ho : o.Molecular) :
    BACoverBy (P := o.Q) (fun k => o.π (β k)) := by
  rintro ⟨c, hc⟩
  obtain ⟨v, hv, hvc⟩ := ho.2 c hc
  obtain ⟨k, hk⟩ := h ⟨_, hv⟩
  exact ⟨k, (ho.1 _ _ hk).trans hvc⟩

/-- the roots read from the coverage (as `lwMomentExp_rep` in `Graph/LWMomentExp.lean`): a vertex of the family `β` in every internal molecule -/
theorem BACoverBy.rep {P : BAPGraph (Fin 2)} {κ : Type} {β : κ → P.E' ⊕ P.I'} (h : BACoverBy β) :
    ∃ (rep : LGraph.AuxIMol P.g.shadow → P.I') (k : LGraph.AuxIMol P.g.shadow → κ), ∀ c, β (k c) = Sum.inr (rep c) ∧ P.g.shadow.molOf (Sum.inr (rep c)) = c.1 := by
  have hex : ∀ c : LGraph.AuxIMol P.g.shadow, ∃ (i : P.I') (k : κ), β k = Sum.inr i ∧ P.g.shadow.molOf (Sum.inr i) = c.1 := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := h ⟨c, hc⟩
    rcases hβ : β k with a | i
    · exact absurd ⟨a, by simpa [hβ] using hk⟩ hc
    · exact ⟨i, k, hβ, by simpa [hβ] using hk⟩
  choose rep k hk hrep using hex
  exact ⟨rep, k, fun c => ⟨hk c, hrep c⟩⟩

/-! ## 3. The weighted expansion -/

/-- **weighted expansion** at the BA data `BAlwData` and the flow law `PF d L W 0`: for every real weight `Wt` on the labellings of the vertices of `P`, the expectation of the weighted
value of `P` is the sum over the outputs of the expectations of their weighted values, the weight read through `π`.  Data hypotheses `3 ≤ L`, `BASelf d L g0 Em m`, `0 ≤ t < 1` only. -/
def BAWExp (d : ℕ) (P : BAPGraph (Fin 2)) (outs : List (BAProvOut P)) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (Wt : (P.E' ⊕ P.I' → Idx d L W) → ℝ) (ℓe : Fin 2 → Idx d L W),
      ∫ ω, P.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
        (outs.map fun o => ∫ ω, o.Q.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ o.π)) ℓe ∂(PF d L W 0)).sum

/-- a leaf of the recursion: the graph itself with the identity map -/
theorem BAWExp.refl (d : ℕ) (P : BAPGraph (Fin 2)) : BAWExp d P [⟨P, id⟩] := by
  intro L W _ _ _ g0 Em t m _ _ _ Wt ℓe; simp

/-- **the weighted identity** (as `WExp.prod` in `Graph/LWProv.lean`): `Wt = Π_k w_k(ℓ β^{(k)})` gives `E[Π_k f^{w_k}] = Σ_r E[Σ_{ℓ_i} Π_k w_k(ℓ(π_r β^{(k)})) term_r]` -/
theorem BAWExp.prod {d p : ℕ} {outs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))}
    (h : BAWExp d (baPG (BAGraph.ofLGraph (fxyPowGraph p))) outs) {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {g0 Em t : ℝ} {m : ℂ}
    (hS : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (w : Fin p → Idx d L W → ℝ) (ℓe : Fin 2 → Idx d L W) :
    ∫ ω, (baPG (BAGraph.ofLGraph (fxyPowGraph p))).valW (BAlwData d L W g0 Em t m ω)
        (fun ℓ => ∏ k, w k (ℓ (Sum.inr (localReg_fxyBeta k)))) ℓe ∂(PF d L W 0) =
      (outs.map fun o => ∫ ω, o.Q.valW (BAlwData d L W g0 Em t m ω)
        (fun ℓ => ∏ k, w k (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) ℓe ∂(PF d L W 0)).sum :=
  h L W hL g0 Em t m hS ht0 ht1 _ ℓe

/-! ## 4. Molecular maps -/

section Mol
variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

/-- a map that keeps `BAGraph.adj` sends shadow-reachable vertices to shadow-reachable vertices (as `lwProv_reach_map` in `Graph/LWProv.lean`, on the shadows) -/
theorem BAProv_reach_map (Γ : BAGraph E I) (Γ' : BAGraph E' I') (f : E ⊕ I → E' ⊕ I')
    (hadj : ∀ u v, Γ.adj u v = true → Γ'.adj (f u) (f v) = true) {u v : E ⊕ I} (h : Γ.shadow.molGraph.Reachable u v) :
    Γ'.shadow.molGraph.Reachable (f u) (f v) :=
  lwProv_reach_map Γ.shadow Γ'.shadow f (fun u v huv => Or.inr (by rw [BAAtom_shadow_adj] at huv ⊢; exact hadj u v huv)) h

/-- adjacent vertices are shadow-reachable -/
theorem BAProv_adj_reach (T : BAGraph E I) {u v : E ⊕ I} (h : T.adj u v = true) : T.shadow.molGraph.Reachable u v := by
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((owx_molGraph_adj T.shadow u v).2 ⟨huv, by rw [BAAtom_shadow_adj]; exact h⟩)

/-- the merge map `vmap` of a graph without `=`-dotted edges keeps shadow reachability (`splitG`/`merge`/`packMerge`) -/
theorem BAProv_merge_reach (T : BAGraph E I) (hT : ∀ e ∈ T.dotted, e.eq = false) {u v : E ⊕ I} (h : T.shadow.molGraph.Reachable u v) :
    T.merge.shadow.molGraph.Reachable (T.toLGraph.vmap u) (T.toLGraph.vmap v) :=
  BAProv_reach_map T T.merge _ (fun u v huv => by rw [BAVocab_merge_adj T hT]; exact huv) h

/-- **coverage at a term** (the start): if every vertex outside the molecules of the external vertices is shadow-joined to some `β k`,
the `β k` cover the internal molecules of the merged term (`vmap` is onto and keeps reachability) -/
theorem BAProv_cover_term {κ : Type} (T : BAGraph (Fin 2) I) (hT : ∀ e ∈ T.dotted, e.eq = false) (β : κ → Fin 2 ⊕ I)
    (h : ∀ w, (∀ a, ¬ T.shadow.molGraph.Reachable w (Sum.inl a)) → ∃ k, T.shadow.molGraph.Reachable w (β k)) :
    BACoverBy (P := T.packMerge) fun k => T.toLGraph.vmap (β k) := by
  rintro ⟨c, hc⟩
  induction c using SimpleGraph.ConnectedComponent.ind with | h w => ?_
  obtain ⟨w₀, rfl⟩ := BAVocab_vmap_surjective T.toLGraph w
  have hmol : ∀ a, T.shadow.molGraph.Reachable w₀ (Sum.inl a) → T.merge.shadow.molOf (T.toLGraph.vmap w₀) =
      T.merge.shadow.molOf (Sum.inl (T.toLGraph.extMap a)) := by
    intro a hw
    rw [← lwProv_vmap_inl]
    exact SimpleGraph.ConnectedComponent.eq.2 (BAProv_merge_reach T hT hw)
  obtain ⟨k, hk⟩ := h w₀ fun a ha => hc ⟨T.toLGraph.extMap a, (hmol a ha).symm⟩
  exact ⟨k, SimpleGraph.ConnectedComponent.eq.2 (BAProv_merge_reach T hT hk).symm⟩

/-- **`T` is a molecular extension of `Γ` along `emb`**: no `=`-dotted edge, the adjacencies of `Γ` are kept, the external vertices are fixed, every vertex of `T` is
shadow-joined to an image of a vertex of `Γ` (no new shadow molecule, the joining edges of the input survive; G5-a (ii)) -/
def BAProv_Ext (Γ : BAGraph E I) (emb : E ⊕ I → E ⊕ I') (T : BAGraph E I') : Prop :=
  (∀ e ∈ T.dotted, e.eq = false) ∧ (∀ u v, Γ.adj u v = true → T.adj (emb u) (emb v) = true) ∧ (∀ a, emb (Sum.inl a) = Sum.inl a) ∧
    ∀ w, ∃ v, T.shadow.molGraph.Reachable w (emb v)

/-- `splitG` only adds `M`-dotted edges -/
theorem BAProv_splitG_adj (T : BAGraph E I) {T' : BAGraph E I} (hT' : T' ∈ T.splitG) {u v : E ⊕ I} (h : T.adj u v = true) : T'.adj u v = true := by
  simp only [BAGraph.splitG, List.mem_map] at hT'
  obtain ⟨r, hr, rfl⟩ := hT'
  simp only [BAGraph.adj, LGraph.adj, BAGraph.atomAdj, List.any_append, Bool.or_eq_true] at h ⊢
  tauto

theorem BAProv_Ext.splitG {Γ : BAGraph E I} {emb : E ⊕ I → E ⊕ I'} {T : BAGraph E I'} (h : BAProv_Ext Γ emb T) :
    ∀ T' ∈ T.splitG, BAProv_Ext Γ emb T' := by
  intro T' hT'
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun u v huv => BAProv_splitG_adj T hT' (h2 u v huv), h3, fun w => ?_⟩
  · rw [(BAGraph.splitG_edges T T' hT').2.1]; exact h1
  · obtain ⟨v, hv⟩ := h4 w
    exact ⟨v, BAProv_reach_map T T' id (fun a b hab => BAProv_splitG_adj T hT' hab) hv⟩

theorem BAProv_Ext.trans {I'' : Type} [Fintype I''] [DecidableEq I''] {Γ : BAGraph E I} {e₁ : E ⊕ I → E ⊕ I'} {T : BAGraph E I'}
    {e₂ : E ⊕ I' → E ⊕ I''} {T' : BAGraph E I''} (h : BAProv_Ext Γ e₁ T) (h' : BAProv_Ext T e₂ T') : BAProv_Ext Γ (e₂ ∘ e₁) T' := by
  obtain ⟨-, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  refine ⟨h1', fun u v huv => h2' _ _ (h2 u v huv), fun a => by simp [Function.comp_apply, h3, h3'], fun w => ?_⟩
  obtain ⟨v', hv'⟩ := h4' w
  obtain ⟨v, hv⟩ := h4 v'
  exact ⟨v, hv'.trans (BAProv_reach_map T T' e₂ h2' hv)⟩

/-- the identity is a (trivial) extension -/
theorem BAProv_Ext.refl (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) : BAProv_Ext Γ id Γ :=
  ⟨hD, fun _ _ h => h, fun _ => rfl, fun w => ⟨w, SimpleGraph.Reachable.refl _⟩⟩

/-- `lanlwExt` with the coefficient `1` is `BAGraph.ext 2` -/
theorem BAProv_lanlwExt_eq (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) : BAGraph.lanlwExt Γ rest 1 s w md = BAGraph.ext 2 Γ rest s w md := rfl

/-- **an extension by two new vertices is a molecular extension** if the new vertex `0` is `M`-joined to the image of an old vertex `x` and `1` is waved-joined to `0`
(the shape of `lw2`, `lanlw`, `gg2`, `dq`) -/
theorem BAProv_Ext_ext2 (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I)
    (h0 : bpM (owxEmb 2 x) (bpv 0) ∈ md ∨ bpM (bpv 0) (owxEmb 2 x) ∈ md) (h1 : bpW true (bpv 0) (bpv 1) ∈ w ∨ bpW false (bpv 0) (bpv 1) ∈ w) :
    BAProv_Ext Γ (owxEmb 2) (BAGraph.ext 2 Γ rest s w md) := by
  have hadj := BAWeightOp_ext_adj 2 Γ rest s w md
  refine ⟨fun e he => ?_, fun u v h => (hadj _ _).2 (Or.inl ⟨u, v, rfl, rfl, h⟩), fun a => rfl, fun v => ?_⟩
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hΓ e0 he0
  · have a0 : (BAGraph.ext 2 Γ rest s w md).adj (bpv 0) (owxEmb 2 x) = true := by
      refine (hadj _ _).2 (Or.inr (Or.inr ?_))
      rcases h0 with h0 | h0
      · exact ⟨_, h0, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨_, h0, Or.inl ⟨rfl, rfl⟩⟩
    have a1 : (BAGraph.ext 2 Γ rest s w md).adj (bpv 0) (bpv 1) = true := by
      refine (hadj _ _).2 (Or.inr (Or.inl ?_))
      rcases h1 with h1 | h1
      · exact ⟨_, h1, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, h1, Or.inl ⟨rfl, rfl⟩⟩
    rcases v with a | i | j
    · exact ⟨Sum.inl a, SimpleGraph.Reachable.refl _⟩
    · exact ⟨Sum.inr i, SimpleGraph.Reachable.refl _⟩
    · fin_cases j
      · exact ⟨x, BAProv_adj_reach _ a0⟩
      · exact ⟨x, (BAProv_adj_reach _ a1).symm.trans (BAProv_adj_reach _ a0)⟩

/-- the same for four new vertices in a chain `x - 0 - 1 - 2 - 3` (`M`, waved, `M`, waved; the shape of `lw4`, `gg4`) -/
theorem BAProv_Ext_ext4 (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 4))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 4)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I)
    (h0 : bpM (owxEmb 4 x) (bpv 0) ∈ md ∨ bpM (bpv 0) (owxEmb 4 x) ∈ md) (h1 : bpW true (bpv 0) (bpv 1) ∈ w ∨ bpW false (bpv 0) (bpv 1) ∈ w)
    (h2 : bpM (bpv 1) (bpv 2) ∈ md ∨ bpM (bpv 2) (bpv 1) ∈ md) (h3 : bpW true (bpv 2) (bpv 3) ∈ w ∨ bpW false (bpv 2) (bpv 3) ∈ w) :
    BAProv_Ext Γ (owxEmb 4) (BAGraph.ext 4 Γ rest s w md) := by
  have hadj := BAWeightOp_ext_adj 4 Γ rest s w md
  refine ⟨fun e he => ?_, fun u v h => (hadj _ _).2 (Or.inl ⟨u, v, rfl, rfl, h⟩), fun a => rfl, fun v => ?_⟩
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact hΓ e0 he0
  · have a0 : (BAGraph.ext 4 Γ rest s w md).adj (bpv 0) (owxEmb 4 x) = true := by
      refine (hadj _ _).2 (Or.inr (Or.inr ?_))
      rcases h0 with h0 | h0
      · exact ⟨_, h0, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨_, h0, Or.inl ⟨rfl, rfl⟩⟩
    have a1 : (BAGraph.ext 4 Γ rest s w md).adj (bpv 0) (bpv 1) = true := by
      refine (hadj _ _).2 (Or.inr (Or.inl ?_))
      rcases h1 with h1 | h1
      · exact ⟨_, h1, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, h1, Or.inl ⟨rfl, rfl⟩⟩
    have a2 : (BAGraph.ext 4 Γ rest s w md).adj (bpv 1) (bpv 2) = true := by
      refine (hadj _ _).2 (Or.inr (Or.inr ?_))
      rcases h2 with h2 | h2
      · exact ⟨_, h2, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, h2, Or.inr ⟨rfl, rfl⟩⟩
    have a3 : (BAGraph.ext 4 Γ rest s w md).adj (bpv 2) (bpv 3) = true := by
      refine (hadj _ _).2 (Or.inr (Or.inl ?_))
      rcases h3 with h3 | h3
      · exact ⟨_, h3, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, h3, Or.inl ⟨rfl, rfl⟩⟩
    have r0 := BAProv_adj_reach _ a0
    have r1 := (BAProv_adj_reach _ a1).symm.trans r0
    have r2 := (BAProv_adj_reach _ a2).symm.trans r1
    have r3 := (BAProv_adj_reach _ a3).symm.trans r2
    rcases v with a | i | j
    · exact ⟨Sum.inl a, SimpleGraph.Reachable.refl _⟩
    · exact ⟨Sum.inr i, SimpleGraph.Reachable.refl _⟩
    · fin_cases j
      · exact ⟨x, r0⟩
      · exact ⟨x, r1⟩
      · exact ⟨x, r2⟩
      · exact ⟨x, r3⟩

/-! ### The extension families of the five frame kinds -/

theorem BAProv_Ext_lanlwD (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAProv_Ext Γ (owxEmb 2) (BAGraph.lanlwD Γ p q) := by
  rw [BAGraph.lanlwD, BAProv_lanlwExt_eq]
  exact BAProv_Ext_ext2 Γ hΓ _ _ _ _ p.1.src (Or.inl (by simp [bpM])) (Or.inr (by simp [bpW]))

theorem BAProv_Ext_lanlwT1 (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAProv_Ext Γ (owxEmb 2) (BAGraph.lanlwT1 Γ p) := by
  rw [BAGraph.lanlwT1, BAProv_lanlwExt_eq]
  exact BAProv_Ext_ext2 Γ hΓ _ _ _ _ p.1.src (Or.inl (by simp [bpM])) (Or.inr (by simp [bpW]))

theorem BAProv_Ext_lanlw (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ BAGraph.lanlwTerms Γ p, BAProv_Ext Γ (owxEmb 2) T := by
  intro T hT
  simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨q, -, rfl⟩
  · exact BAProv_Ext_lanlwT1 Γ hΓ p
  · exact BAProv_Ext_lanlwD Γ hΓ p q

theorem BAProv_Ext_lw2 (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.lw2 p, BAProv_Ext Γ (owxEmb 2) T := by
  intro T hT
  simp only [BAGraph.lw2, List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨q, -, rfl⟩
  · exact BAProv_Ext_ext2 Γ hΓ _ _ _ _ p.1.src (Or.inl (by simp)) (Or.inr (by simp))
  · exact BAProv_Ext_lanlwD Γ hΓ p q

theorem BAProv_Ext_lw4 (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.lw4 p, BAProv_Ext Γ (owxEmb 4) T := by
  intro T hT
  simp only [BAGraph.lw4, List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨q, -, rfl⟩
  all_goals exact BAProv_Ext_ext4 Γ hΓ _ _ _ _ p.1.src (Or.inl (by simp)) (Or.inl (by simp)) (Or.inl (by simp)) (Or.inr (by simp))

theorem BAProv_Ext_gg2 (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.gg2 p q, BAProv_Ext Γ (owxEmb 2) T := by
  intro T hT
  unfold BAGraph.gg2 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, _, rfl⟩
  all_goals exact BAProv_Ext_ext2 Γ hΓ _ _ _ _ p.1.src (Or.inl (by simp)) (by simp)

theorem BAProv_Ext_gg4 (Γ : BAGraph E I) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.gg4 p q, BAProv_Ext Γ (owxEmb 4) T := by
  intro T hT
  unfold BAGraph.gg4 at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, _, rfl⟩
  all_goals exact BAProv_Ext_ext4 Γ hΓ _ _ _ _ p.1.src (Or.inl (by simp)) (Or.inl (by simp)) (Or.inl (by simp)) (Or.inr (by simp))

section Out
variable (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I']

/-- the output of a term `T'` (merged, read through `P.ext` as in `BAPGraph.outsOf`) with the map `vmap ∘ emb` -/
def BAProvOut.ofTerm (emb : P.E' ⊕ P.I' → P.E' ⊕ I') (T' : BAGraph P.E' I') : BAProvOut P :=
  ⟨BALvl1A_pcomp P T'.packMerge, fun v => T'.toLGraph.vmap (emb v)⟩

/-- **a molecular extension gives a `ExtOK` and `Molecular` output** (as `lwProv_blk_mol` in `Graph/LWProv.lean`): the merged, repacked term with the map `vmap ∘ emb` -/
theorem BAProv_ofTerm_good (emb : P.E' ⊕ P.I' → P.E' ⊕ I') (T' : BAGraph P.E' I') (h : BAProv_Ext P.g emb T') :
    (BAProvOut.ofTerm P emb T').ExtOK ∧ (BAProvOut.ofTerm P emb T').Molecular := by
  obtain ⟨hT, hK, hE, hJ⟩ := h
  have hext : ∀ a, T'.toLGraph.vmap (emb (Sum.inl a)) = Sum.inl (T'.toLGraph.extMap a) := fun a => by rw [hE, lwProv_vmap_inl]
  have h1 : ∀ v w, P.g.shadow.molOf v = P.g.shadow.molOf w → T'.merge.shadow.molOf (T'.toLGraph.vmap (emb v)) = T'.merge.shadow.molOf (T'.toLGraph.vmap (emb w)) :=
    fun v w hvw => SimpleGraph.ConnectedComponent.eq.2 (BAProv_merge_reach T' hT (BAProv_reach_map P.g T' emb hK (SimpleGraph.ConnectedComponent.eq.1 hvw)))
  refine ⟨fun i => by simp only [BAProvOut.ofTerm, BALvl1A_pcomp]; rw [hext]; rfl, h1, fun c hc => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with | h w => ?_
  obtain ⟨w₀, rfl⟩ := BAVocab_vmap_surjective T'.toLGraph w
  obtain ⟨v, hv⟩ := hJ w₀
  have hr : T'.merge.shadow.molOf (T'.toLGraph.vmap (emb v)) = T'.merge.shadow.molOf (T'.toLGraph.vmap w₀) :=
    SimpleGraph.ConnectedComponent.eq.2 (BAProv_merge_reach T' hT hv.symm)
  refine ⟨v, fun ⟨a, ha⟩ => hc ⟨T'.toLGraph.extMap a, ?_⟩, hr⟩
  change T'.merge.shadow.molOf (Sum.inl (T'.toLGraph.extMap a)) = T'.merge.shadow.molOf (T'.toLGraph.vmap w₀)
  rw [← lwProv_vmap_inl, ← hE a, ← hr]; exact h1 _ _ ha

/-- the provenance outputs of `outsOf`: one per term of the partition of each term of `Ts` -/
def BAProv_provOuts (emb : P.E' ⊕ P.I' → P.E' ⊕ I') (Ts : List (BAGraph P.E' I')) : List (BAProvOut P) :=
  Ts.flatMap fun T => T.splitG.map (BAProvOut.ofTerm P emb)

end Out

/-! ### The five frame kinds -/

/-! ### The twist and `BALocStep` -/

/-- the twist of a provenance output (the vertex types are those of the untwisted graphs) -/
def BAProvOut.twist (c t : Bool) {P : BAPGraph (Fin 2)} (o : BAProvOut P) : BAProvOut (P.twist c t) := ⟨o.Q.twist c t, o.π⟩

/-- the molecules of a twisted graph are those of the graph (`BAGraph.twist_atomAdj`, `lwSymmTwistG_adj`) -/
theorem BAProv_twist_mol_iff (c t : Bool) (Γ : BAGraph E I) (u v : E ⊕ I) :
    (Γ.twist c t).shadow.molOf u = (Γ.twist c t).shadow.molOf v ↔ Γ.shadow.molOf u = Γ.shadow.molOf v := by
  have h2 : (Γ.twist c t).adj = Γ.adj := by
    funext a b; simp only [BAGraph.adj]
    rw [show (Γ.twist c t).toLGraph = lwSymmTwistG c t Γ.toLGraph from rfl, lwSymmTwistG_adj, BAGraph.twist_atomAdj]
  have h3 : (Γ.twist c t).mol = Γ.mol := by
    have : (Γ.twist c t).step = Γ.step := by funext a; simp only [BAGraph.step, h2]
    funext a; simp only [BAGraph.mol, this]
  rw [BAAtom_shadow_molOf_eq_iff, BAAtom_shadow_molOf_eq_iff, h3]

/-! ### The start terms -/

end Mol

/-! ## 5. The weighted partition -/

section MergeW

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`G = Ǧ + M` at one labelling** (Definition B.4 `defn_normalBA`; `BAGraph.val_splitG` before the sum over the internal labels): the terms of `splitG` add up to the term -/
theorem BAProv_term_splitG (Γ : BAGraph E I) (D : BALData ι) (ℓ : E ⊕ I → ι) :
    (Γ.splitG.map fun Δ => Δ.term D ℓ).sum = Γ.term D ℓ := by
  have hterm : ∀ r : List (SEdge (E ⊕ I)) × List (BAMEdge (E ⊕ I)),
      (BAGraph.mk (LGraph.mk r.1 Γ.waved Γ.dotted Γ.coeff) Γ.psi (r.2 ++ Γ.mdot)).term D ℓ =
        (Γ.coeff * (Γ.waved.map (WEdge.val D.toLData ℓ)).prod * (Γ.dotted.map (DEdge.val ℓ)).prod *
          (Γ.psi.map (BAPsiEdge.val D ℓ)).prod * (Γ.mdot.map (BAMEdge.val D ℓ)).prod) *
        ((r.1.map (SEdge.val D.toLData ℓ)).prod * (r.2.map (BAMEdge.val D ℓ)).prod) := by
    intro r
    simp only [BAGraph.term, LGraph.term, List.map_append, List.prod_append]
    ring
  calc (Γ.splitG.map fun Δ => Δ.term D ℓ).sum
      = ((baSplitSolid Γ.solid).map fun r =>
          (Γ.coeff * (Γ.waved.map (WEdge.val D.toLData ℓ)).prod * (Γ.dotted.map (DEdge.val ℓ)).prod *
            (Γ.psi.map (BAPsiEdge.val D ℓ)).prod * (Γ.mdot.map (BAMEdge.val D ℓ)).prod) *
          ((r.1.map (SEdge.val D.toLData ℓ)).prod * (r.2.map (BAMEdge.val D ℓ)).prod)).sum := by
        simp only [BAGraph.splitG, List.map_map, Function.comp_def, hterm]
    _ = Γ.term D ℓ := by
        rw [List.sum_map_mul_left, BAVocab_split_val]
        simp only [BAGraph.term, LGraph.term]
        ring

/-- the weighted value is the sum of the weighted values of the terms of `G = Ǧ + M` (same vertices, same weight) -/
theorem BAProv_valW_splitG (Γ : BAGraph E I) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) :
    (Γ.splitG.map fun Δ => Δ.valW D Wt ℓe).sum = Γ.valW D Wt ℓe := by
  unfold BAGraph.valW
  calc (Γ.splitG.map fun Δ => ∑ ℓi : I → ι, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Δ.term D (Sum.elim ℓe ℓi)).sum
      = ∑ ℓi : I → ι, (Γ.splitG.map fun Δ => ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Δ.term D (Sum.elim ℓe ℓi)).sum :=
        (lwProv_sum_comm_list Γ.splitG fun Δ ℓi => ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Δ.term D (Sum.elim ℓe ℓi)).symm
    _ = _ := Finset.sum_congr rfl fun ℓi _ => by
        rw [List.sum_map_mul_left, BAProv_term_splitG]

/-- **the weighted value is preserved by merging** (as `lwProv_valW_merge` in `Graph/LWProv.lean`; `BAVocab_val_eq_merge_val` with a weight on all the vertices) -/
theorem BAProv_valW_merge (Γ : BAGraph E I) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓ' : Γ.toLGraph.ExtCls → ι) :
    Γ.valW D Wt (ℓ' ∘ Γ.toLGraph.extMap) = Γ.merge.valW D (fun ℓ => Wt (ℓ ∘ Γ.toLGraph.vmap)) ℓ' := by
  classical
  set Φ : (Γ.toLGraph.IntCls → ι) → (I → ι) := fun ℓi' b => (Sum.elim ℓ' ℓi') (Γ.toLGraph.vmap (Sum.inr b)) with hΦ
  have hlab : ∀ ℓi', Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) (Φ ℓi') = (Sum.elim ℓ' ℓi') ∘ Γ.toLGraph.vmap := by
    intro ℓi'
    funext v
    rcases v with a | b
    · simp [lwProv_vmap_inl]
    · rfl
  have hRHS : Γ.merge.valW D (fun ℓ => Wt (ℓ ∘ Γ.toLGraph.vmap)) ℓ' =
      ∑ ℓi', ((Wt (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) (Φ ℓi')) : ℝ) : ℂ) * Γ.term D (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) (Φ ℓi')) := by
    unfold BAGraph.valW
    refine Finset.sum_congr rfl fun ℓi' _ => ?_
    rw [BAVocab_term_merge, hlab]
  have hinj : Function.Injective Φ := by
    intro f g hfg
    funext q
    obtain ⟨b, hb⟩ := BAVocab_exists_inr_of_int Γ.toLGraph q
    have hq : ¬ Γ.toLGraph.IsExtCls (Γ.toLGraph.cls (Sum.inr b)) := by rw [hb]; exact q.2
    have hv : Γ.toLGraph.vmap (Sum.inr b) = Sum.inr q := by
      rw [BAVocab_vmap_inr_int Γ.toLGraph b hq]
      congr 1
      exact Subtype.ext hb
    have := congrFun hfg b
    simpa [hΦ, hv] using this
  have hrange : ∀ ℓi : I → ι, ℓi ∉ Set.range Φ → Γ.term D (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) ℓi) = 0 := by
    intro ℓi hℓi
    apply BAVocab_term_zero
    intro hgood
    apply hℓi
    refine ⟨fun q => ℓi (Classical.choose (BAVocab_exists_inr_of_int Γ.toLGraph q)), ?_⟩
    funext b
    by_cases hext : Γ.toLGraph.IsExtCls (Γ.toLGraph.cls (Sum.inr b))
    · obtain ⟨a, ha⟩ := hext
      have h1 := BAVocab_good_eq_of_cls hgood (u := Sum.inl a) (v := Sum.inr b) ha
      simp only [hΦ, BAVocab_vmap_inr_ext Γ.toLGraph b ⟨a, ha⟩, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] at h1 ⊢
      rw [← h1]
      congr 1
      exact Subtype.ext ha.symm
    · have hc := Classical.choose_spec (BAVocab_exists_inr_of_int Γ.toLGraph ⟨Γ.toLGraph.cls (Sum.inr b), hext⟩)
      have h1 := BAVocab_good_eq_of_cls hgood
        (u := Sum.inr (Classical.choose (BAVocab_exists_inr_of_int Γ.toLGraph ⟨Γ.toLGraph.cls (Sum.inr b), hext⟩))) (v := Sum.inr b) hc
      simp only [hΦ, BAVocab_vmap_inr_int Γ.toLGraph b hext, Sum.elim_inr]
      simpa using h1
  rw [hRHS]
  unfold BAGraph.valW
  rw [← Finset.sum_image (f := fun ℓi => ((Wt (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) ℓi))
    (fun x _ y _ h => hinj h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro ℓi _ hni
  have := hrange ℓi (fun ⟨x, hx⟩ => hni (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩))
  simp [this]

/-- the merged, packed graph has the weighted value of the graph, for all external labels (those that do not factor through the merge give `0` on both sides) -/
theorem BAProv_valW_packMerge (Γ : BAGraph E I) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) :
    Γ.packMerge.valW D (fun ℓ => Wt (ℓ ∘ Γ.toLGraph.vmap)) ℓe = Γ.valW D Wt ℓe := by
  classical
  by_cases h : ∃ ℓ' : Γ.toLGraph.ExtCls → ι, ℓe = ℓ' ∘ Γ.toLGraph.extMap
  · obtain ⟨ℓ', hℓ⟩ := h
    rw [BAPGraph.valW_of_factor Γ.packMerge D _ hℓ]
    subst hℓ
    exact (BAProv_valW_merge Γ D Wt ℓ').symm
  · rw [BAPGraph.valW_of_not Γ.packMerge D _ h]
    unfold BAGraph.valW
    refine (Finset.sum_eq_zero fun ℓi _ => ?_).symm
    rw [BAVocab_term_zero Γ D ?_, mul_zero]
    intro hgood
    apply h
    refine ⟨fun q => ℓe (Classical.choose q.2), ?_⟩
    funext a
    have hc := Classical.choose_spec (Γ.toLGraph.extMap a).2
    have := BAVocab_good_eq_of_cls hgood (u := Sum.inl (Classical.choose (Γ.toLGraph.extMap a).2)) (v := Sum.inl a) hc
    simpa using this.symm

/-- **the weighted partition** (as `lwProv_valW_partX` in `Graph/LWProv.lean`; no tags, no data hypothesis): `valW Γ Wt = Σ_{Δ ∈ splitG} valW (Δ.packMerge) (Wt ∘ vmap_Δ)`, per labelling -/
theorem BAGraph.valW_partition (Γ : BAGraph E I) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) :
    Γ.valW D Wt ℓe = (Γ.splitG.map fun Δ => Δ.packMerge.valW D (fun ℓ => Wt (ℓ ∘ Δ.toLGraph.vmap)) ℓe).sum := by
  rw [← BAProv_valW_splitG]
  exact congrArg List.sum (List.map_congr_left fun Δ _ => (BAProv_valW_packMerge Δ D Wt ℓe).symm)

end MergeW

/-! ## 6. The domain form of `f_xy` and the bridge -/

/-- `f_{xy}` with the sum over `β` restricted to the blocks in `Dm` (`f^{>ℓ}`, `f^{≤ℓ}` of (7.56) `eq:far_ab_K`; as `LWfD` in `Graph/LWProv.lean`, at the data level); `Dm = univ` is `fxyVal` -/
def fxyValD {d L W : ℕ} [NeZero L] [NeZero W] (D : LData (Idx d L W)) (Dm : Finset (Zd d L)) (x y : Idx d L W) : ℂ :=
  ∑ α, if α = x ∨ α = y then (0 : ℂ) else ∑ β, if (split d L W β).1 ∈ Dm then D.S α β * (D.G β β - D.M β β) * D.G x α * D.G α y else 0

/-- `z^k \bar z^k = ‖z‖^(2k)` (as the band's `lwMoment_pow_conj` in `Graph/LWMoment.lean`) -/
private theorem BAProv_pow_conj (z : ℂ) (k : ℕ) : z ^ k * star z ^ k = ((‖z‖ ^ (2 * k) : ℝ) : ℂ) := by
  rw [← mul_pow, Complex.star_def, Complex.mul_conj', pow_mul]
  push_cast; ring

/-- **the weighted `|f|^p` bridge** (as `lwProv_bridge` in `Graph/LWProv.lean`; pointwise in the sample): at the BA data `BAlwData` (`S = t · svarF` real) and `p` even, the weighted value of the BA
start graph with the weight `Π_k 1_{Dm}([β^{(k)}])` is `‖fxyValD‖^p`; at `Dm = univ` it is the pointwise identity under `ba_fxyPow_integral_eq` (`Graph/BALocReg1B.lean`).  No data hypothesis. -/
theorem baProv_bridge (d L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) (ω : Ω d L W) (p : ℕ) (hp : Even p) (Dm : Finset (Zd d L)) (ℓe : Fin 2 → Idx d L W) :
    (BAGraph.ofLGraph (fxyPowGraph p)).valW (BAlwData d L W g0 Em t m ω)
        (fun ℓ => ∏ k : Fin p, if (split d L W (ℓ (Sum.inr (localReg_fxyBeta k)))).1 ∈ Dm then (1 : ℝ) else 0) ℓe =
      ((‖fxyValD (BAlwData d L W g0 Em t m ω).toLData Dm (ℓe 0) (ℓe 1)‖ ^ p : ℝ) : ℂ) := by
  classical
  obtain ⟨x, y, rfl⟩ : ∃ x y, ℓe = ![x, y] := ⟨ℓe 0, ℓe 1, by funext i; fin_cases i <;> rfl⟩
  let D0 : LData (Idx d L W) := (BAlwData d L W g0 Em t m ω).toLData
  let D1 : LData (Idx d L W) := { D0 with S := fun a b => (if (split d L W b).1 ∈ Dm then 1 else 0) * D0.S a b }
  have hS0 : ∀ i j, star (D0.S i j) = D0.S i j := fun i j => by
    change star (BAlwS d L W t i j) = BAlwS d L W t i j
    simp [BAlwS, star_mul', Complex.star_def, Complex.conj_ofReal]
  have hS1 : ∀ i j, star (D1.S i j) = D1.S i j := fun i j => by
    simp only [D1, star_mul', hS0]
    congr 1
    split_ifs <;> simp
  have hBV : ∀ (σ : Bool) (a b : Idx d L W), localReg_fxyBlockVal D1 x y σ a b =
      (if (split d L W b).1 ∈ Dm then 1 else 0 : ℂ) * localReg_fxyBlockVal D0 x y σ a b := by
    intro σ a b
    unfold localReg_fxyBlockVal
    change _ * ((if (split d L W b).1 ∈ Dm then 1 else 0 : ℂ) * D0.S a b) * _ = _
    ring
  have h1 : (BAGraph.ofLGraph (fxyPowGraph p)).valW (BAlwData d L W g0 Em t m ω)
      (fun ℓ => ∏ k : Fin p, if (split d L W (ℓ (Sum.inr (localReg_fxyBeta k)))).1 ∈ Dm then (1 : ℝ) else 0) ![x, y] =
      (fxyPowGraph p).val D1 ![x, y] := by
    unfold BAGraph.valW LGraph.val
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    have ht : (BAGraph.ofLGraph (fxyPowGraph p)).term (BAlwData d L W g0 Em t m ω) (Sum.elim ![x, y] ℓi) =
        (fxyPowGraph p).term D0 (Sum.elim ![x, y] ℓi) := by
      simp [BAGraph.term, BAGraph.ofLGraph, D0]
    rw [ht, localReg_fxy_term D0 p x y ℓi, localReg_fxy_term D1 p x y ℓi]
    simp only [Sum.elim_inr, hBV, Finset.prod_mul_distrib, Complex.ofReal_prod]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : (split d L W (ℓi (localReg_fxyBeta k))).1 ∈ Dm <;> simp [hk]
  change _ = ((‖fxyValD D0 Dm x y‖ ^ p : ℝ) : ℂ)
  refine h1.trans ?_
  rw [fxyPowGraph_val_eq D1 hS1 p hp x y]
  have h2 : fxyVal D1 x y = fxyValD D0 Dm x y := by
    unfold fxyVal fxyValD
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs with hα
    · rfl
    · refine Finset.sum_congr rfl fun β _ => ?_
      by_cases hb : (split d L W β).1 ∈ Dm
      · simp [D1, hb]
      · simp [D1, hb]
  rw [h2]
  obtain ⟨k, hk⟩ := hp
  have hk2 : p / 2 = k := by omega
  have hk3 : 2 * k = p := by omega
  rw [hk2, BAProv_pow_conj, hk3]

end RBM.Graph

end
