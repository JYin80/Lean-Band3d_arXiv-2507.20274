/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpSim
import RBM3D.Graph.LWExpCertBS0
import RBM3D.Graph.LWExpCertBS1

/-!
# LW-14e-4 (T2318): the soundness of the certificate and `lwG5Expand'_holds`

The AND-tree certificate `cert_all'` (T2319, kernel) is carried through the simulation relation
`Rel` (T2311) to the real expansion `expandRoot selClassical 4` (T2307): `relInvariance` (L6),
`relKids` (L5': the children of every packed graph related to a model node), `belowOfSound` (L7:
the corrected flag `belowOf'` is sound at every term of `cPartitionX`), `soundStep`, `soundRoot`
(every `k`, through a colour-erased key), the induction along `expand` (`lwG5LeafProps_holds`) and
the assembly `lwG5Expand'_holds : ∀ d, LWG5Expand' d` (`B:78-108`, `(eq:sizeGammamu_E)`; "verified
by inspecting", `B:98`).  Helpers are prefixed `lwExpSound_`; of `LWExpSim.lean` only the keyword
`private` of the `lwExpSim_*` layers used here was deleted.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Graph.LWCert RBM.Green

/-! ## 0. The pinned definitions (the texts of `docs/tickets/checks/T2318-check.lean`, section 2-3) -/

/-- The leaf half of `LWG5Expand'`: the six conjuncts for every member of the list. -/
def LWG5LeafProps (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
  ∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧
    ((∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∨
      LWJoined q.2) ∧
    (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder

/-- `LWG5Expand'` split into its two halves. -/
def LWG5ExpandSplit (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2)),
    LWG5LeafProps Ls ∧ LWG5Identity d Ls

/-- The pin `LWG5Expand'Pin d` of T2265 (`docs/tickets/checks/T2265-check.lean:197-207`), up to names. -/
def LWG5Expand' (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2)),
    (∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧
        ((∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∨ LWJoined q.2) ∧
        (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder) ∧
    ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
      (x y : Idx d (sz.L n) (sz.W n)),
      ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
        ((Ls k s).map fun q =>
          (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
            ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum

/-- The final assembly: the pin from the two halves for `selClassical` with fuel `4`. -/
def LWG5ExpandOfHalves : Prop :=
  LWExpandIdentity selClassical 4 → LWG5LeafProps (expandRoot selClassical 4) → ∀ d, LWG5Expand' d

/-- `Rel` transports `Normal`, `n_M`, `LWAttached`, the molecule statement and `LWJoined`. -/
def RelInvariance : Prop :=
  ∀ (N : MNode) (hs : Function.Surjective N.ext) (P : PGraph (Fin 2)), Rel N P →
    (N.g.Normal ↔ P.g.Normal) ∧ P.g.nM = N.g.nM ∧
    (LWAttached P ↔ LWAttached (N.toP hs)) ∧
    ((∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) ↔
      (∀ a b : (N.toP hs).E', (N.toP hs).g.molOf (Sum.inl a) = (N.toP hs).g.molOf (Sum.inl b) → a = b)) ∧
    (LWJoined P ↔ LWJoined (N.toP hs))

/-- The six conjuncts of `LWG5LeafProps` for one packed graph. -/
def LeafOK (P : PGraph (Fin 2)) : Prop :=
  P.g.Normal ∧ P.g.nM ≤ 1 ∧ 2 ≤ P.g.nW ∧ LWAttached P ∧
    ((∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) ∨ LWJoined P) ∧
    (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder

/-- Soundness of the lite classification at a node: under the flag of `childrenB'`, every real child is a leaf with the
leaf properties or is related to a below-target model child. -/
def SoundStep : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (c : Cand N.a N.b) (hc : c ∈ cands N.g), (childrenB' N c).1 = true →
    ∀ Q ∈ (Cand.toR N h c hc).kids,
      ((if Q.2.ext 0 = Q.2.ext 1 then (4 : ℤ) else 5) ≤ Q.2.g.scalingOrder → LeafOK Q.2) ∧
      (¬ (if Q.2.ext 0 = Q.2.ext 1 then (4 : ℤ) else 5) ≤ Q.2.g.scalingOrder → ∃ M ∈ (childrenB' N c).2, Rel M Q.2)

/-- Soundness at the root (`k` is arbitrary: `Rel` ignores the waved colours). -/
def SoundRoot : Prop :=
  ∀ (k s : Bool), (rootInfo' false s).1 = true → ∀ r ∈ partitionX (LWG5Graph k s),
    ((if r.2.ext 0 = r.2.ext 1 then (4 : ℤ) else 5) ≤ r.2.g.scalingOrder → LeafOK r.2) ∧
    (¬ (if r.2.ext 0 = r.2.ext 1 then (4 : ℤ) else 5) ≤ r.2.g.scalingOrder → ∃ M ∈ (rootInfo' false s).2, Rel M r.2)

/-- Bridge 2 along `Rel`: the real children of a packed graph related to a model node, at any of its candidates, are the
model children at a listed model candidate. -/
def RelKids : Prop :=
  ∀ (N : MNode) (P : PGraph (Fin 2)), Rel N P → ∀ c' : RCand P,
    ∃ c : Cand N.a N.b, c ∈ cands N.g ∧
      List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
        (childrenX N c) c'.kids

/-- Soundness of the lite flag of `belowOf'` (T2319's corrected flag): under the flag, a leaf term of `cPartitionX` has the
leaf properties in every related packed graph, and a term below the target is represented in the list up to `Rel`. -/
def BelowOfSound : Prop :=
  ∀ (a b : ℕ) (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)), Function.Surjective ext →
    (belowOf' Δ ext).1 = true → ∀ r ∈ cPartitionX Δ ext,
      (leaf r.2 = true → ∀ Q : PGraph (Fin 2), Rel r.2 Q → LeafOK Q) ∧
      (leaf r.2 = false → ∃ M ∈ (belowOf' Δ ext).2, ∀ Q : PGraph (Fin 2), Rel r.2 Q → Rel M Q)

/-! ## 1. `Rel`: surjectivity of `ext` and the molecules -/

theorem Rel.ext_surj {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) : Function.Surjective N.ext := by
  obtain ⟨eE, eI, he, -⟩ := h
  intro a
  obtain ⟨i, hi⟩ := P.ext_surj (eE a)
  exact ⟨i, eE.injective ((he i).symm.trans hi)⟩

section Mol

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

/-- Copy of the private `LGraph.adj_iff` (`LWVocab.lean:1866`). -/
private theorem lwExpSound_adj_iff (Γ : LGraph E I) (u v : E ⊕ I) :
    Γ.adj u v = true ↔
      (∃ e ∈ Γ.waved, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) ∨
      (∃ e ∈ Γ.dotted, e.eq = true ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) := by
  simp [LGraph.adj, List.any_eq_true]

/-- Adjacency (`mol` reads waved endpoints and `=`-dotted edges only) is transported by a bijection of the vertices. -/
private theorem lwExpSound_adj_map (A : LGraph E I) (B : LGraph E' I') (φ : E ⊕ I ≃ E' ⊕ I')
    (hw : B.waved.map (fun e => (e.x, e.y)) = A.waved.map (fun e => (φ e.x, φ e.y)))
    (hd : B.dotted = A.dotted.map (DEdge.map φ)) (u v : E ⊕ I) : B.adj (φ u) (φ v) = A.adj u v := by
  rw [Bool.eq_iff_iff, lwExpSound_adj_iff, lwExpSound_adj_iff]
  have hW : ∀ p : (E' ⊕ I') × (E' ⊕ I') → Prop, (∃ e ∈ B.waved, p (e.x, e.y)) ↔ ∃ e ∈ A.waved, p (φ e.x, φ e.y) := fun p => by
    simpa [List.mem_map] using congrArg (fun l => ∃ x ∈ l, p x) hw
  have h1 := hW (fun q => (q.1 = φ u ∧ q.2 = φ v) ∨ (q.1 = φ v ∧ q.2 = φ u))
  simp only [φ.injective.eq_iff] at h1
  have hD : (∃ e ∈ B.dotted, e.eq = true ∧ ((e.x = φ u ∧ e.y = φ v) ∨ (e.x = φ v ∧ e.y = φ u))) ↔
      ∃ e ∈ A.dotted, e.eq = true ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
    rw [hd]
    constructor
    · rintro ⟨_, he, h⟩
      obtain ⟨e, he', rfl⟩ := List.mem_map.1 he
      exact ⟨e, he', h.1, by simpa [DEdge.map, φ.injective.eq_iff] using h.2⟩
    · rintro ⟨e, he, h⟩
      exact ⟨DEdge.map φ e, List.mem_map.2 ⟨e, he, rfl⟩, h.1, by simpa [DEdge.map, φ.injective.eq_iff] using h.2⟩
  rw [h1, hD]

/-- The closure `mol` is transported by a bijection of the vertices that transports `adj`. -/
private theorem lwExpSound_mol_map (A : LGraph E I) (B : LGraph E' I') (φ : E ⊕ I ≃ E' ⊕ I')
    (hadj : ∀ u v, B.adj (φ u) (φ v) = A.adj u v) (v : E ⊕ I) :
    B.mol (φ v) = (A.mol v).map φ.toEmbedding := by
  ext w'
  obtain ⟨w, rfl⟩ := φ.surjective w'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, LGraph.mem_mol_iff, LGraph.mem_mol_iff]
  let ι : A.molGraph ≃g B.molGraph := ⟨φ, by
    intro a b
    simp only [LGraph.molGraph, SimpleGraph.fromRel_adj, φ.injective.eq_iff, ne_eq, hadj]⟩
  exact ι.reachable_iff

/-- `Normal` reads `solid` and `dotted` only; it is invariant under `relabel` by a bijection. -/
private theorem lwExpSound_normal_relabel (A : LGraph E I) (φ : E ⊕ I ≃ E' ⊕ I') :
    (A.relabel φ).Normal ↔ A.Normal := by
  unfold LGraph.Normal
  refine and_congr ?_ (and_congr ?_ ?_)
  · simp [LGraph.relabel, DEdge.map]
  · constructor
    · intro h u v huv
      have := h (φ u) (φ v) (φ.injective.ne huv)
      rwa [lwExpSim_xBetween_relabel, lwExpSim_sBetween_relabel] at this
    · intro h u' v' huv
      obtain ⟨u, rfl⟩ := φ.surjective u'
      obtain ⟨v, rfl⟩ := φ.surjective v'
      rw [lwExpSim_xBetween_relabel, lwExpSim_sBetween_relabel]
      exact h u v (fun e => huv (by rw [e]))
  · simp [LGraph.relabel, SEdge.map, φ.injective.eq_iff]

private theorem lwExpSound_normal_map (A : LGraph E I) (B : LGraph E' I') (φ : E ⊕ I ≃ E' ⊕ I')
    (hs : B.solid = A.solid.map (SEdge.map φ)) (hd : B.dotted = A.dotted.map (DEdge.map φ)) :
    B.Normal ↔ A.Normal := by
  rw [← lwExpSound_normal_relabel A φ]
  unfold LGraph.Normal LGraph.XBetween LGraph.SBetween
  rw [hs, hd]
  rfl

private theorem lwExpSound_int_map (A : LGraph E I) (B : LGraph E' I') (φ : E ⊕ I ≃ E' ⊕ I')
    (hmol : ∀ v, B.mol (φ v) = (A.mol v).map φ.toEmbedding) (hφ : ∀ v, (φ v).isRight = v.isRight) (v : E ⊕ I) :
    (∀ w ∈ B.mol (φ v), w.isRight = true) ↔ ∀ w ∈ A.mol v, w.isRight = true := by
  rw [hmol]
  constructor
  · intro h w hw
    have := h (φ w) (Finset.mem_map_of_mem _ hw)
    rwa [hφ] at this
  · intro h w' hw'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hw'
    rw [Equiv.coe_toEmbedding, hφ]
    exact h w hw

/-- `nM` counts the images of `mol` of the internal vertices; it is invariant under a bijection transporting `mol`. -/
private theorem lwExpSound_nM_map (A : LGraph E I) (B : LGraph E' I') (φ : E ⊕ I ≃ E' ⊕ I')
    (hmol : ∀ v, B.mol (φ v) = (A.mol v).map φ.toEmbedding) (hφ : ∀ v, (φ v).isRight = v.isRight) :
    B.nM = A.nM := by
  unfold LGraph.nM
  have himg : (Finset.univ.filter fun v' : E' ⊕ I' => ∀ w ∈ B.mol v', w.isRight = true).image B.mol =
      ((Finset.univ.filter fun v : E ⊕ I => ∀ w ∈ A.mol v, w.isRight = true).image A.mol).image
        (Finset.map φ.toEmbedding) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v', hv', rfl⟩
      obtain ⟨v, rfl⟩ := φ.surjective v'
      exact ⟨A.mol v, ⟨v, (lwExpSound_int_map A B φ hmol hφ v).1 hv', rfl⟩, (hmol v).symm⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨φ v, (lwExpSound_int_map A B φ hmol hφ v).2 hv, hmol v⟩
  rw [himg, Finset.card_image_of_injective _ (Finset.map_injective _)]
end Mol

/-- **`Rel` transports `Normal`, `n_M`, `LWAttached`, the molecule statements and `LWJoined`** (L6). -/
theorem relInvariance : RelInvariance := by
  intro N hs P h
  obtain ⟨eE, eI, he, hsol, hw, hd⟩ := h
  set φ : Fin (N.a + 1) ⊕ Fin N.b ≃ P.E' ⊕ P.I' := Equiv.sumCongr eE eI with hφ
  have hadj := lwExpSound_adj_map N.g P.g φ hw hd
  have hmol := lwExpSound_mol_map N.g P.g φ hadj
  have hmolOf : ∀ u v, P.g.molOf (φ u) = P.g.molOf (φ v) ↔ N.g.molOf u = N.g.molOf v := by
    intro u v
    rw [LGraph.molOf_eq_iff, LGraph.molOf_eq_iff, hmol, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  have hnM : P.g.nM = N.g.nM := lwExpSound_nM_map N.g P.g φ hmol (by rintro (a | a) <;> rfl)
  have hext : ∀ i, P.ext i = eE (N.ext i) := he
  have hφR : ∀ v, (φ v).isRight = v.isRight := by rintro (a | a) <;> rfl
  refine ⟨lwExpSound_normal_map N.g P.g φ hsol hd |>.symm, hnM, ?_, ?_, ?_⟩
  · have key : ∀ v : Fin N.b, ((∀ w ∈ P.g.mol (φ (Sum.inr v)), w.isRight = true) ↔ ∀ w ∈ N.g.mol (Sum.inr v), w.isRight = true) ∧
        (P.g.solid.filter fun e => decide (P.g.mol e.src ≠ P.g.mol e.dst ∧ (P.g.mol e.src = P.g.mol (φ (Sum.inr v)) ∨
          P.g.mol e.dst = P.g.mol (φ (Sum.inr v))))).length =
        (N.g.solid.filter fun e => decide (N.g.mol e.src ≠ N.g.mol e.dst ∧ (N.g.mol e.src = N.g.mol (Sum.inr v) ∨
          N.g.mol e.dst = N.g.mol (Sum.inr v)))).length := by
      intro v
      refine ⟨lwExpSound_int_map N.g P.g φ hmol hφR (Sum.inr v), ?_⟩
      rw [hsol, List.filter_map, List.length_map]
      congr 1
      refine List.filter_congr fun e _ => ?_
      refine decide_eq_decide.2 ?_
      change (P.g.mol (φ e.src) ≠ P.g.mol (φ e.dst) ∧ (P.g.mol (φ e.src) = P.g.mol (φ (Sum.inr v)) ∨
          P.g.mol (φ e.dst) = P.g.mol (φ (Sum.inr v)))) ↔ _
      simp only [hmol, Ne, Finset.map_inj]
    refine (Equiv.forall_congr eI fun v => ?_).symm
    exact imp_congr (key v).1.symm (Iff.of_eq (congrArg (fun n => 2 ≤ n) (key v).2.symm))
  · constructor
    · intro H a b hab
      exact eE.injective (H (eE a) (eE b) ((hmolOf (Sum.inl a) (Sum.inl b)).2 hab))
    · intro H a' b' hab
      obtain ⟨a, rfl⟩ := eE.surjective a'
      obtain ⟨b, rfl⟩ := eE.surjective b'
      exact congrArg eE (H a b ((hmolOf (Sum.inl a) (Sum.inl b)).1 hab))
  · unfold LWJoined
    change (P.ext 0 ≠ P.ext 1 ∧ P.g.molOf (Sum.inl (P.ext 0)) = P.g.molOf (Sum.inl (P.ext 1)) ∧ P.g.nM = 0) ↔
      (N.ext 0 ≠ N.ext 1 ∧ N.g.molOf (Sum.inl (N.ext 0)) = N.g.molOf (Sum.inl (N.ext 1)) ∧ N.g.nM = 0)
    rw [hext 0, hext 1, hnM, eE.injective.ne_iff]
    exact and_congr Iff.rfl (and_congr (hmolOf (Sum.inl (N.ext 0)) (Sum.inl (N.ext 1))) Iff.rfl)

/-! ## 2. `RelKids` (L5'): candidates and children along `Rel` -/

/-- The converse of `cands_spec`: the data of a candidate in the shape of `LWG5Cand` is a listed candidate. -/
private theorem lwExpSound_mem_cands {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin b)) (x : Fin b) (y y' : Fin (a+1) ⊕ Fin b)
    (p q : SEdge (Fin (a+1) ⊕ Fin b) × List (SEdge (Fin (a+1) ⊕ Fin b)))
    (hp : p ∈ lwSplit g.solid) (hq : q ∈ lwSplit p.2) (hy : y ≠ Sum.inr x) (hy' : y' ≠ Sum.inr x)
    (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩) (hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩) :
    (⟨x, y, y', p, q⟩ : Cand a b) ∈ cands g := by
  unfold cands
  rw [List.mem_flatMap]
  refine ⟨p, hp, ?_⟩
  rw [hp1]
  simp only [hy, ne_eq, not_false_eq_true, decide_true, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.true_and]
  rw [List.mem_filterMap]
  refine ⟨q, hq, ?_⟩
  rw [hq1]
  simp [hy']

/-- A candidate of a packed graph related to the model node `N` comes from a listed candidate of `N`. -/
private theorem lwExpSound_cand_of_rel {N : MNode} {P : PGraph (Fin 2)} (eE : Fin (N.a + 1) ≃ P.E')
    (eI : Fin N.b ≃ P.I') (hsol : P.g.solid = N.g.solid.map (SEdge.map (Sum.map eE eI))) (c' : RCand P) :
    ∃ c : Cand N.a N.b, c ∈ cands N.g ∧ c'.x = eI c.x ∧ c'.y = Sum.map eE eI c.y ∧ c'.y' = Sum.map eE eI c.y' ∧
      c'.q.2 = c.q.2.map (SEdge.map (Sum.map eE eI)) := by
  set φ : Fin (N.a + 1) ⊕ Fin N.b ≃ P.E' ⊕ P.I' := Equiv.sumCongr eE eI with hφ
  have hp := c'.hp
  rw [hsol, lwSplit_map] at hp
  obtain ⟨p₀, hp₀, hpe⟩ := List.mem_map.1 hp
  have hq := c'.hq
  rw [← hpe, lwSplit_map] at hq
  obtain ⟨q₀, hq₀, hqe⟩ := List.mem_map.1 hq
  have hp1 := c'.hp1
  rw [← hpe] at hp1
  have hq1 := c'.hq1
  rw [← hqe] at hq1
  simp only [SEdge.map, SEdge.mk.injEq] at hp1 hq1
  obtain ⟨hσ, hcirc, hsrc, hdst⟩ := hp1
  obtain ⟨hσ', hcirc', hsrc', hdst'⟩ := hq1
  have hp₁ : p₀.1 = ⟨true, false, Sum.inr (eI.symm c'.x), φ.symm c'.y⟩ := by
    have h1 : p₀.1 = ⟨p₀.1.σ, p₀.1.circ, p₀.1.src, p₀.1.dst⟩ := rfl
    rw [hσ, hcirc, φ.eq_symm_apply.2 hsrc, φ.eq_symm_apply.2 hdst] at h1
    rw [h1, hφ]
    simp
  have hq₁ : q₀.1 = ⟨true, false, φ.symm c'.y', Sum.inr (eI.symm c'.x)⟩ := by
    have h1 : q₀.1 = ⟨q₀.1.σ, q₀.1.circ, q₀.1.src, q₀.1.dst⟩ := rfl
    rw [hσ', hcirc', φ.eq_symm_apply.2 hsrc', φ.eq_symm_apply.2 hdst'] at h1
    rw [h1, hφ]
    simp
  have hy : φ.symm c'.y ≠ Sum.inr (eI.symm c'.x) := fun h => c'.hy (by simpa [hφ] using congrArg φ h)
  have hy' : φ.symm c'.y' ≠ Sum.inr (eI.symm c'.x) := fun h => c'.hy' (by simpa [hφ] using congrArg φ h)
  refine ⟨⟨eI.symm c'.x, φ.symm c'.y, φ.symm c'.y', p₀, q₀⟩,
    lwExpSound_mem_cands N.g _ _ _ p₀ q₀ hp₀ hq₀ hy hy' hp₁ hq₁, by simp, by simp [hφ], by simp [hφ], ?_⟩
  rw [← hqe]

private theorem lwExpSound_cls_congr {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (D₁ D₂ : LGraph E I) (h : D₁.dotted = D₂.dotted) (u v : E ⊕ I) :
    D₁.cls u = D₁.cls v ↔ D₂.cls u = D₂.cls v := by
  have : D₁.EqRel = D₂.EqRel := by funext u v; simp only [LGraph.EqRel, h]
  rw [show D₁.cls u = D₁.cls v ↔ Relation.EqvGen D₁.EqRel u v from Quotient.eq,
    show D₂.cls u = D₂.cls v ↔ Relation.EqvGen D₂.EqRel u v from Quotient.eq, this]

/-- `Rl ρ Γ Δ`: the graph `Δ` is the graph `Γ` renamed by `ρ`, up to the colours of the waved edges and the coefficient. -/
private def lwExpSound_Rl {E₁ I₁ E₂ I₂ : Type} (ρ : E₁ ⊕ I₁ → E₂ ⊕ I₂) (Γ : LGraph E₁ I₁) (Δ : LGraph E₂ I₂) : Prop :=
  Δ.solid = Γ.solid.map (SEdge.map ρ) ∧ Δ.dotted = Γ.dotted.map (DEdge.map ρ) ∧
    Δ.waved.map (fun e => (e.x, e.y)) = Γ.waved.map (fun e => (ρ e.x, ρ e.y))
private theorem lwExpSound_dotChoices_congr {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (A B : LGraph E I) (hs : A.solid = B.solid) (hd : A.dotted = B.dotted) : A.dotChoices = B.dotChoices := by
  cases A; cases B; simp only at hs hd; subst hs hd; rfl
private theorem lwExpSound_dotBase_congr {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (A B : LGraph E I) (hs : A.solid = B.solid) (hd : A.dotted = B.dotted) : A.dotBase = B.dotBase := by
  cases A; cases B; simp only at hs hd; subst hs hd; rfl
private theorem lwExpSound_consistent_congr {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (A B : LGraph E I) (h : A.dotted = B.dotted) : A.Consistent ↔ B.Consistent := by
  unfold LGraph.Consistent
  rw [h]
  exact forall₂_congr fun e _ => imp_congr_right fun _ => not_congr (lwExpSound_cls_congr A B h e.x e.y)

section Sim

variable (N : MNode) (P : PGraph (Fin 2)) (eE : Fin (N.a + 1) ≃ P.E') (hext : ∀ i, P.ext i = eE (N.ext i)) {b' : ℕ}
  {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  (τ : Fin (N.a + 1) ⊕ I ≃ Fin (N.a + 1) ⊕ Fin b') (hτ : ∀ a, τ (Sum.inl a) = Sum.inl a)
  (ρ : Fin (N.a + 1) ⊕ I ≃ P.E' ⊕ I') (hρ : ∀ a, ρ (Sum.inl a) = Sum.inl (eE a))
include hext hτ hρ

/-- **One dotted term against the model merge, with a general real graph** (the generalisation of `lwExpSim_term_some`
to a real graph `D` that is the relabelling of the model base `Dg` by `ρ`, up to the colours of the waved edges). -/
private theorem lwExpSound_term_some (Dg : LGraph (Fin (N.a + 1)) I) (D : LGraph P.E' I')
    (hs : D.solid = Dg.solid.map (SEdge.map ρ)) (hd : D.dotted = Dg.dotted.map (DEdge.map ρ))
    (hw : D.waved.map (fun e => (e.x, e.y)) = Dg.waved.map (fun e => (ρ e.x, ρ e.y))) (hC : Dg.Consistent) :
    ∃ N', cMerge (Dg.relabel τ) N.ext = some N' ∧
      List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (q : (ℕ × ℕ) × PGraph P.E') => Rel r.2 (pcomp P q.2) ∧ r.1 = q.1)
        (lwExpSim_model N') (lwExpSim_real D) := by
  obtain ⟨N', hN', ψ, hP1, hP2, hP3, hsol, hwav, hdot, hcoe, hext'⟩ :=
    lwExpSim_cMerge_some (Dg.relabel τ) N.ext ((lwExpSim_consistent_relabel Dg τ).2 hC)
  have hDcls : ∀ u v, D.cls u = D.cls v ↔ Dg.cls (ρ.symm u) = Dg.cls (ρ.symm v) := by
    intro u v
    rw [lwExpSound_cls_congr D (Dg.relabel ρ) (by rw [hd]; rfl)]
    obtain ⟨x, rfl⟩ := ρ.surjective u
    obtain ⟨y, rfl⟩ := ρ.surjective v
    rw [lwExpSim_cls_relabel, ρ.symm_apply_apply, ρ.symm_apply_apply]
  obtain ⟨eE', eI', hvm⟩ := lwExpSim_equivs D (fun v => ψ (τ (ρ.symm v)))
    (fun u v => by rw [hP1, lwExpSim_cls_relabel, hDcls])
    (hP2.comp (τ.surjective.comp ρ.symm.surjective))
    (fun v => by
      rw [hP3 (τ (ρ.symm v))]
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨eE a, ?_⟩
        rw [hDcls, show (Sum.inl (eE a) : P.E' ⊕ I') = ρ (Sum.inl a) from (hρ a).symm, ρ.symm_apply_apply]
        exact (lwExpSim_cls_relabel Dg τ (Sum.inl a) (ρ.symm v)).1 (by rwa [hτ])
      · rintro ⟨a', ha'⟩
        refine ⟨eE.symm a', ?_⟩
        rw [← hτ, lwExpSim_cls_relabel]
        rw [hDcls] at ha'
        have : (Sum.inl (eE.symm a') : Fin (N.a + 1) ⊕ I) = ρ.symm (Sum.inl a') :=
          ρ.eq_symm_apply.2 (by rw [hρ]; simp)
        rwa [← this] at ha')
  refine ⟨N', hN', ?_⟩
  have hψ' : Function.Injective (Sum.map eE' eI') := (Equiv.sumCongr eE' eI').injective
  have hvm' : ∀ x, D.vmap (ρ x) = Sum.map eE' eI' (ψ (τ x)) := fun x => by rw [hvm, ρ.symm_apply_apply]
  have hs' : D.merge.solid = N'.g.solid.map (SEdge.map (Sum.map eE' eI')) := by
    rw [hsol]
    simp only [LGraph.merge, LGraph.relabel, hs, List.map_map]
    exact List.map_congr_left fun e _ => by simp [SEdge.map, hvm']
  have hw' : D.merge.waved.map (fun e => (e.x, e.y)) =
      N'.g.waved.map (fun e => (Sum.map eE' eI' e.x, Sum.map eE' eI' e.y)) := by
    rw [hwav]
    simp only [LGraph.merge, LGraph.relabel, List.map_map]
    have h1 : List.map ((fun e : WEdge (D.ExtCls ⊕ D.IntCls) => (e.x, e.y)) ∘ WEdge.map D.vmap) D.waved =
        (D.waved.map (fun e => (e.x, e.y))).map (fun p => (D.vmap p.1, D.vmap p.2)) := by
      rw [List.map_map]; rfl
    rw [h1, hw, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp [hvm', WEdge.map]
  have hd' : D.merge.dotted = N'.g.dotted.map (DEdge.map (Sum.map eE' eI')) := by
    rw [hdot]
    simp only [LGraph.merge, LGraph.relabel, hd, List.filter_map, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp [DEdge.map, hvm']
  unfold lwExpSim_model lwExpSim_real
  rw [hs', lwExpSim_splitLoopsX_map _ hψ', List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  intro r _
  refine ⟨⟨eE', eI', fun i => ?_, rfl, ?_, ?_⟩, rfl⟩
  · have h1 := hvm (Sum.inl (P.ext i))
    rw [lwExpSim_vmap_inl] at h1
    have h2 : ρ.symm (Sum.inl (P.ext i)) = Sum.inl (N.ext i) := ρ.symm_apply_eq.2 (by rw [hρ, hext])
    simp only [h2, hτ, hext', Sum.map_inl] at h1
    exact Sum.inl.inj h1
  · exact hw'
  · exact hd'

/-- **The partition of a graph that is a relabelling of the model base, against `cPartitionX` of the renumbered model**. -/
private theorem lwExpSound_partition_sim (Γ : LGraph (Fin (N.a + 1)) I) (Δ : LGraph P.E' I')
    (hs : Δ.solid = Γ.solid.map (SEdge.map ρ)) (hd : Δ.dotted = Γ.dotted.map (DEdge.map ρ))
    (hw : Δ.waved.map (fun e => (e.x, e.y)) = Γ.waved.map (fun e => (ρ e.x, ρ e.y))) :
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (q : (ℕ × ℕ) × PGraph P.E') => Rel r.2 (pcomp P q.2) ∧ r.1 = q.1)
      (cPartitionX (Γ.relabel τ) N.ext) (partitionX Δ) := by
  classical
  have hch : Δ.dotChoices = Γ.dotChoices.map fun t => (t.1, t.2.map (DEdge.map ρ)) := by
    rw [lwExpSound_dotChoices_congr Δ (Γ.relabel ρ) hs hd, lwExpSim_dotChoices_relabel]
  have hbase : Δ.dotBase = Γ.dotBase.map (DEdge.map ρ) := by
    rw [lwExpSound_dotBase_congr Δ (Γ.relabel ρ) hs hd, lwExpSim_dotBase_relabel]
  unfold cPartitionX partitionX LGraph.partitionTerms
  rw [lwExpSim_terms_relabel, List.flatMap_map, List.flatMap_map, hch, List.map_map, List.filter_map, List.flatMap_map]
  refine lwExpSim_forall₂_flatMap _ _ _ _ _ fun t _ => ?_
  have hD : ∀ t : ℤ × List (DEdge (Fin (N.a + 1) ⊕ I)), (Δ.withDots (t.1, t.2.map (DEdge.map ρ))).dotted =
      (Γ.withDots t).dotted.map (DEdge.map ρ) := by
    intro t
    simp only [LGraph.withDots, hbase, List.map_append]
  have hCt : (Δ.withDots (t.1, t.2.map (DEdge.map ρ))).Consistent ↔ (Γ.withDots t).Consistent := by
    rw [lwExpSound_consistent_congr _ ((Γ.withDots t).relabel ρ) (hD t), lwExpSim_consistent_relabel]
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have hC : (Γ.withDots t).Consistent := hCt.1 (of_decide_eq_true hp)
    obtain ⟨N', hN', hF⟩ := lwExpSound_term_some N P eE hext τ hτ ρ hρ (Γ.withDots t) (Δ.withDots (t.1, t.2.map (DEdge.map ρ)))
      hs (hD t) hw hC
    simp only [Function.comp_apply, hN']
    exact hF
  · have hC : ¬ (Γ.withDots t).Consistent := fun h => of_decide_eq_false hp (hCt.2 h)
    simp only [Function.comp_apply, lwExpSim_cMerge_none _ _ (fun hc => hC ((lwExpSim_consistent_relabel _ τ).1 hc))]

/-- One family: the model partition of the renumbered graph against the real partition, with the shift `j` of `m`. -/
private theorem lwExpSound_block (Γ : LGraph (Fin (N.a + 1)) I) (Δ : LGraph P.E' I') (h : lwExpSound_Rl ρ Γ Δ) (j : ℕ) :
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
      ((cPartitionX (Γ.relabel τ) N.ext).map fun r => ((r.1.1 + j, r.1.2 + 0), r.2))
      ((partitionX Δ).map fun r => ((r.1.1 + j, r.1.2), pcomp P r.2)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine (lwExpSound_partition_sim N P eE hext τ hτ ρ hρ Γ Δ h.1 h.2.1 h.2.2).imp fun r q hq => ⟨hq.1, ?_⟩
  change (r.1.1 + j, r.1.2 + 0) = (q.1.1 + j, q.1.2)
  rw [← hq.2]
  rfl
end Sim

private theorem lwExpSound_Rl_owxExt {E₁ I₁ E₂ I₂ J₁ J₂ : Type} (ρ0 : E₁ ⊕ I₁ → E₂ ⊕ I₂) (ρ1 : E₁ ⊕ J₁ → E₂ ⊕ J₂)
    (Γ : LGraph E₁ I₁) (Δ : LGraph E₂ I₂) (h : lwExpSound_Rl ρ0 Γ Δ)
    (emb : E₁ ⊕ I₁ → E₁ ⊕ J₁) (emb' : E₂ ⊕ I₂ → E₂ ⊕ J₂) (hemb : ∀ v, ρ1 (emb v) = emb' (ρ0 v))
    (c c' : ℂ) (s : List (SEdge (E₁ ⊕ J₁))) (w : List (WEdge (E₁ ⊕ J₁)))
    (s' : List (SEdge (E₂ ⊕ J₂))) (w' : List (WEdge (E₂ ⊕ J₂)))
    (hs' : s' = s.map (SEdge.map ρ1)) (hw' : w'.map (fun e => (e.x, e.y)) = w.map (fun e => (ρ1 e.x, ρ1 e.y))) :
    lwExpSound_Rl ρ1 (Γ.owxExt emb c s w) (Δ.owxExt emb' c' s' w') := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [LGraph.owxExt, h1, hs', List.map_append, List.map_map]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp [SEdge.map, hemb]
  · simp only [LGraph.owxExt, h2, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp [DEdge.map, hemb]
  · have e1 : (Δ.waved.map (WEdge.map emb')).map (fun e => (e.x, e.y)) =
        (Δ.waved.map (fun e => (e.x, e.y))).map (fun p => (emb' p.1, emb' p.2)) := by
      rw [List.map_map, List.map_map]; rfl
    simp only [LGraph.owxExt, List.map_append]
    rw [e1, h3, hw', List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp [WEdge.map, hemb]

section Fam

variable {N : MNode} {P : PGraph (Fin 2)} (eE : Fin (N.a + 1) ≃ P.E') (eI : Fin N.b ≃ P.I')

private theorem lwExpSound_hemb' (k : ℕ) (v : Fin (N.a + 1) ⊕ Fin N.b) :
    Sum.map (⇑eE) (⇑(Equiv.sumCongr eI (Equiv.refl (Fin k)))) (owxEmb k v) = owxEmb k (Sum.map eE eI v) := by
  rcases v with a | z <;> rfl
/-- The families `R2`, `R4`, `R5`, `R6` (and `R3`) of a related candidate are the model families renamed. -/
private theorem lwExpSound_fam2 {c : Cand N.a N.b} {c' : RCand P}
    (hx : c'.x = eI c.x) (hy : c'.y = Sum.map eE eI c.y) (hy' : c'.y' = Sum.map eE eI c.y')
    (hq : c'.q.2 = c.q.2.map (SEdge.map (Sum.map eE eI))) (h : lwExpSound_Rl (Sum.map eE eI) N.g P.g) :
    lwExpSound_Rl (Sum.map eE eI) (oe2xR2 1 N.g c.q c.x c.y c.y') (oe2xR2 1 P.g c'.q c'.x c'.y c'.y') ∧
    lwExpSound_Rl (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 1)))) (owxT1 1 N.g c.x) (owxT1 1 P.g c'.x) ∧
    lwExpSound_Rl (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 2))))
      (oe2xR4 1 N.g c.q c.x c.y c.y') (oe2xR4 1 P.g c'.q c'.x c'.y c'.y') ∧
    lwExpSound_Rl (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 1))))
      (oe2xR5 1 N.g c.q c.x c.y c.y') (oe2xR5 1 P.g c'.q c'.x c'.y c'.y') ∧
    lwExpSound_Rl (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 2))))
      (oe2xR6 1 N.g c.q c.x c.y c.y') (oe2xR6 1 P.g c'.q c'.x c'.y c'.y') := by
  have hb : lwExpSound_Rl (Sum.map eE eI) ({ N.g with solid := c.q.2 } : LGraph _ _) ({ P.g with solid := c'.q.2 } : LGraph _ _) :=
    ⟨hq, h.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold oe2xR2
    refine lwExpSound_Rl_owxExt (Sum.map eE eI) _ _ _ hb id id (fun v => rfl) _ _ _ _ _ _ ?_ ?_
    · simp [SEdge.map, hy, hy']
    · simp [hx, hy]
  · unfold owxT1
    refine lwExpSound_Rl_owxExt (Sum.map eE eI) _ _ _ h _ _ (fun v => lwExpSound_hemb' eE eI 1 v) _ _ _ _ _ _ ?_ ?_
    · simp [SEdge.map]
    · simp [hx]
  · unfold oe2xR4
    refine lwExpSound_Rl_owxExt (Sum.map eE eI) _ _ _ hb _ _ (fun v => lwExpSound_hemb' eE eI 2 v) _ _ _ _ _ _ ?_ ?_
    · simp [SEdge.map, hy, hy', hx, lwExpSound_hemb' eE eI]
    · simp [hx]
  · unfold oe2xR5
    refine lwExpSound_Rl_owxExt (Sum.map eE eI) _ _ _ hb _ _ (fun v => lwExpSound_hemb' eE eI 1 v) _ _ _ _ _ _ ?_ ?_
    · simp [SEdge.map, hy, hy', hx, lwExpSound_hemb' eE eI]
    · simp [hx]
  · unfold oe2xR6
    refine lwExpSound_Rl_owxExt (Sum.map eE eI) _ _ _ hb _ _ (fun v => lwExpSound_hemb' eE eI 2 v) _ _ _ _ _ _ ?_ ?_
    · simp [SEdge.map, hy, hy', hx, lwExpSound_hemb' eE eI]
    · simp [hx]

/-- The families `R7`, `R8` of a related candidate, at a solid edge `q'` of `f` and its image. -/
private theorem lwExpSound_fam78 {c : Cand N.a N.b} {c' : RCand P}
    (hx : c'.x = eI c.x) (hy : c'.y = Sum.map eE eI c.y) (hy' : c'.y' = Sum.map eE eI c.y')
    (h : lwExpSound_Rl (Sum.map eE eI) N.g P.g) (q' : SEdge (Fin (N.a + 1) ⊕ Fin N.b) × List (SEdge (Fin (N.a + 1) ⊕ Fin N.b))) :
    lwExpSound_Rl (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 1))))
      (oe2xR7 1 N.g c.x c.y c.y' q')
      (oe2xR7 1 P.g c'.x c'.y c'.y' (SEdge.map (Sum.map eE eI) q'.1, q'.2.map (SEdge.map (Sum.map eE eI)))) ∧
    lwExpSound_Rl (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin 2))))
      (oe2xR8 1 N.g c.x c.y c.y' q')
      (oe2xR8 1 P.g c'.x c'.y c'.y' (SEdge.map (Sum.map eE eI) q'.1, q'.2.map (SEdge.map (Sum.map eE eI)))) := by
  have hb : lwExpSound_Rl (Sum.map eE eI) ({ N.g with solid := q'.2 } : LGraph _ _)
      ({ P.g with solid := q'.2.map (SEdge.map (Sum.map eE eI)) } : LGraph _ _) := ⟨rfl, h.2⟩
  refine ⟨?_, ?_⟩
  · unfold oe2xR7
    refine lwExpSound_Rl_owxExt (Sum.map eE eI) _ _ _ hb _ _ (fun v => lwExpSound_hemb' eE eI 1 v) _ _ _ _ _ _ ?_ ?_
    · cases hσ : q'.1.σ <;> simp [owxDE, SEdge.map, hσ, hy, hy', hx, lwExpSound_hemb' eE eI]
    · simp [hx]
  · unfold oe2xR8
    refine lwExpSound_Rl_owxExt (Sum.map eE eI) _ _ _ hb _ _ (fun v => lwExpSound_hemb' eE eI 2 v) _ _ _ _ _ _ ?_ ?_
    · cases hσ : q'.1.σ <;> simp [owxDE, SEdge.map, hσ, hy, hy', hx, lwExpSound_hemb' eE eI]
    · simp [hx]
end Fam

/-- **`RelKids` (Bridge 2 along `Rel`)**: the real children of any packed graph related to a model node, at any of its
candidates, are the model children at a listed model candidate. -/
theorem relKids : RelKids := by
  intro N P h c'
  obtain ⟨eE, eI, hext, hsol, hw, hd⟩ := h
  obtain ⟨c, hc, hx, hy, hy', hq⟩ := lwExpSound_cand_of_rel eE eI hsol c'
  refine ⟨c, hc, ?_⟩
  have hRl : lwExpSound_Rl (Sum.map eE eI) N.g P.g := ⟨hsol, hd, hw⟩
  obtain ⟨f2, f3, f4, f5, f6⟩ := lwExpSound_fam2 eE eI hx hy hy' hq hRl
  have e1 : ∀ {k : ℕ} (Γ : LGraph (Fin (N.a + 1)) (Fin N.b ⊕ Fin k)) (Δ : LGraph P.E' (P.I' ⊕ Fin k)) (j : ℕ),
      lwExpSound_Rl (Equiv.sumCongr eE (Equiv.sumCongr eI (Equiv.refl (Fin k)))) Γ Δ →
      List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
        ((cPartitionX (renum Γ) N.ext).map fun r => ((r.1.1 + j, r.1.2 + 0), r.2))
        ((partitionX Δ).map fun r => ((r.1.1 + j, r.1.2), pcomp P r.2)) :=
    fun Γ Δ j hΓΔ => lwExpSound_block N P eE hext (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv) (fun a => rfl) _
      (fun a => rfl) Γ Δ hΓΔ j
  have e0 := lwExpSound_block N P eE hext (Equiv.sumCongr (Equiv.refl _) (Equiv.refl (Fin N.b))) (fun a => rfl)
    (Equiv.sumCongr eE eI) (fun a => rfl) _ _ f2 3
  rw [lwExpSim_relabel_refl] at e0
  unfold childrenX famsX RCand.kids
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_assoc,
    List.append_assoc]
  rw [hq, lwSplit_map, List.flatMap_map]
  exact List.rel_append e0 (List.rel_append (e1 _ _ 1 f3) (List.rel_append (e1 _ _ 3 f4) (List.rel_append (e1 _ _ 1 f5)
    (List.rel_append (e1 _ _ 3 f6) (lwExpSim_forall₂_flatMap_same _ _ _ _ fun q' _ =>
      List.rel_append (e1 _ _ 1 (lwExpSound_fam78 eE eI hx hy hy' hRl q').1)
        (e1 _ _ 3 (lwExpSound_fam78 eE eI hx hy hy' hRl q').2))))))

/-! ## 3. `BelowOfSound` (L7): the fold of `belowOf'` -/

section Fold

/-- The pieces of the body of `belowOf'` (`LWExpCertB.lean:56-72`) as functions of the label list of one term. -/
private def lwExpSound_B (a : ℕ) (labs : List ℕ) : ℤ := ((repsOf labs).filter (· ≥ a + 1)).length
private def lwExpSound_L (S : List (Bool × ℕ × ℕ)) (labs : List ℕ) : ℤ :=
  (S.filter fun e => !e.1 && labs.getD e.2.1 0 == labs.getD e.2.2 0).length
private def lwExpSound_tg (labs : List ℕ) (x0 y0 : ℕ) : ℤ := if labs.getD x0 0 == labs.getD y0 0 then 4 else 5
private def lwExpSound_ok0 (a b : ℕ) (S : List (Bool × ℕ × ℕ)) (W : List (ℕ × ℕ)) (nS nW : ℤ) (x0 y0 : ℕ)
    (labs : List ℕ) : Bool :=
  let n := a + 1 + b
  if nS + 2 * (nW - lwExpSound_B a labs) ≥ lwExpSound_tg labs x0 y0 then
    let mol := W.foldl (fun l e => unite l e.1 e.2) labs
    let nMc := ((List.range n).filter fun i => i ≥ a + 1 && mol.getD i 0 == i).length
    nMc ≤ 1 && nW ≥ 2 &&
    ((List.range n).filter fun i => i ≥ a + 1 && mol.getD i 0 == i).all (fun i =>
      2 ≤ (S.filter fun e => mol.getD e.2.1 0 != mol.getD e.2.2 0 && (mol.getD e.2.1 0 == i || mol.getD e.2.2 0 == i)).length) &&
    (labs.getD x0 0 == labs.getD y0 0 || mol.getD x0 0 != mol.getD y0 0 || nMc == 0)
  else true

/-- One step of the fold of `belowOf'`. -/
private def lwExpSound_tpl (a b : ℕ) (S : List (Bool × ℕ × ℕ)) (W : List (ℕ × ℕ)) (nS nW : ℤ) (x0 y0 : ℕ)
    (labs : List ℕ) (skip : Bool) (cm : Option MNode) (acc : Bool × List MNode) : Bool × List MNode :=
  if skip then acc
  else if nS - lwExpSound_L S labs + 2 * (nW - lwExpSound_B a labs) ≥ lwExpSound_tg labs x0 y0 then
    (lwExpSound_ok0 a b S W nS nW x0 y0 labs && acc.1, acc.2)
  else match cm with
    | none => (lwExpSound_ok0 a b S W nS nW x0 y0 labs && acc.1, acc.2)
    | some N => (lwExpSound_ok0 a b S W nS nW x0 y0 labs && acc.1,
        ((N.g.splitWeights 1).map fun g => { N with g := g }).filter (fun M => !leaf M) ++ acc.2)

private def lwExpSound_labsC (Δ : LGraph (Fin (a+1)) (Fin b)) (c : ℤ × List (DEdge (Fin (a+1) ⊕ Fin b))) : List ℕ :=
  labsOf (a + 1 + b) (((Δ.dotted.filter fun e => e.eq).map (pairOf a b)) ++ ((c.2.filter fun e => e.eq).map (pairOf a b)))
private def lwExpSound_skipC (Δ : LGraph (Fin (a+1)) (Fin b)) (c : ℤ × List (DEdge (Fin (a+1) ⊕ Fin b))) : Bool :=
  (((Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)) ++ ((c.2.filter fun e => !e.eq).map (pairOf a b))).any
    (fun e => (lwExpSound_labsC Δ c).getD e.1 0 == (lwExpSound_labsC Δ c).getD e.2 0)
private theorem lwExpSound_below_eq (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)) :
    belowOf' Δ ext = Δ.dotChoices.foldr (fun c acc => lwExpSound_tpl a b
      (Δ.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst)) (Δ.waved.map fun e => (vi a b e.x, vi a b e.y))
      Δ.solid.length Δ.waved.length (vi a b (Sum.inl (ext 0))) (vi a b (Sum.inl (ext 1)))
      (lwExpSound_labsC Δ c) (lwExpSound_skipC Δ c) (cMerge (Δ.withDots c) ext) acc) (true, []) := rfl

variable {S : List (Bool × ℕ × ℕ)} {W : List (ℕ × ℕ)} {nS nW : ℤ} {x0 y0 : ℕ}

private theorem lwExpSound_tpl_fst {a b : ℕ} {labs : List ℕ} {skip : Bool} {cm : Option MNode} {acc : Bool × List MNode}
    (h : (lwExpSound_tpl a b S W nS nW x0 y0 labs skip cm acc).1 = true) :
    acc.1 = true ∧ (skip = false → lwExpSound_ok0 a b S W nS nW x0 y0 labs = true) := by
  unfold lwExpSound_tpl at h
  by_cases hs : skip = true
  · simp only [hs, ↓reduceIte] at h
    exact ⟨h, by simp [hs]⟩
  · rw [Bool.not_eq_true] at hs
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with h1
    · simp only [Bool.and_eq_true] at h; exact ⟨h.2, fun _ => h.1⟩
    · cases cm <;> simp only [Bool.and_eq_true] at h <;> exact ⟨h.2, fun _ => h.1⟩

private theorem lwExpSound_tpl_snd {a b : ℕ} {labs : List ℕ} {skip : Bool} {cm : Option MNode} {acc : Bool × List MNode} :
    (∀ M ∈ acc.2, M ∈ (lwExpSound_tpl a b S W nS nW x0 y0 labs skip cm acc).2) ∧
    (skip = false → ¬ (nS - lwExpSound_L S labs + 2 * (nW - lwExpSound_B a labs) ≥ lwExpSound_tg labs x0 y0) →
      ∀ N, cm = some N → ∀ M ∈ ((N.g.splitWeights 1).map fun g => { N with g := g }).filter (fun M => !leaf M),
        M ∈ (lwExpSound_tpl a b S W nS nW x0 y0 labs skip cm acc).2) := by
  unfold lwExpSound_tpl
  by_cases hs : skip = true
  · simp [hs]
  · rw [Bool.not_eq_true] at hs
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1
    · exact ⟨fun M hM => hM, fun _ h => absurd h1 h⟩
    · cases cm <;> simp_all

/-- The fold of `belowOf'` (`foldr` of the step over any list of choices). -/
private theorem lwExpSound_fold {a b : ℕ} {α : Type} (labs : α → List ℕ) (sk : α → Bool) (cm : α → Option MNode)
    (cs : List α) :
    ((cs.foldr (fun c acc => lwExpSound_tpl a b S W nS nW x0 y0 (labs c) (sk c) (cm c) acc) (true, [])).1 = true →
      ∀ c ∈ cs, sk c = false → lwExpSound_ok0 a b S W nS nW x0 y0 (labs c) = true) ∧
    ∀ c ∈ cs, sk c = false → ¬ (nS - lwExpSound_L S (labs c) + 2 * (nW - lwExpSound_B a (labs c)) ≥
        lwExpSound_tg (labs c) x0 y0) → ∀ N, cm c = some N →
      ∀ M ∈ ((N.g.splitWeights 1).map fun g => { N with g := g }).filter (fun M => !leaf M),
        M ∈ (cs.foldr (fun c acc => lwExpSound_tpl a b S W nS nW x0 y0 (labs c) (sk c) (cm c) acc) (true, [])).2 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldr_cons]
    refine ⟨fun h d hd hsk => ?_, fun d hd hsk hcov N hN M hM => ?_⟩
    · obtain ⟨h1, h2⟩ := lwExpSound_tpl_fst h
      rcases List.mem_cons.1 hd with rfl | hd
      · exact h2 hsk
      · exact ih.1 h1 d hd hsk
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact (lwExpSound_tpl_snd (S := S) (W := W) (nS := nS) (nW := nW) (x0 := x0) (y0 := y0)).2 hsk hcov N hN M hM
      · exact (lwExpSound_tpl_snd (S := S) (W := W) (nS := nS) (nW := nW) (x0 := x0) (y0 := y0)).1 M (ih.2 d hd hsk hcov N hN M hM)
end Fold

/-! ## 4. One term: the molecules of the merge -/

section Term

variable {a b : ℕ}

/-- The data of the merge of the term `D` (`lwExpSim_cMerge_some`). -/
private structure lwExpSound_MD (D : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)) (N' : MNode) where
  ψ : Fin (a+1) ⊕ Fin b → Fin (N'.a + 1) ⊕ Fin N'.b
  h1 : ∀ u v, ψ u = ψ v ↔ D.cls u = D.cls v
  h2 : Function.Surjective ψ
  h3 : ∀ v, (∃ j, ψ v = Sum.inl j) ↔ D.IsExtCls (D.cls v)
  hsol : N'.g.solid = D.solid.map (SEdge.map ψ)
  hwav : N'.g.waved = D.waved.map (WEdge.map ψ)
  hdot : N'.g.dotted = (D.dotted.filter fun e => !e.eq).map (DEdge.map ψ)
  hext : ∀ i, ψ (Sum.inl (ext i)) = Sum.inl (N'.ext i)

private theorem lwExpSound_md {D : LGraph (Fin (a+1)) (Fin b)} (ext : Fin 2 → Fin (a+1)) (hC : D.Consistent) :
    ∃ N', cMerge D ext = some N' ∧ Nonempty (lwExpSound_MD D ext N') := by
  obtain ⟨N', hN', ψ, h1, h2, h3, hs, hw, hd, -, he⟩ := lwExpSim_cMerge_some D ext hC
  exact ⟨N', hN', ⟨⟨ψ, h1, h2, h3, hs, hw, hd, he⟩⟩⟩

/-- `molOf` is the class of the equivalence relation generated by `adj`. -/
private theorem lwExpSound_molOf_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) (u v : E ⊕ I) : Γ.molOf u = Γ.molOf v ↔ Relation.EqvGen (fun x y => Γ.adj x y = true) u v := by
  unfold LGraph.molOf
  rw [SimpleGraph.ConnectedComponent.eq]
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Relation.EqvGen.refl _
    | cons h _ ih =>
      rw [LGraph.molGraph, SimpleGraph.fromRel_adj] at h
      exact Relation.EqvGen.trans _ _ _ (h.2.elim (fun h' => Relation.EqvGen.rel _ _ h') fun h' => Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h')) ih
  · intro h
    induction h with
    | rel x y h =>
      by_cases hxy : x = y
      · subst hxy; exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (by rw [LGraph.molGraph, SimpleGraph.fromRel_adj]; exact ⟨hxy, Or.inl h⟩)
    | refl x => exact SimpleGraph.Reachable.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

variable {D : LGraph (Fin (a+1)) (Fin b)} {ext : Fin 2 → Fin (a+1)} {N' : MNode}

/-- **The molecules of the merge are the images of the molecules of the term.** -/
private theorem lwExpSound_molOf (M : lwExpSound_MD D ext N') (u w : Fin (a+1) ⊕ Fin b) :
    N'.g.molOf (M.ψ u) = N'.g.molOf (M.ψ w) ↔ D.molOf u = D.molOf w := by
  rw [lwExpSound_molOf_iff, lwExpSound_molOf_iff]
  have hadj : ∀ x y, N'.g.adj x y = true ↔ ∃ e ∈ D.waved, (M.ψ e.x = x ∧ M.ψ e.y = y) ∨ (M.ψ e.x = y ∧ M.ψ e.y = x) := by
    intro x y
    rw [lwExpSound_adj_iff, M.hwav, M.hdot]
    simp only [List.mem_map, List.mem_filter, WEdge.map, DEdge.map]
    constructor
    · rintro (⟨_, ⟨e, he, rfl⟩, h⟩ | ⟨_, ⟨e, ⟨he, hq⟩, rfl⟩, hq', -⟩)
      · exact ⟨e, he, h⟩
      · simp at hq hq'; rw [hq] at hq'; exact absurd hq' (by simp)
    · rintro ⟨e, he, h⟩
      exact Or.inl ⟨_, ⟨e, he, rfl⟩, h⟩
  have hcls : ∀ u v, M.ψ u = M.ψ v → Relation.EqvGen (fun x y => D.adj x y = true) u v := by
    intro u v h
    have : Relation.EqvGen D.EqRel u v := Quotient.exact ((M.h1 u v).1 h)
    exact Relation.EqvGen.mono (fun x y hxy => (lwExpSound_adj_iff D x y).2 (Or.inr (by
      obtain ⟨e, he, hq, hh⟩ := hxy; exact ⟨e, he, hq, hh⟩))) _ _ this
  constructor
  · intro h
    have key : ∀ x' y', Relation.EqvGen (fun x y => N'.g.adj x y = true) x' y' → ∀ u w, M.ψ u = x' → M.ψ w = y' →
        Relation.EqvGen (fun x y => D.adj x y = true) u w := by
      intro x' y' hxy
      induction hxy with
      | rel x y hxy =>
        intro u w hu hw
        obtain ⟨e, he, h⟩ := (hadj x y).1 hxy
        have he' : Relation.EqvGen (fun x y => D.adj x y = true) e.x e.y :=
          Relation.EqvGen.rel _ _ ((lwExpSound_adj_iff D _ _).2 (Or.inl ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩))
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ((hcls u e.x (hu.trans h1.symm)).trans _ _ _ he').trans _ _ _ (hcls e.y w (h2.trans hw.symm))
        · exact ((hcls u e.y (hu.trans h2.symm)).trans _ _ _ he'.symm).trans _ _ _ (hcls e.x w (h1.trans hw.symm))
      | refl x => intro u w hu hw; exact hcls u w (hu.trans hw.symm)
      | symm x y _ ih => intro u w hu hw; exact (ih w u hw hu).symm
      | trans x y z _ _ ih1 ih2 =>
        intro u w hu hw
        obtain ⟨v, hv⟩ := M.h2 y
        exact (ih1 u v hu hv).trans _ _ _ (ih2 v w hv hw)
    exact key _ _ h u w rfl rfl
  · intro h
    induction h with
    | rel x y h =>
      rcases (lwExpSound_adj_iff D x y).1 h with ⟨e, he, h⟩ | ⟨e, he, hq, h⟩
      · exact Relation.EqvGen.rel _ _ ((hadj _ _).2 ⟨e, he, by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]⟩)
      · have : M.ψ x = M.ψ y := by
          rw [M.h1]
          exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨e, he, hq, h⟩)
        rw [this]; exact Relation.EqvGen.refl _
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

/-- A molecule of the merge is internal iff the molecule of the term is. -/
private theorem lwExpSound_int (M : lwExpSound_MD D ext N') (u : Fin (a+1) ⊕ Fin b) :
    (∀ w ∈ N'.g.mol (M.ψ u), w.isRight = true) ↔ ∀ w ∈ D.mol u, w.isRight = true := by
  rw [N'.g.forall_mol_isRight_iff, D.forall_mol_isRight_iff]
  refine not_congr ?_
  constructor
  · rintro ⟨a', ha'⟩
    obtain ⟨v, hv⟩ := M.h2 (Sum.inl a')
    obtain ⟨a, ha⟩ := (M.h3 v).1 ⟨a', hv⟩
    refine ⟨a, (lwExpSound_molOf M (Sum.inl a) u).1 ?_⟩
    rw [show M.ψ (Sum.inl a) = Sum.inl a' by rw [← hv]; exact (M.h1 _ _).2 ha, ha']
  · rintro ⟨a, ha⟩
    obtain ⟨j, hj⟩ := (M.h3 (Sum.inl a)).2 ⟨a, rfl⟩
    exact ⟨j, by rw [← hj]; exact (lwExpSound_molOf M _ _).2 ha⟩

/-- `mol` of `belowOf'`: the union-find of the `=`-edges extended by the waved pairs. -/
private def lwExpSound_mol (D : LGraph (Fin (a+1)) (Fin b)) : List ℕ :=
  (D.waved.map fun e => (vi a b e.x, vi a b e.y)).foldl (fun l e => unite l e.1 e.2) (lwExpSim_labs D)
private theorem lwExpSound_unite_waved : ∀ (W' : List (WEdge (Fin (a+1) ⊕ Fin b))) (labs : List ℕ)
    (r : Fin (a+1) ⊕ Fin b → Fin (a+1) ⊕ Fin b → Prop), lwExpSim_LabsGood a b labs r →
    lwExpSim_LabsGood a b ((W'.map fun e => (vi a b e.x, vi a b e.y)).foldl (fun l e => unite l e.1 e.2) labs)
      (fun u v => r u v ∨ ∃ e ∈ W', (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
  intro W'
  induction W' with
  | nil => intro labs r h; simpa using h
  | cons e W' ih =>
    intro labs r h
    have h1 := lwExpSim_good_unite h e.x e.y
      (r' := fun u v => r u v ∨ (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) (fun u v => Iff.rfl)
    have h2 := ih _ _ h1
    simp only [List.map_cons, List.foldl_cons]
    have : (fun u v => (r u v ∨ (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) ∨ ∃ e' ∈ W', (e'.x = u ∧ e'.y = v) ∨ (e'.x = v ∧ e'.y = u)) =
        (fun u v => r u v ∨ ∃ e' ∈ e :: W', (e'.x = u ∧ e'.y = v) ∨ (e'.x = v ∧ e'.y = u)) := by
      funext u v
      apply propext
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]
    rwa [this] at h2

/-- The labels `mol` are the least vertices of the molecules of the term. -/
private theorem lwExpSound_mol_good (D : LGraph (Fin (a+1)) (Fin b)) :
    (lwExpSound_mol D).length = a + 1 + b ∧ (∀ i < a + 1 + b, (lwExpSound_mol D).getD i 0 ≤ i) ∧
    (∀ i < a + 1 + b, (lwExpSound_mol D).getD ((lwExpSound_mol D).getD i 0) 0 = (lwExpSound_mol D).getD i 0) ∧
    ∀ u v, (lwExpSound_mol D).getD (vi a b u) 0 = (lwExpSound_mol D).getD (vi a b v) 0 ↔ D.molOf u = D.molOf v := by
  obtain ⟨h1, h2, h3, h4⟩ := lwExpSound_unite_waved D.waved _ _ (lwExpSim_labsOf_good (D.dotted.filter fun e => e.eq))
  refine ⟨h1, h2, h3, fun u v => ?_⟩
  rw [lwExpSound_molOf_iff]
  have hr : (fun u v => lwExpSim_R (D.dotted.filter fun e => e.eq) u v ∨ ∃ e ∈ D.waved, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) =
      fun x y => D.adj x y = true := by
    funext x y
    apply propext
    rw [lwExpSound_adj_iff, or_comm]
    simp only [lwExpSim_R, List.mem_filter, decide_eq_true_eq, and_assoc]
  exact (h4 u v).trans (by rw [hr])
end Term

/-! ## 5. The weight split -/

section Split

private def lwExpSound_isLoop {V : Type} [DecidableEq V] (e : SEdge V) : Bool := decide (e.src = e.dst ∧ e.circ = false)
private theorem lwExpSound_split_len {V : Type} [DecidableEq V] (es : List (SEdge V)) :
    ∀ r ∈ lwSplitLoopsX es, r.2.length ≤ es.length ∧ es.length ≤ r.2.length + (es.filter lwExpSound_isLoop).length := by
  induction es with
  | nil => simp [lwSplitLoopsX]
  | cons e es ih =>
    intro r hr
    simp only [lwSplitLoopsX, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    have := ih r' hr'
    by_cases h : e.src = e.dst ∧ e.circ = false
    · have hp : lwExpSound_isLoop e = true := by simpa [lwExpSound_isLoop] using h
      simp only [h, and_self, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [List.length_cons, List.filter_cons, hp, ↓reduceIte] <;> omega
    · have hp : lwExpSound_isLoop e = false := by simpa [lwExpSound_isLoop] using h
      simp only [h, ↓reduceIte, List.mem_singleton] at hr
      subst hr; simp only [List.length_cons, List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]; omega

private theorem lwExpSound_split_filter {V : Type} [DecidableEq V] (es : List (SEdge V)) (p : SEdge V → Bool)
    (hp : ∀ e, e.src = e.dst → p e = false) :
    ∀ r ∈ lwSplitLoopsX es, (r.2.filter p).length = (es.filter p).length := by
  induction es with
  | nil => simp [lwSplitLoopsX]
  | cons e es ih =>
    intro r hr
    simp only [lwSplitLoopsX, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    by_cases h : e.src = e.dst ∧ e.circ = false
    · have hpe := hp e h.1
      simp only [h, and_self, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · have hpc : ∀ (σ : Bool) (x : V), p ⟨σ, true, x, x⟩ = false := fun σ x => hp _ rfl
        simp only [List.filter_cons, hpe, hpc, Bool.false_eq_true, ↓reduceIte, ih r' hr']
      · simp only [List.filter_cons, hpe, Bool.false_eq_true, ↓reduceIte, ih r' hr']
    · simp only [h, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      simp only [List.filter_cons]
      split_ifs <;> simp [ih r' hr']
end Split

/-! ## 6. The leaf properties of a term -/

section Leaf

variable {a b : ℕ} {D : LGraph (Fin (a+1)) (Fin b)} {ext : Fin 2 → Fin (a+1)} {N' : MNode}

private def lwExpSound_vtx (a b i : ℕ) : Fin (a+1) ⊕ Fin b :=
  if h : i < a + 1 then Sum.inl ⟨i, h⟩ else if h2 : i - (a + 1) < b then Sum.inr ⟨i - (a + 1), h2⟩ else Sum.inl 0
private theorem lwExpSound_vi_vtx (i : ℕ) (hi : i < a + 1 + b) : vi a b (lwExpSound_vtx a b i) = i := by
  unfold lwExpSound_vtx
  split_ifs with h h2 <;> simp only [vi, Sum.elim_inl, Sum.elim_inr] <;> omega

/-- The representatives of the internal molecules (`nMc` of `belowOf'` is its length). -/
private def lwExpSound_reps (D : LGraph (Fin (a+1)) (Fin b)) : List ℕ :=
  (List.range (a + 1 + b)).filter fun i => i ≥ a + 1 && (lwExpSound_mol D).getD i 0 == i
private theorem lwExpSound_mol_eq_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) (u v : E ⊕ I) : Γ.mol u = Γ.mol v ↔ Γ.molOf u = Γ.molOf v :=
  ⟨fun h => (LGraph.molOf_eq_iff _ _ _).2 (h ▸ (LGraph.molOf_eq_iff Γ v v).1 rfl), fun h => by
    ext w; rw [← LGraph.molOf_eq_iff, ← LGraph.molOf_eq_iff, h]⟩

private theorem lwExpSound_mol_lab (M : lwExpSound_MD D ext N') (x y : Fin (a+1) ⊕ Fin b) :
    N'.g.mol (M.ψ x) = N'.g.mol (M.ψ y) ↔
      (lwExpSound_mol D).getD (vi a b x) 0 = (lwExpSound_mol D).getD (vi a b y) 0 := by
  rw [lwExpSound_mol_eq_iff, lwExpSound_molOf M, (lwExpSound_mol_good D).2.2.2]

/-- The label `i` of an internal molecule is a representative of the list `reps`, and its vertex is in the molecule. -/
private theorem lwExpSound_rep_mem (M : lwExpSound_MD D ext N') (u : Fin (a+1) ⊕ Fin b)
    (hint : ∀ w ∈ N'.g.mol (M.ψ u), w.isRight = true) :
    (lwExpSound_mol D).getD (vi a b u) 0 ∈ lwExpSound_reps D := by
  obtain ⟨hlen, hle, hid, hiff⟩ := lwExpSound_mol_good D
  have hu := lwExpSim_vi_lt u
  have hi_lt : (lwExpSound_mol D).getD (vi a b u) 0 < a + 1 + b := lt_of_le_of_lt (hle _ hu) hu
  have hw0 := lwExpSound_vi_vtx _ hi_lt
  have hmolOf : D.molOf (lwExpSound_vtx a b ((lwExpSound_mol D).getD (vi a b u) 0)) = D.molOf u :=
    (hiff _ _).1 (by rw [hw0, hid _ hu])
  unfold lwExpSound_reps
  rw [List.mem_filter, List.mem_range]
  refine ⟨hi_lt, ?_⟩
  have hint := (lwExpSound_int M u).1 hint _ ((LGraph.molOf_eq_iff _ _ _).1 hmolOf.symm)
  rcases hw : lwExpSound_vtx a b ((lwExpSound_mol D).getD (vi a b u) 0) with j | j
  · rw [hw] at hint; exact absurd hint (by simp)
  · rw [hw, lwExpSim_vi_inr] at hw0
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨by omega, hid _ hu⟩

/-- The internal molecules of the merge are at most the representatives `≥ a + 1` of `mol`. -/
private theorem lwExpSound_nM_le (M : lwExpSound_MD D ext N') : N'.g.nM ≤ (lwExpSound_reps D).length := by
  obtain ⟨hlen, hle, hid, hiff⟩ := lwExpSound_mol_good D
  refine le_trans ?_ (List.toFinset_card_le _)
  unfold LGraph.nM
  refine Finset.card_le_card_of_surjOn (fun i => N'.g.mol (M.ψ (lwExpSound_vtx a b i))) ?_
  intro T hT
  rw [Finset.mem_coe, Finset.mem_image] at hT
  obtain ⟨v', hv', rfl⟩ := hT
  rw [Finset.mem_filter] at hv'
  obtain ⟨u, rfl⟩ := M.h2 v'
  have hu := lwExpSim_vi_lt u
  have hi_lt : (lwExpSound_mol D).getD (vi a b u) 0 < a + 1 + b := lt_of_le_of_lt (hle _ hu) hu
  refine ⟨_, Finset.mem_coe.2 (List.mem_toFinset.2 (lwExpSound_rep_mem M u hv'.2)), ?_⟩
  rw [lwExpSound_mol_lab M, lwExpSound_vi_vtx _ hi_lt, hid _ hu]

private theorem lwExpSound_ext_surj (M : lwExpSound_MD D ext N') (h : Function.Surjective ext) :
    Function.Surjective N'.ext := by
  intro a'
  obtain ⟨v, hv⟩ := M.h2 (Sum.inl a')
  obtain ⟨e, he⟩ := (M.h3 v).1 ⟨a', hv⟩
  obtain ⟨i, rfl⟩ := h e
  refine ⟨i, Sum.inl.inj (β := Fin N'.b) ?_⟩
  rw [← M.hext i, (M.h1 _ _).2 he, hv]

private theorem lwExpSound_ext_eq (M : lwExpSound_MD D ext N') :
    N'.ext 0 = N'.ext 1 ↔ (lwExpSim_labs D).getD (vi a b (Sum.inl (ext 0))) 0 =
      (lwExpSim_labs D).getD (vi a b (Sum.inl (ext 1))) 0 := by
  rw [(lwExpSim_labs_good D).2.2.2, ← M.h1, M.hext, M.hext]
  exact ⟨congrArg Sum.inl, Sum.inl.inj⟩

/-- **`LWAttached` from the attachment counts of the labels.** -/
private theorem lwExpSound_attached (M : lwExpSound_MD D ext N') (sol : List (SEdge (Fin (N'.a + 1) ⊕ Fin N'.b)))
    (e0 : ℕ × ℕ) (hsplit : (e0, sol) ∈ lwSplitLoopsX N'.g.solid)
    (hok : ∀ i ∈ lwExpSound_reps D, 2 ≤ ((D.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst)).filter fun e =>
      (lwExpSound_mol D).getD e.2.1 0 != (lwExpSound_mol D).getD e.2.2 0 &&
        ((lwExpSound_mol D).getD e.2.1 0 == i || (lwExpSound_mol D).getD e.2.2 0 == i)).length) :
    ∀ v : Fin N'.b, (∀ w ∈ N'.g.mol (Sum.inr v), w.isRight = true) →
      2 ≤ (sol.filter fun e => decide (N'.g.mol e.src ≠ N'.g.mol e.dst ∧
        (N'.g.mol e.src = N'.g.mol (Sum.inr v) ∨ N'.g.mol e.dst = N'.g.mol (Sum.inr v)))).length := by
  intro v hv
  obtain ⟨u, hu⟩ := M.h2 (Sum.inr v)
  rw [← hu] at hv ⊢
  have h2 := hok _ (lwExpSound_rep_mem M u hv)
  rw [List.filter_map, List.length_map] at h2
  rw [lwExpSound_split_filter N'.g.solid _ (fun e he => by simp [he]) (e0, sol) hsplit, M.hsol, List.filter_map,
    List.length_map]
  refine le_of_le_of_eq h2 (congrArg List.length (List.filter_congr fun e _ => ?_))
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, SEdge.map, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq,
    decide_eq_true_eq, ne_eq, lwExpSound_mol_lab M]

/-- **Distinct external molecules, or the two external vertices are joined**, from the last conjunct of the flag. -/
private theorem lwExpSound_molDisj (M : lwExpSound_MD D ext N') (hext : Function.Surjective ext)
    (hnM : N'.g.nM ≤ (lwExpSound_reps D).length)
    (h : ((lwExpSim_labs D).getD (vi a b (Sum.inl (ext 0))) 0 == (lwExpSim_labs D).getD (vi a b (Sum.inl (ext 1))) 0 ||
      (lwExpSound_mol D).getD (vi a b (Sum.inl (ext 0))) 0 != (lwExpSound_mol D).getD (vi a b (Sum.inl (ext 1))) 0 ||
      (lwExpSound_reps D).length == 0) = true) :
    (∀ a' b' : Fin (N'.a + 1), N'.g.molOf (Sum.inl a') = N'.g.molOf (Sum.inl b') → a' = b') ∨
      (N'.ext 0 ≠ N'.ext 1 ∧ N'.g.molOf (Sum.inl (N'.ext 0)) = N'.g.molOf (Sum.inl (N'.ext 1)) ∧ N'.g.nM = 0) := by
  have hs := lwExpSound_ext_surj M hext
  have hE := lwExpSound_ext_eq M
  have hmol : ∀ i j : Fin 2, N'.g.molOf (Sum.inl (N'.ext i)) = N'.g.molOf (Sum.inl (N'.ext j)) ↔
      (lwExpSound_mol D).getD (vi a b (Sum.inl (ext i))) 0 = (lwExpSound_mol D).getD (vi a b (Sum.inl (ext j))) 0 := by
    intro i j
    rw [← M.hext, ← M.hext, lwExpSound_molOf M, (lwExpSound_mol_good D).2.2.2]
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  by_cases hA : (lwExpSim_labs D).getD (vi a b (Sum.inl (ext 0))) 0 = (lwExpSim_labs D).getD (vi a b (Sum.inl (ext 1))) 0
  · left
    intro a' b' _
    obtain ⟨i, rfl⟩ := hs a'
    obtain ⟨j, rfl⟩ := hs b'
    have h01 := hE.2 hA
    fin_cases i <;> fin_cases j <;> simp [h01]
  by_cases hB : (lwExpSound_mol D).getD (vi a b (Sum.inl (ext 0))) 0 = (lwExpSound_mol D).getD (vi a b (Sum.inl (ext 1))) 0
  · right
    have hr : (lwExpSound_reps D).length = 0 := by tauto
    exact ⟨fun h' => hA (hE.1 h'), (hmol 0 1).2 hB, Nat.le_zero.1 (hr ▸ hnM)⟩
  · left
    intro a' b' hab
    obtain ⟨i, rfl⟩ := hs a'
    obtain ⟨j, rfl⟩ := hs b'
    have := (hmol i j).1 hab
    fin_cases i <;> fin_cases j <;> simp_all
end Leaf

/-! ## 7. The order of a term and the assembly of the flag -/

section Ord

variable {a b : ℕ} {D : LGraph (Fin (a+1)) (Fin b)} {ext : Fin 2 → Fin (a+1)} {N' : MNode}

private theorem lwExpSound_b (hN' : cMerge D ext = some N') :
    (N'.b : ℤ) = lwExpSound_B a (lwExpSim_labs D) := by
  unfold cMerge at hN'
  dsimp only at hN'
  split_ifs at hN' with hc
  cases hN'
  change (((repsOf (lwExpSim_labs D)).length - ((repsOf (lwExpSim_labs D)).filter fun x => decide (x < a + 1)).length : ℕ) : ℤ) = _
  have h1 := (repsOf (lwExpSim_labs D)).length_eq_length_filter_add (fun x => decide (x < a + 1))
  have h2 : ((repsOf (lwExpSim_labs D)).filter fun x => !decide (x < a + 1)) =
      (repsOf (lwExpSim_labs D)).filter fun x => decide (x ≥ a + 1) := List.filter_congr (fun x _ => by rw [← decide_not]; exact decide_eq_decide.2 (by omega))
  unfold lwExpSound_B
  rw [h2] at h1
  omega

private theorem lwExpSound_tgt (M : lwExpSound_MD D ext N') :
    tgt N' = lwExpSound_tg (lwExpSim_labs D) (vi a b (Sum.inl (ext 0))) (vi a b (Sum.inl (ext 1))) := by
  unfold tgt lwExpSound_tg
  by_cases h : N'.ext 0 = N'.ext 1
  · simp only [h, (lwExpSound_ext_eq M).1 h, beq_self_eq_true, ↓reduceIte]
  · have h2 : ¬ (((lwExpSim_labs D).getD (vi a b (Sum.inl (ext 0))) 0 == (lwExpSim_labs D).getD (vi a b (Sum.inl (ext 1))) 0) = true) :=
      fun h' => h ((lwExpSound_ext_eq M).2 (beq_iff_eq.1 h'))
    simp only [h, h2, ↓reduceIte, Bool.false_eq_true]

private theorem lwExpSound_L_eq (M : lwExpSound_MD D ext N') :
    lwExpSound_L (D.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst)) (lwExpSim_labs D) =
      (N'.g.solid.filter lwExpSound_isLoop).length := by
  unfold lwExpSound_L
  rw [List.filter_map, M.hsol, List.filter_map, List.length_map, List.length_map]
  refine congrArg (fun n : ℕ => (n : ℤ)) (congrArg List.length (List.filter_congr fun e _ => ?_))
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, lwExpSound_isLoop, SEdge.map, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq, (lwExpSim_labs_good D).2.2.2, ← M.h1]
  simp [and_comm]

/-- The order of the split term against the bound of `belowOf'`. -/
private theorem lwExpSound_ord (M : lwExpSound_MD D ext N') (hN' : cMerge D ext = some N')
    (sol : List (SEdge (Fin (N'.a + 1) ⊕ Fin N'.b))) (e0 : ℕ × ℕ) (hsplit : (e0, sol) ∈ lwSplitLoopsX N'.g.solid) :
    (leaf { N' with g := { N'.g with solid := sol } } = true →
      lwExpSound_tg (lwExpSim_labs D) (vi a b (Sum.inl (ext 0))) (vi a b (Sum.inl (ext 1))) ≤
        (D.solid.length : ℤ) + 2 * ((D.waved.length : ℤ) - lwExpSound_B a (lwExpSim_labs D))) ∧
    (leaf { N' with g := { N'.g with solid := sol } } = false →
      ¬ ((D.solid.length : ℤ) - lwExpSound_L (D.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst)) (lwExpSim_labs D) +
        2 * ((D.waved.length : ℤ) - lwExpSound_B a (lwExpSim_labs D)) ≥
          lwExpSound_tg (lwExpSim_labs D) (vi a b (Sum.inl (ext 0))) (vi a b (Sum.inl (ext 1))))) := by
  obtain ⟨h1, h2⟩ := lwExpSound_split_len N'.g.solid (e0, sol) hsplit
  simp only at h1 h2
  have hS : N'.g.solid.length = D.solid.length := by rw [M.hsol, List.length_map]
  have hW : N'.g.waved.length = D.waved.length := by rw [M.hwav, List.length_map]
  have hB := lwExpSound_b hN'
  have hL := lwExpSound_L_eq M
  have hT := lwExpSound_tgt M
  have hord : ({ N' with g := { N'.g with solid := sol } } : MNode).g.scalingOrder =
      (sol.length : ℤ) + 2 * ((D.waved.length : ℤ) - N'.b) := by
    simp [LGraph.scalingOrder, LGraph.counters, ord, LGraph.nS, LGraph.nW, LGraph.nV, hW, M.hwav]
  have hleaf : leaf { N' with g := { N'.g with solid := sol } } = decide (lwExpSound_tg (lwExpSim_labs D)
      (vi a b (Sum.inl (ext 0))) (vi a b (Sum.inl (ext 1))) ≤ (sol.length : ℤ) + 2 * ((D.waved.length : ℤ) - N'.b)) := by
    unfold leaf
    rw [← hT, hord]
    rfl
  rw [hleaf, hL, ← hB]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [decide_eq_true_eq] at h
    omega
  · simp only [decide_eq_false_iff_not, not_le] at h
    omega

private theorem lwExpSound_nW_rel {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) : P.g.nW = N.g.nW := by
  obtain ⟨eE, eI, -, -, hw, -⟩ := h
  simpa [LGraph.nW] using congrArg List.length hw

/-- **A leaf term of a consistent choice has the leaf properties in every related packed graph**, if the flag
`ok0` of `belowOf'` holds at the term and the term is normal. -/
private theorem lwExpSound_leafOK (M : lwExpSound_MD D ext N') (hext : Function.Surjective ext) (hN' : cMerge D ext = some N')
    (sol : List (SEdge (Fin (N'.a + 1) ⊕ Fin N'.b))) (e0 : ℕ × ℕ) (hsplit : (e0, sol) ∈ lwSplitLoopsX N'.g.solid)
    (hnorm : ({ N'.g with solid := sol } : LGraph _ _).Normal)
    (hleaf : leaf { N' with g := { N'.g with solid := sol } } = true)
    (hok : lwExpSound_ok0 a b (D.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst))
      (D.waved.map fun e => (vi a b e.x, vi a b e.y)) D.solid.length D.waved.length (vi a b (Sum.inl (ext 0)))
      (vi a b (Sum.inl (ext 1))) (lwExpSim_labs D) = true) :
    ∀ Q : PGraph (Fin 2), Rel { N' with g := { N'.g with solid := sol } } Q → LeafOK Q := by
  intro Q hQ
  have hcond := (lwExpSound_ord M hN' sol e0 hsplit).1 hleaf
  unfold lwExpSound_ok0 at hok
  have hcond' : (D.solid.length : ℤ) + 2 * ((D.waved.length : ℤ) - lwExpSound_B a (lwExpSim_labs D)) ≥
      lwExpSound_tg (lwExpSim_labs D) (vi a b (Sum.inl (ext 0))) (vi a b (Sum.inl (ext 1))) := hcond
  simp only [hcond', ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hok
  have hs := lwExpSound_ext_surj M hext
  have hnM : N'.g.nM ≤ (lwExpSound_reps D).length := lwExpSound_nM_le M
  have h3' : ∀ i ∈ lwExpSound_reps D, 2 ≤ ((D.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst)).filter fun e =>
      (lwExpSound_mol D).getD e.2.1 0 != (lwExpSound_mol D).getD e.2.2 0 &&
        ((lwExpSound_mol D).getD e.2.1 0 == i || (lwExpSound_mol D).getD e.2.2 0 == i)).length := h3
  obtain ⟨hn, hm, ha, hmo, hj⟩ := relInvariance { N' with g := { N'.g with solid := sol } } hs Q hQ
  refine ⟨hn.1 hnorm, hm ▸ le_trans hnM (by exact h1), ?_, ha.2 (lwExpSound_attached M sol e0 hsplit h3'), ?_,
    (Rel.leaf_iff hQ).1 hleaf⟩
  · rw [lwExpSound_nW_rel hQ]
    change 2 ≤ N'.g.waved.length
    rw [M.hwav, List.length_map]
    exact_mod_cast h2
  · exact (lwExpSound_molDisj M hext hnM h4).imp hmo.2 hj.2
end Ord

/-! ## 8. `belowOfSound` -/

section Sound

variable {a b : ℕ}

private theorem lwExpSound_labsC_eq (Δ : LGraph (Fin (a+1)) (Fin b)) (c : ℤ × List (DEdge (Fin (a+1) ⊕ Fin b))) :
    lwExpSound_labsC Δ c = lwExpSim_labs (Δ.withDots c) := by
  unfold lwExpSound_labsC lwExpSim_labs
  have h : (Δ.dotBase.filter fun e => e.eq) = Δ.dotted.filter fun e => e.eq := by
    unfold LGraph.dotBase
    rw [List.filter_filter]
    refine List.filter_congr fun e _ => ?_
    cases h : e.eq <;> simp [LGraph.isB, h]
  simp only [LGraph.withDots, List.filter_append, List.map_append, h]

private theorem lwExpSound_skipC_iff (Δ : LGraph (Fin (a+1)) (Fin b)) (c : ℤ × List (DEdge (Fin (a+1) ⊕ Fin b))) :
    lwExpSound_skipC Δ c = true ↔ ¬ (Δ.withDots c).Consistent := by
  rw [← lwExpSim_test_iff, ← lwExpSound_labsC_eq]
  unfold lwExpSound_skipC
  simp only [LGraph.withDots, List.filter_append, List.any_append, List.any_map, Bool.or_eq_true]
  rfl
private theorem lwExpSound_forall₂_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ x ∈ l₁, ∃ y ∈ l₂, R x y
  | _, _, .nil, x, hx => by simp at hx
  | _, _, .cons h t, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hR⟩ := lwExpSound_forall₂_mem_left t x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hR⟩

private theorem lwExpSound_forall₂_mem_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, y, hy => by simp at hy
  | _, _, .cons h t, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hR⟩ := lwExpSound_forall₂_mem_right t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hR⟩

/-- Every term of `cPartitionX` is normal (through the real partition, `partitionSim` and `relInvariance`). -/
private theorem lwExpSound_normal (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1))
    (hext : Function.Surjective ext) : ∀ r ∈ cPartitionX Δ ext, r.2.g.Normal := by
  intro r hr
  obtain ⟨Q, hQ, hrel, -⟩ := lwExpSound_forall₂_mem_left (partitionSim ⟨a, b, Δ, ext⟩ hext 1) r hr
  obtain ⟨P₀, hP₀, rfl⟩ := List.mem_map.1 hQ
  exact (relInvariance r.2 hrel.ext_surj _ hrel).1.2 (LGraph.partition_normal 1 Δ P₀ hP₀)

/-- **L7: soundness of the lite flag of `belowOf'`.** -/
theorem belowOfSound : BelowOfSound := by
  intro a b Δ ext hext hflag r hr
  have hn := lwExpSound_normal Δ ext hext r hr
  unfold cPartitionX at hr
  simp only [List.mem_flatMap, List.mem_map] at hr
  obtain ⟨D, ⟨c, hc, rfl⟩, hr⟩ := hr
  cases hcm : cMerge (Δ.withDots c) ext with
  | none => rw [hcm] at hr; simp at hr
  | some N' =>
    rw [hcm] at hr
    obtain ⟨⟨e0, sol⟩, hsplit, rfl⟩ := List.mem_map.1 hr
    have hC : (Δ.withDots c).Consistent := by
      by_contra h; rw [lwExpSim_cMerge_none _ _ h] at hcm; exact absurd hcm (by simp)
    obtain ⟨N'', hN'', ⟨M⟩⟩ := lwExpSound_md ext hC
    rw [hcm] at hN''
    cases hN''
    have hsk : lwExpSound_skipC Δ c = false := by
      by_contra h; exact (lwExpSound_skipC_iff Δ c).1 (by simpa using h) hC
    rw [lwExpSound_below_eq] at hflag ⊢
    obtain ⟨F1, F2⟩ := lwExpSound_fold (S := Δ.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst))
      (W := Δ.waved.map fun e => (vi a b e.x, vi a b e.y)) (nS := Δ.solid.length) (nW := Δ.waved.length)
      (x0 := vi a b (Sum.inl (ext 0))) (y0 := vi a b (Sum.inl (ext 1))) (a := a) (b := b)
      (lwExpSound_labsC Δ) (lwExpSound_skipC Δ) (fun c => cMerge (Δ.withDots c) ext) Δ.dotChoices
    have hok := F1 hflag c hc hsk
    rw [lwExpSound_labsC_eq] at hok
    refine ⟨fun hleaf Q hQ => lwExpSound_leafOK M hext hcm sol e0 hsplit hn hleaf hok Q hQ, fun hleaf => ?_⟩
    have hcov := (lwExpSound_ord M hcm sol e0 hsplit).2 hleaf
    rw [← lwExpSound_labsC_eq] at hcov
    refine ⟨{ N' with g := { N'.g with solid := sol, coeff := (1 ^ e0.1 * star 1 ^ e0.2) * N'.g.coeff } }, ?_,
      fun Q hQ => hQ⟩
    refine F2 c hc hsk hcov N' hcm _ ?_
    rw [LGraph.splitWeights, lwSplitLoopsX_spec, List.map_map, List.map_map, List.mem_filter]
    exact ⟨List.mem_map.2 ⟨(e0, sol), hsplit, rfl⟩, by simpa using hleaf⟩
end Sound

/-! ## 9. The assembly (L8) -/

section Assembly

theorem goodB'_mono (n : ℕ) (N : MNode) : goodB' n N = true → goodB' (n + 1) N = true := by
  have e : ∀ n N, goodB' (n + 1) N = (leaf N || (!(cands N.g).isEmpty && (cands N.g).all fun c =>
      (childrenB' N c).1 && (childrenB' N c).2.all (goodB' n))) := fun n N => rfl
  induction n generalizing N with
  | zero => intro h; rw [e]; simp [goodB'] at h; simp [h]
  | succ n ih =>
    intro h
    rw [e n N] at h
    rw [e (n + 1) N]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, fun c hc => ⟨(h2 c hc).1, fun K hK => ih K ((h2 c hc).2 K hK)⟩⟩

private theorem lwExpSound_childrenB (N : MNode) (c : Cand N.a N.b) :
    ((childrenB' N c).1 = true → ∀ f ∈ fams N.g c, (belowOf' f.2 N.ext).1 = true) ∧
    ∀ f ∈ fams N.g c, ∀ M ∈ (belowOf' f.2 N.ext).2, M ∈ (childrenB' N c).2 := by
  unfold childrenB'
  generalize fams N.g c = L
  induction L with
  | nil => simp
  | cons f L ih =>
    simp only [List.foldr_cons]
    refine ⟨fun h g hg => ?_, fun g hg M hM => ?_⟩
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact (Bool.and_eq_true_iff.1 h).1
      · exact ih.1 (Bool.and_eq_true_iff.1 h).2 g hg
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact List.mem_append_left _ hM
      · exact List.mem_append_right _ (ih.2 g hg M hM)

/-- Soundness at the model children of a node (every term of `childrenX`). -/
private theorem lwExpSound_childSound (N : MNode) (h : Function.Surjective N.ext) (c : Cand N.a N.b)
    (hflag : (childrenB' N c).1 = true) :
    ∀ r ∈ childrenX N c, (leaf r.2 = true → ∀ Q, Rel r.2 Q → LeafOK Q) ∧
      (leaf r.2 = false → ∃ M ∈ (childrenB' N c).2, ∀ Q, Rel r.2 Q → Rel M Q) := by
  intro r hr
  obtain ⟨f, hf, hr⟩ := List.mem_flatMap.1 hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
  have hf' : f.2 ∈ fams N.g c := by rw [fams_eq_famsX]; exact List.mem_map.2 ⟨f, hf, rfl⟩
  obtain ⟨H1, H2⟩ := lwExpSound_childrenB N c
  obtain ⟨hl, hn⟩ := belowOfSound N.a f.2.1 f.2.2 N.ext h (H1 hflag _ hf') r' hr'
  exact ⟨hl, fun hf0 => (hn hf0).imp fun M hM => ⟨H2 _ hf' M hM.1, hM.2⟩⟩

/-- The soundness statement of a model term is carried to every packed graph related to it. -/
private theorem lwExpSound_transfer {rm : MNode} {P : PGraph (Fin 2)} {L : List MNode} (hrel : Rel rm P)
    (H : (leaf rm = true → ∀ Q, Rel rm Q → LeafOK Q) ∧ (leaf rm = false → ∃ M ∈ L, ∀ Q, Rel rm Q → Rel M Q)) :
    ((if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder → LeafOK P) ∧
    (¬ (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder → ∃ M ∈ L, Rel M P) :=
  ⟨fun hle => H.1 ((Rel.leaf_iff hrel).2 hle) P hrel, fun hnle => (H.2 (by
    by_contra hh; exact hnle ((Rel.leaf_iff hrel).1 (by simpa using hh)))).imp fun M hM => ⟨hM.1, hM.2 P hrel⟩⟩

/-- **`SoundStep`**: under the flag of `childrenB'`, every real child is a leaf with the properties or is related to a
listed child. -/
theorem soundStep : SoundStep := by
  intro N h c hc hflag Q hQ
  obtain ⟨r, hr, hrel, -⟩ := lwExpSound_forall₂_mem_right (childrenSim N h c hc) Q hQ
  exact lwExpSound_transfer hrel (lwExpSound_childSound N h c hflag r hr)

/-- The key of a model node: everything `Rel` reads (the waved colours are not in it). -/
private structure lwExpSound_Key where
  a : ℕ
  b : ℕ
  solid : List (Bool × Bool × ℕ × ℕ)
  waved : List (ℕ × ℕ)
  dotted : List (Bool × ℕ × ℕ)
  e0 : ℕ
  e1 : ℕ
  deriving DecidableEq

private def lwExpSound_key (M : MNode) : lwExpSound_Key :=
  ⟨M.a, M.b, M.g.solid.map fun e => (e.σ, e.circ, vi M.a M.b e.src, vi M.a M.b e.dst),
    M.g.waved.map fun e => (vi M.a M.b e.x, vi M.a M.b e.y),
    M.g.dotted.map fun e => (e.eq, vi M.a M.b e.x, vi M.a M.b e.y), (M.ext 0).val, (M.ext 1).val⟩
private theorem lwExpSound_key_rel {M M' : MNode} (h : lwExpSound_key M = lwExpSound_key M') {Q : PGraph (Fin 2)}
    (hQ : Rel M Q) : Rel M' Q := by
  obtain ⟨a, b, g, ext⟩ := M
  obtain ⟨a', b', g', ext'⟩ := M'
  simp only [lwExpSound_key, lwExpSound_Key.mk.injEq] at h
  obtain ⟨rfl, rfl, hs, hw, hd, h0, h1⟩ := h
  have hs' : g.solid = g'.solid := List.map_injective_iff.2 (fun e e' h => by
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    cases e; cases e'; simp only [SEdge.mk.injEq]
    exact ⟨h1, h2, lwExpSim_vi_inj h3, lwExpSim_vi_inj h4⟩) hs
  have hd' : g.dotted = g'.dotted := List.map_injective_iff.2 (fun e e' h => by
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases e; cases e'; simp only [DEdge.mk.injEq]
    exact ⟨h1, lwExpSim_vi_inj h2, lwExpSim_vi_inj h3⟩) hd
  have hw' : g.waved.map (fun e => (e.x, e.y)) = g'.waved.map (fun e => (e.x, e.y)) :=
    List.map_injective_iff.2 (fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (lwExpSim_vi_inj h.1) (lwExpSim_vi_inj h.2))
      (show (g.waved.map fun e => (e.x, e.y)).map (fun p => (vi a b p.1, vi a b p.2)) =
        (g'.waved.map fun e => (e.x, e.y)).map (fun p => (vi a b p.1, vi a b p.2)) by
        rw [List.map_map, List.map_map]; exact hw)
  have he : ext = ext' := funext fun i => by fin_cases i <;> exact Fin.ext (by assumption)
  subst he
  obtain ⟨eE, eI, he, hsol, hwav, hdot⟩ := hQ
  refine ⟨eE, eI, he, hs' ▸ hsol, ?_, hd' ▸ hdot⟩
  rw [hwav, show (g.waved.map fun e => (Sum.map eE eI e.x, Sum.map eE eI e.y)) =
      (g.waved.map fun e => (e.x, e.y)).map (fun p => (Sum.map eE eI p.1, Sum.map eE eI p.2)) by rw [List.map_map]; rfl,
    show (g'.waved.map fun e => (Sum.map eE eI e.x, Sum.map eE eI e.y)) =
      (g'.waved.map fun e => (e.x, e.y)).map (fun p => (Sum.map eE eI p.1, Sum.map eE eI p.2)) by rw [List.map_map]; rfl, hw']

/-- The colour-erased lists of the model partitions of the two charges of the first waved edge agree (`s = false`). -/
private theorem lwExpSound_key_FF :
    (cPartitionX (a := 1) (b := 3) (LWG5Graph true false) ![0, 1]).map (fun r => lwExpSound_key r.2) =
      (cPartitionX (a := 1) (b := 3) (LWG5Graph false false) ![0, 1]).map (fun r => lwExpSound_key r.2) := by
  decide +kernel

/-- The same for `s = true`. -/
private theorem lwExpSound_key_FT :
    (cPartitionX (a := 1) (b := 3) (LWG5Graph true true) ![0, 1]).map (fun r => lwExpSound_key r.2) =
      (cPartitionX (a := 1) (b := 3) (LWG5Graph false true) ![0, 1]).map (fun r => lwExpSound_key r.2) := by
  decide +kernel

#print axioms lwExpSound_key_FF
#print axioms lwExpSound_key_FT

/-- The model partition of the root and the real one are related term by term, for every `k`, `s`. -/
private theorem lwExpSound_rootSim (k s : Bool) :
    List.Forall₂ (fun (rm : (ℕ × ℕ) × MNode) (r : (ℕ × ℕ) × PGraph (Fin 2)) => Rel rm.2 r.2)
      (cPartitionX (a := 1) (b := 3) (LWG5Graph k s) ![0, 1]) (partitionX (LWG5Graph k s)) := by
  have hN : Function.Surjective (![0, 1] : Fin 2 → Fin (1 + 1)) := by decide
  have hsim := lwExpSim_partition_sim (⟨1, 3, LWG5Graph k s, ![0, 1]⟩ : MNode) hN
    (Equiv.sumCongr (Equiv.refl _) (Equiv.refl (Fin 3))) (fun a => rfl) (LWG5Graph k s)
  rw [lwExpSim_relabel_refl] at hsim
  refine hsim.imp fun rm r hrel => ?_
  obtain ⟨eE, eI, he, hs, hw, hd⟩ := hrel.1
  exact ⟨eE, eI, fun i => by have h := he i; fin_cases i <;> exact h, hs, hw, hd⟩

/-- Every real root term of every `k` is related to a model term of the root of `k = false`. -/
private theorem lwExpSound_rootPartner (k s : Bool) :
    ∀ r ∈ partitionX (LWG5Graph k s), ∃ rm ∈ cPartitionX (a := 1) (b := 3) (LWG5Graph false s) ![0, 1], Rel rm.2 r.2 := by
  intro r hr
  obtain ⟨rm, hrm, hrel⟩ := lwExpSound_forall₂_mem_right (lwExpSound_rootSim k s) r hr
  cases k
  · exact ⟨rm, hrm, hrel⟩
  · have hmem : lwExpSound_key rm.2 ∈ (cPartitionX (a := 1) (b := 3) (LWG5Graph false s) ![0, 1]).map
        (fun r => lwExpSound_key r.2) := by
      cases s
      · rw [← lwExpSound_key_FF]; exact List.mem_map.2 ⟨rm, hrm, rfl⟩
      · rw [← lwExpSound_key_FT]; exact List.mem_map.2 ⟨rm, hrm, rfl⟩
    obtain ⟨rm', hrm', hk⟩ := List.mem_map.1 hmem
    exact ⟨rm', hrm', lwExpSound_key_rel hk.symm hrel⟩

/-- **`SoundRoot`**: soundness at the root, for every `k` (the waved colour is not read). -/
theorem soundRoot : SoundRoot := by
  intro k s hflag r hr
  obtain ⟨rm, hrm, hrel⟩ := lwExpSound_rootPartner k s r hr
  exact lwExpSound_transfer hrel (belowOfSound 1 3 (LWG5Graph false s) ![0, 1] (by decide) hflag rm hrm)

/-- **The induction along `expand`**: the invariant `Inv n` (a leaf has the properties; a node below the target is related to
a model node with an `n`-certificate) gives the leaf properties at every output of `expand selClassical n`. -/
private theorem lwExpSound_expand : ∀ (n : ℕ) (P : PGraph (Fin 2)),
    ((if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder → LeafOK P) →
    (¬ (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder → ∃ M, Rel M P ∧ goodB' n M = true) →
    ∀ t ∈ expand selClassical n P, LeafOK t.2 := by
  intro n
  induction n with
  | zero =>
    intro P h1 h2 t ht
    simp only [expand, List.mem_singleton] at ht
    subst ht
    by_cases hl : (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder
    · exact h1 hl
    · obtain ⟨M, hM, hg⟩ := h2 hl
      exact absurd ((Rel.leaf_iff hM).1 hg) hl
  | succ n ih =>
    intro P h1 h2 t ht
    by_cases hl : (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder
    · simp only [expand, hl, ↓reduceIte, List.mem_singleton] at ht
      subst ht
      exact h1 hl
    · obtain ⟨M, hM, hg⟩ := h2 hl
      have hleaf : leaf M = false := by
        by_contra hh; exact hl ((Rel.leaf_iff hM).1 (by simpa using hh))
      simp only [goodB', hleaf, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hg
      obtain ⟨hne, hall⟩ := hg
      obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _ (List.isEmpty_eq_false_iff.1 hne)
      have hcand := hM.cand c0 hc0
      have hsel : selClassical P = some (Classical.choice ((lwG5Cand_iff_nonempty P).1 hcand)) := by
        unfold selClassical; simp [hcand]
      simp only [expand, hl, ↓reduceIte, hsel, List.mem_flatMap, List.mem_map] at ht
      obtain ⟨r, hr, t', ht', rfl⟩ := ht
      obtain ⟨c, hc, hF⟩ := relKids M P hM _
      obtain ⟨rm, hrm, hrel⟩ := lwExpSound_forall₂_mem_right hF r hr
      obtain ⟨H1, H2⟩ := lwExpSound_transfer hrel.1 (lwExpSound_childSound M hM.ext_surj c (hall c hc).1 rm hrm)
      exact ih r.2 H1 (fun hnle => (H2 hnle).imp fun M' hM' => ⟨hM'.2, (hall c hc).2 M' hM'.1⟩) t' ht'

/-- **The leaf half of `LWG5Expand'`**: every member of the list of `expandRoot selClassical 4` has the six leaf properties. -/
theorem lwG5LeafProps_holds : LWG5LeafProps (expandRoot selClassical 4) := by
  intro k s q hq
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq
  obtain ⟨hflag, hall⟩ := cert_all' s
  obtain ⟨H1, H2⟩ := soundRoot k s hflag r hr
  exact lwExpSound_expand 4 r.2 H1 (fun hnle => (H2 hnle).imp fun M hM =>
    ⟨hM.2, goodB'_mono 3 M (List.all_eq_true.1 hall M hM.1)⟩) t ht

theorem lwG5ExpandSplit_iff (d : ℕ) : LWG5ExpandSplit d ↔ LWG5Expand' d := Iff.rfl
theorem lwG5LeafProps_iff (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) :
    LWG5LeafProps Ls ↔ ∀ k s, ∀ q ∈ Ls k s, LeafOK q.2 := Iff.rfl
theorem lwG5ExpandOfHalves : LWG5ExpandOfHalves := fun hid hleaf d => ⟨expandRoot selClassical 4, hleaf, hid d⟩

/-- **The expansion of `𝒢_xy` (`B:78-108`)**: the pin `LWG5Expand' d` for every `d`. -/
theorem lwG5Expand'_holds : ∀ d, LWG5Expand' d := fun d =>
  lwG5ExpandOfHalves (lwExpandIdentity_holds selClassical 4) lwG5LeafProps_holds d
end Assembly

/-! ## 10. Compiled instances (root term `9` of `(k, s) = (false, false)`: `a = 0`, `b = 3`, `ord 2 < tg 4`, three candidates) -/

section Inst

private abbrev lwExpSound_N : MNode := rootAt' false false 9
private theorem lwExpSound_N_surj : Function.Surjective lwExpSound_N.ext := by decide +kernel
private abbrev lwExpSound_c : Cand lwExpSound_N.a lwExpSound_N.b := (cands lwExpSound_N.g)[0]'(by decide +kernel)
private abbrev lwExpSound_f : Σ b', LGraph (Fin (lwExpSound_N.a + 1)) (Fin b') :=
  (fams lwExpSound_N.g lwExpSound_c)[0]'(by decide +kernel)

/-- Nondegeneracy: below the target, three candidates, `533` children at the first, `11` terms of its family `R2`. -/
example : lwExpSound_N.a = 0 ∧ lwExpSound_N.b = 3 ∧ lwExpSound_N.g.scalingOrder = 2 ∧ tgt lwExpSound_N = 4 ∧
    (cands lwExpSound_N.g).length = 3 ∧ (childrenX lwExpSound_N lwExpSound_c).length = 533 ∧
    (cPartitionX lwExpSound_f.2 lwExpSound_N.ext).length = 11 ∧
    ((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[2]'(by decide +kernel)).2.b = 1 ∧
    ((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[2]'(by decide +kernel)).2.g.scalingOrder = 7 := by decide +kernel

example : LWG5Expand' 3 := lwG5Expand'_holds 3
example := And.intro (lwG5ExpandSplit_iff 3) (And.intro (lwG5LeafProps_iff (expandRoot selClassical 4)) lwG5ExpandOfHalves)

/-- Instance of `relInvariance` at the node and its own packed graph. -/
example := relInvariance lwExpSound_N lwExpSound_N_surj _ (rel_self lwExpSound_N lwExpSound_N_surj)

/-- Instance of `relKids`: the existential witness, the `Forall₂` and the length of the children. -/
theorem lwExpSound_inst_relKids : ∃ c ∈ cands lwExpSound_N.g,
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
      (childrenX lwExpSound_N c) (Cand.toR lwExpSound_N lwExpSound_N_surj lwExpSound_c (List.getElem_mem _)).kids ∧
    (Cand.toR lwExpSound_N lwExpSound_N_surj lwExpSound_c (List.getElem_mem _)).kids.length =
      (childrenX lwExpSound_N c).length :=
  (relKids lwExpSound_N _ (rel_self lwExpSound_N lwExpSound_N_surj)
    (Cand.toR lwExpSound_N lwExpSound_N_surj lwExpSound_c (List.getElem_mem _))).imp fun _ hc => ⟨hc.1, hc.2, hc.2.length_eq.symm⟩

/-- Instances of `belowOfSound` at the root `LWG5Graph false false`: the first partition term is a leaf, the term `95`
is the first one below the target. -/
example : ∀ Q, Rel ((cPartitionX (a := 1) (b := 3) (LWG5Graph false false) ![0, 1])[0]'(by decide +kernel)).2 Q → LeafOK Q :=
  (belowOfSound 1 3 (LWG5Graph false false) ![0, 1] (by decide) root_FF_shape'.1 _ (List.getElem_mem _)).1 (by decide +kernel)
example : ∃ M ∈ (rootInfo' false false).2, ∀ Q, Rel ((cPartitionX (a := 1) (b := 3) (LWG5Graph false false) ![0, 1])[95]'
    (by decide +kernel)).2 Q → Rel M Q :=
  (belowOfSound 1 3 (LWG5Graph false false) ![0, 1] (by decide) root_FF_shape'.1 _ (List.getElem_mem _)).2 (by decide +kernel)

/-- **The terms the certificate of T2306 did not cover** (Amend 1): the family graph `R2` of candidate `0` of the node has
`5` choices that `belowOf` skipped and `belowOf'` evaluates (`lwCertB_lost_R2`); the leaf term `2` (classes `a ~ c ~ x + y`,
the merged b-edge `=(a, c)`) has the leaf properties in every related packed graph, in particular in its own. -/
theorem lwExpSound_inst_belowOfSound_R2 :
    ∀ Q, Rel ((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[2]'(by decide +kernel)).2 Q → LeafOK Q :=
  (belowOfSound _ _ lwExpSound_f.2 lwExpSound_N.ext lwExpSound_N_surj (by decide +kernel) _ (List.getElem_mem _)).1
    (by decide +kernel)

theorem lwExpSound_inst_leafOK_R2 : LeafOK (((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[2]'(by decide +kernel)).2.toP
    (by decide +kernel)) :=
  lwExpSound_inst_belowOfSound_R2 _ (rel_self _ _)
example : ∃ M ∈ (belowOf' lwExpSound_f.2 lwExpSound_N.ext).2, ∀ Q, Rel ((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[8]'
    (by decide +kernel)).2 Q → Rel M Q :=
  (belowOfSound _ _ lwExpSound_f.2 lwExpSound_N.ext lwExpSound_N_surj (by decide +kernel) _ (List.getElem_mem _)).2
    (by decide +kernel)

/-- Instance of `soundStep` at the first kid of the first candidate (`childrenB'` flag by the kernel). -/
example := soundStep lwExpSound_N lwExpSound_N_surj lwExpSound_c (List.getElem_mem _) (by decide +kernel)
  ((Cand.toR lwExpSound_N lwExpSound_N_surj lwExpSound_c (List.getElem_mem _)).kids[0]'
    (by rw [← (childrenSim lwExpSound_N lwExpSound_N_surj lwExpSound_c (List.getElem_mem _)).length_eq]; decide +kernel))
  (List.getElem_mem _)

/-- Instances of `soundRoot` at the first real root term, for `k = false` and `k = true` (`s = false`). -/
example (k : Bool) := soundRoot k false cert_FF'.1 ((partitionX (LWG5Graph k false))[0]'
  (by rw [← (lwExpSound_rootSim k false).length_eq]; cases k <;> decide +kernel)) (List.getElem_mem _)

/-- Instance of `lwG5LeafProps_holds`: the first partition term of the root is a leaf, hence a member of the list. -/
theorem lwExpSound_inst_leafProps : ∃ q ∈ expandRoot selClassical 4 false false, LeafOK q.2 := by
  let rm := (cPartitionX (a := 1) (b := 3) (LWG5Graph false false) ![0, 1])[0]'(by decide +kernel)
  obtain ⟨r, hr, hrel⟩ := lwExpSound_forall₂_mem_left (lwExpSound_rootSim false false) rm (List.getElem_mem _)
  have hle := (Rel.leaf_iff hrel).1 (show leaf rm.2 = true by decide +kernel)
  have hmem : ((r.1.1 + 0, r.1.2 + 0), r.2) ∈ expandRoot selClassical 4 false false :=
    List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨((0, 0), r.2), by simp only [expand, hle, ↓reduceIte, List.mem_singleton], rfl⟩⟩
  exact ⟨_, hmem, lwG5LeafProps_holds false false _ hmem⟩
end Inst

end RBM.Gauss.Sizes

end
