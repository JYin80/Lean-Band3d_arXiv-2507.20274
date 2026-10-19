/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASizeClaim

/-!
# The claim `Γ ≺ size(Γ)` at BA, the model forms and the confinement tails (part 2)

Paper: the claim `Γ ≺ size(Γ)` for normal graphs (Subsection 7.1, after (7.18)
`eq:estSpm-W`); (7.14) `scalemole`; the BA size (B.16) `eq_defsize_BA`; (B.15) `scaleatom`.
Part 1 is `Graph/BASizeClaim` (the kernel edges and the atomic forest); this file imports it.

## Contents (namespace `RBM.Graph`, private prefix `BASizeClaim_`)

1. `BAGraph.sizeConst` (`C_Γ = ‖coeff‖ K₁^{n_A - n_M} K₀^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}`), the
   term bound (`BASizeClaim_term_le`: every solid edge of a normal BA graph is circled, so it is
   `≤ Ψ` by `‖G - M‖ ≤ Ψ`; the `×`-dotted factors are `≤ 1`), the sum over the internal labels
   (`BASizeClaim_sum_le`: the peeling bound with the atomic forest and per-edge constants: a tree
   `M`- or `Ψ`-dotted edge costs `Kd` through its row or column sum, a non-tree one costs `Kd`
   through its entry, a tree waved edge `K₁`, a non-tree waved edge `K₀ W^{-d}`, a root `N`).
2. **`baClaimSize`**: the BA claim `Γ ≺ size(Γ)`, deterministic form, with the hypotheses BA has
   (no `hM : M = m I`, which is false at BA for every `g₀ ≠ 0`).

No smallness of `g₀` and no `(Cλ)^{|a-b|}` decay is used: the uniform decay rate enters only
through the constants `K₀`, `K₁`, `Kd` (`BAct_rate`, `BAp5s_rate`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open Matrix

namespace RBM.Graph

open RBM RBM.Gauss

/-! ## The constant, the weights and the term bound -/

/-- `C_Γ = ‖coeff‖ K₁^{n_A - n_M} K₀^{n_W - (n_A - n_M)} Kd^{#M-dotted + #Ψ-dotted}`: the constant of the BA
claim `Γ ≺ size(Γ)`, depending on the graph and on `(K₀, K₁, Kd)` (that is on `d, Λ, κ`) only. -/
def BAGraph.sizeConst {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (K₀ K₁ Kd : ℝ) : ℝ :=
  ‖Γ.coeff‖ * K₁ ^ (Γ.nA - Γ.nM) * K₀ ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)

private theorem BASizeClaim_sizeConst_nonneg {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) {K₀ K₁ Kd : ℝ} (h₀ : 0 ≤ K₀) (h₁ : 0 ≤ K₁) (hd : 0 ≤ Kd) :
    0 ≤ Γ.sizeConst K₀ K₁ Kd := by
  unfold BAGraph.sizeConst; positivity

section Term

variable {ι V : Type*}

private theorem BASizeClaim_norm_list_prod (l : List ℂ) : ‖l.prod‖ = (l.map fun z => ‖z‖).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem BASizeClaim_list_prod_le (l : List ℝ) (Ψ : ℝ) (h0 : ∀ x ∈ l, 0 ≤ x) (h : ∀ x ∈ l, x ≤ Ψ) :
    l.prod ≤ Ψ ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ]
    have hx0 := h0 x (List.mem_cons_self ..)
    have hx := h x (List.mem_cons_self ..)
    have hl0 : 0 ≤ l.prod := List.prod_nonneg fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    have ih' := ih (fun y hy => h0 y (List.mem_cons_of_mem _ hy)) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have : 0 ≤ Ψ := hx0.trans hx
    calc x * l.prod ≤ Ψ * Ψ ^ l.length := mul_le_mul hx ih' hl0 this
      _ = _ := by ring

private theorem BASizeClaim_list_prod_fin {α : Type*} (l : List α) (g : α → ℝ) :
    (l.map g).prod = ∏ j : Fin l.length, g (l.get j) := by
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

/-- A circled solid edge has the factor `(G - M)_{xy}` or its conjugate, `≤ Ψ` by the entry bound. -/
private theorem BASizeClaim_sedge_le (D : BALData ι) {Ψ : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ)
    (ℓ : V → ι) (e : SEdge V) (hc : e.circ = true) : ‖SEdge.val D.toLData ℓ e‖ ≤ Ψ := by
  unfold SEdge.val
  dsimp only
  simp only [hc, ite_true]
  cases e.σ
  · simp only [Bool.false_eq_true, ite_false, norm_star]
    exact hG _ _
  · simp only [ite_true]
    exact hG _ _

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

/-- Pointwise bound of one term: `|term| ≤ |coeff| Ψ^{n_S} ∏_{waved} |S-factor| ∏_{Ψ-dotted} |·| ∏_{M-dotted} |·|`:
every solid edge of a normal BA graph is circled, so it is `≤ Ψ` by `‖G - M‖ ≤ Ψ` (no `×`-dotted case split);
the `×`-dotted factors are `≤ 1`. -/
private theorem BASizeClaim_term_le (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData ι) {Ψ : ℝ}
    (hΨ : 0 ≤ Ψ) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (ℓ : E ⊕ I → ι) :
    ‖Γ.term D ℓ‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      ((Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod *
        (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod * (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod) := by
  unfold BAGraph.term RBM.Graph.LGraph.term
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, BASizeClaim_norm_list_prod, BASizeClaim_norm_list_prod,
    BASizeClaim_norm_list_prod, BASizeClaim_norm_list_prod, BASizeClaim_norm_list_prod]
  simp only [List.map_map]
  have h1 : (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D.toLData ℓ)).prod ≤ Ψ ^ Γ.nS := by
    have := BASizeClaim_list_prod_le (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D.toLData ℓ)) Ψ (by
        intro x hx
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _) (by
        intro x hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        exact BASizeClaim_sedge_le D hG ℓ e (hN.2 e he))
    simpa [BAGraph.nS] using this
  have h3 : (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod ≤ 1 := by
    have := BASizeClaim_list_prod_le (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)) 1 (by
        intro x hx
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _) (by
        intro x hx
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        simp only [Function.comp, DEdge.val]
        split_ifs <;> simp)
    simpa using this
  have h0s : 0 ≤ (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D.toLData ℓ)).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have h0d : 0 ≤ (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hw' : (Γ.waved.map ((fun z : ℂ => ‖z‖) ∘ WEdge.val D.toLData ℓ)).prod =
      (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod := rfl
  have hp' : (Γ.psi.map ((fun z : ℂ => ‖z‖) ∘ BAPsiEdge.val D ℓ)).prod =
      (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod := rfl
  have hm' : (Γ.mdot.map ((fun z : ℂ => ‖z‖) ∘ BAMEdge.val D ℓ)).prod =
      (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod := rfl
  rw [hw', hp', hm']
  have hwn : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hpn : 0 ≤ (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hmn : 0 ≤ (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  calc ‖Γ.coeff‖ * (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D.toLData ℓ)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod *
        (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod *
        (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod * (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod
      ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod * 1 *
        (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod * (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod := by
        have hΨn : 0 ≤ Ψ ^ Γ.nS := pow_nonneg hΨ _
        gcongr
    _ = _ := by ring

end Term

/-! ## The sum over the internal labels -/

section Sum

/-- The algebra of the forest bound: a tree edge costs `K_j`, every other edge `a_j`; the dotted edges cost
`Kd` in both cases, the waved edges `K₁` or `a`. -/
private theorem BASizeClaim_alg_prod {I : Type} [Fintype I] [DecidableEq I] {p q r : ℕ} (a K₁ Kd : ℝ)
    (KJ aJ : Fin p ⊕ Fin q ⊕ Fin r → ℝ) (hK1 : ∀ jw, KJ (Sum.inl jw) = K₁) (hK2 : ∀ j', KJ (Sum.inr j') = Kd)
    (ha1 : ∀ jw, aJ (Sum.inl jw) = a) (ha2 : ∀ j', aJ (Sum.inr j') = Kd)
    (C : Finset I) (edgeT : I → Fin p ⊕ Fin q ⊕ Fin r) (hinj : Set.InjOn edgeT C) :
    (∏ c ∈ C, KJ (edgeT c)) * ∏ j ∈ (C.image edgeT)ᶜ, aJ j =
      K₁ ^ (C.filter fun c => ∃ jw, edgeT c = Sum.inl jw).card *
        a ^ (p - (C.filter fun c => ∃ jw, edgeT c = Sum.inl jw).card) * Kd ^ (q + r) := by
  classical
  set S := C.image edgeT with hS
  set TW := C.filter fun c => ∃ jw, edgeT c = Sum.inl jw with hTW
  have h1 : (∏ c ∈ C, KJ (edgeT c)) = ∏ j ∈ S, KJ j := (Finset.prod_image hinj).symm
  set g : Fin p ⊕ Fin q ⊕ Fin r → ℝ := fun j => if j ∈ S then KJ j else aJ j with hg
  have h2 : (∏ j ∈ S, KJ j) * ∏ j ∈ Sᶜ, aJ j = ∏ j, g j := by
    rw [← Finset.prod_mul_prod_compl S g]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by simp [hg, hj]
    · exact Finset.prod_congr rfl fun j hj => by simp [hg, (Finset.mem_compl.1 hj)]
  rw [h1, h2, Fintype.prod_sum_type, Fintype.prod_sum_type]
  have h3 : ∀ j', g (Sum.inr j') = Kd := fun j' => by
    simp only [hg]
    split_ifs
    · exact hK2 j'
    · exact ha2 j'
  simp only [h3, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_add]
  set U := Finset.univ.filter (fun jw : Fin p => Sum.inl jw ∈ S) with hU
  have h4 : ∏ jw : Fin p, g (Sum.inl jw) = K₁ ^ U.card * a ^ (p - U.card) := by
    have : ∀ jw : Fin p, g (Sum.inl jw) = if Sum.inl jw ∈ S then K₁ else a := fun jw => by
      simp only [hg]
      split_ifs
      · exact hK1 jw
      · exact ha1 jw
    simp only [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hUc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p)))
      (fun jw => Sum.inl jw ∈ S)
    rw [Finset.card_univ, Fintype.card_fin] at hUc
    have e1 : (Finset.univ.filter fun jw : Fin p => ¬ Sum.inl jw ∈ S).card = p - U.card := by
      simp only [hU]
      omega
    rw [e1]
  have h5 : U.card = TW.card := by
    symm
    refine Finset.card_bij (fun c hc => (Finset.mem_filter.1 hc).2.choose) (fun c hc => ?_)
      (fun c₁ h₁ c₂ h₂ h => ?_) (fun jw hjw => ?_)
    · have hc' := Finset.mem_filter.1 hc
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and, hS]
      rw [← hc'.2.choose_spec]
      exact Finset.mem_image_of_mem _ hc'.1
    · have h₁' := Finset.mem_filter.1 h₁
      have h₂' := Finset.mem_filter.1 h₂
      refine hinj h₁'.1 h₂'.1 ?_
      rw [h₁'.2.choose_spec, h₂'.2.choose_spec, h]
    · have hjw' : Sum.inl jw ∈ S := by simpa [hU] using hjw
      obtain ⟨c, hcC, hc⟩ := Finset.mem_image.1 hjw'
      have hcT : c ∈ TW := Finset.mem_filter.2 ⟨hcC, jw, hc⟩
      refine ⟨c, hcT, ?_⟩
      have h6 := (Finset.mem_filter.1 hcT).2.choose_spec
      exact Sum.inl_injective (h6.symm.trans hc)
  rw [h4, h5]

variable {ι : Type} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype ι]
  [DecidableEq ι]

/-- The three bounds on `S`, `S⁺` give the three bounds on every waved-edge weight (as the private
`lwWVal_bound` in `Graph/LWSizeClaim.lean`). -/
private theorem BASizeClaim_wval_bound {D : LData ι} {a K₁ : ℝ} (hS : LWKBound D.S a K₁)
    (hSp : LWKBound D.Sp a K₁) (e : WEdge (E ⊕ I)) :
    (∀ x y, ‖lwWVal D e x y‖ ≤ a) ∧ (∀ x, ∑ y, ‖lwWVal D e x y‖ ≤ K₁) ∧
      (∀ y, ∑ x, ‖lwWVal D e x y‖ ≤ K₁) := by
  unfold lwWVal
  by_cases hc : e.col = true
  · by_cases hσ : e.σ = true
    · simp only [hc, hσ, ite_true]; exact hSp
    · have hσ' : e.σ = false := by simpa using hσ
      simp only [hc, hσ', ite_true, Bool.false_eq_true, ite_false, norm_star]
      exact ⟨fun x y => hSp.1 y x, fun x => hSp.2.2 x, fun y => hSp.2.1 y⟩
  · have hc' : e.col = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]; exact hS

/-- The weight of an edge of `J = waved ⊕ mdot ⊕ psi` at the labels `(x, y)` of its ends. -/
private def BASizeClaim_fJ (Γ : BAGraph E I) (D : BALData ι) : Γ.Jx → ι → ι → ℝ
  | Sum.inl j, x, y => ‖lwWVal D.toLData (Γ.waved.get j) x y‖
  | Sum.inr (Sum.inl _), x, y => ‖D.M x y‖
  | Sum.inr (Sum.inr _), x, y => ‖D.gPsi x y‖

private def BASizeClaim_aJ (Γ : BAGraph E I) (a Kd : ℝ) : Γ.Jx → ℝ
  | Sum.inl _ => a
  | Sum.inr _ => Kd

private theorem BASizeClaim_mdot_norm (D : BALData ι) {V : Type*} (ℓ : V → ι) (e : BAMEdge V) :
    ‖BAMEdge.val D ℓ e‖ = ‖D.M (ℓ e.x) (ℓ e.y)‖ := by
  unfold BAMEdge.val
  split_ifs <;> simp

private theorem BASizeClaim_prod_J (Γ : BAGraph E I) (D : BALData ι) (ℓ : E ⊕ I → ι) :
    (Γ.waved.map fun e => ‖WEdge.val D.toLData ℓ e‖).prod * (Γ.psi.map fun e => ‖BAPsiEdge.val D ℓ e‖).prod *
        (Γ.mdot.map fun e => ‖BAMEdge.val D ℓ e‖).prod =
      ∏ j : Γ.Jx, BASizeClaim_fJ Γ D j (ℓ (Γ.edgeEnds j).1) (ℓ (Γ.edgeEnds j).2) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, BASizeClaim_list_prod_fin, BASizeClaim_list_prod_fin,
    BASizeClaim_list_prod_fin]
  simp only [BASizeClaim_fJ, BAGraph.edgeEnds, BASizeClaim_mdot_norm]
  have hw : ∏ j : Fin Γ.waved.length, ‖WEdge.val D.toLData ℓ (Γ.waved.get j)‖ =
      ∏ j : Fin Γ.waved.length, ‖lwWVal D.toLData (Γ.waved.get j) (ℓ (Γ.waved.get j).x) (ℓ (Γ.waved.get j).y)‖ :=
    rfl
  have hp : ∏ j : Fin Γ.psi.length, ‖BAPsiEdge.val D ℓ (Γ.psi.get j)‖ =
      ∏ j : Fin Γ.psi.length, ‖D.gPsi (ℓ (Γ.psi.get j).x) (ℓ (Γ.psi.get j).y)‖ := rfl
  rw [hw, hp]
  ring

end Sum

/-! ## The claim `Γ ≺ size(Γ)`, deterministic form -/

section Claim

variable {ι : Type} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype ι]
  [DecidableEq ι]

private def BASizeClaim_KJ (Γ : BAGraph E I) (K₁ Kd : ℝ) : Γ.Jx → ℝ
  | Sum.inl _ => K₁
  | Sum.inr _ => Kd

/-- **The sum over the internal labels** of the product of the weights of the waved, `Ψ`-dotted and `M`-dotted edges:
`≤ N^{n_M} K₁^{n_A - n_M} a^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}`, by the peeling bound with the atomic forest. -/
private theorem BASizeClaim_sum_le (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData ι) {a K₁ Kd : ℝ}
    [Nonempty ι] (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) (hM : LWKBound D.M Kd Kd)
    (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → ι) :
    ∑ ℓi : I → ι, ((Γ.waved.map fun e => ‖WEdge.val D.toLData (Sum.elim ℓe ℓi) e‖).prod *
        (Γ.psi.map fun e => ‖BAPsiEdge.val D (Sum.elim ℓe ℓi) e‖).prod *
        (Γ.mdot.map fun e => ‖BAMEdge.val D (Sum.elim ℓe ℓi) e‖).prod) ≤
      (Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ (Γ.nA - Γ.nM) * a ^ (Γ.nW - (Γ.nA - Γ.nM)) *
        Kd ^ (Γ.mdot.length + Γ.psi.length) := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty ι›
  have hN0 : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  simp only [BASizeClaim_prod_J]
  obtain ⟨C, par, edge, ρ, hcard, hgcard, hrank, hedge, hinj⟩ := Γ.exists_forest hN.1
  rcases isEmpty_or_nonempty Γ.Jx with hJ | hJ
  · -- no edges: `C = ∅`
    have hC : C = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => by
      obtain ⟨j, _⟩ := hedge c hc
      exact hJ.false j
    have hw0 : Γ.waved.length = 0 := by
      by_contra h
      exact hJ.false (Sum.inl ⟨0, Nat.pos_of_ne_zero h⟩)
    have hm0 : Γ.mdot.length = 0 := by
      by_contra h
      exact hJ.false (Sum.inr (Sum.inl ⟨0, Nat.pos_of_ne_zero h⟩))
    have hp0 : Γ.psi.length = 0 := by
      by_contra h
      exact hJ.false (Sum.inr (Sum.inr ⟨0, Nat.pos_of_ne_zero h⟩))
    subst hC
    simp only [Finset.card_empty, zero_add, Finset.filter_empty] at hcard hgcard
    have hnW : Γ.nW = 0 := hw0
    simp only [hnW, hm0, hp0, Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, nsmul_eq_mul, mul_one, Nat.cast_pow, ← hcard, ← hgcard, Nat.sub_self, pow_zero, add_zero]
    simp
  · obtain ⟨j0⟩ := hJ
    let edgeT : I → Γ.Jx := fun c => (edge c).getD j0
    have hedgeT : ∀ c ∈ C, edge c = some (edgeT c) := fun c hc => by
      obtain ⟨j, hj, _⟩ := hedge c hc
      simp [edgeT, hj]
    have hinjT : Set.InjOn edgeT (C : Set I) := fun c₁ h₁ c₂ h₂ h =>
      hinj c₁ h₁ c₂ h₂ (by rw [hedgeT c₁ h₁, hedgeT c₂ h₂, h])
    have hmain := BASizeClaim_forest_sum_le (ι := ι) (I := I) (E := E) (J := Γ.Jx) ℓe
      (fun j => (Γ.edgeEnds j).1) (fun j => (Γ.edgeEnds j).2) (BASizeClaim_fJ Γ D)
      (BASizeClaim_aJ Γ a Kd) (BASizeClaim_KJ Γ K₁ Kd)
      (by rintro (j | j | j) x y <;> exact norm_nonneg _)
      (by
        rintro (j | j | j) x y
        · exact (BASizeClaim_wval_bound hS hSp _).1 x y
        · exact hM.1 x y
        · exact hP.1 x y)
      (by
        rintro (j | j | j) x
        · exact (BASizeClaim_wval_bound hS hSp _).2.1 x
        · exact hM.2.1 x
        · exact hP.2.1 x)
      (by
        rintro (j | j | j) y
        · exact (BASizeClaim_wval_bound hS hSp _).2.2 y
        · exact hM.2.2 y
        · exact hP.2.2 y)
      C par edgeT ρ hinjT
      (fun c hc => by
        obtain ⟨j, hj, hends⟩ := hedge c hc
        rw [hedgeT c hc] at hj
        cases hj
        exact hends)
      hrank
    have hfil : (C.filter fun c => ∃ j, edge c = some (Sum.inl j)) =
        C.filter fun c => ∃ jw, edgeT c = Sum.inl jw := by
      refine Finset.filter_congr fun c hc => ?_
      rw [hedgeT c hc]
      simp
    have halg := BASizeClaim_alg_prod (p := Γ.waved.length) (q := Γ.mdot.length) (r := Γ.psi.length)
      a K₁ Kd (BASizeClaim_KJ Γ K₁ Kd) (BASizeClaim_aJ Γ a Kd) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) C edgeT hinjT
    rw [← hfil] at halg
    set w := (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card with hw
    have hwA : w = Γ.nA - Γ.nM := by omega
    have hNM : Fintype.card I = C.card + Γ.nM := hcard.symm
    rw [mul_assoc, halg, hNM, pow_add] at hmain
    have hnW : Γ.nW = Γ.waved.length := rfl
    rw [← hwA]
    have hNp : 0 < (Fintype.card ι : ℝ) ^ C.card := pow_pos hN0 _
    have : (Fintype.card ι : ℝ) ^ C.card * ∑ ℓi : I → ι, ∏ j : Γ.Jx,
        BASizeClaim_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) ≤
        (Fintype.card ι : ℝ) ^ C.card * ((Fintype.card ι : ℝ) ^ Γ.nM * (K₁ ^ w * a ^ (Γ.nW - w) *
          Kd ^ (Γ.mdot.length + Γ.psi.length))) := by
      refine hmain.trans (le_of_eq ?_)
      rw [hnW]
      ring
    have h2 := le_of_mul_le_mul_left this hNp
    calc _ ≤ _ := h2
      _ = _ := by ring

end Claim

section Val

variable {ι : Type} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype ι]
  [DecidableEq ι]

/-- **The `L¹`-form of the BA claim `Γ ≺ size(Γ)`**: `|Γ.val| ≤ |coeff| Ψ^{n_S} N^{n_M} K₁^{n_A - n_M}
a^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}` for a normal BA graph, `‖G - M‖ ≤ Ψ` entrywise, and weights `S`, `S⁺`
(entries `≤ a`, row and column sums `≤ K₁`), `M`, `g₀ Ψ` (entries, row and column sums `≤ Kd`).  No `hM : M = m I`. -/
private theorem BASizeClaim_val_le (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData ι) {Ψ a K₁ Kd : ℝ}
    [Nonempty ι] (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁)
    (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → ι) :
    ‖Γ.val D ℓe‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      ((Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ (Γ.nA - Γ.nM) * a ^ (Γ.nW - (Γ.nA - Γ.nM)) *
        Kd ^ (Γ.mdot.length + Γ.psi.length)) := by
  obtain ⟨x0⟩ := ‹Nonempty ι›
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG x0 x0)
  unfold BAGraph.val
  calc ‖∑ ℓi : I → ι, Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ∑ ℓi : I → ι, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ℓi : I → ι, ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        ((Γ.waved.map fun e => ‖WEdge.val D.toLData (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.psi.map fun e => ‖BAPsiEdge.val D (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.mdot.map fun e => ‖BAMEdge.val D (Sum.elim ℓe ℓi) e‖).prod) :=
        Finset.sum_le_sum fun ℓi _ => BASizeClaim_term_le Γ hN D hΨ hG _
    _ = ‖Γ.coeff‖ * Ψ ^ Γ.nS * ∑ ℓi : I → ι,
        ((Γ.waved.map fun e => ‖WEdge.val D.toLData (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.psi.map fun e => ‖BAPsiEdge.val D (Sum.elim ℓe ℓi) e‖).prod *
          (Γ.mdot.map fun e => ‖BAMEdge.val D (Sum.elim ℓe ℓi) e‖).prod) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (BASizeClaim_sum_le Γ hN D hS hSp hM hP ℓe)
          (mul_nonneg (norm_nonneg _) (pow_nonneg hΨ _))

/-- The size identity `N^{n_M} (K₀ W^{-d})^{n_W-(n_A-n_M)} = K₀^{n_W-(n_A-n_M)} (L^d)^{n_M} W^{-d(n_W-n_A)}`
(`N = (W L)^d`; as the private `lwSize_alg` in `Graph/LWSizeClaim.lean`, with `n_A` in place of `n_V`). -/
private theorem BASizeClaim_size_alg (W d L nM nV nW : ℕ) (hW : (W : ℝ) ≠ 0) (h1 : nM ≤ nV)
    (h2 : nV - nM ≤ nW) (K₀ : ℝ) :
    ((((W * L) ^ d : ℕ) : ℝ)) ^ nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (nW - (nV - nM)) =
      K₀ ^ (nW - (nV - nM)) * (((L : ℝ) ^ d) ^ nM * (W : ℝ) ^ (-(d : ℤ) * ((nW : ℤ) - nV))) := by
  obtain ⟨t, ht⟩ : ∃ t, nW = (nV - nM) + t := ⟨nW - (nV - nM), by omega⟩
  have htt : nW - (nV - nM) = t := by omega
  have hexp : -(d : ℤ) * ((nW : ℤ) - nV) = ((d * nM : ℕ) : ℤ) - ((d * t : ℕ) : ℤ) := by
    have : (nW : ℤ) - nV = (t : ℤ) - nM := by omega
    rw [this]; push_cast; ring
  rw [htt, hexp, zpow_sub₀ hW, zpow_natCast, zpow_natCast]
  push_cast
  rw [mul_pow, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  field_simp
  rw [pow_mul (W : ℝ) d t]

end Val

section ClaimIdx

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
  [DecidableEq I]

/-- **The claim `Γ ≺ size(Γ)` at BA** (Definition B.5 `def scalingBA`), deterministic form.  For a normal BA graph `Γ`, data `D` on
the fine lattice `Z_{WL}^d` with the entry bound `‖G - M‖ ≤ Ψ` (the hypothesis BA has in place of `M = m I`), and
weights `S`, `S⁺` with entries `≤ K₀ W^{-d}` and row and column sums `≤ K₁`, `M` and `g₀ Ψ` with entries, row and column
sums `≤ Kd`: `|Γ.val| ≤ C_Γ · size(Γ)`, `C_Γ = Γ.sizeConst K₀ K₁ Kd`, for every `Ψ` and every external labelling.
No window on `Ψ`, no smallness of `g₀`. -/
theorem baClaimSize (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ}
    (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hM : LWKBound D.M Kd Kd)
    (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → Idx d L W) :
    ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hb := BASizeClaim_val_le Γ hN D hG hS hSp hM hP ℓe
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hcard : (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) := by
    rw [card_Idx]
  rw [hcard] at hb
  refine hb.trans (le_of_eq ?_)
  have hal := BASizeClaim_size_alg W d L Γ.nM Γ.nA Γ.nW hW h1 h2 K₀
  unfold BAGraph.sizeConst BAGraph.scalingSize Counters.scalingSize
  change ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nA - Γ.nM) *
      (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)) = _
  calc ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nA - Γ.nM) *
        (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length))
      = ‖Γ.coeff‖ * Ψ ^ Γ.nS * K₁ ^ (Γ.nA - Γ.nM) * Kd ^ (Γ.mdot.length + Γ.psi.length) *
        (((((W * L) ^ d : ℕ) : ℝ)) ^ Γ.nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM))) := by ring
    _ = _ := by rw [hal]; simp only [BAGraph.counters]; ring

end ClaimIdx

end RBM.Graph
