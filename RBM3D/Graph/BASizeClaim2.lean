/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASizeClaim

/-!
# BA-L3c2 (T2412), part 2: `claim:size` at BA, the model forms and the confinement tails

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (`7_8:line`),
`paper/tex/B_graphical_lemmas.tex` (`B:line`): `claim:size` (`7_8:264-266`: `Γ ≺ size(Γ)` for
normal
graphs), `scalemole` (`7_8:255-258`), the BA size `(eq_defsize_BA)` (`B:349-350`), (B.15)
(`B:302-304`).  Part 1 is `Graph/BASizeClaim` (the kernel edges and the atomic forest); this file
imports it.  The paper gives no proof of `claim:size` (delta T2040m).

## Contents (namespace `RBM.Graph`, private prefix `BASizeClaim_`)

1. `BAGraph.sizeConst` (`C_Γ = ‖coeff‖ K₁^{n_A - n_M} K₀^{n_W - (n_A - n_M)} Kd^{#M + #Ψ}`), the
   term
   bound (`BASizeClaim_term_le`: every solid edge of a normal BA graph is circled, so it is `≤ Ψ`
   by
   `‖G - M‖ ≤ Ψ`; the `×`-dotted factors are `≤ 1`), the sum over the internal labels
   (`BASizeClaim_sum_le`: the peeling bound with the atomic forest and per-edge constants: a tree
   `M`- or
   `Ψ`-dotted edge costs `Kd` through its row or column sum, a non-tree one costs `Kd` through
   its entry,
   a tree waved edge `K₁`, a non-tree waved edge `K₀ W^{-d}`, a root `N`).
2. **`baClaimSize`**: the BA `claim:size`, deterministic form, with the hypotheses BA has (no
   `hM : M = m I`, which is false at BA for every `g₀ ≠ 0`); **`baClaimSizeG`**: the general
   graph,
   through `BAGraph.val_eq_partition`.
3. **`baClaimSize_E`**, **`baClaimSizeG_E`**: the model forms with `(K₀, K₁, Kd)` depending on
   `(d, Λ, κ)` only; **`baSpTail_E`**, **`baMTail_E`**, **`baTail_log`**: the confinement tails
   (the
   radius `(log W)^p`, `p > 1`).
4. Compiled instances at `d = 3`, `L = 4`, `W = 2`, the flow point `P : FlowPt 4 10`, `baLWT1`,
   `baGGT1`.

No smallness of `g₀` and no `(Cλ)^{|a-b|}` decay is used: the uniform decay rate enters only
through
the constants `K₀`, `K₁`, `Kd` (`BAct_rate`, `BAp5s_rate`).
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
`claim:size`, depending on the graph and on `(K₀, K₁, Kd)` (that is on `d, Λ, κ`) only. -/
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

/-- The three bounds on `S`, `S⁺` give the three bounds on every waved-edge weight (a copy of the private
`lwWVal_bound`, `LWSizeClaim.lean:837`). -/
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

/-! ## `claim:size`, deterministic form -/

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

/-- **The `L¹`-form of the BA `claim:size`**: `|Γ.val| ≤ |coeff| Ψ^{n_S} N^{n_M} K₁^{n_A - n_M}
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
(`N = (W L)^d`; a copy of the private `lwSize_alg`, `LWSizeClaim.lean:1082`, with `n_A` in place of `n_V`). -/
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

/-- **`claim:size` at BA** (`7_8:264-266`, `B:345-350`), deterministic form.  For a normal BA graph `Γ`, data `D` on
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

private theorem BASizeClaim_sizeG_le_iff (Γ : BAGraph E I) (Ψ : ℝ) (W d L : ℕ) (B : ℝ) :
    Γ.scalingSizeG Ψ W d L ≤ B ↔ 0 ≤ B ∧ ∀ P ∈ Γ.partition, P.scalingSize Ψ W d L ≤ B := by
  unfold BAGraph.scalingSizeG
  generalize Γ.partition = L'
  induction L' with
  | nil => simp
  | cons P L' ih =>
    simp only [List.map_cons, List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    tauto

private theorem BASizeClaim_norm_sum_le_of_le {α : Type*} (l : List α) (f : α → ℂ) (c : α → ℝ) (G : ℝ)
    (h : ∀ x ∈ l, ‖f x‖ ≤ c x * G) : ‖(l.map f).sum‖ ≤ (l.map c).sum * G := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    calc ‖f x + (l.map f).sum‖ ≤ ‖f x‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ c x * G + (l.map c).sum * G := add_le_add h1 h2
      _ = _ := by ring

private theorem BASizeClaim_val_of_factor {ι : Type} [Fintype ι] [DecidableEq ι] (P : BAPGraph E)
    (D : BALData ι) {ℓe : E → ι} {ℓ' : P.E' → ι} (h : ℓe = ℓ' ∘ P.ext) : P.val D ℓe = P.g.val D ℓ' := by
  classical
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', h⟩
  simp only [BAPGraph.val, hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans h

private theorem BASizeClaim_val_of_not {ι : Type} [Fintype ι] [DecidableEq ι] (P : BAPGraph E)
    (D : BALData ι) {ℓe : E → ι} (h : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : P.val D ℓe = 0 := by
  classical
  simp only [BAPGraph.val, h, ↓reduceDIte]

/-- **`claim:size` at BA for a general graph** (`B:354`, `scalingSizeG`): the BA partition of `Γ`
(`BAGraph.val_eq_partition`, unconditional) gives `|Γ.val| ≤ (Σ_P C_P) · size(Γ)` with
`size(Γ) = max_P size(P.g)`. -/
theorem baClaimSizeG (Γ : BAGraph E I) (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ} (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (hKd : 0 ≤ Kd) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ)
    (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → Idx d L W) :
    ‖Γ.val D ℓe‖ ≤ (Γ.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * Γ.scalingSizeG Ψ W d L := by
  rw [Γ.val_eq_partition D ℓe]
  unfold BAComb.val
  have hB := (BASizeClaim_sizeG_le_iff Γ Ψ W d L _).1 le_rfl
  refine BASizeClaim_norm_sum_le_of_le Γ.partition (fun P : BAPGraph E => P.val D ℓe)
    (fun P : BAPGraph E => P.g.sizeConst K₀ K₁ Kd) _ fun P hP' => ?_
  have hPN := Γ.partition_normal P hP'
  by_cases h : ∃ ℓ', ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    rw [BASizeClaim_val_of_factor P D hℓ']
    exact (baClaimSize P.g hPN D hG hS hSp hM hP ℓ').trans
      (mul_le_mul_of_nonneg_left (hB.2 P hP') (BASizeClaim_sizeConst_nonneg P.g hK₀ hK₁ hKd))
  · rw [BASizeClaim_val_of_not P D h, norm_zero]
    exact mul_nonneg (BASizeClaim_sizeConst_nonneg P.g hK₀ hK₁ hKd) hB.1

end ClaimIdx

/-! ## `claim:size` for the matrices of the BA model, and the confinement tails -/

section Model

/-- **`claim:size` with the constants of the BA model** (target 3 with target 1).  For `d ≥ 3`, `Λ`, `κ > 0` there
are constants `(K₀, K₁, Kd)`, depending on `(d, Λ, κ)` only, such that for every `L ≥ 3`, `W ≥ 1`, `0 < g₀ ≤ Λ`,
`0 ≤ t < 1`, every real-axis datum `BAReal d L g₀ κ E m`, every normal BA graph `Γ` and every data `D` with
`S = t · svarF`, `S⁺ = S W`, `M = BAlwM`, `gPsi = g₀ Ψ` and `G` satisfying `‖G - M‖ ≤ Ψ` entrywise:
`|Γ.val D ℓe| ≤ C_Γ · size(Γ)`, never depending on `L, W, t, E, g₀, Ψ`. -/
theorem baClaimSize_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'),
          Γ.Normal → ∀ D : BALData (Idx d L W), D.S = Matrix.of (BAlwS d L W t) →
          D.Sp = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m → D.M = BAlwM d L W g0 E m →
          D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ Ψ : ℝ, (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) →
          ∀ ℓe : E' → Idx d L W, ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L := by
  obtain ⟨K₀, K₁, Kd, h₀, h₁, hKd, h⟩ := baKBound_E d hd Λ κ hΛ hκ
  refine ⟨K₀, K₁, Kd, h₀, h₁, hKd,
    fun L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 E' I' _ _ _ _ Γ hN D hS hSp hM hP Ψ hG ℓe => ?_⟩
  obtain ⟨hS', hSp', hM', hP'⟩ := h L W hL g0 E t m hg hgΛ hr ht0 ht1
  rw [← hS] at hS'
  rw [← hSp] at hSp'
  rw [← hM] at hM'
  rw [← hP] at hP'
  exact baClaimSize Γ hN D hG hS' hSp' hM' hP' ℓe

/-- **`claim:size` at BA for a general graph, with the constants of the model**: `|Γ.val| ≤ (Σ_P C_P) ·
size_G(Γ)`, `size_G(Γ) = max_P size(P)` over the BA partition. -/
theorem baClaimSizeG_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'),
          ∀ D : BALData (Idx d L W), D.S = Matrix.of (BAlwS d L W t) →
          D.Sp = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m → D.M = BAlwM d L W g0 E m →
          D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ Ψ : ℝ, (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) →
          ∀ ℓe : E' → Idx d L W,
            ‖Γ.val D ℓe‖ ≤ (Γ.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum *
              Γ.scalingSizeG Ψ W d L := by
  obtain ⟨K₀, K₁, Kd, h₀, h₁, hKd, h⟩ := baKBound_E d hd Λ κ hΛ hκ
  refine ⟨K₀, K₁, Kd, h₀, h₁, hKd,
    fun L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 E' I' _ _ _ _ Γ D hS hSp hM hP Ψ hG ℓe => ?_⟩
  obtain ⟨hS', hSp', hM', hP'⟩ := h L W hL g0 E t m hg hgΛ hr ht0 ht1
  rw [← hS] at hS'
  rw [← hSp] at hSp'
  rw [← hM] at hM'
  rw [← hP] at hP'
  exact baClaimSizeG Γ D h₀.le h₁.le hKd hG hS' hSp' hM' hP' ℓe

end Model

section Tail

/-- **T4 `baSpTail_E`** (twin of `lwSpOf_tail_E`, `LWSizeClaim.lean:1316`): the tail of a row of `S⁺ = S W` beyond
block distance `R` is `≤ C₂ e^{-c₂ R}`, uniformly in `L, W, t, E, g₀` (`(C₂, c₂)` depend on `(d, Λ, κ)` only). -/
theorem baSpTail_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ (x : Idx d L W) (R : ℝ),
          ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)),
            ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤ C₂ * Real.exp (-(c₂ * R)) := by
  obtain ⟨C, c, hC, hc, h⟩ := baSpDecay d hd Λ κ hΛ hκ
  have hE : 0 < expC (d - 2) (c / 2) := by
    unfold expC
    have : 0 < c / 2 := by linarith
    positivity
  refine ⟨C * expC (d - 2) (c / 2), c / 2, mul_pos hC hE, by linarith,
    fun L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 x R => ?_⟩
  have := lwKernel_tail hd hC.le hc (h L W hL g0 E t m hg hgΛ hr ht0 ht1).2 x R
  convert this using 3
  ring

/-- **T4 `baMTail_E`**: the tail of a row of `M` beyond block distance `R` is `≤ C₂ e^{-c₂ R}` (the block spread of
`(B.15)`), from the Combes-Thomas decay of `M^{(B)}` (`BAMB_decay_large`) and the fibre sum. -/
theorem baMTail_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L →
      ∀ (g0 E : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m →
        ∀ (x : Idx d L W) (R : ℝ),
          ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)),
            ‖BAlwM d L W g0 E m x y‖ ≤ C₂ * Real.exp (-(c₂ * R)) := by
  have hd0 : 0 < d := by omega
  have hc := RBM.BA.BAct_rate_pos d Λ κ hd0 hΛ hκ
  set c := RBM.BA.BAct_rate d Λ κ with hcdef
  have hE : 0 < expC (d - 2) (c / 2) := by
    unfold expC
    have : 0 < c / 2 := by linarith
    positivity
  refine ⟨c⁻¹ * expC (d - 2) (c / 2), c / 2, by positivity, by linarith,
    fun L W _ _ hL g0 E m hg hgΛ hr x R => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hr.1.1.ne'
  rw [Finset.sum_filter]
  have h1 : ∀ y : Idx (k + 2) L W, (if R ≤ (lwBdist (k + 2) L W x y : ℝ) then ‖BAlwM (k + 2) L W g0 E m x y‖ else 0) =
      if (split (k + 2) L W x).2 = (split (k + 2) L W y).2 then
        (fun b : Zd (k + 2) L => if R ≤ (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ) then
          ‖RBM.BA.BAMB (k + 2) L g0 (E : ℂ) m (split (k + 2) L W x).1 b‖ else 0) (split (k + 2) L W y).1
      else 0 := by
    intro y
    unfold BAlwM
    rw [RBM.BA.BAMres_fine_apply (k + 2) L W g0 (E : ℂ) m hw x y]
    by_cases ho : (split (k + 2) L W x).2 = (split (k + 2) L W y).2
    · simp [ho, lwBdist]
    · simp [ho]
  simp only [h1]
  rw [BASizeClaim_fibre_sum x (fun b : Zd (k + 2) L => if R ≤ (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ) then
          ‖RBM.BA.BAMB (k + 2) L g0 (E : ℂ) m (split (k + 2) L W x).1 b‖ else 0)]
  calc ∑ b : Zd (k + 2) L, (if R ≤ (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ) then
          ‖RBM.BA.BAMB (k + 2) L g0 (E : ℂ) m (split (k + 2) L W x).1 b‖ else 0)
      ≤ ∑ b : Zd (k + 2) L, c⁻¹ * Real.exp (-(c * R / 2)) *
          Real.exp (-((c / 2) * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        by_cases hR : R ≤ (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ)
        · simp only [hR, ↓reduceIte]
          refine (RBM.BA.BAMB_decay_large (k + 2) L hL (by omega) Λ g0 κ E m hΛ hg hgΛ hκ hr _ _).trans ?_
          have h2 : Real.exp (-c * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ)) ≤
              Real.exp (-(c * R / 2)) *
                Real.exp (-((c / 2) * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith
          calc (RBM.BA.BAct_rate (k + 2) Λ κ)⁻¹ * Real.exp (-RBM.BA.BAct_rate (k + 2) Λ κ *
                (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))
              ≤ c⁻¹ * (Real.exp (-(c * R / 2)) * Real.exp (-((c / 2) *
                (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ)))) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = _ := by ring
        · simp only [hR, ↓reduceIte]
          positivity
    _ = c⁻¹ * Real.exp (-(c * R / 2)) * ∑ b : Zd (k + 2) L,
          Real.exp (-((c / 2) * (zdistD (k + 2) L ((split (k + 2) L W x).1 - b) : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ c⁻¹ * Real.exp (-(c * R / 2)) * expC k (c / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (le_of_eq ?_) (sum_radial_exp_decay_le (L := L) k (by linarith : 0 < c / 2))
        exact Fintype.sum_equiv (Equiv.subLeft _) _ _ fun b => rfl
    _ = _ := by
        simp only [Nat.add_sub_cancel]
        rw [show -(c / 2 * R) = -(c * R / 2) by ring]
        ring

/-- **T4 `baTail_log`** (twin of `lwTail_log32`, `LWSizeClaim.lean:1285`, with `3/2` replaced by `p > 1`): at the radius
`R = (log W)^p` the tail `e^{-cR/2}` is eventually `≤ W^{-D}`. -/
theorem baTail_log (c : ℝ) (hc : 0 < c) (p : ℝ) (hp : 1 < p) (D : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      Real.exp (-(c * (Real.log W) ^ p / 2)) ≤ (W : ℝ) ^ (-D) := by
  have hp1 : 0 < p - 1 := by linarith
  set s : ℝ := (2 * |D| / c) ^ (1 / (p - 1)) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg (by positivity) _
  refine ⟨⌈Real.exp s⌉₊ + 2, fun W hW => ?_⟩
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast (by omega : 2 ≤ W)
  have hWpos : (0 : ℝ) < W := by linarith
  have hlogpos : 0 < Real.log W := Real.log_pos (by linarith)
  have hlog : s ≤ Real.log W := by
    have h1 : Real.exp s ≤ (W : ℝ) := by
      have := Nat.le_ceil (Real.exp s)
      have h2 : ((⌈Real.exp s⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈Real.exp s⌉₊ ≤ W)
      linarith
    rw [← Real.log_exp s]
    exact Real.log_le_log (Real.exp_pos _) h1
  rw [Real.rpow_def_of_pos hWpos]
  apply Real.exp_le_exp.2
  have hsp : s ^ (p - 1) = 2 * |D| / c := by
    rw [hs, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hp1.ne', Real.rpow_one]
  have hge : 2 * |D| / c ≤ (Real.log W) ^ (p - 1) := by
    rw [← hsp]
    exact Real.rpow_le_rpow hs0 hlog hp1.le
  have hpow : (Real.log W) ^ p = Real.log W * (Real.log W) ^ (p - 1) := by
    rw [show p = 1 + (p - 1) by ring, Real.rpow_add hlogpos, Real.rpow_one]
    ring_nf
  rw [hpow]
  have h4 : 2 * |D| ≤ c * (Real.log W) ^ (p - 1) := by
    have := mul_le_mul_of_nonneg_left hge hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have h5 := le_abs_self D
  have h6 : 0 ≤ Real.log W := hlogpos.le
  nlinarith [mul_le_mul_of_nonneg_left h4 h6]

end Tail

/-! ## Compiled nonempty instances (`d = 3`, `L = 4`, `W = 2`, `t = 1/2`, the flow point `P : FlowPt 4 10`)

`P.g0 ∈ (0, 10]`, a real energy `P.E` and `P.m0` with `BAReal 3 4 P.g0 (Im P.m0) P.E P.m0` (`Λ = 10`, `κ = Im P.m0 > 0`);
`G = M + (1/100) J`, so `|Ǧ_{xy}| = 1/100` for all `x, y`, the diagonal included.  The graphs of `BAVocabInst`: `baLWT1`
(normal, `(n_S, n_W, n_A, n_M) = (2, 1, 2, 1)`, no external vertex) and `baGGT1` (normal, `(0, 1, 1, 0)`, two external
vertices with the same offset in different blocks).  Every deterministic hypothesis of every theorem is discharged. -/

namespace BASizeClaimInst2

open RBM.BA.MFixedPointInst BAVocabInst

/-- The BA model data at `P`, `t = 1/2`, `W = 2`: `M = BAlwM`, `S`, `S⁺ = S W`, `g₀ Ψ`, and `G = M + (1/100) J`. -/
def D0 : BALData (Idx 3 4 2) where
  G := Matrix.of fun x y => BAlwM 3 4 2 P.g0 P.E P.m0 x y + 1 / 100
  M := BAlwM 3 4 2 P.g0 P.E P.m0
  S := Matrix.of (BAlwS 3 4 2 (1 / 2))
  Sp := Matrix.of (BAlwS 3 4 2 (1 / 2)) * BAlwW 3 4 2 P.g0 P.E (1 / 2) P.m0
  gPsi := (P.g0 : ℂ) • PsiI 3 4 2

theorem D0_hG : ∀ x y, ‖D0.G x y - D0.M x y‖ ≤ 1 / 100 := by
  intro x y
  simp [D0]

/-- Two external labels with the same offset in different blocks (`W = 2`: the points `0` and `2` of each coordinate). -/
def ellInst : Fin 2 → Idx 3 4 2 := ![fun _ => 0, fun _ => 2]

/-- **Instance of `baClaimSize` and `baClaimSizeG`** (the deterministic form, no `hM`) on `baLWT1` at `D0`: the
constants `(K₀, K₁, Kd)` come from `baKBound_E`; the size is positive. -/
example : ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ baLWT1.counters = ⟨2, 1, 2, 1, 0, 0⟩ ∧
    0 < baLWT1.scalingSize (1 / 100) 2 3 4 ∧
    ‖baLWT1.val D0 Fin.elim0‖ ≤ baLWT1.sizeConst K₀ K₁ Kd * baLWT1.scalingSize (1 / 100) 2 3 4 ∧
    ‖baLWT1.val D0 Fin.elim0‖ ≤
      (baLWT1.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * baLWT1.scalingSizeG (1 / 100) 2 3 4 := by
  have hκ : 0 < P.m0.im := P.real.1.1
  obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := baKBound_E 3 le_rfl 10 P.m0.im (by norm_num) hκ
  obtain ⟨hS, hSp, hM, hP⟩ := hK 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num)
    (by norm_num)
  refine ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, baLWT1_counters, ?_,
    baClaimSize baLWT1 ⟨by decide, by decide⟩ D0 D0_hG hS hSp hM hP _,
    baClaimSizeG baLWT1 D0 hK₀.le hK₁.le hKd D0_hG hS hSp hM hP _⟩
  unfold BAGraph.scalingSize
  rw [baLWT1_counters]
  simp only [Counters.scalingSize]
  norm_num

/-- **Instance of `baClaimSize_E` and `baClaimSizeG_E`** on `baGGT1` (two external vertices) at `D0`. -/
example : (∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ baGGT1.counters = ⟨0, 1, 1, 0, 0, 0⟩ ∧
      0 < baGGT1.scalingSize (1 / 100) 2 3 4 ∧
      ‖baGGT1.val D0 ellInst‖ ≤ baGGT1.sizeConst K₀ K₁ Kd * baGGT1.scalingSize (1 / 100) 2 3 4) ∧
    (∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
      ‖baGGT1.val D0 ellInst‖ ≤
        (baGGT1.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * baGGT1.scalingSizeG (1 / 100) 2 3 4) := by
  have hκ : 0 < P.m0.im := P.real.1.1
  refine ⟨?_, ?_⟩
  · obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := baClaimSize_E 3 le_rfl 10 P.m0.im (by norm_num) hκ
    refine ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, baGGT1_counters, ?_,
      hK 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num) (Fin 2) (Fin 3)
        baGGT1 ⟨by decide, by decide⟩ D0 rfl rfl rfl rfl (1 / 100) D0_hG _⟩
    unfold BAGraph.scalingSize
    rw [baGGT1_counters]
    simp only [Counters.scalingSize]
    norm_num
  · obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := baClaimSizeG_E 3 le_rfl 10 P.m0.im (by norm_num) hκ
    exact ⟨K₀, K₁, Kd, hK₀, hK₁, hKd,
      hK 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real (by norm_num) (by norm_num) (Fin 2) (Fin 3)
        baGGT1 D0 rfl rfl rfl rfl (1 / 100) D0_hG _⟩

/-- **Instance of the tails** `baSpTail_E`, `baMTail_E`, `baTail_log` at `P` (`x = 0`, radius `R = 1`; `c = 1`, `p = 3/2`,
`D = 3`). -/
example : (∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ x : Idx 3 4 2,
      ∑ y ∈ Finset.univ.filter (fun y => 1 ≤ (lwBdist 3 4 2 x y : ℝ)),
        ‖(Matrix.of (BAlwS 3 4 2 (1 / 2)) * BAlwW 3 4 2 P.g0 P.E (1 / 2) P.m0) x y‖ ≤ C₂ * Real.exp (-(c₂ * 1))) ∧
    (∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ x : Idx 3 4 2,
      ∑ y ∈ Finset.univ.filter (fun y => 1 ≤ (lwBdist 3 4 2 x y : ℝ)),
        ‖BAlwM 3 4 2 P.g0 P.E P.m0 x y‖ ≤ C₂ * Real.exp (-(c₂ * 1))) ∧
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      Real.exp (-(1 * (Real.log W) ^ ((3 : ℝ) / 2) / 2)) ≤ (W : ℝ) ^ (-(3 : ℝ)) := by
  have hκ : 0 < P.m0.im := P.real.1.1
  refine ⟨?_, ?_, baTail_log 1 one_pos (3 / 2) (by norm_num) 3⟩
  · obtain ⟨C₂, c₂, hC₂, hc₂, h⟩ := baSpTail_E 3 le_rfl 10 P.m0.im (by norm_num) hκ
    exact ⟨C₂, c₂, hC₂, hc₂, fun x => h 4 2 (by norm_num) P.g0 P.E (1 / 2) P.m0 P.g0_pos P.g0_le P.real
      (by norm_num) (by norm_num) x 1⟩
  · obtain ⟨C₂, c₂, hC₂, hc₂, h⟩ := baMTail_E 3 le_rfl 10 P.m0.im (by norm_num) hκ
    exact ⟨C₂, c₂, hC₂, hc₂, fun x => h 4 2 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real x 1⟩

end BASizeClaimInst2

end RBM.Graph
