/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import RBM3D.Loop.KLTree

/-!
# The cut of a tree at an internal edge and the cut bijection, `d ≥ 3`

The value of the tree of a crossing-free family `F ∈ T_SP(n)` with leaf weights `M v` and
internal edge weights `E J` is `KLtreeValW` of `RBM3D/Loop/KLTree.lean`, where the laminar
vocabulary (`KLwholeP`, `KLnodes`, `KLIsTSP`, …) is also defined.

* `KLgval` : the value of a weighted tree over arbitrary node, leaf and edge types; its
  transport `KLgval_congr` along isomorphisms; the splitting identity `KLgval_split` (two
  parts joined by one edge `P S Q`).
* `KLtreeValW_eq_gval` and the derivative `KLhasDerivAt_treeValW` (one term per edge).
* `KLtreeValW_cut` (section `Cut`): cutting `F ∋ J` at the internal edge `J` carrying `P S Q`,
  the tree value is `∑_{u,w}` (inside tree with the extra root leaf `(u, Pᵀ)`) `S_{uw}` (outside
  tree with the glue leaf `(w, Q)`).
* `CutIn`, `CutOut` (sections): the inside polygon, with `KLwIn J + 1 = j - i + 1` vertices, and
  the outside polygon, with `n - KLwIn J + 1` vertices; the vertex maps `KLinV`, `KLoutV`,
  `KLglueV`; `KLgval_in_eq`, `KLgval_out_eq`: the inside and the outside part of the cut are
  again tree values (of `KLFIn F J`, `KLFOut F J`).
* `CutBij` (section): the maps `KLunShift`, `KLunColP`, the glued family `KLglueF`, the
  membership lemmas, `KLglueF_cut`, `KLFIn_glueF`, `KLFOut_glueF` and the cut bijection `KLsum_cut`:
  `∑_{F ∈ T_SP(n), J ∈ F} f (F_out) (F_in) = ∑_{G ∈ T_SP(n-w+1)} ∑_{H ∈ T_SP(w+1)} f G H`,
  `w = KLwIn J`.

Public: `KLgval`, `KLtreeValW_cut`, `KLsum_cut`, the bridge lemmas `KLgval_in_eq`,
`KLgval_out_eq`, and the objects their statements mention; every other helper is `private`.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

section Generic

variable (d L : ℕ) [NeZero L]

/-- The value of a weighted tree with internal nodes `Nd`, leaves `Lf` and internal edges
`Ed`: the leaf `ℓ` has label `a ℓ`, weight `M ℓ` and hangs on `p ℓ`; the edge `e` has weight
`E e` from `c e` to `q e`.  `∑_b ∏_ℓ (M_ℓ)_{a_ℓ, b(p ℓ)} ∏_e (E_e)_{b(c e), b(q e)}`. -/
noncomputable def KLgval {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf]
    [Fintype Ed]
    (a : Lf → Zd d L) (M : Lf → Matrix (Zd d L) (Zd d L) ℂ) (p : Lf → Nd)
    (E : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → Nd) : ℂ :=
  ∑ b : Nd → Zd d L, (∏ ℓ, M ℓ (a ℓ) (b (p ℓ))) * ∏ e, E e (b (c e)) (b (q e))

variable {d L}

/-- **Transport**: the value only depends on the tree up to isomorphism. -/
theorem KLgval_congr {Nd Lf Ed Nd' Lf' Ed' : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf]
    [Fintype Ed] [Fintype Nd'] [DecidableEq Nd'] [Fintype Lf'] [Fintype Ed']
    (eN : Nd ≃ Nd') (eL : Lf ≃ Lf') (eE : Ed ≃ Ed')
    {a : Lf → Zd d L} {M : Lf → Matrix (Zd d L) (Zd d L) ℂ} {p : Lf → Nd}
    {E : Ed → Matrix (Zd d L) (Zd d L) ℂ} {c q : Ed → Nd}
    {a' : Lf' → Zd d L} {M' : Lf' → Matrix (Zd d L) (Zd d L) ℂ} {p' : Lf' → Nd'}
    {E' : Ed' → Matrix (Zd d L) (Zd d L) ℂ} {c' q' : Ed' → Nd'}
    (ha : ∀ ℓ, a' (eL ℓ) = a ℓ) (hM : ∀ ℓ, M' (eL ℓ) = M ℓ) (hp : ∀ ℓ, p' (eL ℓ) = eN (p ℓ))
    (hE : ∀ e, E' (eE e) = E e) (hc : ∀ e, c' (eE e) = eN (c e))
    (hq : ∀ e, q' (eE e) = eN (q e)) :
    KLgval d L a M p E c q = KLgval d L a' M' p' E' c' q' := by
  unfold KLgval
  rw [← (eN.arrowCongr (Equiv.refl (Zd d L))).sum_comp]
  refine Fintype.sum_congr _ _ fun b => ?_
  congr 1
  · rw [← eL.prod_comp]
    refine Fintype.prod_congr _ _ fun ℓ => ?_
    simp [Equiv.arrowCongr_apply, ha, hM, hp]
  · rw [← eE.prod_comp]
    refine Fintype.prod_congr _ _ fun e => ?_
    simp [Equiv.arrowCongr_apply, hE, hc, hq]

/-- Reordering a fourfold sum: `(a, b, c, d) ↦ (d, c, a, b)`. -/
private theorem sum_perm4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d :=
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **Splitting along an edge.**  A tree made of two parts `N₁`, `N₂` joined by one edge
`c₀ — q₀` of weight `P S Q` is `∑_{u,w} part₂(u) S_{uw} part₁(w)`, where each part gets the
cut edge back as an extra leaf: `(u, Pᵀ)` on `c₀ ∈ N₂` and `(w, Q)` on `q₀ ∈ N₁`. -/
theorem KLgval_split {N₁ N₂ Lf₁ Lf₂ Ed₁ Ed₂ : Type*} [Fintype N₁] [DecidableEq N₁]
    [Fintype N₂]
    [DecidableEq N₂] [Fintype Lf₁] [Fintype Lf₂] [Fintype Ed₁] [Fintype Ed₂]
    (a₁ : Lf₁ → Zd d L) (M₁ : Lf₁ → Matrix (Zd d L) (Zd d L) ℂ) (p₁ : Lf₁ → N₁)
    (E₁ : Ed₁ → Matrix (Zd d L) (Zd d L) ℂ) (c₁ q₁ : Ed₁ → N₁)
    (a₂ : Lf₂ → Zd d L) (M₂ : Lf₂ → Matrix (Zd d L) (Zd d L) ℂ) (p₂ : Lf₂ → N₂)
    (E₂ : Ed₂ → Matrix (Zd d L) (Zd d L) ℂ) (c₂ q₂ : Ed₂ → N₂)
    (P S Q : Matrix (Zd d L) (Zd d L) ℂ) (c₀ : N₂) (q₀ : N₁) :
    KLgval d L (Sum.elim a₁ a₂) (Sum.elim M₁ M₂) (Sum.elim (Sum.inl ∘ p₁) (Sum.inr ∘ p₂))
        (fun o : Option (Ed₁ ⊕ Ed₂) => o.elim (P * S * Q) (Sum.elim E₁ E₂))
        (fun o => o.elim (Sum.inr c₀) (Sum.elim (Sum.inl ∘ c₁) (Sum.inr ∘ c₂)))
        (fun o => o.elim (Sum.inl q₀) (Sum.elim (Sum.inl ∘ q₁) (Sum.inr ∘ q₂)))
      = ∑ u : Zd d L, ∑ w : Zd d L,
          KLgval d L (fun o : Option Lf₂ => o.elim u a₂) (fun o => o.elim P.transpose M₂)
              (fun o => o.elim c₀ p₂) E₂ c₂ q₂
            * S u w *
          KLgval d L (fun o : Option Lf₁ => o.elim w a₁) (fun o => o.elim Q M₁)
              (fun o => o.elim q₀ p₁) E₁ c₁ q₁ := by
  unfold KLgval
  rw [← (Equiv.sumArrowEquivProdArrow N₁ N₂ (Zd d L)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_option, Option.elim, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [sum_perm4]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  ring

end Generic

section Value

variable (d L : ℕ) [NeZero L] {n : ℕ} [NeZero n]

/-- The tree value `KLtreeValW` is the generic value `KLgval` over the nodes `KLnodes F`, the
leaves `Fin n` and the edges `↥F`, with the parents `KLleafPar`, `KLnodePar` (definitional). -/
theorem KLtreeValW_eq_gval (F : Finset (Fin n × Fin n)) (a : Fin n → Zd d L)
    (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) :
    KLtreeValW d L F a M E
      = KLgval d L a M (fun v => (⟨KLleafPar F v, KLleafPar_mem F v⟩ : ↥(KLnodes F))) E
          (fun d => (⟨d.1, KLmem_nodes_of_mem d.2⟩ : ↥(KLnodes F)))
          (fun d => (⟨KLnodePar F d, KLnodePar_mem F d⟩ : ↥(KLnodes F))) :=
  rfl

/-! ### The derivative: one term per edge -/

variable {F : Finset (Fin n × Fin n)} {a : Fin n → Zd d L}
  {M : ℝ → Fin n → Matrix (Zd d L) (Zd d L) ℂ} {E : ℝ → ↥F → Matrix (Zd d L) (Zd d L) ℂ}
  {M' : Fin n → Matrix (Zd d L) (Zd d L) ℂ} {E' : ↥F → Matrix (Zd d L) (Zd d L) ℂ} {t : ℝ}

/-- If `g` agrees with `f` away from `v`, then `∏ g = g v * ∏_{w ≠ v} f w`. -/
theorem KLprod_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) (g : ι → ℂ)
    (v : ι)
    (hg : ∀ w, w ≠ v → g w = f w) :
    ∏ w, g w = g v * ∏ w ∈ Finset.univ.erase v, f w := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  congr 1
  exact Finset.prod_congr rfl fun w hw => hg w (Finset.ne_of_mem_erase hw)

/-- The derivative of the tree value is the sum over its edges of the value with that edge
differentiated. -/
theorem KLhasDerivAt_treeValW (hM : ∀ v i j, HasDerivAt (fun r => M r v i j) (M' v i j) t)
    (hE : ∀ d i j, HasDerivAt (fun r => E r d i j) (E' d i j) t) :
    HasDerivAt (fun r => KLtreeValW d L F a (M r) (E r))
      (∑ v : Fin n, KLtreeValW d L F a (Function.update (M t) v (M' v)) (E t)
        + ∑ e : ↥F, KLtreeValW d L F a (M t) (Function.update (E t) e (E' e))) t := by
  classical
  simp only [KLtreeValW]
  refine (HasDerivAt.fun_sum fun b _ =>
    (HasDerivAt.fun_finsetProd fun v _ => hM v _ _).mul
      (HasDerivAt.fun_finsetProd fun d _ => hE d _ _)).congr_deriv ?_
  conv_rhs => arg 1; rw [Finset.sum_comm]
  conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [KLprod_update_eq (fun w => M t w (a w) (b ⟨KLleafPar F w, KLleafPar_mem F w⟩)) _ v
      (fun w hw => by rw [Function.update_of_ne hw]), Function.update_self, smul_eq_mul]
    ring
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [KLprod_update_eq (fun e => E t e (b ⟨e.1, KLmem_nodes_of_mem e.2⟩)
      (b ⟨KLnodePar F e, KLnodePar_mem F e⟩)) _ d (fun e he => by rw [Function.update_of_ne he]),
      Function.update_self, smul_eq_mul]
    ring

end Value

section Cut

variable (d L : ℕ) [NeZero L] {n : ℕ} [NeZero n]

/-- The nodes of `F` whose arc is contained in the arc of the cut `J` (the inside nodes,
including `J`). -/
abbrev KLNIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :=
    {x : ↥(KLnodes F) // KLArcLe x.1 J}
/-- The nodes of `F` whose arc is not contained in the arc of `J` (the outside nodes). -/
abbrev KLNOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :=
    {x : ↥(KLnodes F) // ¬KLArcLe x.1 J}
/-- The leaves (vertices) in the arc of `J`: `i ≤ v < j`. -/
abbrev KLLIn (J : Fin n × Fin n) := {v : Fin n // KLInArc J v}
/-- The leaves (vertices) outside the arc of `J`. -/
abbrev KLLOut (J : Fin n × Fin n) := {v : Fin n // ¬KLInArc J v}
/-- The internal edges of `F` strictly inside `J`: arc contained in the arc of `J`, different
from `J`. -/
abbrev KLEIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :=
    {d : ↥F // KLArcLe d.1 J ∧ d.1 ≠ J}
/-- The internal edges of `F` whose arc is not contained in the arc of `J` (the outside
edges). -/
abbrev KLEOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) := {d : ↥F // ¬KLArcLe d.1 J}

variable {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) {J : Fin n × Fin n}
  (hJ : J ∈ F)

/-- The parent of an inside leaf, as an inside node. -/
noncomputable def KLinLeafPar (v : KLLIn J) : KLNIn F J :=
  ⟨⟨KLleafPar F v, KLleafPar_mem F v⟩, KLleafPar_arcLe_of_inArc hF hJ v.2⟩

/-- The parent of an outside leaf, as an outside node. -/
noncomputable def KLoutLeafPar (v : KLLOut J) : KLNOut F J :=
  ⟨⟨KLleafPar F v, KLleafPar_mem F v⟩, KLnot_arcLe_leafPar hF hJ v.2⟩

/-- The child and parent ends of an inside edge. -/
def KLinChild (d : KLEIn F J) : KLNIn F J := ⟨⟨d.1.1, KLmem_nodes_of_mem d.1.2⟩, d.2.1⟩

/-- The parent end of an inside edge: `KLnodePar F d`, an inside node. -/
noncomputable def KLinPar (d : KLEIn F J) : KLNIn F J :=
  ⟨⟨KLnodePar F d.1.1, KLnodePar_mem F _⟩, KLnodePar_arcLe hF hn hJ d.1.2 d.2.1 d.2.2⟩

/-- The child and parent ends of an outside edge. -/
def KLoutChild (d : KLEOut F J) : KLNOut F J := ⟨⟨d.1.1, KLmem_nodes_of_mem d.1.2⟩, d.2⟩

/-- The parent end of an outside edge: `KLnodePar F d`, an outside node. -/
noncomputable def KLoutPar (d : KLEOut F J) : KLNOut F J :=
  ⟨⟨KLnodePar F d.1.1, KLnodePar_mem F _⟩, KLnot_arcLe_nodePar hF hn d.1.2 d.2⟩

/-- The two ends of the cut edge `J`. -/
def KLcutIn : KLNIn F J := ⟨⟨J, KLmem_nodes_of_mem hJ⟩, ⟨le_refl _, le_refl _⟩⟩

/-- The outside end of the cut edge `J`: the parent `KLnodePar F J` of `J`. -/
noncomputable def KLcutOut : KLNOut F J :=
  ⟨⟨KLnodePar F J, KLnodePar_mem F J⟩, KLnot_arcLe_nodePar_self hF hn hJ⟩

/-- The edges of `F`: the cut `J`, the outside edges and the inside edges. -/
private def edgeEquiv : ↥F ≃ Option (KLEOut F J ⊕ KLEIn F J) where
  toFun d := if h1 : d.1 = J then none else
    if h2 : KLArcLe d.1 J then some (Sum.inr ⟨d, h2, h1⟩) else some (Sum.inl ⟨d, h2⟩)
  invFun o := o.elim ⟨J, hJ⟩ (Sum.elim (fun x => x.1) (fun x => x.1))
  left_inv d := by
    by_cases h1 : d.1 = J
    · simp only [h1, dite_true, Option.elim]; exact Subtype.ext h1.symm
    · by_cases h2 : KLArcLe d.1 J <;> simp [h1, h2]
  right_inv o := by
    rcases o with _ | x | x
    · simp
    · have h2 := x.2
      have h1 : x.1.1 ≠ J := fun h => h2 (by rw [h]; exact ⟨le_refl _, le_refl _⟩)
      simp [h1, h2]
    · have h1 := x.2.2
      have h2 := x.2.1
      simp [h1, h2]

/-- **Cutting a tree at the internal edge `J`.**  If the edge `J` carries `P S Q`, the tree
value is `∑_{u,w} (inside tree + root leaf (u, Pᵀ)) S_{uw} (outside tree + leaf (w, Q))`. -/
theorem KLtreeValW_cut (a : Fin n → Zd d L) (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (P S Q : Matrix (Zd d L) (Zd d L) ℂ) :
    KLtreeValW d L F a M (Function.update E ⟨J, hJ⟩ (P * S * Q))
      = ∑ u : Zd d L, ∑ w : Zd d L,
          KLgval d L (fun o : Option (KLLIn J) => o.elim u (fun v => a v.1))
              (fun o => o.elim P.transpose (fun v => M v.1))
              (fun o => o.elim (KLcutIn hJ) (KLinLeafPar hF hJ)) (fun d : KLEIn F J => E d.1)
              KLinChild (KLinPar hF hn hJ)
            * S u w *
          KLgval d L (fun o : Option (KLLOut J) => o.elim w (fun v => a v.1))
              (fun o => o.elim Q (fun v => M v.1))
              (fun o => o.elim (KLcutOut hF hn hJ) (KLoutLeafPar hF hJ)) (fun d : KLEOut F J => E d.1)
              KLoutChild (KLoutPar hF hn) := by
  rw [KLtreeValW_eq_gval, ← KLgval_split]
  refine KLgval_congr
    ((Equiv.sumCompl (fun x : ↥(KLnodes F) => KLArcLe x.1 J)).symm.trans (Equiv.sumComm _ _))
    ((Equiv.sumCompl (fun v : Fin n => KLInArc J v)).symm.trans (Equiv.sumComm _ _))
    (edgeEquiv hJ) ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    by_cases h : KLInArc J v
    · simp [Equiv.sumCompl_symm_apply_of_pos h]
    · simp [Equiv.sumCompl_symm_apply_of_neg h]
  · intro v
    by_cases h : KLInArc J v
    · simp [Equiv.sumCompl_symm_apply_of_pos h]
    · simp [Equiv.sumCompl_symm_apply_of_neg h]
  · intro v
    by_cases h : KLInArc J v
    · have h' : KLArcLe (KLleafPar F v) J := KLleafPar_arcLe_of_inArc hF hJ h
      simp [Equiv.sumCompl_symm_apply_of_pos h, Equiv.sumCompl_symm_apply_of_pos
        (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨KLleafPar F v, KLleafPar_mem F v⟩) h',
        KLinLeafPar]
    · have h' : ¬KLArcLe (KLleafPar F v) J := KLnot_arcLe_leafPar hF hJ h
      simp [Equiv.sumCompl_symm_apply_of_neg h, Equiv.sumCompl_symm_apply_of_neg
        (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨KLleafPar F v, KLleafPar_mem F v⟩) h',
        KLoutLeafPar]
  · intro d
    by_cases h1 : d.1 = J
    · have hd : d = ⟨J, hJ⟩ := Subtype.ext h1
      subst hd
      simp [edgeEquiv]
    · have hne : d ≠ ⟨J, hJ⟩ := fun h => h1 (congrArg Subtype.val h)
      by_cases h2 : KLArcLe d.1 J <;> simp [edgeEquiv, h1, h2, Function.update_of_ne hne]
  · intro d
    by_cases h1 : d.1 = J
    · have hd : d = ⟨J, hJ⟩ := Subtype.ext h1
      subst hd
      simp [edgeEquiv, Equiv.sumCompl_symm_apply_of_pos
        (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨J, KLmem_nodes_of_mem hJ⟩)
        (⟨le_refl _, le_refl _⟩ : KLArcLe J J), KLcutIn]
    · by_cases h2 : KLArcLe d.1 J
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_pos
          (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨d.1, KLmem_nodes_of_mem d.2⟩) h2,
          KLinChild]
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_neg
          (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨d.1, KLmem_nodes_of_mem d.2⟩) h2,
          KLoutChild]
  · intro d
    by_cases h1 : d.1 = J
    · have hd : d = ⟨J, hJ⟩ := Subtype.ext h1
      subst hd
      simp [edgeEquiv, Equiv.sumCompl_symm_apply_of_neg
        (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨KLnodePar F J, KLnodePar_mem F J⟩)
        (KLnot_arcLe_nodePar_self hF hn hJ), KLcutOut]
    · by_cases h2 : KLArcLe d.1 J
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_pos
          (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨KLnodePar F d.1, KLnodePar_mem F _⟩)
          (KLnodePar_arcLe hF hn hJ d.2 h2 h1), KLinPar]
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_neg
          (p := fun x : ↥(KLnodes F) => KLArcLe x.1 J) (a := ⟨KLnodePar F d.1, KLnodePar_mem F _⟩)
          (KLnot_arcLe_nodePar hF hn d.2 h2), KLoutPar]

end Cut

section CutIn

variable {n : ℕ} [NeZero n]

/-- The width `j - i` of the cut `J = (i, j)`: the inside polygon has `KLwIn J + 1` vertices. -/
def KLwIn (J : Fin n × Fin n) : ℕ := J.2.val - J.1.val

/-- Shift a region pair inside `J` to the inside polygon: `(x₁, x₂) ↦ (x₁ - i, x₂ - i)`. -/
def KLshiftIn (J : Fin n × Fin n) (d : Fin n × Fin n) : Fin (KLwIn J + 1) × Fin (KLwIn J + 1) :=
  (⟨min (d.1.val - J.1.val) (KLwIn J), by omega⟩, ⟨min (d.2.val - J.1.val) (KLwIn J), by omega⟩)

/-- The family of the inside polygon: the edges strictly inside `J`, shifted. -/
def KLFIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :
    Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) :=
  (F.filter fun d => KLArcLe d J ∧ d ≠ J).image (KLshiftIn J)

/-- The inside vertex `v ∈ J` in the inside polygon: `v - i`. -/
def KLinV (J : Fin n × Fin n) (v : Fin n) : Fin (KLwIn J + 1) :=
  ⟨min (v.val - J.1.val) (KLwIn J), by omega⟩

variable {J : Fin n × Fin n}

omit [NeZero n] in
/-- Inside `J` the shift is exact (no truncation): `(KLshiftIn J d).k = d.k - i`. -/
theorem KLshiftIn_val {d : Fin n × Fin n} (h : KLArcLe d J) (h12 : d.1 ≤ d.2) :
    (KLshiftIn J d).1.val = d.1.val - J.1.val ∧ (KLshiftIn J d).2.val = d.2.val - J.1.val := by
  simp only [KLArcLe, Fin.le_def] at h h12
  simp only [KLshiftIn, KLwIn]
  constructor <;> omega

omit [NeZero n] in
/-- For a vertex `v` in the arc of `J`: `KLinV J v = v - i`. -/
theorem KLinV_val {v : Fin n} (h : KLInArc J v) : (KLinV J v).val = v.val - J.1.val := by
  simp only [KLInArc, Fin.le_def, Fin.lt_def] at h
  simp only [KLinV, KLwIn]
  omega

omit [NeZero n] in
private theorem shiftIn_self : KLshiftIn J J = KLwholeP (KLwIn J + 1) := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [KLshiftIn, KLwholeP, KLwIn]

omit [NeZero n] in
/-- `KLshiftIn J` is injective on the pairs `d` inside `J` with `d.1 ≤ d.2`. -/
theorem KLshiftIn_injOn {d e : Fin n × Fin n} (hd : KLArcLe d J) (hd12 : d.1 ≤ d.2)
    (he : KLArcLe e J) (he12 : e.1 ≤ e.2) (h : KLshiftIn J d = KLshiftIn J e) : d = e := by
  have h1 := KLshiftIn_val hd hd12
  have h2 := KLshiftIn_val he he12
  have h3 := congrArg (fun x => x.1.val) h
  have h4 := congrArg (fun x => x.2.val) h
  simp only [KLArcLe, Fin.le_def] at hd he hd12 he12
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero n] in
private theorem arcLe_shiftIn_iff {d e : Fin n × Fin n} (hd : KLArcLe d J) (hd12 : d.1 ≤ d.2)
    (he : KLArcLe e J) (he12 : e.1 ≤ e.2) :
    KLArcLe (KLshiftIn J d) (KLshiftIn J e) ↔ KLArcLe d e := by
  have h1 := KLshiftIn_val hd hd12
  have h2 := KLshiftIn_val he he12
  simp only [KLArcLe, Fin.le_def] at hd he hd12 he12 ⊢
  omega

omit [NeZero n] in
private theorem inArc_shiftIn_iff {d : Fin n × Fin n} (hd : KLArcLe d J) (hd12 : d.1 ≤ d.2)
    {v : Fin n}
    (hv : KLInArc J v) : KLInArc (KLshiftIn J d) (KLinV J v) ↔ KLInArc d v := by
  have h1 := KLshiftIn_val hd hd12
  have h2 := KLinV_val hv
  simp only [KLArcLe, KLInArc, Fin.le_def, Fin.lt_def] at hd hv hd12 ⊢
  omega

variable {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hJ

private theorem shiftIn_mem_nodes {x : Fin n × Fin n} (hx : x ∈ KLnodes F) (hxJ : KLArcLe x J) :
    KLshiftIn J x ∈ KLnodes (KLFIn F J) := by
  by_cases h : x = J
  · subst h
    rw [shiftIn_self]
    exact KLwholeP_mem_nodes _
  · have hxF : x ∈ F := by
      rcases mem_insert.1 hx with rfl | hx
      · exact absurd hxJ (KLnot_arcLe_wholeP hF hJ)
      · exact hx
    exact KLmem_nodes_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨hxF, hxJ, h⟩))

omit hF in
private theorem exists_of_mem_nodes_FIn {y : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)}
    (hy : y ∈ KLnodes (KLFIn F J)) : ∃ x ∈ KLnodes F, KLArcLe x J ∧ KLshiftIn J x = y := by
  rcases mem_insert.1 hy with rfl | hy
  · exact ⟨J, KLmem_nodes_of_mem hJ, ⟨le_refl _, le_refl _⟩, shiftIn_self⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    have hx' := mem_filter.1 hx
    exact ⟨x, KLmem_nodes_of_mem hx'.1, hx'.2.1, rfl⟩

include hn

/-- **The inside part of a cut is a tree value on the inside polygon** `Fin (KLwIn J + 1)`:
`J` becomes the root node, the inside leaves are shifted by `-i`, and the cut leaf becomes the
root vertex `KLwIn J`. -/
theorem KLgval_in_eq (d L : ℕ) [NeZero L] (a : Fin n → Zd d L)
    (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (u : Zd d L) (R : Matrix (Zd d L) (Zd d L) ℂ)
    (a' : Fin (KLwIn J + 1) → Zd d L) (M' : Fin (KLwIn J + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (E' : ↥(KLFIn F J) → Matrix (Zd d L) (Zd d L) ℂ)
    (ha0 : a' (Fin.last _) = u) (ha1 : ∀ v : KLLIn J, a' (KLinV J v) = a v)
    (hM0 : M' (Fin.last _) = R) (hM1 : ∀ v : KLLIn J, M' (KLinV J v) = M v)
    (hE : ∀ d : KLEIn F J,
      E' ⟨KLshiftIn J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩ = E d.1) :
    KLgval d L (fun o : Option (KLLIn J) => o.elim u (fun v => a v.1))
        (fun o => o.elim R (fun v => M v.1))
        (fun o => o.elim (KLcutIn hJ) (KLinLeafPar hF hJ)) (fun d : KLEIn F J => E d.1)
        KLinChild (KLinPar hF hn hJ)
      = KLtreeValW d L (KLFIn F J) a' M' E' := by
  have h12 : ∀ x ∈ KLnodes F, x.1 ≤ x.2 := fun x hx => le_of_lt (KLlt_of_mem_nodes hF hn hx)
  -- the three bijections
  let fN : KLNIn F J → ↥(KLnodes (KLFIn F J)) := fun x =>
    ⟨KLshiftIn J x.1.1, shiftIn_mem_nodes hF hJ x.1.2 x.2⟩
  have hfN : Function.Bijective fN := by
    constructor
    · intro x y h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (KLshiftIn_injOn x.2 (h12 _ x.1.2) y.2 (h12 _ y.1.2) this))
    · intro y
      obtain ⟨x, hx, hxJ, hxy⟩ := exists_of_mem_nodes_FIn hJ y.2
      exact ⟨⟨⟨x, hx⟩, hxJ⟩, Subtype.ext hxy⟩
  let fL : Option (KLLIn J) → Fin (KLwIn J + 1) := fun o => o.elim (Fin.last _) (fun v => KLinV J v.1)
  have hlt : ∀ v : KLLIn J, (KLinV J v.1).val < KLwIn J := by
    intro v
    have h1 := KLinV_val v.2
    have h2 := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def] at h2
    simp only [KLwIn]; omega
  have hfL : Function.Bijective fL := by
    constructor
    · rintro (_ | v) (_ | v') h
      · rfl
      · have := hlt v'; simp only [fL, Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · have := hlt v; simp only [fL, Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · simp only [fL, Option.elim, Fin.ext_iff] at h
        have h1 := KLinV_val v.2
        have h2 := KLinV_val v'.2
        have h3 := v.2
        have h4 := v'.2
        simp only [KLInArc, Fin.le_def] at h3 h4
        exact congrArg some (Subtype.ext (Fin.ext (by omega)))
    · intro i
      by_cases hi : i.val = KLwIn J
      · exact ⟨none, Fin.ext (by simp [fL, hi])⟩
      · have hi' : i.val < KLwIn J := by have := i.isLt; omega
        have hv : i.val + J.1.val < n := by
          have := J.2.isLt; simp only [KLwIn] at hi'; omega
        have hin : KLInArc J ⟨i.val + J.1.val, hv⟩ := by
          simp only [KLInArc, Fin.le_def, Fin.lt_def]; simp only [KLwIn] at hi'; omega
        refine ⟨some ⟨⟨i.val + J.1.val, hv⟩, hin⟩, Fin.ext ?_⟩
        simp only [fL, Option.elim]
        rw [KLinV_val hin]; simp
  let fE : KLEIn F J → ↥(KLFIn F J) := fun d =>
    ⟨KLshiftIn J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩
  have hfE : Function.Bijective fE := by
    constructor
    · intro d e h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (KLshiftIn_injOn d.2.1 (h12 _ (KLmem_nodes_of_mem d.1.2))
        e.2.1 (h12 _ (KLmem_nodes_of_mem e.1.2)) this))
    · intro y
      obtain ⟨x, hx, hxy⟩ := mem_image.1 y.2
      have hx' := mem_filter.1 hx
      exact ⟨⟨⟨x, hx'.1⟩, hx'.2⟩, Subtype.ext hxy⟩
  rw [KLtreeValW_eq_gval]
  refine KLgval_congr (Equiv.ofBijective fN hfN) (Equiv.ofBijective fL hfL)
    (Equiv.ofBijective fE hfE) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro (_ | v)
    · simpa [fL] using ha0
    · simpa [fL] using ha1 v
  · rintro (_ | v)
    · simpa [fL] using hM0
    · simpa [fL] using hM1 v
  · rintro (_ | v)
    · refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, KLcutIn]
      rw [KLleafPar_root _ (by simp), shiftIn_self]
    · refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, KLinLeafPar]
      have hr := KLlt_of_inArc v.2
      have hspec := KLleafPar_spec hF hr
      have hin := KLleafPar_arcLe_of_inArc hF hJ v.2
      have hmem := KLleafPar_mem F v.1
      refine KLleafPar_eq (shiftIn_mem_nodes hF hJ hmem hin)
        ((inArc_shiftIn_iff hin (h12 _ hmem) v.2).2 hspec.1) ?_
      intro e' he' hev'
      obtain ⟨x, hx, hxJ, rfl⟩ := exists_of_mem_nodes_FIn hJ he'
      have hxv := (inArc_shiftIn_iff hxJ (h12 _ hx) v.2).1 hev'
      exact (arcLe_shiftIn_iff hin (h12 _ hmem) hxJ (h12 _ hx)).2 (hspec.2 x hx hxv)
  · intro d
    simpa [fE] using hE d
  · intro d
    rfl
  · intro d
    refine Subtype.ext ?_
    simp only [Equiv.ofBijective_apply, fE, fN, KLinPar]
    have hd := KLmem_nodes_of_mem d.1.2
    have hspec := KLnodePar_spec hF hn hd (KLne_wholeP hF d.1.2)
    have hin := KLnodePar_arcLe hF hn hJ d.1.2 d.2.1 d.2.2
    have hpm := KLnodePar_mem F d.1.1
    have hdd := KLshiftIn_val d.2.1 (h12 _ hd)
    have hlt' := KLlt_of_mem_nodes hF hn hd
    refine KLnodePar_eq ?_ (shiftIn_mem_nodes hF hJ hpm hin)
      ((arcLe_shiftIn_iff d.2.1 (h12 _ hd) hin (h12 _ hpm)).2 hspec.2.1) ?_ ?_
    · rw [Fin.le_def, hdd.1, hdd.2]; rw [Fin.lt_def] at hlt'; omega
    · intro h
      exact hspec.2.2.1 (KLshiftIn_injOn hin (h12 _ hpm) d.2.1 (h12 _ hd) h)
    · intro e' he' hde' hne'
      obtain ⟨x, hx, hxJ, rfl⟩ := exists_of_mem_nodes_FIn hJ he'
      have hdx := (arcLe_shiftIn_iff d.2.1 (h12 _ hd) hxJ (h12 _ hx)).1 hde'
      have hxd : x ≠ d.1.1 := fun h => hne' (by rw [h])
      exact (arcLe_shiftIn_iff hin (h12 _ hpm) hxJ (h12 _ hx)).2 (hspec.2.2.2 x hx hdx hxd)

end CutIn

section CutOut

variable {n : ℕ} [NeZero n]

/-- Collapse the arc of `J = (i, j)` to the single point `i`: `r ↦ r` for `r ≤ i`,
`r ↦ r - (j - i - 1)` beyond. -/
def KLcol (J : Fin n × Fin n) (r : ℕ) : ℕ := if r ≤ J.1.val then r else r - (KLwIn J - 1)

/-- The outside polygon has `n - KLwIn J + 1` vertices. -/
def KLshiftOut (J : Fin n × Fin n) (d : Fin n × Fin n) :
    Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1) :=
  (⟨min (KLcol J d.1.val) (n - KLwIn J), by omega⟩, ⟨min (KLcol J d.2.val) (n - KLwIn J), by omega⟩)

/-- The family of the outside polygon: the edges not inside `J`, collapsed. -/
def KLFOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :
    Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) :=
  (F.filter fun d => ¬KLArcLe d J).image (KLshiftOut J)

/-- An outside vertex in the outside polygon. -/
def KLoutV (J : Fin n × Fin n) (v : Fin n) : Fin (n - KLwIn J + 1) :=
  ⟨min (KLcol J v.val) (n - KLwIn J), by omega⟩

/-- The glue vertex of the outside polygon: `J` collapsed to the point `i`. -/
def KLglueV (J : Fin n × Fin n) : Fin (n - KLwIn J + 1) := ⟨min J.1.val (n - KLwIn J), by omega⟩

variable {J : Fin n × Fin n}

/-- The endpoint condition of an outside node: no endpoint strictly inside `J`. -/
def KLOutEnds (J : Fin n × Fin n) (x : Fin n × Fin n) : Prop :=
  (x.1.val ≤ J.1.val ∨ J.2.val ≤ x.1.val) ∧ (x.2.val ≤ J.1.val ∨ J.2.val ≤ x.2.val) ∧
    x.1.val < x.2.val

omit [NeZero n] in
/-- `KLcol J r = r` for `r ≤ i`. -/
theorem KLcol_of_le {r : ℕ} (h : r ≤ J.1.val) : KLcol J r = r := by simp [KLcol, h]

omit [NeZero n] in
/-- `KLcol J r = r - (j - i - 1)` for `r > i`. -/
theorem KLcol_of_gt {r : ℕ} (h : J.1.val < r) : KLcol J r = r - (KLwIn J - 1) := by
  simp [KLcol, not_le.2 h]

omit [NeZero n] in
private theorem col_val {r : ℕ} (hr' : r < n) (hJ2 : J.1.val < J.2.val) :
    min (KLcol J r) (n - KLwIn J) = KLcol J r := by
  have := J.2.isLt
  simp only [KLcol, KLwIn] at *
  split_ifs <;> omega

omit [NeZero n] in
/-- For `i < j` no truncation occurs: `(KLshiftOut J x).k = KLcol J x.k`. -/
theorem KLshiftOut_val (x : Fin n × Fin n) (hJ2 : J.1.val < J.2.val) :
    (KLshiftOut J x).1.val = KLcol J x.1.val ∧ (KLshiftOut J x).2.val = KLcol J x.2.val :=
  ⟨col_val x.1.isLt hJ2, col_val x.2.isLt hJ2⟩

omit [NeZero n] in
/-- For `i < j`: `KLoutV J v = KLcol J v`. -/
theorem KLoutV_val (v : Fin n) (hJ2 : J.1.val < J.2.val) :
    (KLoutV J v).val = KLcol J v.val := by
  exact col_val v.isLt hJ2

omit [NeZero n] in
/-- `KLcol` is strictly monotone on points outside the open arc of `J`. -/
private theorem col_le_iff {r s : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r)
    (hs : s ≤ J.1.val ∨ J.2.val ≤ s)
    (hJ : J.1.val + 2 ≤ J.2.val) : KLcol J r ≤ KLcol J s ↔ r ≤ s := by
  simp only [KLcol, KLwIn]
  split_ifs <;> omega

omit [NeZero n] in
private theorem col_lt_of_vertex {r v : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r)
    (hv : v < J.1.val ∨ J.2.val ≤ v) (hJ : J.1.val + 2 ≤ J.2.val) :
    (KLcol J v < KLcol J r ↔ v < r) ∧ (KLcol J r ≤ KLcol J v ↔ r ≤ v) := by
  simp only [KLcol, KLwIn]
  constructor <;> split_ifs <;> omega

omit [NeZero n] in
/-- For a diagonal arc `i + 2 ≤ j`, `KLshiftOut J` is injective on the pairs with `KLOutEnds J`. -/
theorem KLshiftOut_injOn {d e : Fin n × Fin n} (hd : KLOutEnds J d) (he : KLOutEnds J e)
    (hJ : J.1.val + 2 ≤ J.2.val) (h : KLshiftOut J d = KLshiftOut J e) : d = e := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have h2 := KLshiftOut_val e hJ2
  have h3 := congrArg (fun x => x.1.val) h
  have h4 := congrArg (fun x => x.2.val) h
  have a1 := (col_le_iff hd.1 he.1 hJ).1 (by omega)
  have a2 := (col_le_iff he.1 hd.1 hJ).1 (by omega)
  have a3 := (col_le_iff hd.2.1 he.2.1 hJ).1 (by omega)
  have a4 := (col_le_iff he.2.1 hd.2.1 hJ).1 (by omega)
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero n] in
private theorem arcLe_shiftOut_iff {d e : Fin n × Fin n} (hd : KLOutEnds J d) (he : KLOutEnds J e)
    (hJ : J.1.val + 2 ≤ J.2.val) : KLArcLe (KLshiftOut J d) (KLshiftOut J e) ↔ KLArcLe d e := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have h2 := KLshiftOut_val e hJ2
  simp only [KLArcLe, Fin.le_def, h1, h2, col_le_iff he.1 hd.1 hJ, col_le_iff hd.2.1 he.2.1 hJ]

omit [NeZero n] in
private theorem inArc_shiftOut_iff {d : Fin n × Fin n} (hd : KLOutEnds J d) {v : Fin n}
    (hv : ¬KLInArc J v) (hJ : J.1.val + 2 ≤ J.2.val) :
    KLInArc (KLshiftOut J d) (KLoutV J v) ↔ KLInArc d v := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have h2 := KLoutV_val v hJ2
  have hv' : v.val < J.1.val ∨ J.2.val ≤ v.val := by
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega
  simp only [KLInArc, Fin.le_def, Fin.lt_def, h1, h2, (col_lt_of_vertex hd.1 hv' hJ).2,
    (col_lt_of_vertex hd.2.1 hv' hJ).1]

omit [NeZero n] in
/-- An outside node contains the glue vertex iff it contains `J`. -/
private theorem inArc_glue_iff {d : Fin n × Fin n} (hd : KLOutEnds J d) (hJ : J.1.val + 2 ≤ J.2.val) :
    KLInArc (KLshiftOut J d) (KLglueV J) ↔ KLArcLe J d := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have hg : (KLglueV J).val = J.1.val := by
    have := J.2.isLt; simp only [KLglueV, KLwIn]; omega
  obtain ⟨e1, e2, e3⟩ := hd
  simp only [KLInArc, KLArcLe, Fin.le_def, Fin.lt_def, h1, hg]
  simp only [KLcol, KLwIn]
  split_ifs <;> omega

variable {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hJ

omit [NeZero n] in
/-- The cut `J = (i, j)` is a diagonal, so `i + 2 ≤ j`. -/
theorem KLdiag_width : J.1.val + 2 ≤ J.2.val := by
  obtain ⟨h1, h2, -⟩ := hF.1 J hJ
  rw [Fin.lt_def] at h1
  omega

include hn in
/-- By laminarity, an outside node of a tree `F ∋ J` has no endpoint strictly inside `J`. -/
theorem KLoutEnds_of {x : Fin n × Fin n} (hx : x ∈ KLnodes F)
    (hxJ : ¬KLArcLe x J) : KLOutEnds J x := by
  have hlt := KLlt_of_mem_nodes hF hn hx
  have hJw := KLdiag_width hF hJ
  rcases KLnodes_laminar hF hx (KLmem_nodes_of_mem hJ) with h | h | h | h
  · exact absurd h hxJ
  all_goals simp only [KLArcLe, Fin.le_def, Fin.lt_def] at h hlt ⊢
  all_goals exact ⟨by omega, by omega, hlt⟩

private theorem shiftOut_whole : KLshiftOut J (KLwholeP n) = KLwholeP (n - KLwIn J + 1) := by
  have hJw := KLdiag_width hF hJ
  have := J.2.isLt
  have hc : KLcol J (n - 1) = n - KLwIn J := by
    rw [KLcol_of_gt (by omega)]; simp only [KLwIn]; omega
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · simp [KLshiftOut, KLwholeP, KLcol]
  · simp only [KLshiftOut, KLwholeP, hc]; simp

private theorem shiftOut_mem_nodes {x : Fin n × Fin n} (hx : x ∈ KLnodes F) (hxJ : ¬KLArcLe x J) :
    KLshiftOut J x ∈ KLnodes (KLFOut F J) := by
  rcases mem_insert.1 hx with rfl | hx
  · rw [shiftOut_whole hF hJ]; exact KLwholeP_mem_nodes _
  · exact KLmem_nodes_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨hx, hxJ⟩))

private theorem exists_of_mem_nodes_FOut {y : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)}
    (hy : y ∈ KLnodes (KLFOut F J)) : ∃ x ∈ KLnodes F, ¬KLArcLe x J ∧ KLshiftOut J x = y := by
  rcases mem_insert.1 hy with rfl | hy
  · exact ⟨KLwholeP n, KLwholeP_mem_nodes F, KLnot_arcLe_wholeP hF hJ, shiftOut_whole hF hJ⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    have hx' := mem_filter.1 hx
    exact ⟨x, KLmem_nodes_of_mem hx'.1, hx'.2, rfl⟩

include hn

/-- **The outside part of a cut is a tree value on the outside polygon**
`Fin (n - KLwIn J + 1)`: `J` collapses to the glue vertex, which hangs on the parent of `J`. -/
theorem KLgval_out_eq (d L : ℕ) [NeZero L] (a : Fin n → Zd d L)
    (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L)
    (Q : Matrix (Zd d L) (Zd d L) ℂ) (a' : Fin (n - KLwIn J + 1) → Zd d L)
    (M' : Fin (n - KLwIn J + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (E' : ↥(KLFOut F J) → Matrix (Zd d L) (Zd d L) ℂ)
    (ha0 : a' (KLglueV J) = x) (ha1 : ∀ v : KLLOut J, a' (KLoutV J v) = a v)
    (hM0 : M' (KLglueV J) = Q) (hM1 : ∀ v : KLLOut J, M' (KLoutV J v) = M v)
    (hE : ∀ d : KLEOut F J, E' ⟨KLshiftOut J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩
      = E d.1) :
    KLgval d L (fun o : Option (KLLOut J) => o.elim x (fun v => a v.1))
        (fun o => o.elim Q (fun v => M v.1))
        (fun o => o.elim (KLcutOut hF hn hJ) (KLoutLeafPar hF hJ)) (fun d : KLEOut F J => E d.1)
        KLoutChild (KLoutPar hF hn)
      = KLtreeValW d L (KLFOut F J) a' M' E' := by
  have hJw := KLdiag_width hF hJ
  have hJ2 : J.1.val < J.2.val := by omega
  have hends : ∀ y ∈ KLnodes F, ¬KLArcLe y J → KLOutEnds J y := fun y hy hyJ => KLoutEnds_of hF hn hJ hy hyJ
  have hg : (KLglueV J).val = J.1.val := by
    have := J.2.isLt; simp only [KLglueV, KLwIn]; omega
  have hvside : ∀ v : KLLOut J, v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
    intro v; have := v.2; simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
  -- nodes
  let fN : KLNOut F J → ↥(KLnodes (KLFOut F J)) := fun y =>
    ⟨KLshiftOut J y.1.1, shiftOut_mem_nodes hF hJ y.1.2 y.2⟩
  have hfN : Function.Bijective fN := by
    constructor
    · intro y z h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (KLshiftOut_injOn (hends _ y.1.2 y.2)
        (hends _ z.1.2 z.2) hJw this))
    · intro y
      obtain ⟨z, hz, hzJ, hzy⟩ := exists_of_mem_nodes_FOut hF hJ y.2
      exact ⟨⟨⟨z, hz⟩, hzJ⟩, Subtype.ext hzy⟩
  -- leaves
  let fL : Option (KLLOut J) → Fin (n - KLwIn J + 1) := fun o => o.elim (KLglueV J) (fun v => KLoutV J v.1)
  have hfL : Function.Bijective fL := by
    constructor
    · have hcol : ∀ v : KLLOut J, (KLcol J v.1.val < J.1.val ∧ KLcol J v.1.val = v.1.val) ∨
          (J.1.val < KLcol J v.1.val ∧ KLcol J v.1.val = v.1.val - (KLwIn J - 1)) := by
        intro v
        rcases hvside v with h | h
        · exact Or.inl (by rw [KLcol_of_le (le_of_lt h)]; exact ⟨h, rfl⟩)
        · refine Or.inr ?_
          rw [KLcol_of_gt (lt_of_lt_of_le hJ2 h)]
          refine ⟨?_, rfl⟩
          simp only [KLwIn]; omega
      rintro (_ | v) (_ | v') h
      · rfl
      · have h1 := KLoutV_val v'.1 hJ2
        simp only [fL, Option.elim, Fin.ext_iff, hg, h1] at h
        rcases hcol v' with h2 | h2 <;> omega
      · have h1 := KLoutV_val v.1 hJ2
        simp only [fL, Option.elim, Fin.ext_iff, hg, h1] at h
        rcases hcol v with h2 | h2 <;> omega
      · have h1 := KLoutV_val v.1 hJ2; have h2 := KLoutV_val v'.1 hJ2
        simp only [fL, Option.elim, Fin.ext_iff, h1, h2] at h
        refine congrArg some (Subtype.ext (Fin.ext ?_))
        have h3 := hvside v; have h4 := hvside v'
        rcases hcol v with h5 | h5 <;> rcases hcol v' with h6 | h6 <;> simp only [KLwIn] at * <;>
          omega
    · intro i
      have hi := i.isLt
      have := J.2.isLt
      by_cases h1 : i.val = J.1.val
      · exact ⟨none, Fin.ext (by simp [fL, hg, h1])⟩
      by_cases h2 : i.val < J.1.val
      · have hv : ¬KLInArc J ⟨i.val, by omega⟩ := by
          simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt]; omega
        refine ⟨some ⟨⟨i.val, by omega⟩, hv⟩, Fin.ext ?_⟩
        simp only [fL, Option.elim, KLoutV_val _ hJ2]
        rw [KLcol_of_le (by omega)]
      · have hin : i.val + (KLwIn J - 1) < n := by simp only [KLwIn] at hi ⊢; omega
        have hv : ¬KLInArc J ⟨i.val + (KLwIn J - 1), hin⟩ := by
          simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt, KLwIn]; omega
        refine ⟨some ⟨⟨i.val + (KLwIn J - 1), hin⟩, hv⟩, Fin.ext ?_⟩
        simp only [fL, Option.elim, KLoutV_val _ hJ2]
        rw [KLcol_of_gt (by simp only [KLwIn]; omega)]
        simp only [KLwIn]; omega
  -- edges
  let fE : KLEOut F J → ↥(KLFOut F J) := fun d =>
    ⟨KLshiftOut J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩
  have hfE : Function.Bijective fE := by
    constructor
    · intro d e h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (KLshiftOut_injOn (hends _ (KLmem_nodes_of_mem d.1.2) d.2)
        (hends _ (KLmem_nodes_of_mem e.1.2) e.2) hJw this))
    · intro y
      obtain ⟨z, hz, hzy⟩ := mem_image.1 y.2
      have hz' := mem_filter.1 hz
      exact ⟨⟨⟨z, hz'.1⟩, hz'.2⟩, Subtype.ext hzy⟩
  rw [KLtreeValW_eq_gval]
  refine KLgval_congr (Equiv.ofBijective fN hfN) (Equiv.ofBijective fL hfL)
    (Equiv.ofBijective fE hfE) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro (_ | v)
    · simpa [fL] using ha0
    · simpa [fL] using ha1 v
  · rintro (_ | v)
    · simpa [fL] using hM0
    · simpa [fL] using hM1 v
  · rintro (_ | v)
    · -- the glue leaf hangs on the parent of `J`
      refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, KLcutOut]
      have hJn := KLmem_nodes_of_mem hJ
      have hspec := KLnodePar_spec hF hn hJn (KLne_wholeP hF hJ)
      have hout := KLnot_arcLe_nodePar_self hF hn hJ
      have hpm := KLnodePar_mem F J
      refine KLleafPar_eq (shiftOut_mem_nodes hF hJ hpm hout)
        ((inArc_glue_iff (hends _ hpm hout) hJw).2 hspec.2.1) ?_
      intro e' he' hge'
      obtain ⟨z, hz, hzJ, rfl⟩ := exists_of_mem_nodes_FOut hF hJ he'
      have hJz := (inArc_glue_iff (hends _ hz hzJ) hJw).1 hge'
      have hzne : z ≠ J := fun h => hzJ (h ▸ ⟨le_refl _, le_refl _⟩)
      exact (arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2
        (hspec.2.2.2 z hz hJz hzne)
    · refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, KLoutLeafPar]
      by_cases hr : v.1.val < n - 1
      · have hspec := KLleafPar_spec hF hr
        have hout := KLnot_arcLe_leafPar hF hJ v.2
        have hpm := KLleafPar_mem F v.1
        refine KLleafPar_eq (shiftOut_mem_nodes hF hJ hpm hout)
          ((inArc_shiftOut_iff (hends _ hpm hout) v.2 hJw).2 hspec.1) ?_
        intro e' he' hve'
        obtain ⟨z, hz, hzJ, rfl⟩ := exists_of_mem_nodes_FOut hF hJ he'
        have hzv := (inArc_shiftOut_iff (hends _ hz hzJ) v.2 hJw).1 hve'
        exact (arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2 z hz hzv)
      · have hroot : v.1.val = n - 1 := by have := v.1.isLt; omega
        rw [KLleafPar_root F hroot, shiftOut_whole hF hJ, KLleafPar_root]
        rw [KLoutV_val _ hJ2, hroot]
        have := J.2.isLt
        rw [KLcol_of_gt (by omega)]
        simp only [KLwIn]; omega
  · intro d
    simpa [fE] using hE d
  · intro d
    rfl
  · intro d
    refine Subtype.ext ?_
    simp only [Equiv.ofBijective_apply, fE, fN, KLoutPar]
    have hd := KLmem_nodes_of_mem d.1.2
    have hspec := KLnodePar_spec hF hn hd (KLne_wholeP hF d.1.2)
    have hout := KLnot_arcLe_nodePar hF hn d.1.2 d.2
    have hpm := KLnodePar_mem F d.1.1
    have hdE := hends _ hd d.2
    have hdd := KLshiftOut_val d.1.1 hJ2
    have hlt' := KLlt_of_mem_nodes hF hn hd
    refine KLnodePar_eq ?_ (shiftOut_mem_nodes hF hJ hpm hout)
      ((arcLe_shiftOut_iff hdE (hends _ hpm hout) hJw).2 hspec.2.1) ?_ ?_
    · rw [Fin.le_def, hdd.1, hdd.2]
      exact (col_le_iff hdE.1 hdE.2.1 hJw).2 (le_of_lt hdE.2.2)
    · intro h
      exact hspec.2.2.1 (KLshiftOut_injOn (hends _ hpm hout) hdE hJw h)
    · intro e' he' hde' hne'
      obtain ⟨z, hz, hzJ, rfl⟩ := exists_of_mem_nodes_FOut hF hJ he'
      have hdz := (arcLe_shiftOut_iff hdE (hends _ hz hzJ) hJw).1 hde'
      have hzd : z ≠ d.1.1 := fun h => hne' (by rw [h])
      exact (arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2
        (hspec.2.2.2 z hz hdz hzd)

end CutOut

section CutBij

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- Lift a region pair of the inside polygon back: `(i', j') ↦ (i' + J.1, j' + J.1)`. -/
def KLunShift (J : Fin n × Fin n) (h : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) : Fin n × Fin n :=
  (⟨min (h.1.val + J.1.val) (n - 1), by have := NeZero.pos n; omega⟩,
    ⟨min (h.2.val + J.1.val) (n - 1), by have := NeZero.pos n; omega⟩)

/-- Undo the collapse: `r ↦ r` for `r ≤ i`, `r ↦ r + (w - 1)` beyond. -/
def KLunCol (J : Fin n × Fin n) (r : ℕ) : ℕ := if r ≤ J.1.val then r else r + (KLwIn J - 1)

/-- Lift a region pair of the outside polygon back. -/
def KLunColP (J : Fin n × Fin n) (g : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) :
    Fin n × Fin n :=
  (⟨min (KLunCol J g.1.val) (n - 1), by have := NeZero.pos n; omega⟩,
    ⟨min (KLunCol J g.2.val) (n - 1), by have := NeZero.pos n; omega⟩)

/-- `(KLunShift J h).k = h.k + i`. -/
theorem KLunShift_val (h : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) :
    (KLunShift J h).1.val = h.1.val + J.1.val ∧ (KLunShift J h).2.val = h.2.val + J.1.val := by
  have h1 := h.1.isLt; have h2 := h.2.isLt; have := J.2.isLt
  simp only [KLunShift, KLwIn] at *
  constructor <;> omega

omit [NeZero n] in
private theorem unCol_lt {r : ℕ} (hr : r < n - KLwIn J + 1)
    (hJ : J.1.val < J.2.val) : KLunCol J r < n := by
  have := J.2.isLt
  simp only [KLunCol, KLwIn] at *
  split_ifs <;> omega

/-- For `i < j`: `(KLunColP J g).k = KLunCol J g.k`. -/
theorem KLunColP_val (g : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))
    (hJ : J.1.val < J.2.val) :
    (KLunColP J g).1.val = KLunCol J g.1.val ∧ (KLunColP J g).2.val = KLunCol J g.2.val := by
  have h1 := unCol_lt g.1.isLt hJ; have h2 := unCol_lt g.2.isLt hJ
  simp only [KLunColP]
  constructor <;> omega

omit [NeZero n] in
/-- `KLunCol J r = r` for `r ≤ i`. -/
theorem KLunCol_of_le {r : ℕ} (h : r ≤ J.1.val) : KLunCol J r = r := by simp [KLunCol, h]

omit [NeZero n] in
/-- `KLunCol J r = r + (j - i - 1)` for `r > i`. -/
theorem KLunCol_of_gt {r : ℕ} (h : J.1.val < r) : KLunCol J r = r + (KLwIn J - 1) := by
  simp [KLunCol, not_le.2 h]

omit [NeZero n] in
private theorem col_unCol {r : ℕ} : KLcol J (KLunCol J r) = r := by
  simp only [KLcol, KLunCol, KLwIn]
  split_ifs <;> omega

omit [NeZero n] in
/-- `KLunCol` undoes `KLcol` on points outside the open arc of `J` (for `i + 2 ≤ j`). -/
theorem KLunCol_col {r : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r) (hJ : J.1.val + 2 ≤ J.2.val) :
    KLunCol J (KLcol J r) = r := by
  simp only [KLcol, KLunCol, KLwIn]
  split_ifs <;> omega

omit [NeZero n] in
private theorem unCol_ends {r : ℕ} (hJ : J.1.val + 2 ≤ J.2.val) :
    KLunCol J r ≤ J.1.val ∨ J.2.val ≤ KLunCol J r := by
  simp only [KLunCol, KLwIn]
  split_ifs <;> omega

private theorem shiftIn_unShift (h : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) :
    KLshiftIn J (KLunShift J h) = h := by
  have hv := KLunShift_val h
  have h1 := h.1.isLt; have h2 := h.2.isLt
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [KLshiftIn, hv] <;> omega

private theorem unShift_shiftIn {d : Fin n × Fin n} (hd : KLArcLe d J) (h12 : d.1 ≤ d.2) :
    KLunShift J (KLshiftIn J d) = d := by
  have hv := KLshiftIn_val hd h12
  simp only [KLArcLe, Fin.le_def] at hd h12
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [KLunShift, hv] <;>
    have := d.2.isLt <;> omega

private theorem shiftOut_unColP (g : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))
    (hJ : J.1.val + 2 ≤ J.2.val) : KLshiftOut J (KLunColP J g) = g := by
  have hJ2 : J.1.val < J.2.val := by omega
  have hv := KLunColP_val g hJ2
  have h1 := KLshiftOut_val (KLunColP J g) hJ2
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · rw [h1.1, hv.1, col_unCol]
  · rw [h1.2, hv.2, col_unCol]

private theorem unColP_shiftOut {d : Fin n × Fin n} (hd : KLOutEnds J d)
    (hJ : J.1.val + 2 ≤ J.2.val) :
    KLunColP J (KLshiftOut J d) = d := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have hv := KLunColP_val (KLshiftOut J d) hJ2
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · rw [hv.1, h1.1, KLunCol_col hd.1 hJ]
  · rw [hv.2, h1.2, KLunCol_col hd.2.1 hJ]

/-- A lifted outside pair has no endpoint strictly inside `J`. -/
private theorem outEnds_unColP (g : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) (hg : g.1 < g.2)
    (hJ : J.1.val + 2 ≤ J.2.val) : KLOutEnds J (KLunColP J g) := by
  have hJ2 : J.1.val < J.2.val := by omega
  have hv := KLunColP_val g hJ2
  rw [Fin.lt_def] at hg
  refine ⟨hv.1 ▸ unCol_ends hJ, hv.2 ▸ unCol_ends hJ, ?_⟩
  rw [hv.1, hv.2]
  simp only [KLunCol, KLwIn]; split_ifs <;> omega

/-- Glue an outside and an inside family back along `J`. -/
def KLglueF (J : Fin n × Fin n) (G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)))
    (H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))) : Finset (Fin n × Fin n) :=
  insert J (G.image (KLunColP J) ∪ H.image (KLunShift J))

/-- `d` is in `diagonals m` iff `IsDiag m d.1 d.2`. -/
theorem KLmem_diagonals_iff {m : ℕ}
    {d : Fin m × Fin m} : d ∈ diagonals m ↔ IsDiag m d.1 d.2 := by
  simp [diagonals]

variable (hJd : IsDiag n J.1 J.2)
include hJd

omit [NeZero n] in
/-- A diagonal `J = (i, j)` of the `n`-gon has `i + 2 ≤ j`. -/
theorem KLwidth_of_isDiag : J.1.val + 2 ≤ J.2.val := by
  obtain ⟨h1, h2, -⟩ := hJd; rw [Fin.lt_def] at h1; omega

omit [NeZero n] hJd in
/-- The inside family is a crossing-free family of diagonals. -/
theorem KLFIn_mem_TSP {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) :
    KLFIn F J ∈ TSP (KLwIn J + 1) := by
  rw [mem_TSP]
  constructor
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨hdF, hdJ, hne⟩ := mem_filter.1 hd
    obtain ⟨d1, d2, d3⟩ := hF.1 d hdF
    have hv := KLshiftIn_val hdJ (le_of_lt d1)
    rw [KLmem_diagonals_iff]
    have hJ' := hdJ
    simp only [KLArcLe, Fin.le_def] at hJ'
    have hne' : ¬(d.1.val = J.1.val ∧ d.2.val = J.2.val) := fun h =>
      hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    rw [Fin.lt_def] at d1
    refine ⟨by rw [Fin.lt_def, hv.1, hv.2]; omega, by rw [hv.1, hv.2]; omega, ?_⟩
    rw [hv.1, hv.2]; simp only [KLwIn]; omega
  · intro y hy z hz hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hz
    obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
    obtain ⟨heF, heJ, -⟩ := mem_filter.1 he
    have hd1 := (hF.1 d hdF).1
    have he1 := (hF.1 e heF).1
    have hv := KLshiftIn_val hdJ (le_of_lt hd1)
    have hw := KLshiftIn_val heJ (le_of_lt he1)
    apply hF.2 d hdF e heF
    simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
    simp only [KLArcLe, Fin.le_def] at hdJ heJ
    omega

/-- The outside family is a crossing-free family of diagonals. -/
theorem KLFOut_mem_TSP {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KLFOut F J ∈ TSP (n - KLwIn J + 1) := by
  have hJw := KLwidth_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  rw [mem_TSP]
  constructor
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
    have hE := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hdF) hdJ
    obtain ⟨d1, d2, d3⟩ := hF.1 d hdF
    have hv := KLshiftOut_val d hJ2
    have hne : ¬(d.1.val = J.1.val ∧ d.2.val = J.2.val) := fun h =>
      hdJ (by simp only [KLArcLe, Fin.le_def]; omega)
    have hn2 := J.2.isLt
    have hd2 := d.2.isLt
    rw [KLmem_diagonals_iff]
    obtain ⟨e1, e2, e3⟩ := hE
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.lt_def, hv.1, hv.2]; simp only [KLcol, KLwIn]; split_ifs <;> omega
    · rw [hv.1, hv.2]; simp only [KLcol, KLwIn]; split_ifs <;> omega
    · rw [hv.1, hv.2]; simp only [KLcol, KLwIn]; split_ifs <;> omega
  · intro y hy z hz hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hz
    obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
    obtain ⟨heF, heJ⟩ := mem_filter.1 he
    have hdE := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hdF) hdJ
    have heE := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem heF) heJ
    have hv := KLshiftOut_val d hJ2
    have hw := KLshiftOut_val e hJ2
    apply hF.2 d hdF e heF
    obtain ⟨a1, a2, a3⟩ := hdE
    obtain ⟨b1, b2, b3⟩ := heE
    simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
    simp only [KLcol, KLwIn] at hc
    split_ifs at hc <;> omega

private theorem arcLe_unShift (h : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) : KLArcLe (KLunShift J h) J := by
  have hv := KLunShift_val h
  have hJw := KLwidth_of_isDiag hJd
  have h2 := h.2.isLt
  have hw : KLwIn J = J.2.val - J.1.val := rfl
  constructor
  · rw [Fin.le_def, hv.1]; omega
  · rw [Fin.le_def, hv.2]; omega

omit hJd in
private theorem unShift_ne {h : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)}
    (hh : IsDiag (KLwIn J + 1) h.1 h.2) :
    KLunShift J h ≠ J := by
  intro he
  have hv := KLunShift_val h
  obtain ⟨-, -, h3⟩ := hh
  apply h3
  have e1 := congrArg (fun x => x.1.val) he
  have e2 := congrArg (fun x => x.2.val) he
  simp only [hv.1, hv.2] at e1 e2
  simp only [KLwIn]; omega

private theorem not_arcLe_unColP {g : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)}
    (hg : IsDiag (n - KLwIn J + 1) g.1 g.2) : ¬KLArcLe (KLunColP J g) J := by
  have hJw := KLwidth_of_isDiag hJd
  have hv := KLunColP_val g (by omega)
  obtain ⟨g1, g2, -⟩ := hg
  rw [Fin.lt_def] at g1
  simp only [KLArcLe, Fin.le_def, hv.1, hv.2, KLunCol, KLwIn]
  split_ifs <;> omega

/-- The glued family is a crossing-free family of diagonals. -/
theorem KLglueF_mem_TSP {G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))}
    {H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))} (hG : G ∈ TSP (n - KLwIn J + 1))
    (hH : H ∈ TSP (KLwIn J + 1)) : KLglueF J G H ∈ TSP n := by
  have hJw := KLwidth_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  rw [mem_TSP] at hG hH ⊢
  have hGd : ∀ g ∈ G, IsDiag _ g.1 g.2 := fun g hg => KLmem_diagonals_iff.1 (hG.1 hg)
  have hHd : ∀ h ∈ H, IsDiag _ h.1 h.2 := fun h hh => KLmem_diagonals_iff.1 (hH.1 hh)
  have hn2 := J.2.isLt
  -- the three kinds of elements
  have kinds : ∀ x ∈ KLglueF J G H, x = J ∨ (∃ g ∈ G, KLunColP J g = x) ∨
      (∃ h ∈ H, KLunShift J h = x) := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact Or.inl rfl
    rcases mem_union.1 hx with hx | hx
    · exact Or.inr (Or.inl (mem_image.1 hx))
    · exact Or.inr (Or.inr (mem_image.1 hx))
  constructor
  · intro x hx
    rw [KLmem_diagonals_iff]
    rcases kinds x hx with rfl | ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩
    · exact hJd
    · have hv := KLunColP_val g hJ2
      obtain ⟨g1, g2, g3⟩ := hGd g hg
      rw [Fin.lt_def] at g1
      refine ⟨?_, ?_, ?_⟩
      · rw [Fin.lt_def, hv.1, hv.2]; simp only [KLunCol, KLwIn]; split_ifs <;> omega
      · rw [hv.1, hv.2]; simp only [KLunCol, KLwIn]; split_ifs <;> omega
      · rw [hv.1, hv.2]; simp only [KLunCol, KLwIn] at g3 ⊢; split_ifs <;> omega
    · have hv := KLunShift_val h
      obtain ⟨h1, h2, h3⟩ := hHd h hh
      rw [Fin.lt_def] at h1
      have hb := h.2.isLt
      refine ⟨by rw [Fin.lt_def, hv.1, hv.2]; omega, by rw [hv.1, hv.2]; omega, ?_⟩
      rw [hv.1, hv.2]; simp only [KLwIn] at h3 hb ⊢; omega
  · -- crossing-freeness
    have outE : ∀ g ∈ G, KLOutEnds J (KLunColP J g) := fun g hg =>
      outEnds_unColP g (hGd g hg).1 hJw
    have crossJ : ∀ x, KLOutEnds J x → ¬Crossing J x ∧ ¬Crossing x J := by
      intro x ⟨a1, a2, a3⟩
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossIn : ∀ h, ¬Crossing J (KLunShift J h) ∧ ¬Crossing (KLunShift J h) J := by
      intro h
      have := arcLe_unShift hJd h
      simp only [KLArcLe, Fin.le_def] at this
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossGH : ∀ g h, KLOutEnds J (KLunColP J g) →
        ¬Crossing (KLunColP J g) (KLunShift J h) ∧ ¬Crossing (KLunShift J h) (KLunColP J g) := by
      intro g h ⟨a1, a2, a3⟩
      have := arcLe_unShift hJd h
      simp only [KLArcLe, Fin.le_def] at this
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossGG : ∀ g ∈ G, ∀ g' ∈ G, ¬Crossing (KLunColP J g) (KLunColP J g') := by
      intro g hg g' hg' hc
      apply hG.2 g hg g' hg'
      have hv := KLunColP_val g hJ2
      have hw := KLunColP_val g' hJ2
      simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2, KLunCol, KLwIn] at hc ⊢
      split_ifs at hc <;> omega
    have crossHH : ∀ h ∈ H, ∀ h' ∈ H, ¬Crossing (KLunShift J h) (KLunShift J h') := by
      intro h hh h' hh' hc
      apply hH.2 h hh h' hh'
      have hv := KLunShift_val h
      have hw := KLunShift_val h'
      simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
      omega
    intro x hx y hy
    rcases kinds x hx with rfl | ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩ <;>
      rcases kinds y hy with rfl | ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
    · exact not_crossing_self _
    · exact (crossJ _ (outE g' hg')).1
    · exact (crossIn h').1
    · exact (crossJ _ (outE g hg)).2
    · exact crossGG g hg g' hg'
    · exact (crossGH g h' (outE g hg)).1
    · exact (crossIn h).2
    · exact (crossGH g' h (outE g' hg')).2
    · exact crossHH h hh h' hh'

/-- Cutting the glued family along `J` recovers the inside family. -/
theorem KLFIn_glueF {G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))}
    {H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))} (hG : G ∈ TSP (n - KLwIn J + 1))
    (hH : H ∈ TSP (KLwIn J + 1)) : KLFIn (KLglueF J G H) J = H := by
  rw [mem_TSP] at hG hH
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    obtain ⟨hxg, hxJ, hne⟩ := mem_filter.1 hx
    rcases mem_insert.1 hxg with rfl | hxg
    · exact absurd rfl hne
    rcases mem_union.1 hxg with hxg | hxg
    · obtain ⟨g, hg, rfl⟩ := mem_image.1 hxg
      exact absurd hxJ (not_arcLe_unColP hJd (KLmem_diagonals_iff.1 (hG.1 hg)))
    · obtain ⟨h, hh, rfl⟩ := mem_image.1 hxg
      rw [shiftIn_unShift]; exact hh
  · intro hy
    refine mem_image.2 ⟨KLunShift J y, mem_filter.2 ⟨?_, arcLe_unShift hJd y,
      unShift_ne (KLmem_diagonals_iff.1 (hH.1 hy))⟩, shiftIn_unShift y⟩
    exact mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ hy))

/-- Cutting the glued family along `J` recovers the outside family. -/
theorem KLFOut_glueF {G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))}
    {H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))} (hG : G ∈ TSP (n - KLwIn J + 1)) :
    KLFOut (KLglueF J G H) J = G := by
  have hJw := KLwidth_of_isDiag hJd
  rw [mem_TSP] at hG
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    obtain ⟨hxg, hxJ⟩ := mem_filter.1 hx
    rcases mem_insert.1 hxg with rfl | hxg
    · exact absurd ⟨le_refl _, le_refl _⟩ hxJ
    rcases mem_union.1 hxg with hxg | hxg
    · obtain ⟨g, hg, rfl⟩ := mem_image.1 hxg
      rw [shiftOut_unColP g hJw]; exact hg
    · obtain ⟨h, -, rfl⟩ := mem_image.1 hxg
      exact absurd (arcLe_unShift hJd h) hxJ
  · intro hy
    refine mem_image.2 ⟨KLunColP J y, mem_filter.2 ⟨?_,
      not_arcLe_unColP hJd (KLmem_diagonals_iff.1 (hG.1 hy))⟩, shiftOut_unColP y hJw⟩
    exact mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ hy))

/-- Gluing the two pieces of a tree `F ∋ J` back along `J` gives `F`. -/
theorem KLglueF_cut {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KLglueF J (KLFOut F J) (KLFIn F J) = F := by
  have hJw := KLwidth_of_isDiag hJd
  ext x
  constructor
  · intro hx
    rcases mem_insert.1 hx with rfl | hx
    · exact hJ
    rcases mem_union.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      rw [unColP_shiftOut (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hdF) hdJ) hJw]
      exact hdF
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      rw [unShift_shiftIn hdJ (le_of_lt (hF.1 d hdF).1)]
      exact hdF
  · intro hx
    by_cases h1 : x = J
    · rw [h1]; exact mem_insert_self _ _
    refine mem_insert_of_mem ?_
    by_cases h2 : KLArcLe x J
    · refine mem_union_right _ (mem_image.2 ⟨KLshiftIn J x, mem_image_of_mem _
        (mem_filter.2 ⟨hx, h2, h1⟩), unShift_shiftIn h2 (le_of_lt (hF.1 x hx).1)⟩)
    · refine mem_union_left _ (mem_image.2 ⟨KLshiftOut J x, mem_image_of_mem _
        (mem_filter.2 ⟨hx, h2⟩), unColP_shiftOut
          (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hx) h2) hJw⟩)

/-- **The cut bijection**: `{F ∈ T_SP(n) : J ∈ F} ≃ T_SP(outside) × T_SP(inside)`. -/
theorem KLsum_cut (hn : 2 ≤ n)
    (f : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) →
      Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ) :
    ∑ F ∈ (TSP n).filter (fun F => J ∈ F), f (KLFOut F J) (KLFIn F J)
      = ∑ G ∈ TSP (n - KLwIn J + 1), ∑ H ∈ TSP (KLwIn J + 1), f G H := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun F => (KLFOut F J, KLFIn F J)) (fun p => KLglueF J p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    have hF' := KLisTSP_of_mem_TSP hFT
    exact mem_product.2 ⟨KLFOut_mem_TSP hJd hF' hn hJF, KLFIn_mem_TSP hF'⟩
  · intro p hp
    obtain ⟨hG, hH⟩ := mem_product.1 hp
    exact mem_filter.2 ⟨KLglueF_mem_TSP hJd hG hH, mem_insert_self _ _⟩
  · intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    exact KLglueF_cut hJd (KLisTSP_of_mem_TSP hFT) hn hJF
  · intro p hp
    obtain ⟨hG, hH⟩ := mem_product.1 hp
    exact Prod.ext (KLFOut_glueF hJd hG) (KLFIn_glueF hJd hG hH)
  · intro F _
    rfl

end CutBij

end RBM.Loop
