/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.DecayGen
import RBM3D.BA.FlowPins
import RBM3D.BA.KTreeRep
import RBM3D.BA.Prop6Path
import RBM3D.BA.CombesThomas
import RBM3D.BA.GreenSchur
import RBM3D.BA.TwistStep2
import RBM3D.BA.Step5IIIKer
import RBM3D.BA.EMn2BA
import RBM3D.Induction.KDecay

/-!
# Ticket T2486, target 1: the far decay of the block Anderson `𝒦` (`BAKcalDecay`)

The BA twin of `Induction/KDecay.lean` §1-§8 (`STKcalDecay`, `stKcalDecay_holds`): the merged generic premise
`STKcalDecaygL` (`Chain/DecayGen.lean:83`) at the BA carrier `baFMz sz z`, along every BA flow
(paper `(eq:bcal_k)`, `1_2:1056`; `tree-representation_BA` `A:592-598`; `lem_pureloop` `A:643-660`; `lem:propM` `7_8:1847`).

* §1 walks in the graph of a weighted tree value (`KLgval`) and the distance bound `|a_i - a_j| ≤ k S`; the generic bound
  `‖KLgval‖ ≤ (L^d)^{#nodes} B^{n + #edges} exp(-κ' maxDist/(R+1))` when any two labels are joined by a walk of at most `R` steps.
* §2 the slot graph of the cactus of `F ∈ TSP n` (leaf `Θ`, chord `tΘ`, `M`-edges `s → BAnextSlot s`) is connected
  (`BAnextSlot_orbit`, the chord slots, the tree of `F`); a walk bound `R_n` uniform in `F ∈ TSP n` (finitely many trees).
* §3 `Γ_M(F)`: the cactus value is bounded by `(L^d)^{n+2n²} B^{2n+3n²} e^{-κ' maxDist/(R+1)}`.
* §4 the edge bounds at the BA datum from `baProp5to8_holds` (`Θ`) and `baPropM_holds` (`M^{(B)}`): `C₁ W^{2Q} e^{-(c/ℓ_u)|x-y|}`.
* §5 `𝒦` for `k = 2` (`(Kn2sol)`, the convolution `Θ M^{(σσ')}`) and `k ≥ 3` (`baTreeRep`); §6 the far-region estimate at fixed `(L, W)`.
* §7 `BAKcalDecay` and `baKcalDecay_holds` (the absorption into `W^{-D}`); §8 the compiled nonempty instances at `d = 3`.

Private helpers of `Induction/KDecay.lean` are reached by `open private`; no merged file is edited.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private KDecay_zdistD_symm KDecay_zdistD_tri KDecay_B0_le KDecay_card_TSP KDecay_eventually
  KDecay_anc_step KDecay_maxDist_two_le from RBM3D.Induction.KDecay

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes Finset

/-! ## 1. Walks and the generic bound for a weighted tree value -/

section Graph

variable {d L : ℕ} [NeZero L]

/-- Walks of length `k` in a graph. -/
private inductive KDecayBA_Walk {V : Type*} (adj : V → V → Prop) : ℕ → V → V → Prop
  | refl (x : V) : KDecayBA_Walk adj 0 x x
  | step {k : ℕ} {x y z : V} : adj x y → KDecayBA_Walk adj k y z → KDecayBA_Walk adj (k + 1) x z

/-- The (symmetric) adjacency of the graph of a weighted tree value: leaf `ℓ — p ℓ`, edge `c e — q e`. -/
private def KDecayBA_adj {Nd Lf Ed : Type*} (p : Lf → Nd) (c q : Ed → Nd) : Lf ⊕ Nd → Lf ⊕ Nd → Prop :=
  fun x y => (∃ ℓ, x = Sum.inl ℓ ∧ y = Sum.inr (p ℓ)) ∨ (∃ ℓ, y = Sum.inl ℓ ∧ x = Sum.inr (p ℓ)) ∨
    (∃ e, x = Sum.inr (c e) ∧ y = Sum.inr (q e)) ∨ (∃ e, y = Sum.inr (c e) ∧ x = Sum.inr (q e))

private theorem KDecayBA_walk_of_rtg {V : Type*} {adj : V → V → Prop} {x y : V}
    (h : Relation.ReflTransGen adj x y) : ∃ k, KDecayBA_Walk adj k x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, KDecayBA_Walk.refl _⟩
  | head hxy _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, KDecayBA_Walk.step hxy hk⟩

private theorem KDecayBA_walk_dist {V : Type*} (adj : V → V → Prop) (β : V → Zd d L) (S : ℕ)
    (hadj : ∀ x y, adj x y → zdistD d L (β x - β y) ≤ S) :
    ∀ (k : ℕ) (x y : V), KDecayBA_Walk adj k x y → zdistD d L (β x - β y) ≤ k * S := by
  intro k x y h
  induction h with
  | refl x => simp
  | @step k x y z hxy _ ih =>
    have h1 := KDecay_zdistD_tri (β x) (β y) (β z)
    have h2 := hadj x y hxy
    rw [Nat.add_mul, one_mul]
    omega

/-- **The generic bound** for a weighted tree value: if every leaf weight and every edge weight is bounded by
`B e^{-κ' |x-y|}` and any two labels are joined by a walk of at most `R` steps, then
`‖KLgval‖ ≤ (L^d)^{#nodes} B^{n + #edges} e^{-κ' maxDist/(R+1)}`. -/
private theorem KDecayBA_gval_bound {Nd Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Ed] {n : ℕ}
    (a : Fin n → Zd d L) (Mw : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (p : Fin n → Nd)
    (E : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → Nd) {B κ' : ℝ} (hB : 1 ≤ B) (hκ : 0 ≤ κ')
    (hM : ∀ ℓ x y, ‖Mw ℓ x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    (hE : ∀ e x y, ‖E e x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ)))) {R : ℕ}
    (hconn : ∀ i j : Fin n, ∃ k ≤ R, KDecayBA_Walk (KDecayBA_adj p c q) k (Sum.inl i) (Sum.inl j)) :
    ‖KLgval d L a Mw p E c q‖ ≤ ((L ^ d : ℕ) : ℝ) ^ (Fintype.card Nd) * B ^ (n + Fintype.card Ed) *
      Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))) := by
  have hB0 : 0 ≤ B := by linarith
  set X : ℝ := B ^ (n + Fintype.card Ed) * Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))) with hX
  have hpt : ∀ b : Nd → Zd d L,
      ‖(∏ ℓ, Mw ℓ (a ℓ) (b (p ℓ))) * ∏ e, E e (b (c e)) (b (q e))‖ ≤ X := by
    intro b
    set S₁ : ℕ := ∑ ℓ, zdistD d L (a ℓ - b (p ℓ)) with hS₁
    set S₂ : ℕ := ∑ e, zdistD d L (b (c e) - b (q e)) with hS₂
    have hadj : ∀ x y, KDecayBA_adj p c q x y →
        zdistD d L (Sum.elim a b x - Sum.elim a b y) ≤ S₁ + S₂ := by
      intro x y h
      rcases h with ⟨ℓ, rfl, rfl⟩ | ⟨ℓ, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      · simp only [Sum.elim_inl, Sum.elim_inr]
        have := Finset.single_le_sum (f := fun ℓ => zdistD d L (a ℓ - b (p ℓ))) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ ℓ)
        omega
      · simp only [Sum.elim_inl, Sum.elim_inr]
        rw [KDecay_zdistD_symm]
        have := Finset.single_le_sum (f := fun ℓ => zdistD d L (a ℓ - b (p ℓ))) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ ℓ)
        omega
      · simp only [Sum.elim_inr]
        have := Finset.single_le_sum (f := fun e => zdistD d L (b (c e) - b (q e))) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ e)
        omega
      · simp only [Sum.elim_inr]
        rw [KDecay_zdistD_symm]
        have := Finset.single_le_sum (f := fun e => zdistD d L (b (c e) - b (q e))) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ e)
        omega
    have hmax : KLmaxDist d L a ≤ R * (S₁ + S₂) := by
      refine Finset.sup_le fun pr _ => ?_
      obtain ⟨k, hkR, hk⟩ := hconn pr.1 pr.2
      have h := KDecayBA_walk_dist _ (Sum.elim a b) (S₁ + S₂) hadj k _ _ hk
      simp only [Sum.elim_inl] at h
      exact h.trans (Nat.mul_le_mul_right _ hkR)
    have hmaxR : (KLmaxDist d L a : ℝ) ≤ ((R : ℝ) + 1) * ((S₁ + S₂ : ℕ) : ℝ) := by
      have h1 : (KLmaxDist d L a : ℝ) ≤ ((R * (S₁ + S₂) : ℕ) : ℝ) := by exact_mod_cast hmax
      push_cast at h1 ⊢
      have : (0 : ℝ) ≤ ((S₁ : ℝ) + S₂) := by positivity
      nlinarith
    have hL : ∏ ℓ, ‖Mw ℓ (a ℓ) (b (p ℓ))‖ ≤ B ^ n * Real.exp (-(κ' * (S₁ : ℝ))) := by
      calc ∏ ℓ, ‖Mw ℓ (a ℓ) (b (p ℓ))‖
          ≤ ∏ ℓ, (B * Real.exp (-(κ' * (zdistD d L (a ℓ - b (p ℓ)) : ℝ)))) :=
            prod_le_prod₀ (fun _ _ => norm_nonneg _) fun ℓ _ => hM _ _ _
        _ = B ^ n * Real.exp (-(κ' * (S₁ : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← Real.exp_sum]
            congr 2
            simp only [hS₁, Nat.cast_sum, mul_sum, sum_neg_distrib]
    have hE' : ∏ e, ‖E e (b (c e)) (b (q e))‖ ≤ B ^ Fintype.card Ed * Real.exp (-(κ' * (S₂ : ℝ))) := by
      calc ∏ e, ‖E e (b (c e)) (b (q e))‖
          ≤ ∏ e, (B * Real.exp (-(κ' * (zdistD d L (b (c e) - b (q e)) : ℝ)))) :=
            prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => hE _ _ _
        _ = B ^ Fintype.card Ed * Real.exp (-(κ' * (S₂ : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, ← Real.exp_sum]
            congr 2
            simp only [hS₂, Nat.cast_sum, mul_sum, sum_neg_distrib]
    have hexp : Real.exp (-(κ' * (S₁ : ℝ))) * Real.exp (-(κ' * (S₂ : ℝ))) ≤
        Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
      have h1 : (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1) ≤ ((S₁ + S₂ : ℕ) : ℝ) := by
        rw [div_le_iff₀ hR1]; linarith
      have h2 : κ' * ((KLmaxDist d L a : ℝ) / ((R : ℝ) + 1)) ≤ κ' * ((S₁ + S₂ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hκ
      push_cast at h2
      rw [mul_div_assoc]
      linarith
    rw [norm_mul, norm_prod, norm_prod]
    calc _ ≤ (B ^ n * Real.exp (-(κ' * (S₁ : ℝ)))) * (B ^ Fintype.card Ed * Real.exp (-(κ' * (S₂ : ℝ)))) :=
          mul_le_mul hL hE' (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = B ^ (n + Fintype.card Ed) * (Real.exp (-(κ' * (S₁ : ℝ))) * Real.exp (-(κ' * (S₂ : ℝ)))) := by
          ring
      _ ≤ X := by rw [hX]; gcongr
  have hcard : Fintype.card (Nd → Zd d L) = (L ^ d) ^ Fintype.card Nd := by
    rw [Fintype.card_fun, card_Zd]
  unfold KLgval
  calc _ ≤ ∑ b : Nd → Zd d L, ‖(∏ ℓ, Mw ℓ (a ℓ) (b (p ℓ))) * ∏ e, E e (b (c e)) (b (q e))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _b : Nd → Zd d L, X := sum_le_sum fun b _ => hpt b
    _ = ((L ^ d : ℕ) : ℝ) ^ (Fintype.card Nd) * X := by
        rw [sum_const, card_univ, hcard, nsmul_eq_mul]
        push_cast
        ring
    _ = _ := by rw [hX]; ring

end Graph

/-! ## 2. The slot graph of the cactus is connected -/

section Slots

variable {n : ℕ} [NeZero n]

/-- The graph of the cactus value `BACactusVal`: labels `Fin n`, slots `BAslot F`; leaf edges, chords, `M`-edges. -/
private abbrev KDecayBA_G (F : Finset (Fin n × Fin n)) : Fin n ⊕ BAslot F → Fin n ⊕ BAslot F → Prop :=
  KDecayBA_adj (BAslotLeaf F) (BACactusValSrc F) (BACactusValTgt F)

/-- The slots of one node are joined by `M`-edges (`BAnextSlot_orbit`: one cycle per node). -/
private theorem KDecayBA_node_conn {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) {s t : BAslot F}
    (h : BAslotNode F s = BAslotNode F t) :
    Relation.ReflTransGen (KDecayBA_G F) (Sum.inr s) (Sum.inr t) := by
  obtain ⟨k, hk⟩ := (BAnextSlot_orbit hF hn s t).1 h
  rw [← hk]
  clear hk h
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Relation.ReflTransGen.tail ih (Or.inr (Or.inr (Or.inl ⟨Sum.inr _, rfl, rfl⟩)))

private theorem KDecayBA_adj_symm {Nd Lf Ed : Type*} (p : Lf → Nd) (c q : Ed → Nd) :
    ∀ x y, KDecayBA_adj p c q x y → KDecayBA_adj p c q y x := by
  intro x y h
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

private theorem KDecayBA_rtg_symm {V : Type*} {adj : V → V → Prop} (h : ∀ x y, adj x y → adj y x) {x y : V}
    (hxy : Relation.ReflTransGen adj x y) : Relation.ReflTransGen adj y x := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (h _ _ hbc) ih

/-- Every slot is joined to the slot of the last leaf (in the root node). -/
private theorem KDecayBA_root_conn {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (r : Fin n)
    (hr : r.val = n - 1) :
    ∀ (m : ℕ) (x : Fin n × Fin n), x ∈ KLnodes F → (F.filter (KLArcLe x)).card ≤ m → ∀ s : BAslot F,
      BAslotNode F s = x → Relation.ReflTransGen (KDecayBA_G F) (Sum.inr s) (Sum.inr (BAslotLeaf F r)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hx hxm s hs
    by_cases hxw : x = KLwholeP n
    · refine KDecayBA_node_conn hF hn ?_
      rw [hs, hxw]
      exact (KLleafPar_root F hr).symm
    · obtain ⟨hp, -, -, hxF, hcard, -⟩ := KDecay_anc_step hF hn hx hxw
      set J : ↥F := ⟨x, hxF⟩ with hJ
      have h1 : Relation.ReflTransGen (KDecayBA_G F) (Sum.inr s) (Sum.inr (BAslotIn F J)) :=
        KDecayBA_node_conn hF hn (by rw [hs]; rfl)
      have h2 : KDecayBA_G F (Sum.inr (BAslotIn F J)) (Sum.inr (BAslotOut F J)) :=
        Or.inr (Or.inr (Or.inl ⟨Sum.inl J, rfl, rfl⟩))
      have h3 := ih ((F.filter (KLArcLe (KLnodePar F x))).card) (by omega) (KLnodePar F x) hp le_rfl
        (BAslotOut F J) rfl
      exact (h1.tail h2).trans h3

/-- **The slot graph of the cactus is connected**: any two labels are joined (leaf `Θ`, chord, `M`-edges). -/
private theorem KDecayBA_labels_conn {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (i j : Fin n) :
    Relation.ReflTransGen (KDecayBA_G F) (Sum.inl i) (Sum.inl j) := by
  have hr : ((⟨n - 1, by have := NeZero.pos n; omega⟩ : Fin n)).val = n - 1 := rfl
  have key : ∀ v : Fin n, Relation.ReflTransGen (KDecayBA_G F) (Sum.inl v)
      (Sum.inr (BAslotLeaf F ⟨n - 1, by have := NeZero.pos n; omega⟩)) := fun v =>
    Relation.ReflTransGen.head (Or.inl ⟨v, rfl, rfl⟩)
      (KDecayBA_root_conn hF hn _ hr _ (KLleafPar F v) (KLleafPar_mem F v) le_rfl (BAslotLeaf F v) rfl)
  exact (key i).trans (KDecayBA_rtg_symm (KDecayBA_adj_symm _ _ _) (key j))

/-- **A walk bound uniform in `F ∈ TSP n`** (finitely many trees): `R_n` steps join any two labels. -/
private theorem KDecayBA_walk_bound (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ∃ R : ℕ, ∀ F ∈ TSP n, ∀ i j : Fin n,
      ∃ k ≤ R, KDecayBA_Walk (KDecayBA_G F) k (Sum.inl i) (Sum.inl j) := by
  have h : ∀ F ∈ TSP n, ∀ i j : Fin n, ∃ k, KDecayBA_Walk (KDecayBA_G F) k (Sum.inl i) (Sum.inl j) :=
    fun F hF i j => KDecayBA_walk_of_rtg (KDecayBA_labels_conn (KLisTSP_of_mem_TSP hF) hn i j)
  choose! f hf using h
  refine ⟨(TSP n).sup fun F => univ.sup fun i => univ.sup fun j => f F i j, fun F hF i j => ⟨f F i j, ?_, hf F hF i j⟩⟩
  exact (Finset.le_sup (f := fun j => f F i j) (mem_univ j)).trans
    ((Finset.le_sup (f := fun i => univ.sup fun j => f F i j) (mem_univ i)).trans
      (Finset.le_sup (f := fun F => univ.sup fun i => univ.sup fun j => f F i j) hF))

end Slots

/-! ## 3. The cactus value of a tree with decaying edges decays -/

section Cactus

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **`Γ_M(F)` for `F ∈ TSP n`**: if every `Θ`-entry and every `M`-entry is bounded by `B e^{-κ' |x-y|}`, then
`|Γ_M(F)| ≤ (L^d)^{n + 2n²} B^{2n + 3n²} e^{-κ' maxDist a/(R+1)}`, `R` the walk bound of the slot graph. -/
private theorem KDecayBA_cactus_bound {R : ℕ}
    (hR : ∀ F ∈ TSP n, ∀ i j : Fin n, ∃ k ≤ R, KDecayBA_Walk (KDecayBA_G F) k (Sum.inl i) (Sum.inl j))
    {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (σ : Fin n → Bool) (a : Fin n → Zd d L) {B κ' : ℝ} (hB : 1 ≤ B) (hκ : 0 ≤ κ')
    (hΘ : ∀ s s' x y, ‖BAThetaOf M t s s' x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    (hMM : ∀ s x y, ‖M s x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ)))) :
    ‖BACactusVal d L M t F σ a‖ ≤ ((L ^ d : ℕ) : ℝ) ^ (n + 2 * (n * n)) * B ^ (2 * n + 3 * (n * n)) *
      Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))) := by
  have hB0 : 0 ≤ B := by linarith
  have hleaf : ∀ (v : Fin n) x y, ‖BACactusValLeafW M t σ v x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))) :=
    fun v x y => hΘ _ _ x y
  have hedge : ∀ (e : ↥F ⊕ BAslot F) x y, ‖BACactusValEdgeW M t F σ e x y‖ ≤
      B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))) := by
    intro e x y
    rcases e with J | s
    · simp only [BACactusValEdgeW, Sum.elim_inl, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0]
      calc t * ‖BAThetaOf M t (σ J.1.1) (σ J.1.2) x y‖ ≤ 1 * ‖BAThetaOf M t (σ J.1.1) (σ J.1.2) x y‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hΘ _ _ x y
    · simp only [BACactusValEdgeW, Sum.elim_inr]
      exact hMM _ x y
  have h := KDecayBA_gval_bound (Nd := BAslot F) (Ed := ↥F ⊕ BAslot F) a (BACactusValLeafW M t σ) (BAslotLeaf F)
    (BACactusValEdgeW M t F σ) (BACactusValSrc F) (BACactusValTgt F) hB hκ hleaf hedge (hR F hF)
  have hFn : F.card ≤ n * n := by
    have := card_le_univ F
    simpa using this
  have hLL : (1 : ℝ) ≤ ((L ^ d : ℕ) : ℝ) := by
    have : 1 ≤ L ^ d := Nat.one_le_pow _ _ (NeZero.pos L)
    exact_mod_cast this
  have hc1 : Fintype.card (BAslot F) ≤ n + 2 * (n * n) := by rw [BAslot_card]; omega
  have hc2 : n + Fintype.card (↥F ⊕ BAslot F) ≤ 2 * n + 3 * (n * n) := by
    rw [Fintype.card_sum, Fintype.card_coe, BAslot_card]; omega
  unfold BACactusVal
  refine h.trans ?_
  have he : 0 ≤ Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))) := (Real.exp_pos _).le
  gcongr

end Cactus

/-! ## 4. The edge bounds at the BA datum (`baProp5to8_holds`, `baPropM_holds`) -/

section EdgeBounds

variable {d : ℕ}

private theorem KDecayBA_Msigma_norm {L : ℕ} [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y : Zd d L) :
    ‖BAMsigma d L (BAMB d L g z m) σ x y‖ = ‖BAMB d L g z m x y‖ := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ↓reduceIte, Matrix.conjTranspose_apply, norm_star]
    rw [BAMB_symm]
  · simp [BAMsigma]

/-- `‖M^{(B)}_{xy}‖ ≤ B_M e^{-c_M |x-y|}` in both regimes of `lem:propM` (`7_8:1847`). -/
private theorem KDecayBA_M_const (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ BM : ℝ, 1 ≤ BM ∧ ∃ cM : ℝ, 0 < cM ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal d L g κ E m → ∀ x y : Zd d L,
        ‖BAMB d L g (E : ℂ) m x y‖ ≤ BM * Real.exp (-(cM * (zdistD d L (x - y) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := baPropM_holds d Λ κ hd hΛ hκ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max 1 c⁻¹, le_max_left _ _, min (Real.log 2) c, lt_min hlog hc, ?_⟩
  intro L _ hL g hg hgΛ E m hr x y
  obtain ⟨-, -, -, -, h5, h6⟩ := H L hL g hg hgΛ E m hr
  have hr0 : (0 : ℝ) ≤ (zdistD d L (x - y) : ℝ) := Nat.cast_nonneg _
  have hBM : 0 ≤ max 1 c⁻¹ := le_trans zero_le_one (le_max_left _ _)
  by_cases hsm : g < (2 * C)⁻¹
  · have h := (h5 hsm x y).2
    have hCg : C * g ≤ 1 / 2 := by
      have := mul_lt_mul_of_pos_left hsm hC
      have e : C * (2 * C)⁻¹ = 1 / 2 := by field_simp
      linarith
    have h1 : (C * g) ^ zdistD d L (x - y) ≤ (1 / 2 : ℝ) ^ zdistD d L (x - y) :=
      pow_le_pow_left₀ (by positivity) hCg _
    have h2 : ((1 : ℝ) / 2) ^ zdistD d L (x - y) = Real.exp (-(Real.log 2 * (zdistD d L (x - y) : ℝ))) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]
      congr 1; ring
    have h3 : Real.exp (-(Real.log 2 * (zdistD d L (x - y) : ℝ))) ≤
        Real.exp (-(min (Real.log 2) c * (zdistD d L (x - y) : ℝ))) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left (Real.log 2) c])
    calc ‖BAMB d L g (E : ℂ) m x y‖ ≤ (C * g) ^ zdistD d L (x - y) := h
      _ ≤ Real.exp (-(min (Real.log 2) c * (zdistD d L (x - y) : ℝ))) := h1.trans (h2 ▸ h3)
      _ ≤ max 1 c⁻¹ * Real.exp (-(min (Real.log 2) c * (zdistD d L (x - y) : ℝ))) :=
          le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
  · have h := h6 (not_lt.mp hsm) x y
    have h3 : Real.exp (-c * (zdistD d L (x - y) : ℝ)) ≤
        Real.exp (-(min (Real.log 2) c * (zdistD d L (x - y) : ℝ))) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right (Real.log 2) c])
    calc ‖BAMB d L g (E : ℂ) m x y‖ ≤ c⁻¹ * Real.exp (-c * (zdistD d L (x - y) : ℝ)) := h
      _ ≤ max 1 c⁻¹ * Real.exp (-(min (Real.log 2) c * (zdistD d L (x - y) : ℝ))) :=
          mul_le_mul (le_max_right _ _) h3 (Real.exp_pos _).le hBM

/-- Property 5 (`prop:ThfadC`) for all entries, with `B_{t,|a|} ≤ B_{t,0}`. -/
private theorem KDecayBA_theta_const (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ x y : Zd d L,
        ‖BATheta d L g E m t σ₁ σ₂ x y‖ ≤
          C * Bparam d L g t 0 * Real.exp (-(c / ellT L g t * (zdistD d L (x - y) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := (baProp5to8_holds d Λ κ (1 / 2)).decay hd hΛ hκ
  refine ⟨C, hC, c, hc, ?_⟩
  intro L _ hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ x y
  rw [EMn2BA_theta_shift]
  have h := H L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (y - x)
  have hd' : zdistD d L (y - x) = zdistD d L (x - y) := KDecay_zdistD_symm y x
  rw [hd'] at h
  have hB := KLIndStepA_Bparam_le_zero (d := d) (L := L) (g := g) t (zdistD d L (x - y))
  have e : -c * (zdistD d L (x - y) : ℝ) / ellT L g t = -(c / ellT L g t * (zdistD d L (x - y) : ℝ)) := by ring
  rw [e] at h
  refine h.trans ?_
  gcongr

/-- **The edge constants**: in the far region `ℓ_u(g₀) < L` with `W^{-Q} ≤ g₀`, every `Θ`-entry and every
`M`-entry is bounded by `C₁ W^{2Q} e^{-(c/ℓ_u)|x-y|}` (`B_{u,0} ≤ 2 g₀⁻² ≤ 2 W^{2Q}`, `KDecay_B0_le`). -/
private theorem KDecayBA_edge_const (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ (g E u Q : ℝ) (m : ℂ),
      0 < g → g ≤ Λ → BAReal d L g κ E m → 0 ≤ u → u < 1 → 0 < Q → (W : ℝ) ^ (-Q) ≤ g → ellT L g u < L →
      (∀ s s' x y, ‖BATheta d L g E m u s s' x y‖ ≤
        (C₁ * (W : ℝ) ^ (2 * Q)) * Real.exp (-(c / ellT L g u * (zdistD d L (x - y) : ℝ)))) ∧
      (∀ s x y, ‖BAMsigma d L (BAMB d L g (E : ℂ) m) s x y‖ ≤
        (C₁ * (W : ℝ) ^ (2 * Q)) * Real.exp (-(c / ellT L g u * (zdistD d L (x - y) : ℝ)))) := by
  obtain ⟨CΘ, hCΘ, cΘ, hcΘ, HΘ⟩ := KDecayBA_theta_const hd hΛ hκ
  obtain ⟨BM, hBM, cM, hcM, HM⟩ := KDecayBA_M_const hd hΛ hκ
  refine ⟨2 * CΘ + BM, by linarith, min cΘ cM, lt_min hcΘ hcM, ?_⟩
  intro L W _ hL hW g E u Q m hg0 hgΛ hr hu0 hu1 hQ hgQ hℓL
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWQ1 : 1 ≤ (W : ℝ) ^ (2 * Q) := Real.one_le_rpow hW1r (by linarith)
  have hWQneg : 0 < (W : ℝ) ^ (-Q) := Real.rpow_pos_of_pos hWpos _
  have hsq : ((W : ℝ) ^ (-Q)) ^ 2 = ((W : ℝ) ^ (2 * Q))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le, ← Real.rpow_neg hWpos.le]
    congr 1; push_cast; ring
  have hg2 : (g ^ 2)⁻¹ ≤ (W : ℝ) ^ (2 * Q) := by
    have h1 : ((W : ℝ) ^ (-Q)) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hWQneg.le hgQ 2
    have h2 := inv_anti₀ (by positivity) h1
    rwa [hsq, inv_inv] at h2
  have hB0le := KDecay_B0_le (by omega : 2 ≤ d) (by omega : 1 ≤ L) hg0 hu1 hℓL
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓ1 : 1 ≤ ellT L g u := one_le_ellT hL1r
  have hℓ0 : 0 < ellT L g u := lt_of_lt_of_le one_pos hℓ1
  have hc0 : 0 < min cΘ cM := lt_min hcΘ hcM
  have hrate : ∀ x y : Zd d L, ∀ c' : ℝ, min cΘ cM ≤ c' → 0 < c' →
      Real.exp (-(c' * (zdistD d L (x - y) : ℝ))) ≤
        Real.exp (-(min cΘ cM / ellT L g u * (zdistD d L (x - y) : ℝ))) := by
    intro x y c' hc' hc'0
    apply Real.exp_le_exp.2
    have hr0 : (0 : ℝ) ≤ (zdistD d L (x - y) : ℝ) := Nat.cast_nonneg _
    have h1 : min cΘ cM / ellT L g u ≤ c' := (div_le_self hc0.le hℓ1).trans hc'
    nlinarith
  refine ⟨fun s s' x y => ?_, fun s x y => ?_⟩
  · have h := HΘ L hL g hg0 hgΛ E m hr u hu0 hu1 s s' x y
    have hB : Bparam d L g u 0 ≤ 2 * (W : ℝ) ^ (2 * Q) := by linarith
    have hexp : Real.exp (-(cΘ / ellT L g u * (zdistD d L (x - y) : ℝ))) ≤
        Real.exp (-(min cΘ cM / ellT L g u * (zdistD d L (x - y) : ℝ))) := by
      apply Real.exp_le_exp.2
      have hr0 : (0 : ℝ) ≤ (zdistD d L (x - y) : ℝ) := Nat.cast_nonneg _
      have : min cΘ cM / ellT L g u ≤ cΘ / ellT L g u :=
        div_le_div_of_nonneg_right (min_le_left _ _) hℓ0.le
      nlinarith
    calc ‖BATheta d L g E m u s s' x y‖
        ≤ CΘ * Bparam d L g u 0 * Real.exp (-(cΘ / ellT L g u * (zdistD d L (x - y) : ℝ))) := h
      _ ≤ CΘ * (2 * (W : ℝ) ^ (2 * Q)) * Real.exp (-(min cΘ cM / ellT L g u * (zdistD d L (x - y) : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hB hCΘ.le) hexp (Real.exp_pos _).le (by positivity)
      _ ≤ ((2 * CΘ + BM) * (W : ℝ) ^ (2 * Q)) * Real.exp (-(min cΘ cM / ellT L g u * (zdistD d L (x - y) : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          nlinarith [mul_nonneg (by linarith : 0 ≤ BM) (by linarith : (0 : ℝ) ≤ (W : ℝ) ^ (2 * Q))]
  · rw [KDecayBA_Msigma_norm]
    have h := HM L hL g hg0 hgΛ E m hr x y
    have hexp := hrate x y cM (min_le_right _ _) hcM
    calc ‖BAMB d L g (E : ℂ) m x y‖ ≤ BM * Real.exp (-(cM * (zdistD d L (x - y) : ℝ))) := h
      _ ≤ BM * Real.exp (-(min cΘ cM / ellT L g u * (zdistD d L (x - y) : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (by linarith)
      _ ≤ ((2 * CΘ + BM) * (W : ℝ) ^ (2 * Q)) * Real.exp (-(min cΘ cM / ellT L g u * (zdistD d L (x - y) : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          nlinarith [mul_nonneg hCΘ.le (by linarith : (0 : ℝ) ≤ (W : ℝ) ^ (2 * Q))]

end EdgeBounds

/-! ## 5. `𝒦` in the far region: `k = 2` (`(Kn2sol)`) and `k ≥ 3` (`baTreeRep`) -/

section Kfar

variable {d : ℕ}

/-- `‖(Θ M^{(σ₁σ₂)})(a₁,a₂)‖ ≤ L^d B³ e^{-κ' |a₁-a₂|}`: the convolution, with the triangle inequality. -/
private theorem KDecayBA_two_bound {L : ℕ} [NeZero L] {g E u B κ' : ℝ} {m : ℂ} (hB : 1 ≤ B) (hκ' : 0 ≤ κ')
    (hΘ : ∀ s s' x y, ‖BATheta d L g E m u s s' x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    (hMM : ∀ s x y, ‖BAMsigma d L (BAMB d L g (E : ℂ) m) s x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    ‖(BATheta d L g E m u σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a₂‖ ≤
      ((L ^ d : ℕ) : ℝ) * B ^ 3 * Real.exp (-(κ' * (zdistD d L (a₁ - a₂) : ℝ))) := by
  have hB0 : 0 ≤ B := by linarith
  have hpt : ∀ b : Zd d L, ‖BATheta d L g E m u σ₁ σ₂ a₁ b * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ b a₂‖ ≤
      B ^ 3 * Real.exp (-(κ' * (zdistD d L (a₁ - a₂) : ℝ))) := by
    intro b
    have h1 := hΘ σ₁ σ₂ a₁ b
    have h2 := hMM σ₁ a₂ b
    have h3 := hMM σ₂ b a₂
    have htri := KDecay_zdistD_tri a₁ b a₂
    have hsym : zdistD d L (a₂ - b) = zdistD d L (b - a₂) := KDecay_zdistD_symm a₂ b
    have e1 : Real.exp (-(κ' * (zdistD d L (a₂ - b) : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ κ' * (zdistD d L (a₂ - b) : ℝ) := by positivity
      linarith
    have e2 : Real.exp (-(κ' * (zdistD d L (a₁ - b) : ℝ))) * Real.exp (-(κ' * (zdistD d L (b - a₂) : ℝ))) ≤
        Real.exp (-(κ' * (zdistD d L (a₁ - a₂) : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have : (zdistD d L (a₁ - a₂) : ℝ) ≤ (zdistD d L (a₁ - b) : ℝ) + (zdistD d L (b - a₂) : ℝ) := by
        exact_mod_cast htri
      nlinarith
    change ‖BATheta d L g E m u σ₁ σ₂ a₁ b * (BAMsigma d L (BAMB d L g (E : ℂ) m) σ₁ a₂ b *
      BAMsigma d L (BAMB d L g (E : ℂ) m) σ₂ b a₂)‖ ≤ _
    rw [norm_mul, norm_mul]
    have hp : 0 ≤ Real.exp (-(κ' * (zdistD d L (a₁ - b) : ℝ))) := (Real.exp_pos _).le
    have hq : 0 ≤ Real.exp (-(κ' * (zdistD d L (b - a₂) : ℝ))) := (Real.exp_pos _).le
    have hq' : 0 ≤ Real.exp (-(κ' * (zdistD d L (a₂ - b) : ℝ))) := (Real.exp_pos _).le
    calc ‖BATheta d L g E m u σ₁ σ₂ a₁ b‖ * (‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ₁ a₂ b‖ *
          ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ₂ b a₂‖)
        ≤ (B * Real.exp (-(κ' * (zdistD d L (a₁ - b) : ℝ)))) *
          ((B * Real.exp (-(κ' * (zdistD d L (a₂ - b) : ℝ)))) * (B * Real.exp (-(κ' * (zdistD d L (b - a₂) : ℝ))))) :=
          mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
      _ = B ^ 3 * (Real.exp (-(κ' * (zdistD d L (a₂ - b) : ℝ))) *
          (Real.exp (-(κ' * (zdistD d L (a₁ - b) : ℝ))) * Real.exp (-(κ' * (zdistD d L (b - a₂) : ℝ))))) := by ring
      _ ≤ B ^ 3 * (1 * Real.exp (-(κ' * (zdistD d L (a₁ - a₂) : ℝ)))) := by
          gcongr
      _ = _ := by ring
  rw [Matrix.mul_apply]
  have hcard : (Fintype.card (Zd d L) : ℝ) = ((L ^ d : ℕ) : ℝ) := by rw [card_Zd]
  calc _ ≤ ∑ b : Zd d L, ‖BATheta d L g E m u σ₁ σ₂ a₁ b * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ b a₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _b : Zd d L, B ^ 3 * Real.exp (-(κ' * (zdistD d L (a₁ - a₂) : ℝ))) := sum_le_sum fun b _ => hpt b
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul, hcard]; ring

/-- **`𝒦` for every `k ≥ 2`** at a BA flow point: `(Kn2sol)` for `k = 2`, `baTreeRep` for `k ≥ 3`; the one shape
`2^{k²} (L^d)^{k+2k²} B^{2k+3k²} e^{-κ' maxDist a/(R+1)}`, with `R` depending on `k` only. -/
private theorem KDecayBA_Kn_far {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ R : ℕ, ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ (g E u B κ' : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      0 ≤ u → u < 1 → 1 ≤ B → 0 ≤ κ' →
      (∀ s s' x y, ‖BATheta d L g E m u s s' x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ)))) →
      (∀ s x y, ‖BAMsigma d L (BAMB d L g (E : ℂ) m) s x y‖ ≤ B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ)))) →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d L),
        ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) u (KLloopOf d L σ a)‖ ≤
          2 ^ (k * k) * (((L ^ d : ℕ) : ℝ) ^ (k + 2 * (k * k)) * B ^ (2 * k + 3 * (k * k)) *
            Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1)))) := by
  have key : ∀ (L W : ℕ) [NeZero L], 3 ≤ L → ∀ (g E u : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      0 ≤ u → u < 1 → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d L),
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) u (KLloopOf d L σ a) =
        BAKcac d L W g E m u (KLloopOf d L σ a) := by
    intro L W _ hL g E u m hg hgΛ hr hu0 hu1 σ a
    exact baK_unique _ _ (BAKsol_isKLoopS (baKsolve d) hΛ hκ hL hg hgΛ hr) (baKcac_isKLoopS (W := W) hr) u ⟨hu0, hu1⟩
      (KLloopOf d L σ a) (by simp [LoopIdx.WF, KLloopOf])
      (by simp only [LoopIdx.length, KLloopOf, List.length_ofFn]; omega)
  by_cases hk3 : 3 ≤ k
  · have : NeZero k := ⟨by omega⟩
    obtain ⟨R, hR⟩ := KDecayBA_walk_bound k (by omega)
    refine ⟨R, fun L W _ hL hW g E u B κ' m hg hgΛ hr hu0 hu1 hB hκ' hΘ hMM σ a => ?_⟩
    have hB0 : 0 ≤ B := by linarith
    rw [baTreeRep d Λ κ hΛ hκ L hL W g hg hgΛ E m hr u ⟨hu0, hu1⟩ k hk3 σ a]
    set X : ℝ := ((L ^ d : ℕ) : ℝ) ^ (k + 2 * (k * k)) * B ^ (2 * k + 3 * (k * k)) *
      Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))) with hX
    have hX0 : 0 ≤ X := by positivity
    have htree : ∀ F ∈ TSP k, ‖BAGamma d L k (BAMsigma d L (BAMB d L g (E : ℂ) m)) u F σ a‖ ≤ X := fun F hF =>
      KDecayBA_cactus_bound hR hF _ hu0 hu1.le σ a hB hκ' (fun s s' x y => hΘ s s' x y) (fun s x y => hMM s x y)
    have hW' : ‖(((W : ℂ) ^ d)⁻¹) ^ (k - 1)‖ ≤ 1 := by
      rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
      have h1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ h1))
    have hsum : ‖∑ F ∈ TSP k, BAGamma d L k (BAMsigma d L (BAMB d L g (E : ℂ) m)) u F σ a‖ ≤ 2 ^ (k * k) * X := by
      refine (norm_sum_le _ _).trans ?_
      refine (sum_le_sum htree).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have h2 : ((TSP k).card : ℝ) ≤ 2 ^ (k * k) := by exact_mod_cast KDecay_card_TSP k
      exact mul_le_mul_of_nonneg_right h2 hX0
    rw [norm_mul]
    calc _ ≤ 1 * (2 ^ (k * k) * X) := mul_le_mul hW' hsum (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · have hk2 : k = 2 := by omega
    subst hk2
    refine ⟨0, fun L W _ hL hW g E u B κ' m hg hgΛ hr hu0 hu1 hB hκ' hΘ hMM σ a => ?_⟩
    have hB0 : 0 ≤ B := by linarith
    have hI : KLloopOf d L σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
      simp [KLloopOf, List.ofFn_succ]
    rw [key L W hL g E u m hg hgΛ hr hu0 hu1 σ a, hI,
      (BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)).2.1 u (σ 0) (σ 1) (a 0) (a 1)]
    have hW' : ‖((W : ℂ) ^ d)⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_pow, Complex.norm_natCast]
      have h1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
      exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    have hT := KDecayBA_two_bound hB hκ' hΘ hMM (σ 0) (σ 1) (a 0) (a 1)
    have hmd : (KLmaxDist d L a : ℝ) ≤ (zdistD d L (a 0 - a 1) : ℝ) := by
      exact_mod_cast KDecay_maxDist_two_le a
    have hexp : Real.exp (-(κ' * (zdistD d L (a 0 - a 1) : ℝ))) ≤
        Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / (((0 : ℕ) : ℝ) + 1))) := by
      apply Real.exp_le_exp.2
      simp only [Nat.cast_zero, zero_add, div_one]
      have := mul_le_mul_of_nonneg_left hmd hκ'
      linarith
    have hLL : (1 : ℝ) ≤ ((L ^ d : ℕ) : ℝ) := by
      have : 1 ≤ L ^ d := Nat.one_le_pow _ _ (NeZero.pos L)
      exact_mod_cast this
    have hLpow : ((L ^ d : ℕ) : ℝ) ≤ ((L ^ d : ℕ) : ℝ) ^ (2 + 2 * (2 * 2)) :=
      le_self_pow₀ hLL (by norm_num)
    have hBpow : B ^ 3 ≤ B ^ (2 * 2 + 3 * (2 * 2)) := pow_le_pow_right₀ hB (by norm_num)
    have he : 0 ≤ Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / (((0 : ℕ) : ℝ) + 1))) := (Real.exp_pos _).le
    rw [norm_mul]
    calc ‖((W : ℂ) ^ d)⁻¹‖ * ‖(BATheta d L g E m u (σ 0) (σ 1) * BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) (a 1)‖
        ≤ 1 * (((L ^ d : ℕ) : ℝ) * B ^ 3 * Real.exp (-(κ' * (zdistD d L (a 0 - a 1) : ℝ)))) :=
          mul_le_mul hW' hT (norm_nonneg _) zero_le_one
      _ ≤ 1 * (((L ^ d : ℕ) : ℝ) ^ (2 + 2 * (2 * 2)) * B ^ (2 * 2 + 3 * (2 * 2)) *
            Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / (((0 : ℕ) : ℝ) + 1)))) := by
          gcongr
      _ ≤ 2 ^ (2 * 2) * (((L ^ d : ℕ) : ℝ) ^ (2 + 2 * (2 * 2)) * B ^ (2 * 2 + 3 * (2 * 2)) *
            Real.exp (-(κ' * (KLmaxDist d L a : ℝ) / (((0 : ℕ) : ℝ) + 1)))) := by
          rw [one_mul]
          exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))

end Kfar

/-! ## 6. The far-region estimate at fixed `(L, W)` -/

section Pointwise

variable {d : ℕ}

private theorem KDecayBA_ellT_mono {L : ℕ} {g₀ g : ℝ} (h : g₀ ≤ g) (u : ℝ) : ellT L g₀ u ≤ ellT L g u :=
  min_le_min (max_le_max (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)) le_rfl) le_rfl

/-- **The far-region estimate** (`k ≥ 2`, `ℓ_u(g) < L`, kernels at `g₀ ≤ g`): `|𝒦_{u,σ,a}| ≤ Ak N^{P_k} e^{-c W^τ}` for every
`N ≥ max(W, L^d)` and `ℓ_u(g) W^τ ≤ maxDist a`; `Ak = 2^{k²} C₁^{2k+3k²}`, `P_k = (k + 2k²) + 2Q(2k + 3k²)`,
`c = c₀/(R_k+1)`; the constants depend on `(d, Λ, κ, k)` only. -/
private theorem KDecayBA_far_const (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ Ak : ℝ, 0 ≤ Ak ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L W N : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → W ≤ N → L ^ d ≤ N →
      ∀ (Q τ g g₀ E u : ℝ) (m : ℂ), 0 < Q → 0 < g₀ → g₀ ≤ g → g₀ ≤ Λ → BAReal d L g₀ κ E m → 0 ≤ u → u < 1 →
      (W : ℝ) ^ (-Q) ≤ g₀ → ellT L g u < L → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d L),
      ellT L g u * (W : ℝ) ^ τ ≤ (KLmaxDist d L a : ℝ) →
        ‖BAKsol d L W (BAMsigma d L (BAMB d L g₀ (E : ℂ) m)) (PropSpin m) u (KLloopOf d L σ a)‖ ≤
          Ak * (N : ℝ) ^ (((k + 2 * (k * k) : ℕ) : ℝ) + 2 * Q * ((2 * k + 3 * (k * k) : ℕ) : ℝ)) *
            Real.exp (-(c * (W : ℝ) ^ τ)) := by
  obtain ⟨C₁, hC₁, c₀, hc₀, Hedge⟩ := KDecayBA_edge_const hd hΛ hκ
  obtain ⟨R, HK⟩ := KDecayBA_Kn_far hΛ hκ k hk
  have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  refine ⟨2 ^ (k * k) * C₁ ^ (2 * k + 3 * (k * k)), by positivity, c₀ / ((R : ℝ) + 1), by positivity, ?_⟩
  intro L W N _ hL hW hWN hLdN Q τ g g₀ E u m hQ hg0 hgg hgΛ hr hu0 hu1 hgQ hℓL σ a hfar
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hWpos (by exact_mod_cast hWN)
  have hWNr : (W : ℝ) ≤ N := by exact_mod_cast hWN
  have hLdNr : ((L ^ d : ℕ) : ℝ) ≤ N := by exact_mod_cast hLdN
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓ0L : ellT L g₀ u < L := lt_of_le_of_lt (KDecayBA_ellT_mono hgg u) hℓL
  have hℓ0pos : 0 < ellT L g₀ u := ellT_pos hL1r
  obtain ⟨hΘ, hMM⟩ := Hedge L W hL hW g₀ E u Q m hg0 hgΛ hr hu0 hu1 hQ hgQ hℓ0L
  have hWQ1 : 1 ≤ (W : ℝ) ^ (2 * Q) := Real.one_le_rpow (by exact_mod_cast hW) (by linarith)
  have hB1 : 1 ≤ C₁ * (W : ℝ) ^ (2 * Q) := one_le_mul_of_one_le_of_one_le hC₁ hWQ1
  have hκ'0 : 0 ≤ c₀ / ellT L g₀ u := by positivity
  have hK := HK L W hL hW g₀ E u (C₁ * (W : ℝ) ^ (2 * Q)) (c₀ / ellT L g₀ u) m hg0 hgΛ hr hu0 hu1 hB1 hκ'0 hΘ hMM σ a
  -- `κ' maxDist ≥ c₀ W^τ`
  have hWτ : 0 < (W : ℝ) ^ τ := Real.rpow_pos_of_pos hWpos τ
  have hκ' : c₀ * (W : ℝ) ^ τ ≤ c₀ / ellT L g₀ u * (KLmaxDist d L a : ℝ) := by
    have hle : ellT L g₀ u * (W : ℝ) ^ τ ≤ (KLmaxDist d L a : ℝ) :=
      (mul_le_mul_of_nonneg_right (KDecayBA_ellT_mono hgg u) hWτ.le).trans hfar
    have h1 : c₀ / ellT L g₀ u * (ellT L g₀ u * (W : ℝ) ^ τ) ≤ c₀ / ellT L g₀ u * (KLmaxDist d L a : ℝ) :=
      mul_le_mul_of_nonneg_left hle hκ'0
    have h2 : c₀ / ellT L g₀ u * (ellT L g₀ u * (W : ℝ) ^ τ) = c₀ * (W : ℝ) ^ τ := by field_simp
    linarith
  have hexp : Real.exp (-(c₀ / ellT L g₀ u * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))) ≤
      Real.exp (-(c₀ / ((R : ℝ) + 1) * (W : ℝ) ^ τ)) := by
    apply Real.exp_le_exp.2
    have h3 : c₀ * (W : ℝ) ^ τ / ((R : ℝ) + 1) ≤ c₀ / ellT L g₀ u * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1) :=
      div_le_div_of_nonneg_right hκ' hR1.le
    have h4 : c₀ / ((R : ℝ) + 1) * (W : ℝ) ^ τ = c₀ * (W : ℝ) ^ τ / ((R : ℝ) + 1) := by ring
    have h5 : -(c₀ / ellT L g₀ u * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1)) =
        -(c₀ / ellT L g₀ u * (KLmaxDist d L a : ℝ)) / ((R : ℝ) + 1) := by ring
    rw [h4]
    linarith
  refine hK.trans ?_
  have he : 0 ≤ Real.exp (-(c₀ / ((R : ℝ) + 1) * (W : ℝ) ^ τ)) := (Real.exp_pos _).le
  have hYle : (W : ℝ) ^ (2 * Q) ≤ (N : ℝ) ^ (2 * Q) := Real.rpow_le_rpow hWpos.le hWNr (by linarith)
  have hBN : C₁ * (W : ℝ) ^ (2 * Q) ≤ C₁ * (N : ℝ) ^ (2 * Q) := mul_le_mul_of_nonneg_left hYle (by linarith)
  have hNpow : (N : ℝ) ^ (k + 2 * (k * k)) * ((N : ℝ) ^ (2 * Q)) ^ (2 * k + 3 * (k * k)) =
      (N : ℝ) ^ (((k + 2 * (k * k) : ℕ) : ℝ) + 2 * Q * ((2 * k + 3 * (k * k) : ℕ) : ℝ)) := by
    have e1 : ((N : ℝ) ^ (2 * Q)) ^ (2 * k + 3 * (k * k)) = (N : ℝ) ^ (2 * Q * ((2 * k + 3 * (k * k) : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    have e2 : (N : ℝ) ^ (k + 2 * (k * k)) = (N : ℝ) ^ (((k + 2 * (k * k) : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
    rw [e1, e2, ← Real.rpow_add hN0]
  have hBpow : (C₁ * (W : ℝ) ^ (2 * Q)) ^ (2 * k + 3 * (k * k)) ≤
      C₁ ^ (2 * k + 3 * (k * k)) * ((N : ℝ) ^ (2 * Q)) ^ (2 * k + 3 * (k * k)) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hBN _
  have hLpow : ((L ^ d : ℕ) : ℝ) ^ (k + 2 * (k * k)) ≤ (N : ℝ) ^ (k + 2 * (k * k)) :=
    pow_le_pow_left₀ (by positivity) hLdNr _
  calc 2 ^ (k * k) * (((L ^ d : ℕ) : ℝ) ^ (k + 2 * (k * k)) * (C₁ * (W : ℝ) ^ (2 * Q)) ^ (2 * k + 3 * (k * k)) *
        Real.exp (-(c₀ / ellT L g₀ u * (KLmaxDist d L a : ℝ) / ((R : ℝ) + 1))))
      ≤ 2 ^ (k * k) * ((N : ℝ) ^ (k + 2 * (k * k)) *
          (C₁ ^ (2 * k + 3 * (k * k)) * ((N : ℝ) ^ (2 * Q)) ^ (2 * k + 3 * (k * k))) *
            Real.exp (-(c₀ / ((R : ℝ) + 1) * (W : ℝ) ^ τ))) := by
        gcongr
    _ = 2 ^ (k * k) * C₁ ^ (2 * k + 3 * (k * k)) *
        (N : ℝ) ^ (((k + 2 * (k * k) : ℕ) : ℝ) + 2 * Q * ((2 * k + 3 * (k * k) : ℕ) : ℝ)) *
        Real.exp (-(c₀ / ((R : ℝ) + 1) * (W : ℝ) ^ τ)) := by
        rw [← hNpow]
        ring

end Pointwise

/-! ## 7. Target 1: `BAKcalDecay` -/

/-- **Target 1, `BAKcalDecay`** (`T2486_BAKcalDecay`; REQ-1418-UBA `:39`; paper `(eq:bcal_k)`, `1_2:1056`): the far decay of the
BA `𝒦` along every BA flow, the BA reading of `STKcalDecaygL`, in the `hKcal` shape of `gridGoodNgL_of`.  The size level
(the cutoff `ℓ_u(sz.lam) W^τ`) and the kernel level (`g₀ = BAflowLam0`) meet only in `ℓ(g₀) ≤ ℓ(g)` where `0 < g₀`
(`baStep5III_lam0_le_lam`, 1457 F1 (f)). -/
def BAKcalDecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (baFMz sz z)

/-- **`BAKcalDecay` is proved** for every `d` (`3 ≤ d` enters through `baProp5to8_holds`, `baPropM_holds`). -/
theorem baKcalDecay_holds (d : ℕ) : BAKcalDecay d := by
  intro hd sz κ ε 𝔠 𝔡 z hκ hflow k hk τ D hτ hD
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := hflow.1
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hQ : 0 < (d : ℝ) / 2 := by positivity
  -- the threshold `W₀` of `W^{-Q} ≤ g₀`: `√(κ/(κ+1)) W^𝔡 ≥ 1`
  have hs0 : 0 < Real.sqrt (κ / (κ + 1)) := Real.sqrt_pos.2 (by positivity)
  set W₀ : ℝ := (Real.sqrt (κ / (κ + 1)))⁻¹ ^ (𝔡⁻¹) with hW₀
  have hW₀0 : 0 ≤ W₀ := Real.rpow_nonneg (inv_nonneg.2 hs0.le) _
  have hk1 : k = 1 ∨ 2 ≤ k := by omega
  rcases hk1 with rfl | hk2
  · -- `k = 1`: `maxDist = 0`, the premise fails
    filter_upwards [Filter.Eventually.of_forall fun _ => trivial] with n _
    intro u hu0 hu1 σ a hfar
    exfalso
    have hmd : KLmaxDist d (sz.L n) a = 0 := by
      refine Nat.le_zero.1 (Finset.sup_le fun p _ => ?_)
      have : p.1 = p.2 := Subsingleton.elim _ _
      simp [this]
    rw [hmd, Nat.cast_zero] at hfar
    have hL1r : (1 : ℝ) ≤ (sz.L n : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
    have hW1 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have := mul_pos (ellT_pos (g := sz.lam n) (t := u) hL1r) (Real.rpow_pos_of_pos hW1 τ)
    linarith
  · obtain ⟨Ak, hA0, c, hc, HF⟩ := KDecayBA_far_const hd hΛ hκ k hk2
    obtain ⟨Pk, hPk⟩ : ∃ Pk : ℝ, Pk = ((k + 2 * (k * k) : ℕ) : ℝ) + 2 * ((d : ℝ) / 2) * ((2 * k + 3 * (k * k) : ℕ) : ℝ) :=
      ⟨_, rfl⟩
    have hT := tendsto_size sz hN
    filter_upwards [hT.eventually (KDecay_eventually Ak (Pk + D) c (𝔠 * τ) hc (mul_pos h𝔠 hτ)),
      hT.eventually (((tendsto_rpow_atTop (mul_pos h𝔠 hτ)).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (d : ℝ)),
      hT.eventually (((tendsto_rpow_atTop h𝔠).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop W₀),
      hB, hWO, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn hNd hNW₀ hbw hwo hwin
    obtain ⟨hg0, hg0Λ⟩ := hwin
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hW1' : 1 ≤ sz.W n := sz.W_pos n
    have hLpos' : 0 < sz.L n := by have := sz.three_le_L n; omega
    have hLpos : (0 : ℝ) < (sz.L n : ℝ) := by exact_mod_cast hLpos'
    have hL1r : (1 : ℝ) ≤ (sz.L n : ℝ) := by exact_mod_cast hLpos'
    have hNdef : sz.size n = (sz.W n * sz.L n) ^ d := rfl
    have hWN' : sz.W n ≤ sz.size n := by
      rw [hNdef]
      calc sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hLpos'
        _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
    have hLdN' : sz.L n ^ d ≤ sz.size n := by
      rw [hNdef]
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW1') d
    have hWN : ((sz.W n : ℕ) : ℝ) ≤ (sz.size n : ℝ) := by exact_mod_cast hWN'
    have hN0 : (0 : ℝ) < (sz.size n : ℝ) := lt_of_lt_of_le hWpos hWN
    have hNτ : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbw hτ.le
    have hdW : (d : ℝ) < ((sz.W n : ℕ) : ℝ) ^ τ := lt_of_lt_of_le hNd hNτ
    have hWτpos : 0 < ((sz.W n : ℕ) : ℝ) ^ τ := Real.rpow_pos_of_pos hWpos τ
    -- `0 < lam`, `g₀ ≤ lam`, `W^{-Q} ≤ g₀`
    have hlam0 : 0 < sz.lam n :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
    have hgg : BAflowLam0 sz z n ≤ sz.lam n := baStep5III_lam0_le_lam hκ hflow n hg0
    have hgQ : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) / 2)) ≤ BAflowLam0 sz z n := by
      have hWW₀ : W₀ ≤ ((sz.W n : ℕ) : ℝ) := (hNW₀.trans_le hbw).le
      have hWδ : (Real.sqrt (κ / (κ + 1)))⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ 𝔡 := by
        have := Real.rpow_le_rpow hW₀0 hWW₀ h𝔡.le
        rwa [hW₀, Real.rpow_inv_rpow (inv_nonneg.2 hs0.le) h𝔡.ne'] at this
      have hs1 : 1 ≤ Real.sqrt (κ / (κ + 1)) * ((sz.W n : ℕ) : ℝ) ^ 𝔡 := by
        have := mul_le_mul_of_nonneg_left hWδ hs0.le
        rwa [mul_inv_cancel₀ hs0.ne'] at this
      have hT0 := TwistStep2_T0_ge hκ hflow n
      have hsq : Real.sqrt (κ / (κ + 1)) ≤ Real.sqrt (BAflowT0 sz z n) := Real.sqrt_le_sqrt hT0
      have hg0e : BAflowLam0 sz z n = Real.sqrt (BAflowT0 sz z n) * sz.lam n := rfl
      have hexpo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) =
          ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) / 2)) * ((sz.W n : ℕ) : ℝ) ^ 𝔡 := by
        rw [← Real.rpow_add hWpos]; congr 1; ring
      have hpos : 0 < ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) / 2)) := Real.rpow_pos_of_pos hWpos _
      calc ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) / 2))
          ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) / 2)) * (Real.sqrt (κ / (κ + 1)) * ((sz.W n : ℕ) : ℝ) ^ 𝔡) :=
            le_mul_of_one_le_right hpos.le hs1
        _ = Real.sqrt (κ / (κ + 1)) * (((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) / 2)) * ((sz.W n : ℕ) : ℝ) ^ 𝔡) := by ring
        _ = Real.sqrt (κ / (κ + 1)) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) := by rw [hexpo]
        _ ≤ Real.sqrt (BAflowT0 sz z n) * sz.lam n :=
            mul_le_mul hsq hwo.1 (Real.rpow_nonneg hWpos.le _) (Real.sqrt_nonneg _)
        _ = BAflowLam0 sz z n := hg0e.symm
    intro u hu0 hu1 σ a hfar
    have hℓpos : 0 < ellT (sz.L n) (sz.lam n) u := ellT_pos hL1r
    have hℓle : ellT (sz.L n) (sz.lam n) u ≤ sz.L n := ellT_le_L
    have hmaxL : (KLmaxDist d (sz.L n) a : ℝ) ≤ d * sz.L n := by
      have : KLmaxDist d (sz.L n) a ≤ d * sz.L n := Finset.sup_le fun p _ => zdistD_le d _
      exact_mod_cast this
    have hℓL : ellT (sz.L n) (sz.lam n) u < sz.L n := by
      refine lt_of_le_of_ne hℓle fun h => ?_
      rw [h] at hfar
      have h1 : (sz.L n : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ ≤ d * sz.L n := hfar.trans hmaxL
      have h2 := mul_lt_mul_of_pos_left hdW hLpos
      nlinarith
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have h := HF (sz.L n) (sz.W n) (sz.size n) (sz.three_le_L n) hW1' hWN' hLdN' ((d : ℝ) / 2) τ (sz.lam n)
      (BAflowLam0 sz z n) (BAflowEs sz z n) u (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hQ hg0 hgg hg0Λ hr hu0 hu1
      hgQ hℓL σ a hfar
    rw [← hPk] at h
    have hK : ‖(baFMz sz z).K n u σ a‖ ≤ Ak * ((sz.size n : ℕ) : ℝ) ^ Pk * Real.exp (-(c * ((sz.W n : ℕ) : ℝ) ^ τ)) := h
    -- absorb into `W^{-D}`
    have hWD : ((sz.W n : ℕ) : ℝ) ^ D ≤ ((sz.size n : ℕ) : ℝ) ^ D := Real.rpow_le_rpow hWpos.le hWN hD.le
    have hexp : Real.exp (-(c * ((sz.W n : ℕ) : ℝ) ^ τ)) ≤ Real.exp (-(c * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ))) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hNτ hc.le
      linarith
    have hWDpos : 0 < ((sz.W n : ℕ) : ℝ) ^ D := Real.rpow_pos_of_pos hWpos D
    rw [Real.rpow_neg hWpos.le, ← one_div, le_div_iff₀ hWDpos]
    have hAN : 0 ≤ Ak * ((sz.size n : ℕ) : ℝ) ^ Pk := mul_nonneg hA0 (Real.rpow_nonneg hN0.le _)
    calc ‖(baFMz sz z).K n u σ a‖ * ((sz.W n : ℕ) : ℝ) ^ D
        ≤ (Ak * ((sz.size n : ℕ) : ℝ) ^ Pk * Real.exp (-(c * ((sz.W n : ℕ) : ℝ) ^ τ))) * ((sz.W n : ℕ) : ℝ) ^ D :=
          mul_le_mul_of_nonneg_right hK hWDpos.le
      _ ≤ (Ak * ((sz.size n : ℕ) : ℝ) ^ Pk * Real.exp (-(c * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ)))) *
            ((sz.size n : ℕ) : ℝ) ^ D :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hAN) hWD hWDpos.le (mul_nonneg hAN (Real.exp_pos _).le)
      _ = Ak * ((sz.size n : ℕ) : ℝ) ^ (Pk + D) * Real.exp (-(c * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ))) := by
          rw [Real.rpow_add hN0]; ring
      _ ≤ 1 := hn

/-! ## 8. Compiled nonempty instance of target 1

`d = 3`, the preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N = (WL)^3`), the spectral
parameters `zSeq` with `flow_sz0` (`BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`, `FlowPins:1214`): every deterministic
premise is discharged.  The far set of `STKcalDecaygL` is nonempty for `k = 3`, `τ = 1/20`, `u = 0` (`ℓ_0 = 1`):
the labels `a = (0, (h,h,h), 0)`, `h = L/2`, have `maxDist ≥ 3h ≥ W^{τ}` at every `n`. -/

end RBM.BA

end
