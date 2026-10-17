/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLTree
import RBM3D.Loop.KLIndStepA
import RBM3D.Loop.KLFinal
import RBM3D.Defs.Tail
import RBM3D.Defs.RadialSum
import RBM3D.Defs.Params
import RBM3D.Induction.Defs
import RBM3D.Induction.Step34Pins
import RBM3D.Green.Pins

/-!
# Far-label decay of the primitive loop `𝒦` and the lattice sum of the tail `𝒯_t`

The fast decay of the primitive loop `𝒦` at far labels (`STKcalDecay`), the uniform-in-time forms of
`STKbound`/`STKward` over `TimeIcc`, and the lattice sum of the tail `𝒯_t` that enters (4.16)
`eq:sumtwoloop`.

Paper: (2.58) `eq:bcal_k` in Lemma 2.16 (`ML:Kbound`), Lemma 4.2 (`lem_wardineq_K`), and (4.16)
`eq:sumtwoloop` in the proof of Lemma 4.3 (`lem:SEforLn`); the tree representation of `𝒦` is
(A.30) `eq_Ktree`, and the case of two vertices is (2.71) `Kn2sol`.  The tree sums follow the
two-dimensional formalization (RBM2D's `kcalDecay_tree_bound` and the lemmas around it), here on `Zd d L`
with the distance `zdistD`.

* Sections 1-3 (private, `RBM.Loop`): the path bound (two vertices of a tree are at distance at most
  its total edge length) and the crude tree bound, on the laminar vocabulary `KLnodes`, `KLnodePar`,
  `KLleafPar`, `KLtreeValW`.
* Sections 4-6 (private): the edge kernels from the propagator properties 5 and 5' (`KLPT_holds`:
  `KLDecay`, `KLShort`; `d`-dimensional, with `ℓ_u = ellT L g u` and `B_{u,r}`), the tree sums for
  `k ≥ 3` and `k = 2`, the far-region estimate under `W^{-Q} ≤ g`, and the absorption
  `A N^P e^{-c N^s} ≤ 1`.
* Section 7: `STKcalDecay d` and `stKcalDecay_holds (hd : 3 ≤ d) : STKcalDecay d`.
* Section 8: `inst_stKcalDecay_admissible`, the form of `stKcalDecay_holds` for an admissible size
  sequence.
* Section 9: `stKbound_timeIcc`, `stKward_timeIcc`: `STKbound`, `STKward` with the time
  `u ∈ [s_n,t_n]` inside the `≺`.
* Section 10: `KDecay_tailC`, `KDecay_one_le_tailC`, `KDecay_sum_tailT_le` (the lattice sum
  `Σ_a 𝒯_t(|a|_∞) ≤ C_∞(d)/(1-t)`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Loop

open Finset

/-! ## 1. Distances on `Z_L^d` -/

section Dist

variable {d L : ℕ} [NeZero L]

private theorem KDecay_zdistD_symm (x y : Zd d L) : zdistD d L (x - y) = zdistD d L (y - x) := by
  rw [← zdistD_neg, neg_sub]

private theorem KDecay_zdistD_tri (x y z : Zd d L) :
    zdistD d L (x - z) ≤ zdistD d L (x - y) + zdistD d L (y - z) := by
  have := zdistD_add_le d L (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

end Dist

/-! ## 2. The path bound: two vertices of a tree are at distance at most its total edge length -/

section Path

variable {n d : ℕ} [NeZero n] {L : ℕ} [NeZero L]

/-- The edge length above the node `e`. -/
private def KDecay_elen (F : Finset (Fin n × Fin n)) (β : Fin n × Fin n → Zd d L)
    (e : Fin n × Fin n) : ℕ :=
  zdistD d L (β e - β (KLnodePar F e))

/-- The edges on the path between the nodes `x` and `y`: those above exactly one of them. -/
private def KDecay_pathSet (F : Finset (Fin n × Fin n)) (x y : Fin n × Fin n) :
    Finset (Fin n × Fin n) :=
  F.filter fun e => ¬(KLArcLe x e ↔ KLArcLe y e)

private theorem KDecay_anc_step {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    {x : Fin n × Fin n} (hx : x ∈ KLnodes F) (hxw : x ≠ KLwholeP n) :
    KLnodePar F x ∈ KLnodes F ∧ KLArcLe x (KLnodePar F x) ∧ ¬KLArcLe (KLnodePar F x) x ∧ x ∈ F ∧
      (F.filter (KLArcLe (KLnodePar F x))).card < (F.filter (KLArcLe x)).card ∧
      ∀ e ∈ F, e ≠ x → (KLArcLe x e ↔ KLArcLe (KLnodePar F x) e) := by
  have hxF : x ∈ F := (mem_insert.1 hx).resolve_left hxw
  obtain ⟨hp, hdp, hne, hmin⟩ := KLnodePar_spec hF hn hx hxw
  have hpd : ¬KLArcLe (KLnodePar F x) x := fun h => hne (KLArcLe.antisymm hdp h).symm
  have hsub : F.filter (KLArcLe (KLnodePar F x)) ⊆ (F.filter (KLArcLe x)).erase x := by
    intro e he
    obtain ⟨heF, hpe⟩ := mem_filter.1 he
    refine mem_erase.2 ⟨?_, mem_filter.2 ⟨heF, KLArcLe.trans hdp hpe⟩⟩
    rintro rfl
    exact hpd hpe
  have hxmem : x ∈ F.filter (KLArcLe x) := mem_filter.2 ⟨hxF, le_rfl, le_rfl⟩
  have hcard : (F.filter (KLArcLe (KLnodePar F x))).card < (F.filter (KLArcLe x)).card := by
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hxmem] at h1
    have := card_pos.2 ⟨x, hxmem⟩
    omega
  exact ⟨hp, hdp, hpd, hxF, hcard, fun e he hex =>
    ⟨fun h => hmin e (KLmem_nodes_of_mem he) h hex, fun h => KLArcLe.trans hdp h⟩⟩

private theorem KDecay_path_aux {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → Zd d L) :
    ∀ k : ℕ, ∀ x ∈ KLnodes F, ∀ y ∈ KLnodes F,
      (F.filter (KLArcLe x)).card + (F.filter (KLArcLe y)).card = k →
      zdistD d L (β x - β y) ≤ ∑ e ∈ KDecay_pathSet F x y, KDecay_elen F β e := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have key : ∀ x ∈ KLnodes F, ∀ y ∈ KLnodes F,
        (F.filter (KLArcLe x)).card + (F.filter (KLArcLe y)).card = k → x ≠ KLwholeP n →
          ¬KLArcLe y x → zdistD d L (β x - β y) ≤ ∑ e ∈ KDecay_pathSet F x y, KDecay_elen F β e := by
      intro x hx y hy hk hxw hyx
      obtain ⟨hp, hdp, hpd, hxF, hcard, hiff⟩ := KDecay_anc_step hF hn hx hxw
      have hih := ih _ (by omega) (KLnodePar F x) hp y hy rfl
      have htri := KDecay_zdistD_tri (β x) (β (KLnodePar F x)) (β y)
      have hxn : x ∉ KDecay_pathSet F (KLnodePar F x) y := by
        intro h
        exact (mem_filter.1 h).2 ⟨fun h' => absurd h' hpd, fun h' => absurd h' hyx⟩
      have hsub : insert x (KDecay_pathSet F (KLnodePar F x) y) ⊆ KDecay_pathSet F x y := by
        intro e he
        rcases mem_insert.1 he with rfl | he
        · exact mem_filter.2 ⟨hxF, fun h => hyx (h.1 ⟨le_rfl, le_rfl⟩)⟩
        · obtain ⟨heF, hne⟩ := mem_filter.1 he
          have hex : e ≠ x := by
            rintro rfl; exact hxn he
          exact mem_filter.2 ⟨heF, fun h => hne ((hiff e heF hex).symm.trans h)⟩
      have hs := sum_le_sum_of_subset (f := KDecay_elen F β) hsub
      rw [sum_insert hxn] at hs
      have : KDecay_elen F β x = zdistD d L (β x - β (KLnodePar F x)) := rfl
      omega
    intro x hx y hy hk
    by_cases h1 : x ≠ KLwholeP n ∧ ¬KLArcLe y x
    · exact key x hx y hy hk h1.1 h1.2
    by_cases h2 : y ≠ KLwholeP n ∧ ¬KLArcLe x y
    · have := key y hy x hx (by omega) h2.1 h2.2
      have hs : KDecay_pathSet F y x = KDecay_pathSet F x y := by
        ext e; simp only [KDecay_pathSet, mem_filter, iff_comm]
      rw [hs] at this
      rwa [KDecay_zdistD_symm]
    · have hyx : KLArcLe y x := by
        by_contra hc
        exact h1 ⟨fun hxw => hc (hxw ▸ KLarcLe_wholeP y), hc⟩
      have hxy : KLArcLe x y := by
        by_contra hc
        exact h2 ⟨fun hyw => hc (hyw ▸ KLarcLe_wholeP x), hc⟩
      have := KLArcLe.antisymm hxy hyx
      subst this
      simp

/-- Any two nodes of the tree are at distance at most the total length of the internal edges. -/
private theorem KDecay_path_le {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → Zd d L) {x y : Fin n × Fin n} (hx : x ∈ KLnodes F) (hy : y ∈ KLnodes F) :
    zdistD d L (β x - β y) ≤ ∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) :=
  (KDecay_path_aux hF hn β _ x hx y hy rfl).trans (sum_le_sum_of_subset (filter_subset _ _))

/-- **Pointwise part of the tree bound.**  With `D` the total edge length of the labelling `β`
(leaf edges plus internal edges), any two leaves are at distance at most `D`. -/
private theorem KDecay_dist_bounds {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (a : Fin n → Zd d L) (β : Fin n × Fin n → Zd d L) (i : Fin n) :
    ∀ j, zdistD d L (a i - a j) ≤
      (∑ v, zdistD d L (a v - β (KLleafPar F v)) +
        ∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e))) := by
  set Ls := ∑ v, zdistD d L (a v - β (KLleafPar F v))
  set Es := ∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e))
  intro j
  by_cases hij : i = j
  · subst hij; simp
  · have hpair : zdistD d L (a i - β (KLleafPar F i)) + zdistD d L (a j - β (KLleafPar F j))
        ≤ Ls := by
      have := sum_le_sum_of_subset (f := fun v => zdistD d L (a v - β (KLleafPar F v)))
        (show ({i, j} : Finset (Fin n)) ⊆ univ from subset_univ _)
      rwa [sum_pair hij] at this
    have h1 := KDecay_zdistD_tri (a i) (β (KLleafPar F i)) (a j)
    have h2 := KDecay_zdistD_tri (β (KLleafPar F i)) (β (KLleafPar F j)) (a j)
    have h3 := KDecay_path_le hF hn β (KLleafPar_mem F i) (KLleafPar_mem F j)
    have h4 : zdistD d L (β (KLleafPar F j) - a j) = zdistD d L (a j - β (KLleafPar F j)) :=
      KDecay_zdistD_symm _ _
    omega

end Path

/-! ## 3. A tree with exponentially decaying edges decays

Crude count of the internal labels: there are `(L^d)^{|nodes F|}` of them, and the summand is
bounded by `B^{n + |F|} e^{-κ D}`, `D` the total edge length, which dominates `maxDist a`
(`KDecay_dist_bounds`).  The polynomial loss `(L^d)^{n²}` is absorbed at the end. -/

section TreeBound

variable {n d : ℕ} [NeZero n] {L : ℕ} [NeZero L]

private theorem KDecay_tree_bound {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (a : Fin n → Zd d L) (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) {B κ : ℝ} (hB : 1 ≤ B) (hκ : 0 ≤ κ)
    (hM : ∀ v x y, ‖M v x y‖ ≤ B * Real.exp (-(κ * (zdistD d L (x - y) : ℝ))))
    (hE : ∀ J x y, ‖E J x y‖ ≤ B * Real.exp (-(κ * (zdistD d L (x - y) : ℝ)))) :
    ‖KLtreeValW d L F a M E‖ ≤ ((L ^ d : ℕ) : ℝ) ^ (n * n) * B ^ (n + n * n) *
        Real.exp (-(κ * (KLmaxDist d L a : ℝ))) := by
  have hB0 : 0 ≤ B := by linarith
  have hnn : F.card ≤ n * n := by
    have := card_le_univ F
    simpa using this
  have hN : (KLnodes F).card ≤ n * n := by
    have := card_le_univ (KLnodes F)
    simpa using this
  set X : ℝ := B ^ (n + F.card) * Real.exp (-(κ * (KLmaxDist d L a : ℝ))) with hX
  have hpt : ∀ b : ↥(KLnodes F) → Zd d L,
      ‖(∏ v : Fin n, M v (a v) (b ⟨KLleafPar F v, KLleafPar_mem F v⟩)) *
        ∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)‖
        ≤ X := by
    intro b
    obtain ⟨β, hβ⟩ : ∃ β : Fin n × Fin n → Zd d L, ∀ J (h : J ∈ KLnodes F), b ⟨J, h⟩ = β J :=
      ⟨fun J => if h : J ∈ KLnodes F then b ⟨J, h⟩ else 0, fun J h => by simp [h]⟩
    set Ls := ∑ v, zdistD d L (a v - β (KLleafPar F v))
    set Es := ∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e))
    have hmax : KLmaxDist d L a ≤ Ls + Es := by
      refine Finset.sup_le fun p _ => ?_
      exact KDecay_dist_bounds hF hn a β p.1 p.2
    have hL : ∏ v : Fin n, ‖M v (a v) (b ⟨KLleafPar F v, KLleafPar_mem F v⟩)‖
        ≤ B ^ n * Real.exp (-(κ * (Ls : ℝ))) := by
      calc ∏ v : Fin n, ‖M v (a v) (b ⟨KLleafPar F v, KLleafPar_mem F v⟩)‖
          ≤ ∏ v : Fin n, (B * Real.exp (-(κ * (zdistD d L (a v - β (KLleafPar F v)) : ℝ)))) := by
            refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
            rw [hβ]; exact hM _ _ _
        _ = B ^ n * Real.exp (-(κ * (Ls : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← Real.exp_sum]
            congr 2
            simp only [Ls, Nat.cast_sum, mul_sum, sum_neg_distrib]
    have hE' : ∏ J : ↥F, ‖E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)‖
        ≤ B ^ F.card * Real.exp (-(κ * (Es : ℝ))) := by
      calc ∏ J : ↥F, ‖E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)‖
          ≤ ∏ J : ↥F, (B * Real.exp
              (-(κ * (zdistD d L (β J.1 - β (KLnodePar F J.1)) : ℝ)))) := by
            refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun J _ => ?_
            rw [hβ, hβ]; exact hE _ _ _
        _ = B ^ F.card * Real.exp (-(κ * (Es : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_coe, ← Real.exp_sum]
            congr 2
            rw [sum_coe_sort F (fun e => -(κ * (zdistD d L (β e - β (KLnodePar F e)) : ℝ)))]
            simp only [Es, Nat.cast_sum, mul_sum, sum_neg_distrib]
    have hexp : Real.exp (-(κ * (Ls : ℝ))) * Real.exp (-(κ * (Es : ℝ)))
        ≤ Real.exp (-(κ * (KLmaxDist d L a : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (KLmaxDist d L a : ℝ) ≤ (Ls : ℝ) + Es := by exact_mod_cast hmax
      have h2 : κ * (KLmaxDist d L a : ℝ) ≤ κ * ((Ls : ℝ) + Es) :=
        mul_le_mul_of_nonneg_left h1 hκ
      linarith
    rw [norm_mul, norm_prod, norm_prod]
    calc _ ≤ (B ^ n * Real.exp (-(κ * (Ls : ℝ)))) * (B ^ F.card * Real.exp (-(κ * (Es : ℝ)))) :=
          mul_le_mul hL hE' (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = B ^ (n + F.card) * (Real.exp (-(κ * (Ls : ℝ))) * Real.exp (-(κ * (Es : ℝ)))) := by
          ring
      _ ≤ B ^ (n + F.card) * Real.exp (-(κ * (KLmaxDist d L a : ℝ))) := by gcongr
  have hcard : Fintype.card (↥(KLnodes F) → Zd d L) = (L ^ d) ^ (KLnodes F).card := by
    rw [Fintype.card_fun, Fintype.card_coe, card_Zd]
  rw [KLtreeValW]
  calc _ ≤ ∑ b : ↥(KLnodes F) → Zd d L,
        ‖(∏ v : Fin n, M v (a v) (b ⟨KLleafPar F v, KLleafPar_mem F v⟩)) *
          ∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _b : ↥(KLnodes F) → Zd d L, X := sum_le_sum fun b _ => hpt b
    _ = (((L ^ d : ℕ) : ℝ) ^ (KLnodes F).card) * X := by
        rw [sum_const, card_univ, hcard, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((L ^ d : ℕ) : ℝ) ^ (n * n) * B ^ (n + n * n) * Real.exp (-(κ * (KLmaxDist d L a : ℝ))) := by
        have hLL : (1 : ℝ) ≤ ((L ^ d : ℕ) : ℝ) := by
          have : 1 ≤ L ^ d := Nat.one_le_pow _ _ (NeZero.pos L)
          exact_mod_cast this
        have h1 : ((L ^ d : ℕ) : ℝ) ^ (KLnodes F).card ≤ ((L ^ d : ℕ) : ℝ) ^ (n * n) :=
          pow_le_pow_right₀ hLL hN
        have h2 : B ^ (n + F.card) ≤ B ^ (n + n * n) :=
          pow_le_pow_right₀ hB (by omega)
        have h3 : 0 ≤ Real.exp (-(κ * (KLmaxDist d L a : ℝ))) := (Real.exp_pos _).le
        calc ((L ^ d : ℕ) : ℝ) ^ (KLnodes F).card * X
            = ((L ^ d : ℕ) : ℝ) ^ (KLnodes F).card * B ^ (n + F.card) *
                Real.exp (-(κ * (KLmaxDist d L a : ℝ))) := by rw [hX]; ring
          _ ≤ ((L ^ d : ℕ) : ℝ) ^ (n * n) * B ^ (n + n * n) *
                Real.exp (-(κ * (KLmaxDist d L a : ℝ))) := by gcongr

end TreeBound

/-! ## 4. The edge kernels

The edge parameter of the tree representation is `ξ = u m(σ_i) m(σ_j)`.  For opposite charges
`m(+) m(-) = |m|² = 1`, so `ξ = u` and the propagator property `KLDecay` (property 5) applies; for
equal charges the property `KLShort` (property 5') applies.  In both cases `ℓ_u ≥ 1`, so both give a
bound `B_edge e^{-c |x-y|/ℓ_u}` with `c = min c_d c_κ`, `B_edge = C_d B_{u,0} + C_κ (1 + gmax²)`
(`B_{u,r} ≤ B_{u,0}`). -/

section Edges

variable {d L : ℕ} [NeZero L]

private theorem KDecay_mSigma_mul_not {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    mSigma E s * mSigma E (!s) = 1 := by
  have h := norm_mE hE
  have h1 : mE E * (starRingEnd ℂ) (mE E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  cases s
  · simp only [mSigma, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [mul_comm]; exact h1
  · simpa [mSigma] using h1

/-- The body of `KLDecay d gmax` at the constants `C_d`, `c_d`. -/
private def KDDecayBody (d : ℕ) (gmax Cd cd : ℝ) : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax →
    ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta d L g (t : ℂ) 0 a‖
        ≤ Cd * Bparam d L g t (zdistD d L a) * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t)

/-- The body of `KLShort d κ gmax` at the constants `C_κ`, `c_κ`. -/
private def KDShortBody (d : ℕ) (κ gmax Cκ cκ : ℝ) : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s : Bool, ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta d L g ((t : ℂ) * (mSigma E s * mSigma E s)) 0 a‖
        ≤ Cκ * ((if a = 0 then 1 else 0) + g ^ 2 * Real.exp (-cκ * (zdistD d L a : ℝ)))

/-- **The edge bound** `|Θ_ξ(x,y)| ≤ (C_d B_{u,0} + C_κ(1+gmax²)) e^{-c|x-y|/ℓ_u}`, `c = min c_d c_κ`,
for every edge parameter `ξ = u m(s) m(s')`, `0 ≤ u < 1`, `|E| ≤ 2 - κ`, `0 < g ≤ gmax`. -/
private theorem KDecay_edge_bound {κ gmax Cd cd Cκ cκ : ℝ} (hCd : 0 < Cd) (hcd : 0 < cd)
    (hCκ : 0 < Cκ) (hcκ : 0 < cκ) (Hd : KDDecayBody d gmax Cd cd)
    (Hs : KDShortBody d κ gmax Cκ cκ) (hL : 3 ≤ L) {g E u : ℝ} (hg0 : 0 < g) (hg1 : g ≤ gmax)
    (hκ : 0 ≤ κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (s s' : Bool) (x y : Zd d L) :
    ‖Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) x y‖ ≤
      (Cd * Bparam d L g u 0 + Cκ * (1 + gmax ^ 2)) *
        Real.exp (-(min cd cκ / ellT L g u * (zdistD d L (x - y) : ℝ))) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hξ : ‖(u : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := norm_mul_mSigma_lt_one hE2 hu0 hu1 s s'
  rw [KLIndStepA_Theta_apply_sub hL hξ x y]
  set a : Zd d L := y - x with ha
  have hr : zdistD d L (x - y) = zdistD d L a := by rw [ha, KDecay_zdistD_symm]
  rw [hr]
  have hr0 : (0 : ℝ) ≤ (zdistD d L a : ℝ) := Nat.cast_nonneg _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓ1 : 1 ≤ ellT L g u := one_le_ellT hL1
  have hℓ0 : 0 < ellT L g u := lt_of_lt_of_le one_pos hℓ1
  have hc0 : 0 < min cd cκ := lt_min hcd hcκ
  have he'0 : 0 < Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) := Real.exp_pos _
  have hB0 : 0 ≤ Bparam d L g u 0 := KLIndStepA_Bparam_nonneg u 0
  have hCB : 0 ≤ Cd * Bparam d L g u 0 := mul_nonneg hCd.le hB0
  have hCκ' : 0 ≤ Cκ * (1 + gmax ^ 2) := by positivity
  by_cases hss : s = s'
  · subst hss
    have h := Hs L hL g hg0 hg1 E hE s u hu0 hu1 a
    have h1 : Real.exp (-cκ * (zdistD d L a : ℝ)) ≤
        Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) := by
      apply Real.exp_le_exp.2
      have : min cd cκ / ellT L g u * (zdistD d L a : ℝ) ≤ cκ * (zdistD d L a : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hr0
        calc min cd cκ / ellT L g u ≤ min cd cκ := div_le_self hc0.le hℓ1
          _ ≤ cκ := min_le_right _ _
      linarith
    have h2 : (if a = 0 then (1 : ℝ) else 0) ≤
        Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · simp only [ha0, ite_false]; exact he'0.le
    have hg2 : g ^ 2 ≤ gmax ^ 2 := pow_le_pow_left₀ hg0.le hg1 2
    calc ‖Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s)) 0 a‖
        ≤ Cκ * ((if a = 0 then 1 else 0) + g ^ 2 * Real.exp (-cκ * (zdistD d L a : ℝ))) := h
      _ ≤ Cκ * (Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) +
            g ^ 2 * Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCκ.le
          have := mul_le_mul_of_nonneg_left h1 (sq_nonneg g)
          linarith
      _ = Cκ * (1 + g ^ 2) * Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) := by ring
      _ ≤ Cκ * (1 + gmax ^ 2) * Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ he'0.le
          exact mul_le_mul_of_nonneg_left (by linarith) hCκ.le
      _ ≤ (Cd * Bparam d L g u 0 + Cκ * (1 + gmax ^ 2)) *
            Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) he'0.le
  · have hs' : s' = !s := by cases s <;> cases s' <;> simp_all
    subst hs'
    rw [KDecay_mSigma_mul_not hE2 s, mul_one]
    have h := Hd L hL g hg0 hg1 u hu0 hu1 a
    have hBle : Bparam d L g u (zdistD d L a) ≤ Bparam d L g u 0 :=
      KLIndStepA_Bparam_le_zero u _
    have hexp : Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g u) ≤
        Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) := by
      apply Real.exp_le_exp.2
      have h3 : -cd * (zdistD d L a : ℝ) / ellT L g u = -(cd / ellT L g u * (zdistD d L a : ℝ)) := by
        ring
      rw [h3, neg_le_neg_iff]
      apply mul_le_mul_of_nonneg_right _ hr0
      exact div_le_div_of_nonneg_right (min_le_left _ _) hℓ0.le
    calc ‖Theta d L g (u : ℂ) 0 a‖
        ≤ Cd * Bparam d L g u (zdistD d L a) * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g u) := h
      _ ≤ (Cd * Bparam d L g u 0) * Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBle hCd.le) hexp (Real.exp_pos _).le hCB
      _ ≤ (Cd * Bparam d L g u 0 + Cκ * (1 + gmax ^ 2)) *
            Real.exp (-(min cd cκ / ellT L g u * (zdistD d L a : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) he'0.le

/-- The internal-edge bound: `|(Θ_ξ - 1)(x,y)| ≤ (B_edge + 1) e^{-c|x-y|/ℓ_u}`. -/
private theorem KDecay_internal_bound {κ gmax Cd cd Cκ cκ : ℝ} (hCd : 0 < Cd) (hcd : 0 < cd)
    (hCκ : 0 < Cκ) (hcκ : 0 < cκ) (Hd : KDDecayBody d gmax Cd cd)
    (Hs : KDShortBody d κ gmax Cκ cκ) (hL : 3 ≤ L) {g E u : ℝ} (hg0 : 0 < g) (hg1 : g ≤ gmax)
    (hκ : 0 ≤ κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (s s' : Bool) (x y : Zd d L) :
    ‖(Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) - 1) x y‖ ≤
      (Cd * Bparam d L g u 0 + Cκ * (1 + gmax ^ 2) + 1) *
        Real.exp (-(min cd cκ / ellT L g u * (zdistD d L (x - y) : ℝ))) := by
  have hT := KDecay_edge_bound hCd hcd hCκ hcκ Hd Hs hL hg0 hg1 hκ hE hu0 hu1 s s' x y
  have he0 : 0 < Real.exp (-(min cd cκ / ellT L g u * (zdistD d L (x - y) : ℝ))) :=
    Real.exp_pos _
  rw [Matrix.sub_apply]
  by_cases hxy : x = y
  · subst hxy
    have h0 : (zdistD d L (x - x) : ℝ) = 0 := by simp
    rw [h0] at hT ⊢
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, Matrix.one_apply_eq] at hT ⊢
    have h2 := norm_sub_le (Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) x x) (1 : ℂ)
    rw [norm_one] at h2
    linarith
  · rw [Matrix.one_apply_ne hxy, sub_zero]
    refine hT.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) he0.le

/-- **The far region**: `ℓ_u < L` forces `g² < L²(1-u)`, hence `B_{u,0} ≤ 2 g⁻²`. -/
private theorem KDecay_B0_le (hd : 2 ≤ d) (hL : 1 ≤ L) {g u : ℝ} (hg : 0 < g) (hu1 : u < 1)
    (hℓ : ellT L g u < L) : Bparam d L g u 0 ≤ 2 * (g ^ 2)⁻¹ := by
  have hu : (0 : ℝ) < 1 - u := by linarith
  have habs : |1 - u| = 1 - u := abs_of_pos hu
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hmax : max (g / Real.sqrt |1 - u|) 1 < L := by
    unfold ellT at hℓ
    rcases min_lt_iff.1 hℓ with h | h
    · exact h
    · exact absurd h (lt_irrefl _)
  have hlt : g / Real.sqrt |1 - u| < L := lt_of_le_of_lt (le_max_left _ _) hmax
  have hsq : 0 < Real.sqrt |1 - u| := Real.sqrt_pos.2 (by rw [habs]; exact hu)
  have hg' : g < L * Real.sqrt |1 - u| := (div_lt_iff₀ hsq).1 hlt
  have hg2 : g ^ 2 < (L : ℝ) ^ 2 * (1 - u) := by
    have := pow_lt_pow_left₀ hg' hg.le (two_ne_zero)
    rwa [mul_pow, Real.sq_sqrt (abs_nonneg _), habs] at this
  have hLd : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have hgd : g ^ 2 ≤ (L : ℝ) ^ d * (1 - u) := by
    have := mul_le_mul_of_nonneg_right hLd hu.le
    linarith
  have hg2pos : 0 < g ^ 2 := by positivity
  have h1 : (g ^ 2 + |1 - u|)⁻¹ ≤ (g ^ 2)⁻¹ := by
    apply inv_anti₀ hg2pos
    rw [habs]; linarith
  have h2 : ((L : ℝ) ^ d * |1 - u|)⁻¹ ≤ (g ^ 2)⁻¹ := by
    apply inv_anti₀ hg2pos
    rw [habs]; exact hgd
  unfold Bparam
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  linarith

end Edges

/-! ## 5. The primitive loop `𝒦` in the far region -/

section KFar

variable {d L : ℕ} [NeZero L]

/-- Crude count of the trees: `|T_SP(n)| ≤ 2^{n²}`. -/
private theorem KDecay_card_TSP (n : ℕ) : (TSP n).card ≤ 2 ^ (n * n) := by
  have h1 : (TSP n).card ≤ ((diagonals n).powerset).card := card_le_card (filter_subset _ _)
  rw [card_powerset] at h1
  have h2 : (diagonals n).card ≤ n * n := by
    have := card_le_univ (diagonals n)
    simpa using this
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)

/-- **`𝒦` for `k ≥ 3`** (the tree representation `(eq_Ktree)`): if every leaf edge and every internal
edge is bounded by `B e^{-κ' |x-y|}`, then
`|𝒦_{u,σ,a}| ≤ 2^{k²} (L^d)^{k²} B^{k+k²} e^{-κ' maxDist a}`. -/
private theorem KDecay_Kn_far {W : ℕ} (hW : 1 ≤ W) {g E u B κ' : ℝ} (hE2 : |E| ≤ 2) (hB : 1 ≤ B)
    (hκ' : 0 ≤ κ')
    (hleaf : ∀ (s s' : Bool) (x y : Zd d L),
      ‖Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) x y‖ ≤
        B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    (hint : ∀ (s s' : Bool) (x y : Zd d L),
      ‖(Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) - 1) x y‖ ≤
        B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ‖KLK d L g W E u (KLloopOf d L σ a)‖ ≤ 2 ^ (k * k) * (((L ^ d : ℕ) : ℝ) ^ (k * k) *
      B ^ (k + k * k) * Real.exp (-(κ' * (KLmaxDist d L a : ℝ)))) := by
  rw [KLK, KLgen_loopOf d L g W (mSigma E) u hk σ a, KLn]
  set X : ℝ := ((L ^ d : ℕ) : ℝ) ^ (k * k) * B ^ (k + k * k) *
    Real.exp (-(κ' * (KLmaxDist d L a : ℝ))) with hX
  have hB0 : 0 ≤ B := by linarith
  have hX0 : 0 ≤ X := by positivity
  have htree : ∀ F ∈ TSP k, ‖KLtreeValG d L g (mSigma E) u σ a F‖ ≤ X := by
    intro F hF
    unfold KLtreeValG
    exact KDecay_tree_bound (KLisTSP_of_mem_TSP hF) (by omega) a _ _ hB hκ'
      (fun v x y => hleaf (σ v) (σ (v + 1)) x y) (fun J x y => hint (σ J.1.1) (σ J.1.2) x y)
  have hW' : ‖(((W : ℂ) ^ d)⁻¹) ^ (k - 1)‖ ≤ 1 := by
    rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
    have h1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ h1))
  have hprod : ‖∏ i : Fin k, mSigma E (σ i)‖ = 1 := by
    rw [norm_prod]
    exact prod_eq_one fun i _ => norm_mSigma hE2 _
  have hsum : ‖∑ F ∈ TSP k, KLtreeValG d L g (mSigma E) u σ a F‖ ≤ 2 ^ (k * k) * X := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum htree).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have h2 : ((TSP k).card : ℝ) ≤ 2 ^ (k * k) := by exact_mod_cast KDecay_card_TSP k
    exact mul_le_mul_of_nonneg_right h2 hX0
  rw [norm_mul, norm_mul, hprod, one_mul]
  calc ‖(((W : ℂ) ^ d)⁻¹) ^ (k - 1)‖ * ‖∑ F ∈ TSP k, KLtreeValG d L g (mSigma E) u σ a F‖
      ≤ 1 * (2 ^ (k * k) * X) := mul_le_mul hW' hsum (norm_nonneg _) zero_le_one
    _ = 2 ^ (k * k) * X := one_mul _

/-- `max_{i,j} |a_i - a_j| ≤ |a₁ - a₂|` for `k = 2`. -/
private theorem KDecay_maxDist_two_le (a : Fin 2 → Zd d L) :
    KLmaxDist d L a ≤ zdistD d L (a 0 - a 1) := by
  refine Finset.sup_le fun p _ => ?_
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> simp [KDecay_zdistD_symm]

/-- **`𝒦` for `k = 2`** (`(Kn2sol)`): `|𝒦_{u,σ,(a₁,a₂)}| = W^{-d}|Θ_ξ(a₁,a₂)| ≤ B e^{-κ' maxDist a}`. -/
private theorem KDecay_Kn_two {W : ℕ} (hW : 1 ≤ W) {g E u B κ' : ℝ} (hE2 : |E| ≤ 2) (hB : 1 ≤ B)
    (hκ' : 0 ≤ κ')
    (hleaf : ∀ (s s' : Bool) (x y : Zd d L),
      ‖Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) x y‖ ≤
        B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d L) :
    ‖KLK d L g W E u (KLloopOf d L σ a)‖ ≤ B * Real.exp (-(κ' * (KLmaxDist d L a : ℝ))) := by
  have hI : KLloopOf d L σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [hI, KLK_two]
  have hB0 : 0 ≤ B := by linarith
  have hW' : ‖((W : ℂ) ^ d)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    have h1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  have hm : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, mul_one]
  have hT := hleaf (σ 0) (σ 1) (a 0) (a 1)
  have hmd : (KLmaxDist d L a : ℝ) ≤ (zdistD d L (a 0 - a 1) : ℝ) := by
    exact_mod_cast KDecay_maxDist_two_le a
  have hexp : Real.exp (-(κ' * (zdistD d L (a 0 - a 1) : ℝ))) ≤
      Real.exp (-(κ' * (KLmaxDist d L a : ℝ))) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hmd hκ'
    linarith
  rw [norm_mul, norm_mul, hm, mul_one]
  calc ‖((W : ℂ) ^ d)⁻¹‖ * ‖Theta d L g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖
      ≤ 1 * (B * Real.exp (-(κ' * (KLmaxDist d L a : ℝ)))) := by
        refine mul_le_mul hW' (hT.trans ?_) (norm_nonneg _) zero_le_one
        exact mul_le_mul_of_nonneg_left hexp hB0
    _ = _ := one_mul _

end KFar

/-! ## 6. The asymptotic absorption -/

/-- `A N^P e^{-c N^s} ≤ 1` eventually in `N`, for `c, s > 0`. -/
private theorem KDecay_eventually (A P c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    ∀ᶠ N : ℕ in Filter.atTop, A * (N : ℝ) ^ P * Real.exp (-(c * (N : ℝ) ^ s)) ≤ 1 := by
  have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ s) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (P / s) c hc
  have h3 : Filter.Tendsto (fun N : ℕ => A * (((N : ℝ) ^ s) ^ (P / s) *
      Real.exp (-c * (N : ℝ) ^ s))) Filter.atTop (nhds (A * 0)) :=
    (h2.comp h1).const_mul A
  rw [mul_zero] at h3
  filter_upwards [Filter.eventually_ge_atTop 1, h3.eventually (gt_mem_nhds one_pos)] with N hN1 hN3
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have e1 : ((N : ℝ) ^ s) ^ (P / s) = (N : ℝ) ^ P := by
    rw [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ hs.ne']
  have e2 : -c * (N : ℝ) ^ s = -(c * (N : ℝ) ^ s) := by ring
  simp only [e1, e2] at hN3
  linarith [hN3, show A * ((N : ℝ) ^ P * Real.exp (-(c * (N : ℝ) ^ s))) =
    A * (N : ℝ) ^ P * Real.exp (-(c * (N : ℝ) ^ s)) by ring]

/-! ## 6b. The far-region estimate, deterministic -/

section FarCore

variable {d L : ℕ} [NeZero L]

/-- **`𝒦` for every `k ≥ 2`** (`(Kn2sol)` for `k = 2`, `(eq_Ktree)` for `k ≥ 3`) with the one shape
`2^{k²} (L^d)^{k²} B^{k+k²} e^{-κ' maxDist a}` (for `k = 2` the factors `2^4 (L^d)^4 B^5 ≥ 1` are
harmless). -/
private theorem KDecay_Kn_all {W : ℕ} (hW : 1 ≤ W) {g E u B κ' : ℝ} (hE2 : |E| ≤ 2) (hB : 1 ≤ B)
    (hκ' : 0 ≤ κ')
    (hleaf : ∀ (s s' : Bool) (x y : Zd d L),
      ‖Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) x y‖ ≤
        B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    (hint : ∀ (s s' : Bool) (x y : Zd d L),
      ‖(Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) - 1) x y‖ ≤
        B * Real.exp (-(κ' * (zdistD d L (x - y) : ℝ))))
    {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ‖KLK d L g W E u (KLloopOf d L σ a)‖ ≤ 2 ^ (k * k) * (((L ^ d : ℕ) : ℝ) ^ (k * k) *
      B ^ (k + k * k) * Real.exp (-(κ' * (KLmaxDist d L a : ℝ)))) := by
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2 : k = 2 := by omega
    subst hk2
    refine (KDecay_Kn_two hW hE2 hB hκ' hleaf σ a).trans ?_
    have hLL : (1 : ℝ) ≤ ((L ^ d : ℕ) : ℝ) := by
      have : 1 ≤ L ^ d := Nat.one_le_pow _ _ (NeZero.pos L)
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ 2 ^ (2 * 2) := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ ((L ^ d : ℕ) : ℝ) ^ (2 * 2) := one_le_pow₀ hLL
    have h4 : B ≤ B ^ (2 + 2 * 2) := le_self_pow₀ hB (by norm_num)
    have h5 : (1 : ℝ) ≤ 2 ^ (2 * 2) * ((L ^ d : ℕ) : ℝ) ^ (2 * 2) := one_le_mul_of_one_le_of_one_le h2 h3
    have he : 0 ≤ Real.exp (-(κ' * (KLmaxDist d L a : ℝ))) := (Real.exp_pos _).le
    have hB0 : 0 ≤ B ^ (2 + 2 * 2) := by positivity
    calc B * Real.exp (-(κ' * (KLmaxDist d L a : ℝ)))
        ≤ B ^ (2 + 2 * 2) * Real.exp (-(κ' * (KLmaxDist d L a : ℝ))) :=
          mul_le_mul_of_nonneg_right h4 he
      _ ≤ (2 ^ (2 * 2) * ((L ^ d : ℕ) : ℝ) ^ (2 * 2)) * B ^ (2 + 2 * 2) *
            Real.exp (-(κ' * (KLmaxDist d L a : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hB0 h5) he
      _ = 2 ^ (2 * 2) * (((L ^ d : ℕ) : ℝ) ^ (2 * 2) * B ^ (2 + 2 * 2) *
            Real.exp (-(κ' * (KLmaxDist d L a : ℝ)))) := by ring
  · have : NeZero k := ⟨by omega⟩
    exact KDecay_Kn_far hW hE2 hB hκ' hleaf hint hk3 σ a

/-- The edge bounds with the one constant `B = C₁ W^{2Q}` in the far region `ℓ_u < L`, under `W^{-Q} ≤ g`:
`B_edge + 1 ≤ (2 C_d + C_κ(1+gmax²) + 1) W^{2Q}` since `B_{u,0} ≤ 2 g⁻² ≤ 2 W^{2Q}`. -/
private theorem KDecay_edges_far {κ gmax Cd cd Cκ cκ : ℝ} (hCd : 0 < Cd) (hcd : 0 < cd)
    (hCκ : 0 < Cκ) (hcκ : 0 < cκ) (Hd : KDDecayBody d gmax Cd cd)
    (Hs : KDShortBody d κ gmax Cκ cκ) (hd : 2 ≤ d) (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W)
    {g E u Q : ℝ} (hg0 : 0 < g) (hg1 : g ≤ gmax) (hκ : 0 ≤ κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hQ : 0 < Q) (hgQ : (W : ℝ) ^ (-Q) ≤ g) (hℓL : ellT L g u < L) :
    1 ≤ (2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q) ∧
    (∀ (s s' : Bool) (x y : Zd d L),
      ‖Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) x y‖ ≤
        ((2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q)) *
          Real.exp (-(min cd cκ / ellT L g u * (zdistD d L (x - y) : ℝ)))) ∧
    (∀ (s s' : Bool) (x y : Zd d L),
      ‖(Theta d L g ((u : ℂ) * (mSigma E s * mSigma E s')) - 1) x y‖ ≤
        ((2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q)) *
          Real.exp (-(min cd cκ / ellT L g u * (zdistD d L (x - y) : ℝ)))) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hCκ' : 0 < Cκ * (1 + gmax ^ 2) := mul_pos hCκ (by positivity)
  have hWQ1 : 1 ≤ (W : ℝ) ^ (2 * Q) := Real.one_le_rpow hW1r (by linarith)
  have hWQneg : 0 < (W : ℝ) ^ (-Q) := Real.rpow_pos_of_pos hWpos _
  have hsq : ((W : ℝ) ^ (-Q)) ^ 2 = ((W : ℝ) ^ (2 * Q))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le, ← Real.rpow_neg hWpos.le]
    congr 1; push_cast; ring
  have hg2 : (g ^ 2)⁻¹ ≤ (W : ℝ) ^ (2 * Q) := by
    have h1 : ((W : ℝ) ^ (-Q)) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hWQneg.le hgQ 2
    have h2 := inv_anti₀ (by positivity) h1
    rwa [hsq, inv_inv] at h2
  have hB0le := KDecay_B0_le hd (by omega : 1 ≤ L) hg0 hu1 hℓL
  have hBedge : Cd * Bparam d L g u 0 + Cκ * (1 + gmax ^ 2) + 1 ≤
      (2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q) := by
    have h1 : Cd * Bparam d L g u 0 ≤ Cd * (2 * (W : ℝ) ^ (2 * Q)) :=
      mul_le_mul_of_nonneg_left (by linarith) hCd.le
    have h2 : Cκ * (1 + gmax ^ 2) + 1 ≤ (Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q) :=
      le_mul_of_one_le_right (by linarith) hWQ1
    linarith
  refine ⟨one_le_mul_of_one_le_of_one_le (by linarith) hWQ1, fun s s' x y => ?_, fun s s' x y => ?_⟩
  · have h := KDecay_edge_bound hCd hcd hCκ hcκ Hd Hs hL hg0 hg1 hκ hE hu0 hu1 s s' x y
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    linarith
  · have h := KDecay_internal_bound hCd hcd hCκ hcκ Hd Hs hL hg0 hg1 hκ hE hu0 hu1 s s' x y
    exact h.trans (mul_le_mul_of_nonneg_right hBedge (Real.exp_pos _).le)

end FarCore

end RBM.Loop

/-! ## 7. The fast decay of `𝒦` at far labels, `STKcalDecay`

`STKcalDecay d` is the `d`-dimensional form of RBM2D's `KcalDecay`, on the `K`-loop vocabulary `KLK`,
`KLloopOf`, `KLmaxDist`.  The coupling `g ∈ (0, gmax]` is a parameter, and the premise `W^{-Q} ≤ g`
(`Q > 0` fixed before the `∀ᶠ N`) is part of the statement; the paper has it from (2.10) `eq:WO`,
with `Q = d/2`.

Proof (deterministic): `k = 1`: `maxDist = 0`, the premise fails.  `k ≥ 2`: `maxDist ≤ d L` and
`W^τ > d` force `ℓ_u < L`, hence `g² < L²(1-u)`, `B_{u,0} ≤ 2 g⁻² ≤ 2 W^{2Q}`; every edge of the tree
representation is `≤ B e^{-c|x-y|/ℓ_u}` with `B = C₁ W^{2Q}`, `c = min c_d c_κ` (`KLPT_holds`), the tree
sum is bounded by `2^{k²} (L^d)^{k²} B^{k+k²} e^{-c maxDist/ℓ_u}` (`KDecay_Kn_all`), and
`maxDist ≥ ℓ_u W^τ` turns this into `A N^{P} e^{-c W^τ}`, `W^τ ≥ N^{𝔠τ}`. -/

namespace RBM.Loop

open Finset

section Pointwise

variable {d : ℕ} {L : ℕ} [NeZero L]

/-- **The far-region estimate at fixed `(L, W)`** (`k ≥ 2`, `ℓ_u < L`):
`|𝒦_{u,σ,a}| ≤ A N^{P_k} e^{-c W^τ}` for every `N ≥ max(W, L^d)`, `ℓ_u W^τ ≤ maxDist a`,
`c = min c_d c_κ`, `A = 2^{k²} C₁^{k+k²}`, `P_k = k² + 2Q(k+k²)`. -/
private theorem KDecay_pointwise {κ gmax Cd cd Cκ cκ : ℝ} (hCd : 0 < Cd) (hcd : 0 < cd)
    (hCκ : 0 < Cκ) (hcκ : 0 < cκ) (Hd : KDDecayBody d gmax Cd cd)
    (Hs : KDShortBody d κ gmax Cκ cκ) (hd : 2 ≤ d) (hL : 3 ≤ L) {W N : ℕ} (hW : 1 ≤ W)
    (hWN : W ≤ N) (hLdN : L ^ d ≤ N) {g E u Q τ : ℝ} (hg0 : 0 < g) (hg1 : g ≤ gmax) (hκ : 0 ≤ κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hQ : 0 < Q)
    (hgQ : (W : ℝ) ^ (-Q) ≤ g) (hℓL : ellT L g u < L) {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool)
    (a : Fin k → Zd d L)
    (hfar : ellT L g u * (W : ℝ) ^ τ ≤ (KLmaxDist d L a : ℝ)) :
    ‖KLK d L g W E u (KLloopOf d L σ a)‖ ≤
      2 ^ (k * k) * (2 * Cd + Cκ * (1 + gmax ^ 2) + 1) ^ (k + k * k) *
        (N : ℝ) ^ (((k * k : ℕ) : ℝ) + 2 * Q * ((k + k * k : ℕ) : ℝ)) *
        Real.exp (-(min cd cκ * (W : ℝ) ^ τ)) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hCκ' : 0 < Cκ * (1 + gmax ^ 2) := mul_pos hCκ (by positivity)
  have hC₁1 : 1 ≤ 2 * Cd + Cκ * (1 + gmax ^ 2) + 1 := by linarith
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hWpos (by exact_mod_cast hWN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hW.trans hWN)
  have hWNr : (W : ℝ) ≤ N := by exact_mod_cast hWN
  have hLdNr : ((L ^ d : ℕ) : ℝ) ≤ N := by exact_mod_cast hLdN
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓpos : 0 < ellT L g u := ellT_pos hL1r
  have hc : 0 < min cd cκ := lt_min hcd hcκ
  obtain ⟨hB1, hleaf, hint⟩ := KDecay_edges_far hCd hcd hCκ hcκ Hd Hs hd hL hW hg0 hg1 hκ hE hu0 hu1
    hQ hgQ hℓL
  have hκ'0 : 0 ≤ min cd cκ / ellT L g u := by positivity
  have hK := KDecay_Kn_all hW hE2 hB1 hκ'0 hleaf hint hk σ a
  -- `κ' maxDist ≥ c W^τ`
  have hκ' : min cd cκ * (W : ℝ) ^ τ ≤ min cd cκ / ellT L g u * (KLmaxDist d L a : ℝ) := by
    have h1 : min cd cκ / ellT L g u * (ellT L g u * (W : ℝ) ^ τ) ≤
        min cd cκ / ellT L g u * (KLmaxDist d L a : ℝ) :=
      mul_le_mul_of_nonneg_left hfar hκ'0
    have h2 : min cd cκ / ellT L g u * (ellT L g u * (W : ℝ) ^ τ) = min cd cκ * (W : ℝ) ^ τ := by
      field_simp
    linarith
  have hexp : Real.exp (-(min cd cκ / ellT L g u * (KLmaxDist d L a : ℝ))) ≤
      Real.exp (-(min cd cκ * (W : ℝ) ^ τ)) := Real.exp_le_exp.2 (by linarith)
  refine hK.trans ?_
  -- `B ≤ C₁ N^{2Q}`
  have hYle : (W : ℝ) ^ (2 * Q) ≤ (N : ℝ) ^ (2 * Q) :=
    Real.rpow_le_rpow hWpos.le hWNr (by linarith)
  have hBN : (2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q) ≤
      (2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (N : ℝ) ^ (2 * Q) :=
    mul_le_mul_of_nonneg_left hYle (by linarith)
  have hNpow : (N : ℝ) ^ (k * k) * ((N : ℝ) ^ (2 * Q)) ^ (k + k * k) =
      (N : ℝ) ^ (((k * k : ℕ) : ℝ) + 2 * Q * ((k + k * k : ℕ) : ℝ)) := by
    have e1 : ((N : ℝ) ^ (2 * Q)) ^ (k + k * k) = (N : ℝ) ^ (2 * Q * ((k + k * k : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    have e2 : (N : ℝ) ^ (k * k) = (N : ℝ) ^ (((k * k : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
    rw [e1, e2, ← Real.rpow_add hN0]
  have hBpow : ((2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q)) ^ (k + k * k) ≤
      (2 * Cd + Cκ * (1 + gmax ^ 2) + 1) ^ (k + k * k) * ((N : ℝ) ^ (2 * Q)) ^ (k + k * k) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hBN _
  calc 2 ^ (k * k) * (((L ^ d : ℕ) : ℝ) ^ (k * k) *
        ((2 * Cd + Cκ * (1 + gmax ^ 2) + 1) * (W : ℝ) ^ (2 * Q)) ^ (k + k * k) *
          Real.exp (-(min cd cκ / ellT L g u * (KLmaxDist d L a : ℝ))))
      ≤ 2 ^ (k * k) * (((N : ℝ)) ^ (k * k) *
          ((2 * Cd + Cκ * (1 + gmax ^ 2) + 1) ^ (k + k * k) * ((N : ℝ) ^ (2 * Q)) ^ (k + k * k)) *
            Real.exp (-(min cd cκ * (W : ℝ) ^ τ))) := by
        gcongr
    _ = 2 ^ (k * k) * (2 * Cd + Cκ * (1 + gmax ^ 2) + 1) ^ (k + k * k) *
        (N : ℝ) ^ (((k * k : ℕ) : ℝ) + 2 * Q * ((k + k * k : ℕ) : ℝ)) *
        Real.exp (-(min cd cκ * (W : ℝ) ^ τ)) := by
        rw [← hNpow]
        ring

end Pointwise

end RBM.Loop

namespace RBM.Gauss.Sizes

open Filter RBM RBM.Loop

/-- **`STKcalDecay d`**: the fast decay of the primitive loop `𝒦` at far labels (source (2.58)
`eq:bcal_k` and the tree representation (A.30) `eq_Ktree`), the `d`-dimensional form of RBM2D's
`KcalDecay`; deterministic, eventually in `N`.  The lower bound `W^{-Q} ≤ g` (`Q > 0` fixed before
the `∀ᶠ N`) is a premise of the statement. -/
def STKcalDecay (d : ℕ) : Prop :=
  ∀ κ gmax : ℝ, 0 < κ → 0 < gmax → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ k : ℕ, 1 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D →
    ∀ Q : ℝ, 0 < Q →
    ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], (W * L) ^ d = N →
      (N : ℝ) ^ 𝔠 ≤ (W : ℝ) → 3 ≤ L →
      ∀ g : ℝ, 0 < g → g ≤ gmax → ((W : ℕ) : ℝ) ^ (-Q) ≤ g →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d L),
        ellT L g u * ((W : ℕ) : ℝ) ^ τ ≤ (KLmaxDist d L a : ℝ) →
          ‖KLK d L g W E u (KLloopOf d L σ a)‖ ≤ ((W : ℕ) : ℝ) ^ (-D)

/-- **`STKcalDecay d` holds** for `3 ≤ d`: the hypothesis `3 ≤ d` enters through `KLPT_holds`, the
propagator properties 5, 5', which are stated for `d ≥ 3`.  `inst_stKcalDecay_admissible` below gives
the form for an admissible size sequence. -/
theorem stKcalDecay_holds {d : ℕ} (hd : 3 ≤ d) : STKcalDecay d := by
  intro κ gmax hκ hg 𝔠 h𝔠 k hk τ D hτ hD Q hQ
  obtain ⟨Cd, hCd, cd, hcd, Hd⟩ := (KLPT_holds hd hκ hg).decay
  obtain ⟨Cκ, hCκ, cκ, hcκ, Hs⟩ := (KLPT_holds hd hκ hg).short
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min cd cκ := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min hcd hcκ
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 * Cd + Cκ * (1 + gmax ^ 2) + 1 := ⟨_, rfl⟩
  have hCκ' : 0 < Cκ * (1 + gmax ^ 2) := mul_pos hCκ (by positivity)
  have hC₁1 : 1 ≤ C₁ := by rw [hC₁]; linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 ^ (k * k) * C₁ ^ (k + k * k) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨Pk, hPk⟩ : ∃ Pk : ℝ, Pk = ((k * k : ℕ) : ℝ) + 2 * Q * ((k + k * k : ℕ) : ℝ) := ⟨_, rfl⟩
  filter_upwards [KDecay_eventually A (Pk + D) c (𝔠 * τ) hc (mul_pos h𝔠 hτ),
    eventually_ge_atTop 2,
    ((tendsto_rpow_atTop (mul_pos h𝔠 hτ)).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      (d : ℝ)] with N hN hN2 hNd
  intro L W _ _ hNLW hNW hL g hg0 hg1 hgQ E hE u hu0 hu1 σ a hfar
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hW1' : 1 ≤ W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1'
  have hLpos' : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLpos'
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hLpos'
  have hWN' : W ≤ N := by
    rw [← hNLW]
    calc W ≤ W * L := Nat.le_mul_of_pos_right _ hLpos'
      _ ≤ (W * L) ^ d := Nat.le_self_pow (by omega) _
  have hLdN' : L ^ d ≤ N := by
    rw [← hNLW]
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW1') d
  have hWN : (W : ℝ) ≤ N := by exact_mod_cast hWN'
  have hNτ : (N : ℝ) ^ (𝔠 * τ) ≤ (W : ℝ) ^ τ := by
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hNW hτ.le
  have hdW : (d : ℝ) < (W : ℝ) ^ τ := lt_of_lt_of_le hNd hNτ
  have hWτpos : 0 < (W : ℝ) ^ τ := Real.rpow_pos_of_pos hWpos τ
  have hℓpos : 0 < ellT L g u := ellT_pos hL1r
  have hℓle : ellT L g u ≤ L := ellT_le_L
  -- the far-region estimate `|𝒦| ≤ A N^{Pk} e^{-c W^τ}`
  have key : ‖KLK d L g W E u (KLloopOf d L σ a)‖ ≤
      A * (N : ℝ) ^ Pk * Real.exp (-(c * (W : ℝ) ^ τ)) := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · exfalso
      have hk1 : k = 1 := by omega
      subst hk1
      have hmd : KLmaxDist d L a = 0 := by
        refine Nat.le_zero.1 (Finset.sup_le fun p _ => ?_)
        have : p.1 = p.2 := Subsingleton.elim _ _
        simp [this]
      rw [hmd, Nat.cast_zero] at hfar
      have := mul_pos hℓpos hWτpos
      linarith
    · have hmaxL : (KLmaxDist d L a : ℝ) ≤ d * L := by
        have : KLmaxDist d L a ≤ d * L := Finset.sup_le fun p _ => zdistD_le d _
        exact_mod_cast this
      have hℓL : ellT L g u < L := by
        refine lt_of_le_of_ne hℓle fun h => ?_
        rw [h] at hfar
        have h1 : (L : ℝ) * (W : ℝ) ^ τ ≤ d * L := hfar.trans hmaxL
        have h2 := mul_lt_mul_of_pos_left hdW hLpos
        nlinarith
      have h := KDecay_pointwise hCd hcd hCκ hcκ Hd Hs (by omega) hL hW1' hWN' hLdN' hg0 hg1 hκ.le hE
        hu0 hu1 hQ hgQ hℓL hk2 σ a hfar
      rw [← hcdef, ← hC₁, ← hPk] at h
      rw [hA]
      calc _ ≤ 2 ^ (k * k) * C₁ ^ (k + k * k) * (N : ℝ) ^ Pk * Real.exp (-(c * (W : ℝ) ^ τ)) := h
        _ = _ := by ring
  -- absorb into `W^{-D}`
  have hWD : (W : ℝ) ^ D ≤ (N : ℝ) ^ D := Real.rpow_le_rpow hWpos.le hWN hD.le
  have hexp : Real.exp (-(c * (W : ℝ) ^ τ)) ≤ Real.exp (-(c * (N : ℝ) ^ (𝔠 * τ))) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hNτ hc.le
    linarith
  have hWDpos : 0 < (W : ℝ) ^ D := Real.rpow_pos_of_pos hWpos D
  rw [Real.rpow_neg hWpos.le, ← one_div, le_div_iff₀ hWDpos]
  have hAN : 0 ≤ A * (N : ℝ) ^ Pk := mul_nonneg hA0 (Real.rpow_nonneg hN0.le _)
  calc ‖KLK d L g W E u (KLloopOf d L σ a)‖ * (W : ℝ) ^ D
      ≤ (A * (N : ℝ) ^ Pk * Real.exp (-(c * (W : ℝ) ^ τ))) * (W : ℝ) ^ D :=
        mul_le_mul_of_nonneg_right key hWDpos.le
    _ ≤ (A * (N : ℝ) ^ Pk * Real.exp (-(c * (N : ℝ) ^ (𝔠 * τ)))) * (N : ℝ) ^ D :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp hAN) hWD hWDpos.le
          (mul_nonneg hAN (Real.exp_pos _).le)
    _ = A * (N : ℝ) ^ (Pk + D) * Real.exp (-(c * (N : ℝ) ^ (𝔠 * τ))) := by
        rw [Real.rpow_add hN0]; ring
    _ ≤ 1 := hN

end RBM.Gauss.Sizes

/-! ## 8. The form for an admissible size sequence -/

namespace RBM.Gauss.KDecayInst

open Filter RBM RBM.Loop RBM.Gauss.Sizes

/-- **How a consumer with `sz.Admissible 𝔠 𝔡` uses `stKcalDecay_holds`**: `(eq:WO)` gives
`W^{-d/2} ≤ W^{-d/2+𝔡} ≤ lam n` (so `Q = d/2`) and `lam n ≤ 𝔡⁻¹ = gmax` eventually; `Bandwidth 𝔠` gives
`N^𝔠 ≤ W`, `SizeTendsto` gives `N → ∞`, and `N = (W L)^d` is `Sizes.size`. -/
theorem inst_stKcalDecay_admissible {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {𝔠 𝔡 : ℝ}
    (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {k : ℕ} (hk : 1 ≤ k) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ ≤ (KLmaxDist d (sz.L n) a : ℝ) →
          ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E u (KLloopOf d (sz.L n) σ a)‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := hA
  have hS := stKcalDecay_holds hd κ 𝔡⁻¹ hκ (inv_pos.2 h𝔡) 𝔠 h𝔠 k hk τ D hτ hD ((d : ℝ) / 2)
    (by have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity)
  filter_upwards [(tendsto_size sz hN).eventually hS, hB, hWO] with n hn hbw hwo
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlam : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) / 2)) ≤ sz.lam n :=
    (Real.rpow_le_rpow_of_exponent_le hW1 (by rw [neg_div]; linarith)).trans hwo.1
  have hlam0 : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hlam
  intro E hE u hu0 hu1 σ a hfar
  exact hn (sz.L n) (sz.W n) rfl hbw (sz.three_le_L n) (sz.lam n) hlam0 hwo.2 hlam E hE u hu0 hu1 σ a
    hfar

end RBM.Gauss.KDecayInst


/-! ## 9. `STKbound`, `STKward` uniformly in time

`STKbound`, `STKward` are per time sequence `τ : ℕ → ℝ`.  Step 3 needs them with the time inside the
`≺`: `u ∈ [s_n, t_n]` an index of the union (as `STLmaxU`).  The left sides are deterministic, so the
per-sequence bound at every section `u` gives it: `Green.perTime_timeIcc_of_forall_seq` turns the
sections into the per-time bound over `TimeIcc s t`, and a per-time bound of a deterministic family is
eventually empty (`P(univ) = 1`), hence a `Prec`. -/

namespace RBM.Gauss.Sizes

open Filter MeasureTheory RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- A per-time bound of a deterministic family is a `Prec`: each bad event is `∅` or the whole space, and
`P(univ) = 1 > N^{-1}` for `N ≥ 2`. -/
private theorem KDecay_prec_of_perTime_det (hN : sz.SizeTendsto) {U : ℕ → Type*}
    (f g : ∀ n, U n → ℝ)
    (h : PerTimeDomAt sz.seqP sz.size (U := U) (fun n u _ => f n u) (fun n u _ => g n u)) :
    sz.Prec (fun n u _ => f n u) (fun n u _ => g n u) := by
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  have hsz := tendsto_size sz hN
  filter_upwards [h τ hτ 1 one_pos, hsz.eventually_ge_atTop 2] with n hn hn2
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro u
  by_contra hlt
  push Not at hlt
  have hset : {ω' : SeqΩ sz | ((sz.size n : ℕ) : ℝ) ^ τ * g n u < f n u} = Set.univ := by
    ext ω'
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hlt
  have h1 := hn u
  rw [hset, measure_univ] at h1
  have hN2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn2
  have hlt1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) < 1 := by
    rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  exact absurd h1 (not_le.2 (ENNReal.ofReal_lt_one.2 hlt1))

/-- The deterministic maximiser, as the bridge: sections `u n ∈ [s n, t n]` ⇒ the `Prec` over `TimeIcc s t`. -/
private theorem KDecay_prec_timeIcc (hN : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    {V : ℕ → Type} (hV : ∀ n, Nonempty (V n)) (f g : ∀ n, ℝ → V n → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      sz.Prec (U := V) (fun n v _ => f n (u n) v) (fun n v _ => g n (u n) v)) :
    sz.Prec (U := fun n => TimeIcc s t n × V n) (fun n p _ => f n (p.1 : ℝ) p.2)
      (fun n p _ => g n (p.1 : ℝ) p.2) := by
  refine KDecay_prec_of_perTime_det sz hN (U := fun n => TimeIcc s t n × V n)
    (fun n p => f n (p.1 : ℝ) p.2) (fun n p => g n (p.1 : ℝ) p.2) ?_
  refine Green.perTime_timeIcc_of_forall_seq sz.seqP sz.size hst hV
    (fun n u v _ => f n u v) (fun n u v _ => g n u v) fun u hu => ?_
  intro τ hτ D hD
  filter_upwards [h u hu τ hτ D hD] with n hn
  intro p
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  exact ⟨p.2, hω⟩

/-- **`STKbound` uniformly in `u ∈ [s_n, t_n]`** (Lemma 2.16 `ML:Kbound`, (2.58) `eq:bcal_k`, the shape
of `STLmaxU` for `𝒦`): `max_{u ∈ [s,t], σ, a} |𝒦^{(k)}_{u,σ,a}| / (W^{-d}B_{u,0})^{k-1} ≺ 1`, every
`k ≥ 1`, from `stKbound_holds` under its hypotheses and the window `0 ≤ s ≤ t < 1`. -/
theorem stKbound_timeIcc (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) :
    ∀ k : ℕ, 1 ≤ k →
      sz.Prec (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
        (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1)) := by
  intro k hk
  refine KDecay_prec_timeIcc sz hN hst (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n u p => ‖STKloop sz n (E n) u p.1 p.2‖) (fun n u _ => (sz.Bctl n u) ^ (k - 1)) ?_
  intro u hu
  exact stKbound_holds sz hd hκ hg hN hE hlam u (fun n => (hs0 n).trans (hu n).1)
    (fun n => (hu n).2.trans_lt (ht1 n)) k hk

/-- **`STKward` uniformly in `u ∈ [s_n, t_n]`** (Lemma 4.2 `lem_wardineq_K`, (4.9) `wardineq_K`): for
every `k ≥ 2`, `max_{σ, a_1..a_{k-1}} Σ_{a_k} |𝒦^{(k)}_{u,σ,a}| ≺ (W^d η_u)⁻¹ (W^{-d}B_{u,0})^{k-2}`,
uniformly in `u ∈ [s,t]`, from `stKward_holds`. -/
theorem stKward_timeIcc (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) :
    ∀ k : ℕ, 2 ≤ k →
      sz.Prec (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
        (fun n p _ => ∑ x : Zd d (sz.L n),
          ‖STKI sz n (E n) (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
        (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (p.1 : ℝ))⁻¹ *
          (sz.Bctl n (p.1 : ℝ)) ^ (k - 2)) := by
  intro k hk
  refine KDecay_prec_timeIcc sz hN hst (V := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n u p => ∑ x : Zd d (sz.L n), ‖STKI sz n (E n) u ⟨List.ofFn p.1, List.ofFn p.2 ++ [x]⟩‖)
    (fun n u _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) u)⁻¹ * (sz.Bctl n u) ^ (k - 2)) ?_
  intro u hu
  exact stKward_holds sz hd hκ hg hN hE hlam u (fun n => (hs0 n).trans (hu n).1)
    (fun n => (hu n).2.trans_lt (ht1 n)) k hk

end RBM.Gauss.Sizes


/-! ## 10. The lattice sum of the tail `𝒯_t` and (4.16) `eq:sumtwoloop`

In (4.16) `eq:sumtwoloop`, in the proof of Lemma 4.3 (`lem:SEforLn`):
`((1-s)/(1-t))^{C_d} (W^{-d}B_{t,0})^{1/5} Σ_{a₂} 𝒯_t(|a₁-a₂|) ≺ (W^{-d}B_{t,0})^{1/6} η_t⁻¹`
under (2.83) `con_st_ind` as long as `𝔠_d` is small depending on `C_d`.
The distance `|a|` is the block `l^∞` distance `zdistInf`; the propagator side is in `zdistD`, with
`zdistInf ≤ zdistD ≤ d zdistInf`.  The lattice sum is
`Σ_a 𝒯_t(|a|_∞) ≤ C_∞(d) (1-t)⁻¹`, `C_∞(d) = d^{d-2} 2^d C(1/d) + 1`, uniformly in `L`, `g ≥ 0`, `t < 1`:
the first term of `B_{t,r}` is summed by the radial sum `sum_radial_exp_le` (`l¹` reduction
`|a|_1 ≤ d |a|_∞`) and `(1-t) ℓ_t² ≤ g² + (1-t)`, the zero-mode term `(L^d(1-t))⁻¹` by the number of
points `L^d`. -/

namespace RBM.Loop

open Finset Real RBM.Gauss

/-- The constant `C_∞(d) = d^{d-2} 2^d C(1/d) + 1` of the lattice sum of the tail (`C(κ)` is `radC`). -/
def KDecay_tailC (d : ℕ) : ℝ := (d : ℝ) ^ (d - 2) * 2 ^ d * radC (1 / (d : ℝ)) + 1

theorem KDecay_one_le_tailC {d : ℕ} (hd : 1 ≤ d) : 1 ≤ KDecay_tailC d := by
  unfold KDecay_tailC
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have := radC_pos (one_div_pos.2 hd')
  have : 0 ≤ (d : ℝ) ^ (d - 2) * 2 ^ d * radC (1 / (d : ℝ)) := by positivity
  linarith

/-- The lattice sum of the tail for `d = k + 2` (the form of `sum_radial_exp_le`). -/
private theorem KDecay_sum_tailT_core (k : ℕ) {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 ≤ g)
    (ht : t < 1) :
    ∑ a : Zd (k + 2) L, tailT (k + 2) L g t (zdistInf (k + 2) L a : ℝ) ≤
      KDecay_tailC (k + 2) / (1 - t) := by
  have hu : (0 : ℝ) < 1 - t := by linarith
  have habs : |1 - t| = 1 - t := abs_of_pos hu
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT hL1
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le one_pos hℓ1
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ((k + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hD1 : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast (by omega : 1 ≤ k + 2)
  have hD0 : (0 : ℝ) < D := by linarith
  have hA0 : 0 < (g ^ 2 + (1 - t))⁻¹ := inv_pos.2 (by positivity)
  have hZ0 : 0 ≤ ((L : ℝ) ^ (k + 2) * (1 - t))⁻¹ := by positivity
  -- pointwise bound
  have hpt : ∀ a : Zd (k + 2) L, tailT (k + 2) L g t (zdistInf (k + 2) L a : ℝ) ≤
      (g ^ 2 + (1 - t))⁻¹ * D ^ k *
        ((((zdistD (k + 2) L a : ℝ) + 1) ^ k)⁻¹ *
          Real.exp (-((1 / D) * Real.sqrt ((zdistD (k + 2) L a : ℝ) / ellT L g t)))) +
      ((L : ℝ) ^ (k + 2) * (1 - t))⁻¹ := by
    intro a
    set r : ℝ := (zdistInf (k + 2) L a : ℝ) with hr
    set r1 : ℝ := (zdistD (k + 2) L a : ℝ) with hr1
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hr10 : 0 ≤ r1 := Nat.cast_nonneg _
    have hrr : r1 ≤ D * r := by
      have := zdistD_le_mul_zdistInf (k + 2) L a
      rw [hr1, hr, hD]
      exact_mod_cast this
    -- (i)
    have h1 : (r1 + 1) ^ k ≤ D ^ k * (r + 1) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) k
    have h2 : (((r + 1) ^ k)⁻¹) ≤ D ^ k * (((r1 + 1) ^ k)⁻¹) := by
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    -- (ii)
    have h3 : (1 / D) * Real.sqrt (r1 / ellT L g t) ≤ Real.sqrt (r / ellT L g t) := by
      apply Real.le_sqrt_of_sq_le
      have hs : Real.sqrt (r1 / ellT L g t) ^ 2 = r1 / ellT L g t := Real.sq_sqrt (by positivity)
      rw [mul_pow, hs]
      have he : (1 / D) ^ 2 * (r1 / ellT L g t) = (r1 / D ^ 2) / ellT L g t := by field_simp
      rw [he]
      apply div_le_div_of_nonneg_right _ hℓ0.le
      rw [div_le_iff₀ (by positivity)]
      calc r1 ≤ D * r := hrr
        _ ≤ D * r * D := le_mul_of_one_le_right (by positivity) hD1
        _ = r * D ^ 2 := by ring
    have h4 : Real.exp (-Real.sqrt (r / ellT L g t)) ≤
        Real.exp (-((1 / D) * Real.sqrt (r1 / ellT L g t))) :=
      Real.exp_le_exp.2 (by linarith)
    have he0 : 0 ≤ Real.exp (-Real.sqrt (r / ellT L g t)) := (Real.exp_pos _).le
    have he1 : Real.exp (-Real.sqrt (r / ellT L g t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [Real.sqrt_nonneg (r / ellT L g t)]
    have hBr : BparamR (k + 2) L g t r =
        (g ^ 2 + (1 - t))⁻¹ * ((r + 1) ^ k)⁻¹ + ((L : ℝ) ^ (k + 2) * (1 - t))⁻¹ := by
      simp [BparamR, habs]
    have htail : tailT (k + 2) L g t r =
        ((g ^ 2 + (1 - t))⁻¹ * ((r + 1) ^ k)⁻¹ + ((L : ℝ) ^ (k + 2) * (1 - t))⁻¹) *
          Real.exp (-Real.sqrt (r / ellT L g t)) := by
      unfold tailT
      rw [hBr]
    rw [htail, add_mul]
    refine add_le_add ?_ ?_
    · calc (g ^ 2 + (1 - t))⁻¹ * ((r + 1) ^ k)⁻¹ * Real.exp (-Real.sqrt (r / ellT L g t))
          ≤ (g ^ 2 + (1 - t))⁻¹ * (D ^ k * ((r1 + 1) ^ k)⁻¹) *
              Real.exp (-((1 / D) * Real.sqrt (r1 / ellT L g t))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hA0.le) h4 he0 (by positivity)
        _ = (g ^ 2 + (1 - t))⁻¹ * D ^ k *
            (((r1 + 1) ^ k)⁻¹ * Real.exp (-((1 / D) * Real.sqrt (r1 / ellT L g t)))) := by ring
    · exact mul_le_of_le_one_right hZ0 he1
  -- the sum
  have hrad := sum_radial_exp_le (L := L) k (κ := 1 / D) (ℓ := ellT L g t) (one_div_pos.2 hD0) hℓ1
  have hcardZ : ∑ _a : Zd (k + 2) L, ((L : ℝ) ^ (k + 2) * (1 - t))⁻¹ = (1 - t)⁻¹ := by
    rw [sum_const, card_univ, card_Zd, nsmul_eq_mul]
    push_cast
    field_simp
  have hAl : (g ^ 2 + (1 - t))⁻¹ * ellT L g t ^ 2 ≤ (1 - t)⁻¹ := by
    have h := one_sub_mul_ellT_sq_le (L := L) hg ht
    rw [habs] at h
    rw [← div_eq_inv_mul, inv_eq_one_div, div_le_div_iff₀ (by positivity) hu]
    linarith
  calc ∑ a : Zd (k + 2) L, tailT (k + 2) L g t (zdistInf (k + 2) L a : ℝ)
      ≤ ∑ a : Zd (k + 2) L, ((g ^ 2 + (1 - t))⁻¹ * D ^ k *
        ((((zdistD (k + 2) L a : ℝ) + 1) ^ k)⁻¹ *
          Real.exp (-((1 / D) * Real.sqrt ((zdistD (k + 2) L a : ℝ) / ellT L g t)))) +
        ((L : ℝ) ^ (k + 2) * (1 - t))⁻¹) := sum_le_sum fun a _ => hpt a
    _ = (g ^ 2 + (1 - t))⁻¹ * D ^ k * ∑ a : Zd (k + 2) L,
          ((((zdistD (k + 2) L a : ℝ) + 1) ^ k)⁻¹ *
            Real.exp (-((1 / D) * Real.sqrt ((zdistD (k + 2) L a : ℝ) / ellT L g t)))) +
        (1 - t)⁻¹ := by
        rw [sum_add_distrib, ← mul_sum, hcardZ]
    _ ≤ (g ^ 2 + (1 - t))⁻¹ * D ^ k * (2 ^ (k + 2) * radC (1 / D) * ellT L g t ^ 2) +
        (1 - t)⁻¹ := by
        gcongr
    _ = D ^ k * 2 ^ (k + 2) * radC (1 / D) * ((g ^ 2 + (1 - t))⁻¹ * ellT L g t ^ 2) +
        (1 - t)⁻¹ := by ring
    _ ≤ D ^ k * 2 ^ (k + 2) * radC (1 / D) * (1 - t)⁻¹ + (1 - t)⁻¹ := by
        have : 0 ≤ D ^ k * 2 ^ (k + 2) * radC (1 / D) := by
          have := radC_pos (one_div_pos.2 hD0)
          positivity
        have := mul_le_mul_of_nonneg_left hAl this
        linarith
    _ = KDecay_tailC (k + 2) / (1 - t) := by
        unfold KDecay_tailC
        rw [hD]
        simp only [Nat.add_sub_cancel]
        field_simp

/-- **The lattice sum of the tail**: `Σ_{a ∈ Z_L^d} 𝒯_t(|a|_∞) ≤ C_∞(d) (1-t)⁻¹`, `d ≥ 2`,
uniformly in `L ≥ 1`, `g ≥ 0` and `t < 1` (in particular `g ∈ (0, gmax]`, `t ∈ [0,1)`). -/
theorem KDecay_sum_tailT_le {d L : ℕ} [NeZero L] (hd : 2 ≤ d) {g t : ℝ} (hg : 0 ≤ g)
    (ht : t < 1) :
    ∑ a : Zd d L, tailT d L g t (zdistInf d L a : ℝ) ≤ KDecay_tailC d / (1 - t) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  exact KDecay_sum_tailT_core k hg ht

end RBM.Loop
