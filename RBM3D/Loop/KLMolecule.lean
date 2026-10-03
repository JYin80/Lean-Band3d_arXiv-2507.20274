/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLSumZeroWard
import RBM3D.Loop.PureLoop
import RBM3D.Propagator.Prop5Short

/-!
# The `K`-loop layer, KL8 + KL9: the molecule decay and the sum-zero estimates (`d ≥ 3`)

Ticket T2070.  Names are in `RBM.Loop`; every unpinned helper is `private` and carries the file
stem `KLMolecule`.

* `KLmoleculeAt`, `KLsumZeroAt`: the statements of the pins `KLmoleculePin`, `KLsumZeroPin` of the
  T2004 probe (`64b58eb:RBM3D/Probe/T2004Pins.lean` lines 821-843), verbatim.
* `KLShort_holds`: `KLShort d κ gmax` for every `3 ≤ d`, `0 < κ`, `0 < gmax`, from the merged
  `prop5Short_holds` (`(prop:ThfadC_short)`, `Propagator/Prop5Short.lean`).
* `KLmolecule_holds`: the molecule decay `(eq:molecule-decay)`,
  `|Σ^{(∅)}(t,σ,δ)| ≤ C e^{-c max_{ij}|δ_i - δ_j|}`, every `σ`.  Port of RBM2D
  `Loop/PureLoop.lean:747` (`SigmaPi_empty_shortRange_prec`) at `c9a24cf`: the laminar path bound
  and the tree bound `tree_bound`, with `Z2 L ↦ Zd d L`, the explicit constants of `KLShort`
  instead of `Prop5Hyp` and `UnifDetDom`, and the lattice sum `expC` of `RadialSum` instead of
  `(1 + 2/λ)²`.
* `KLsumZero_holds`: `(eq:Sigma-empty-sum-zero)` at `σ = σ^{(alt)}`, `n` even: the signed sum is
  `O(1 - t)` (merged `KLSigmaPi_alt_sumZero_le`, with `η_t ≤ 1 - t`) and the absolute sum is
  `O(g² + (1 - t))`.  The latter is new (RBM1D and RBM2D have `g = 1`): for a non-constant
  `δ` every labelling of the tree sum has an off-diagonal edge, which carries the `g²` of
  `(prop:ThfadC_short)` (no `1_{a=0}` term); the constant `δ = (x, …, x)` is read off from the
  signed sum.
* Section 7: the compiled instances at `d = 3`, `L = 5`, `g = 1/2`, `E = 0`, `t = 9/10`.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. The pinned statements -/

/-- **Route pin `(eq:molecule-decay)`**: `|Σ^{(∅)}(t,σ,b)| ≤ C e^{-c max|b_i-b_j|}`, every `σ`. -/
def KLmoleculeAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (δ : Fin n → Zd d p.L),
    ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * Real.exp (-(c * (KLmaxDist d p.L δ : ℝ)))

/-- **Route pin `(eq:Sigma-empty-sum-zero)`**, `σ = σ^{(alt)}`, `n` even: the signed sum is
`O(|1-t|)` ([YY_25] Lemma 3.10) and the absolute sum is `O(g² + |1-t|)` ([RBSO1D] Claim 4.30,
cited by the paper; `RBM1D`/`RBM2D` work at `g = 1` and have no analogue; split row KL9 derives it
from the signed estimate and `(prop:ThfadC_short)`). -/
def KLsumZeroAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (x : Zd d p.L),
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x),
        KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (1 - p.t) ∧
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x),
        ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (p.g ^ 2 + (1 - p.t))

/-! ## 2. The laminar structure: the path bound

Port of `RBM2D/Loop/PureLoop.lean:176-296` (`pathSet`, `anc_step`, `path_aux`, `path_le`) at
`c9a24cf`, `Z2 L ↦ Zd d L`, `zdist2 ↦ zdistD`, the laminar API of `KLTree.lean` in place of the
private one of RBM2D.  `dist_bounds` is inlined into `KLMolecule_tree_bound`: for a labelling
consistent with `δ` the leaf distances vanish.  New: `KLMolecule_const_of_edges`,
`KLMolecule_exists_offdiag` (a tree whose edges all have equal labels at their ends is constant). -/

section Path

variable {n : ℕ} [NeZero n] {d L : ℕ} [NeZero L]

private theorem KLMolecule_zdistD_symm (x y : Zd d L) :
    zdistD d L (x - y) = zdistD d L (y - x) := by
  rw [← zdistD_neg d L (x - y), neg_sub]

private theorem KLMolecule_zdistD_tri (x y z : Zd d L) :
    zdistD d L (x - z) ≤ zdistD d L (x - y) + zdistD d L (y - z) := by
  have := zdistD_add_le d L (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

/-- The edges on the path between the nodes `x` and `y`: those above exactly one of them. -/
private def KLMolecule_pathSet (F : Finset (Fin n × Fin n)) (x y : Fin n × Fin n) :
    Finset (Fin n × Fin n) :=
  F.filter fun e => ¬(KLArcLe x e ↔ KLArcLe y e)

private theorem KLMolecule_anc_step {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    {x : Fin n × Fin n} (hx : x ∈ KLnodes F) (hxw : x ≠ KLwholeP n) :
    KLnodePar F x ∈ KLnodes F ∧ KLArcLe x (KLnodePar F x) ∧ ¬KLArcLe (KLnodePar F x) x ∧
      x ∈ F ∧ (F.filter (KLArcLe (KLnodePar F x))).card < (F.filter (KLArcLe x)).card ∧
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
  have hxmem : x ∈ F.filter (KLArcLe x) :=
    mem_filter.2 ⟨hxF, ⟨le_refl _, le_refl _⟩⟩
  have hcard : (F.filter (KLArcLe (KLnodePar F x))).card < (F.filter (KLArcLe x)).card := by
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hxmem] at h1
    have := card_pos.2 ⟨x, hxmem⟩
    omega
  exact ⟨hp, hdp, hpd, hxF, hcard, fun e he hex =>
    ⟨fun h => hmin e (KLmem_nodes_of_mem he) h hex, fun h => KLArcLe.trans hdp h⟩⟩

private theorem KLMolecule_path_aux {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → Zd d L) :
    ∀ m : ℕ, ∀ x ∈ KLnodes F, ∀ y ∈ KLnodes F,
      (F.filter (KLArcLe x)).card + (F.filter (KLArcLe y)).card = m →
      zdistD d L (β x - β y) ≤
        ∑ e ∈ KLMolecule_pathSet F x y, zdistD d L (β e - β (KLnodePar F e)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have key : ∀ x ∈ KLnodes F, ∀ y ∈ KLnodes F,
        (F.filter (KLArcLe x)).card + (F.filter (KLArcLe y)).card = m → x ≠ KLwholeP n →
          ¬KLArcLe y x → zdistD d L (β x - β y) ≤
            ∑ e ∈ KLMolecule_pathSet F x y, zdistD d L (β e - β (KLnodePar F e)) := by
      intro x hx y hy hm hxw hyx
      obtain ⟨hp, hdp, hpd, hxF, hcard, hiff⟩ := KLMolecule_anc_step hF hn hx hxw
      have hih := ih _ (by omega) (KLnodePar F x) hp y hy rfl
      have htri := KLMolecule_zdistD_tri (β x) (β (KLnodePar F x)) (β y)
      have hxn : x ∉ KLMolecule_pathSet F (KLnodePar F x) y := by
        intro h
        exact (mem_filter.1 h).2 ⟨fun h' => absurd h' hpd, fun h' => absurd h' hyx⟩
      have hsub : insert x (KLMolecule_pathSet F (KLnodePar F x) y) ⊆ KLMolecule_pathSet F x y := by
        intro e he
        rcases mem_insert.1 he with rfl | he
        · exact mem_filter.2 ⟨hxF, fun h => hyx (h.1 ⟨le_refl _, le_refl _⟩)⟩
        · obtain ⟨heF, hne⟩ := mem_filter.1 he
          have hex : e ≠ x := by
            rintro rfl; exact hxn he
          exact mem_filter.2 ⟨heF, fun h => hne ((hiff e heF hex).symm.trans h)⟩
      have hs := sum_le_sum_of_subset (f := fun e => zdistD d L (β e - β (KLnodePar F e))) hsub
      rw [sum_insert hxn] at hs
      omega
    intro x hx y hy hm
    by_cases h1 : x ≠ KLwholeP n ∧ ¬KLArcLe y x
    · exact key x hx y hy hm h1.1 h1.2
    by_cases h2 : y ≠ KLwholeP n ∧ ¬KLArcLe x y
    · have := key y hy x hx (by omega) h2.1 h2.2
      have hs : KLMolecule_pathSet F y x = KLMolecule_pathSet F x y := by
        ext e; simp only [KLMolecule_pathSet, mem_filter, iff_comm]
      rw [hs] at this
      rwa [KLMolecule_zdistD_symm]
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
private theorem KLMolecule_path_le {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → Zd d L) {x y : Fin n × Fin n} (hx : x ∈ KLnodes F)
    (hy : y ∈ KLnodes F) :
    zdistD d L (β x - β y) ≤ ∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) :=
  (KLMolecule_path_aux hF hn β _ x hx y hy rfl).trans
    (sum_le_sum_of_subset (filter_subset _ _))

/-- If every internal edge of the tree has equal labels at its two ends, the labelling is
constant on the nodes (the tree is connected). -/
private theorem KLMolecule_const_of_edges {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F)
    (hn : 2 ≤ n) {α : Type*} (β : Fin n × Fin n → α)
    (h : ∀ J ∈ F, β J = β (KLnodePar F J)) : ∀ ν ∈ KLnodes F, β ν = β (KLwholeP n) := by
  have key : ∀ m : ℕ, ∀ ν ∈ KLnodes F, (F.filter (KLArcLe ν)).card = m →
      β ν = β (KLwholeP n) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro ν hν hm
      by_cases hνw : ν = KLwholeP n
      · rw [hνw]
      · obtain ⟨hp, -, -, hνF, hcard, -⟩ := KLMolecule_anc_step hF hn hν hνw
        rw [h ν hνF]
        exact ih _ (by omega) (KLnodePar F ν) hp rfl
  exact fun ν hν => key _ ν hν rfl

/-- A labelling with two different leaf labels has an internal edge with different labels. -/
private theorem KLMolecule_exists_offdiag {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F)
    (hn : 2 ≤ n) {α : Type*} (β : Fin n × Fin n → α) {v w : Fin n}
    (hvw : β (KLleafPar F v) ≠ β (KLleafPar F w)) : ∃ J ∈ F, β J ≠ β (KLnodePar F J) := by
  by_contra hcon
  push Not at hcon
  have h := KLMolecule_const_of_edges hF hn β hcon
  exact hvw ((h _ (KLleafPar_mem F v)).trans (h _ (KLleafPar_mem F w)).symm)

end Path

/-! ## 3. The tree bound

Port of `RBM2D/Loop/PureLoop.lean:312-419` (`tree_bound`) at `c9a24cf`.  Two changes: the leaf
matrices are the identity (the self-energy has no leaf edges), so for a labelling consistent with
`δ` the leaf distances vanish and no `B^n` is paid; and the bound on the product of the edge
entries is a hypothesis `hprod` (a constant `Γ` times `e^{-κ ∑ |edge|}`), so that the same lemma
serves the molecule bound (`Γ = B^{n²}`) and the `g²`-gain for a non-constant `δ`. -/

section TreeBound

variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]

private theorem KLMolecule_tree_bound {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F)
    (hn : 2 ≤ n) (k : ℕ) (δ : Fin n → Zd (k + 2) L)
    (E : ↥F → Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) {κ Γ : ℝ} (hκ : 0 < κ) (hΓ : 0 ≤ Γ)
    (hprod : ∀ β : Fin n × Fin n → Zd (k + 2) L, (∀ v : Fin n, β (KLleafPar F v) = δ v) →
      ∏ J : ↥F, ‖E J (β J.1) (β (KLnodePar F J.1))‖ ≤
        Γ * Real.exp (-(κ * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ))))
    (i j : Fin n) :
    ‖KLtreeValW (k + 2) L F δ (fun _ => 1) E‖ ≤
      Γ * (expC k (κ / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n) *
        Real.exp (-(κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ))) := by
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
    have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
  set lam := κ / (2 * ((n * n : ℕ) : ℝ)) with hlam_def
  have hlam : 0 < lam := by positivity
  set S := expC k lam with hS
  set N := (KLnodes F).card with hNdef
  have hN : N ≤ n * n := by
    have := card_le_univ (KLnodes F)
    simpa using this
  set g : Zd (k + 2) L → ℝ := fun y => Real.exp (-(lam * (zdistD (k + 2) L (δ i - y) : ℝ)))
    with hg
  have hgS : ∑ y, g y ≤ S := sum_exp_decay_centre k hlam (δ i)
  have hg0 : 0 ≤ ∑ y, g y := sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hg1 : 1 ≤ ∑ y, g y := by
    calc (1 : ℝ) = g (δ i) := by simp [hg]
      _ ≤ ∑ y, g y := single_le_sum (f := g) (fun _ _ => (Real.exp_pos _).le) (mem_univ _)
  have hS1 : 1 ≤ S := hg1.trans hgS
  set C0 := Γ * Real.exp (-(κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ))) with hC0def
  have hC0 : 0 ≤ C0 := by positivity
  have hpt : ∀ b : ↥(KLnodes F) → Zd (k + 2) L,
      ‖(∏ v : Fin n, (1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) (δ v)
          (b ⟨KLleafPar F v, KLleafPar_mem F v⟩)) *
        ∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)‖
        ≤ C0 * ∏ ν : ↥(KLnodes F), g (b ν) := by
    intro b
    by_cases hcons : ∀ v : Fin n, b ⟨KLleafPar F v, KLleafPar_mem F v⟩ = δ v
    · obtain ⟨β, hβ⟩ : ∃ β : Fin n × Fin n → Zd (k + 2) L,
          ∀ d (h : d ∈ KLnodes F), b ⟨d, h⟩ = β d :=
        ⟨fun d => if h : d ∈ KLnodes F then b ⟨d, h⟩ else 0, fun d h => by simp [h]⟩
      have hβ' : ∀ ν : ↥(KLnodes F), b ν = β ν.1 := fun ν => hβ ν.1 ν.2
      have hδ : ∀ v : Fin n, β (KLleafPar F v) = δ v := fun v => by
        rw [← hβ _ (KLleafPar_mem F v)]; exact hcons v
      have hij : (zdistD (k + 2) L (δ i - δ j) : ℝ) ≤
          ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) := by
        have h := KLMolecule_path_le hF hn β (KLleafPar_mem F i) (KLleafPar_mem F j)
        rw [hδ i, hδ j] at h
        exact_mod_cast h
      have hnode : ∀ ν : ↥(KLnodes F), (zdistD (k + 2) L (δ i - b ν) : ℝ) ≤
          ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) := by
        intro ν
        have h := KLMolecule_path_le hF hn β (KLleafPar_mem F i) ν.2
        rw [hδ i, ← hβ'] at h
        exact_mod_cast h
      have h1 : ∏ v : Fin n, (1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) (δ v)
          (b ⟨KLleafPar F v, KLleafPar_mem F v⟩) = 1 := by
        refine prod_eq_one fun v _ => ?_
        rw [hcons v, Matrix.one_apply_eq]
      have hE : ∏ J : ↥F, ‖E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)‖
          ≤ Γ * Real.exp (-(κ * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) := by
        simpa only [hβ] using hprod β hδ
      have hexp : Real.exp (-(κ * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ)))
          ≤ Real.exp (-(κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ))) *
            ∏ ν : ↥(KLnodes F), g (b ν) := by
        simp only [hg, ← Real.exp_sum, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have h2 : ∑ ν : ↥(KLnodes F), (zdistD (k + 2) L (δ i - b ν) : ℝ) ≤
            N * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) := by
          calc _ ≤ ∑ _ν : ↥(KLnodes F),
                  ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) :=
                sum_le_sum fun ν _ => hnode ν
            _ = N * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) := by
                rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
        have h3 : (N : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hN
        have hD : (0 : ℝ) ≤ ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        have h4 : lam * ∑ ν : ↥(KLnodes F), (zdistD (k + 2) L (δ i - b ν) : ℝ)
            ≤ κ / 2 * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) := by
          calc _ ≤ lam * (((n * n : ℕ) : ℝ) *
                  ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ)) := by
                gcongr; exact h2.trans (by gcongr)
            _ = κ / 2 * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) := by
                rw [hlam_def]; field_simp
        have h5 : κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ) ≤
            κ / 2 * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hij (by positivity)
        have h6 : ∑ ν : ↥(KLnodes F), -(lam * (zdistD (k + 2) L (δ i - b ν) : ℝ))
            = -(lam * ∑ ν : ↥(KLnodes F), (zdistD (k + 2) L (δ i - b ν) : ℝ)) := by
          rw [mul_sum, sum_neg_distrib]
        rw [h6]
        nlinarith
      rw [h1, one_mul, norm_prod]
      calc _ ≤ Γ * Real.exp (-(κ * ((∑ e ∈ F, zdistD (k + 2) L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) := hE
        _ ≤ Γ * (Real.exp (-(κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ))) *
              ∏ ν : ↥(KLnodes F), g (b ν)) := mul_le_mul_of_nonneg_left hexp hΓ
        _ = C0 * ∏ ν : ↥(KLnodes F), g (b ν) := by rw [hC0def]; ring
    · push Not at hcons
      obtain ⟨v, hv⟩ := hcons
      have h0 : ∏ v : Fin n, (1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) (δ v)
          (b ⟨KLleafPar F v, KLleafPar_mem F v⟩) = 0 :=
        prod_eq_zero (mem_univ v) (Matrix.one_apply_ne (Ne.symm hv))
      rw [h0, zero_mul, norm_zero]
      exact mul_nonneg hC0 (prod_nonneg fun ν _ => (Real.exp_pos _).le)
  have hsum : ∑ b : ↥(KLnodes F) → Zd (k + 2) L, ∏ ν : ↥(KLnodes F), g (b ν)
      = (∑ x, g x) ^ N := by
    have h := Finset.prod_univ_sum (fun _ : ↥(KLnodes F) => (univ : Finset (Zd (k + 2) L)))
      (fun _ x => g x)
    rw [Fintype.piFinset_univ] at h
    rw [← h, prod_const, card_univ, Fintype.card_coe]
  rw [KLtreeValW]
  calc _ ≤ ∑ b : ↥(KLnodes F) → Zd (k + 2) L, C0 * ∏ ν : ↥(KLnodes F), g (b ν) :=
        (norm_sum_le _ _).trans (sum_le_sum fun b _ => hpt b)
    _ = C0 * (∑ x, g x) ^ N := by rw [← mul_sum, hsum]
    _ ≤ C0 * S ^ (n * n) := by
        gcongr
        exact (pow_le_pow_left₀ hg0 hgS N).trans (pow_le_pow_right₀ hS1 hN)
    _ = Γ * S ^ (n * n) * Real.exp (-(κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ))) := by
        rw [hC0def]; ring

end TreeBound

/-! ## 4. `(prop:ThfadC_short)`: `KLShort` is proved, and the edge entries it gives

`KLShort d κ gmax` is `(prop:ThfadC_short)` in the explicit-constant form of the `K`-loop layer.
It follows from the merged `prop5Short_holds` (constants `(d, gmax, κ'')`, `κ'' = √(κ(4-κ))/2 ≤
Im m(E)` for `|E| ≤ 2 - κ`), because `mSigma E s = PropSpin (mE E) s`.  For `κ > 2` the bulk
`|E| ≤ 2 - κ` is empty and the statement is vacuous. -/

section Short

/-- **`KLShort d κ gmax` holds** for every `3 ≤ d`, `0 < κ`, `0 < gmax`: property 5' of
`lem_propTH` is proved (`Propagator/Prop5Short.lean`), so the pins `KLmoleculePin`,
`KLsumZeroPin` (which assume it) hold unconditionally. -/
theorem KLShort_holds (d : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hκ : 0 < κ) (hg : 0 < gmax) :
    KLShort d κ gmax := by
  by_cases hκ2 : κ ≤ 2
  · have hpos : 0 < κ * (4 - κ) := by nlinarith
    have hκ'0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
      have := Real.sqrt_pos.2 hpos
      positivity
    obtain ⟨C, hC, c, hc, H⟩ := prop5Short_holds d gmax (Real.sqrt (κ * (4 - κ)) / 2) hd hg hκ'0
    refine ⟨C, hC, c, hc, fun L hL g hg0 hg1 E hE s t ht0 ht1 a => ?_⟩
    have hE2 : |E| ≤ 2 := by linarith
    have him : Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE E).im := by
      rw [mE_im]
      have h1 : κ * (4 - κ) ≤ 4 - E ^ 2 := by
        nlinarith [sq_abs E, abs_nonneg E, mul_self_le_mul_self (abs_nonneg E) hE]
      have := Real.sqrt_le_sqrt h1
      linarith
    exact H L hL g hg0 hg1 t ht0 ht1 (mE E) (norm_mE hE2) him s a
  · refine ⟨1, one_pos, 1, one_pos, fun L hL g hg0 hg1 E hE s t ht0 ht1 a => ?_⟩
    exfalso
    have := abs_nonneg E
    linarith [not_le.1 hκ2]

/-- The entries of the internal edges `Θ_{t m(s)²} - I` of a tree whose long edges are absent
(equal charges): a bound `B e^{-c|x-y|}` for all `x, y`, and the bound `C_κ g² e^{-c|x-y|}` for
`x ≠ y` (no `1_{a=0}` term).  The constants depend on the constants of `KLShort` and on `gmax`
only (not on `L`, `W`, `g`, `E`, `t`, `s`). -/
private theorem KLMolecule_edge {d : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hshort : KLShort d κ gmax) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ Cκ : ℝ, 0 < Cκ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (p : KLPar κ gmax) (s : Bool),
      (∀ x y : Zd d p.L, ‖(thetaEdge d p.L p.g (mSigma p.E) p.t s s - 1) x y‖ ≤
          B * Real.exp (-(c * (zdistD d p.L (x - y) : ℝ)))) ∧
      (∀ x y : Zd d p.L, x ≠ y → ‖(thetaEdge d p.L p.g (mSigma p.E) p.t s s - 1) x y‖ ≤
          (Cκ * p.g ^ 2) * Real.exp (-(c * (zdistD d p.L (x - y) : ℝ)))) := by
  obtain ⟨Ck, hCk, ck, hck, H⟩ := hshort
  have hB1 : 1 ≤ Ck * (1 + gmax ^ 2) + 1 := by
    have : 0 ≤ Ck * (1 + gmax ^ 2) := by positivity
    linarith
  refine ⟨Ck * (1 + gmax ^ 2) + 1, hB1, Ck, hCk, ck, hck, fun p s => ?_⟩
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hξ : ‖(p.t : ℂ) * (mSigma p.E s * mSigma p.E s)‖ < 1 :=
    norm_mul_mSigma_lt_one hE2 p.ht0 p.ht1 s s
  have htrans : ∀ x y : Zd d p.L,
      Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s)) x y
        = Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s)) 0 (y - x) := by
    intro x y
    have h := Theta_apply_add_right_of_three_le (g := p.g) p.hL hξ 0 (y - x) x
    simpa using h
  have hH : ∀ a : Zd d p.L,
      ‖Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s)) 0 a‖
        ≤ Ck * ((if a = 0 then (1 : ℝ) else 0) + p.g ^ 2 * Real.exp (-ck * (zdistD d p.L a : ℝ))) :=
    fun a => H p.L p.hL p.g p.hg0 p.hg1 p.E p.hE s p.t p.ht0 p.ht1 a
  have hg2 : p.g ^ 2 ≤ gmax ^ 2 := pow_le_pow_left₀ p.hg0.le p.hg1 2
  have hentry : ∀ x y : Zd d p.L, (thetaEdge d p.L p.g (mSigma p.E) p.t s s - 1) x y
      = Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s)) x y
        - (1 : Matrix (Zd d p.L) (Zd d p.L) ℂ) x y := fun x y => by
    rw [Matrix.sub_apply]; rfl
  have hoff : ∀ x y : Zd d p.L, x ≠ y → ‖(thetaEdge d p.L p.g (mSigma p.E) p.t s s - 1) x y‖ ≤
      (Ck * p.g ^ 2) * Real.exp (-(ck * (zdistD d p.L (x - y) : ℝ))) := by
    intro x y hxy
    have hyx : y - x ≠ 0 := fun h => hxy (sub_eq_zero.1 h).symm
    rw [hentry, Matrix.one_apply_ne hxy, sub_zero, htrans]
    refine (hH _).trans ?_
    have hite : (if y - x = 0 then (1 : ℝ) else 0) = 0 := by simp [hyx]
    rw [hite, zero_add, KLMolecule_zdistD_symm y x, neg_mul]
    exact le_of_eq (by ring)
  refine ⟨fun x y => ?_, hoff⟩
  by_cases hxy : x = y
  · subst hxy
    rw [hentry, htrans, sub_self, Matrix.one_apply_eq, zdistD_zero]
    have h0 : ‖Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s)) 0 0‖
        ≤ Ck * (1 + p.g ^ 2) := by
      have := hH 0
      simpa using this
    have h1 : ‖Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s)) 0 0 - 1‖ ≤
        Ck * (1 + gmax ^ 2) + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      nlinarith [mul_le_mul_of_nonneg_left hg2 hCk.le]
    simpa using h1
  · refine (hoff x y hxy).trans ?_
    gcongr
    have : Ck * p.g ^ 2 ≤ Ck * gmax ^ 2 := mul_le_mul_of_nonneg_left hg2 hCk.le
    nlinarith

end Short

/-! ## 5. The molecule decay `(eq:molecule-decay)`

Port of `RBM2D/Loop/PureLoop.lean:687-747` (`SigmaPi_bound`, `SigmaPi_empty_shortRange_prec`) at
`c9a24cf`: for a tree of the layer `π = ∅` (no long edge) every internal edge carries equal
charges, so every entry of `Θ - I` is bounded by `B e^{-c|x-y|}` (`KLMolecule_edge`), and
`KLMolecule_tree_bound` gives `|selfW| ≤ B^{n²} expC^{n²} e^{-(c/2) max|δ_i-δ_j|}`. -/

section Molecule

variable {n : ℕ} [NeZero n] {d L : ℕ} [NeZero L]

omit [NeZero L] in
/-- `∏_J B e^{-κ |edge J|} = B^{|F|} e^{-κ ∑ |edge|}`. -/
private theorem KLMolecule_prod_const_exp {F : Finset (Fin n × Fin n)} (B κ : ℝ)
    (β : Fin n × Fin n → Zd d L) :
    ∏ J : ↥F, (B * Real.exp (-(κ * (zdistD d L (β J.1 - β (KLnodePar F J.1)) : ℝ))))
      = B ^ F.card *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) := by
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_coe, ← Real.exp_sum]
  congr 2
  rw [sum_coe_sort F (fun e => -(κ * (zdistD d L (β e - β (KLnodePar F e)) : ℝ)))]
  simp only [Nat.cast_sum, mul_sum, sum_neg_distrib]

omit [NeZero n] in
private theorem KLMolecule_card_le (F : Finset (Fin n × Fin n)) : F.card ≤ n * n := by
  simpa using card_le_univ F

omit [NeZero L] in
/-- All entries bounded by `B e^{-κ|x-y|}` (`B ≥ 1`): the product over the edges is at most
`B^{n²} e^{-κ ∑ |edge|}`. -/
private theorem KLMolecule_prod_le {F : Finset (Fin n × Fin n)}
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) {B κ : ℝ} (hB : 1 ≤ B)
    (hE : ∀ J x y, ‖E J x y‖ ≤ B * Real.exp (-(κ * (zdistD d L (x - y) : ℝ))))
    (β : Fin n × Fin n → Zd d L) :
    ∏ J : ↥F, ‖E J (β J.1) (β (KLnodePar F J.1))‖ ≤
      B ^ (n * n) *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) := by
  calc ∏ J : ↥F, ‖E J (β J.1) (β (KLnodePar F J.1))‖
      ≤ ∏ J : ↥F, (B * Real.exp (-(κ * (zdistD d L (β J.1 - β (KLnodePar F J.1)) : ℝ)))) :=
        prod_le_prod₀ (fun _ _ => norm_nonneg _) fun J _ => hE J _ _
    _ = B ^ F.card *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) :=
        KLMolecule_prod_const_exp B κ β
    _ ≤ B ^ (n * n) *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (KLMolecule_card_le F))
          (Real.exp_pos _).le

omit [NeZero L] in
/-- The same with one off-diagonal edge: if `β J ≠ β (par J)` for some `J ∈ F`, that edge carries
the bound `ε e^{-κ|x-y|}` for `x ≠ y`, and the product is at most
`(ε/B) B^{n²} e^{-κ ∑ |edge|}`. -/
private theorem KLMolecule_prod_off {F : Finset (Fin n × Fin n)}
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) {B ε κ : ℝ} (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hE : ∀ J x y, ‖E J x y‖ ≤ B * Real.exp (-(κ * (zdistD d L (x - y) : ℝ))))
    (hEoff : ∀ J x y, x ≠ y → ‖E J x y‖ ≤ ε * Real.exp (-(κ * (zdistD d L (x - y) : ℝ))))
    (β : Fin n × Fin n → Zd d L) (hJ : ∃ J ∈ F, β J ≠ β (KLnodePar F J)) :
    ∏ J : ↥F, ‖E J (β J.1) (β (KLnodePar F J.1))‖ ≤
      (ε / B * B ^ (n * n)) *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) := by
  obtain ⟨J0, hJ0F, hJ0⟩ := hJ
  have hB0 : 0 < B := by linarith
  set J0' : ↥F := ⟨J0, hJ0F⟩ with hJ0'
  set f : ↥F → ℝ := fun J => ‖E J (β J.1) (β (KLnodePar F J.1))‖ with hf
  set h : ↥F → ℝ := fun J =>
    B * Real.exp (-(κ * (zdistD d L (β J.1 - β (KLnodePar F J.1)) : ℝ))) with hh
  have hfh : ∀ J, f J ≤ h J := fun J => hE J _ _
  have hf0 : f J0' ≤ ε / B * h J0' := by
    have h1 := hEoff J0' (β J0) (β (KLnodePar F J0)) hJ0
    calc f J0' ≤ ε * Real.exp (-(κ * (zdistD d L (β J0 - β (KLnodePar F J0)) : ℝ))) := h1
      _ = ε / B * h J0' := by
          simp only [hh, hJ0']
          field_simp
  have hh0 : ∀ J, 0 ≤ h J := fun J => by positivity
  have hf00 : ∀ J, 0 ≤ f J := fun J => norm_nonneg _
  have hprod : ∏ J : ↥F, f J ≤ ε / B * ∏ J : ↥F, h J := by
    rw [← mul_prod_erase univ f (mem_univ J0'), ← mul_prod_erase univ h (mem_univ J0')]
    calc f J0' * ∏ J ∈ univ.erase J0', f J
        ≤ (ε / B * h J0') * ∏ J ∈ univ.erase J0', h J :=
          mul_le_mul hf0 (prod_le_prod₀ (fun J _ => hf00 J) fun J _ => hfh J)
            (prod_nonneg fun J _ => hf00 J) (mul_nonneg (div_nonneg hε hB0.le) (hh0 J0'))
      _ = ε / B * (h J0' * ∏ J ∈ univ.erase J0', h J) := by ring
  have hH : ∏ J : ↥F, h J = B ^ F.card *
      Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) :=
    KLMolecule_prod_const_exp B κ β
  calc ∏ J : ↥F, ‖E J (β J.1) (β (KLnodePar F J.1))‖ = ∏ J : ↥F, f J := rfl
    _ ≤ ε / B * ∏ J : ↥F, h J := hprod
    _ = ε / B * (B ^ F.card *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ)))) := by
        rw [hH]
    _ ≤ ε / B * (B ^ (n * n) *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (KLMolecule_card_le F))
            (Real.exp_pos _).le) (div_nonneg hε hB0.le)
    _ = (ε / B * B ^ (n * n)) *
        Real.exp (-(κ * ((∑ e ∈ F, zdistD d L (β e - β (KLnodePar F e)) : ℕ) : ℝ))) := by
        ring

/-- The self-energy of one tree is the tree value with identity leaf matrices. -/
private theorem KLMolecule_selfW_eq {F : Finset (Fin n × Fin n)}
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (δ : Fin n → Zd d L) :
    KLselfW d L F E δ = KLtreeValW d L F δ (fun _ => 1) E := by
  simp only [KLselfW, KLtreeValW, Matrix.one_apply]

/-- **The molecule bound for one tree** (`KLMolecule_tree_bound` at `Γ = B^{n²}`). -/
private theorem KLMolecule_selfW_bound {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F)
    (hn : 2 ≤ n) (k : ℕ) {L : ℕ} [NeZero L] (δ : Fin n → Zd (k + 2) L)
    (E : ↥F → Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) {B κ : ℝ} (hB : 1 ≤ B) (hκ : 0 < κ)
    (hE : ∀ J x y, ‖E J x y‖ ≤ B * Real.exp (-(κ * (zdistD (k + 2) L (x - y) : ℝ))))
    (i j : Fin n) :
    ‖KLselfW (k + 2) L F E δ‖ ≤
      B ^ (n * n) * (expC k (κ / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n) *
        Real.exp (-(κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ))) := by
  rw [KLMolecule_selfW_eq]
  exact KLMolecule_tree_bound hF hn k δ E hκ (by positivity)
    (fun β _ => KLMolecule_prod_le E hB hE β) i j

/-- **The molecule bound for one tree and a non-constant `δ`**: the off-diagonal edge of every
labelling consistent with `δ` carries the factor `ε` (here `ε = C_κ g²`) instead of `B`. -/
private theorem KLMolecule_selfW_bound_nc {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F)
    (hn : 2 ≤ n) (k : ℕ) {L : ℕ} [NeZero L] (δ : Fin n → Zd (k + 2) L)
    (E : ↥F → Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) {B ε κ : ℝ} (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hκ : 0 < κ)
    (hE : ∀ J x y, ‖E J x y‖ ≤ B * Real.exp (-(κ * (zdistD (k + 2) L (x - y) : ℝ))))
    (hEoff : ∀ J x y, x ≠ y →
      ‖E J x y‖ ≤ ε * Real.exp (-(κ * (zdistD (k + 2) L (x - y) : ℝ))))
    (hnc : ∃ v w : Fin n, δ v ≠ δ w) (i j : Fin n) :
    ‖KLselfW (k + 2) L F E δ‖ ≤
      (ε / B * B ^ (n * n)) * (expC k (κ / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n) *
        Real.exp (-(κ / 2 * (zdistD (k + 2) L (δ i - δ j) : ℝ))) := by
  rw [KLMolecule_selfW_eq]
  have hB0 : 0 < B := by linarith
  obtain ⟨v, w, hvw⟩ := hnc
  refine KLMolecule_tree_bound hF hn k δ E hκ (by positivity) (fun β hβ => ?_) i j
  refine KLMolecule_prod_off E hB hε hE hEoff β ?_
  exact KLMolecule_exists_offdiag hF hn β (v := v) (w := w) (by rw [hβ v, hβ w]; exact hvw)

/-- From a bound for every tree of the layer `π = ∅` to a bound for `Σ^{(∅)}`:
`‖∏ m(σ_i)‖ = 1` and `|T_{SP}(σ, ∅)| ≤ |TSP(n)|`. -/
private theorem KLMolecule_SigmaPi_of_tree {g E t : ℝ} (hE2 : |E| ≤ 2) (σ : Fin n → Bool)
    (δ : Fin n → Zd d L) {X : ℝ} (hX : 0 ≤ X)
    (htree : ∀ F ∈ KLTSPlong n σ ∅,
      ‖KLselfW d L F (fun J => thetaEdge d L g (mSigma E) t (σ J.1.1) (σ J.1.2) - 1) δ‖ ≤ X) :
    ‖KLSigmaPi d L g (mSigma E) t σ ∅ δ‖ ≤ ((TSP n).card : ℝ) * X := by
  have hprod : ‖∏ i, mSigma E (σ i)‖ = 1 := by simp [norm_prod, norm_mSigma hE2]
  unfold KLSigmaPi
  rw [norm_mul, hprod, one_mul]
  calc ‖∑ F ∈ KLTSPlong n σ ∅,
        KLselfW d L F (fun J => thetaEdge d L g (mSigma E) t (σ J.1.1) (σ J.1.2) - 1) δ‖
      ≤ ∑ F ∈ KLTSPlong n σ ∅, X := (norm_sum_le _ _).trans (sum_le_sum htree)
    _ = (KLTSPlong n σ ∅).card * X := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (TSP n).card * X := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact_mod_cast card_le_card (filter_subset _ _)

omit [NeZero L] in
/-- A pair of indices realising `max_{i,j} |δ_i - δ_j|`. -/
private theorem KLMolecule_exists_pair (a : Fin n → Zd d L) :
    ∃ i j : Fin n, KLmaxDist d L a = zdistD d L (a i - a j) := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n × Fin n))
    Finset.univ_nonempty fun p : Fin n × Fin n => zdistD d L (a p.1 - a p.2)
  exact ⟨p.1, p.2, hp⟩

omit [NeZero n] in
/-- A tree of the layer `π = ∅` has equal charges at the two ends of every internal edge. -/
private theorem KLMolecule_same_charge {σ : Fin n → Bool} {F : Finset (Fin n × Fin n)}
    (hF : F ∈ KLTSPlong n σ ∅) : ∀ e ∈ F, σ e.1 = σ e.2 := by
  intro e he
  by_contra h
  have hFl : KLFlong F σ = ∅ := (mem_filter.1 hF).2
  have : e ∈ KLFlong F σ := mem_filter.2 ⟨he, h⟩
  rw [hFl] at this
  simp at this

end Molecule

/-! ### The theorem -/

/-- **`(eq:molecule-decay)`**: `|Σ^{(∅)}(t,σ,δ)| ≤ C e^{-c max_{i,j}|δ_i - δ_j|}` for every `σ`,
`n ≥ 3`, `d ≥ 3`; `C, c` depend on `d, n, κ, gmax` only (through the constants of `KLShort`), not
on `L`, `W`, `g`, `E`, `t`, `σ`, `δ`.  Port of RBM2D `SigmaPi_empty_shortRange_prec`
(`Loop/PureLoop.lean:747`) with the explicit constants of property 5'; the `g²` factor of 5' is
absorbed in `B`.  Rate `c = c_κ/2`. -/
theorem KLmolecule_holds :
    ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLShort d κ gmax →
      KLmoleculeAt d n κ gmax := by
  intro d n _ κ gmax hd hn hκ hgm hshort
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨B, hB, Cκ, hCκ, c, hc, hedge⟩ := KLMolecule_edge hκ hshort
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
    have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
  have hlam : 0 < c / (2 * ((n * n : ℕ) : ℝ)) := by positivity
  have hS0 : 0 < expC k (c / (2 * ((n * n : ℕ) : ℝ))) := by unfold expC; positivity
  have hT : 0 < ((TSP n).card : ℝ) := by
    exact_mod_cast card_pos.2 ⟨∅, empty_mem_TSP n⟩
  refine ⟨((TSP n).card : ℝ) * (B ^ (n * n) * (expC k (c / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n)),
    by have : 0 < B := by linarith
       positivity, c / 2, by positivity, fun p σ δ => ?_⟩
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  obtain ⟨i, j, hij⟩ := KLMolecule_exists_pair δ
  have hB0 : 0 < B := by linarith
  have hX : (0 : ℝ) ≤ B ^ (n * n) * (expC k (c / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n) *
      Real.exp (-(c / 2 * (zdistD (k + 2) p.L (δ i - δ j) : ℝ))) := by positivity
  have h := KLMolecule_SigmaPi_of_tree (g := p.g) (t := p.t) hE2 σ δ hX (fun F hF => by
    have hsame := KLMolecule_same_charge hF
    have hFT : F ∈ TSP n := (mem_filter.1 hF).1
    exact KLMolecule_selfW_bound (KLisTSP_of_mem_TSP hFT) (by omega) k δ _ hB hc
      (fun J x y => by
        have := (hedge p (σ J.1.1)).1 x y
        rw [← hsame J.1 J.2]
        exact this) i j)
  rw [hij]
  calc _ ≤ _ := h
    _ = _ := by ring

/-! ## 6. The sum-zero estimates `(eq:Sigma-empty-sum-zero)`

(a) The signed estimate is the merged `KLSigmaPi_alt_sumZero_le` with `η_t ≤ 1 - t`.

(b) The absolute estimate (row KL9; RBM1D/RBM2D have `g = 1` and no analogue; the paper cites
[RBSO1D] Claim 4.30).  Let `S = {δ : δ_0 = x}` and `c₀ = (x, …, x) ∈ S`.

* For `δ ∈ S`, `δ ≠ c₀` (so `δ` is non-constant): every labelling of the tree sum consistent with
  `δ` has an internal edge with different labels, and for `x ≠ y` an entry of `Θ - I` is
  `Θ(x,y)`, bounded by `C_κ g² e^{-c_κ|x-y|}` (property 5', no `1_{a=0}` term).  The tree bound
  of §3 with one factor `ε = C_κ g²` instead of `B` gives
  `|Σ^{(∅)}(δ)| ≤ g² G₁ e^{-(c/2) max|δ_i-δ_j|}`.
* `∑_{δ ∈ S} e^{-(c/2) max|δ_i - δ_j|} ≤ expC^{n-1}` (a product of `n - 1` one-point lattice
  sums), so `∑_{δ ∈ S, δ ≠ c₀} |Σ^{(∅)}(δ)| ≤ g² R`.
* The signed sum is `Σ(c₀) + ∑_{δ ≠ c₀} Σ(δ)`, so `|Σ(c₀)| ≤ |signed| + g² R` and
  `∑_S |Σ| = |Σ(c₀)| + ∑_{δ ≠ c₀} |Σ(δ)| ≤ |signed| + 2 g² R ≤ C_a (1-t) + 2 R g²`. -/

section SumZero

variable {n : ℕ} [NeZero n] {d L : ℕ} [NeZero L]

private theorem KLMolecule_etaT_le {E t : ℝ} (ht : t ≤ 1) : Gauss.etaT E t ≤ 1 - t := by
  have him : (mE E).im ≤ 1 := by
    rw [mE_im, div_le_one (by norm_num)]
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  have h1 : 0 ≤ 1 - t := by linarith
  calc Gauss.etaT E t = (1 - t) * (mE E).im := rfl
    _ ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left him h1
    _ = 1 - t := mul_one _

/-- **(a) The signed estimate**: `‖∑_{δ_0 = x} Σ^{(∅)}(σ^{alt})‖ ≤ C_a (1 - t)`. -/
private theorem KLMolecule_signed {κ gmax : ℝ} (hκ : 0 < κ) (hn : 4 ≤ n) (hev : Even n)
    (p : KLPar κ gmax) (x : Zd d p.L) :
    ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x),
        KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖
      ≤ (2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ)))) * (1 - p.t) := by
  have h := KLSigmaPi_alt_sumZero_le d p.g κ hκ p.L p.hL p.E p.hE p.t ⟨p.ht0, p.ht1⟩ n hn hev x
  have h0 : (⟨0, by omega⟩ : Fin n) = 0 := Fin.ext (by simp)
  simp only [h0] at h
  refine h.trans ?_
  have hA : 0 ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) := by
    have : 0 ≤ gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    positivity
  exact mul_le_mul_of_nonneg_left (KLMolecule_etaT_le p.ht1.le) hA

/-- A sum over the slice `δ_0 = x` of a product of one-point functions. -/
private theorem KLMolecule_sum_slice (x : Zd d L) (f : Zd d L → ℝ) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ 0 = x), ∏ i : Fin n, f (δ i)
      = f x * (∑ y, f y) ^ (n - 1) := by
  classical
  have hS : univ.filter (fun δ : Fin n → Zd d L => δ 0 = x)
      = Fintype.piFinset (fun i : Fin n => if i = 0 then ({x} : Finset (Zd d L)) else univ) := by
    ext δ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = 0
      · simp [hi, h]
      · simp [hi]
    · intro h
      have := h 0
      simpa using this
  have h := Finset.prod_univ_sum
    (fun i : Fin n => if i = 0 then ({x} : Finset (Zd d L)) else univ) (fun _ y => f y)
  rw [hS, ← h]
  have hfac : ∀ i : Fin n,
      ∑ y ∈ (if i = 0 then ({x} : Finset (Zd d L)) else univ), f y
        = if i = 0 then f x else ∑ y, f y := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  simp only [hfac]
  rw [← mul_prod_erase univ _ (mem_univ (0 : Fin n))]
  have h0 : (if (0 : Fin n) = 0 then f x else ∑ y, f y) = f x := by simp
  have h1 : ∀ i ∈ univ.erase (0 : Fin n),
      (if i = 0 then f x else ∑ y, f y) = ∑ y, f y := fun i hi => by
    simp [ne_of_mem_erase hi]
  rw [h0, prod_congr rfl h1, prod_const, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]

/-- `∑_{δ_0 = x} e^{-c max|δ_i - δ_j|} ≤ expC(c/n)^{n-1}`. -/
private theorem KLMolecule_sum_exp_maxDist (k : ℕ) {c : ℝ} (hc : 0 < c) (x : Zd (k + 2) L) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x),
        Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ (expC k (c / n)) ^ (n - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcn : 0 < c / n := by positivity
  set f : Zd (k + 2) L → ℝ := fun y => Real.exp (-(c / n * (zdistD (k + 2) L (x - y) : ℝ)))
    with hf
  have hterm : ∀ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x),
      Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ ∏ i : Fin n, f (δ i) := by
    intro δ hδ
    have hδ0 : δ 0 = x := (mem_filter.1 hδ).2
    simp only [hf, ← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hle : ∀ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ) ≤ KLmaxDist (k + 2) L δ := by
      intro i
      have : zdistD (k + 2) L (δ 0 - δ i) ≤ KLmaxDist (k + 2) L δ :=
        Finset.le_sup (f := fun q : Fin n × Fin n => zdistD (k + 2) L (δ q.1 - δ q.2))
          (mem_univ ((0 : Fin n), i))
      rw [hδ0] at this
      exact_mod_cast this
    have hsum : ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)
        ≤ n * (KLmaxDist (k + 2) L δ : ℝ) := by
      calc _ ≤ ∑ _i : Fin n, (KLmaxDist (k + 2) L δ : ℝ) := sum_le_sum fun i _ => hle i
        _ = n * (KLmaxDist (k + 2) L δ : ℝ) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ i : Fin n, -(c / n * (zdistD (k + 2) L (x - δ i) : ℝ))
        = -(c / n * ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)) := by
      rw [mul_sum, sum_neg_distrib]
    rw [h1]
    have h2 : c / n * ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)
        ≤ c * (KLmaxDist (k + 2) L δ : ℝ) := by
      calc _ ≤ c / n * (n * (KLmaxDist (k + 2) L δ : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum hcn.le
        _ = c * (KLmaxDist (k + 2) L δ : ℝ) := by field_simp
    linarith
  have hfx : f x = 1 := by simp [hf]
  have hfs : ∑ y, f y ≤ expC k (c / n) := sum_exp_decay_centre k hcn x
  have hf0 : 0 ≤ ∑ y, f y := sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc _ ≤ ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x), ∏ i : Fin n, f (δ i) :=
        sum_le_sum hterm
    _ = f x * (∑ y, f y) ^ (n - 1) := KLMolecule_sum_slice x f
    _ ≤ 1 * (expC k (c / n)) ^ (n - 1) := by
        rw [hfx]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf0 hfs _) zero_le_one
    _ = _ := one_mul _

end SumZero

/-- **`(eq:Sigma-empty-sum-zero)`** at `σ = σ^{(alt)}`, `n ≥ 4` even, `d ≥ 3`: with
`S = {δ : δ_0 = x}`,
`‖∑_{δ∈S} Σ^{(∅)}(σ^{alt}, δ)‖ ≤ C (1 - t)` and `∑_{δ∈S} ‖Σ^{(∅)}(σ^{alt}, δ)‖ ≤ C (g² + (1 - t))`;
`C` depends on `d, n, κ, gmax` only (not on `L`, `W`, `g`, `E`, `t`, `x`).  The first estimate is
the merged `KLSigmaPi_alt_sumZero_le`; the second is new (RBM1D and RBM2D have `g = 1`; the paper
cites [RBSO1D] Claim 4.30). -/
theorem KLsumZero_holds :
    ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 4 ≤ n → Even n → 0 < κ → 0 < gmax →
      KLShort d κ gmax → KLsumZeroAt d n κ gmax := by
  intro d n _ κ gmax hd hn hev hκ hgm hshort
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨B, hB, Cκ, hCκ, c, hc, hedge⟩ := KLMolecule_edge hκ hshort
  have hB0 : 0 < B := by linarith
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
    have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hlam0 : 0 < c / (2 * ((n * n : ℕ) : ℝ)) := by positivity
  have hS0 : 0 < expC k (c / (2 * ((n * n : ℕ) : ℝ))) := by unfold expC; positivity
  have hc2n : 0 < c / 2 / n := by positivity
  have hS1 : 0 < expC k (c / 2 / n) := by unfold expC; positivity
  have hT : 0 < ((TSP n).card : ℝ) := by
    exact_mod_cast card_pos.2 ⟨∅, empty_mem_TSP n⟩
  set G1 : ℝ := ((TSP n).card : ℝ) *
    (Cκ / B * B ^ (n * n) * (expC k (c / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n)) with hG1
  set R : ℝ := G1 * (expC k (c / 2 / n)) ^ (n - 1) with hR
  set Ca : ℝ := 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) with hCa
  have hCa0 : 0 ≤ Ca := by
    have : 0 ≤ gapK κ := le_min zero_le_one (Real.sqrt_nonneg _)
    rw [hCa]; positivity
  have hG10 : 0 ≤ G1 := by rw [hG1]; positivity
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  refine ⟨Ca + 2 * R + 1, by linarith, fun p x => ?_⟩
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  set S := univ.filter (fun δ : Fin n → Zd (k + 2) p.L => δ 0 = x) with hS
  set c0 : Fin n → Zd (k + 2) p.L := fun _ => x with hc0
  have hc0S : c0 ∈ S := by simp [hS, hc0]
  -- (i) the non-constant patterns carry the factor `g²`
  have hnc : ∀ δ ∈ S.erase c0,
      ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖
        ≤ p.g ^ 2 * G1 * Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ))) := by
    intro δ hδ
    obtain ⟨hne, hδS⟩ := mem_erase.1 hδ
    have hδ0 : δ 0 = x := (mem_filter.1 hδS).2
    have hnc' : ∃ v w : Fin n, δ v ≠ δ w := by
      by_contra hcon
      push Not at hcon
      exact hne (funext fun i => (hcon i 0).trans hδ0)
    obtain ⟨i, j, hij⟩ := KLMolecule_exists_pair δ
    have hX : 0 ≤ (Cκ * p.g ^ 2 / B * B ^ (n * n)) *
        (expC k (c / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n) *
          Real.exp (-(c / 2 * (zdistD (k + 2) p.L (δ i - δ j) : ℝ))) := by positivity
    have h := KLMolecule_SigmaPi_of_tree (g := p.g) (t := p.t) hE2 (KLsigAlt n) δ hX
      (fun F hF => by
        have hsame := KLMolecule_same_charge hF
        have hFT : F ∈ TSP n := (mem_filter.1 hF).1
        exact KLMolecule_selfW_bound_nc (KLisTSP_of_mem_TSP hFT) (by omega) k δ _ hB
          (ε := Cκ * p.g ^ 2) (by positivity) hc
          (fun J x y => by
            have := (hedge p (KLsigAlt n J.1.1)).1 x y
            rw [← hsame J.1 J.2]
            exact this)
          (fun J x y hxy => by
            have := (hedge p (KLsigAlt n J.1.1)).2 x y hxy
            rw [← hsame J.1 J.2]
            exact this)
          hnc' i j)
    rw [hij]
    calc _ ≤ _ := h
      _ = _ := by rw [hG1]; ring
  -- (ii) the sum over the non-constant patterns
  have hrest : ∑ δ ∈ S.erase c0,
      ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ p.g ^ 2 * R := by
    calc _ ≤ ∑ δ ∈ S.erase c0,
          p.g ^ 2 * G1 * Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ))) :=
          sum_le_sum hnc
      _ ≤ ∑ δ ∈ S, p.g ^ 2 * G1 * Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ))) :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun δ _ _ => by positivity
      _ = p.g ^ 2 * G1 * ∑ δ ∈ S, Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ))) := by
          rw [← mul_sum]
      _ ≤ p.g ^ 2 * G1 * (expC k (c / 2 / n)) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left (KLMolecule_sum_exp_maxDist k (by positivity : 0 < c / 2) x)
            (by positivity)
      _ = p.g ^ 2 * R := by rw [hR]; ring
  -- (iii) the constant pattern `δ = (x, …, x)` is read off from the signed sum
  have habs := add_sum_erase S (fun δ =>
    ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖) hc0S
  have hsig := add_sum_erase S (fun δ =>
    KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ) hc0S
  have hc0norm : ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ c0‖ ≤
      ‖∑ δ ∈ S, KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ +
        ∑ δ ∈ S.erase c0, ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ := by
    have h1 : KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ c0
        = ∑ δ ∈ S, KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ
          - ∑ δ ∈ S.erase c0, KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ := by
      rw [← hsig]; ring
    rw [h1]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have hsigned := KLMolecule_signed (d := k + 2) (n := n) hκ hn hev p x
  have h1t : 0 < 1 - p.t := by linarith [p.ht1]
  have hg2 : 0 ≤ p.g ^ 2 := sq_nonneg _
  refine ⟨hsigned.trans ?_, ?_⟩
  · nlinarith [mul_nonneg hR0 h1t.le]
  · rw [← habs]
    nlinarith [mul_nonneg hCa0 hg2, mul_nonneg hR0 h1t.le, mul_nonneg hg2 hR0]

/-! ## 7. The compiled instances: `d = 3`, `L = 5` (`125` sites), `g = 1/2`, `E = 0`, `t = 9/10`

`κ = gmax = 1` (the bulk `|E| ≤ 1`), `n = 3` (molecule) and `n = 4` (sum-zero), the data
`KLinstPar`, `KLinstσ`, `KLinsta` of `KLTree.lean`.  `KLShort 3 1 1` is `KLShort_holds`, so no
hypothesis is left.  Nondegeneracy: the molecule at `(0,0,0)` has norm `1` (`max|δ_i - δ_j| = 0`,
so the bound there is `1 ≤ C`), and the signed sum is `1/19 ≠ 0`
(`Q(σ^{(alt)}, ∅)(t) = 1 + 2((1 + t)⁻¹ - 1)`), so the absolute sum is at least `1/19`. -/

section Instances

private theorem KLMolecule_mE_zero : mE 0 = Complex.I := by
  simp only [mE]
  have h : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]; push_cast; simp

private theorem KLMolecule_mSigma_sq (s : Bool) : mSigma 0 s * mSigma 0 s = -1 := by
  cases s <;> simp [mSigma, KLMolecule_mE_zero]

/-- `T_SP(σ^{(alt)}, ∅)` for `n = 4`: both diagonals join equal signs. -/
private theorem KLMolecule_TSPlong_four :
    KLTSPlong 4 (KLsigAlt 4) ∅ = {∅, {(0, 2)}, {(1, 3)}} := by
  decide

/-- `Q(σ^{(alt)}, ∅)(t) = 1 + 2((1 + t)⁻¹ - 1)` at `n = 4`, `E = 0` (as in KL7a, `chk_Qlayer`). -/
private theorem KLMolecule_Qlayer_four (t : ℝ) :
    Qlayer (mSigma 0) t (KLsigAlt 4) ∅ = 1 + 2 * ((1 + (t : ℂ))⁻¹ - 1) := by
  rw [Qlayer, KLMolecule_TSPlong_four, sum_insert (by decide), sum_insert (by decide),
    sum_singleton]
  have h0 : KLsigAlt 4 0 = true := rfl
  have h1 : KLsigAlt 4 1 = false := rfl
  have h2 : KLsigAlt 4 2 = true := rfl
  have h3 : KLsigAlt 4 3 = false := rfl
  simp only [prod_empty, prod_singleton, edgeR, h0, h1, h2, h3, KLMolecule_mSigma_sq]
  ring

/-- `T_SP(σ, ∅)` at `n = 3`, `σ = (+,-,+)`: the star only. -/
private theorem KLMolecule_TSPlong_three : KLTSPlong 3 KLinstσ ∅ = {∅} := by
  decide

/-- The molecule at the constant pattern `(0,0,0)`, `n = 3`: `‖Σ^{(∅)}‖ = 1`
(`Σ^{(∅)} = ∏ m · 1_{δ_0 = δ_1 = δ_2}`). -/
theorem KLMolecule_inst_molecule_norm :
    ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun _ => 0)‖ = 1 := by
  have hprod : ‖∏ i, mSigma 0 (KLinstσ i)‖ = 1 := by
    simp [norm_prod, norm_mSigma (show |(0 : ℝ)| ≤ 2 by norm_num)]
  unfold KLSigmaPi
  rw [norm_mul, hprod, one_mul, KLMolecule_TSPlong_three, sum_singleton,
    KLMolecule_selfW_eq, KLtreeValW_empty]
  simp [Matrix.one_apply]

/-- **Instance of `KLmolecule_holds`** (the probe's `KLinst_molecule`; the pin is replaced by
`KLmolecule_holds` and the hypothesis `KLShort 3 1 1` by `KLShort_holds`): `n = 3`,
`σ = (+,-,+)`, `δ = (0, 1, 2)`; and the same `C, c` at the constant pattern `δ = (0,0,0)`, where
`‖Σ^{(∅)}‖ = 1`, so `C ≥ 1`. -/
theorem KLMolecule_inst_molecule :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ KLinsta‖
        ≤ C * Real.exp (-(c * (KLmaxDist 3 5 KLinsta : ℝ))) ∧
      ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun _ => 0)‖ = 1 ∧
      ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun _ => 0)‖
        ≤ C * Real.exp (-(c * (KLmaxDist 3 5 (fun _ : Fin 3 => (0 : Zd 3 5)) : ℝ))) := by
  obtain ⟨C, hC, c, hc, h⟩ := KLmolecule_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos
    one_pos (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos)
  exact ⟨C, hC, c, hc, h KLinstPar KLinstσ KLinsta, KLMolecule_inst_molecule_norm,
    h KLinstPar KLinstσ (fun _ => 0)⟩

/-- The signed sum of the instance is `Q(σ^{(alt)}, ∅)(9/10) = 1/19`
(`SumZero_sum_slice_alt` of KL7a, `L = 5`). -/
theorem KLMolecule_inst_signed_val :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
      KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ = 1 / 19 := by
  have h := SumZero_sum_slice_alt 3 (1 / 2) 1 one_pos 5 (by norm_num) 0 (by norm_num) (9 / 10)
    ⟨by norm_num, by norm_num⟩ 4 le_rfl (by decide) 0
  have h0 : (⟨0, by omega⟩ : Fin 4) = 0 := rfl
  simp only [h0] at h
  rw [h, KLMolecule_Qlayer_four]
  push_cast
  norm_num

/-- **Instance of `KLsumZero_holds`** (the probe's `KLinst_sumZero`; the pin is replaced by
`KLsumZero_holds` and the hypothesis `KLShort 3 1 1` by `KLShort_holds`): `n = 4`,
`σ = σ^{(alt)}`, `x = 0`; the signed sum is `1/19` (so the bound is not `0 ≤ B`), and the absolute
sum is at least `1/19`. -/
theorem KLMolecule_inst_sumZero :
    ∃ C : ℝ, 0 < C ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ = 1 / 19 ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ ≤ C * (1 - 9 / 10) ∧
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
          ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖
        ≤ C * ((1 / 2) ^ 2 + (1 - 9 / 10)) := by
  obtain ⟨C, hC, h⟩ := KLsumZero_holds 3 4 1 1 (by norm_num) (by norm_num) ⟨2, by norm_num⟩
    one_pos one_pos (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos)
  have h0 := h KLinstPar 0
  refine ⟨C, hC, ?_, h0⟩
  rw [KLMolecule_inst_signed_val]
  simp

/-- A second parameter point on the boundary of the range `KLPar 1 1`: `g = gmax = 1`,
`|E| = 2 - κ = 1`, `t = 99/100`, `L = 3` (`27` sites), `W = 1`. -/
private noncomputable def KLMolecule_parEdge : KLPar 1 1 where
  L := 3
  W := 1
  hL := le_refl _
  hW := le_refl _
  g := 1
  hg0 := one_pos
  hg1 := le_refl _
  E := 1
  hE := by norm_num
  t := 99 / 100
  ht0 := by norm_num
  ht1 := by norm_num

/-- The boundary point `(g, E) = (gmax, 2 - κ)`, `n = 6`, `σ = σ^{(alt)}`, `x = 0`; the molecule
at `δ = (0, …, 0)` and the three estimates of `KLsumZero_holds`. -/
example :
    (∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ‖KLSigmaPi 3 3 1 (mSigma 1) (99 / 100) (KLsigAlt 6) ∅ (fun _ => 0)‖
        ≤ C * Real.exp (-(c * (KLmaxDist 3 3 (fun _ : Fin 6 => (0 : Zd 3 3)) : ℝ)))) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 6 → Zd 3 3 => δ 0 = 0),
          KLSigmaPi 3 3 1 (mSigma 1) (99 / 100) (KLsigAlt 6) ∅ δ‖ ≤ C * (1 - 99 / 100) ∧
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin 6 → Zd 3 3 => δ 0 = 0),
          ‖KLSigmaPi 3 3 1 (mSigma 1) (99 / 100) (KLsigAlt 6) ∅ δ‖ ≤ C * (1 ^ 2 + (1 - 99 / 100))) := by
  have hS := KLShort_holds 3 1 1 (by norm_num) one_pos one_pos
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, c, hc, h⟩ := KLmolecule_holds 3 6 1 1 (by norm_num) (by norm_num) one_pos
      one_pos hS
    exact ⟨C, hC, c, hc, h KLMolecule_parEdge (KLsigAlt 6) (fun _ => 0)⟩
  · obtain ⟨C, hC, h⟩ := KLsumZero_holds 3 6 1 1 (by norm_num) (by norm_num) ⟨3, by norm_num⟩
      one_pos one_pos hS
    exact ⟨C, hC, h KLMolecule_parEdge 0⟩

/-- Other loop lengths and another bulk parameter: `n = 4` and the odd `n = 5` for the molecule,
`n = 8` for the sum-zero estimates, `κ = 1/2`, `gmax = 2`. -/
example : KLShort 3 (1 / 2) 2 := KLShort_holds 3 (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)

example : KLmoleculeAt 3 4 1 1 :=
  KLmolecule_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos
    (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos)

example : KLmoleculeAt 3 5 (1 / 2) 2 :=
  KLmolecule_holds 3 5 (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (KLShort_holds 3 (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num))

example : KLsumZeroAt 3 8 (1 / 2) 2 :=
  KLsumZero_holds 3 8 (1 / 2) 2 (by norm_num) (by norm_num) ⟨4, by norm_num⟩ (by norm_num)
    (by norm_num) (KLShort_holds 3 (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num))

end Instances

end RBM.Loop
