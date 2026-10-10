/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KSumZeroA
import RBM3D.BA.KPure
import RBM3D.BA.KMolecule
import RBM3D.Loop.KLIndStepA

/-!
# Stage K, row K08b: the absolute weighted clause of the BA molecule weight and `SigSumZeroAbs`

Ticket T2391 (design BA-DK, `docs/reports/T2360-design.md` §3 (c), §5 row K08b).  The argument was
written and audited in the design gate of T2385 (`docs/reports/T2385-prove.md` (a+), "Absolute
weighted clause (K08b)").  Paper: `(eq:Sigma-empty-sum-zero)` and `(eq:molecule-decay)`
(`A_deterministic_estimates.tex:691-734`).  The BA twin of the band `Loop/KLIndStepA.lean` §5
(`KLIndStepA_nc_pointwise`, `KLsumZero_weighted`, `sigSumZeroAbs_band`).

1. `KSumZeroB_unequal_edge` (B1): for a labelling `β` of the slots of a cactus whose leaf labels
   are not constant, either a chord has `β (In J) ≠ β (Out J)` or a node has two `M`-edges with
   unequal ends.
2. `baSig_nc_pointwise` (B2): `|Σ^{(∅)}(σ, δ)| ≤ G g² e^{-c max_{i,j} |δ_i - δ_j|}` for every `σ`
   and every non-constant `δ`, uniformly in the family `(L, g ≤ Λ, E, m, t ≤ 1)`.
3. `baSig_weighted` (B3): for every `Q` and every alternating `σ`, on every slice `δ_r = x`,
   `Σ |Σ^{(∅)}(δ)| (max |δ_i - δ_j| + 1)^Q ≤ C (g² + (1 - t))` (the proof of `KLsumZero_weighted`,
   with B2 for `KLIndStepA_nc_pointwise` and the signed clause `baSig_signed_sum` of K08a).
4. `baSig_sumZeroAbs` (B4): the K-b predicate `SigSumZeroAbs d n L g t (BASig d n L g E m t)`,
   under `3 ≤ n`, `t i < 1` (the ranges of `sigSumZeroAbs_band` and of its consumers;
   `SigSumZeroAbs` itself, which is false at `n = 2`, is untouched).
5. Compiled nonempty instances at the flow point `P` of `(d, L) = (3, 4)`, `n = 4`.

Public: the declarations above; every other helper is `private` with the stem `KSumZeroB_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. B1: an unequal edge in every cactus labelling that is not constant on the leaves -/

section Cycle

/-- A cycle with at most one unequal edge has none: if `b s ≠ b (nx s)` and every other element of the orbit of `s` has
`b s' = b (nx s')`, then going once round the orbit `nx s, nx² s, …, s` shows `b (nx s) = b s`. -/
private theorem KSumZeroB_cycle {α β X : Type*} (nx : α → α) (nd : α → β) (hnd : ∀ s, nd (nx s) = nd s)
    (horb : ∀ s t, nd s = nd t → ∃ k : ℕ, nx^[k] s = t) (b : α → X) {s : α} (hs : b s ≠ b (nx s)) :
    ∃ s' : α, s' ≠ s ∧ nd s' = nd s ∧ b s' ≠ b (nx s') := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∃ k : ℕ, nx^[k] (nx s) = s := horb (nx s) s (hnd s)
  have hk₀spec : nx^[Nat.find hex] (nx s) = s := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, nx^[j] (nx s) ≠ s := fun j hj => Nat.find_min hex hj
  have hnodeIter : ∀ j : ℕ, nd (nx^[j] (nx s)) = nd s := by
    intro j
    induction j with
    | zero => exact hnd s
    | succ j ih => rw [Function.iterate_succ_apply', hnd, ih]
  have hchain : ∀ j : ℕ, j ≤ Nat.find hex → b (nx s) = b (nx^[j] (nx s)) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have h2 := hcon (nx^[j] (nx s)) (hmin j (by omega)) (hnodeIter j)
      rw [Function.iterate_succ_apply', ← h2]
      exact ih (by omega)
  have h3 := hchain (Nat.find hex) le_rfl
  rw [hk₀spec] at h3
  exact hs h3.symm

end Cycle

section Combinatorics

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **B1.**  A labelling `β` of the slots of the cactus of `F` (`KLIsTSP F`, `2 ≤ n`) whose leaf labels `β (leaf v)` are not
all equal has either a chord `J` with `β (In J) ≠ β (Out J)`, or a node with two distinct `M`-edges `s — next s` with unequal
ends.  If every chord and every node cycle (`BAnextSlot_orbit`) had equal ends then every edge would, the total length is
`0` and `baSlot_path_le` makes `β` constant.  An unequal `M`-edge is never alone in its node: a cycle closes. -/
theorem KSumZeroB_unequal_edge {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (β : BAslot F → Zd d L) (hnc : ∃ v w : Fin n, β (BAslotLeaf F v) ≠ β (BAslotLeaf F w)) :
    (∃ J : ↥F, β (BAslotIn F J) ≠ β (BAslotOut F J)) ∨
      ∃ s s' : BAslot F, s ≠ s' ∧ BAslotNode F s = BAslotNode F s' ∧
        β s ≠ β (BAnextSlot F s) ∧ β s' ≠ β (BAnextSlot F s') := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hch, hM⟩ := hcon
  have hnext : ∀ s, β s = β (BAnextSlot F s) := by
    intro s
    by_contra hs
    obtain ⟨s', hne, hnd, hs'⟩ := KSumZeroB_cycle (BAnextSlot F) (BAslotNode F) (BAslotNode_nextSlot F)
      (fun s t h => (BAnextSlot_orbit hF hn s t).1 h) β hs
    exact hs (hM s' s hne hnd hs')
  have hall : ∀ s t : BAslot F, β s = β t := by
    intro s t
    have h := baSlot_path_le hF hn β s t
    have hz : ∑ e : ↥F ⊕ BAslot F, zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) = 0 := by
      refine Finset.sum_eq_zero fun e _ => ?_
      rcases e with J | s
      · change zdistD d L (β (BAslotIn F J) - β (BAslotOut F J)) = 0
        rw [hch J, sub_self, zdistD_zero]
      · change zdistD d L (β s - β (BAnextSlot F s)) = 0
        rw [← hnext s, sub_self, zdistD_zero]
    rw [hz] at h
    exact sub_eq_zero.1 ((zdistD_eq_zero_iff d L).1 (Nat.le_zero.1 h))
  obtain ⟨v, w, hvw⟩ := hnc
  exact hvw (hall _ _)

end Combinatorics

/-! ## 2. The product of the edge entries with the gain `g²` -/

section Prod

/-- The gain in a product: if `f ≤ h` termwise (`f, h ≥ 0`) and one factor has the extra gain `g²`, or two factors
have the extra gain `g` each, then `∏ f ≤ g² ∏ h`. -/
private theorem KSumZeroB_prod_gain {Eg : Type*} [Fintype Eg] (f h : Eg → ℝ) {g : ℝ}
    (hf : ∀ e, 0 ≤ f e) (hh : ∀ e, 0 ≤ h e) (hg : 0 ≤ g) (hle : ∀ e, f e ≤ h e)
    (hdis : (∃ e, f e ≤ h e * g ^ 2) ∨ ∃ e e', e ≠ e' ∧ f e ≤ h e * g ∧ f e' ≤ h e' * g) :
    ∏ e, f e ≤ (∏ e, h e) * g ^ 2 := by
  classical
  rcases hdis with ⟨e, he⟩ | ⟨e, e', hne, he, he'⟩
  · rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e),
      ← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ e)]
    have hrest : ∏ x ∈ Finset.univ.erase e, f x ≤ ∏ x ∈ Finset.univ.erase e, h x :=
      Finset.prod_le_prod₀ (fun x _ => hf x) (fun x _ => hle x)
    calc f e * ∏ x ∈ Finset.univ.erase e, f x
        ≤ (h e * g ^ 2) * ∏ x ∈ Finset.univ.erase e, h x :=
          mul_le_mul he hrest (Finset.prod_nonneg fun x _ => hf x) (mul_nonneg (hh e) (sq_nonneg g))
      _ = (h e * ∏ x ∈ Finset.univ.erase e, h x) * g ^ 2 := by ring
  · have he'mem : e' ∈ Finset.univ.erase e := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ e'⟩
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e), ← Finset.mul_prod_erase _ f he'mem,
      ← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ e), ← Finset.mul_prod_erase _ h he'mem]
    have hrest : ∏ x ∈ (Finset.univ.erase e).erase e', f x ≤ ∏ x ∈ (Finset.univ.erase e).erase e', h x :=
      Finset.prod_le_prod₀ (fun x _ => hf x) (fun x _ => hle x)
    have hP : 0 ≤ ∏ x ∈ (Finset.univ.erase e).erase e', f x := Finset.prod_nonneg fun x _ => hf x
    calc f e * (f e' * ∏ x ∈ (Finset.univ.erase e).erase e', f x)
        ≤ (h e * g) * ((h e' * g) * ∏ x ∈ (Finset.univ.erase e).erase e', h x) :=
          mul_le_mul he (mul_le_mul he' hrest hP (mul_nonneg (hh e') hg)) (mul_nonneg (hf e') hP)
            (mul_nonneg (hh e) hg)
      _ = (h e * (h e' * ∏ x ∈ (Finset.univ.erase e).erase e', h x)) * g ^ 2 := by ring

/-- `∏_e B e^{-r z_e} = B^{|E|} e^{-r Σ z_e}` (a copy of the private `KPure_prod_const_exp`, `BA/KPure.lean:399`). -/
private theorem KSumZeroB_prod_exp {Eg : Type*} [Fintype Eg] (z : Eg → ℕ) (B r : ℝ) :
    ∏ e, (B * Real.exp (-(r * (z e : ℝ)))) =
      B ^ Fintype.card Eg * Real.exp (-(r * ((∑ e, z e : ℕ) : ℝ))) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  simp only [Nat.cast_sum, Finset.mul_sum, Finset.sum_neg_distrib]

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero L] [NeZero n] in
/-- The number of edges of the cactus of `F` is at most `n + 3 n²` (`n + 3 |F|`, `|F| ≤ n²`). -/
private theorem KSumZeroB_card_edges (F : Finset (Fin n × Fin n)) :
    Fintype.card (↥F ⊕ BAslot F) ≤ n + 3 * (n * n) := by
  rw [Fintype.card_sum, Fintype.card_coe, BAslot_card]
  have : F.card ≤ n * n := by simpa using Finset.card_le_univ F
  omega

/-- **The product of the edge entries with the gain `g²`**: let every edge entry of the cactus of `F` be at most
`B e^{-r |x-y|}` (`hM`, `hΘ`; the chords are short, `hsame`), an off-diagonal `M`-entry at most `B g e^{-r |x-y|}`
(`hMo`) and an off-diagonal short chord at most `B g² e^{-r |x-y|}` (`hΘo`).  At every labelling `β` of the slots
whose leaf labels are not constant (B1: an unequal chord or two unequal `M`-edges),
`∏_e |E_e(β src, β tgt)| ≤ B^{n+3n²} g² e^{-r T(β)}`, `T(β)` the total edge length. -/
private theorem KSumZeroB_prod_le {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (hsame : ∀ e ∈ F, σ e.1 = σ e.2)
    {B r g : ℝ} (hB : 1 ≤ B) (hg : 0 ≤ g)
    (hM : ∀ (s : Bool) (x y : Zd d L), ‖M s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘ : ∀ (s : Bool) (x y : Zd d L),
      ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hMo : ∀ (s : Bool) (x y : Zd d L), x ≠ y →
      ‖M s x y‖ ≤ B * g * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘo : ∀ (s : Bool) (x y : Zd d L), x ≠ y →
      ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * g ^ 2 * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (β : BAslot F → Zd d L) (hnc : ∃ v w : Fin n, β (BAslotLeaf F v) ≠ β (BAslotLeaf F w)) :
    ∏ e : ↥F ⊕ BAslot F, ‖BACactusValEdgeW M t F σ e (β (BACactusValSrc F e)) (β (BACactusValTgt F e))‖ ≤
      B ^ (n + 3 * (n * n)) * g ^ 2 * Real.exp (-(r * ((∑ e : ↥F ⊕ BAslot F,
        zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) : ℕ) : ℝ))) := by
  classical
  have hB0 : 0 < B := by linarith
  set z : ↥F ⊕ BAslot F → ℕ := fun e => zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) with hz
  set f : ↥F ⊕ BAslot F → ℝ :=
    fun e => ‖BACactusValEdgeW M t F σ e (β (BACactusValSrc F e)) (β (BACactusValTgt F e))‖ with hf
  set h : ↥F ⊕ BAslot F → ℝ := fun e => B * Real.exp (-(r * (z e : ℝ))) with hh
  have hle : ∀ e, f e ≤ h e := by
    rintro (J | s)
    · change ‖((t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) (β (BAslotIn F J)) (β (BAslotOut F J))‖ ≤
        B * Real.exp (-(r * (zdistD d L (β (BAslotIn F J) - β (BAslotOut F J)) : ℝ)))
      rw [Matrix.smul_apply, smul_eq_mul, ← hsame J.1 J.2]
      exact hΘ _ _ _
    · exact hM _ _ _
  have hdis : (∃ e, f e ≤ h e * g ^ 2) ∨ ∃ e e', e ≠ e' ∧ f e ≤ h e * g ∧ f e' ≤ h e' * g := by
    rcases KSumZeroB_unequal_edge hF hn β hnc with ⟨J, hJ⟩ | ⟨s, s', hss', -, hs, hs'⟩
    · left
      refine ⟨Sum.inl J, ?_⟩
      change ‖((t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) (β (BAslotIn F J)) (β (BAslotOut F J))‖ ≤
        B * Real.exp (-(r * (zdistD d L (β (BAslotIn F J) - β (BAslotOut F J)) : ℝ))) * g ^ 2
      rw [Matrix.smul_apply, smul_eq_mul, ← hsame J.1 J.2]
      calc _ ≤ B * g ^ 2 * Real.exp (-(r * (zdistD d L (β (BAslotIn F J) - β (BAslotOut F J)) : ℝ))) :=
            hΘo _ _ _ hJ
        _ = _ := by ring
    · right
      refine ⟨Sum.inr s, Sum.inr s', fun hss => hss' (Sum.inr.inj hss), ?_, ?_⟩
      · change ‖M (BAMcharge F σ s) (β s) (β (BAnextSlot F s))‖ ≤
          B * Real.exp (-(r * (zdistD d L (β s - β (BAnextSlot F s)) : ℝ))) * g
        calc _ ≤ B * g * Real.exp (-(r * (zdistD d L (β s - β (BAnextSlot F s)) : ℝ))) := hMo _ _ _ hs
          _ = _ := by ring
      · change ‖M (BAMcharge F σ s') (β s') (β (BAnextSlot F s'))‖ ≤
          B * Real.exp (-(r * (zdistD d L (β s' - β (BAnextSlot F s')) : ℝ))) * g
        calc _ ≤ B * g * Real.exp (-(r * (zdistD d L (β s' - β (BAnextSlot F s')) : ℝ))) := hMo _ _ _ hs'
          _ = _ := by ring
  have hmain := KSumZeroB_prod_gain f h (fun e => norm_nonneg _) (fun e => by positivity) hg hle hdis
  have hprodh : ∏ e, h e = B ^ Fintype.card (↥F ⊕ BAslot F) * Real.exp (-(r * ((∑ e, z e : ℕ) : ℝ))) :=
    KSumZeroB_prod_exp z B r
  have hpow : B ^ Fintype.card (↥F ⊕ BAslot F) ≤ B ^ (n + 3 * (n * n)) :=
    pow_le_pow_right₀ hB (KSumZeroB_card_edges F)
  calc ∏ e, f e ≤ (∏ e, h e) * g ^ 2 := hmain
    _ = (B ^ Fintype.card (↥F ⊕ BAslot F) * g ^ 2) * Real.exp (-(r * ((∑ e, z e : ℕ) : ℝ))) := by
      rw [hprodh]; ring
    _ ≤ (B ^ (n + 3 * (n * n)) * g ^ 2) * Real.exp (-(r * ((∑ e, z e : ℕ) : ℝ))) := by
      gcongr

end Prod

end RBM.BA
