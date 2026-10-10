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

/-- A cycle with at most one unequal edge has none: if `b s ≠ b (nx s)` and every other slot `s'` of the node of `s`
(`nd s' = nd s`) has `b s' = b (nx s')`, then going once round the cycle `nx s, nx² s, …, s` (`horb`: one cycle per
node) shows `b (nx s) = b s`, a contradiction. -/
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

/-! ## 3. B2: the pointwise bound with the gain `g²` for a non-constant `δ` -/

section Pointwise

variable {d : ℕ} {Λ κ : ℝ} {L : ℕ} [NeZero L] {g : ℝ} {E : ℝ} {m : ℂ}

/-- `Θ^{(s,s')}` is invariant under the translation `x ↦ x + c` when every `M(σ)` is (a copy of the private
`KPure_theta_shift`, `BA/KPure.lean:71`). -/
private theorem KSumZeroB_theta_shift (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (s s' : Bool) (x y c : Zd d L) :
    BAThetaOf M t s s' (x + c) (y + c) = BAThetaOf M t s s' x y := by
  have hQ : ∀ x y, BAMssOf M s s' (x + c) (y + c) = BAMssOf M s s' x y := fun x y => by
    simp only [BAMssOf, Matrix.of_apply, hM]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s').submatrix (Equiv.addRight c)
      (Equiv.addRight c) = 1 - (t : ℂ) • BAMssOf M s s' := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Equiv.coe_addRight, add_left_inj, hQ]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s')
    (Equiv.addRight c) (Equiv.addRight c)
  rw [hA] at h2
  unfold BAThetaOf PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- `|M(σ)_{ab}| = |M^{(B)}_{ab}|` (a copy of the private `KInduct_norm_sigma`, `BA/KInduct.lean:156`). -/
private theorem KSumZeroB_norm_sigma (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b‖ = ‖BAMB d L g (E : ℂ) m a b‖ := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.norm_conj]
    rw [BAMB_symm d L g (E : ℂ) m b a]
  · simp only [BAMsigma, ite_true]

/-- **An off-diagonal short chord carries `g²`**: `|t Θ_t^{(s,s)}(x,y)| ≤ B g² e^{-r |x-y|}` for `x ≠ y`, `0 ≤ t ≤ 1`
(`(prop:ThfadC_short)`, `baProp5s_of_real`, with no `1_{a=0}` term; `B = baPureB`, `r = baPureRate`, `r ≤ c_s`,
`C₅ ≤ B`). -/
private theorem KSumZeroB_chord_off (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : 3 ≤ L) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : Bool) {x y : Zd d L}
    (hxy : x ≠ y) :
    ‖(t : ℂ) * BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y‖ ≤
      baPureB d Λ κ * g ^ 2 * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))) := by
  have hd0 : 0 < d := by omega
  have hrs : baPureRate d Λ κ ≤ BAp5s_rate d Λ κ := min_le_right _ _
  have hBC : BAp5s_C d Λ κ * (1 + Λ ^ 2) ≤ baPureB d Λ κ := le_max_right _ _
  have hC := BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hCB : BAp5s_C d Λ κ ≤ baPureB d Λ κ :=
    (le_mul_of_one_le_right hC.le (by nlinarith [sq_nonneg Λ])).trans hBC
  have hshift : BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y =
      BATheta d L g E m t s s 0 (y - x) := by
    have h := KSumZeroB_theta_shift (BAMsigma d L (BAMB d L g (E : ℂ) m))
      (fun σ x y c => BAMsigma_shift d L g (E : ℂ) m σ x y c) t s s 0 (y - x) x
    rw [zero_add, sub_add_cancel] at h
    exact h
  have h5 := baProp5s_of_real d L hL (by omega) Λ g κ E m hΛ hg hgΛ hκ hr t ht0 ht1 s (y - x)
  have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  simp only [hyx, ite_false, zero_add] at h5
  have hzc : zdistD d L (x - y) = zdistD d L (y - x) := by rw [← zdistD_neg d L (x - y), neg_sub]
  rw [hzc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, hshift]
  set z : ℝ := (zdistD d L (y - x) : ℝ) with hz
  have hz0 : 0 ≤ z := Nat.cast_nonneg _
  have hexp : Real.exp (-BAp5s_rate d Λ κ * z) ≤ Real.exp (-(baPureRate d Λ κ * z)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  calc t * ‖BATheta d L g E m t s s 0 (y - x)‖ ≤ ‖BATheta d L g E m t s s 0 (y - x)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht1
    _ ≤ BAp5s_C d Λ κ * (g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * z)) := h5
    _ ≤ baPureB d Λ κ * (g ^ 2 * Real.exp (-(baPureRate d Λ κ * z))) :=
        mul_le_mul hCB (mul_le_mul_of_nonneg_left hexp hg2) (by positivity) (hC.le.trans hCB)
    _ = baPureB d Λ κ * g ^ 2 * Real.exp (-(baPureRate d Λ κ * z)) := by ring

/-- **An off-diagonal `M`-entry carries `g`**: `|M(σ)_{xy}| ≤ A^{1/2} g e^{-r |x-y|}` for `x ≠ y`
(`BAK_off_le`: `|M_{xy}|² = K_{xy} ≤ A g² e^{-2 c₀ |x-y|}`, `A = BAp5s_A`, `r ≤ c₀`). -/
private theorem KSumZeroB_M_off (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : 3 ≤ L) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hr : BAReal d L g κ E m) (σ : Bool) {x y : Zd d L} (hxy : x ≠ y) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ ≤
      Real.sqrt (BAp5s_A d Λ κ) * g * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))) := by
  have hd0 : 0 < d := by omega
  rw [KSumZeroB_norm_sigma]
  have hK := BAK_off_le d L hL hd0 Λ g κ E m hΛ hg hgΛ hκ hr x y hxy
  rw [BAK_apply] at hK
  have hA : 0 ≤ BAp5s_A d Λ κ := by unfold BAp5s_A; positivity
  have hrc : baPureRate d Λ κ ≤ BAct_rate d Λ κ := (min_le_left _ _).trans (min_le_left _ _)
  set z : ℝ := (zdistD d L (x - y) : ℝ) with hz
  have hz0 : 0 ≤ z := Nat.cast_nonneg _
  have hsq : (Real.sqrt (BAp5s_A d Λ κ) * g * Real.exp (-(BAct_rate d Λ κ * z))) ^ 2 =
      BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * z)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA, sq (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  have h1 : ‖BAMB d L g (E : ℂ) m x y‖ ≤ Real.sqrt (BAp5s_A d Λ κ) * g * Real.exp (-(BAct_rate d Λ κ * z)) := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [hsq]
    exact hK
  refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
  nlinarith

end Pointwise

section Tree

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **The tree bound with the gain `g²`** (the twin of `baSigmaTree_bound_maxDist` for a non-constant `δ`): under the
entry bounds of `KSumZeroB_prod_le`, `|Σ_F(δ)| ≤ g² B^{n+3n²} S₀^{N₀} e^{-(r/4) max_{i,j} |δ_i - δ_j|}`
(`baSigmaTree_bound` in its `hprod` form, `hprod` from `KSumZeroB_prod_le` at every labelling consistent with `δ`). -/
private theorem KSumZeroB_tree_bound (hd : 2 ≤ d) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (hsame : ∀ e ∈ F, σ e.1 = σ e.2)
    {B r g : ℝ} (hB : 1 ≤ B) (hr : 0 < r) (hg : 0 ≤ g)
    (hM : ∀ (s : Bool) (x y : Zd d L), ‖M s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘ : ∀ (s : Bool) (x y : Zd d L),
      ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hMo : ∀ (s : Bool) (x y : Zd d L), x ≠ y →
      ‖M s x y‖ ≤ B * g * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (hΘo : ∀ (s : Bool) (x y : Zd d L), x ≠ y →
      ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * g ^ 2 * Real.exp (-(r * (zdistD d L (x - y) : ℝ))))
    (δ : Fin n → Zd d L) (hnc : ∃ v w : Fin n, δ v ≠ δ w) :
    ‖BASigmaTree d L M t F σ δ‖ ≤
      g ^ 2 * B ^ (n + 3 * (n * n)) *
        (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
          Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))) := by
  obtain ⟨i, j, hij⟩ := KLMolecule_exists_pair δ
  rw [hij]
  have hΓ : 0 ≤ g ^ 2 * B ^ (n + 3 * (n * n)) := by
    have : 0 < B := by linarith
    positivity
  refine baSigmaTree_bound hd hF hn M t σ δ hr hΓ (fun β hβ => ?_) i j
  have hnc' : ∃ v w : Fin n, β (BAslotLeaf F v) ≠ β (BAslotLeaf F w) := by
    obtain ⟨v, w, hvw⟩ := hnc
    exact ⟨v, w, by rw [hβ v, hβ w]; exact hvw⟩
  calc _ ≤ B ^ (n + 3 * (n * n)) * g ^ 2 * Real.exp (-(r * ((∑ e : ↥F ⊕ BAslot F,
          zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) : ℕ) : ℝ))) :=
        KSumZeroB_prod_le hF hn M t σ hsame hB hg hM hΘ hMo hΘo β hnc'
    _ = _ := by ring

end Tree

/-- **B2 (`baSig_nc_pointwise`): the pointwise `g²` gain of the molecule weight for a non-constant `δ`** (the BA twin of
`KLIndStepA_nc_pointwise`, `Loop/KLIndStepA.lean:892`): for every charge vector `σ` and every `δ` that is not
constant, `|Σ^{(∅)}(σ, δ)| ≤ G g² e^{-c max_{i,j} |δ_i - δ_j|}`, uniformly in the family `ι` of `(L, g, E, m, t)`:
`3 ≤ L i`, `0 < g i ≤ Λ`, `BAReal d (L i) (g i) κ (E i) (m i)`, `0 ≤ t i ≤ 1`.  `G, c` depend on `(d, n, Λ, κ)` only.
Every edge of a layer-`∅` tree is at most `B e^{-r |x-y|}` (`baPure_edge`), and B1 gives a chord, or two `M`-edges,
at which the entries are off-diagonal and carry `g²` (`baProp5s_of_real`) or `g · g` (`BAK_off_le`). -/
theorem baSig_nc_pointwise {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 2 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ)
    (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i)
    (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i))
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (σ : Fin n → Bool) (δ : Fin n → Zd d (L i)),
      (∃ v w : Fin n, δ v ≠ δ w) →
        ‖BASig d n L g E m t i σ δ‖ ≤ G * g i ^ 2 * Real.exp (-(c * (KLmaxDist d (L i) δ : ℝ))) := by
  have hd0 : 0 < d := by omega
  set B : ℝ := max (baPureB d Λ κ) (Real.sqrt (BAp5s_A d Λ κ)) with hBdef
  have hB1 : 1 ≤ B := (baPureB_one_le d Λ κ).trans (le_max_left _ _)
  have hB0 : 0 < B := by linarith
  have hr0 := baPureRate_pos hd0 hΛ hκ
  have hnn : (0 : ℝ) < ((n + 2 * (n * n) : ℕ) : ℝ) := by
    have := NeZero.pos n
    exact_mod_cast (by positivity : 0 < n + 2 * (n * n))
  have hlam : 0 < baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)) := by positivity
  have hS0 : 0 < expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ))) := by
    unfold expC; positivity
  have hT : 0 < ((TSP n).card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨∅, empty_mem_TSP n⟩
  refine ⟨((TSP n).card : ℝ) * (B ^ (n + 3 * (n * n)) *
    (expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n))), by positivity,
    baPureRate d Λ κ / 4, by positivity, fun i σ δ hnc => ?_⟩
  obtain ⟨hMe, -, hΘe⟩ := baPure_edge hd hΛ hκ (hL i) (hg i) (hgΛ i) (hr i) (ht0 i) (ht1 i)
  have hg0 : 0 ≤ g i := (hg i).le
  have hBe : ∀ (z : ℝ), baPureB d Λ κ * Real.exp z ≤ B * Real.exp z := fun z =>
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have hMB : ∀ (s : Bool) (x y : Zd d (L i)),
      ‖BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i)) s x y‖ ≤
        B * Real.exp (-(baPureRate d Λ κ * (zdistD d (L i) (x - y) : ℝ))) := fun s x y =>
    (hMe s x y).trans (hBe _)
  have hΘB : ∀ (s : Bool) (x y : Zd d (L i)),
      ‖((t i : ℝ) : ℂ) * BAThetaOf (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) s s x y‖ ≤
        B * Real.exp (-(baPureRate d Λ κ * (zdistD d (L i) (x - y) : ℝ))) := fun s x y =>
    (hΘe s x y).trans (hBe _)
  have hMo : ∀ (s : Bool) (x y : Zd d (L i)), x ≠ y →
      ‖BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i)) s x y‖ ≤
        B * g i * Real.exp (-(baPureRate d Λ κ * (zdistD d (L i) (x - y) : ℝ))) := fun s x y hxy =>
    (KSumZeroB_M_off hd hΛ hκ (hL i) (hg i) (hgΛ i) (hr i) s hxy).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hg0) (Real.exp_pos _).le)
  have hΘo : ∀ (s : Bool) (x y : Zd d (L i)), x ≠ y →
      ‖((t i : ℝ) : ℂ) * BAThetaOf (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) s s x y‖ ≤
        B * g i ^ 2 * Real.exp (-(baPureRate d Λ κ * (zdistD d (L i) (x - y) : ℝ))) := fun s x y hxy =>
    (KSumZeroB_chord_off hd hΛ hκ (hL i) (hg i) (hgΛ i) (hr i) (ht0 i) (ht1 i) s hxy).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        (Real.exp_pos _).le)
  have hX : 0 ≤ g i ^ 2 * B ^ (n + 3 * (n * n)) *
      (expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
        Real.exp (-(baPureRate d Λ κ / 4 * (KLmaxDist d (L i) δ : ℝ))) := by positivity
  have h : ‖BASigmaPi d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ ∅ δ‖ ≤
      ((TSP n).card : ℝ) * (g i ^ 2 * B ^ (n + 3 * (n * n)) *
        (expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
          Real.exp (-(baPureRate d Λ κ / 4 * (KLmaxDist d (L i) δ : ℝ)))) := by
    unfold BASigmaPi
    calc ‖∑ F ∈ KLTSPlong n σ ∅, BASigmaTree d (L i) (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i)))
          (t i) F σ δ‖
        ≤ ∑ F ∈ KLTSPlong n σ ∅, (g i ^ 2 * B ^ (n + 3 * (n * n)) *
            (expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
              Real.exp (-(baPureRate d Λ κ / 4 * (KLmaxDist d (L i) δ : ℝ)))) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun F hF => ?_)
          have hsame := KLMolecule_same_charge hF
          have hFT : F ∈ TSP n := (Finset.mem_filter.1 hF).1
          exact KSumZeroB_tree_bound (by omega) (KLisTSP_of_mem_TSP hFT) hn _ (t i) σ hsame hB1 hr0 hg0
            hMB hΘB hMo hΘo δ hnc
      _ = ((KLTSPlong n σ ∅).card : ℝ) * (g i ^ 2 * B ^ (n + 3 * (n * n)) *
            (expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
              Real.exp (-(baPureRate d Λ κ / 4 * (KLmaxDist d (L i) δ : ℝ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((TSP n).card : ℝ) * (g i ^ 2 * B ^ (n + 3 * (n * n)) *
            (expC (d - 2) (baPureRate d Λ κ / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) *
              Real.exp (-(baPureRate d Λ κ / 4 * (KLmaxDist d (L i) δ : ℝ)))) := by
          refine mul_le_mul_of_nonneg_right ?_ hX
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  calc ‖BASig d n L g E m t i σ δ‖ ≤ _ := h
    _ = _ := by ring

/-! ## 4. The slice arithmetic of the weighted estimate (B3)

The proof of the band `KLsumZero_weighted` (`Loop/KLIndStepA.lean:941`), in two steps: the slice arithmetic for an
abstract weight `Sg` (a signed sum-zero bound and a pointwise `g²` bound for the non-constant `δ`), then its
instance at `Sg = BASig`, with the signed clause `baSig_signed_sum` of K08a and B2 in place of
`KLIndStepA_sumZero_signed` and `KLIndStepA_nc_pointwise`.  The band helpers are `private` there, so they are
proved again here. -/

section Weighted

/-- `(x + 1)^m ≤ 2^m (x^m + 1)` (a copy of the private `KLIndStepA_pow_le`, `Loop/KLIndStepA.lean:516`). -/
private theorem KSumZeroB_pow_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : (x + 1) ^ m ≤ 2 ^ m * (x ^ m + 1) := by
  have h1 : x + 1 ≤ 2 * max x 1 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max x 1) ^ m ≤ x ^ m + 1 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_right h, one_pow]; have := pow_nonneg hx m; linarith
    · rw [max_eq_left h]; linarith
  calc (x + 1) ^ m ≤ (2 * max x 1) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = 2 ^ m * (max x 1) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (x ^ m + 1) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `(M+1)^Q e^{-cM} ≤ C_Q e^{-(c/2) M}`, `C_Q = 2^Q (1 + Q!/(c/2)^Q)` (a copy of the private `KLIndStepA_poly_exp`,
`Loop/KLIndStepA.lean:859`). -/
private theorem KSumZeroB_poly_exp (Q : ℕ) {c : ℝ} (hc : 0 < c) {M : ℝ} (hM : 0 ≤ M) :
    (M + 1) ^ Q * Real.exp (-(c * M))
      ≤ (2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q)) * Real.exp (-(c / 2 * M)) := by
  have hc2 : 0 < c / 2 := by positivity
  have h1 : (M + 1) ^ Q ≤ 2 ^ Q * (M ^ Q + 1) := KSumZeroB_pow_le Q hM
  have h2 := pow_mul_exp_neg_le hc2 Q hM
  have h3 : Real.exp (-(c / 2 * M)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have h4 : Real.exp (-(c * M)) = Real.exp (-(c / 2 * M)) * Real.exp (-(c / 2 * M)) := by
    rw [← Real.exp_add]; congr 1; ring
  set e := Real.exp (-(c / 2 * M)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  rw [h4]
  calc (M + 1) ^ Q * (e * e) ≤ (2 ^ Q * (M ^ Q + 1)) * (e * e) := by gcongr
    _ = 2 ^ Q * ((M ^ Q * e) + e) * e := by ring
    _ ≤ 2 ^ Q * ((Nat.factorial Q : ℝ) / (c / 2) ^ Q + 1) * e := by gcongr
    _ = (2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q)) * e := by ring

variable {k n : ℕ} [NeZero n] {L : ℕ} [NeZero L]

/-- `Σ_{δ_r = x} e^{-c max|δ_i - δ_j|} ≤ expC(c/n)^{n-1}` for every root `r` (a copy of the private
`KLIndStepA_sum_exp_root`, `Loop/KLIndStepA.lean:881`: the merged `KLMolecule_sum_exp_maxDist` at root `0` and
`KLIndStepA_sum_slice_root`). -/
private theorem KSumZeroB_sum_exp_root {c : ℝ} (hc : 0 < c) (r : Fin n) (x : Zd (k + 2) L) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) L => δ r = x),
        Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ (expC k (c / n)) ^ (n - 1) := by
  rw [KLIndStepA_sum_slice_root
    (fun δ : Fin n → Zd (k + 2) L => Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))))
    (fun δ c' => by rw [KLIndStepA_maxDist_add_const]) r 0 x]
  exact KLMolecule_sum_exp_maxDist k hc x

/-- **The slice arithmetic of the weighted estimate** (the second half of `KLsumZero_weighted`): from a signed bound on
the slice `δ_r = x`, `|Σ_S Sg| ≤ C₁ τ`, and the pointwise bound `|Sg δ| ≤ G γ e^{-c max|δ_i - δ_j|}` for every
non-constant `δ`, one gets `Σ_S |Sg δ| (max|δ_i - δ_j| + 1)^Q ≤ (C₁ + 2R + 1)(γ + τ)`, `R = G C_Q expC(c/(2n))^{n-1}`:
the constant `δ ≡ x` is read off from the signed sum, the other terms are `≤ γ R` (B2, `KSumZeroB_poly_exp`,
`KSumZeroB_sum_exp_root`). -/
private theorem KSumZeroB_weighted_of (Sg : (Fin n → Zd (k + 2) L) → ℂ) {γ τ C₁ G c : ℝ}
    (hγ : 0 ≤ γ) (hτ : 0 < τ) (hC₁ : 0 ≤ C₁) (hG : 0 ≤ G) (hc : 0 < c)
    (hnc : ∀ δ : Fin n → Zd (k + 2) L, (∃ v w : Fin n, δ v ≠ δ w) →
      ‖Sg δ‖ ≤ G * γ * Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))))
    (Q : ℕ) (r : Fin n) (x : Zd (k + 2) L)
    (hsig : ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) L => δ r = x), Sg δ‖ ≤ C₁ * τ) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) L => δ r = x),
        ‖Sg δ‖ * ((KLmaxDist (k + 2) L δ : ℝ) + 1) ^ Q ≤
      (C₁ + 2 * (G * (2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q)) * (expC k (c / 2 / n)) ^ (n - 1)) + 1) *
        (γ + τ) := by
  classical
  set CQ : ℝ := 2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q) with hCQ
  set R : ℝ := G * CQ * (expC k (c / 2 / n)) ^ (n - 1) with hR
  have hCQ0 : 0 ≤ CQ := by rw [hCQ]; positivity
  have hR0 : 0 ≤ R := by rw [hR]; unfold expC; positivity
  set S := Finset.univ.filter (fun δ : Fin n → Zd (k + 2) L => δ r = x) with hS
  set c0 : Fin n → Zd (k + 2) L := fun _ => x with hc0
  have hc0S : c0 ∈ S := by simp [hS, hc0]
  have hM0 : KLmaxDist (k + 2) L c0 = 0 := by simp [KLmaxDist, hc0]
  have hrest : ∑ δ ∈ S.erase c0, ‖Sg δ‖ * ((KLmaxDist (k + 2) L δ : ℝ) + 1) ^ Q ≤ γ * R := by
    calc _ ≤ ∑ δ ∈ S.erase c0, G * γ * (CQ * Real.exp (-(c / 2 * (KLmaxDist (k + 2) L δ : ℝ)))) := by
          refine Finset.sum_le_sum fun δ hδ => ?_
          obtain ⟨hne, hδS⟩ := Finset.mem_erase.1 hδ
          have hδr : δ r = x := (Finset.mem_filter.1 hδS).2
          have hnc' : ∃ v w : Fin n, δ v ≠ δ w := by
            by_contra hcon
            push Not at hcon
            exact hne (funext fun i => (hcon i r).trans hδr)
          have h1 := hnc δ hnc'
          have h2 := KSumZeroB_poly_exp Q hc (Nat.cast_nonneg (KLmaxDist (k + 2) L δ))
          calc ‖Sg δ‖ * ((KLmaxDist (k + 2) L δ : ℝ) + 1) ^ Q
              ≤ (G * γ * Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ)))) *
                ((KLmaxDist (k + 2) L δ : ℝ) + 1) ^ Q := by gcongr
            _ = G * γ * (((KLmaxDist (k + 2) L δ : ℝ) + 1) ^ Q *
                Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ)))) := by ring
            _ ≤ G * γ * (CQ * Real.exp (-(c / 2 * (KLmaxDist (k + 2) L δ : ℝ)))) := by gcongr
      _ ≤ ∑ δ ∈ S, G * γ * (CQ * Real.exp (-(c / 2 * (KLmaxDist (k + 2) L δ : ℝ)))) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun δ _ _ => by positivity
      _ = G * γ * CQ * ∑ δ ∈ S, Real.exp (-(c / 2 * (KLmaxDist (k + 2) L δ : ℝ))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun δ _ => by ring
      _ ≤ G * γ * CQ * (expC k (c / 2 / n)) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left (KSumZeroB_sum_exp_root (by positivity) r x) (by positivity)
      _ = γ * R := by rw [hR]; ring
  -- the constant pattern is read off from the signed sum
  have habs := Finset.add_sum_erase S (fun δ => ‖Sg δ‖ * ((KLmaxDist (k + 2) L δ : ℝ) + 1) ^ Q) hc0S
  have hsg := Finset.add_sum_erase S (fun δ => Sg δ) hc0S
  have hc0norm : ‖Sg c0‖ ≤ ‖∑ δ ∈ S, Sg δ‖ + ∑ δ ∈ S.erase c0, ‖Sg δ‖ := by
    have h1 : Sg c0 = ∑ δ ∈ S, Sg δ - ∑ δ ∈ S.erase c0, Sg δ := by
      rw [← hsg]; ring
    rw [h1]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have hrest0 : ∑ δ ∈ S.erase c0, ‖Sg δ‖ ≤
      ∑ δ ∈ S.erase c0, ‖Sg δ‖ * ((KLmaxDist (k + 2) L δ : ℝ) + 1) ^ Q :=
    Finset.sum_le_sum fun δ _ => le_mul_of_one_le_right (norm_nonneg _)
      (one_le_pow₀ (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ KLmaxDist (k + 2) L δ)]))
  rw [← habs]
  simp only [hM0, Nat.cast_zero, zero_add, one_pow, mul_one]
  nlinarith [mul_nonneg hC₁ hγ, mul_nonneg hR0 hτ.le, mul_nonneg hγ hR0]

end Weighted

/-! ## 5. B3 and B4: the weighted clause and the K-b predicate -/

/-- **B3 (`baSig_weighted`): the weighted absolute sum-zero estimate on every slice**, for every `Q`: for `σ` cyclically
alternating, every root `r` and label `x`, `Σ_{δ_r = x} |Σ^{(∅)}(σ, δ)| (max_{i,j} |δ_i - δ_j| + 1)^Q ≤ C (g² + (1 - t))`,
`C = C(d, n, Λ, κ, Q)`.  The BA twin of `KLsumZero_weighted` (`Loop/KLIndStepA.lean:941`), at the family data of
`baSig_signed_sum` (`3 ≤ L i`, `0 < g i ≤ Λ`, `BAReal`, `0 ≤ t i < 1`); the unweighted absolute sum of `baSig_decay`
does not give the weighted one uniformly in `g, 1 - t`, the pointwise `g²` factor of a non-constant `δ` (B2) does. -/
theorem baSig_weighted {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ)
    (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i)
    (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1)
    (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d (L i)),
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x),
          ‖BASig d n L g E m t i σ δ‖ * ((KLmaxDist d (L i) δ : ℝ) + 1) ^ Q ≤ C * (g i ^ 2 + (1 - t i)) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨C₁, hC₁, hsig⟩ := baSig_signed_sum hd hn hΛ hκ L g E m t hL hg hgΛ hr ht0 ht1
  have hn2 : 2 ≤ n := by omega
  obtain ⟨G, hG, c, hc, hnc⟩ :=
    baSig_nc_pointwise hd hn2 hΛ hκ L g E m t hL hg hgΛ hr ht0 (fun i => (ht1 i).le)
  have hCQ0 : 0 ≤ 2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q) := by positivity
  have hR0 : 0 ≤ G * (2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q)) * (expC k (c / 2 / n)) ^ (n - 1) := by
    unfold expC; positivity
  refine ⟨C₁ + 2 * (G * (2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q)) * (expC k (c / 2 / n)) ^ (n - 1)) + 1,
    by linarith, fun i σ hσ r x => ?_⟩
  exact KSumZeroB_weighted_of (fun δ => BASig (k + 2) n L g E m t i σ δ) (sq_nonneg _) (by linarith [ht1 i]) hC₁.le
    hG.le hc (fun δ hδ => hnc i σ δ hδ) Q r x (hsig i σ hσ r x)

/-- **B4 (`baSig_sumZeroAbs`): the K-b predicate at the BA molecule weight.**  `SigSumZeroAbs d n L g t (BASig d n L g E m t)`
(`Loop/KLIndStepA.lean:1036`) for the family data of `baSig_signed_sum`, `3 ≤ n`, `t i < 1`.  The reflection and the
translation clauses are `baSig_transl`; the bound clause, for every `Q`, is the signed estimate `baSig_signed_sum`
(`O(1 - t)`) and the weighted one `baSig_weighted` (`O(g² + 1 - t)`) with the larger of the two constants.
`SigSumZeroAbs` has no range for `n` or `t` and is false at `n = 2` (`T2385b`); it is not edited, the ranges are
those of `sigSumZeroAbs_band` and of its consumers (`KLIndStepB.lean:299, 364`). -/
theorem baSig_sumZeroAbs {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ)
    (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i)
    (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i))
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1) :
    SigSumZeroAbs d n L g t (BASig d n L g E m t) := by
  obtain ⟨hrefl, hshift⟩ := baSig_transl d n L g E m t
  obtain ⟨C₁, hC₁, hsig⟩ := baSig_signed_sum hd hn hΛ hκ L g E m t hL hg hgΛ hr ht0 ht1
  refine ⟨hrefl, hshift, fun Q _ => ?_⟩
  obtain ⟨C₂, hC₂, hw⟩ := baSig_weighted hd hn hΛ hκ L g E m t hL hg hgΛ hr ht0 ht1 Q
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun i σ halt r x => ⟨?_, ?_⟩⟩
  · exact (hsig i σ halt r x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [ht1 i]))
  · exact (hw i σ halt r x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by nlinarith [ht1 i, sq_nonneg (g i)]))

/-! ## 6. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m₀`,
`0 < P.g0 ≤ 10`), `Λ = 10`, `κ = Im m₀ > 0`, `n = 4`, `σ = KLsigAlt 4 = (+,-,+,-)` (cyclically alternating), `t = 1/2`
and `t = 999/1000` (near `1`), the family `ι = Unit`.  The label vector `δ₀ = (0, 0, 0, e₁)` is not constant.  Every
deterministic hypothesis of every theorem is discharged at this datum; no hypothesis of another gate remains. -/

namespace KSumZeroBInst

open RBM.BA.MFixedPointInst

/-- The non-constant label vector `δ₀ = (0, 0, 0, e₁)` of `Z_4^3` (`e₁ = (1, 0, 0)` at the vertex `3`). -/
private def KSumZeroB_nc : Fin 4 → Zd 3 4 := fun v j => if v = 3 ∧ j = 0 then 1 else 0

private theorem KSumZeroB_nc_nonconst : ∃ v w : Fin 4, KSumZeroB_nc v ≠ KSumZeroB_nc w := ⟨0, 3, by decide⟩

/-- The tree `{(0, 2)}` of the quadrilateral (one chord, `6` slots) is a `TSP`. -/
private theorem KSumZeroB_F02 : KLIsTSP ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) :=
  KLisTSP_of_mem_TSP (by rw [TSP_four]; decide)

/-- **B1** (`KSumZeroB_unequal_edge`) at the tree `F = {(0, 2)}` (a chord, `n + 2 |F| = 6` slots) and the labelling
`β = (δ₀ on the four leaves, 0 on the two chord slots)`: the leaf labels are not constant. -/
example :=
  KSumZeroB_unequal_edge (d := 3) (L := 4) (n := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) KSumZeroB_F02
    (by norm_num) (Sum.elim KSumZeroB_nc (fun _ => 0)) KSumZeroB_nc_nonconst

/-- The same labelling has equal ends at the chord (both chord slots carry `0`), so B1 yields two unequal `M`-edges of
one node. -/
example : ∃ s s' : BAslot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)), s ≠ s' ∧
    BAslotNode ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s =
      BAslotNode ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s' ∧
    (Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) : BAslot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) →
        Zd 3 4) s ≠
      Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) (BAnextSlot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s) ∧
    Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) s' ≠
      Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) (BAnextSlot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s') :=
  (KSumZeroB_unequal_edge (d := 3) (L := 4) (n := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) KSumZeroB_F02
    (by norm_num) (Sum.elim KSumZeroB_nc (fun _ => 0)) KSumZeroB_nc_nonconst).resolve_left (by decide)

/-- **B2** (`baSig_nc_pointwise`) at `P`, `t = 1/2`, the alternating `σ = KLsigAlt 4` and the non-constant `δ₀`. -/
example : ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧
    ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) ()
      (KLsigAlt 4) KSumZeroB_nc‖ ≤ G * P.g0 ^ 2 * Real.exp (-(c * (KLmaxDist 3 4 KSumZeroB_nc : ℝ))) := by
  obtain ⟨G, hG, c, hc, h⟩ := baSig_nc_pointwise (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num)
    (Λ := 10) (κ := P.m0.im) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (1 : ℝ) / 2) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num)
  exact ⟨G, hG, c, hc, h () (KLsigAlt 4) KSumZeroB_nc KSumZeroB_nc_nonconst⟩

/-- **B2** at `t = 999/1000` (near `1`), `σ = KLsigAlt 4`. -/
example : ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧
    ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000) ()
      (KLsigAlt 4) KSumZeroB_nc‖ ≤ G * P.g0 ^ 2 * Real.exp (-(c * (KLmaxDist 3 4 KSumZeroB_nc : ℝ))) := by
  obtain ⟨G, hG, c, hc, h⟩ := baSig_nc_pointwise (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num)
    (Λ := 10) (κ := P.m0.im) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (999 : ℝ) / 1000) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num)
  exact ⟨G, hG, c, hc, h () (KLsigAlt 4) KSumZeroB_nc KSumZeroB_nc_nonconst⟩

/-- **B2** at `t = 1/2` and a charge vector that is not alternating, `σ = (+,+,-,+)` (B2 holds for every `σ`). -/
example : ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧
    ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) ()
      (fun v : Fin 4 => decide (v ≠ 2)) KSumZeroB_nc‖ ≤
        G * P.g0 ^ 2 * Real.exp (-(c * (KLmaxDist 3 4 KSumZeroB_nc : ℝ))) := by
  obtain ⟨G, hG, c, hc, h⟩ := baSig_nc_pointwise (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num)
    (Λ := 10) (κ := P.m0.im) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (1 : ℝ) / 2) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num)
  exact ⟨G, hG, c, hc, h () (fun v : Fin 4 => decide (v ≠ 2)) KSumZeroB_nc KSumZeroB_nc_nonconst⟩

/-- **B3** (`baSig_weighted`) at `P`, `t = 1/2`, `Q = 4 = 2 (d - 1)`, `σ = KLsigAlt 4`, root `0`, label `0`: the weighted
absolute sum over the slice `δ_0 = 0` (`4^{3·3} = 262144` points). -/
example : ∃ C : ℝ, 0 < C ∧
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0),
      ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) ()
        (KLsigAlt 4) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 4 ≤ C * (P.g0 ^ 2 + (1 - 1 / 2)) := by
  obtain ⟨C, hC, h⟩ := baSig_weighted (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num)
    (Λ := 10) (κ := P.m0.im) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (1 : ℝ) / 2) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num) 4
  exact ⟨C, hC, h () (KLsigAlt 4) (by decide) 0 0⟩

/-- **B3** at `t = 999/1000`, `Q = 4`, `σ = KLsigAlt 4`, root `3`, label `e₁ = (1, 0, 0)`. -/
example : ∃ C : ℝ, 0 < C ∧
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 3 = fun j => if j = 0 then 1 else 0),
      ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000) ()
        (KLsigAlt 4) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 4 ≤ C * (P.g0 ^ 2 + (1 - 999 / 1000)) := by
  obtain ⟨C, hC, h⟩ := baSig_weighted (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num)
    (Λ := 10) (κ := P.m0.im) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (999 : ℝ) / 1000) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num) 4
  exact ⟨C, hC, h () (KLsigAlt 4) (by decide) 3 (fun j => if j = 0 then 1 else 0)⟩

/-- **B3** at `t = 1/2`, `Q = 2`, the complementary alternating vector `(-,+,-,+)`, root `1`, label `0`. -/
example : ∃ C : ℝ, 0 < C ∧
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 1 = 0),
      ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) ()
        (fun k => !KLsigAlt 4 k) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 2 ≤ C * (P.g0 ^ 2 + (1 - 1 / 2)) := by
  obtain ⟨C, hC, h⟩ := baSig_weighted (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num)
    (Λ := 10) (κ := P.m0.im) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (1 : ℝ) / 2) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num) 2
  exact ⟨C, hC, h () (fun k => !KLsigAlt 4 k) (by decide) 1 0⟩

/-- **B4** (`baSig_sumZeroAbs`, the K-b predicate `SigSumZeroAbs`) at `P`, `t = 999/1000`: all three conjuncts. -/
example : SigSumZeroAbs 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => (999 : ℝ) / 1000)
    (BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000)) :=
  baSig_sumZeroAbs (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num) (Λ := 10) (κ := P.m0.im) (by norm_num)
    P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000)
    (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real) (fun _ => by norm_num)
    (fun _ => by norm_num)

/-- **B4**, the third conjunct at `Q = 4 = 2 (d - 1)`, `t = 1/2`, `σ = KLsigAlt 4`, root `0`, label `0`: one constant `C`
for the signed estimate `O(1 - t)` and the weighted one `O(g² + 1 - t)`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0),
        BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) ()
          (KLsigAlt 4) δ‖ ≤ C * (1 - 1 / 2) ∧
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0),
        ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) ()
          (KLsigAlt 4) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 4 ≤ C * (P.g0 ^ 2 + (1 - 1 / 2)) := by
  obtain ⟨-, -, hQ⟩ := baSig_sumZeroAbs (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num) (Λ := 10)
    (κ := P.m0.im) (by norm_num) P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (1 : ℝ) / 2) (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real)
    (fun _ => by norm_num) (fun _ => by norm_num)
  obtain ⟨C, hC, h⟩ := hQ 4 (by norm_num)
  exact ⟨C, hC, h () (KLsigAlt 4) (by decide) 0 0⟩

end KSumZeroBInst

end RBM.BA
