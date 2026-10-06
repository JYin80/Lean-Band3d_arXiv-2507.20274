/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey5
import RBM3D.Graph.AnpKey4
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic

/-!
# LW-12f: `lem:Anp_key_gh`, the deterministic form for every nested graph, and `LWAnp` (T2270)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`):
`lem:Anp_key_gh` `:1041-1077` (`(adsuu22)` `:1043`), the base-case argument `:1110` (a long edge of
a ghost-free path), Cauchy-Schwarz on a fixed vertex `:1178`, `(kwuyayw_ng)` `:1397-1402`,
`(kwuyayw_ng_tree)` and the sums along the spanning tree `:1414-1451`, AM-GM `:1428-1431`, end
`:1533-1534`.  Part f (last) of the six tickets of `lem:Anp`.

The route is direct (DECISIONS §87 (2)): no induction on `q`, no region, no case.

* Section 1: the sums along a nested order (`anpKey6_order`).
* Section 2: the sums along a certificate, by AM-GM (`anpKey6_sum`).
* Section 3: the long-edge union bound (`anpKey6_union`).
* Section 4: the deterministic `lem:Anp_key_gh` (`anpDetGh_holds`).
* Section 5: the merged step, case and `≺` pins, unconditional.
* Section 6: compiled nonempty instances at `d = 3`.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The sums along a nested order (`7_8:1397-1402`, `:1420-1423`) -/

section Order

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ℕ}

/-- The factor `ξ(ℓ e.1, ℓ e.2)` of the edge at position `k` of `E`, at the labels `(a, b, ℓ)`. -/
def anpKey6_F (ξ : ι → ι → ℝ) (E : List (NV p q × NV p q)) (a b : Fin p → ι) (ℓ : Fin q → ι)
    (k : Fin E.length) : ℝ :=
  ξ (Sum.elim (Sum.elim a b) ℓ (E.get k).1) (Sum.elim (Sum.elim a b) ℓ (E.get k).2)

theorem anpKey6_prod_eq (ξ : ι → ι → ℝ) (E : List (NV p q × NV p q)) (a b : Fin p → ι) (ℓ : Fin q → ι) :
    (E.map fun e => ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod =
      ∏ k : Fin E.length, anpKey6_F ξ E a b ℓ k := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- The positions of `E` whose two ends are external or among the first `m` entries of `σ`. -/
def anpKey6_Em (E : List (NV p q × NV p q)) (σ : List (Fin q)) (m : ℕ) : Finset (Fin E.length) :=
  Finset.univ.filter fun k =>
    anpKey5_early σ m (E.get k).1 = true ∧ anpKey5_early σ m (E.get k).2 = true

theorem anpKey6_early_succ (σ : List (Fin q)) (m : ℕ) (hm : m < σ.length) (w : NV p q) :
    anpKey5_early σ (m + 1) w = true ↔ anpKey5_early σ m w = true ∨ w = Sum.inr σ[m] := by
  rcases w with x | i
  · simp [anpKey5_early]
  · simp only [anpKey5_early, Sum.elim_inr, decide_eq_true_eq, Sum.inr.injEq]
    rw [List.take_add_one, List.getElem?_eq_getElem hm]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton]

theorem anpKey6_early_mono (σ : List (Fin q)) (m : ℕ) (hm : m < σ.length) (w : NV p q)
    (h : anpKey5_early σ m w = true) : anpKey5_early σ (m + 1) w = true :=
  (anpKey6_early_succ σ m hm w).2 (Or.inl h)

theorem anpKey6_not_mem_take (σ : List (Fin q)) (hσ : σ.Nodup) (m : ℕ) (hm : m < σ.length) :
    σ[m] ∉ σ.take m := by
  intro h
  rw [List.mem_take_iff_getElem] at h
  obtain ⟨j, hj, hjm⟩ := h
  have hj' : j < m := by omega
  have := (hσ.getElem_inj_iff (hi := by omega) (hj := hm)).1 hjm
  omega

/-- A label of an early vertex is unchanged when the label of `σ[m]` is replaced. -/
theorem anpKey6_lab_update (σ : List (Fin q)) (hσ : σ.Nodup) (m : ℕ) (hm : m < σ.length)
    (a b : Fin p → ι) (ℓ₀ : Fin q → ι) (x : ι) (w : NV p q) (hw : anpKey5_early σ m w = true) :
    Sum.elim (Sum.elim a b) (Function.update ℓ₀ σ[m] x) w = Sum.elim (Sum.elim a b) ℓ₀ w := by
  rcases w with w | i
  · rfl
  · simp only [anpKey5_early, Sum.elim_inr, decide_eq_true_eq] at hw ⊢
    have : i ≠ σ[m] := fun h => anpKey6_not_mem_take σ hσ m hm (h ▸ hw)
    exact Function.update_of_ne this x ℓ₀

/-- Peeling one coordinate off a restricted sum. -/
theorem anpKey6_peel (P : Fin q → Prop) [DecidablePred P] (i : Fin q) (hi : ¬ P i) (ℓ₀ : Fin q → ι)
    (f : (Fin q → ι) → ℝ) :
    ∑ ℓ : Fin q → ι, (if ∀ j, P j → ℓ j = ℓ₀ j then f ℓ else 0) =
      ∑ x : ι, ∑ ℓ : Fin q → ι,
        (if ∀ j, (P j ∨ j = i) → ℓ j = Function.update ℓ₀ i x j then f ℓ else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have key : ∀ x : ι, (∀ j, (P j ∨ j = i) → ℓ j = Function.update ℓ₀ i x j) ↔
      (ℓ i = x ∧ ∀ j, P j → ℓ j = ℓ₀ j) := by
    intro x
    constructor
    · intro h
      refine ⟨by simpa using h i (Or.inr rfl), fun j hj => ?_⟩
      have hji : j ≠ i := fun h' => hi (h' ▸ hj)
      have := h j (Or.inl hj)
      rwa [Function.update_of_ne hji] at this
    · rintro ⟨h1, h2⟩ j hj
      rcases hj with hj | rfl
      · have hji : j ≠ i := fun h' => hi (h' ▸ hj)
        rw [Function.update_of_ne hji]
        exact h2 j hj
      · simpa using h1
  simp only [key]
  by_cases hc : ∀ j, P j → ℓ j = ℓ₀ j
  · simp only [eq_true hc, and_true, ite_true, Finset.sum_ite_eq, Finset.mem_univ]
  · simp only [eq_false hc, and_false, ite_false, Finset.sum_const_zero]

/-- The counted positions of the order condition lie in `E_{m+1} \ E_m`. -/
theorem anpKey6_A_mem (E : List (NV p q × NV p q)) (σ : List (Fin q)) (hnd : σ.Nodup) (m : ℕ)
    (hm : m < σ.length) (k : Fin E.length)
    (hk : ((decide ((E.get k).1 = Sum.inr σ[m]) && anpKey5_early σ m (E.get k).2) ||
        (decide ((E.get k).2 = Sum.inr σ[m]) && anpKey5_early σ m (E.get k).1)) = true) :
    k ∈ anpKey6_Em E σ (m + 1) \ anpKey6_Em E σ m := by
  have hns : anpKey5_early σ m (Sum.inr σ[m] : NV p q) = false := by
    simpa [anpKey5_early] using anpKey6_not_mem_take σ hnd m hm
  have hself : ∀ w : NV p q, w = Sum.inr σ[m] → anpKey5_early σ (m + 1) w = true :=
    fun w hw => (anpKey6_early_succ σ m hm w).2 (Or.inr hw)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
  simp only [anpKey6_Em, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨⟨hself _ h1, anpKey6_early_mono σ m hm _ h2⟩, fun h _ => ?_⟩
    rw [h1, hns] at h
    exact Bool.noConfusion h
  · refine ⟨⟨anpKey6_early_mono σ m hm _ h2, hself _ h1⟩, fun _ h => ?_⟩
    rw [h1, hns] at h
    exact Bool.noConfusion h

/-- The counted positions are `ξ(x, y)` for the label `x` of `σ[m]` and a fixed `y`. -/
theorem anpKey6_A_val (ξ : ι → ι → ℝ) (hsym : ∀ α β, ξ α β = ξ β α) (E : List (NV p q × NV p q))
    (σ : List (Fin q)) (hnd : σ.Nodup) (m : ℕ) (hm : m < σ.length) (a b : Fin p → ι)
    (ℓ₀ : Fin q → ι) (k : Fin E.length)
    (hk : ((decide ((E.get k).1 = Sum.inr σ[m]) && anpKey5_early σ m (E.get k).2) ||
        (decide ((E.get k).2 = Sum.inr σ[m]) && anpKey5_early σ m (E.get k).1)) = true) :
    ∃ y, ∀ x, anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) k = ξ x y := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨Sum.elim (Sum.elim a b) ℓ₀ (E.get k).2, fun x => ?_⟩
    unfold anpKey6_F
    rw [anpKey6_lab_update σ hnd m hm a b ℓ₀ x _ h2, h1]
    simp
  · refine ⟨Sum.elim (Sum.elim a b) ℓ₀ (E.get k).1, fun x => ?_⟩
    unfold anpKey6_F
    rw [anpKey6_lab_update σ hnd m hm a b ℓ₀ x _ h2, h1, hsym]
    simp

/-- The step of the downward induction: from the prefix `m + 1` to the prefix `m` (`7_8:1420-1423`): the label
of `σ[m]` is summed; two of its edges go to labels still fixed (`Σ_x ξ(y₁, x) ξ(y₂, x) ≤ θ`), its other edges
inside the prefix `m + 1` are `≤ ψ(0)`, and the edges inside the prefix `m` do not see `σ[m]`. -/
theorem anpKey6_order_step (E : List (NV p q × NV p q)) (σ : List (Fin q)) (hσ : AnpSumOrder E σ)
    (ξ : ι → ι → ℝ) (ψ0 θ : ℝ) (hψ0 : 0 < ψ0) (hθ : 0 < θ)
    (hξ0 : ∀ α β, 0 ≤ ξ α β) (hsym : ∀ α β, ξ α β = ξ β α) (hξψ : ∀ α β, ξ α β ≤ ψ0)
    (hrow : ∀ α, ∑ β, ξ α β ^ 2 ≤ θ) (a b : Fin p → ι) (m k : ℕ) (hm : m < σ.length)
    (IH : ∀ ℓ₀ : Fin q → ι, ∑ ℓ : Fin q → ι,
        (if ∀ j, j ∈ σ.take (m + 1) → ℓ j = ℓ₀ j then ∏ i, anpKey6_F ξ E a b ℓ i else 0) ≤
      θ ^ k * ψ0 ^ ((E.length : ℤ) - ((anpKey6_Em E σ (m + 1)).card : ℤ) - 2 * (k : ℤ)) *
        ∏ i ∈ anpKey6_Em E σ (m + 1), anpKey6_F ξ E a b ℓ₀ i)
    (ℓ₀ : Fin q → ι) :
    ∑ ℓ : Fin q → ι, (if ∀ j, j ∈ σ.take m → ℓ j = ℓ₀ j then ∏ i, anpKey6_F ξ E a b ℓ i else 0) ≤
      θ ^ (k + 1) * ψ0 ^ ((E.length : ℤ) - ((anpKey6_Em E σ m).card : ℤ) - 2 * ((k + 1 : ℕ) : ℤ)) *
        ∏ i ∈ anpKey6_Em E σ m, anpKey6_F ξ E a b ℓ₀ i := by
  classical
  obtain ⟨hnd, -, hcnt⟩ := hσ
  -- the order condition at `m`: two counted positions
  have hc2 := hcnt ⟨m, hm⟩
  rw [anpKey5_countP_eq_card] at hc2
  obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le (by norm_num) hc2)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
  have hk₁' := hk₁
  have hk₂' := hk₂
  have hsg : σ.get ⟨m, hm⟩ = σ[m] := rfl
  rw [hsg] at hk₁' hk₂'
  have hm₁ := anpKey6_A_mem E σ hnd m hm k₁ hk₁'
  have hm₂ := anpKey6_A_mem E σ hnd m hm k₂ hk₂'
  obtain ⟨y₁, hy₁⟩ := anpKey6_A_val ξ hsym E σ hnd m hm a b ℓ₀ k₁ hk₁'
  obtain ⟨y₂, hy₂⟩ := anpKey6_A_val ξ hsym E σ hnd m hm a b ℓ₀ k₂ hk₂'
  -- sets
  set Em := anpKey6_Em E σ m with hEm
  set Em1 := anpKey6_Em E σ (m + 1) with hEm1
  have hsub : Em ⊆ Em1 := by
    intro i hi
    simp only [hEm, hEm1, anpKey6_Em, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨anpKey6_early_mono σ m hm _ hi.1, anpKey6_early_mono σ m hm _ hi.2⟩
  set D := Em1 \ Em with hD
  have hpair : ({k₁, k₂} : Finset (Fin E.length)) ⊆ D := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hm₁
    · exact hm₂
  set D' := D \ {k₁, k₂} with hD'
  have hcardD : D'.card + 2 = D.card := by
    have := Finset.card_sdiff_add_card_eq_card hpair
    rw [Finset.card_pair hne] at this
    exact this
  have hcardE : D.card + Em.card = Em1.card := Finset.card_sdiff_add_card_eq_card hsub
  -- the edges inside the prefix `m` do not see the label of `σ[m]`
  have hEmconst : ∀ x : ι, ∏ i ∈ Em, anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i =
      ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i := by
    intro x
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [hEm, anpKey6_Em, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    unfold anpKey6_F
    rw [anpKey6_lab_update σ hnd m hm a b ℓ₀ x _ hi.1, anpKey6_lab_update σ hnd m hm a b ℓ₀ x _ hi.2]
  -- peel the coordinate `σ[m]`
  have h1 := anpKey6_peel (fun j => j ∈ σ.take m) σ[m] (anpKey6_not_mem_take σ hnd m hm) ℓ₀
    (fun ℓ => ∏ i, anpKey6_F ξ E a b ℓ i)
  have hiff : ∀ j, (j ∈ σ.take m ∨ j = σ[m]) ↔ j ∈ σ.take (m + 1) := by
    intro j
    rw [List.take_add_one, List.getElem?_eq_getElem hm]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton]
  simp only [hiff] at h1
  rw [h1]
  -- the bound of each summand
  have hxbound : ∀ x : ι, ∑ ℓ : Fin q → ι,
      (if ∀ j, j ∈ σ.take (m + 1) → ℓ j = Function.update ℓ₀ σ[m] x j then
        ∏ i, anpKey6_F ξ E a b ℓ i else 0) ≤
      (θ ^ k * ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) * ψ0 ^ D'.card *
        ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i) * (ξ x y₁ * ξ x y₂) := by
    intro x
    refine (IH (Function.update ℓ₀ σ[m] x)).trans ?_
    set Kc : ℝ := θ ^ k * ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) with hKc
    have hKc0 : 0 ≤ Kc := mul_nonneg (pow_nonneg hθ.le _) (zpow_nonneg hψ0.le _)
    have hPm0 : 0 ≤ ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i :=
      Finset.prod_nonneg fun i _ => hξ0 _ _
    have hF0 : ∀ i x', 0 ≤ anpKey6_F ξ E a b x' i := fun i x' => hξ0 _ _
    -- split the product over `E_{m+1}`
    have hsplit : ∏ i ∈ Em1, anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i =
        (∏ i ∈ D, anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i) *
          ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i := by
      rw [← hEmconst x, hD]
      exact (Finset.prod_sdiff hsub).symm
    have hsplitD : ∏ i ∈ D, anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i =
        (∏ i ∈ D', anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i) *
          (anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) k₁ *
            anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) k₂) := by
      rw [← Finset.prod_pair hne, hD']
      exact (Finset.prod_sdiff hpair).symm
    have hrest : ∏ i ∈ D', anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i ≤ ψ0 ^ D'.card := by
      calc _ ≤ ∏ _i ∈ D', ψ0 :=
            Finset.prod_le_prod₀ (fun i _ => hF0 i _) (fun i _ => hξψ _ _)
        _ = ψ0 ^ D'.card := Finset.prod_const _
    rw [hsplit, hsplitD, hy₁, hy₂]
    have hxx : 0 ≤ ξ x y₁ * ξ x y₂ := mul_nonneg (hξ0 _ _) (hξ0 _ _)
    calc Kc * ((∏ i ∈ D', anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i) * (ξ x y₁ * ξ x y₂) *
          ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i)
        = (Kc * (∏ i ∈ D', anpKey6_F ξ E a b (Function.update ℓ₀ σ[m] x) i) *
          ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i) * (ξ x y₁ * ξ x y₂) := by ring
      _ ≤ (Kc * ψ0 ^ D'.card * ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i) * (ξ x y₁ * ξ x y₂) := by
          refine mul_le_mul_of_nonneg_right ?_ hxx
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrest hKc0) hPm0
      _ = _ := rfl
  -- sum over `x`
  have hxx : ∑ x : ι, ξ x y₁ * ξ x y₂ ≤ θ := by
    have := anpKey3_sum_xx ξ θ hξ0 hrow Finset.univ y₁ y₂
    simpa only [hsym _ y₁, hsym _ y₂] using this
  have hK0 : 0 ≤ θ ^ k * ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) * ψ0 ^ D'.card *
      ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hθ.le _) (zpow_nonneg hψ0.le _))
      (pow_nonneg hψ0.le _)) (Finset.prod_nonneg fun i _ => hξ0 _ _)
  calc _ ≤ ∑ x : ι, (θ ^ k * ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) * ψ0 ^ D'.card *
        ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i) * (ξ x y₁ * ξ x y₂) := Finset.sum_le_sum fun x _ => hxbound x
    _ = (θ ^ k * ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) * ψ0 ^ D'.card *
        ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i) * ∑ x : ι, ξ x y₁ * ξ x y₂ := by rw [Finset.mul_sum]
    _ ≤ (θ ^ k * ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) * ψ0 ^ D'.card *
        ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i) * θ := mul_le_mul_of_nonneg_left hxx hK0
    _ = _ := by
      have hexp : ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) * ψ0 ^ D'.card =
          ψ0 ^ ((E.length : ℤ) - (Em.card : ℤ) - 2 * ((k + 1 : ℕ) : ℤ)) := by
        rw [← zpow_natCast, ← zpow_add₀ hψ0.ne']
        congr 1
        push_cast
        omega
      calc _ = θ ^ k * θ * (ψ0 ^ ((E.length : ℤ) - (Em1.card : ℤ) - 2 * (k : ℤ)) * ψ0 ^ D'.card) *
            ∏ i ∈ Em, anpKey6_F ξ E a b ℓ₀ i := by ring
        _ = _ := by rw [hexp, pow_succ]

/-- **The sums along a nested order** (`(kwuyayw_ng)`, `7_8:1397-1402`), for a general finite label set: with
`ξ ≥ 0` symmetric, `ξ ≤ ψ₀`, `Σ_β ξ_{αβ}² ≤ θ`, the sum over the internal labels of the product of the edge
factors of `E` is at most `θ^q ψ₀^{|E| - 2q}` (an integer power). -/
theorem anpKey6_order_gen [Nonempty ι] (E : List (NV p q × NV p q)) (σ : List (Fin q))
    (hσ : AnpSumOrder E σ) (ξ : ι → ι → ℝ) (ψ0 θ : ℝ) (hψ0 : 0 < ψ0) (hθ : 0 < θ)
    (hξ0 : ∀ α β, 0 ≤ ξ α β) (hsym : ∀ α β, ξ α β = ξ β α) (hξψ : ∀ α β, ξ α β ≤ ψ0)
    (hrow : ∀ α, ∑ β, ξ α β ^ 2 ≤ θ) (a b : Fin p → ι) :
    ∑ ℓ : Fin q → ι, (E.map fun e =>
        ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤
      θ ^ q * ψ0 ^ ((E.length : ℤ) - 2 * (q : ℤ)) := by
  classical
  have hlen : σ.length = q := by
    have h1 := List.toFinset_card_of_nodup hσ.1
    have h2 : σ.toFinset = Finset.univ := by
      ext i
      simp [hσ.2.1 i]
    rw [h2] at h1
    simpa using h1.symm
  have key : ∀ k m : ℕ, m + k = q → ∀ ℓ₀ : Fin q → ι,
      ∑ ℓ : Fin q → ι, (if ∀ j, j ∈ σ.take m → ℓ j = ℓ₀ j then ∏ i, anpKey6_F ξ E a b ℓ i else 0) ≤
        θ ^ k * ψ0 ^ ((E.length : ℤ) - ((anpKey6_Em E σ m).card : ℤ) - 2 * (k : ℤ)) *
          ∏ i ∈ anpKey6_Em E σ m, anpKey6_F ξ E a b ℓ₀ i := by
    intro k
    induction k with
    | zero =>
      intro m hm ℓ₀
      have hmq : m = q := by omega
      have htake : σ.take m = σ := List.take_of_length_le (by omega)
      have hcond : ∀ ℓ : Fin q → ι, (∀ j, j ∈ σ.take m → ℓ j = ℓ₀ j) ↔ ℓ = ℓ₀ := by
        intro ℓ
        rw [htake]
        constructor
        · intro h
          funext j
          exact h j (hσ.2.1 j)
        · rintro rfl j _
          rfl
      have hall : anpKey6_Em E σ m = Finset.univ := by
        ext i
        simp only [anpKey6_Em, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have hearly : ∀ w : NV p q, anpKey5_early σ m w = true := by
          intro w
          rcases w with w | j
          · rfl
          · simp only [anpKey5_early, Sum.elim_inr, decide_eq_true_eq]
            rw [htake]
            exact hσ.2.1 j
        exact ⟨hearly _, hearly _⟩
      simp only [hcond]
      rw [Finset.sum_ite_eq']
      simp [hall]
    | succ k ih =>
      intro m hm ℓ₀
      exact anpKey6_order_step E σ hσ ξ ψ0 θ hψ0 hθ hξ0 hsym hξψ hrow a b m k (by omega)
        (ih (m + 1) (by omega)) ℓ₀
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  have h0 := key q 0 (by omega) (fun _ => x₀)
  simp only [List.take_zero, List.not_mem_nil, false_imp_iff, implies_true, ite_true] at h0
  simp only [anpKey6_prod_eq]
  refine h0.trans ?_
  set Em := anpKey6_Em E σ 0
  have hP : ∏ i ∈ Em, anpKey6_F ξ E a b (fun _ => x₀) i ≤ ψ0 ^ Em.card := by
    calc _ ≤ ∏ _i ∈ Em, ψ0 :=
          Finset.prod_le_prod₀ (fun i _ => hξ0 _ _) (fun i _ => hξψ _ _)
      _ = _ := Finset.prod_const _
  have hA : 0 ≤ θ ^ q * ψ0 ^ ((E.length : ℤ) - (Em.card : ℤ) - 2 * (q : ℤ)) :=
    mul_nonneg (pow_nonneg hθ.le _) (zpow_nonneg hψ0.le _)
  calc _ ≤ θ ^ q * ψ0 ^ ((E.length : ℤ) - (Em.card : ℤ) - 2 * (q : ℤ)) * ψ0 ^ Em.card :=
        mul_le_mul_of_nonneg_left hP hA |> fun h => by simpa [mul_assoc] using h
    _ = _ := by
      rw [mul_assoc, ← zpow_natCast ψ0 Em.card, ← zpow_add₀ hψ0.ne']
      congr 2
      ring

end Order

/-! ## 2. The sums along a certificate: AM-GM (`7_8:1428-1431`) -/

section Cert

theorem anpKey6_prod_set_mul (l : List ℝ) (j : ℕ) (hj : j < l.length) (a : ℝ) :
    (l.set j a).prod * l[j] = l.prod * a := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x t ih =>
    cases j with
    | zero => simp only [List.set_cons_zero, List.prod_cons, List.getElem_cons_zero]; ring
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      simp only [List.set_cons_succ, List.prod_cons, List.getElem_cons_succ]
      calc x * (t.set j a).prod * t[j] = x * ((t.set j a).prod * t[j]) := by ring
        _ = x * (t.prod * a) := by rw [ih j hj']
        _ = _ := by ring

/-- `ξ_k ξ_{k'} ≤ (ξ_k² + ξ_{k'}²) / 2` for the product of a list of nonnegative factors: replacing the factor
`k'` by a copy of the factor `k`, and `k` by a copy of `k'`, doubles the product at most. -/
theorem anpKey6_amgm (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x) (k k' : ℕ) (hk : k < l.length)
    (hk' : k' < l.length) :
    2 * l.prod ≤ (l.set k' l[k]).prod + (l.set k l[k']).prod := by
  have hP : 0 ≤ l.prod := List.prod_nonneg hl
  have hset : ∀ (n : ℕ) (a : ℝ), 0 ≤ a → 0 ≤ (l.set n a).prod := by
    intro n a ha
    refine List.prod_nonneg fun z hz => ?_
    rcases List.mem_or_eq_of_mem_set hz with h | h
    · exact hl z h
    · exact h ▸ ha
  have hx : 0 ≤ l[k] := hl _ (List.getElem_mem hk)
  have hy : 0 ≤ l[k'] := hl _ (List.getElem_mem hk')
  have S1 := hset k' _ hx
  have S2 := hset k _ hy
  have h1 := anpKey6_prod_set_mul l k' hk' l[k]
  have h2 := anpKey6_prod_set_mul l k hk l[k']
  set x := l[k] with hxdef
  set y := l[k'] with hydef
  rcases hx.eq_or_lt with hx0 | hxpos
  · have : l.prod = 0 := List.prod_eq_zero (hx0 ▸ List.getElem_mem hk)
    linarith
  rcases hy.eq_or_lt with hy0 | hypos
  · have : l.prod = 0 := List.prod_eq_zero (hy0 ▸ List.getElem_mem hk')
    linarith
  have hsq : (l.set k' x).prod + (l.set k y).prod - 2 * l.prod ≥ 0 := by
    have e : ((l.set k' x).prod + (l.set k y).prod - 2 * l.prod) * (x * y) =
        l.prod * (x - y) ^ 2 := by
      linear_combination x * h1 + y * h2
    have : 0 ≤ ((l.set k' x).prod + (l.set k y).prod - 2 * l.prod) * (x * y) := by
      rw [e]; positivity
    exact nonneg_of_mul_nonneg_left this (mul_pos hxpos hypos)
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ℕ}

/-- **The sums along a certificate** (`(kwuyayw_ng_tree)`, `7_8:1414-1451`), for a general finite label set:
induction on the depth, a nested order at the leaves, AM-GM at the nodes. -/
theorem anpKey6_sum_gen [Nonempty ι] (n : ℕ) :
    ∀ (E : List (NV p q × NV p q)), AnpSumCert n E → ∀ (ξ : ι → ι → ℝ) (ψ0 θ : ℝ), 0 < ψ0 → 0 < θ →
    (∀ α β, 0 ≤ ξ α β) → (∀ α β, ξ α β = ξ β α) → (∀ α β, ξ α β ≤ ψ0) →
    (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) → ∀ a b : Fin p → ι,
    ∑ ℓ : Fin q → ι, (E.map fun e =>
        ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤
      θ ^ q * ψ0 ^ ((E.length : ℤ) - 2 * (q : ℤ)) := by
  induction n with
  | zero =>
    intro E h ξ ψ0 θ hψ0 hθ hξ0 hsym hξψ hrow a b
    obtain ⟨σ, hσ⟩ := h
    exact anpKey6_order_gen E σ hσ ξ ψ0 θ hψ0 hθ hξ0 hsym hξψ hrow a b
  | succ n ih =>
    intro E h ξ ψ0 θ hψ0 hθ hξ0 hsym hξψ hrow a b
    rcases h with ⟨σ, hσ⟩ | ⟨k, k', hkk, h1, h2⟩
    · exact anpKey6_order_gen E σ hσ ξ ψ0 θ hψ0 hθ hξ0 hsym hξψ hrow a b
    · have B1 := ih _ h1 ξ ψ0 θ hψ0 hθ hξ0 hsym hξψ hrow a b
      have B2 := ih _ h2 ξ ψ0 θ hψ0 hθ hξ0 hsym hξψ hrow a b
      rw [List.length_set] at B1 B2
      set f : NV p q × NV p q → (Fin q → ι) → ℝ := fun e ℓ =>
        ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2) with hf
      have pt : ∀ ℓ : Fin q → ι, 2 * (E.map (fun e => f e ℓ)).prod ≤
          ((E.set k'.1 (E.get k)).map (fun e => f e ℓ)).prod +
            ((E.set k.1 (E.get k')).map (fun e => f e ℓ)).prod := by
        intro ℓ
        have hk : k.1 < (E.map (fun e => f e ℓ)).length := by simp
        have hk' : k'.1 < (E.map (fun e => f e ℓ)).length := by simp
        have := anpKey6_amgm (E.map (fun e => f e ℓ)) (by
          intro z hz
          obtain ⟨e, -, rfl⟩ := List.mem_map.1 hz
          exact hξ0 _ _) k.1 k'.1 hk hk'
        rw [List.map_set, List.map_set]
        simpa [List.get_eq_getElem] using this
      have hsum : 2 * ∑ ℓ : Fin q → ι, (E.map fun e => f e ℓ).prod ≤
          ∑ ℓ : Fin q → ι, ((E.set k'.1 (E.get k)).map fun e => f e ℓ).prod +
            ∑ ℓ : Fin q → ι, ((E.set k.1 (E.get k')).map fun e => f e ℓ).prod := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_le_sum fun ℓ _ => pt ℓ
      linarith

/-! ## 2'. The two sum pins on `Z_L^d` (`AnpKey6OrderPin`, `AnpKey6SumPin`) -/

/-- `ξ_{αβ} ≤ ψ(|α - β|) ≤ ψ(0)` for the non-increasing `ψ`. -/
theorem anpKey6_le_psi0 {d L : ℕ} [NeZero L] (ψ : ℝ → ℝ) (hanti : AntitoneOn ψ (Set.Ici 0))
    (ξ : Zd d L → Zd d L → ℝ) (hξψ : ∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) (α β : Zd d L) :
    ξ α β ≤ ψ 0 :=
  (hξψ α β).trans (hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

/-- **`anpKey6_order`** (`AnpKey6OrderPin`): the sums along a nested order (`(kwuyayw_ng)`, `7_8:1397-1402`;
`7_8:1420-1423`). -/
theorem anpKey6_order : ∀ (d p q : ℕ) (E : List (NV p q × NV p q)) (σ : List (Fin q)), AnpSumOrder E σ →
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          ∑ ℓ : Fin q → Zd d L, (E.map fun e =>
              ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤
            θ ^ q * ψ 0 ^ ((E.length : ℤ) - 2 * (q : ℤ)) := by
  intro d p q E σ hσ L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
  have : Nonempty (Zd d L) := ⟨fun _ => 0⟩
  exact anpKey6_order_gen E σ hσ ξ (ψ 0) θ (hpos 0 le_rfl) hθ (fun α β => (hξ α β).1)
    (fun α β => (hξ α β).2) (anpKey6_le_psi0 ψ hanti ξ hξψ) hrow a b

/-- **`anpKey6_sum`** (`AnpKey6SumPin`): the sums along a summation certificate (`(kwuyayw_ng_tree)`,
`7_8:1414-1533`; the AM-GM split `7_8:1428-1431`). -/
theorem anpKey6_sum : ∀ (d p q n : ℕ) (E : List (NV p q × NV p q)), AnpSumCert n E →
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          ∑ ℓ : Fin q → Zd d L, (E.map fun e =>
              ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤
            θ ^ q * ψ 0 ^ ((E.length : ℤ) - 2 * (q : ℤ)) := by
  intro d p q n E hE L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
  have : Nonempty (Zd d L) := ⟨fun _ => 0⟩
  exact anpKey6_sum_gen n E hE ξ (ψ 0) θ (hpos 0 le_rfl) hθ (fun α β => (hξ α β).1)
    (fun α β => (hξ α β).2) (anpKey6_le_psi0 ψ hanti ξ hξψ) hrow a b

end Cert

/-! ## 3. The long-edge union bound (`7_8:1110`) -/

section Union

variable {p q : ℕ}

/-- The reserved set of a choice function `f` (one position `f j` on each path): the chosen edge of every
ghost-free path. -/
def anpKey6_M (Γ : NGraph p q) (f : ∀ j : Fin p, Fin (Γ.path j).length) : Finset (Fin Γ.es.length) :=
  (Finset.univ.filter fun j : Fin p => Γ.noGhostPath j = true).image fun j => ((Γ.path j).get (f j)).1

/-- The edge of a step of a ghost-free path is solid. -/
theorem anpKey6_solid_of_noGhostPath (Γ : NGraph p q) (j : Fin p) (hj : Γ.noGhostPath j = true)
    (st : Fin Γ.es.length × NV p q) (hst : st ∈ Γ.path j) : (Γ.es.get st.1).ghost = false := by
  unfold NGraph.noGhostPath at hj
  rw [List.all_eq_true] at hj
  simpa using hj st hst

theorem anpKey6_choice_inj (Γ : NGraph p q) (hN : Γ.IsNested) (f : ∀ j : Fin p, Fin (Γ.path j).length) :
    Function.Injective fun j : Fin p => ((Γ.path j).get (f j)).1 := by
  intro i j hij
  by_contra hne
  exact hN.2.2.2.1 i j hne _ (List.get_mem _ (f i)) _ (List.get_mem _ (f j)) hij

theorem anpKey6_M_card (Γ : NGraph p q) (hN : Γ.IsNested) (f : ∀ j : Fin p, Fin (Γ.path j).length) :
    (anpKey6_M Γ f).card = Γ.nngh := by
  unfold anpKey6_M NGraph.nngh
  rw [Finset.card_image_of_injective _ (anpKey6_choice_inj Γ hN f)]

/-- A list whose image under `g` is duplicate-free and constant has at most one element. -/
theorem anpKey6_len_le_one {X Y : Type*} (l : List X) (g : X → Y) (c : Y) (hnd : (l.map g).Nodup)
    (hc : ∀ x ∈ l, g x = c) : l.length ≤ 1 := by
  have : l.map g = List.replicate l.length c := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hc x hx
  rw [this] at hnd
  exact List.nodup_replicate.1 hnd

theorem anpKey6_perPath (Γ : NGraph p q) (hG : Γ.GhostOK) (hN : Γ.IsNested)
    (f : ∀ j : Fin p, Fin (Γ.path j).length) : anpKey5_perPath Γ (anpKey6_M Γ f) := by
  classical
  intro j
  have hmem : ∀ st ∈ Γ.path j, st.1 ∈ anpKey6_M Γ f →
      ∃ j' : Fin p, Γ.noGhostPath j' = true ∧ ((Γ.path j').get (f j')).1 = st.1 := by
    intro st _ h
    simp only [anpKey6_M, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨j', hj', h'⟩ := h
    exact ⟨j', hj', h'⟩
  by_cases hj : Γ.noGhostPath j = true
  · -- a ghost-free path: only its chosen edge
    refine anpKey6_len_le_one _ Prod.fst ((Γ.path j).get (f j)).1 ?_ ?_
    · exact List.Nodup.sublist ((List.filter_sublist).map Prod.fst) (hN.2.2.1 j)
    · intro st hst
      rw [List.mem_filter] at hst
      obtain ⟨hst1, hst2⟩ := hst
      have hg : (Γ.es.get st.1).ghost = false := anpKey6_solid_of_noGhostPath Γ j hj st hst1
      have hM : st.1 ∈ anpKey6_M Γ f := by
        rw [hg, Bool.false_or, decide_eq_true_eq] at hst2
        exact hst2
      obtain ⟨j', hj', hj'e⟩ := hmem st hst1 hM
      by_cases hjj : j' = j
      · subst hjj
        exact hj'e.symm
      · exact absurd hj'e (hN.2.2.2.1 j' j hjj _ (List.get_mem _ (f j')) st hst1)
  · -- a path with a ghost edge: the reserved edges are on other paths
    have hfil : (Γ.path j).filter (fun st => (Γ.es.get st.1).ghost || decide (st.1 ∈ anpKey6_M Γ f)) =
        (Γ.path j).filter (fun st => (Γ.es.get st.1).ghost) := by
      refine List.filter_congr fun st hst => ?_
      have hnM : st.1 ∉ anpKey6_M Γ f := by
        intro h
        obtain ⟨j', hj', hj'e⟩ := hmem st hst h
        have hjj : j' ≠ j := fun e => hj (e ▸ hj')
        exact hN.2.2.2.1 j' j hjj _ (List.get_mem _ (f j')) st hst hj'e
      simp [hnM]
    rw [hfil]
    exact (hG j).1

/-- The number of solid edges, as a cardinality of positions. -/
theorem anpKey6_nSolid_card (Γ : NGraph p q) :
    Γ.nSolid = (Finset.univ.filter fun k : Fin Γ.es.length => (Γ.es.get k).ghost = false).card := by
  unfold NGraph.nSolid
  rw [← List.countP_eq_length_filter, anpKey5_countP_eq_card]
  congr 1
  ext k
  simp

theorem anpKey6_rest_length (Γ : NGraph p q) (hN : Γ.IsNested) (f : ∀ j : Fin p, Fin (Γ.path j).length) :
    (anpKey5_rest Γ (anpKey6_M Γ f)).length + Γ.nngh = Γ.nSolid := by
  classical
  have h1 := anpKey5_rest_countP Γ (anpKey6_M Γ f) (fun _ => true)
  rw [List.countP_true] at h1
  set M := anpKey6_M Γ f with hM
  set Sol := Finset.univ.filter fun k : Fin Γ.es.length => (Γ.es.get k).ghost = false with hSol
  have hMS : M ⊆ Sol := by
    intro k hk
    simp only [hM, anpKey6_M, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    simp only [hSol, Finset.mem_filter, Finset.mem_univ, true_and]
    exact anpKey6_solid_of_noGhostPath Γ j hj _ (List.get_mem _ (f j))
  have h2 : (anpKey5_rest Γ M).length = (Sol \ M).card := by
    rw [h1, ← Finset.card_filter]
    congr 1
    ext k
    simp [hSol]
  have h3 := Finset.card_sdiff_add_card_eq_card hMS
  rw [h2, anpKey6_nSolid_card, ← hSol, ← anpKey6_M_card Γ hN f]
  exact h3

/-- The product over the rest list as a product over the positions. -/
theorem anpKey6_rest_prod (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)) (g : NV p q × NV p q → ℝ) :
    ((anpKey5_rest Γ M).map g).prod = ∏ k : Fin Γ.es.length,
      if ((Γ.es.get k).ghost = false ∧ k ∉ M) then g ((Γ.es.get k).u, (Γ.es.get k).v) else 1 := by
  unfold anpKey5_rest
  rw [Fin.prod_univ_def]
  have key : ∀ l : List (Fin Γ.es.length),
      ((l.filterMap fun k => if (Γ.es.get k).ghost = true ∨ k ∈ M then none
          else some ((Γ.es.get k).u, (Γ.es.get k).v)).map g).prod =
      (l.map fun k => if ((Γ.es.get k).ghost = false ∧ k ∉ M) then
        g ((Γ.es.get k).u, (Γ.es.get k).v) else 1).prod := by
    intro l
    induction l with
    | nil => simp
    | cons k t ih =>
      by_cases h : (Γ.es.get k).ghost = true ∨ k ∈ M
      · have h' : ¬ ((Γ.es.get k).ghost = false ∧ k ∉ M) := by
          rintro ⟨h1, h2⟩
          rcases h with h | h
          · rw [h1] at h; exact Bool.noConfusion h
          · exact h2 h
        simp only [List.filterMap_cons, h, h', ↓reduceIte, List.map_cons, List.prod_cons, one_mul]
        exact ih
      · have h' : ((Γ.es.get k).ghost = false ∧ k ∉ M) := by
          rw [not_or] at h
          exact ⟨by simpa using h.1, h.2⟩
        have e1 : (Γ.es.get k).ghost = false := h'.1
        have e2 : k ∉ M := h'.2
        simp only [List.filterMap_cons, e1, e2, Bool.false_eq_true, false_or, not_false_eq_true,
          ↓reduceIte, List.map_cons, List.prod_cons, ih, and_self]
  exact key _

end Union

section UnionMain

variable {p q : ℕ}

/-- The factor of the edge at position `k` in the value of `Γ`: a ghost edge `1`, a solid edge `ξ` of its labels. -/
def anpKey6_w {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) (ℓ : Fin q → ι)
    (k : Fin Γ.es.length) : ℝ :=
  if (Γ.es.get k).ghost then 1
  else ξ (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).u) (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).v)

theorem anpKey6_val_eq {ι : Type*} [Fintype ι] (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) :
    Γ.val ξ a b = ∑ ℓ : Fin q → ι, ∏ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k := by
  unfold NGraph.val
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

theorem anpKey6_w_nonneg {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ) (hξ0 : ∀ α β, 0 ≤ ξ α β)
    (a b : Fin p → ι) (ℓ : Fin q → ι) (k : Fin Γ.es.length) : 0 ≤ anpKey6_w Γ ξ a b ℓ k := by
  unfold anpKey6_w
  split_ifs
  · exact zero_le_one
  · exact hξ0 _ _

/-- The long-edge bound at one labelling `ℓ` (`7_8:1110` on every ghost-free path, `anpKey_long_edge`): for some
choice function `f` (the chosen edge of each path), the product of the edge factors is at most the long-edge
factors times the product over the edges outside `M_f`. -/
theorem anpKey6_point (Γ : NGraph p q) (hN : Γ.IsNested) {d L : ℕ} [NeZero L] (ψ : ℝ → ℝ)
    (hanti : AntitoneOn ψ (Set.Ici 0)) (hpos : ∀ r : ℝ, 0 ≤ r → 0 < ψ r)
    (ξ : Zd d L → Zd d L → ℝ) (hξ0 : ∀ α β, 0 ≤ ξ α β)
    (hξψ : ∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) (a b : Fin p → Zd d L)
    (ℓ : Fin q → Zd d L) :
    ∃ f : ∀ j : Fin p, Fin (Γ.path j).length,
      ∏ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k ≤
        (∏ i, (if Γ.noGhostPath i = true then
          ψ ((1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)) *
        ∏ k : Fin Γ.es.length, (if ((Γ.es.get k).ghost = false ∧ k ∉ anpKey6_M Γ f) then
          ξ (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).u) (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).v)
          else 1) := by
  classical
  set lbl : NV p q → Zd d L := Sum.elim (Sum.elim a b) ℓ with hlbl
  have hlong : ∀ j : Fin p, ∃ n : Fin (Γ.path j).length,
      zdistInf d L (a j - b j) ≤ (Γ.path j).length *
        zdistInf d L (lbl (Γ.es.get ((Γ.path j).get n).1).u - lbl (Γ.es.get ((Γ.path j).get n).1).v) := by
    intro j
    obtain ⟨st, hst, h⟩ := anpKey_long_edge Γ lbl j (hN.2.1 j)
    obtain ⟨n, rfl⟩ := List.mem_iff_get.1 hst
    exact ⟨n, h⟩
  choose f hf using hlong
  refine ⟨f, ?_⟩
  set M := anpKey6_M Γ f with hM
  have hfac : ∀ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k =
      (if k ∈ M then anpKey6_w Γ ξ a b ℓ k else 1) *
        (if ((Γ.es.get k).ghost = false ∧ k ∉ M) then
          ξ (lbl (Γ.es.get k).u) (lbl (Γ.es.get k).v) else 1) := by
    intro k
    by_cases hk : k ∈ M
    · simp [hk]
    · by_cases hg : (Γ.es.get k).ghost = false
      · have hg' : Γ.es[k.1].ghost = false := hg
        simp [hk, hg', anpKey6_w, hlbl]
      · have : Γ.es[k.1].ghost = true := by simpa using hg
        simp [hk, this, anpKey6_w]
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter]
  have hRnn : 0 ≤ ∏ k : Fin Γ.es.length, (if ((Γ.es.get k).ghost = false ∧ k ∉ M) then
      ξ (lbl (Γ.es.get k).u) (lbl (Γ.es.get k).v) else 1) := by
    refine Finset.prod_nonneg fun k _ => ?_
    split_ifs
    · exact hξ0 _ _
    · exact zero_le_one
  have hc0 : (0 : ℝ) < (1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ := by
    have : (0 : ℝ) ≤ ∑ j, ((Γ.path j).length : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
    positivity
  have hΨnn : 0 ≤ ∏ i, (if Γ.noGhostPath i = true then
      ψ ((1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) := by
    refine Finset.prod_nonneg fun i _ => ?_
    split_ifs
    · exact (hpos _ (by positivity)).le
    · exact zero_le_one
  refine mul_le_mul_of_nonneg_right ?_ hRnn
  -- the chosen edges
  rw [hM, anpKey6_M, Finset.prod_image (fun i _ j _ h => anpKey6_choice_inj Γ hN f h), ← Finset.prod_filter]
  · refine Finset.prod_le_prod₀ (fun j _ => anpKey6_w_nonneg Γ ξ hξ0 a b ℓ _) (fun j hj => ?_)
    have hj' : Γ.noGhostPath j = true := (Finset.mem_filter.1 hj).2
    have hg := anpKey6_solid_of_noGhostPath Γ j hj' _ (List.get_mem _ (f j))
    have hw : anpKey6_w Γ ξ a b ℓ ((Γ.path j).get (f j)).1 =
        ξ (lbl (Γ.es.get ((Γ.path j).get (f j)).1).u) (lbl (Γ.es.get ((Γ.path j).get (f j)).1).v) := by
      unfold anpKey6_w
      rw [hg]
      rfl
    rw [hw]
    refine (hξψ _ _).trans (hanti ?_ ?_ ?_)
    · exact Set.mem_Ici.2 (by positivity)
    · exact Set.mem_Ici.2 (Nat.cast_nonneg _)
    · -- `c r ≤ len`
      have h1 := hf j
      have hlen : ((Γ.path j).length : ℝ) ≤ 1 + ∑ i, ((Γ.path i).length : ℝ) := by
        have : ((Γ.path j).length : ℝ) ≤ ∑ i, ((Γ.path i).length : ℝ) :=
          Finset.single_le_sum (f := fun i => ((Γ.path i).length : ℝ)) (fun i _ => Nat.cast_nonneg _)
            (Finset.mem_univ j)
        linarith
      have h2 : ((zdistInf d L (a j - b j) : ℕ) : ℝ) ≤ ((Γ.path j).length : ℝ) *
          ((zdistInf d L (lbl (Γ.es.get ((Γ.path j).get (f j)).1).u -
            lbl (Γ.es.get ((Γ.path j).get (f j)).1).v) : ℕ) : ℝ) := by exact_mod_cast h1
      have hlen0 : (0 : ℝ) ≤ ((zdistInf d L (lbl (Γ.es.get ((Γ.path j).get (f j)).1).u -
            lbl (Γ.es.get ((Γ.path j).get (f j)).1).v) : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [inv_mul_le_iff₀ (by positivity)]
      calc ((zdistInf d L (a j - b j) : ℕ) : ℝ) ≤ _ := h2
        _ ≤ _ := mul_le_mul_of_nonneg_right hlen hlen0

end UnionMain

section UnionThm

/-- **`anpKey6_union`** (`AnpKey6UnionPin`): the long-edge union bound (the base-case argument of `7_8:1110` on
every ghost-free path, `anpKey_long_edge`).  The family `𝓜` is the image of the choice functions (one position
on each path), so `|𝓜| ≤ Π_j |𝔓_j|`; each `M ∈ 𝓜` reserves one solid edge on every ghost-free path (`perPath`,
`|rest| + n_ngh = n_S`); every labelling is bounded by the sum over `M` of the long-edge factors times the
product over the rest. -/
theorem anpKey6_union : ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested →
    ∃ 𝓜 : Finset (Finset (Fin Γ.es.length)),
      (𝓜.card : ℝ) ≤ ∏ j, max (1 : ℝ) ((Γ.path j).length : ℝ) ∧
      (∀ M ∈ 𝓜, anpKey5_perPath Γ M ∧ (anpKey5_rest Γ M).length + Γ.nngh = Γ.nSolid) ∧
      ∀ (d L : ℕ) [NeZero L] (ψ : ℝ → ℝ), AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) →
        ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
          (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
          ∀ a b : Fin p → Zd d L,
            Γ.val ξ a b ≤ ∑ M ∈ 𝓜,
              (∏ i, (if Γ.noGhostPath i = true then
                ψ ((1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)) *
              ∑ ℓ : Fin q → Zd d L, ((anpKey5_rest Γ M).map fun e =>
                ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod := by
  classical
  intro p q Γ hG hN
  set 𝓕 : Finset (∀ j : Fin p, Fin (Γ.path j).length) :=
    Fintype.piFinset fun j => (Finset.univ : Finset (Fin (Γ.path j).length)) with h𝓕
  refine ⟨𝓕.image (anpKey6_M Γ), ?_, ?_, ?_⟩
  · -- the cardinality
    have h1 : (𝓕.image (anpKey6_M Γ)).card ≤ ∏ j : Fin p, (Γ.path j).length := by
      refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [h𝓕, Fintype.card_piFinset]
      simp
    calc ((𝓕.image (anpKey6_M Γ)).card : ℝ) ≤ ((∏ j : Fin p, (Γ.path j).length : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = ∏ j : Fin p, ((Γ.path j).length : ℝ) := by push_cast; rfl
      _ ≤ _ := Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => le_max_right _ _)
  · intro M hM
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hM
    exact ⟨anpKey6_perPath Γ hG hN f, anpKey6_rest_length Γ hN f⟩
  · intro d L _ ψ hanti hpos ξ hξ hξψ a b
    rw [anpKey6_val_eq]
    set Ψ : ℝ := ∏ i, (if Γ.noGhostPath i = true then
      ψ ((1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) with hΨ
    have hΨnn : 0 ≤ Ψ := by
      refine Finset.prod_nonneg fun i _ => ?_
      split_ifs
      · refine (hpos _ ?_).le
        have : (0 : ℝ) ≤ ∑ j, ((Γ.path j).length : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
        positivity
      · exact zero_le_one
    have hrest : ∀ (M : Finset (Fin Γ.es.length)) (ℓ : Fin q → Zd d L),
        ((anpKey5_rest Γ M).map fun e =>
          ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod =
        ∏ k : Fin Γ.es.length, (if ((Γ.es.get k).ghost = false ∧ k ∉ M) then
          ξ (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).u) (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).v)
          else 1) := fun M ℓ => anpKey6_rest_prod Γ M _
    have hrnn : ∀ (M : Finset (Fin Γ.es.length)) (ℓ : Fin q → Zd d L),
        0 ≤ ((anpKey5_rest Γ M).map fun e =>
          ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod := by
      intro M ℓ
      refine List.prod_nonneg fun z hz => ?_
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hz
      exact (hξ _ _).1
    calc ∑ ℓ : Fin q → Zd d L, ∏ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k
        ≤ ∑ ℓ : Fin q → Zd d L, ∑ M ∈ 𝓕.image (anpKey6_M Γ), Ψ *
            ((anpKey5_rest Γ M).map fun e =>
              ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod := by
          refine Finset.sum_le_sum fun ℓ _ => ?_
          obtain ⟨f, hf⟩ := anpKey6_point Γ hN ψ hanti hpos ξ (fun α β => (hξ α β).1) hξψ a b ℓ
          refine hf.trans ?_
          rw [← hrest]
          exact Finset.single_le_sum (f := fun M => Ψ * ((anpKey5_rest Γ M).map fun e =>
            ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod)
            (fun M _ => mul_nonneg hΨnn (hrnn M ℓ))
            (Finset.mem_image.2 ⟨f, Fintype.mem_piFinset.2 fun j => Finset.mem_univ _, rfl⟩)
      _ = ∑ M ∈ 𝓕.image (anpKey6_M Γ), Ψ * ∑ ℓ : Fin q → Zd d L,
            ((anpKey5_rest Γ M).map fun e =>
              ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [Finset.mul_sum]

end UnionThm

/-! ## 4. The deterministic `lem:Anp_key_gh` for every nested graph (`7_8:1041-1077`) -/

section Det

/-- **`anpDetGh_holds`** (`AnpKey6DirectPin`, T2264's interface): the deterministic `lem:Anp_key_gh`, with
`C = Π_j max 1 |𝔓_j|` and `c = 1/(1 + Σ_j |𝔓_j|)`.  One union bound over the long edges of the ghost-free paths
(`anpKey6_union`), the certificate of the rest (`anpKey5_cert`), and the sums along it (`anpKey6_sum`); no
induction on `q`, no region, no case. -/
theorem anpDetGh_holds : ∀ d : ℕ, AnpDetGh d := by
  intro d p q Γ hG hN
  obtain ⟨𝓜, hcard, hM, hmain⟩ := anpKey6_union p q Γ hG hN
  have hS0 : (0 : ℝ) ≤ ∑ j, ((Γ.path j).length : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hC : 0 < ∏ j, max (1 : ℝ) ((Γ.path j).length : ℝ) :=
    Finset.prod_pos fun j _ => lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨∏ j, max (1 : ℝ) ((Γ.path j).length : ℝ), (1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹, hC,
    by positivity, inv_le_one_of_one_le₀ (by linarith), ?_⟩
  intro L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
  have h1 := hmain d L ψ hanti hpos ξ hξ hξψ a b
  set Ψ : ℝ := ∏ i, (if Γ.noGhostPath i = true then
    ψ ((1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1) with hΨ
  have hΨnn : 0 ≤ Ψ := by
    refine Finset.prod_nonneg fun i _ => ?_
    split_ifs
    · exact (hpos _ (by positivity)).le
    · exact zero_le_one
  set K : ℝ := θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) with hK
  have hK0 : 0 ≤ K := mul_nonneg (pow_nonneg hθ.le _) (zpow_nonneg (hpos 0 le_rfl).le _)
  have hMbound : ∀ M ∈ 𝓜, ∑ ℓ : Fin q → Zd d L, ((anpKey5_rest Γ M).map fun e =>
      ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤ K := by
    intro M hMm
    obtain ⟨hpp, hlen⟩ := hM M hMm
    obtain ⟨n, hn⟩ := anpKey5_cert p q Γ M hN hpp
    have h2 := anpKey6_sum d p q n (anpKey5_rest Γ M) hn L ψ θ hanti hpos hθ ξ hξ hξψ hrow a b
    have hexp : ((anpKey5_rest Γ M).length : ℤ) - 2 * (q : ℤ) = Γ.ordN - (Γ.nngh : ℤ) := by
      unfold NGraph.ordN
      simp only [ord]
      have : ((anpKey5_rest Γ M).length : ℤ) + (Γ.nngh : ℤ) = (Γ.nSolid : ℤ) := by exact_mod_cast hlen
      omega
    rw [hexp] at h2
    exact h2
  calc Γ.val ξ a b ≤ ∑ M ∈ 𝓜, Ψ * ∑ ℓ : Fin q → Zd d L, ((anpKey5_rest Γ M).map fun e =>
        ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod := h1
    _ ≤ ∑ M ∈ 𝓜, Ψ * K :=
        Finset.sum_le_sum fun M hMm => mul_le_mul_of_nonneg_left (hMbound M hMm) hΨnn
    _ = (𝓜.card : ℝ) * (Ψ * K) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ j, max (1 : ℝ) ((Γ.path j).length : ℝ)) * (Ψ * K) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hΨnn hK0)
    _ = _ := by simp only [hK]; ring

end Det

/-! ## 5. The merged step, case and `≺` pins, unconditional -/

section Corollaries

/-- `valOn` on a region is at most the full value (`valOn` over a subset of the labels, all terms `≥ 0`). -/
theorem anpKey6_valOn_le {p q : ℕ} (Γ : NGraph p q) {d L : ℕ} [NeZero L] (ξ : Zd d L → Zd d L → ℝ)
    (hξ0 : ∀ α β, 0 ≤ ξ α β) (a b : Fin p → Zd d L) (S : Finset (Fin q → Zd d L)) :
    Γ.valOn ξ a b S ≤ Γ.val ξ a b := by
  rw [anpKey2_val_eq_valOn]
  unfold NGraph.valOn
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun ℓ _ _ => ?_
  refine List.prod_nonneg fun z hz => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hz
  split_ifs
  · exact zero_le_one
  · exact hξ0 _ _

/-- **`anpDetGhCaseIV_holds`** (`AnpKey6IVPin`): case (IV) on a region.  The bound of `anpDetGh_holds` holds for the
whole sum, hence for the sum over the region; the case and induction hypotheses are not used. -/
theorem anpDetGhCaseIV_holds : ∀ d : ℕ, AnpDetGhCaseIV d := by
  intro d q _ _ p Γ π hG hN _ _ _
  obtain ⟨C, c, hC, hc, hc1, H⟩ := anpDetGh_holds d p q Γ hG hN
  refine ⟨C, c, hC, hc, hc1, fun L _ ψ θ hanti hpos hθ ξ hξ hξψ hrow a b => ?_⟩
  exact (anpKey6_valOn_le Γ ξ (fun α β => (hξ α β).1) a b _).trans
    (H L ψ θ hanti hpos hθ ξ hξ hξψ hrow a b)

/-- **`anpDetGhStep_holds`** (`AnpKey6StepPin`): the merged step pin; its induction hypothesis is not used. -/
theorem anpDetGhStep_holds : ∀ d : ℕ, AnpDetGhStep d :=
  fun d q _ _ p Γ hG hN => anpDetGh_holds d p q Γ hG hN

/-- **`anpIH_holds`** (`AnpKey6IHPin`): the induction hypothesis, for every `q`. -/
theorem anpIH_holds : ∀ d q : ℕ, AnpIH d q :=
  fun d _ p' k _ Γ' hG' hN' => anpDetGh_holds d p' k Γ' hG' hN'

/-- **`anpDetGhRegStep_holds`** (`AnpKey6RegStepPin`): the merged step on regions, from the merged case split with
the three case pins proved. -/
theorem anpDetGhRegStep_holds : ∀ d : ℕ, AnpDetGhRegStep d :=
  fun d => anpDetGhRegStep_of_cases d (anpDetGhCaseI_holds d) (anpDetGhCaseIII_holds d)
    (anpDetGhCaseIV_holds d)

/-- **`lwAnpKeyGh_holds`** (`AnpKey6KeyGhPin`): `lem:Anp_key_gh` (`7_8:1041-1077`), unconditionally. -/
theorem lwAnpKeyGh_holds : ∀ d : ℕ, LWAnpKeyGh d := fun d => lwAnpKeyGh_of_det d (anpDetGh_holds d)

/-- **`lwAnpKey_holds`** (`AnpKey6KeyPin`): `lem:Anp_key` (`7_8:960-985`), unconditionally. -/
theorem lwAnpKey_holds : ∀ d : ℕ, LWAnpKey d := fun d => lwAnpKey_of_gh d (lwAnpKeyGh_holds d)

/-- **`lwAnp_holds`** (`AnpKey6AnpPin`): `lem:Anp` (`7_8:933-939`), unconditionally. -/
theorem lwAnp_holds : ∀ d : ℕ, LWAnp d := fun d => lwAnp_of_key d (lwAnpKey_holds d)

end Corollaries

/-! ## 6. Compiled nonempty instances at `d = 3` -/

section Instances

private theorem anpKey6_zdist_three_le (u : ZMod 3) : zdist 3 u ≤ 1 := by
  revert u
  decide

private theorem anpKey6_zdistInf_three_le (x : Zd 3 3) : zdistInf 3 3 x ≤ 1 :=
  Finset.sup_le fun i _ => anpKey6_zdist_three_le (x i)

/-- The concrete data of the instances: `d = L = 3`, `ψ r = (1 + r)⁻¹` (positive, non-increasing), `θ = 1`,
`ξ ≡ 1/6` (`Σ_β ξ² = 27/36 ≤ 1`, `ξ ≤ 1/2 ≤ ψ(|α - β|)` since `|α - β| ≤ 1` on `Z_3^3`). -/
theorem anpKey6_inst_data :
    AntitoneOn (fun r : ℝ => (1 + r)⁻¹) (Set.Ici 0) ∧ (∀ r : ℝ, 0 ≤ r → 0 < (fun r : ℝ => (1 + r)⁻¹) r) ∧
      (0 : ℝ) < 1 ∧ (∀ _α _β : Zd 3 3, (0 : ℝ) ≤ 1 / 6 ∧ (1 / 6 : ℝ) = 1 / 6) ∧
      (∀ α β : Zd 3 3, (1 / 6 : ℝ) ≤ (fun r : ℝ => (1 + r)⁻¹) ((zdistInf 3 3 (α - β) : ℕ) : ℝ)) ∧
      (∀ _α : Zd 3 3, ∑ _β : Zd 3 3, (1 / 6 : ℝ) ^ 2 ≤ 1) := by
  refine ⟨?_, ?_, one_pos, fun _ _ => ⟨by norm_num, rfl⟩, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : (0 : ℝ) ≤ a := ha
    exact inv_anti₀ (by linarith) (by linarith)
  · intro r hr
    exact inv_pos.2 (by linarith)
  · intro α β
    have h1 : ((zdistInf 3 3 (α - β) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast anpKey6_zdistInf_three_le _
    have h2 : (0 : ℝ) ≤ ((zdistInf 3 3 (α - β) : ℕ) : ℝ) := Nat.cast_nonneg _
    change (1 / 6 : ℝ) ≤ (1 + ((zdistInf 3 3 (α - β) : ℕ) : ℝ))⁻¹
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · intro α
    simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    norm_num

/-- Instance (1): `anpDetGh_holds` at three merged graphs: `figAux` (no ghost), `anpKey5_figIVext` (case (IV),
`q = 1 < p = 2`) and `anpKey2_figAuxGh` (ghost edges), with the concrete data of `anpKey6_inst_data` (`a ≡ 0`,
`b ≡ 1`, `|a - b| = 1`) put into the bound: every deterministic hypothesis is discharged. -/
theorem anpKey6_inst_eval {p q : ℕ} (Γ : NGraph p q) (hG : Γ.GhostOK) (hN : Γ.IsNested) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      Γ.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤
        C * (1 : ℝ) ^ q * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
          ∏ i, (if Γ.noGhostPath i = true then
            (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ))
            else 1) := by
  obtain ⟨C, c, hC, hc, hc1, H⟩ := anpDetGh_holds 3 p q Γ hG hN
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := anpKey6_inst_data
  exact ⟨C, c, hC, hc, hc1, H 3 (fun r : ℝ => (1 + r)⁻¹) 1 h1 h2 h3 (fun _ _ => 1 / 6) h4 h5 h6
    (fun _ => 0) (fun _ => 1)⟩

theorem anpKey6_inst_det :
    AnpDetGhAt 3 figAux ∧ AnpDetGhAt 3 anpKey5_figIVext ∧ AnpDetGhAt 3 anpKey2_figAuxGh :=
  ⟨anpDetGh_holds 3 2 2 figAux (anpKey_ghostOK_of_noGhost figAux_nested.2) figAux_nested.1,
    anpDetGh_holds 3 2 1 anpKey5_figIVext anpKey5_inst_figIVext.1 anpKey5_inst_figIVext.2.1,
    anpDetGh_holds 3 2 2 anpKey2_figAuxGh anpKey2_figAuxGh_ghostOK anpKey2_figAuxGh_nested⟩

/-- Instance (1'): the bound at the concrete data, at the three merged graphs. -/
theorem anpKey6_inst_det_eval :
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      figAux.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤
        C * (1 : ℝ) ^ 2 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (figAux.ordN - (figAux.nngh : ℤ)) *
          ∏ i, (if figAux.noGhostPath i = true then
            (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ))
            else 1)) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      anpKey5_figIVext.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤
        C * (1 : ℝ) ^ 1 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (anpKey5_figIVext.ordN - (anpKey5_figIVext.nngh : ℤ)) *
          ∏ i, (if anpKey5_figIVext.noGhostPath i = true then
            (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ))
            else 1)) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      anpKey2_figAuxGh.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤
        C * (1 : ℝ) ^ 2 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (anpKey2_figAuxGh.ordN - (anpKey2_figAuxGh.nngh : ℤ)) *
          ∏ i, (if anpKey2_figAuxGh.noGhostPath i = true then
            (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ))
            else 1)) :=
  ⟨anpKey6_inst_eval figAux (anpKey_ghostOK_of_noGhost figAux_nested.2) figAux_nested.1,
    anpKey6_inst_eval anpKey5_figIVext anpKey5_inst_figIVext.1 anpKey5_inst_figIVext.2.1,
    anpKey6_inst_eval anpKey2_figAuxGh anpKey2_figAuxGh_ghostOK anpKey2_figAuxGh_nested⟩

/-- Instance (2): the three merged `≺` pins at `d = 3` (`LWAnp 3` is the `h` of the merged `inst_Anp`, `LWAnpKey 3`
that of `inst_AnpKey`), with no hypothesis. -/
theorem anpKey6_inst_lw : LWAnpKeyGh 3 ∧ LWAnpKey 3 ∧ LWAnp 3 :=
  ⟨lwAnpKeyGh_holds 3, lwAnpKey_holds 3, lwAnp_holds 3⟩

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.LWInst in
/-- Instance (2'): the merged `inst_Anp` and `inst_AnpKey` with no hypothesis but the edge variables `ξ` and their
bounds `LWXi` (the premise owed at its registry line). -/
theorem anpKey6_inst_anp
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    (∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
        (fun n ab ω => figAux.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 *
          Φ0 n 0 ^ (figAux.ordN - (2 : ℕ)))) ∧
    (∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n ab ω => figAux.val (fun α β => ξ n α β ω) ab.1 ab.2)
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n 0 ^ (figAux.ordN - (2 : ℕ)) *
          ∏ i, Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)))) :=
  ⟨anpKey_inst_anp (anpDetGhStep_holds 3) ξ hξ, inst_AnpKey (lwAnpKey_holds 3) ξ hξ⟩

/-- Instance (3): every merged step and case pin at `d = 3`, and the merged chains
`anpKey3_inst_chain`, `anpKey2_inst_chain` closed with no hypothesis left. -/
theorem anpKey6_inst_cases :
    AnpDetGhCaseI 3 ∧ AnpDetGhCaseIII 3 ∧ AnpDetGhCaseIV 3 ∧ AnpDetGhRegStep 3 ∧ AnpDetGhStep 3 ∧ AnpIH 3 2 ∧
      LWAnpKeyGh 3 ∧ LWAnpKeyGh 3 :=
  ⟨anpDetGhCaseI_holds 3, anpDetGhCaseIII_holds 3, anpDetGhCaseIV_holds 3, anpDetGhRegStep_holds 3,
    anpDetGhStep_holds 3, anpIH_holds 3 2,
    anpKey3_inst_chain (anpDetGhCaseIII_holds 3) (anpDetGhCaseIV_holds 3),
    anpKey2_inst_chain (anpDetGhCaseI_holds 3) (anpDetGhCaseIII_holds 3) (anpDetGhCaseIV_holds 3)⟩

/-- Instance (3'): the three region/step corollaries applied at concrete graphs with every hypothesis discharged:
case (IV) at `anpKey5_figIVext` (`q = 1`, no `A2` edge, neither case (I) nor case (III): `anpKey5_inst_figIVext`), the
step at `figAux` (`q = 2`), the step on regions at `anpKey2_figAuxGh` (`π ≡ false`, no `A2` edge:
`anpKey2_inst_figAuxGh`). -/
theorem anpKey6_inst_apply :
    AnpDetGhRegAt 3 anpKey5_figIVext anpKey5_piIV ∧ AnpDetGhAt 3 figAux ∧
      AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false) :=
  ⟨anpDetGhCaseIV_holds 3 1 one_pos (anpIH_holds 3 1) 2 anpKey5_figIVext anpKey5_piIV
      anpKey5_inst_figIVext.1 anpKey5_inst_figIVext.2.1 anpKey5_inst_figIVext.2.2.1
      anpKey5_inst_figIVext.2.2.2.1 anpKey5_inst_figIVext.2.2.2.2.1,
    anpDetGhStep_holds 3 2 two_pos (anpIH_holds 3 2) 2 figAux
      (anpKey_ghostOK_of_noGhost figAux_nested.2) figAux_nested.1,
    anpDetGhRegStep_holds 3 2 two_pos (anpIH_holds 3 2) 2 anpKey2_figAuxGh (fun _ _ => false)
      anpKey2_inst_figAuxGh.1 anpKey2_inst_figAuxGh.2.1 anpKey2_inst_figAuxGh.2.2.1⟩

/-- Instance (4): `anpKey6_sum` at the depth-1 certificate of `figAux` minus `anpKey5_resAux` (no nested order,
AM-GM needed), `d = L = 3`, `ψ r = (1 + r)⁻¹`, `θ = 1`, `ξ ≡ 1/6`, `a ≡ 0`, `b ≡ 1`. -/
theorem anpKey6_inst_sum :
    ∑ ℓ : Fin 2 → Zd 3 3, ((anpKey5_rest figAux anpKey5_resAux).map fun e : NV 2 2 × NV 2 2 =>
        (fun _ _ : Zd 3 3 => (1 / 6 : ℝ))
          (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.1)
          (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.2)).prod ≤
      (1 : ℝ) ^ 2 * (fun r : ℝ => (1 + r)⁻¹) 0 ^
        (((anpKey5_rest figAux anpKey5_resAux).length : ℤ) - 2 * (2 : ℤ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := anpKey6_inst_data
  exact anpKey6_sum 3 2 2 1 (anpKey5_rest figAux anpKey5_resAux) anpKey5_inst_resAux.2.2 3
    (fun r : ℝ => (1 + r)⁻¹) 1 h1 h2 h3 (fun _ _ => 1 / 6) h4 h5 h6
    (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3))

/-- Instance (4'): `anpKey6_order` at the nested order `[α]` of `figIVext` with nothing reserved (`p = 2`, `q = 1`,
four solid edges), the same data. -/
theorem anpKey6_inst_order :
    ∑ ℓ : Fin 1 → Zd 3 3, ((anpKey5_rest anpKey5_figIVext ∅).map fun e : NV 2 1 × NV 2 1 =>
        (fun _ _ : Zd 3 3 => (1 / 6 : ℝ))
          (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.1)
          (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.2)).prod ≤
      (1 : ℝ) ^ 1 * (fun r : ℝ => (1 + r)⁻¹) 0 ^
        (((anpKey5_rest anpKey5_figIVext ∅).length : ℤ) - 2 * (1 : ℤ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := anpKey6_inst_data
  exact anpKey6_order 3 2 1 (anpKey5_rest anpKey5_figIVext ∅) [0] anpKey5_inst_figIVext.2.2.2.2.2.2.2.2 3
    (fun r : ℝ => (1 + r)⁻¹) 1 h1 h2 h3 (fun _ _ => 1 / 6) h4 h5 h6
    (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3))

/-- Instance (5): the union bound's family at `figAux` (two ghost-free paths of length 3: at most 9 reserved sets,
each with `perPath` and `|rest| + n_ngh = n_S`), and its bound at the concrete data. -/
theorem anpKey6_inst_union :
    ∃ 𝓜 : Finset (Finset (Fin figAux.es.length)), (𝓜.card : ℝ) ≤ 9 ∧
      (∀ M ∈ 𝓜, anpKey5_perPath figAux M ∧ (anpKey5_rest figAux M).length + figAux.nngh = figAux.nSolid) ∧
      figAux.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤
        ∑ M ∈ 𝓜, (∏ i, (if figAux.noGhostPath i = true then
          (fun r : ℝ => (1 + r)⁻¹) ((1 + ∑ j, ((figAux.path j).length : ℝ))⁻¹ *
            ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ)) else 1)) *
          ∑ ℓ : Fin 2 → Zd 3 3, ((anpKey5_rest figAux M).map fun e : NV 2 2 × NV 2 2 =>
            (fun _ _ : Zd 3 3 => (1 / 6 : ℝ))
              (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.1)
              (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.2)).prod := by
  obtain ⟨𝓜, hcard, hM, H⟩ := anpKey6_union 2 2 figAux (anpKey_ghostOK_of_noGhost figAux_nested.2) figAux_nested.1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := anpKey6_inst_data
  refine ⟨𝓜, ?_, hM, H 3 3 (fun r : ℝ => (1 + r)⁻¹) h1 h2 (fun _ _ => 1 / 6) h4 h5
    (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3))⟩
  refine hcard.trans (le_of_eq ?_)
  have hlen : ∀ j, (figAux.path j).length = 3 := by decide +kernel
  simp only [hlen, Fin.prod_univ_two]
  norm_num

end Instances

end RBM.Graph
