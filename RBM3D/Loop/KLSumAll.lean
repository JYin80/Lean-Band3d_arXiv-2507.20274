/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLSumZero
import RBM3D.Loop.KLWard
import RBM3D.Loop.KLUnique

/-!
# The total-sum bound `(sumallAinK)` with an explicit constant, `d ≥ 3`

Ticket T2048 (design ticket T2004, row KL7, second of three: KL7a is `KLSumZero.lean`, KL7c is
`SumZeroWard`).  Names are in `RBM.Loop`; every helper is `private` and carries the file stem
`KLSumAll_`; the compiled instances are `KLSumAll_inst_*`.

* **`RBM.Loop.KLK_sumAll_le`**: for `κ > 0`, `3 ≤ L`, `1 ≤ W`, `|E| ≤ 2 - κ`, `t ∈ [0,1)`, `n ≥ 2`,
  `σ₁ = +`, `σ_n = -` and every `a₁`,
  `|∑_{a₂,…,aₙ} 𝒦_{t,σ,a}| ≤ 2^{n²} c_κ^{-2n} (W^d η_t)^{-(n-1)}`, `c_κ = gapK κ`,
  `η_t = (1 - t) Im m(E)`, for `𝒦 = KLK` (the tree sum of KL1).  It is the port of RBM2D's
  `Kcal_sumAll_le` (`RBM2D/Loop/SumAll.lean:749` at `c9a24cf`).  This paper does not state the
  bound; RBM2D's paper has it as Corollary `lem_sumAinK`, `(sumallAinK)`, `O([W²η_t]^{-n+1})`,
  a consequence of Ward's identity, and the explicit constant is RBM2D's paper-delta T2004a-11
  (cited, not re-proposed).  No hypothesis is added: `3 ≤ d` is not used, nothing is assumed
  about `g`, and no unproved `Prop` enters.

Route, as in RBM2D.  Total sums `T_n(σ) = ∑_a 𝒦_{t,σ,a}`:
* translation (`KLK_translate`, KL5) gives `T_n(σ) = L^d ∑_{a : a₁ fixed} 𝒦`;
* rotation (`KLK_rotate`, KL5) gives `T_n(σ) = T_n(σ ∘ (· + j))`;
* pure `σ`: `n = 1`, `n = 2` (`KLK_two`, `sum_Theta_row_of_three_le`) and `n ≥ 3`
  (`KLK_eq_sum_Kpi`, `sum_Kpi_closed` of KL7a) are bounded directly;
* non-pure `σ`: rotate to `σ₁ = +`, `σ_n = -` and apply `KLK_ward` (KL6), by induction on `n` with
  the claim `‖T_n(σ)‖ ≤ L^d B_n`, `B_n = 2^{n²} c_κ^{-2n} (W^d η_t)^{-(n-1)}`, for all sign
  vectors.

## Sources and changes

Port of `../RBM2D/RBM2D/Loop/SumAll.lean` at `c9a24cf` (788 lines, read-only; its only public
declaration is `Kcal_sumAll_le`).  Renaming: `Z2 L ↦ Zd d L`,
`Kcal L W E t (loopOf L σ a) ↦ KLK d L g W E t (KLloopOf d L σ a)`, `Kcal_rotate`,
`Kcal_translate`, `Kcal_ward`, `Kcal_two`, `Kcal_eq_sum_Kpi ↦ KLK_rotate`, `KLK_translate`,
`KLK_ward`, `KLK_two`, `KLK_eq_sum_Kpi`, `mSig ↦ mSigma`, `Gauss.spectralM ↦ mE`,
`etaT ↦ Gauss.etaT`, `Theta L ↦ Theta d L g`, `TSPlong`, `Flong`, `ArcLe ↦ KLTSPlong`, `KLFlong`,
`KLArcLe`, `W² ↦ W^d`, `L² ↦ L^d` (`SumAll_card_Z2 ↦ card_Zd`).

* **Merged API used instead of copies** (the private helpers of `SumAll.lean` that re-prove them are
  not ported): `norm_mSigma`, `norm_mul_mSigma_lt_one` (for `SumAll_norm_mSig'`,
  `SumAll_norm_xi'`; only `‖ξ‖ < 1` is used), `gapK_le_norm` (public in `KLSumZero.lean`; for
  `SumAll_gapK_sq_le`, `SumAll_norm_one_sub_sq`, `SumAll_gapK_le_norm`), `Gauss.etaT_pos` (for
  `SumAll_etaT_pos`; `SumAll_etaT_eq` is `rfl` here), `card_Zd`, `KLisTSP_of_mem_TSP`.
* **Copied after renaming and kept private** (they are private in `KLSumZero.lean`):
  `gapK_pos`, `gapK_le_one`, `norm_edge_le`, the `goodPt` chain, `card_le_of_mem_TSP`,
  `card_TSPlong_le`, with the prefix `KLSumAll_`; then the sections 3-5 of `SumAll.lean`.
* **The factor `∏_i m(σ_i)` (DECISIONS §23).**  The merged `KLKpi` carries it, so `Alayer`
  contains it and `KLK_eq_sum_Kpi` has no separate `∏ m` (RBM2D's `Kcal_eq_sum_Kpi` has).  In
  `KLSumAll_pure_ge3` the identity `T_n = (W^d)^{-(n-1)} (L^d Alayer ∅)` therefore loses RBM2D's
  separate factor `∏ m(σ_i)`, and `‖Alayer‖` gains the factor `‖∏ m(σ_i)‖ = 1`.  Nowhere else
  does the factor enter (`n = 1, 2`, Ward, rotation, translation, the statement).
* The binders `(d : ℕ) (g : ℝ)` come first in `KLK_sumAll_le`, as in
  `SigmaPi_alt_sumZero_le_of_Qlayer_one` (KL7a); the rest of the statement is RBM2D's after the
  renaming and `W² ↦ W^d`.
* Section 7: the compiled instances at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `t = 1/2`,
  `κ = 1`: `n = 4`, `σ = (+,-,+,-)`; `n = 2`; `n = 3`, `σ = (+,+,-)` (RBM2D's check at :775 in
  `d = 3`); and the value `1/4` of the sum at `n = 2`, so that the instance is not `0 ≤ B`.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. Private helpers re-ported from `KLSumZero.lean` (where they are private) -/

section Helpers

variable {n : ℕ}

private theorem KLSumAll_isDiag_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d : Fin n × Fin n} (hd : d ∈ F) : IsDiag n d.1 d.2 :=
  (KLisTSP_of_mem_TSP hF).1 d hd

private theorem KLSumAll_crossingFree_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    CrossingFree F :=
  (KLisTSP_of_mem_TSP hF).2

private theorem KLSumAll_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ := by
  unfold gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem KLSumAll_gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

/-- The factor `f(t) = (1 - tμ)⁻¹ - 1` is bounded by `c⁻¹`. -/
private theorem KLSumAll_norm_edge_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) :
    ‖(1 - (t : ℂ) * μ)⁻¹ - 1‖ ≤ c⁻¹ := by
  have hne : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hct; linarith
  have h : (1 - (t : ℂ) * μ)⁻¹ - 1 = ((t : ℂ) * μ) * (1 - (t : ℂ) * μ)⁻¹ := by
    field_simp
    ring
  rw [h, norm_mul, norm_mul, hμ, Complex.norm_real, Real.norm_of_nonneg ht0, norm_inv, mul_one]
  have hinv : ‖1 - (t : ℂ) * μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hct
  have hc1 : 0 ≤ ‖1 - (t : ℂ) * μ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  nlinarith [ht1]

/-- A vertex `v` strictly inside the arc of `d` and not strictly inside the arc of any other
diagonal of `F` below `d`. -/
private def KLSumAll_goodPt {n : ℕ} (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n)
    (v : Fin n) : Prop :=
  d.1 < v ∧ v < d.2 ∧ ∀ e ∈ F, e ≠ d → KLArcLe e d → ¬(e.1 < v ∧ v < e.2)

private theorem KLSumAll_exists_goodPt {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d : Fin n × Fin n} (hd : d ∈ F) : ∃ v, KLSumAll_goodPt F d v := by
  have hdD := KLSumAll_isDiag_of_mem_TSP hF hd
  have hcf := KLSumAll_crossingFree_of_mem_TSP hF
  obtain ⟨hd12, hdadj, -⟩ := hdD
  rw [Fin.lt_def] at hd12
  set S := F.filter (fun e => e.1 = d.1 ∧ e.2 < d.2) with hSdef
  rcases S.eq_empty_or_nonempty with hS | hS
  · have hlt : d.1.val + 1 < n := by have := d.2.isLt; omega
    refine ⟨⟨d.1.val + 1, hlt⟩, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; simp
    · rw [Fin.lt_def]; simp only; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      simp only at h1 h2
      have he1 : e.1 = d.1 := Fin.ext (by omega)
      have he2 : e.2 < d.2 := by
        rw [Fin.lt_def]
        rcases Nat.lt_or_ge e.2.val d.2.val with h | h
        · exact h
        · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
      have : e ∈ S := mem_filter.2 ⟨he, he1, he2⟩
      rw [hS] at this
      exact absurd this (notMem_empty e)
  · obtain ⟨e₀, he₀, hmax⟩ := S.exists_max_image (fun e => e.2.val) hS
    obtain ⟨he₀F, he₀1, he₀2⟩ := mem_filter.1 he₀
    have he₀D := (KLSumAll_isDiag_of_mem_TSP hF he₀F).1
    rw [Fin.lt_def] at he₀D he₀2
    have he₀1' : e₀.1.val = d.1.val := congrArg Fin.val he₀1
    refine ⟨e₀.2, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; omega
    · rw [Fin.lt_def]; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      rcases Nat.lt_or_ge d.1.val e.1.val with h | h
      · apply hcf e₀ he₀F e he
        left
        refine ⟨?_, ?_, ?_⟩ <;> rw [Fin.lt_def] <;> omega
      · have he1 : e.1 = d.1 := Fin.ext (by omega)
        have he2 : e.2 < d.2 := by
          rw [Fin.lt_def]
          rcases Nat.lt_or_ge e.2.val d.2.val with h' | h'
          · exact h'
          · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
        have : e.2.val ≤ e₀.2.val := hmax e (mem_filter.2 ⟨he, he1, he2⟩)
        omega

private theorem KLSumAll_goodPt_inj {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {d d' : Fin n × Fin n} (hd : d ∈ F) (hd' : d' ∈ F) {v : Fin n}
    (hv : KLSumAll_goodPt F d v) (hv' : KLSumAll_goodPt F d' v) : d = d' := by
  by_contra hne
  have hcf := KLSumAll_crossingFree_of_mem_TSP hF
  obtain ⟨a1, a2, a3⟩ := hv
  obtain ⟨b1, b2, b3⟩ := hv'
  by_cases h1 : KLArcLe d' d
  · exact a3 d' hd' (Ne.symm hne) h1 ⟨b1, b2⟩
  by_cases h2 : KLArcLe d d'
  · exact b3 d hd hne h2 ⟨a1, a2⟩
  simp only [KLArcLe, Fin.le_def, not_and_or, not_le] at h1 h2
  rw [Fin.lt_def] at a1 a2 b1 b2
  have hc1 := hcf d hd d' hd'
  have hc2 := hcf d' hd' d hd
  simp only [Crossing, Fin.lt_def, not_or, not_and_or, not_lt] at hc1 hc2
  omega

/-- A crossing-free set of diagonals of the `n`-gon has at most `n - 2` elements. -/
private theorem KLSumAll_card_le_of_mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)}
    (hF : F ∈ TSP n) : F.card ≤ n - 2 := by
  classical
  let g : Fin n × Fin n → Fin n := fun d =>
    if h : ∃ v, KLSumAll_goodPt F d v then Classical.choose h else d.1
  have hg : ∀ d ∈ F, KLSumAll_goodPt F d (g d) := by
    intro d hd
    have h := KLSumAll_exists_goodPt hF hd
    simp only [g, h, ↓reduceDIte]
    exact Classical.choose_spec h
  have hcard : (Finset.Ioo 0 (n - 1)).card = n - 2 := by
    rw [Nat.card_Ioo]; omega
  rw [← hcard]
  refine card_le_card_of_injOn (fun d => (g d).val) (fun d hd => ?_) (fun d hd d' hd' h => ?_)
  · obtain ⟨h1, h2, -⟩ := hg d hd
    rw [Fin.lt_def] at h1 h2
    have := d.2.isLt
    simp only [coe_Ioo, Set.mem_Ioo]
    omega
  · have hv : g d = g d' := Fin.ext h
    have g' := hg d' hd'
    rw [← hv] at g'
    exact KLSumAll_goodPt_inj hF hd hd' (hg d hd) g'

/-- The number of trees: `#T_SP(σ,π) ≤ #T_SP(n) ≤ 2^{n²}`. -/
private theorem KLSumAll_card_TSPlong_le (n : ℕ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : (KLTSPlong n σ π).card ≤ 2 ^ (n ^ 2) := by
  calc (KLTSPlong n σ π).card ≤ (TSP n).card := card_filter_le _ _
    _ ≤ (diagonals n).powerset.card := card_filter_le _ _
    _ = 2 ^ (diagonals n).card := card_powerset _
    _ ≤ 2 ^ (n ^ 2) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_univ _
          _ = n ^ 2 := by simp [sq]

end Helpers

/-! ## 2. Scalar facts on `η_t` -/

section Scalars

private theorem KLSumAll_etaT_le_one (E : ℝ) {t : ℝ} (ht0 : 0 ≤ t) : Gauss.etaT E t ≤ 1 := by
  rw [Gauss.etaT]
  have h0 : 0 ≤ (mE E).im := by
    rw [mE_im]; positivity
  have h1 : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
    linarith
  nlinarith

end Scalars

/-! ## 3. Total sums, translation and rotation -/

section Total

variable {d L : ℕ} [NeZero L]

/-- The total sum `T_n(σ) = ∑_a 𝒦_{t,σ,a}`. -/
private noncomputable def KLSumAll_T (d L : ℕ) [NeZero L] (g : ℝ) (W : ℕ) (E t : ℝ) {n : ℕ}
    (σ : Fin n → Bool) : ℂ :=
  ∑ a : Fin n → Zd d L, KLK d L g W E t (KLloopOf d L σ a)

/-- Splitting off the last coordinate. -/
private theorem KLSumAll_sum_snoc {α M : Type*} [Fintype α] [AddCommMonoid M] (m : ℕ)
    (f : (Fin (m + 1) → α) → M) :
    ∑ a, f a = ∑ a' : Fin m → α, ∑ x : α, f (Fin.snoc (α := fun _ => α) a' x) := by
  rw [← Fintype.sum_prod_type', ← (Fin.snocEquiv (fun _ : Fin (m + 1) => α)).sum_comp]
  rw [← Equiv.sum_comp (Equiv.prodComm _ _)]
  rfl

private theorem KLSumAll_ofFn_rot {α : Type*} {k : ℕ} (f : Fin (k + 1) → α) :
    List.ofFn (fun i : Fin (k + 1) => f (i + 1))
      = List.ofFn (fun i : Fin k => f i.succ) ++ [f 0] := by
  rw [List.ofFn_succ']
  simp [Fin.coeSucc_eq_succ, Fin.last_add_one]

private theorem KLSumAll_T_rot {g : ℝ} (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ}
    (hE : |E| < 2) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool) :
    KLSumAll_T d L g W E t σ = KLSumAll_T d L g W E t (fun i => σ (i + 1)) := by
  unfold KLSumAll_T
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.subRight (1 : Fin (k + 1))) (Equiv.refl (Zd d L))) _ _ (fun a => ?_)
  have hea : (Equiv.arrowCongr (Equiv.subRight (1 : Fin (k + 1))) (Equiv.refl (Zd d L))) a
      = fun i => a (i + 1) := by
    funext i; simp [Equiv.arrowCongr]
  rw [hea]
  have h1 : KLloopOf d L σ a = ⟨σ 0 :: List.ofFn (fun i : Fin k => σ i.succ),
      a 0 :: List.ofFn (fun i : Fin k => a i.succ)⟩ := by
    simp only [KLloopOf]; rw [List.ofFn_succ, List.ofFn_succ]
  have h2 : KLloopOf d L (fun i => σ (i + 1)) (fun i => a (i + 1)) =
      ⟨List.ofFn (fun i : Fin k => σ i.succ) ++ [σ 0],
        List.ofFn (fun i : Fin k => a i.succ) ++ [a 0]⟩ := by
    simp only [KLloopOf]; rw [KLSumAll_ofFn_rot, KLSumAll_ofFn_rot]
  rw [h1, h2]
  exact KLK_rotate d L W g E hL hW hE t ht (σ 0) (a 0) _ _ (by simp)

open Fin.NatCast in
private theorem KLSumAll_T_rot_iter {g : ℝ} (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ}
    (hE : |E| < 2) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool)
    (j : ℕ) :
    KLSumAll_T d L g W E t σ = KLSumAll_T d L g W E t (fun i => σ (i + (j : Fin (k + 1)))) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, KLSumAll_T_rot hL hW hE ht]
    congr 1
    funext i
    congr 1
    push_cast
    rw [add_assoc, add_comm (1 : Fin (k + 1))]

open Fin.NatCast in
private theorem KLSumAll_exists_false_true {k : ℕ} (σ : Fin (k + 1) → Bool)
    (h : ¬ ∀ i, σ i = σ 0) : ∃ i, σ i = false ∧ σ (i + 1) = true := by
  by_contra hne0
  have hne : ∀ i, σ i = false → σ (i + 1) = false := fun i hi => by
    by_contra hc
    exact hne0 ⟨i, hi, by simpa using hc⟩
  obtain ⟨j0, hj0⟩ : ∃ j0, σ j0 = false := by
    obtain ⟨i, hi⟩ := not_forall.1 h
    cases h0 : σ 0
    · exact ⟨0, h0⟩
    · exact ⟨i, by simpa [h0] using hi⟩
  have hall : ∀ m : ℕ, σ (j0 + (m : Fin (k + 1))) = false := by
    intro m
    induction m with
    | zero => simpa using hj0
    | succ m ih =>
      have := hne _ ih
      simpa [Nat.cast_succ, ← add_assoc] using this
  have hall' : ∀ i, σ i = false := by
    intro i
    have := hall (i - j0).val
    simpa using this
  exact h fun i => by rw [hall' i, hall' 0]

/-- Translation invariance of the fibre sums (`KLK_translate`). -/
private theorem KLSumAll_fiber_const {g : ℝ} (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ}
    (hE : |E| < 2) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool)
    (y y' : Zd d L) :
    ∑ a ∈ univ.filter (fun a : Fin (k + 1) → Zd d L => a 0 = y),
        KLK d L g W E t (KLloopOf d L σ a)
      = ∑ a ∈ univ.filter (fun a : Fin (k + 1) → Zd d L => a 0 = y'),
          KLK d L g W E t (KLloopOf d L σ a) := by
  refine Finset.sum_nbij' (fun a i => a i + (y' - y)) (fun a i => a i - (y' - y))
    (fun a ha => ?_) (fun a ha => ?_) (fun a _ => ?_) (fun a _ => ?_) (fun a _ => ?_)
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [ha]; abel
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [ha]; abel
  · funext i; simp
  · funext i; simp
  · have h := KLK_translate d L W g E hL hW hE t ht (y' - y) (KLloopOf d L σ a)
      (by simp [LoopIdx.WF, KLloopOf])
    rw [← h]
    congr 1
    simp only [KLloopOf, List.map_ofFn]
    rfl

/-- `T_n(σ) = L^d ∑_{a : a₀ = a₁} 𝒦_{t,σ,a}`. -/
private theorem KLSumAll_T_eq_fiber {g : ℝ} (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ}
    (hE : |E| < 2) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 1) → Bool)
    (a₁ : Zd d L) :
    KLSumAll_T d L g W E t σ = (L : ℂ) ^ d *
      ∑ a ∈ univ.filter (fun a : Fin (k + 1) → Zd d L => a 0 = a₁),
        KLK d L g W E t (KLloopOf d L σ a) := by
  unfold KLSumAll_T
  rw [← Finset.sum_fiberwise univ (fun a : Fin (k + 1) → Zd d L => a 0)]
  rw [Finset.sum_congr rfl (fun y _ => KLSumAll_fiber_const hL hW hE ht σ y a₁)]
  rw [Finset.sum_const, Finset.card_univ, card_Zd]
  simp

omit [NeZero L] in
/-- The list form of `KLloopOf σ (snoc a' x)` for `σ₀ = +`, `σ_{last} = −`. -/
private theorem KLSumAll_loopOf_snoc {k : ℕ} (σ : Fin (k + 2) → Bool) (h0 : σ 0 = true)
    (hl : σ (Fin.last (k + 1)) = false) (a' : Fin (k + 1) → Zd d L) (x : Zd d L) :
    KLloopOf d L σ (Fin.snoc (α := fun _ => Zd d L) a' x) =
      ⟨true :: List.ofFn (fun i : Fin k => σ i.succ.castSucc) ++ [false],
        List.ofFn a' ++ [x]⟩ := by
  simp only [KLloopOf]
  rw [List.ofFn_succ' σ, List.ofFn_succ' (Fin.snoc (α := fun _ => Zd d L) a' x)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hl, List.concat_eq_append]
  rw [List.ofFn_succ (f := fun i : Fin (k + 1) => σ i.castSucc)]
  simp [h0]

omit [NeZero L] in
private theorem KLSumAll_loopOf_cons {k : ℕ} (σ : Fin (k + 2) → Bool) (b : Bool)
    (a' : Fin (k + 1) → Zd d L) :
    KLloopOf d L (Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 b) a' =
      ⟨b :: List.ofFn (fun i : Fin k => σ i.succ.castSucc), List.ofFn a'⟩ := by
  simp only [KLloopOf]
  rw [List.ofFn_succ]
  simp [Function.update_of_ne, Fin.succ_ne_zero]

/-- The Ward step on total sums (`KLK_ward`). -/
private theorem KLSumAll_T_ward {g : ℝ} (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {E : ℝ}
    (hE : |E| < 2) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {k : ℕ} (σ : Fin (k + 2) → Bool)
    (h0 : σ 0 = true) (hl : σ (Fin.last (k + 1)) = false) :
    KLSumAll_T d L g W E t σ = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
      (KLSumAll_T d L g W E t (fun i : Fin (k + 1) => σ i.castSucc)
        - KLSumAll_T d L g W E t
            (Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 false)) := by
  have hg : (fun i : Fin (k + 1) => σ i.castSucc)
      = Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 true := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp [h0]
    · simp [Function.update_of_ne hi]
  have hw : ∀ a' : Fin (k + 1) → Zd d L,
      ∑ x : Zd d L, KLK d L g W E t (KLloopOf d L σ (Fin.snoc (α := fun _ => Zd d L) a' x))
        = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
          (KLK d L g W E t (KLloopOf d L (fun i : Fin (k + 1) => σ i.castSucc) a')
            - KLK d L g W E t
              (KLloopOf d L (Function.update (fun i : Fin (k + 1) => σ i.castSucc) 0 false)
                a')) := by
    intro a'
    rw [Finset.sum_congr rfl (fun x _ => by rw [KLSumAll_loopOf_snoc σ h0 hl a' x])]
    have hward := KLK_ward d L W g E hL hW hE t ht.1 ht.2 true
      (List.ofFn (fun i : Fin k => σ i.succ.castSucc)) (List.ofFn a') (by simp)
    simp only [Bool.not_true] at hward
    rw [hward]
    have hgl := KLSumAll_loopOf_cons σ true a'
    rw [← hg] at hgl
    rw [hgl, KLSumAll_loopOf_cons σ false a']
  unfold KLSumAll_T
  rw [KLSumAll_sum_snoc (k + 1), Finset.sum_congr rfl (fun a' _ => hw a'), ← Finset.mul_sum,
    Finset.sum_sub_distrib]

end Total

/-! ## 4. Pure sign vectors -/

section Pure

variable {d L : ℕ} [NeZero L]

private theorem KLSumAll_norm_inv_one_sub_le {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht0 : 0 ≤ t) (s : Bool) :
    ‖(1 - (t : ℂ) * (mSigma E s * mSigma E s))⁻¹‖ ≤ (gapK κ)⁻¹ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  rw [norm_inv]
  exact inv_anti₀ (KLSumAll_gapK_pos hκ hκ2) (gapK_le_norm hκ hE ht0 s)

/-- `n = 1`. -/
private theorem KLSumAll_pure_one {g : ℝ} {W : ℕ} {E t : ℝ} (hE : |E| ≤ 2) (σ : Fin 1 → Bool) :
    ‖KLSumAll_T d L g W E t σ‖ ≤ (L : ℝ) ^ d := by
  have hK : ∀ a : Fin 1 → Zd d L, KLK d L g W E t (KLloopOf d L σ a) = mSigma E (σ 0) := by
    intro a
    simp [KLloopOf, List.ofFn_succ, KLK, KLgen, LoopIdx.length]
  unfold KLSumAll_T
  rw [Finset.sum_congr rfl (fun a _ => hK a), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, card_Zd]
  simp [norm_mSigma hE]

/-- `n = 2`, pure. -/
private theorem KLSumAll_pure_two {g : ℝ} (hL : 3 ≤ L) {W : ℕ} {κ E t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) :
    ‖KLSumAll_T d L g W E t (fun _ : Fin 2 => s)‖
      ≤ (L : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹ * (gapK κ)⁻¹) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hK : ∀ a : Fin 2 → Zd d L, KLK d L g W E t (KLloopOf d L (fun _ : Fin 2 => s) a)
      = ((W : ℂ) ^ d)⁻¹ * (mSigma E s * mSigma E s) *
        Theta d L g ((t : ℂ) * (mSigma E s * mSigma E s)) (a 0) (a 1) := by
    intro a
    have : KLloopOf d L (fun _ : Fin 2 => s) a = ⟨[s, s], [a 0, a 1]⟩ := by
      simp [KLloopOf, List.ofFn_succ]
    rw [this, KLK_two]
  have hξ : ‖(t : ℂ) * (mSigma E s * mSigma E s)‖ < 1 :=
    norm_mul_mSigma_lt_one hE2 ht.1 ht.2 s s
  unfold KLSumAll_T
  rw [Finset.sum_congr rfl (fun a _ => hK a)]
  rw [Fintype.sum_equiv (finTwoArrowEquiv (Zd d L)) _
    (fun p : Zd d L × Zd d L => ((W : ℂ) ^ d)⁻¹ * (mSigma E s * mSigma E s) *
        Theta d L g ((t : ℂ) * (mSigma E s * mSigma E s)) p.1 p.2)
    (fun a => by simp [finTwoArrowEquiv])]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_Theta_row_of_three_le (g := g) hL hξ]
  rw [Finset.sum_const, Finset.card_univ, card_Zd]
  have h2 : ‖((W : ℂ) ^ d)⁻¹‖ = ((W : ℝ) ^ d)⁻¹ := by simp
  have h3 : ‖mSigma E s * mSigma E s‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2]; norm_num
  have hC := KLSumAll_norm_inv_one_sub_le hκ hE ht.1 s
  have hAB : ‖((W : ℂ) ^ d)⁻¹ * (mSigma E s * mSigma E s)‖ = ((W : ℝ) ^ d)⁻¹ := by
    rw [norm_mul, h2, h3, mul_one]
  have hn : ‖((L ^ d : ℕ)) • (1 - (t : ℂ) * (mSigma E s * mSigma E s))⁻¹‖
      ≤ (L : ℝ) ^ d * (gapK κ)⁻¹ := by
    refine le_trans (norm_nsmul_le (E := ℂ)) ?_
    push_cast
    exact mul_le_mul_of_nonneg_left hC (by positivity)
  calc _ ≤ ‖((W : ℂ) ^ d)⁻¹ * (mSigma E s * mSigma E s)‖ *
        ‖((L ^ d : ℕ)) • (1 - (t : ℂ) * (mSigma E s * mSigma E s))⁻¹‖ := norm_mul_le _ _
    _ ≤ ((W : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d * (gapK κ)⁻¹) := by rw [hAB]; gcongr
    _ = (L : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹ * (gapK κ)⁻¹) := by ring

/-- `n = k + 3 ≥ 3`, pure: only `π = ∅` survives; `(eq_K-Kpi)`, `sum_Kpi_closed`.  Here the factor
`∏ m(σ_i)` of the merged `KLKpi` sits inside `Alayer` (DECISIONS §23): `KLK_eq_sum_Kpi` has no
separate `∏ m(σ_i)`, whereas RBM2D's `Kcal_eq_sum_Kpi` has one. -/
private theorem KLSumAll_pure_ge3 {g : ℝ} (hL : 3 ≤ L) {W : ℕ} {κ E t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) (k : ℕ) :
    ‖KLSumAll_T d L g W E t (fun _ : Fin (k + 3) => s)‖
      ≤ (L : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹) ^ (k + 2) *
          (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (2 * k + 4)) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hc := KLSumAll_gapK_pos hκ hκ2
  have hct := gapK_le_norm hκ hE ht.1 s
  have hD1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hc).2 (KLSumAll_gapK_le_one κ)
  set σ : Fin (k + 3) → Bool := fun _ => s with hσ
  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := fun s s' =>
    norm_mul_mSigma_lt_one hE2 ht.1 ht.2 s s'
  have hzero : ∀ π ∈ (diagonals (k + 3)).powerset, π ≠ ∅ →
      (L : ℂ) ^ d * Alayer (mSigma E) t σ π = 0 := by
    intro π _ hπ
    have hT : KLTSPlong (k + 3) σ π = ∅ := by
      unfold KLTSPlong
      refine Finset.filter_eq_empty_iff.2 fun F _ hF => hπ ?_
      rw [← hF]
      simp [KLFlong, hσ]
    simp [Alayer, Qlayer, hT]
  have hT : KLSumAll_T d L g W E t σ = ((W : ℂ) ^ d)⁻¹ ^ (k + 3 - 1) *
      ((L : ℂ) ^ d * Alayer (mSigma E) t σ ∅) := by
    unfold KLSumAll_T
    rw [Finset.sum_congr rfl
        (fun a _ => KLK_eq_sum_Kpi d L g W E t (n := k + 3) (by omega) σ a),
      ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    rw [Finset.sum_congr rfl (fun π _ => sum_Kpi_closed d L g (mSigma E) hm hL σ π)]
    exact Finset.sum_eq_single_of_mem ∅ (by simp) hzero
  -- the bound on `Alayer`
  have hQ : ‖Qlayer (mSigma E) t σ ∅‖ ≤ 2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1) := by
    unfold Qlayer
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ F ∈ KLTSPlong (k + 3) σ ∅,
        ‖∏ e ∈ F, edgeR (mSigma E) t (σ e.1) (σ e.2)‖ ≤ (gapK κ)⁻¹ ^ (k + 1) := by
      intro F hF
      have hFT : F ∈ TSP (k + 3) := (mem_filter.1 hF).1
      rw [norm_prod]
      calc ∏ e ∈ F, ‖edgeR (mSigma E) t (σ e.1) (σ e.2)‖
          ≤ ∏ _e ∈ F, (gapK κ)⁻¹ := by
            refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun e _ => ?_
            have hμ : ‖mSigma E s * mSigma E s‖ = 1 := by
              rw [norm_mul, norm_mSigma hE2]; norm_num
            exact KLSumAll_norm_edge_le hμ ht.1 ht.2.le hc hct
        _ = (gapK κ)⁻¹ ^ F.card := Finset.prod_const _
        _ ≤ (gapK κ)⁻¹ ^ (k + 1) :=
            pow_le_pow_right₀ hD1 (by have := KLSumAll_card_le_of_mem_TSP hFT; omega)
    calc ∑ F ∈ KLTSPlong (k + 3) σ ∅, ‖∏ e ∈ F, edgeR (mSigma E) t (σ e.1) (σ e.2)‖
        ≤ ∑ _F ∈ KLTSPlong (k + 3) σ ∅, (gapK κ)⁻¹ ^ (k + 1) := Finset.sum_le_sum hterm
      _ = (KLTSPlong (k + 3) σ ∅).card * (gapK κ)⁻¹ ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1) := by
          gcongr
          exact_mod_cast KLSumAll_card_TSPlong_le (k + 3) σ ∅
  have hprodm : ‖∏ i, mSigma E (σ i)‖ = 1 := by
    rw [norm_prod]; simp [hσ, norm_mSigma hE2]
  have hP : ‖∏ v : Fin (k + 3), (1 - (t : ℂ) * (mSigma E (σ v) * mSigma E (σ (v + 1))))⁻¹‖
      ≤ (gapK κ)⁻¹ ^ (k + 3) := by
    rw [norm_prod]
    calc _ ≤ ∏ _v : Fin (k + 3), (gapK κ)⁻¹ :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ =>
            KLSumAll_norm_inv_one_sub_le hκ hE ht.1 s
      _ = _ := by simp
  have hA : ‖Alayer (mSigma E) t σ ∅‖ ≤
      (gapK κ)⁻¹ ^ (k + 3) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1)) := by
    unfold Alayer
    rw [norm_mul, norm_mul, hprodm, one_mul]
    exact mul_le_mul hP hQ (norm_nonneg _) (by positivity)
  rw [hT, norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 : ‖((W : ℂ) ^ d)⁻¹‖ = ((W : ℝ) ^ d)⁻¹ := by simp
  have h3 : ‖(L : ℂ)‖ = L := by simp
  rw [h1, h3]
  have hk : k + 3 - 1 = k + 2 := by omega
  rw [hk]
  have hpos : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ ^ (k + 2) := by positivity
  calc _ ≤ ((W : ℝ) ^ d)⁻¹ ^ (k + 2) * ((L : ℝ) ^ d *
        ((gapK κ)⁻¹ ^ (k + 3) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1)))) := by gcongr
    _ = _ := by ring

/-- The bound `B_n = 2^{n²} c_κ^{-2n} (W^d η_t)^{-(n-1)}`. -/
private noncomputable def KLSumAll_B (d : ℕ) (κ : ℝ) (W : ℕ) (E t : ℝ) (n : ℕ) : ℝ :=
  2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (((W : ℝ) ^ d * Gauss.etaT E t)⁻¹) ^ (n - 1)

/-- Pure sign vectors: `‖T_n(s,…,s)‖ ≤ L^d B_n`. -/
private theorem KLSumAll_pure_bound {g : ℝ} (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {κ E t : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) (k : ℕ) :
    ‖KLSumAll_T d L g W E t (fun _ : Fin (k + 1) => s)‖
      ≤ (L : ℝ) ^ d * KLSumAll_B d κ W E t (k + 1) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hE' : |E| < 2 := by linarith
  have hc := KLSumAll_gapK_pos hκ hκ2
  have hD1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hc).2 (KLSumAll_gapK_le_one κ)
  have hη := Gauss.etaT_pos hE' ht.2
  have hη1 := KLSumAll_etaT_le_one E ht.1
  have hW0 : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  have hwu : ((W : ℝ) ^ d)⁻¹ ≤ ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ :=
    inv_anti₀ (mul_pos hW0 hη) (by nlinarith)
  have hw0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
  unfold KLSumAll_B
  match k with
  | 0 =>
    refine (KLSumAll_pure_one hE2 _).trans ?_
    simp only [zero_add, Nat.sub_self, pow_zero, mul_one]
    refine le_mul_of_one_le_right hL0 ?_
    calc (1 : ℝ) ≤ 1 * 1 := by norm_num
      _ ≤ 2 ^ (1 ^ 2) * (gapK κ)⁻¹ ^ (2 * 1) := by
        gcongr
        · norm_num
        · exact one_le_pow₀ hD1
  | 1 =>
    refine (KLSumAll_pure_two hL hκ hE ht s).trans ?_
    simp only [Nat.add_sub_cancel, pow_one]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have h1 : (gapK κ)⁻¹ ≤ (gapK κ)⁻¹ ^ (2 * (1 + 1)) := by
      calc (gapK κ)⁻¹ = (gapK κ)⁻¹ ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hD1 (by norm_num)
    have h2 : (1 : ℝ) ≤ 2 ^ ((1 + 1) ^ 2) := one_le_pow₀ (by norm_num)
    calc ((W : ℝ) ^ d)⁻¹ * (gapK κ)⁻¹
        ≤ ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ * (gapK κ)⁻¹ ^ (2 * (1 + 1)) := by gcongr
      _ = 1 * (gapK κ)⁻¹ ^ (2 * (1 + 1)) * ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ := by ring
      _ ≤ 2 ^ ((1 + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (1 + 1)) *
            ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ := by
        gcongr
  | k + 2 =>
    refine (KLSumAll_pure_ge3 hL hκ hE ht s k).trans ?_
    have hk : k + 2 + 1 - 1 = k + 2 := by omega
    rw [hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have h1 : ((W : ℝ) ^ d)⁻¹ ^ (k + 2) ≤ ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ ^ (k + 2) :=
      pow_le_pow_left₀ hw0 hwu _
    have h2 : (gapK κ)⁻¹ ^ (2 * k + 4) ≤ (gapK κ)⁻¹ ^ (2 * (k + 2 + 1)) :=
      pow_le_pow_right₀ hD1 (by omega)
    have h3 : (0 : ℝ) ≤ 2 ^ ((k + 3) ^ 2) := by positivity
    calc ((W : ℝ) ^ d)⁻¹ ^ (k + 2) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (2 * k + 4))
        ≤ ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ ^ (k + 2) *
            (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 2 + 1))) := by gcongr
      _ = 2 ^ ((k + 2 + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 2 + 1)) *
            ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ ^ (k + 2) := by ring

end Pure

/-! ## 5. The induction over all sign vectors -/

section Induction

variable {d L : ℕ} [NeZero L]

open Fin.NatCast in
/-- The claim `P(n)` for every sign vector: `‖T_n(σ)‖ ≤ L^d B_n`. -/
private theorem KLSumAll_main {g : ℝ} (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) {κ E t : ℝ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) :
    ∀ σ : Fin (k + 1) → Bool,
      ‖KLSumAll_T d L g W E t σ‖ ≤ (L : ℝ) ^ d * KLSumAll_B d κ W E t (k + 1) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hE' : |E| < 2 := by linarith
  have hc := KLSumAll_gapK_pos hκ hκ2
  have hD1 : 1 ≤ (gapK κ)⁻¹ := (one_le_inv₀ hc).2 (KLSumAll_gapK_le_one κ)
  have hη := Gauss.etaT_pos hE' ht.2
  have hW0 : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  have hu : (0 : ℝ) < ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ := inv_pos.2 (mul_pos hW0 hη)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
  induction k with
  | zero =>
    intro σ
    have h := KLSumAll_pure_bound (d := d) (g := g) hL hW hκ hE ht (σ 0) 0
    have hσ : σ = fun _ => σ 0 := by
      funext i; rw [Fin.ext (show i.val = (0 : Fin (0 + 1)).val by have := i.isLt; simp)]
    rw [hσ]
    exact h
  | succ k ih =>
    intro σ
    by_cases hp : ∀ i, σ i = σ 0
    · have hσ : σ = fun _ => σ 0 := funext hp
      rw [hσ]
      exact KLSumAll_pure_bound (d := d) (g := g) hL hW hκ hE ht (σ 0) (k + 1)
    · obtain ⟨i0, hi0f, hi0t⟩ := KLSumAll_exists_false_true σ hp
      set σ' : Fin (k + 2) → Bool :=
        fun i => σ (i + (((i0 + 1 : Fin (k + 2)).val : ℕ) : Fin (k + 2))) with hσ'
      have hrot := KLSumAll_T_rot_iter (d := d) (g := g) hL hW hE' ht σ
        ((i0 + 1 : Fin (k + 2)).val)
      have h0 : σ' 0 = true := by simpa [hσ'] using hi0t
      have hl : σ' (Fin.last (k + 1)) = false := by
        have : Fin.last (k + 1) + (((i0 + 1 : Fin (k + 2)).val : ℕ) : Fin (k + 2)) = i0 := by
          rw [Fin.cast_val_eq_self, add_comm i0 1, ← add_assoc, Fin.last_add_one, zero_add]
        change σ (Fin.last (k + 1) + _) = false
        rw [this]; exact hi0f
      rw [hrot]
      change ‖KLSumAll_T d L g W E t σ'‖ ≤ _
      rw [KLSumAll_T_ward hL hW hE' ht σ' h0 hl, norm_mul]
      have hκn : ‖(2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹‖
          = (2 * (((W : ℝ) ^ d * Gauss.etaT E t)))⁻¹ := by
        rw [norm_inv]
        congr 1
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_I, Complex.norm_natCast,
          Complex.norm_real, Real.norm_of_nonneg hη.le, mul_one]
        ring
      rw [hκn]
      have h1 := ih (fun i : Fin (k + 1) => σ' i.castSucc)
      have h2 := ih (Function.update (fun i : Fin (k + 1) => σ' i.castSucc) 0 false)
      have h3 : ‖KLSumAll_T d L g W E t (fun i : Fin (k + 1) => σ' i.castSucc)
          - KLSumAll_T d L g W E t
              (Function.update (fun i : Fin (k + 1) => σ' i.castSucc) 0 false)‖
          ≤ 2 * ((L : ℝ) ^ d * KLSumAll_B d κ W E t (k + 1)) := by
        refine (norm_sub_le _ _).trans ?_
        linarith
      refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans ?_
      set u := ((W : ℝ) ^ d * Gauss.etaT E t)⁻¹ with hudef
      have hinv : (2 * ((W : ℝ) ^ d * Gauss.etaT E t))⁻¹ = 2⁻¹ * u := by
        rw [hudef, mul_inv]
      rw [hinv]
      unfold KLSumAll_B
      have h4 : (2 : ℝ) ^ ((k + 1) ^ 2) ≤ 2 ^ ((k + 1 + 1) ^ 2) :=
        pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
      have h5 : (gapK κ)⁻¹ ^ (2 * (k + 1)) ≤ (gapK κ)⁻¹ ^ (2 * (k + 1 + 1)) :=
        pow_le_pow_right₀ hD1 (by omega)
      have hk1 : k + 1 - 1 = k := by omega
      have hk2 : k + 1 + 1 - 1 = k + 1 := by omega
      rw [hk1, hk2]
      calc 2⁻¹ * u * (2 * ((L : ℝ) ^ d * (2 ^ ((k + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 1)) * u ^ k)))
          = (L : ℝ) ^ d * ((2 ^ ((k + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 1))) * u ^ (k + 1)) := by
            ring
        _ ≤ (L : ℝ) ^ d * ((2 ^ ((k + 1 + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (k + 1 + 1))) *
              u ^ (k + 1)) := by gcongr
        _ = _ := by ring

end Induction

/-! ## 6. The theorem -/

section Main

variable (d : ℕ) (g : ℝ)

/-- **`(sumallAinK)` with an explicit constant** (RBM2D `Kcal_sumAll_le`, `Loop/SumAll.lean:749`
at `c9a24cf`): for `σ₁ = +`, `σ_n = -`, `n ≥ 2`,
`|∑_{a₂,…,aₙ} 𝒦_{t,σ,a}| ≤ 2^{n²} c_κ^{-2n} (W^d η_t)^{-(n-1)}`, `c_κ = gapK κ`. -/
theorem KLK_sumAll_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) (hn : 2 ≤ n) (σ : Fin n → Bool),
      σ ⟨0, by omega⟩ = true → σ ⟨n - 1, by omega⟩ = false → ∀ a₁ : Zd d L,
        ‖∑ a ∈ Finset.univ.filter (fun a : Fin n → Zd d L => a ⟨0, by omega⟩ = a₁),
            KLK d L g W E t (KLloopOf d L σ a)‖
          ≤ 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (((W : ℝ) ^ d * Gauss.etaT E t)⁻¹) ^ (n - 1) := by
  intro κ hκ L W _ hL hW E hE t ht n hn σ _ _ a₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have hE' : |E| < 2 := by linarith
  have hmain := KLSumAll_main (d := d) (g := g) hL hW hκ hE ht (k + 1) σ
  have hfib := KLSumAll_T_eq_fiber (d := d) (g := g) hL hW hE' ht σ a₁
  have hz : ((⟨0, by omega⟩ : Fin (k + 1 + 1))) = 0 := rfl
  simp only [hz]
  rw [hfib, norm_mul, norm_pow, Complex.norm_natCast] at hmain
  have hL2 : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    positivity
  exact le_of_mul_le_mul_left hmain hL2

end Main

/-! ## 7. The compiled instances: `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `t = 1/2`, `κ = 1`

`L = 3` (`27` blocks), `W = 2` (`W^d = 8`), `m(+) = i`, `η_t = 1/2`, `c_κ = gapK 1 = 1`.  Every
deterministic hypothesis of `KLK_sumAll_le` (`0 < 1`, `3 ≤ 3`, `1 ≤ 2`, `|0| ≤ 2 - 1`,
`1/2 ∈ [0,1)`, `2 ≤ n`, `σ₁ = +`, `σ_n = -`) is discharged; no hypothesis is left. -/

section Instances

private theorem KLSumAll_gapK_one : gapK 1 = 1 := by
  unfold gapK
  exact min_eq_left (Real.one_le_sqrt.2 (by norm_num))

private theorem KLSumAll_etaT_half : Gauss.etaT 0 (1 / 2) = 1 / 2 := by
  rw [Gauss.etaT, mE_im]
  have h : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]
  norm_num

/-- `KLK_sumAll_le` at `n = 4`, `σ = (+,-,+,-)`: the fibre `a₁` has `27³` terms. -/
theorem KLSumAll_inst_four (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 4 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false, true, false] a)‖
      ≤ 2 ^ (4 ^ 2) * (gapK 1)⁻¹ ^ (2 * 4) *
          ((((2 : ℕ) : ℝ) ^ 3 * Gauss.etaT 0 (1 / 2))⁻¹) ^ (4 - 1) :=
  KLK_sumAll_le 3 (1 / 2) 1 one_pos 3 2 (by norm_num) (by norm_num) 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 (by norm_num) ![true, false, true, false] rfl rfl a₁

/-- The right side of `KLSumAll_inst_four` is `2^{16} · 1 · (1/4)³ = 1024`. -/
theorem KLSumAll_inst_four_val (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 4 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false, true, false] a)‖ ≤ 1024 := by
  have h := KLSumAll_inst_four a₁
  rw [KLSumAll_gapK_one, KLSumAll_etaT_half] at h
  norm_num at h
  exact h

/-- `KLK_sumAll_le` at `n = 2`, `σ = (+,-)`. -/
theorem KLSumAll_inst_two (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false] a)‖
      ≤ 2 ^ (2 ^ 2) * (gapK 1)⁻¹ ^ (2 * 2) *
          ((((2 : ℕ) : ℝ) ^ 3 * Gauss.etaT 0 (1 / 2))⁻¹) ^ (2 - 1) :=
  KLK_sumAll_le 3 (1 / 2) 1 one_pos 3 2 (by norm_num) (by norm_num) 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 2 (by norm_num) ![true, false] rfl rfl a₁

/-- `KLK_sumAll_le` at `n = 3`, `σ = (+,+,-)` (RBM2D's check at :775 in `d = 3`). -/
theorem KLSumAll_inst_three (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 3 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, true, false] a)‖
      ≤ 2 ^ (3 ^ 2) * (gapK 1)⁻¹ ^ (2 * 3) *
          ((((2 : ℕ) : ℝ) ^ 3 * Gauss.etaT 0 (1 / 2))⁻¹) ^ (3 - 1) :=
  KLK_sumAll_le 3 (1 / 2) 1 one_pos 3 2 (by norm_num) (by norm_num) 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 3 (by norm_num) ![true, true, false] rfl rfl a₁

private theorem KLSumAll_mSigma_zero : mSigma 0 true * mSigma 0 false = 1 := by
  have h := norm_mE (E := 0) (by norm_num)
  have h1 : mE 0 * (starRingEnd ℂ) (mE 0) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  simpa [mSigma] using h1

/-- The sum of `KLSumAll_inst_two` is not `0`: it is `W^{-d}/(1 - t) = 1/4` (`(Kn2sol)`), against
the bound `2^4 · 1 · (1/4) = 4`. -/
theorem KLSumAll_inst_two_val (a₁ : Zd 3 3) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false] a) = 1 / 4 := by
  have hm := KLSumAll_mSigma_zero
  have hξ : ‖(((1 / 2 : ℝ) : ℂ)) * (mSigma 0 true * mSigma 0 false)‖ < 1 := by
    rw [hm]; norm_num
  have hK : ∀ a : Fin 2 → Zd 3 3, KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false] a)
      = ((2 : ℂ) ^ 3)⁻¹ * (mSigma 0 true * mSigma 0 false) *
        Theta 3 3 (1 / 2) (((1 / 2 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) (a 0) (a 1) := by
    intro a
    have : KLloopOf 3 3 ![true, false] a = ⟨[true, false], [a 0, a 1]⟩ := by
      simp [KLloopOf, List.ofFn_succ]
    rw [this, KLK_two]
    norm_num
  rw [Finset.sum_filter]
  rw [Fintype.sum_equiv (finTwoArrowEquiv (Zd 3 3)) _
    (fun p : Zd 3 3 × Zd 3 3 => if p.1 = a₁ then
      ((2 : ℂ) ^ 3)⁻¹ * (mSigma 0 true * mSigma 0 false) *
        Theta 3 3 (1 / 2) (((1 / 2 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) p.1 p.2 else 0)
    (fun a => by rw [hK a]; rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a₁ (fun x _ hx => by simp [hx]) (fun h => absurd (Finset.mem_univ a₁) h)]
  simp only [ite_true]
  rw [← Finset.mul_sum, sum_Theta_row_of_three_le (g := (1 / 2 : ℝ)) (by norm_num) hξ, hm]
  norm_num

end Instances

end RBM.Loop
