/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KPure
import RBM3D.BA.KWard
import RBM3D.BA.KInduct
import RBM3D.BA.KMolecule
import RBM3D.Loop.KLMolecule

/-!
# Stage K, row K08a: Ward bound for sums of `𝒦` and the signed sum-zero of `BASig`

Ticket T2385 (design BA-DK, `docs/reports/T2360-design.md` §3 (c), §5; supervisor
`2026-10-09-2051.md` K-b, `2026-10-10-1155.md` C1; statements fixed by
`docs/reports/T2385-prove.md` section (a+) (iv), audited in `docs/reports/T2385-1a-audit.md`).
Paper: `(eq:Sigma-empty-sum-zero)` (`A_deterministic_estimates.tex:728-734`), which the TeX only
cites; here it is proved from `(WI_calK)` (`baK_ward`), the cut factorisation
`(eq:molecule-Kpi)` (`baSigmaPi_cut`) and translation invariance.

1. `baSigmaPi_slice`: the slice sums `Σ_{δ_r = x} Σ^{(π)}(δ)` do not depend on `(r, x)`
   (translation invariance).
2. `baK_sumAll_eq_layers`: `(W^d)^{n-1} (1-t)^n Σ_a 𝒦 = Σ_π Σ_δ Σ^{(π)}` (column sums of
   `Θ^{(+,-)}`).
3. `baK_sumAll_le`: the Ward bound for sums of `𝒦`, `|Σ_a 𝒦^{(n)}| ≤ B L^d (W^d η_t)^{-(n-1)}`
   (induction on `n`: `baK_ward` after a rotation of the loop; the constant charge vector by the
   pure-loop bounds).
4. `baSigmaPi_total_le`: `|Σ_δ Σ^{(π)}(δ)| ≤ C L^d (1-t)` at alternating `σ`, every layer `π`
   (induction on `n`; the cut recursion `(1-t) L^d 𝒮(σ,π) = t 𝒮(σ_in,∅) 𝒮(σ_out,π')`).
5. `baSig_signed_sum_unif`, `baSig_signed_sum`: the first bound clause of `SigSumZeroAbs`
   (`Loop/KLIndStepA.lean:1036`) at `BASig`, uniformly in `(L, g ≤ Λ, E, m, t < 1)`: constants
   depend on `(d, n, Λ, κ)` only (C1).
6. Compiled instances at the flow point `P` of `(d, L) = (3, 4)`, `n = 4` and `n = 6`.

Public: the declarations above; every other helper is `private` with the stem `KSumZeroA_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. The slice sums of `Σ^{(π)}` do not depend on the slice -/

section Slice

variable {d L n : ℕ} [NeZero L] [NeZero n]

/-- **A1 (the twin of `SumZero_sum_slice`)**: for a translation invariant `M`, `L^d Σ_{δ_r = x} Σ^{(π)}(δ) = Σ_δ Σ^{(π)}(δ)`
for every root `r`, label `x` and layer `π`: translating by `y - x` maps the slice `δ_r = x` onto the slice `δ_r = y`
(`baSigmaPi_shift`), and `|Z_L^d| = L^d`. -/
theorem baSigmaPi_slice (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (r : Fin n) (x : Zd d L) :
    (L : ℂ) ^ d * ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = x), BASigmaPi d L n M t σ π δ =
      ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ π δ := by
  classical
  set S := ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = x), BASigmaPi d L n M t σ π δ with hS
  have key : ∀ y : Zd d L, ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = y),
      BASigmaPi d L n M t σ π δ = S := by
    intro y
    refine Finset.sum_nbij' (fun δ j => δ j - y + x) (fun δ j => δ j - x + y) ?_ ?_ ?_ ?_ ?_
    · intro δ hδ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ ⊢
      simp [hδ]
    · intro δ hδ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ ⊢
      simp [hδ]
    · intro δ _
      funext j
      simp
    · intro δ _
      funext j
      simp
    · intro δ _
      have h := baSigmaPi_shift M hshift t σ π δ (x - y)
      have e : (fun j => δ j + (x - y)) = fun j => δ j - y + x := by
        funext j
        ring
      rw [e] at h
      exact h.symm
  rw [← Finset.sum_fiberwise Finset.univ (fun δ : Fin n → Zd d L => δ r)]
  simp only [key, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
  push_cast
  ring

end Slice

/-! ## 2. Column sums of `Θ^{(+,-)}` and the layer identity -/

section Layers

variable {d L : ℕ} [NeZero L]

/-- Row sums of the BA propagator at distinct charges: `Σ_b Θ^{(s,s')}_{xb} = (1-t)⁻¹` for `s ≠ s'`
(`BATheta_row_sum_pm`, and `BATheta_swap` for `(-,+)`). -/
private theorem KSumZeroA_theta_row {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) {s s' : Bool} (hss : s ≠ s') (x : Zd d L) :
    ∑ b, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s' x b = (1 - (t : ℂ))⁻¹ := by
  rw [show BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s' = BATheta d L g E m t s s' from rfl]
  cases s <;> cases s'
  · exact absurd rfl hss
  · rw [BATheta_swap]
    exact BATheta_row_sum_pm d L g κ E m hr t ht0 ht1 x
  · exact BATheta_row_sum_pm d L g κ E m hr t ht0 ht1 x
  · exact absurd rfl hss

/-- Column sums of the BA propagator at distinct charges: `Σ_a Θ^{(s,s')}_{ax} = (1-t)⁻¹` for `s ≠ s'`
(`Θᵀ = Θ`, `BATheta_isSymm`). -/
private theorem KSumZeroA_theta_col {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) {s s' : Bool} (hss : s ≠ s') (x : Zd d L) :
    ∑ a, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s' a x = (1 - (t : ℂ))⁻¹ := by
  have hsymm := BATheta_isSymm d L g κ E m hr t ht0 ht1 s s'
  have h : ∀ a, BATheta d L g E m t s s' a x = BATheta d L g E m t s s' x a := fun a => by
    have := congrFun (congrFun hsymm x) a
    simpa [Matrix.transpose_apply] using this
  have e := KSumZeroA_theta_row hr ht0 ht1 hss x
  rw [show BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s' = BATheta d L g E m t s s' from rfl] at e ⊢
  simp only [h]
  exact e

variable {n : ℕ} [NeZero n]

/-- **A2 (the layer identity)**: for alternating `σ` (`n ≥ 3`) every leaf edge of every tree has distinct charges, so
`Σ_a Θ^{(σ_v,σ_{v+1})}(a_v, δ_v) = (1-t)⁻¹`: `(1-t)^n Σ_a K^{(π)}(σ,a) = Σ_δ Σ^{(π)}(δ)`, and with `(eq_K-Kpi)`
(`baK_eq_sum_Kpi`) `(W^d)^{n-1} (1-t)^n Σ_a 𝒦^{(n)}_{t,σ,a} = Σ_{π ⊆ Z_n^{off}} Σ_δ Σ^{(π)}(δ)`.  `1 ≤ W` is needed:
at `W = 0` Lean's `0⁻¹ = 0` makes the left side `0`. -/
theorem baK_sumAll_eq_layers {κ g E : ℝ} {m : ℂ} (hκ : 0 < κ) (hg : 0 < g) (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W)
    (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (hn : 3 ≤ n) (σ : Fin n → Bool)
    (halt : ∀ j, σ j ≠ σ (j + 1)) :
    ((W : ℂ) ^ d) ^ (n - 1) * ((1 - (t : ℂ)) ^ n *
      ∑ a : Fin n → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)) =
      ∑ π ∈ (diagonals n).powerset, ∑ δ : Fin n → Zd d L,
        BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ π δ := by
  have hW0 : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have ht1 : (1 - (t : ℂ)) ≠ 0 := by
    intro h
    have h' : (t : ℂ) = 1 := by linear_combination -h
    have : t = 1 := by exact_mod_cast h'
    linarith [ht.2]
  have hlayer : ∀ π : Finset (Fin n × Fin n), ∑ a : Fin n → Zd d L,
      BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π =
        ((1 - (t : ℂ))⁻¹) ^ n * ∑ δ : Fin n → Zd d L,
          BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ π δ := by
    intro π
    simp only [baKpi_eq_sum_SigmaPi]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← Finset.mul_sum]
    have hprod : ∑ a : Fin n → Zd d L, ∏ v, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t (σ v) (σ (v + 1))
        (a v) (δ v) = ((1 - (t : ℂ))⁻¹) ^ n := by
      have := (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Zd d L)))
        (fun v x => BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t (σ v) (σ (v + 1)) x (δ v))).symm
      rw [Fintype.piFinset_univ] at this
      rw [this]
      rw [Finset.prod_congr rfl fun v _ => KSumZeroA_theta_col hr ht.1 ht.2 (halt v) (δ v)]
      simp
    rw [hprod]
    ring
  simp only [baK_eq_sum_Kpi d hκ hg hL W hr ht hn σ _]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hlayer]
  rw [← Finset.mul_sum]
  have e1 : ((W : ℂ) ^ d) ^ (n - 1) * (((W : ℂ) ^ d)⁻¹) ^ (n - 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hW0, one_pow]
  have e2 : (1 - (t : ℂ)) ^ n * ((1 - (t : ℂ))⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ht1, one_pow]
  generalize ∑ π ∈ (diagonals n).powerset, ∑ δ : Fin n → Zd d L,
    BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ π δ = X
  calc _ = (((W : ℂ) ^ d) ^ (n - 1) * (((W : ℂ) ^ d)⁻¹) ^ (n - 1)) *
        ((1 - (t : ℂ)) ^ n * ((1 - (t : ℂ))⁻¹) ^ n) * X := by ring
    _ = X := by rw [e1, e2]; ring

end Layers

/-! ## 3. The Ward bound for sums of `𝒦` (T1) -/

section Ward

variable {d L : ℕ} [NeZero L]

omit [NeZero L] in
/-- One step of the rotation of a loop, in the `Fin` form: `K(σ, a) = K(σ ∘ (· + 1), a ∘ (· + 1))`. -/
private theorem KSumZeroA_rot1 {K : LoopIdx (Zd d L) → ℂ}
    (hrot : ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      K ⟨s :: σ, b :: a⟩ = K ⟨σ ++ [s], a ++ [b]⟩)
    {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d L) :
    K (KLloopOf d L σ a) = K (KLloopOf d L (fun j => σ (j + 1)) (fun j => a (j + 1))) := by
  have h1 : ∀ (f : Fin (k + 1) → Bool), List.ofFn (fun j => f (j + 1)) =
      List.ofFn (fun i : Fin k => f i.succ) ++ [f 0] := by
    intro f
    rw [List.ofFn_succ']
    simp [Fin.coeSucc_eq_succ, Fin.last_add_one]
  have h2 : ∀ (f : Fin (k + 1) → Zd d L), List.ofFn (fun j => f (j + 1)) =
      List.ofFn (fun i : Fin k => f i.succ) ++ [f 0] := by
    intro f
    rw [List.ofFn_succ']
    simp [Fin.coeSucc_eq_succ, Fin.last_add_one]
  unfold KLloopOf
  rw [h1 σ, h2 a, List.ofFn_succ (f := σ), List.ofFn_succ (f := a)]
  exact hrot (σ 0) (a 0) _ _ (by simp)

open Fin.NatCast in
omit [NeZero L] in
/-- `r` steps of the rotation. -/
private theorem KSumZeroA_rotN {K : LoopIdx (Zd d L) → ℂ}
    (hrot : ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      K ⟨s :: σ, b :: a⟩ = K ⟨σ ++ [s], a ++ [b]⟩)
    {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d L) (r : ℕ) :
    K (KLloopOf d L σ a) =
      K (KLloopOf d L (fun j => σ (j + (r : Fin (k + 1)))) (fun j => a (j + (r : Fin (k + 1))))) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ih, KSumZeroA_rot1 hrot]
    have e : ∀ j : Fin (k + 1), j + 1 + (r : Fin (k + 1)) = j + ((r + 1 : ℕ) : Fin (k + 1)) := fun j => by
      rw [Nat.cast_succ]
      abel
    simp only [e]

open Fin.NatCast in
/-- The sum over the labels of a loop is rotation invariant (`a ↦ a ∘ (· + r)` is a bijection). -/
private theorem KSumZeroA_sum_rot {K : LoopIdx (Zd d L) → ℂ}
    (hrot : ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      K ⟨s :: σ, b :: a⟩ = K ⟨σ ++ [s], a ++ [b]⟩)
    {k : ℕ} (σ : Fin (k + 1) → Bool) (r : ℕ) :
    ∑ a : Fin (k + 1) → Zd d L, K (KLloopOf d L σ a) =
      ∑ a : Fin (k + 1) → Zd d L, K (KLloopOf d L (fun j => σ (j + (r : Fin (k + 1)))) a) := by
  calc ∑ a : Fin (k + 1) → Zd d L, K (KLloopOf d L σ a)
      = ∑ a : Fin (k + 1) → Zd d L, K (KLloopOf d L (fun j => σ (j + (r : Fin (k + 1))))
          (fun j => a (j + (r : Fin (k + 1))))) := Finset.sum_congr rfl fun a _ => KSumZeroA_rotN hrot σ a r
    _ = _ := Fintype.sum_equiv (Equiv.arrowCongr (Equiv.addRight (r : Fin (k + 1))).symm (Equiv.refl _)) _ _
          (fun a => rfl)

/-- **The Ward step in `Fin` form** (the sum over the last label of a loop `(s, μ, -s)`): if
`Σ_x K(s, μ, -s; a, x) = c (K(+, μ; a) - K(-, μ; a))` (the shape of `baK_ward`), then for `σ` of length `k + 2` with
`σ_last = -σ_0`, `Σ_a K(σ, a) = c (Σ_{a'} K((+, μ), a') - Σ_{a'} K((-, μ), a'))`, `μ = (σ_1, …, σ_k)`. -/
private theorem KSumZeroA_ward_fin {K : LoopIdx (Zd d L) → ℂ} {c : ℂ}
    (hward : ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, K ⟨s :: μ ++ [!s], a ++ [x]⟩ = c * (K ⟨true :: μ, a⟩ - K ⟨false :: μ, a⟩))
    {k : ℕ} (σ : Fin (k + 2) → Bool) (hσ : σ (Fin.last _) = !σ 0) :
    ∑ a : Fin (k + 2) → Zd d L, K (KLloopOf d L σ a) =
      c * (∑ a : Fin (k + 1) → Zd d L,
          K (KLloopOf d L (Fin.cons true (fun j : Fin k => σ j.castSucc.succ) : Fin (k + 1) → Bool) a) -
        ∑ a : Fin (k + 1) → Zd d L,
          K (KLloopOf d L (Fin.cons false (fun j : Fin k => σ j.castSucc.succ) : Fin (k + 1) → Bool) a)) := by
  have hσl : List.ofFn σ = σ 0 :: (List.ofFn (fun j : Fin k => σ j.castSucc.succ) ++ [!σ 0]) := by
    rw [List.ofFn_succ, List.ofFn_succ' (fun i : Fin (k + 1) => σ i.succ)]
    simp [Fin.succ_last, hσ]
  have hsnoc : ∀ (a' : Fin (k + 1) → Zd d L) (x : Zd d L),
      List.ofFn (Fin.snoc a' x : Fin (k + 2) → Zd d L) = List.ofFn a' ++ [x] := by
    intro a' x
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  have hcons : ∀ (b : Bool), List.ofFn (Fin.cons b (fun j : Fin k => σ j.castSucc.succ) : Fin (k + 1) → Bool) =
      b :: List.ofFn (fun j : Fin k => σ j.castSucc.succ) := fun b => List.ofFn_cons _ _
  have e := Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k + 2) => Zd d L))
    (fun p => K (KLloopOf d L σ (Fin.snocEquiv (fun _ : Fin (k + 2) => Zd d L) p)))
    (fun a => K (KLloopOf d L σ a)) (fun _ => rfl)
  rw [← e, Fintype.sum_prod_type, Finset.sum_comm]
  have hpt : ∀ a' : Fin (k + 1) → Zd d L, ∑ x : Zd d L,
      K (KLloopOf d L σ (Fin.snocEquiv (fun _ : Fin (k + 2) => Zd d L) (x, a'))) =
      c * (K (KLloopOf d L (Fin.cons true (fun j : Fin k => σ j.castSucc.succ) : Fin (k + 1) → Bool) a') -
        K (KLloopOf d L (Fin.cons false (fun j : Fin k => σ j.castSucc.succ) : Fin (k + 1) → Bool) a')) := by
    intro a'
    have h := hward (σ 0) (List.ofFn (fun j : Fin k => σ j.castSucc.succ)) (List.ofFn a') (by simp)
    simp only [KLloopOf, hcons]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, hσl, hsnoc]
    exact h
  simp only [hpt, ← Finset.mul_sum, Finset.sum_sub_distrib]

open Fin.NatCast in
/-- A charge vector is constant, or some rotation of it has `σ_last = -σ_0` (a cyclically adjacent pair of distinct
charges exists; rotate it to the end). -/
private theorem KSumZeroA_const_or_rot {k : ℕ} (σ : Fin (k + 1) → Bool) :
    (∀ j, σ j = σ 0) ∨ ∃ r : ℕ, σ (Fin.last k + (r : Fin (k + 1))) = !σ (0 + (r : Fin (k + 1))) := by
  by_cases hc : ∀ j, σ j = σ 0
  · exact Or.inl hc
  · right
    have hex : ∃ i : Fin (k + 1), σ i ≠ σ (i + 1) := by
      by_contra hne
      push Not at hne
      apply hc
      have hcast : ∀ p : ℕ, σ (p : Fin (k + 1)) = σ 0 := by
        intro p
        induction p with
        | zero => simp
        | succ p ih => rw [Nat.cast_succ, ← hne (p : Fin (k + 1))]; exact ih
      intro j
      have := hcast j.val
      rwa [Fin.cast_val_eq_self] at this
    obtain ⟨i, hi⟩ := hex
    refine ⟨i.val + 1, ?_⟩
    have e1 : ((i.val + 1 : ℕ) : Fin (k + 1)) = i + 1 := by
      rw [Nat.cast_succ, Fin.cast_val_eq_self]
    have e2 : Fin.last k + (i + 1) = i := by
      rw [← add_assoc, add_comm (Fin.last k) i, add_assoc, Fin.last_add_one, add_zero]
    rw [e1, e2, zero_add]
    cases h1 : σ i <;> cases h2 : σ (i + 1) <;> simp_all

/-- `Σ_a e^{-c max_{i,j} |a_i - a_j|} ≤ L^d expC(d-2, c/n)^{n-1}` over all `a : Fin n → Z_L^d` (fibres of `a ↦ a_0`,
`KLMolecule_sum_exp_maxDist`). -/
private theorem KSumZeroA_sum_exp {d n : ℕ} [NeZero n] (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c) :
    ∑ a : Fin n → Zd d L, Real.exp (-(c * (KLmaxDist d L a : ℝ))) ≤
      (L : ℝ) ^ d * (expC (d - 2) (c / n)) ^ (n - 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  rw [← Finset.sum_fiberwise Finset.univ (fun a : Fin n → Zd (k + 2) L => a 0)]
  calc _ ≤ ∑ x : Zd (k + 2) L, (expC k (c / n)) ^ (n - 1) :=
        Finset.sum_le_sum fun x _ => KLMolecule_sum_exp_maxDist k hc x
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        simp

/-- **The pure bound for sums, `n = 2`**: `|Σ_{a_0,a_1} 𝒦^{(2)}_{(s,s),a}| ≤ Σ_{a_0,a_1} |𝒦^{(2)}_{(s,s),a}| ≤ W^{-d} L^d B expC(d-2, r)`:
`(Kn2sol)` (`baKsol_two`), the entry bound `|Θ^{(s,s)}_{xz}| ≤ B e^{-r|x-z|}` (`baPure_edge`), the row sums `Σ_y |M^{(s,s)}_{zy}| = Σ_y K_{zy} = 1`
and `Σ_z e^{-r|x-z|} ≤ expC(d-2, r)`. -/
private theorem KSumZeroA_pure_two {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (W : ℕ) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (σ₀ : Bool) :
    ‖∑ a : Fin 2 → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
        (KLloopOf d L (fun _ => σ₀) a)‖ ≤
      (L : ℝ) ^ d * (baPureB d Λ κ * expC (d - 2) (baPureRate d Λ κ)) * ((W : ℝ) ^ d)⁻¹ := by
  have hd0 : 0 < d := by omega
  have hB1 := baPureB_one_le d Λ κ
  have hr0 := baPureRate_pos hd0 hΛ hκ
  obtain ⟨-, hΘ, -⟩ := baPure_edge hd hΛ hκ hL hg hgΛ hr ht.1 ht.2.le
  have hW0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hS : ∀ x : Zd d L, ∑ z, ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ x z‖ ≤
      baPureB d Λ κ * expC (d - 2) (baPureRate d Λ κ) := fun x => by
    calc ∑ z, ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ x z‖
        ≤ ∑ z, baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - z) : ℝ))) :=
          Finset.sum_le_sum fun z _ => hΘ σ₀ x z
      _ = baPureB d Λ κ * ∑ z, Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - z) : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (BAsum_exp_decay_le d L (by omega) _ hr0 x) (by linarith)
  have hK2 : ∀ a : Fin 2 → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
      (KLloopOf d L (fun _ => σ₀) a) = ((W : ℂ) ^ d)⁻¹ *
        ∑ z, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ (a 0) z *
          BAMss d L (BAMB d L g (E : ℂ) m) σ₀ σ₀ z (a 1) := fun a => by
    rw [baKsol_two d hκ hg hL W hr ht (fun _ => σ₀) a, Matrix.mul_apply]
    rfl
  have e := Fintype.sum_equiv (piFinTwoEquiv (fun _ : Fin 2 => Zd d L)).symm
    (fun p : Zd d L × Zd d L => BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
      (KLloopOf d L (fun _ => σ₀) ((piFinTwoEquiv (fun _ : Fin 2 => Zd d L)).symm p)))
    (fun a => BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L (fun _ => σ₀) a))
    (fun _ => rfl)
  rw [← e, Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_apply, hK2]
  have h0 : ∀ (x y : Zd d L), (Fin.cons x (Fin.cons y finZeroElim) : Fin 2 → Zd d L) 0 = x := fun x y => rfl
  have h1 : ∀ (x y : Zd d L), (Fin.cons x (Fin.cons y finZeroElim) : Fin 2 → Zd d L) 1 = y := fun x y => rfl
  simp only [h0, h1]
  have hν : ‖((W : ℂ) ^ d)⁻¹‖ = ((W : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  have hrow : ∀ z : Zd d L, ∑ y, BAK d L g E m z y = 1 := fun z => BAK_row_sum d L g E m hr.1 z
  calc ‖∑ x : Zd d L, ∑ y : Zd d L, ((W : ℂ) ^ d)⁻¹ * ∑ z, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ x z *
          BAMss d L (BAMB d L g (E : ℂ) m) σ₀ σ₀ z y‖
      ≤ ∑ x : Zd d L, ∑ y : Zd d L, ‖((W : ℂ) ^ d)⁻¹ * ∑ z, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ x z *
          BAMss d L (BAMB d L g (E : ℂ) m) σ₀ σ₀ z y‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x : Zd d L, ∑ y : Zd d L, ((W : ℝ) ^ d)⁻¹ * ∑ z, ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ x z‖ *
          BAK d L g E m z y := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul, hν]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) hW0
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [norm_mul, BAMss_norm_eq_BAK]
    _ = ((W : ℝ) ^ d)⁻¹ * ∑ x : Zd d L, ∑ z, ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ x z‖ := by
        simp only [← Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.mul_sum, hrow, mul_one]
    _ ≤ ((W : ℝ) ^ d)⁻¹ * ∑ x : Zd d L, baPureB d Λ κ * expC (d - 2) (baPureRate d Λ κ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hS x) hW0
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast
        ring

/-- **The pure bound for sums, `n ≥ 3`**: `lem_pureloop` (`baPure_loop`) and `Σ_a e^{-c max_{i,j} |a_i - a_j|} ≤ L^d S^{n-1}`. -/
private theorem KSumZeroA_pure_three {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ)
    (hκ : 0 < κ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₀ : Bool,
        ‖∑ a : Fin n → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
            (KLloopOf d L (fun _ => σ₀) a)‖ ≤ B * (L : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹) ^ (n - 1) := by
  obtain ⟨C, hC, c, hc, hbd⟩ := baPure_loop (d := d) (n := n) hd hn hΛ hκ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcn : 0 < c / n := by positivity
  have hS0 : 0 < expC (d - 2) (c / n) := by unfold expC; positivity
  refine ⟨C * (expC (d - 2) (c / n)) ^ (n - 1), by positivity, fun L _ hL W g hg hgΛ E m hr t ht0 ht1 σ₀ => ?_⟩
  have hν : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  calc ‖∑ a : Fin n → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
          (KLloopOf d L (fun _ => σ₀) a)‖
      ≤ ∑ a : Fin n → Zd d L, ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
          (KLloopOf d L (fun _ => σ₀) a)‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin n → Zd d L, C * (((W : ℝ) ^ d)⁻¹) ^ (n - 1) * Real.exp (-(c * (KLmaxDist d L a : ℝ))) :=
        Finset.sum_le_sum fun a _ => hbd L hL W g hg hgΛ E m hr t ht0 ht1 σ₀ a
    _ = C * (((W : ℝ) ^ d)⁻¹) ^ (n - 1) * ∑ a : Fin n → Zd d L, Real.exp (-(c * (KLmaxDist d L a : ℝ))) := by
        rw [← Finset.mul_sum]
    _ ≤ C * (((W : ℝ) ^ d)⁻¹) ^ (n - 1) * ((L : ℝ) ^ d * (expC (d - 2) (c / n)) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left (KSumZeroA_sum_exp hd hc) (by positivity)
    _ = _ := by ring

/-- **The pure bound for sums, every `n ≥ 2`** (`n = k + 2`): `|Σ_a 𝒦^{(n)}_{(σ₀,…,σ₀),a}| ≤ B L^d (W^{-d})^{n-1}`. -/
private theorem KSumZeroA_pure_aux {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₀ : Bool,
        ‖∑ a : Fin (k + 2) → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
            (KLloopOf d L (fun _ => σ₀) a)‖ ≤ B * (L : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹) ^ (k + 1) := by
  rcases k with _ | k
  · have hd0 : 0 < d := by omega
    have hB1 := baPureB_one_le d Λ κ
    have hr0 := baPureRate_pos hd0 hΛ hκ
    have hS : 0 < expC (d - 2) (baPureRate d Λ κ) := by unfold expC; positivity
    refine ⟨baPureB d Λ κ * expC (d - 2) (baPureRate d Λ κ), by positivity, fun L _ hL W hW g hg hgΛ E m hr t ht0 ht1 σ₀ => ?_⟩
    have := KSumZeroA_pure_two hd hΛ hκ hL W hg hgΛ hr ⟨ht0, ht1⟩ σ₀
    simpa [mul_comm, mul_left_comm] using this
  · obtain ⟨B, hB, hBd⟩ := KSumZeroA_pure_three (d := d) (n := k + 1 + 2) hd (by omega) hΛ hκ
    exact ⟨B, hB, fun L _ hL W _ g hg hgΛ E m hr t ht0 ht1 σ₀ => hBd L hL W g hg hgΛ E m hr t ht0 ht1 σ₀⟩

open Fin.NatCast in
/-- **The Ward bound for sums, by induction on the length** (`n = k + 1`): `B_{k+1} = max (B_k, B_pure)`.  A constant charge
vector is the pure bound; otherwise a rotation brings a pair of distinct adjacent charges to `(σ_last, σ_0)`, and
`baK_ward` (`KSumZeroA_ward_fin`) gives `(2 i W^d η)⁻¹ (T_k(+, μ) - T_k(-, μ))`, no growth of the constant. -/
private theorem KSumZeroA_ward_aux {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∀ k : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin (k + 1) → Bool,
        ‖∑ a : Fin (k + 1) → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
            (KLloopOf d L σ a)‖ ≤ B * (L : ℝ) ^ d * (((W : ℝ) ^ d * ((1 - t) * m.im))⁻¹) ^ k := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, one_pos, fun L _ hL W hW g hg hgΛ E m hr t ht0 ht1 σ => ?_⟩
    have hm : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
    have hs : ‖PropSpin m (σ 0)‖ ≤ 1 := by
      cases σ 0 <;> simpa [PropSpin] using hm
    have h1 : ∀ a : Fin 1 → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
        (KLloopOf d L σ a) = PropSpin m (σ 0) := fun a => baKsol_one d hκ hg hL W hr ⟨ht0, ht1⟩ σ a
    have hcard : Fintype.card (Fin 1 → Zd d L) = L ^ d := by
      rw [Fintype.card_fun, Fintype.card_fin, pow_one, card_Zd]
    have hsum : ∑ a : Fin 1 → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
        (KLloopOf d L σ a) = ((L : ℂ) ^ d) * PropSpin m (σ 0) := by
      simp only [h1, Finset.sum_const, Finset.card_univ]
      rw [hcard, nsmul_eq_mul]
      push_cast
      rfl
    rw [hsum, norm_mul, norm_pow, Complex.norm_natCast]
    calc (L : ℝ) ^ d * ‖PropSpin m (σ 0)‖ ≤ (L : ℝ) ^ d * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by simp
  | succ k ih =>
    obtain ⟨B, hB, hBd⟩ := ih
    obtain ⟨Bp, hBp, hBpd⟩ := KSumZeroA_pure_aux hd hΛ hκ k
    refine ⟨max B Bp, lt_max_of_lt_left hB, fun L _ hL W hW g hg hgΛ E m hr t ht0 ht1 σ => ?_⟩
    have ht : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht0, ht1⟩
    have hm : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
    have hmim : 0 < m.im := hr.1.1
    have hmle : m.im ≤ 1 := (Complex.im_le_norm m).trans hm
    set η : ℝ := (1 - t) * m.im with hη
    have hη0 : 0 < η := mul_pos (by linarith) hmim
    have hη1 : η ≤ 1 := by
      calc η = (1 - t) * m.im := rfl
        _ ≤ 1 * 1 := mul_le_mul (by linarith) hmle hmim.le zero_le_one
        _ = 1 := one_mul 1
    have hWd : (1 : ℝ) ≤ (W : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW)
    have hWd0 : 0 < (W : ℝ) ^ d := by linarith
    have hν : ((W : ℝ) ^ d)⁻¹ ≤ ((W : ℝ) ^ d * η)⁻¹ :=
      inv_anti₀ (mul_pos hWd0 hη0) (by nlinarith)
    have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
    have hMax0 : 0 ≤ max B Bp * (L : ℝ) ^ d := mul_nonneg (hB.le.trans (le_max_left _ _)) hL0
    rcases KSumZeroA_const_or_rot σ with hconst | ⟨r, hrot'⟩
    · obtain ⟨σ₀, rfl⟩ : ∃ σ₀, σ = fun _ => σ₀ := ⟨σ 0, funext hconst⟩
      have hp := hBpd L hL W hW g hg hgΛ E m hr t ht0 ht1 σ₀
      refine hp.trans ?_
      have h1 : (((W : ℝ) ^ d)⁻¹) ^ (k + 1) ≤ (((W : ℝ) ^ d * η)⁻¹) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) hν _
      calc Bp * (L : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹) ^ (k + 1)
          ≤ max B Bp * (L : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹) ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hL0) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hMax0
    · set σr : Fin (k + 2) → Bool := fun j => σ (j + (r : Fin (k + 2))) with hσr
      have hσlast : σr (Fin.last _) = !σr 0 := hrot'
      have hK := BAKsol_isKLoopS (baKsolve d) hg hκ hL hg le_rfl hr (W := W)
      have hrot : ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
          BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨s :: σ, b :: a⟩ =
            BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨σ ++ [s], a ++ [b]⟩ :=
        fun s b σ a h => BAKsol_rotate (baKsolve d) hg hκ hL hg le_rfl hr t ht s b σ a h
      have hn2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
          BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
            (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 *
              BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂ := by
        intro t ht σ a₁ a₂
        have h := baKsol_two d hκ hg hL W hr ht ![σ.1, σ.2] ![a₁, a₂]
        simpa [KLloopOf, List.ofFn_succ] using h
      have hward := baK_ward d L W g κ E m hr hL hW hK hn2 t ht
      rw [KSumZeroA_sum_rot hrot σ r, KSumZeroA_ward_fin hward σr hσlast, norm_mul]
      have hc : ‖(2 * Complex.I * (W : ℂ) ^ d * (((1 - t) * (PropSpin m true).im : ℝ) : ℂ))⁻¹‖ =
          (2 * ((W : ℝ) ^ d * η))⁻¹ := by
        have e : (PropSpin m true).im = m.im := by simp [PropSpin]
        rw [e, norm_inv, norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_pow, Complex.norm_natCast,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]
        simp
        ring
      rw [hc]
      set τ : Fin k → Bool := fun j => σr j.castSucc.succ with hτ
      have hT1 := hBd L hL W hW g hg hgΛ E m hr t ht0 ht1 (Fin.cons true τ : Fin (k + 1) → Bool)
      have hT2 := hBd L hL W hW g hg hgΛ E m hr t ht0 ht1 (Fin.cons false τ : Fin (k + 1) → Bool)
      set X : ℝ := B * (L : ℝ) ^ d * (((W : ℝ) ^ d * η)⁻¹) ^ k with hX
      have hdiff := norm_sub_le (∑ a : Fin (k + 1) → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))
          (PropSpin m) t (KLloopOf d L (Fin.cons true τ : Fin (k + 1) → Bool) a))
        (∑ a : Fin (k + 1) → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))
          (PropSpin m) t (KLloopOf d L (Fin.cons false τ : Fin (k + 1) → Bool) a))
      have hcpos : 0 ≤ (2 * ((W : ℝ) ^ d * η))⁻¹ := by positivity
      have hX0 : 0 ≤ X := by positivity
      calc (2 * ((W : ℝ) ^ d * η))⁻¹ * ‖_ - _‖ ≤ (2 * ((W : ℝ) ^ d * η))⁻¹ * (X + X) :=
            mul_le_mul_of_nonneg_left (hdiff.trans (add_le_add hT1 hT2)) hcpos
        _ = B * (L : ℝ) ^ d * (((W : ℝ) ^ d * η)⁻¹) ^ (k + 1) := by
            rw [hX, pow_succ']
            field_simp
            norm_num
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0) (by positivity)

end Ward

/-- **T1: the Ward bound for sums of `𝒦`** (`(WI_calK)`, `baK_ward`, summed over the labels): for every charge vector `σ`
and `n ≥ 1`, `|Σ_{a ∈ Z_L^{dn}} 𝒦^{(n)}_{t,σ,a}| ≤ B L^d (W^d η_t)^{-(n-1)}`, `η_t = (1-t) Im m`.  `B` depends on `(d, n, Λ, κ)`
only, uniformly in `L ≥ 3`, `W ≥ 1`, `g ∈ (0, Λ]`, the real-axis data and `t ∈ [0, 1)` (supervisor 1155 C1). -/
theorem baK_sumAll_le {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 1 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool,
        ‖∑ a : Fin n → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t
            (KLloopOf d L σ a)‖ ≤ B * (L : ℝ) ^ d * (((W : ℝ) ^ d * ((1 - t) * m.im))⁻¹) ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact KSumZeroA_ward_aux hd hΛ hκ k

/-! ## 4. The cut recursion (A4) -/

section Split

variable {n : ℕ} {J : Fin n × Fin n}

/-- `(BAinVinv J k)_val = i + k` on the arc. -/
private theorem KSumZeroA_inVinv_val [NeZero n] (k : Fin (KLwIn J + 1)) (hk : k.val < KLwIn J) :
    (BAinVinv J k).val = J.1.val + k.val := by
  have := J.2.isLt
  simp only [BAinVinv, KLwIn] at *
  omega

private theorem KSumZeroA_inV_inVinv [NeZero n] (k : Fin (KLwIn J + 1)) (hk : k.val < KLwIn J) :
    KLinV J (BAinVinv J k) = k := by
  refine Fin.ext ?_
  have := J.2.isLt
  simp only [BAinVinv, KLinV, KLwIn] at *
  omega

private theorem KSumZeroA_outV_outVinv [NeZero n] (hJ : J.1.val + 2 ≤ J.2.val) (k : Fin (n - KLwIn J + 1)) :
    KLoutV J (BAoutVinv J k) = k := by
  refine Fin.ext ?_
  have := J.2.isLt
  have := k.isLt
  simp only [BAoutVinv, KLoutV, KLcol, KLunCol, KLwIn] at *
  split_ifs <;> omega

private theorem KSumZeroA_glueV_val (hJ : J.1.val + 2 ≤ J.2.val) : (KLglueV J).val = J.1.val := by
  have := J.2.isLt
  simp only [KLglueV, KLwIn]
  omega

/-- The glued labelling: `α` on the arc `[i, j)`, `β` on the rest. -/
private def KSumZeroA_glue {G : Type*} (J : Fin n × Fin n) (α : Fin (KLwIn J + 1) → G)
    (β : Fin (n - KLwIn J + 1) → G) : Fin n → G :=
  fun v => if J.1.val ≤ v.val ∧ v.val < J.2.val then α (KLinV J v) else β (KLoutV J v)

private theorem KSumZeroA_deltaIn_glue [NeZero n] {G : Type*} (hJ : J.1.val + 2 ≤ J.2.val)
    (α : Fin (KLwIn J + 1) → G) (β : Fin (n - KLwIn J + 1) → G) (u : G) (hu : α (Fin.last _) = u) :
    BAdeltaIn J (KSumZeroA_glue J α β) u = α := by
  funext k
  by_cases hk : k = Fin.last _
  · subst hk
    simp [BAdeltaIn, hu]
  · have hk' : k.val < KLwIn J := by
      have h1 : k.val ≠ KLwIn J := fun h => hk (Fin.ext (by simpa using h))
      have := k.isLt
      omega
    simp only [BAdeltaIn, Function.update_of_ne hk, KSumZeroA_glue]
    have h3 := KSumZeroA_inV_inVinv (J := J) k hk'
    have h2 := KSumZeroA_inVinv_val (J := J) k hk'
    have h4 : J.1.val ≤ (BAinVinv J k).val ∧ (BAinVinv J k).val < J.2.val := by
      simp only [KLwIn] at hk'
      omega
    simp only [h4, and_self, ↓reduceIte, h3]

private theorem KSumZeroA_deltaOut_glue [NeZero n] {G : Type*} (hJ : J.1.val + 2 ≤ J.2.val)
    (α : Fin (KLwIn J + 1) → G) (β : Fin (n - KLwIn J + 1) → G) (w : G) (hw : β (KLglueV J) = w) :
    BAdeltaOut J (KSumZeroA_glue J α β) w = β := by
  funext k
  by_cases hk : k = KLglueV J
  · subst hk
    simp [BAdeltaOut, hw]
  · simp only [BAdeltaOut, Function.update_of_ne hk, KSumZeroA_glue]
    have hnot : ¬(J.1.val ≤ (BAoutVinv J k).val ∧ (BAoutVinv J k).val < J.2.val) := by
      have h1 : k.val ≠ J.1.val := fun h => hk (Fin.ext (by rw [KSumZeroA_glueV_val hJ]; exact h))
      have := J.2.isLt
      have := k.isLt
      simp only [BAoutVinv, KLunCol, KLwIn] at *
      split_ifs <;> omega
    simp only [hnot, ↓reduceIte, KSumZeroA_outV_outVinv hJ k]

private theorem KSumZeroA_glue_delta [NeZero n] {G : Type*} (hJ : J.1.val + 2 ≤ J.2.val) (δ : Fin n → G) (u w : G) :
    KSumZeroA_glue J (BAdeltaIn J δ u) (BAdeltaOut J δ w) = δ := by
  funext v
  have hjn := J.2.isLt
  have hvn := v.isLt
  by_cases hv : J.1.val ≤ v.val ∧ v.val < J.2.val
  · have hin : KLInArc J v := by
      simp only [KLInArc, Fin.le_def, Fin.lt_def]
      exact hv
    have hval := KLinV_val hin
    have hlt : (KLinV J v) ≠ Fin.last _ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, KLwIn] at this
      omega
    simp only [KSumZeroA_glue, hv, and_self, ↓reduceIte, BAdeltaIn, Function.update_of_ne hlt]
    congr 1
    refine Fin.ext ?_
    simp only [BAinVinv, hval]
    omega
  · have hne : KLoutV J v ≠ KLglueV J := by
      intro h
      have h1 := congrArg Fin.val h
      rw [KSumZeroA_glueV_val hJ] at h1
      simp only [KLoutV, KLcol, KLwIn] at h1
      split_ifs at h1 <;> omega
    simp only [KSumZeroA_glue, hv, ↓reduceIte, BAdeltaOut, Function.update_of_ne hne]
    congr 1
    refine Fin.ext ?_
    simp only [BAoutVinv, KLoutV, KLcol, KLunCol, KLwIn]
    split_ifs <;> omega

/-- **The label-splitting bijection**: the labels `δ ∈ Z^n` are the labels of the arc `[i, j)` together with those of the rest
(`BAdeltaIn J δ u`, `BAdeltaOut J δ w`), so `Σ_δ F(δ_in, u) H(δ_out, w) = (Σ_{α_last = u} F α)(Σ_{β_glue = w} H β)`. -/
private theorem KSumZeroA_split_sum [NeZero n] {G : Type*} [Fintype G] [DecidableEq G] (hJ : J.1.val + 2 ≤ J.2.val)
    (F : (Fin (KLwIn J + 1) → G) → ℂ) (H : (Fin (n - KLwIn J + 1) → G) → ℂ) (u w : G) :
    ∑ δ : Fin n → G, F (BAdeltaIn J δ u) * H (BAdeltaOut J δ w) =
      (∑ α ∈ Finset.univ.filter (fun α : Fin (KLwIn J + 1) → G => α (Fin.last _) = u), F α) *
      (∑ β ∈ Finset.univ.filter (fun β : Fin (n - KLwIn J + 1) → G => β (KLglueV J) = w), H β) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij' (fun δ _ => (BAdeltaIn J δ u, BAdeltaOut J δ w)) (fun p _ => KSumZeroA_glue J p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro δ _
    simp [BAdeltaIn, BAdeltaOut]
  · intro p _
    exact Finset.mem_univ _
  · intro δ _
    exact KSumZeroA_glue_delta hJ δ u w
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Prod.ext (KSumZeroA_deltaIn_glue hJ p.1 p.2 u hp.1) (KSumZeroA_deltaOut_glue hJ p.1 p.2 w hp.2)
  · intro δ _
    rfl

end Split

section Cut

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **The cut identity**: `(1-t) L^d 𝒮(σ,π) = t 𝒮(σ_in,∅) 𝒮(σ_out,π')`, `𝒮(σ,π) = Σ_δ Σ^{(π)}(δ)`, at an innermost long edge
`J ∈ π`.  `baSigmaPi_cut` writes `Σ^{(π)}` as `Σ_{u,w} Σ_in(δ_in, u) tΘ(u,w) Σ_out(δ_out, w)`; the labels split
(`KSumZeroA_split_sum`); each factor is a slice sum, `𝒮/L^d` (`baSigmaPi_slice`); `Σ_{u,w} Θ^{(σ_i,σ_j)}(u,w) = L^d (1-t)⁻¹`. -/
private theorem KSumZeroA_cut_sum (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π)
    (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J)
    (hrow : ∀ u : Zd d L, ∑ w, BAThetaOf M t (σ J.1) (σ J.2) u w = (1 - (t : ℂ))⁻¹)
    (ht : (1 - (t : ℂ)) ≠ 0) :
    (L : ℂ) ^ d * (1 - (t : ℂ)) * ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ π δ =
      (t : ℂ) * (∑ δ : Fin (KLwIn J + 1) → Zd d L, BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ δ) *
        ∑ δ : Fin (n - KLwIn J + 1) → Zd d L,
          BASigmaPi d L (n - KLwIn J + 1) M t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) δ := by
  classical
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJd : IsDiag n J.1 J.2 := (KLisTSP_of_mem_TSP hF₀).1 J hJF₀
  have hJ : J.1.val + 2 ≤ J.2.val := by
    obtain ⟨h1, h2, -⟩ := hJd
    simp only [Fin.lt_def] at h1
    omega
  set A : (Fin (KLwIn J + 1) → Zd d L) → ℂ := fun α =>
    BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ α with hA
  set B : (Fin (n - KLwIn J + 1) → Zd d L) → ℂ := fun β =>
    BASigmaPi d L (n - KLwIn J + 1) M t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) β with hB
  set θ : Zd d L → Zd d L → ℂ := fun u w => (t : ℂ) * BAThetaOf M t (σ J.1) (σ J.2) u w with hθ
  set a : Zd d L → ℂ := fun u => ∑ α ∈ Finset.univ.filter (fun α : Fin (KLwIn J + 1) → Zd d L => α (Fin.last _) = u),
    A α with ha
  set b : Zd d L → ℂ := fun w => ∑ β ∈ Finset.univ.filter (fun β : Fin (n - KLwIn J + 1) → Zd d L => β (KLglueV J) = w),
    B β with hb
  have h1 : ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ π δ = ∑ u, ∑ w, θ u w * (a u * b w) := by
    simp only [baSigmaPi_cut hn M t σ hF₀ hπ hJπ hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← KSumZeroA_split_sum hJ A B u w, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    ring
  have hAs : ∀ u, (L : ℂ) ^ d * a u = ∑ δ, A δ := fun u =>
    baSigmaPi_slice M hshift t (sigmaIn σ J) ∅ (Fin.last _) u
  have hBs : ∀ w, (L : ℂ) ^ d * b w = ∑ δ, B δ := fun w =>
    baSigmaPi_slice M hshift t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) (KLglueV J) w
  have hLd : (L : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have hθs : ∀ u, ∑ w, θ u w = (t : ℂ) * (1 - (t : ℂ))⁻¹ := fun u => by
    simp only [hθ, ← Finset.mul_sum, hrow u]
  apply mul_left_cancel₀ hLd
  calc (L : ℂ) ^ d * ((L : ℂ) ^ d * (1 - (t : ℂ)) * ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ π δ)
      = (1 - (t : ℂ)) * ∑ u, ∑ w, θ u w * (((L : ℂ) ^ d * a u) * ((L : ℂ) ^ d * b w)) := by
        rw [h1]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
        ring
    _ = (1 - (t : ℂ)) * ∑ u, ∑ w, θ u w * ((∑ δ, A δ) * (∑ δ, B δ)) := by
        simp only [hAs, hBs]
    _ = (L : ℂ) ^ d * ((t : ℂ) * (∑ δ, A δ) * ∑ δ, B δ) := by
        simp only [← Finset.sum_mul]
        simp only [hθs, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast
        field_simp

end Cut

/-! ## 5. The polygons of a long chord of an alternating `σ` -/

section Alt

variable {n : ℕ}

private theorem KSumZeroA_alt_step (σ : Fin (n + 1) → Bool) (halt : ∀ j, σ j ≠ σ (j + 1)) (p : ℕ) (hp : p < n) :
    σ ⟨p, by omega⟩ ≠ σ ⟨p + 1, by omega⟩ := by
  have h := halt ⟨p, by omega⟩
  have hlt : (⟨p, by omega⟩ : Fin (n + 1)) < Fin.last n := by
    simp only [Fin.lt_def, Fin.val_last]
    exact hp
  have e : (⟨p, by omega⟩ : Fin (n + 1)) + 1 = ⟨p + 1, by omega⟩ :=
    Fin.ext (by rw [Fin.val_add_one_of_lt hlt])
  rwa [e] at h

private theorem KSumZeroA_alt_wrap (σ : Fin (n + 1) → Bool) (halt : ∀ j, σ j ≠ σ (j + 1)) :
    σ (Fin.last n) ≠ σ 0 := by
  have h := halt (Fin.last n)
  rwa [Fin.last_add_one] at h

private theorem KSumZeroA_sigmaIn_eq (σ : Fin (n + 1) → Bool) (J : Fin (n + 1) × Fin (n + 1)) (k : Fin (KLwIn J + 1))
    (p : Fin (n + 1)) (hp : p.val = J.1.val + k.val) : sigmaIn σ J k = σ p := by
  have := J.2.isLt
  have := k.isLt
  simp only [sigmaIn]
  congr 1
  refine Fin.ext ?_
  simp only [KLwIn] at *
  omega

private theorem KSumZeroA_sigmaOut_eq_le (σ : Fin (n + 1) → Bool) (J : Fin (n + 1) × Fin (n + 1))
    (k : Fin (n + 1 - KLwIn J + 1)) (hk : k.val ≤ J.1.val) (p : Fin (n + 1)) (hp : p.val = k.val) :
    sigmaOut σ J k = σ p := by
  have := J.2.isLt
  have := k.isLt
  simp only [sigmaOut]
  congr 1
  refine Fin.ext ?_
  simp only [KLunCol, hk, ↓reduceIte]
  simp only [KLwIn] at *
  omega

private theorem KSumZeroA_sigmaOut_eq_gt (σ : Fin (n + 1) → Bool) (J : Fin (n + 1) × Fin (n + 1))
    (hJ : J.1.val + 2 ≤ J.2.val) (k : Fin (n + 1 - KLwIn J + 1)) (hk : J.1.val < k.val) (p : Fin (n + 1))
    (hp : p.val + 1 + J.1.val = k.val + J.2.val) : sigmaOut σ J k = σ p := by
  have := J.2.isLt
  have := k.isLt
  simp only [sigmaOut]
  congr 1
  refine Fin.ext ?_
  simp only [KLunCol, not_le.2 hk, ↓reduceIte]
  simp only [KLwIn] at *
  omega

/-- The inner polygon of a long chord of an alternating `σ` is alternating. -/
private theorem KSumZeroA_sigmaIn_alt (σ : Fin (n + 1) → Bool) (halt : ∀ j, σ j ≠ σ (j + 1))
    {J : Fin (n + 1) × Fin (n + 1)} (hJ : J.1.val + 2 ≤ J.2.val) (hlong : σ J.1 ≠ σ J.2) :
    ∀ k : Fin (KLwIn J + 1), sigmaIn σ J k ≠ sigmaIn σ J (k + 1) := by
  intro k
  have hj := J.2.isLt
  by_cases hk : k = Fin.last _
  · subst hk
    rw [Fin.last_add_one, KSumZeroA_sigmaIn_eq σ J _ J.2 (by simp [KLwIn]; omega),
      KSumZeroA_sigmaIn_eq σ J 0 J.1 (by simp)]
    exact hlong.symm
  · have hk' : k.val < KLwIn J := by
      have h1 : k.val ≠ KLwIn J := fun h => hk (Fin.ext (by simpa using h))
      have := k.isLt
      omega
    have hlt : k < Fin.last _ := by
      simp only [Fin.lt_def, Fin.val_last]
      exact hk'
    have hv : (k + 1).val = k.val + 1 := Fin.val_add_one_of_lt hlt
    simp only [KLwIn] at hk'
    rw [KSumZeroA_sigmaIn_eq σ J k ⟨J.1.val + k.val, by omega⟩ rfl,
      KSumZeroA_sigmaIn_eq σ J (k + 1) ⟨J.1.val + k.val + 1, by omega⟩ (by simp only [hv]; omega)]
    exact KSumZeroA_alt_step σ halt (J.1.val + k.val) (by omega)

/-- The outer polygon of a long chord of an alternating `σ` is alternating. -/
private theorem KSumZeroA_sigmaOut_alt (σ : Fin (n + 1) → Bool) (halt : ∀ j, σ j ≠ σ (j + 1))
    {J : Fin (n + 1) × Fin (n + 1)} (hJ : J.1.val + 2 ≤ J.2.val) (hlong : σ J.1 ≠ σ J.2) :
    ∀ k : Fin (n + 1 - KLwIn J + 1), sigmaOut σ J k ≠ sigmaOut σ J (k + 1) := by
  intro k
  have hj := J.2.isLt
  by_cases hk : k = Fin.last _
  · subst hk
    rw [Fin.last_add_one, KSumZeroA_sigmaOut_eq_gt σ J hJ _ (by simp only [Fin.val_last, KLwIn]; omega) (Fin.last n)
        (by simp only [Fin.val_last, KLwIn]; omega),
      KSumZeroA_sigmaOut_eq_le σ J 0 (by simp) 0 (by simp)]
    exact KSumZeroA_alt_wrap σ halt
  · have hk' : k.val < n + 1 - KLwIn J := by
      have h1 : k.val ≠ n + 1 - KLwIn J := fun h => hk (Fin.ext (by simpa using h))
      have := k.isLt
      omega
    have hlt : k < Fin.last _ := by
      simp only [Fin.lt_def, Fin.val_last]
      exact hk'
    have hv : (k + 1).val = k.val + 1 := Fin.val_add_one_of_lt hlt
    simp only [KLwIn] at hk'
    by_cases h1 : k.val + 1 ≤ J.1.val
    · rw [KSumZeroA_sigmaOut_eq_le σ J k (by omega) ⟨k.val, by omega⟩ rfl,
        KSumZeroA_sigmaOut_eq_le σ J (k + 1) (by omega) ⟨k.val + 1, by omega⟩ (by simp only [hv])]
      exact KSumZeroA_alt_step σ halt k.val (by omega)
    · by_cases h2 : k.val = J.1.val
      · rw [KSumZeroA_sigmaOut_eq_le σ J k (by omega) J.1 h2.symm,
          KSumZeroA_sigmaOut_eq_gt σ J hJ (k + 1) (by omega) J.2 (by omega)]
        exact hlong
      · rw [KSumZeroA_sigmaOut_eq_gt σ J hJ k (by omega) ⟨k.val + (J.2.val - J.1.val) - 1, by omega⟩
          (by simp only; omega),
          KSumZeroA_sigmaOut_eq_gt σ J hJ (k + 1) (by omega) ⟨k.val + (J.2.val - J.1.val) - 1 + 1, by omega⟩
          (by simp only [hv]; omega)]
        exact KSumZeroA_alt_step σ halt (k.val + (J.2.val - J.1.val) - 1) (by omega)

end Alt

/-! ## 6. The induction (A5) -/

section Induction

variable {d L : ℕ} [NeZero L]

/-- `‖1 - t‖ = 1 - t` in `ℂ`, for `t < 1`. -/
private theorem KSumZeroA_norm_one_sub {t : ℝ} (ht : t < 1) : ‖(1 - (t : ℂ))‖ = 1 - t := by
  have : (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]

/-- **A layer `π ≠ ∅`** (the cut recursion and the induction hypothesis): if every `𝒮(σ', π')` of a shorter length
`3 ≤ k ≤ n` (alternating `σ'`) is `≤ C L^d (1-t)`, then `|𝒮(σ, π)| ≤ C² L^d (1-t)` for `σ` alternating of length `n + 1`,
`π ≠ ∅`.  If no tree has the long edges `π`, `Σ^{(π)} = 0`; otherwise an innermost `J ∈ π` gives the cut identity
`(1-t) L^d 𝒮(σ,π) = t 𝒮(σ_in,∅) 𝒮(σ_out,π')` with `3 ≤ n_in, n_out ≤ n`. -/
private theorem KSumZeroA_offdiag (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hrow : ∀ s s' : Bool, s ≠ s' → ∀ u : Zd d L, ∑ w, BAThetaOf M t s s' u w = (1 - (t : ℂ))⁻¹) {C : ℝ}
    (hC : 0 ≤ C) {n : ℕ}
    (IH : ∀ (k : ℕ) [NeZero k], 3 ≤ k → k ≤ n → ∀ σ' : Fin k → Bool, (∀ j, σ' j ≠ σ' (j + 1)) →
      ∀ π' : Finset (Fin k × Fin k),
        ‖∑ δ : Fin k → Zd d L, BASigmaPi d L k M t σ' π' δ‖ ≤ C * (L : ℝ) ^ d * (1 - t))
    (hn : 3 ≤ n + 1) (σ : Fin (n + 1) → Bool) (halt : ∀ j, σ j ≠ σ (j + 1))
    (π : Finset (Fin (n + 1) × Fin (n + 1))) (hπ : π ≠ ∅) :
    ‖∑ δ : Fin (n + 1) → Zd d L, BASigmaPi d L (n + 1) M t σ π δ‖ ≤ C ^ 2 * (L : ℝ) ^ d * (1 - t) := by
  classical
  have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by
    have := NeZero.pos L
    positivity
  have h1t : 0 < 1 - t := by linarith
  have hR : 0 ≤ C ^ 2 * (L : ℝ) ^ d * (1 - t) := by positivity
  by_cases hemp : KLTSPlong (n + 1) σ π = ∅
  · have h0 : ∀ δ : Fin (n + 1) → Zd d L, BASigmaPi d L (n + 1) M t σ π δ = 0 := fun δ => by
      simp [BASigmaPi, hemp]
    simp only [h0, Finset.sum_const_zero, norm_zero]
    exact hR
  · obtain ⟨F₀, hF₀⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    obtain ⟨hF₀T, hF₀π⟩ := Finset.mem_filter.1 hF₀
    have hπdiag : π ⊆ diagonals (n + 1) := hF₀π ▸ Flong_subset_diagonals hF₀T σ
    obtain ⟨J, hJπ, hinner⟩ := exists_innermost hπdiag (Finset.nonempty_iff_ne_empty.2 hπ)
    have hJL : J ∈ KLFlong F₀ σ := by rw [hF₀π]; exact hJπ
    have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ hJL
    have hlong : σ J.1 ≠ σ J.2 := (Finset.mem_filter.1 hJL).2
    have hJd : IsDiag (n + 1) J.1 J.2 := (KLisTSP_of_mem_TSP hF₀T).1 J hJF₀
    obtain ⟨hJ1, hJ2, hJ3⟩ := hJd
    simp only [Fin.lt_def] at hJ1
    have hj := J.2.isLt
    have hJ : J.1.val + 2 ≤ J.2.val := by omega
    have ht' : (1 - (t : ℂ)) ≠ 0 := by
      intro h
      have := KSumZeroA_norm_one_sub ht1
      rw [h, norm_zero] at this
      linarith
    have hcut := KSumZeroA_cut_sum (by omega) M hshift t σ hF₀T hF₀π hJπ hinner (hrow _ _ hlong) ht'
    have hin := IH (KLwIn J + 1) (by simp only [KLwIn]; omega) (by simp only [KLwIn]; omega) (sigmaIn σ J)
      (KSumZeroA_sigmaIn_alt σ halt hJ hlong) ∅
    have hout := IH (n + 1 - KLwIn J + 1) (by simp only [KLwIn]; omega) (by simp only [KLwIn]; omega) (sigmaOut σ J)
      (KSumZeroA_sigmaOut_alt σ halt hJ hlong) ((π.erase J).image (KLshiftOut J))
    have hN := congrArg norm hcut
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, KSumZeroA_norm_one_sub ht1,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at hN
    have hS0 : 0 ≤ ‖∑ δ : Fin (n + 1) → Zd d L, BASigmaPi d L (n + 1) M t σ π δ‖ := norm_nonneg _
    have hbound : (L : ℝ) ^ d * (1 - t) * ‖∑ δ : Fin (n + 1) → Zd d L, BASigmaPi d L (n + 1) M t σ π δ‖ ≤
        (L : ℝ) ^ d * (1 - t) * (C ^ 2 * (L : ℝ) ^ d * (1 - t)) := by
      rw [hN]
      calc t * ‖∑ δ : Fin (KLwIn J + 1) → Zd d L, BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ δ‖ *
            ‖∑ δ : Fin (n + 1 - KLwIn J + 1) → Zd d L, BASigmaPi d L (n + 1 - KLwIn J + 1) M t (sigmaOut σ J)
              ((π.erase J).image (KLshiftOut J)) δ‖
          ≤ 1 * (C * (L : ℝ) ^ d * (1 - t)) * (C * (L : ℝ) ^ d * (1 - t)) := by
            refine mul_le_mul (mul_le_mul (by linarith) hin (norm_nonneg _) zero_le_one) hout (norm_nonneg _) ?_
            positivity
        _ = (L : ℝ) ^ d * (1 - t) * (C ^ 2 * (L : ℝ) ^ d * (1 - t)) := by ring
    exact le_of_mul_le_mul_left hbound (by positivity)

/-- The number of layers is at most `2^{n²}`. -/
private theorem KSumZeroA_card_layers (n : ℕ) : ((diagonals n).powerset.card : ℝ) ≤ 2 ^ (n * n) := by
  have h1 : (diagonals n).card ≤ n * n := by
    calc (diagonals n).card ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_le_univ _
      _ = n * n := by simp
  rw [Finset.card_powerset]
  exact_mod_cast Nat.pow_le_pow_right (by norm_num) h1

/-- **The strong induction on the length** (A5): `|𝒮(σ,π)| ≤ C L^d (1-t)` for every alternating `σ` of length `3 ≤ n ≤ N` and every
layer `π`, `C = C(d, N, Λ, κ)`.  Step `N + 1`: a layer `π ≠ ∅` is the cut recursion (`KSumZeroA_offdiag`, `C'²`); the layer `π = ∅`
is `(1-t)^n Σ_a 𝒦` (A2 at `W = 1`) minus the other layers, and `(1-t)^n |Σ_a 𝒦| ≤ B κ^{-(n-1)} L^d (1-t)` (A3, `η_t ≥ (1-t) κ`). -/
private theorem KSumZeroA_total_aux {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], 3 ≤ n → n ≤ N → ∀ (L : ℕ) [NeZero L], 3 ≤ L →
      ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 →
        ∀ σ : Fin n → Bool, (∀ j, σ j ≠ σ (j + 1)) → ∀ π : Finset (Fin n × Fin n),
          ‖∑ δ : Fin n → Zd d L, BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ π δ‖ ≤
            C * (L : ℝ) ^ d * (1 - t) := by
  intro N
  induction N with
  | zero => exact ⟨1, one_pos, fun n _ h3 hn => absurd hn (by omega)⟩
  | succ N ih =>
    obtain ⟨C', hC', hC'd⟩ := ih
    obtain ⟨Bn, hBn, hBnd⟩ := baK_sumAll_le (d := d) (n := N + 1) hd (by omega) hΛ hκ
    set Cn : ℝ := Bn * (κ ^ N)⁻¹ + 2 ^ ((N + 1) * (N + 1)) * C' ^ 2 with hCn
    refine ⟨max C' Cn, lt_max_of_lt_left hC', fun n _ h3 hn L _ hL g hg hgΛ E m hr t ht0 ht1 σ halt π => ?_⟩
    have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
    have h1t : 0 < 1 - t := by linarith
    rcases Nat.lt_or_ge n (N + 1) with hlt | hge
    · refine (hC'd n h3 (by omega) L hL g hg hgΛ E m hr t ht0 ht1 σ halt π).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0) h1t.le
    · have hnN : n = N + 1 := by omega
      subst hnN
      set S := BAMsigma d L (BAMB d L g (E : ℂ) m) with hS
      have hshift : ∀ (σ : Bool) (x y c : Zd d L), S σ (x + c) (y + c) = S σ x y := fun σ x y c =>
        BAMsigma_shift d L g (E : ℂ) m σ x y c
      have hrow : ∀ s s' : Bool, s ≠ s' → ∀ u : Zd d L, ∑ w, BAThetaOf S t s s' u w = (1 - (t : ℂ))⁻¹ :=
        fun s s' hss u => KSumZeroA_theta_row hr ht0 ht1 hss u
      have IH' : ∀ (k : ℕ) [NeZero k], 3 ≤ k → k ≤ N → ∀ σ' : Fin k → Bool, (∀ j, σ' j ≠ σ' (j + 1)) →
          ∀ π' : Finset (Fin k × Fin k),
            ‖∑ δ : Fin k → Zd d L, BASigmaPi d L k S t σ' π' δ‖ ≤ C' * (L : ℝ) ^ d * (1 - t) :=
        fun k _ h3 hk σ' halt' π' => hC'd k h3 hk L hL g hg hgΛ E m hr t ht0 ht1 σ' halt' π'
      have hoff : ∀ π' : Finset (Fin (N + 1) × Fin (N + 1)), π' ≠ ∅ →
          ‖∑ δ : Fin (N + 1) → Zd d L, BASigmaPi d L (N + 1) S t σ π' δ‖ ≤ C' ^ 2 * (L : ℝ) ^ d * (1 - t) :=
        fun π' hπ' => KSumZeroA_offdiag S hshift t ht0 ht1 hrow hC'.le IH' h3 σ halt π' hπ'
      have hCn0 : 0 ≤ Bn * (κ ^ N)⁻¹ := by positivity
      have hC2 : C' ^ 2 ≤ Cn := by
        have h2 : (1 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) := one_le_pow₀ (by norm_num)
        have : 0 ≤ C' ^ 2 := by positivity
        nlinarith
      have hfin : ∀ X : ℝ, X ≤ Cn * (L : ℝ) ^ d * (1 - t) → X ≤ max C' Cn * (L : ℝ) ^ d * (1 - t) := fun X hX =>
        hX.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hL0) h1t.le)
      by_cases hπ : π = ∅
      · subst hπ
        refine hfin _ ?_
        have hlay := baK_sumAll_eq_layers hκ hg hL 1 le_rfl hr ⟨ht0, ht1⟩ h3 σ halt
        have hmem : (∅ : Finset (Fin (N + 1) × Fin (N + 1))) ∈ (diagonals (N + 1)).powerset :=
          Finset.empty_mem_powerset _
        have hsplit := Finset.add_sum_erase ((diagonals (N + 1)).powerset)
          (fun π => ∑ δ : Fin (N + 1) → Zd d L, BASigmaPi d L (N + 1) S t σ π δ) hmem
        simp only [Nat.cast_one, one_pow, one_mul] at hlay
        have hE : ∑ δ : Fin (N + 1) → Zd d L, BASigmaPi d L (N + 1) S t σ ∅ δ =
            (1 - (t : ℂ)) ^ (N + 1) * ∑ a : Fin (N + 1) → Zd d L, BAKsol d L 1 S (PropSpin m) t (KLloopOf d L σ a) -
              ∑ π ∈ (diagonals (N + 1)).powerset.erase ∅, ∑ δ : Fin (N + 1) → Zd d L,
                BASigmaPi d L (N + 1) S t σ π δ := by
          rw [hlay, ← hsplit]
          ring
        have hT := hBnd L hL 1 le_rfl g hg hgΛ E m hr t ht0 ht1 σ
        simp only [Nat.cast_one, one_pow, one_mul, Nat.add_sub_cancel] at hT
        have hη : (((1 - t) * m.im)⁻¹) ≤ (((1 - t) * κ)⁻¹) :=
          inv_anti₀ (mul_pos h1t hκ) (mul_le_mul_of_nonneg_left hr.2 h1t.le)
        have hT' : (1 - t) ^ (N + 1) * ‖∑ a : Fin (N + 1) → Zd d L, BAKsol d L 1 S (PropSpin m) t
            (KLloopOf d L σ a)‖ ≤ Bn * (κ ^ N)⁻¹ * (L : ℝ) ^ d * (1 - t) := by
          calc (1 - t) ^ (N + 1) * ‖∑ a : Fin (N + 1) → Zd d L, BAKsol d L 1 S (PropSpin m) t (KLloopOf d L σ a)‖
              ≤ (1 - t) ^ (N + 1) * (Bn * (L : ℝ) ^ d * (((1 - t) * m.im)⁻¹) ^ N) :=
                mul_le_mul_of_nonneg_left hT (by positivity)
            _ ≤ (1 - t) ^ (N + 1) * (Bn * (L : ℝ) ^ d * (((1 - t) * κ)⁻¹) ^ N) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (inv_nonneg.2 (mul_pos h1t hr.1.1).le) hη N) (by positivity)) (by positivity)
            _ = Bn * (κ ^ N)⁻¹ * (L : ℝ) ^ d * (1 - t) := by
                have h2 : (1 - t) ^ N ≠ 0 := pow_ne_zero _ h1t.ne'
                have e : (1 - t) ^ (N + 1) * (((1 - t) * κ)⁻¹) ^ N = (1 - t) * (κ ^ N)⁻¹ := by
                  rw [mul_inv, mul_pow, inv_pow, inv_pow, pow_succ]
                  field_simp
                calc (1 - t) ^ (N + 1) * (Bn * (L : ℝ) ^ d * (((1 - t) * κ)⁻¹) ^ N)
                    = Bn * (L : ℝ) ^ d * ((1 - t) ^ (N + 1) * (((1 - t) * κ)⁻¹) ^ N) := by ring
                  _ = _ := by rw [e]; ring
        have hcardE : (((diagonals (N + 1)).powerset.erase ∅).card : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) :=
          le_trans (by exact_mod_cast Finset.card_erase_le) (KSumZeroA_card_layers (N + 1))
        have hsumE : ‖∑ π ∈ (diagonals (N + 1)).powerset.erase ∅, ∑ δ : Fin (N + 1) → Zd d L,
            BASigmaPi d L (N + 1) S t σ π δ‖ ≤ 2 ^ ((N + 1) * (N + 1)) * (C' ^ 2 * (L : ℝ) ^ d * (1 - t)) := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ π ∈ (diagonals (N + 1)).powerset.erase ∅, ‖∑ δ : Fin (N + 1) → Zd d L,
                BASigmaPi d L (N + 1) S t σ π δ‖
              ≤ ∑ π ∈ (diagonals (N + 1)).powerset.erase ∅, (C' ^ 2 * (L : ℝ) ^ d * (1 - t)) :=
                Finset.sum_le_sum fun π hπ => hoff π (Finset.ne_of_mem_erase hπ)
            _ = (((diagonals (N + 1)).powerset.erase ∅).card : ℝ) * (C' ^ 2 * (L : ℝ) ^ d * (1 - t)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ _ := mul_le_mul_of_nonneg_right hcardE (by positivity)
        rw [hE]
        calc ‖(1 - (t : ℂ)) ^ (N + 1) * ∑ a : Fin (N + 1) → Zd d L, BAKsol d L 1 S (PropSpin m) t (KLloopOf d L σ a) -
              ∑ π ∈ (diagonals (N + 1)).powerset.erase ∅, ∑ δ : Fin (N + 1) → Zd d L,
                BASigmaPi d L (N + 1) S t σ π δ‖
            ≤ ‖(1 - (t : ℂ)) ^ (N + 1) * ∑ a : Fin (N + 1) → Zd d L, BAKsol d L 1 S (PropSpin m) t
                (KLloopOf d L σ a)‖ + ‖∑ π ∈ (diagonals (N + 1)).powerset.erase ∅, ∑ δ : Fin (N + 1) → Zd d L,
                BASigmaPi d L (N + 1) S t σ π δ‖ := norm_sub_le _ _
          _ ≤ Bn * (κ ^ N)⁻¹ * (L : ℝ) ^ d * (1 - t) + 2 ^ ((N + 1) * (N + 1)) * (C' ^ 2 * (L : ℝ) ^ d * (1 - t)) := by
              refine add_le_add ?_ hsumE
              rw [norm_mul, norm_pow, KSumZeroA_norm_one_sub ht1]
              exact hT'
          _ = Cn * (L : ℝ) ^ d * (1 - t) := by rw [hCn]; ring
      · exact hfin _ ((hoff π hπ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hL0) h1t.le))

/-- **The signed sum-zero, in the total form** (`(eq:Sigma-empty-sum-zero)`, `A:728-734`): for `σ` cyclically alternating,
`3 ≤ n`, and **every layer `π`**, `|Σ_δ Σ^{(π)}(δ)| ≤ C L^d (1-t)`, with `C = C(d, n, Λ, κ)` uniform in `L ≥ 3`, `g ∈ (0, Λ]`, the
real-axis data and `t ∈ [0, 1)` (no smallness of `g`: supervisor 1155 C1). -/
theorem baSigmaPi_total_le {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, (∀ j, σ j ≠ σ (j + 1)) →
        ∀ π : Finset (Fin n × Fin n),
          ‖∑ δ : Fin n → Zd d L, BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ π δ‖ ≤
            C * (L : ℝ) ^ d * (1 - t) := by
  obtain ⟨C, hC, h⟩ := KSumZeroA_total_aux hd hΛ hκ n
  exact ⟨C, hC, fun L _ hL g hg hgΛ E m hr t ht0 ht1 σ halt π => h n hn le_rfl L hL g hg hgΛ E m hr t ht0 ht1 σ halt π⟩

end Induction

/-! ## 7. The signed sum-zero of `BASig` -/

/-- **The signed sum-zero, uniform form** (the first bound clause of `SigSumZeroAbs`, `Loop/KLIndStepA.lean:1036`, at `BASig`):
for `σ` cyclically alternating, `3 ≤ n`, every root `r` and label `x`, `|Σ_{δ_r = x} Σ^{(∅)}(δ)| ≤ C (1-t)`.  The slice sum is
`𝒮(σ,∅)/L^d` (`baSigmaPi_slice`), and `baSigmaPi_total_le`.  `C = C(d, n, Λ, κ)`: no smallness of `g` (1155 C1). -/
theorem baSig_signed_sum_unif {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, (∀ j, σ j ≠ σ (j + 1)) →
        ∀ (r : Fin n) (x : Zd d L),
          ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = x),
              BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ ∅ δ‖ ≤ C * (1 - t) := by
  obtain ⟨C, hC, h⟩ := baSigmaPi_total_le hd hn hΛ hκ
  refine ⟨C, hC, fun L _ hL g hg hgΛ E m hr t ht0 ht1 σ halt r x => ?_⟩
  have hsl := baSigmaPi_slice (BAMsigma d L (BAMB d L g (E : ℂ) m))
    (fun σ x y c => BAMsigma_shift d L g (E : ℂ) m σ x y c) t σ ∅ r x
  have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by
    have := NeZero.pos L
    positivity
  have h1 := h L hL g hg hgΛ E m hr t ht0 ht1 σ halt ∅
  rw [← hsl, norm_mul, norm_pow, Complex.norm_natCast] at h1
  exact le_of_mul_le_mul_left (h1.trans (le_of_eq (by ring))) hL0

/-- **The signed sum-zero of `BASig`, family form** (the first bound clause of `SigSumZeroAbs` at `BASig d n L g E m t`): over a
family `ι` of data `3 ≤ L i`, `0 < g i ≤ Λ`, `BAReal d (L i) (g i) κ (E i) (m i)`, `0 ≤ t i < 1`, one constant `C = C(d, n, Λ, κ)` with
`|Σ_{δ_r = x} Σ^{(∅)}(δ)| ≤ C (1 - t i)` at every alternating `σ`, root `r`, label `x`.  The strict `t i < 1` and `3 ≤ n` are the ranges
of the consumers (`KLIndStepB.lean:297, 362`) and of the band instance `sigSumZeroAbs_band`; `SigSumZeroAbs` itself is untouched. -/
theorem baSig_signed_sum {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ)
    (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i)
    (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d (L i)),
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), BASig d n L g E m t i σ δ‖ ≤ C * (1 - t i) := by
  obtain ⟨C, hC, h⟩ := baSig_signed_sum_unif hd hn hΛ hκ
  exact ⟨C, hC, fun i σ halt r x =>
    h (L i) (hL i) (g i) (hg i) (hgΛ i) (E i) (m i) (hr i) (t i) (ht0 i) (ht1 i) σ halt r x⟩

/-! ## 8. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m₀`,
`0 < P.g0 ≤ 10`), `Λ = 10`, `κ = Im m₀ > 0`, `n = 4` (and `n = 6`), `σ = KLsigAlt n = (+,-,+,-,…)` (cyclically alternating), `t = 1/2`
and `t = 999/1000` (near `1`), `W = 1` and `W = 2`.  `TSP 4` has three trees and `KLTSPlong 4 σ ∅ = TSP 4` (two examples below);
at `n = 6` the long layer `π = {(0,3)}` is nonempty.  Every deterministic hypothesis of every theorem is discharged at this datum;
no hypothesis of another gate remains (no pin enters: `BAKsolve` is the merged `baKsolve`). -/

namespace KSumZeroAInst

open RBM.BA.MFixedPointInst

/-- The datum is not degenerate: `KLsigAlt 4` is cyclically alternating, and the layer `π = ∅` of `TSP 4` is nonempty. -/
example : ∀ j : Fin 4, KLsigAlt 4 j ≠ KLsigAlt 4 (j + 1) := by decide

example : KLTSPlong 4 (KLsigAlt 4) ∅ = TSP 4 := by decide

example : (TSP 4).card = 3 := by rw [TSP_four]; decide

/-- **`baSigmaPi_slice`** at `P`: the slice sum (root `0`, label `0`) times `4^3` is the total sum; the layer `π = ∅`. -/
example :=
  baSigmaPi_slice (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
    (fun σ x y c => BAMsigma_shift 3 4 P.g0 _ P.m0 σ x y c) (1 / 2) (KLsigAlt 4) ∅ 0 0

/-- **`baK_sumAll_eq_layers`** (A2) at `P`, `W = 1`, `t = 1/2`: `(1-t)^4 Σ_a 𝒦^{(4)} = Σ_π Σ_δ Σ^{(π)}`. -/
example :=
  baK_sumAll_eq_layers (d := 3) (L := 4) (n := 4) P.real.1.1 P.g0_pos (by norm_num) 1 le_rfl P.real
    (t := 1 / 2) ⟨by norm_num, by norm_num⟩ (by norm_num) (KLsigAlt 4) (by decide)

/-- The same at `W = 2` (`W^d = 8`), `t = 999/1000`. -/
example :=
  baK_sumAll_eq_layers (d := 3) (L := 4) (n := 4) P.real.1.1 P.g0_pos (by norm_num) 2 (by norm_num) P.real
    (t := 999 / 1000) ⟨by norm_num, by norm_num⟩ (by norm_num) (KLsigAlt 4) (by decide)

/-- **`baK_sumAll_le`** (T1, the Ward bound for sums) at `P`: the bound on `Σ_a 𝒦^{(4)}_{t,σ,a}` at `W = 2`, `t = 1/2`, `σ = KLsigAlt 4`
(the constant `B` is the theorem's; `Λ = 10`, `κ = Im m₀`). -/
example : ∃ B : ℝ, 0 < B ∧
    ‖∑ a : Fin 4 → Zd 3 4, BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
      (KLloopOf 3 4 (KLsigAlt 4) a)‖ ≤ B * (4 : ℝ) ^ 3 * (((2 : ℝ) ^ 3 * ((1 - 1 / 2) * P.m0.im))⁻¹) ^ 3 := by
  obtain ⟨B, hB, h⟩ := baK_sumAll_le (d := 3) (n := 4) (by norm_num) (by norm_num) (Λ := 10) (κ := P.m0.im)
    (by norm_num) P.real.1.1
  exact ⟨B, hB, by
    simpa using h 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
      (by norm_num) (KLsigAlt 4)⟩

/-- `baK_sumAll_le` at `n = 1` and at `n = 3` (a constant charge vector, the pure bound), `t = 999/1000`, `W = 1`. -/
example : ∃ B : ℝ, 0 < B ∧
    ‖∑ a : Fin 3 → Zd 3 4, BAKsol 3 4 1 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (999 / 1000)
      (KLloopOf 3 4 (fun _ => true) a)‖ ≤ B * (4 : ℝ) ^ 3 * (((1 : ℝ) ^ 3 * ((1 - 999 / 1000) * P.m0.im))⁻¹) ^ 2 := by
  obtain ⟨B, hB, h⟩ := baK_sumAll_le (d := 3) (n := 3) (by norm_num) (by norm_num) (Λ := 10) (κ := P.m0.im)
    (by norm_num) P.real.1.1
  exact ⟨B, hB, by
    simpa using h 4 (by norm_num) 1 le_rfl P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (999 / 1000) (by norm_num)
      (by norm_num) (fun _ => true)⟩

/-- **`baSigmaPi_total_le`** (A5) at `P`, `t = 999/1000`, the layer `π = ∅`: `|Σ_δ Σ^{(∅)}(δ)| ≤ C 4^3 (1-t)`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖∑ δ : Fin 4 → Zd 3 4, BASigmaPi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (999 / 1000) (KLsigAlt 4) ∅ δ‖ ≤
      C * (4 : ℝ) ^ 3 * (1 - 999 / 1000) := by
  obtain ⟨C, hC, h⟩ := baSigmaPi_total_le (d := 3) (n := 4) (by norm_num) (by norm_num) (Λ := 10) (κ := P.m0.im)
    (by norm_num) P.real.1.1
  exact ⟨C, hC, by
    simpa using h 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (999 / 1000) (by norm_num) (by norm_num)
      (KLsigAlt 4) (by decide) ∅⟩

/-- `n = 6`: `σ = KLsigAlt 6` is cyclically alternating and the layer `π = {(0,3)}` (a long chord, `σ_0 ≠ σ_3`) is nonempty
(the tree `{(0,3)} ∈ TSP 6`), so the cut recursion of the proof is exercised at `n = 6` (inner and outer polygon of length `4`). -/
example : ∀ j : Fin 6, KLsigAlt 6 j ≠ KLsigAlt 6 (j + 1) := by decide

example : ({((0 : Fin 6), (3 : Fin 6))} : Finset (Fin 6 × Fin 6)) ∈
    KLTSPlong 6 (KLsigAlt 6) {((0 : Fin 6), (3 : Fin 6))} := by
  simp only [KLTSPlong, Finset.mem_filter]
  exact ⟨by rw [mem_TSP]; decide, by decide⟩

/-- **`baSigmaPi_total_le`** at `n = 6`, `P`, `t = 1/2`, the nonempty long layer `π = {(0,3)}`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖∑ δ : Fin 6 → Zd 3 4, BASigmaPi 3 4 6 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (KLsigAlt 6)
      {((0 : Fin 6), (3 : Fin 6))} δ‖ ≤ C * (4 : ℝ) ^ 3 * (1 - 1 / 2) := by
  obtain ⟨C, hC, h⟩ := baSigmaPi_total_le (d := 3) (n := 6) (by norm_num) (by norm_num) (Λ := 10) (κ := P.m0.im)
    (by norm_num) P.real.1.1
  exact ⟨C, hC, by
    simpa using h 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      (KLsigAlt 6) (by decide) {((0 : Fin 6), (3 : Fin 6))}⟩

/-- **`baSig_signed_sum_unif`** (T2, uniform form) at `P`, `t = 1/2`, root `r = 0`, label `x = 0`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0),
        BASigmaPi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (KLsigAlt 4) ∅ δ‖ ≤ C * (1 - 1 / 2) := by
  obtain ⟨C, hC, h⟩ := baSig_signed_sum_unif (d := 3) (n := 4) (by norm_num) (by norm_num) (Λ := 10) (κ := P.m0.im)
    (by norm_num) P.real.1.1
  exact ⟨C, hC, by
    simpa using h 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      (KLsigAlt 4) (by decide) 0 0⟩

/-- **`baSig_signed_sum`** (T2, family form, the first bound clause of `SigSumZeroAbs` at `BASig`) at `P`, `ι = Unit`,
`t = 999/1000`: every alternating `σ` (here all of `Fin 4 → Bool` with the hypothesis), every root and label. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ (i : Unit) (σ : Fin 4 → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin 4) (x : Zd 3 4),
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ r = x),
        BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000) i
          σ δ‖ ≤ C * (1 - (999 : ℝ) / 1000) :=
  baSig_signed_sum (ι := Unit) (d := 3) (n := 4) (by norm_num) (by norm_num) (Λ := 10) (κ := P.m0.im) (by norm_num)
    P.real.1.1 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000)
    (fun _ => by norm_num) (fun _ => P.g0_pos) (fun _ => P.g0_le) (fun _ => P.real) (fun _ => by norm_num)
    (fun _ => by norm_num)

end KSumZeroAInst

end RBM.BA
