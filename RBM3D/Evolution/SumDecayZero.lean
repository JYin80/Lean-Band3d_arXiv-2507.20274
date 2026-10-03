/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.SumDecay
import RBM3D.Propagator.Prop6Hold

/-!
# Evolution kernel EK-4: `(sumAzero) ⟹ (sum_res_2)` of `lem:sum_decay`, every `n ≥ 2`, `d ≥ 3`

Proof `ekSumDecay2_holds : EKSumDecay2 d n Λ κ` of the pin of `RBM3D/Evolution/Pins.lean`,
uniform in `g ∈ (0, Λ]`.  The pin carries the antecedent `L^d ≤ W^K` and the constant `C`
depends on `K` (candidate `T2042a`, DECISIONS §21): the leading term of `(eq:bddfA)` vanishes
by `(sumAzero)` only over all of `b'`, so the window complement costs `W^{-D} L^{d(n-1)}`.

Route (paper `A_deterministic_estimates.tex:155-199`).  `u_i = δ + Ξ_i` (`(eq:decompUalt)`); the
index `i₀` of the sum-zero property carries `δ + Ξ_{i₀}`.

* `δ`-part and `S_near` (`|b_{i₀} - a_i| ≤ W^{2ε} ℓ_s` for some `i`): `ek_core_bound` with the
  anchor `i₀`; the near ball sums of `Ξ` come from `ekXiBall_holds` (`Λ' = W^{2ε}`).
* `S_far`: the window `|b_i - b_{i₀}| < W^ε ℓ_s` and its complement (where `(deccA0)` gives
  `W^{-D}`); on the window `u_i = Ξ_i` (no `δ`), and `Ξ_i(a_i, b_i) = Ξ_i(a_i, b_{i₀}) + ΔΞ_i`
  is expanded over the subsets of `{i ≠ i₀}`.  The empty subset is killed by `(sumAzero)`
  (`ekSZ_fempty_bound`); every other subset has a distinguished index whose `ΔΞ` is bounded by
  `(prop:BD1)` at `c = 1/2` (`ekSZ_dXi_le`, range `ρ ≥ 4`) and summed against `Ξ_{i₀}` by
  `latticesum_d3` (`ekSZ_lattice`, `log L ≤ W^ε`).

Part I (`ekSZ_core`) is the combinatorics over an arbitrary finite type; Part II
(`ekSZ_concrete`) verifies its hypotheses on `Z_L^d`; Part III is the arithmetic of the
constants; Part IV is the pin and its instances.  Only `ekSumDecay2_holds` is public; every
helper is private.  The exponent of `W^ε` proved is `m₁ + 2n + 2` (not the paper's `n + 5`: each
window sum is bounded by `ρ² r`); the pin's `C` is existential, so this changes no statement.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace RBM

open Matrix
open scoped Matrix.Norms.Operator

/-! ### Part I: the combinatorics, over an arbitrary finite type -/

section Core

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- the one-index kernel row `u_i(a_i, ·) = δ_{a_i ·} + Ξ_i(a_i, ·)` of `(eq:decompUalt)`. -/
private noncomputable def ekSZU (Ξ : Fin n → X → X → ℂ) (a : Fin n → X) (i : Fin n) (y : X) : ℂ :=
  (if a i = y then 1 else 0) + Ξ i (a i) y

omit [Fintype X] in
/-- a row of `u` over a finite set is at most `1` plus the row of `Ξ`. -/
private theorem ekSZ_u_sum_le (Ξ : Fin n → X → X → ℂ) (a : Fin n → X) (i : Fin n) (E : Finset X) :
    ∑ y ∈ E, ‖ekSZU Ξ a i y‖ ≤ 1 + ∑ y ∈ E, ‖Ξ i (a i) y‖ := by
  have h1 : ∀ y ∈ E, ‖ekSZU Ξ a i y‖ ≤ (if a i = y then (1 : ℝ) else 0) + ‖Ξ i (a i) y‖ := by
    intro y _
    refine (norm_add_le _ _).trans ?_
    by_cases h : a i = y <;> simp [h]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib]
  have h2 : ∑ y ∈ E, (if a i = y then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
  linarith

/-- the number of `b : Fin n → X` with `b k = x` is `|X|^{n-1}`. -/
private theorem ekSZ_fiber_card (k : Fin n) (x : X) :
    (Finset.univ.filter (fun b : Fin n → X => b k = x)).card = Fintype.card X ^ (n - 1) := by
  classical
  have h : Finset.univ.filter (fun b : Fin n → X => b k = x)
      = Fintype.piFinset (fun i => if i = k then ({x} : Finset X) else Finset.univ) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hb i
      by_cases hi : i = k
      · subst hi; simp [hb]
      · simp [hi]
    · intro h
      have := h k
      simpa using this
  rw [h, Fintype.card_piFinset]
  have h2 : ∀ i : Fin n, (if i = k then ({x} : Finset X) else Finset.univ).card
      = if i = k then 1 else Fintype.card X := by
    intro i; by_cases hi : i = k <;> simp [hi]
  simp only [h2]
  have h3 : ∏ i : Fin n, (if i = k then 1 else Fintype.card X) = Fintype.card X ^ (n - 1) := by
    rw [← Finset.prod_erase Finset.univ (f := fun i : Fin n => if i = k then 1 else Fintype.card X)
      (a := k) (by simp)]
    rw [Finset.prod_congr rfl (g := fun _ => Fintype.card X)
      (fun i hi => by simp [Finset.ne_of_mem_erase hi]), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  exact h3

/-- **Anchored sum with anchor-dependent kernels** (equality): over the window
`{b : ∀ i ≠ k, b_i ∈ Win(b_k)}` the sum of `F(b_k) ∏_{i≠k} h_i(b_k, b_i)` is
`Σ_x F(x) ∏_{i≠k} Σ_{y ∈ Win(x)} h_i(x, y)`. -/
private theorem ekSZ_anchor_dep (k : Fin n) (Win : X → Finset X) (F : X → ℝ)
    (h : Fin n → X → X → ℝ) :
    ∑ b : Fin n → X, (if ∀ i, i ≠ k → b i ∈ Win (b k) then
        F (b k) * ∏ i ∈ Finset.univ.erase k, h i (b k) (b i) else 0)
      = ∑ x : X, F x * ∏ i ∈ Finset.univ.erase k, ∑ y ∈ Win x, h i x y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin n → X => b k)]
  refine Finset.sum_congr rfl fun x _ => ?_
  set T : ∀ _ : Fin n, Finset X := fun i => if i = k then {x} else Win x with hT
  rw [← Finset.sum_filter, Finset.filter_filter]
  have hset : Finset.univ.filter (fun b : Fin n → X =>
      b k = x ∧ ∀ i, i ≠ k → b i ∈ Win (b k)) = Fintype.piFinset T := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hT]
    constructor
    · rintro ⟨hb, hW⟩ i
      by_cases hi : i = k
      · subst hi; simp [hb]
      · simp only [hi, ite_false]; rw [← hb]; exact hW i hi
    · intro h
      have hk : b k = x := by simpa using h k
      refine ⟨hk, fun i hi => ?_⟩
      have := h i
      simp only [hi, ite_false] at this
      rwa [hk]
  rw [hset]
  have h2 : ∀ b ∈ Fintype.piFinset T, F (b k) * ∏ i ∈ Finset.univ.erase k, h i (b k) (b i)
      = F x * ∏ i ∈ Finset.univ.erase k, h i x (b i) := by
    intro b hb
    have hk : b k = x := by
      have := Fintype.mem_piFinset.mp hb k
      simpa [hT] using this
    rw [hk]
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  congr 1
  set g : Fin n → X → ℝ := fun i y => if i = k then 1 else h i x y with hg
  have h3 : ∀ b : Fin n → X, ∏ i ∈ Finset.univ.erase k, h i x (b i) = ∏ i, g i (b i) := by
    intro b
    rw [← Finset.prod_erase Finset.univ (f := fun i => g i (b i)) (a := k) (by simp [hg])]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [hg, Finset.ne_of_mem_erase hi]
  rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.prod_univ_sum]
  rw [← Finset.prod_erase Finset.univ
    (f := fun i => ∑ y ∈ T i, g i y) (a := k) (by simp [hT, hg])]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp [hT, hg, Finset.ne_of_mem_erase hi]


/-- **The `δ + near` part**: with a row `w` at the index `i₀` (row-sum `≤ Rk`) and the one-index
kernels `u_i(a_i, ·)` at the other indices, `ek_core_bound` gives
`M Rk (1+Sξ)^{n-1} + δ Rk (1+Q)^{n-1}`. -/
private theorem ekSZ_UW_bound (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) {M δ Q Sξ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 ≤ δ)
    (hSξ0 : 0 ≤ Sξ) (hM : ∀ b, ‖A b‖ ≤ M)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hrow : ∀ i x, ∑ y, ‖Ξ i x y‖ ≤ Q)
    (hwin : ∀ i, i ≠ i₀ → ∀ x, ∑ y ∈ Win x, ‖Ξ i (a i) y‖ ≤ Sξ)
    (w : X → ℂ) {Rk : ℝ} (hw : ∑ x, ‖w x‖ ≤ Rk) :
    ‖∑ b : Fin n → X, ((w (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b‖
      ≤ M * (Rk * (1 + Sξ) ^ (n - 1)) + δ * (Rk * (1 + Q) ^ (n - 1)) := by
  classical
  set κ : Fin n → X → ℂ := fun i y => if i = i₀ then w y else ekSZU Ξ a i y with hκ
  have hprod : ∀ b : Fin n → X, ∏ i, κ i (b i)
      = (w (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i) := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ (fun i => κ i (b i)) (Finset.mem_univ i₀)]
    congr 1
    · simp [hκ]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [hκ, Finset.ne_of_mem_erase hi]
  have hbound := ek_core_bound (X := X) i₀ (fun x y => y ∈ Win x) κ A (M := M) (δ := δ)
    (S := 1 + Sξ) (P := 1 + Q) (Rk := Rk) hM0 hδ hM htail (by linarith) ?_ ?_ ?_
  · simpa only [hprod] using hbound
  · intro i hi x
    have hfilt : Finset.univ.filter (fun y => y ∈ Win x) = Win x := by
      ext y; simp
    rw [hfilt]
    have : ∀ y, κ i y = ekSZU Ξ a i y := fun y => by simp [hκ, hi]
    simp only [this]
    exact (ekSZ_u_sum_le Ξ a i (Win x)).trans (by linarith [hwin i hi x])
  · intro i hi
    have : ∀ y, κ i y = ekSZU Ξ a i y := fun y => by simp [hκ, hi]
    simp only [this]
    exact (ekSZ_u_sum_le Ξ a i Finset.univ).trans (by linarith [hrow i (a i)])
  · simpa [hκ] using hw


/-- **The tail part**: off the window `|A_b| ≤ δ`, and the product of the rows is summable. -/
private theorem ekSZ_tail_bound (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) (wf : X → ℂ) {δ Q Rk : ℝ} (hδ : 0 ≤ δ)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hrow : ∀ i x, ∑ y, ‖Ξ i x y‖ ≤ Q) (hw : ∑ x, ‖wf x‖ ≤ Rk) :
    ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
        ((wf (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b)‖
      ≤ δ * (Rk * (1 + Q) ^ (n - 1)) := by
  classical
  set K : Fin n → X → ℝ := fun i y => if i = i₀ then ‖wf y‖ else ‖ekSZU Ξ a i y‖ with hK
  have hK0 : ∀ i x, 0 ≤ K i x := fun i x => by
    simp only [hK]; split_ifs <;> exact norm_nonneg _
  have hprod : ∀ b : Fin n → X, ∏ i, K i (b i)
      = ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖ekSZU Ξ a i (b i)‖ := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ (fun i => K i (b i)) (Finset.mem_univ i₀)]
    congr 1
    · simp [hK]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [hK, Finset.ne_of_mem_erase hi]
  have hsum := ek_prod_sum_le i₀ K hK0 (P := 1 + Q) (Rk := Rk) ?_ ?_
  · calc ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
          ((wf (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b)‖
        ≤ ∑ b : Fin n → X, ‖(if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
          ((wf (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b)‖ := norm_sum_le _ _
      _ ≤ ∑ b : Fin n → X, δ * ∏ i, K i (b i) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [hprod b]
          have hp0 : 0 ≤ ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖ekSZU Ξ a i (b i)‖ :=
            mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
          split_ifs with hwb
          · simpa using mul_nonneg hδ hp0
          · rw [norm_mul, norm_mul, norm_prod]
            have := htail b hwb
            have hp1 : 0 ≤ ∏ i ∈ Finset.univ.erase i₀, ‖ekSZU Ξ a i (b i)‖ :=
              Finset.prod_nonneg fun i _ => norm_nonneg _
            calc ‖wf (b i₀)‖ * (∏ i ∈ Finset.univ.erase i₀, ‖ekSZU Ξ a i (b i)‖) * ‖A b‖
                ≤ ‖wf (b i₀)‖ * (∏ i ∈ Finset.univ.erase i₀, ‖ekSZU Ξ a i (b i)‖) * δ :=
                  mul_le_mul_of_nonneg_left this hp0
              _ = δ * (‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖ekSZU Ξ a i (b i)‖) := by ring
      _ = δ * ∑ b : Fin n → X, ∏ i, K i (b i) := by rw [Finset.mul_sum]
      _ ≤ δ * (Rk * (1 + Q) ^ (n - 1)) := mul_le_mul_of_nonneg_left hsum hδ
  · intro i hi
    have : ∀ y, K i y = ‖ekSZU Ξ a i y‖ := fun y => by simp [hK, hi]
    simp only [this]
    exact (ekSZ_u_sum_le Ξ a i Finset.univ).trans (by linarith [hrow i (a i)])
  · simpa [hK] using hw

/-- **The leading term**: the window part of a function of `b_{i₀}` alone is, by `(sumAzero)`,
minus the off-window part, which is at most `δ` per point (the paper's `W^{-D+n}`, here with the
count `|X|^{n-1}` of the complement). -/
private theorem ekSZ_fempty_bound (i₀ : Fin n) (A : (Fin n → X) → ℂ) (Win : X → Finset X)
    (c : X → ℂ) {δ Cc : ℝ} (hδ : 0 ≤ δ)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hsz : ∀ x, ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), A b = 0)
    (hc : ∑ x, ‖c x‖ ≤ Cc) :
    ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖
      ≤ δ * (Cc * (Fintype.card X) ^ (n - 1)) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin n → X => b i₀)]
  have hx : ∀ x : X, ‖∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
      (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖
      ≤ ‖c x‖ * (δ * (Fintype.card X) ^ (n - 1)) := by
    intro x
    have h1 : ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)
        = c x * ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then A b else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hbx : b i₀ = x := (Finset.mem_filter.mp hb).2
      rw [hbx]
      split_ifs <;> simp
    have h2 : ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then A b else 0)
        = - ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else A b) := by
      have h := hsz x
      have h3 : ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), A b
          = ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
              (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then A b else 0)
            + ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
              (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else A b) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      rw [h3] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [h1, h2, norm_mul, norm_neg]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else A b)‖
        ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), δ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          split_ifs with hwb
          · simpa using hδ
          · exact htail b hwb
      _ = δ * (Fintype.card X) ^ (n - 1) := by
          rw [Finset.sum_const, ekSZ_fiber_card, nsmul_eq_mul]
          push_cast; ring
  calc ‖∑ x : X, ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖
      ≤ ∑ x : X, ‖∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ x : X, ‖c x‖ * (δ * (Fintype.card X) ^ (n - 1)) := Finset.sum_le_sum fun x _ => hx x
    _ = (∑ x : X, ‖c x‖) * (δ * (Fintype.card X) ^ (n - 1)) := (Finset.sum_mul _ _ _).symm
    _ ≤ Cc * (δ * (Fintype.card X) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = δ * (Cc * (Fintype.card X) ^ (n - 1)) := by ring


/-- `∏_{i ∈ S} (if i ∈ B then f i else g i) = ∏_{i ∈ B} f i * ∏_{i ∈ S \ B} g i` for `B ⊆ S`. -/
private theorem ekSZ_prod_ite_subset {ι : Type*} [DecidableEq ι] {S B : Finset ι} (hB : B ⊆ S)
    (f g : ι → ℝ) :
    ∏ i ∈ S, (if i ∈ B then f i else g i) = (∏ i ∈ B, f i) * ∏ i ∈ S \ B, g i := by
  rw [Finset.prod_ite]
  congr 2
  · ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hB h, h⟩⟩
  · ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff]

/-- **A term of the first-difference expansion with a non-empty set `B` of differenced indices**:
the sum over the window of `w_far(b_{i₀}) ∏_{i∈B} Δ_i ∏_{i∉B} X_i A_b` is at most
`M Snon^{n-2} Ψ`, where `Ψ` bounds the lattice sum of the distinguished index `j ∈ B`. -/
private theorem ekSZ_fB_bound (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) (far : X → Prop) [DecidablePred far]
    (wf : X → ℂ) (hwf : ∀ x, ‖wf x‖ = if far x then ‖Ξ i₀ (a i₀) x‖ else 0)
    {M Snon Ψ : ℝ} (hM0 : 0 ≤ M) (hSnon0 : 0 ≤ Snon) (hM : ∀ b, ‖A b‖ ≤ M)
    (hX : ∀ x, far x → ∀ i, i ≠ i₀ → ((Win x).card : ℝ) * ‖Ξ i (a i) x‖ ≤ Snon)
    (hΔ : ∀ x, far x → ∀ i, i ≠ i₀ → ∑ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖ ≤ Snon)
    (hΨ : ∀ j, j ≠ i₀ → ∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
        ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ ≤ Ψ)
    (B : Finset (Fin n)) (hBS : B ⊆ Finset.univ.erase i₀) (hBne : B.Nonempty) :
    ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ M * (Snon ^ (n - 2) * Ψ) := by
  classical
  obtain ⟨j, hjB⟩ := hBne
  have hjS : j ∈ Finset.univ.erase i₀ := hBS hjB
  have hji : j ≠ i₀ := Finset.ne_of_mem_erase hjS
  set h : Fin n → X → X → ℝ := fun i x y =>
    if i ∈ B then ‖Ξ i (a i) y - Ξ i (a i) x‖ else ‖Ξ i (a i) x‖ with hh
  -- step 1: pointwise
  have hpt : ∀ b : Fin n → X, ‖(if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ M * (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i) else 0) := by
    intro b
    split_ifs with hwb
    · rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod]
      have hprod : ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i)
          = (∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖ :=
        ekSZ_prod_ite_subset hBS (fun i => ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
          (fun i => ‖Ξ i (a i) (b i₀)‖)
      rw [hprod]
      have hp0 : 0 ≤ ‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖) :=
        mul_nonneg (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _))
      calc ‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖) * ‖A b‖
          ≤ ‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖) * M :=
            mul_le_mul_of_nonneg_left (hM b) hp0
        _ = M * (‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖)) := by ring
    · simp
  -- step 2: the anchored sum
  have hsum : ∑ b : Fin n → X, M * (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i) else 0)
      = M * ∑ x : X, ‖wf x‖ * ∏ i ∈ Finset.univ.erase i₀, ∑ y ∈ Win x, h i x y := by
    rw [← Finset.mul_sum, ekSZ_anchor_dep i₀ Win (fun x => ‖wf x‖) h]
  -- step 3: the bound at a point `x`
  have hx : ∀ x : X, ‖wf x‖ * ∏ i ∈ Finset.univ.erase i₀, ∑ y ∈ Win x, h i x y
      ≤ if far x then ‖Ξ i₀ (a i₀) x‖ * (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖) * Snon ^ (n - 2)
        else 0 := by
    intro x
    by_cases hfx : far x
    · have hw := hwf x
      simp only [hfx, ↓reduceIte] at hw ⊢
      rw [hw]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun i => ∑ y ∈ Win x, h i x y) hjS]
      have hj : ∑ y ∈ Win x, h j x y = ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ := by
        simp [hh, hjB]
      rw [hj]
      have hrest : ∏ i ∈ (Finset.univ.erase i₀).erase j, ∑ y ∈ Win x, h i x y ≤ Snon ^ (n - 2) := by
        calc ∏ i ∈ (Finset.univ.erase i₀).erase j, ∑ y ∈ Win x, h i x y
            ≤ ∏ _i ∈ (Finset.univ.erase i₀).erase j, Snon := by
              refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => ?_) ?_
              · simp only [hh]; split_ifs <;> exact norm_nonneg _
              · intro i hi
                have hij : i ≠ j := Finset.ne_of_mem_erase hi
                have hiS : i ∈ Finset.univ.erase i₀ := Finset.mem_of_mem_erase hi
                have hii : i ≠ i₀ := Finset.ne_of_mem_erase hiS
                by_cases hiB : i ∈ B
                · simp only [hh, hiB, ↓reduceIte]
                  exact hΔ x hfx i hii
                · simp only [hh, hiB, ↓reduceIte]
                  rw [Finset.sum_const, nsmul_eq_mul]
                  exact hX x hfx i hii
          _ = Snon ^ (n - 2) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem hjS,
                Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
              congr 1
      have hs0 : 0 ≤ ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ :=
        Finset.sum_nonneg fun y _ => norm_nonneg _
      calc ‖Ξ i₀ (a i₀) x‖ * ((∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖)
            * ∏ i ∈ (Finset.univ.erase i₀).erase j, ∑ y ∈ Win x, h i x y)
          ≤ ‖Ξ i₀ (a i₀) x‖ * ((∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖) * Snon ^ (n - 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrest hs0) (norm_nonneg _)
        _ = ‖Ξ i₀ (a i₀) x‖ * (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖) * Snon ^ (n - 2) := by
            ring
    · have hw := hwf x
      simp only [hfx, ↓reduceIte] at hw ⊢
      rw [hw]
      simp
  -- step 4: the sum over `x`
  calc ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ ∑ b : Fin n → X, ‖(if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n → X, M * (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i) else 0) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = M * ∑ x : X, ‖wf x‖ * ∏ i ∈ Finset.univ.erase i₀, ∑ y ∈ Win x, h i x y := hsum
    _ ≤ M * ∑ x : X, (if far x then ‖Ξ i₀ (a i₀) x‖ * (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖)
          * Snon ^ (n - 2) else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hx x) hM0
    _ = M * ((∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
          (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖)) * Snon ^ (n - 2)) := by
        rw [← Finset.sum_filter, Finset.sum_mul]
    _ ≤ M * (Ψ * Snon ^ (n - 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hΨ j hji) (by positivity)) hM0
    _ = M * (Snon ^ (n - 2) * Ψ) := by ring


/-- **The abstract core of `(sumAzero) ⟹ (sum_res_2)`.**  Over any finite type `X`, with the one-index
rows `u_i = δ + Ξ_i`, the product of `n` rows against a sum-zero tensor `A` (zero sum over all indices
but `i₀`, fast decay `δ` off the window `Win`) is bounded by the five terms below: the part of the
sum with `δ_{a_{i₀} b_{i₀}}` or `b_{i₀}` near an `a_i`, the off-window tail, the leading term killed by
the sum-zero property up to the complement count `|X|^{n-1}`, and the first-difference terms
(`2^{n-1}` subsets, each carrying the lattice sum `Ψ`). -/
private theorem ekSZ_core (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) (far : X → Prop) [DecidablePred far]
    {M δ Q Sξ Rn Snon Ψ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 ≤ δ) (hQ0 : 0 ≤ Q) (hSξ0 : 0 ≤ Sξ)
    (hSnon0 : 0 ≤ Snon) (hΨ0 : 0 ≤ Ψ) (hM : ∀ b, ‖A b‖ ≤ M)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hsz : ∀ x, ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), A b = 0)
    (hrow : ∀ i x, ∑ y, ‖Ξ i x y‖ ≤ Q)
    (hwin : ∀ i, i ≠ i₀ → ∀ x, ∑ y ∈ Win x, ‖Ξ i (a i) y‖ ≤ Sξ)
    (hnear : ∑ x ∈ Finset.univ.filter (fun x => ¬ far x), ‖Ξ i₀ (a i₀) x‖ ≤ Rn)
    (hne : ∀ x, far x → ∀ i, i ≠ i₀ → ∀ y ∈ Win x, a i ≠ y)
    (hX : ∀ x, far x → ∀ i, i ≠ i₀ → ((Win x).card : ℝ) * ‖Ξ i (a i) x‖ ≤ Snon)
    (hΔ : ∀ x, far x → ∀ i, i ≠ i₀ → ∑ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖ ≤ Snon)
    (hΨ : ∀ j, j ≠ i₀ → ∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
        ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ ≤ Ψ) :
    ‖∑ b : Fin n → X, (∏ i, ekSZU Ξ a i (b i)) * A b‖ ≤
      (M * ((1 + Rn) * (1 + Sξ) ^ (n - 1)) + δ * ((1 + Rn) * (1 + Q) ^ (n - 1)))
        + δ * (Q * (1 + Q) ^ (n - 1)) + δ * (Q ^ n * (Fintype.card X) ^ (n - 1))
        + 2 ^ (n - 1) * (M * (Snon ^ (n - 2) * Ψ)) := by
  classical
  set ξ0 : X → ℂ := fun x => Ξ i₀ (a i₀) x with hξ0
  set δa : X → ℂ := fun x => if a i₀ = x then 1 else 0 with hδa
  set wn : X → ℂ := fun x => if far x then 0 else ξ0 x with hwn
  set wf : X → ℂ := fun x => if far x then ξ0 x else 0 with hwf'
  have hwf : ∀ x, ‖wf x‖ = if far x then ‖Ξ i₀ (a i₀) x‖ else 0 := by
    intro x; simp only [hwf', hξ0]; split_ifs <;> simp
  -- Step 1: `u_{i₀} = δ + w_near + w_far`
  have hpt : ∀ b : Fin n → X, (∏ i, ekSZU Ξ a i (b i)) * A b
      = ((δa (b i₀) + wn (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b
        + (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ (fun i => ekSZU Ξ a i (b i)) (Finset.mem_univ i₀)]
    have h0 : ekSZU Ξ a i₀ (b i₀) = (δa (b i₀) + wn (b i₀)) + wf (b i₀) := by
      simp only [ekSZU, hδa, hwn, hwf', hξ0]
      split_ifs <;> ring
    rw [h0]; ring
  have hsplit : ∑ b : Fin n → X, (∏ i, ekSZU Ξ a i (b i)) * A b
      = ∑ b : Fin n → X, ((δa (b i₀) + wn (b i₀)) *
            ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b
        + ∑ b : Fin n → X, (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => hpt b
  -- Step 2: the `δ + near` part
  have hw1 : ∑ x, ‖δa x + wn x‖ ≤ 1 + Rn := by
    calc ∑ x, ‖δa x + wn x‖ ≤ ∑ x, (‖δa x‖ + ‖wn x‖) :=
          Finset.sum_le_sum fun x _ => norm_add_le _ _
      _ = ∑ x, ‖δa x‖ + ∑ x, ‖wn x‖ := Finset.sum_add_distrib
      _ ≤ 1 + Rn := by
          have h1 : ∑ x, ‖δa x‖ = 1 := by
            have : ∀ x, ‖δa x‖ = if a i₀ = x then (1 : ℝ) else 0 := by
              intro x; simp only [hδa]; split_ifs <;> simp
            simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          have h2 : ∑ x, ‖wn x‖ = ∑ x ∈ Finset.univ.filter (fun x => ¬ far x), ‖Ξ i₀ (a i₀) x‖ := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [hwn, hξ0]
            split_ifs <;> simp_all
          rw [h1, h2]; linarith
  have hP1 := ekSZ_UW_bound i₀ Ξ a A Win hM0 hδ hSξ0 hM htail hrow hwin (fun x => δa x + wn x) hw1
  -- the far weight: `‖w_far‖ ≤ ‖Ξ‖`, total at most `Q`
  have hwfQ : ∑ x, ‖wf x‖ ≤ Q := by
    calc ∑ x, ‖wf x‖ ≤ ∑ x, ‖Ξ i₀ (a i₀) x‖ := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [hwf x]; split_ifs <;> simp
      _ ≤ Q := hrow i₀ (a i₀)
  -- Step 3: window / tail
  have hWT : ∑ b : Fin n → X, (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b
      = ∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b else 0)
        + ∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have hP3 := ekSZ_tail_bound i₀ Ξ a A Win wf hδ htail hrow hwfQ
  -- Step 4: the first-difference expansion of the window part
  have hexp : ∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b else 0)
      = ∑ B ∈ (Finset.univ.erase i₀).powerset, ∑ b : Fin n → X,
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hwb : ∀ i, i ≠ i₀ → b i ∈ Win (b i₀)
    · simp only [eq_true hwb, ↓reduceIte]
      have hQ : wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)
          = wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀,
              ((Ξ i (a i) (b i) - Ξ i (a i) (b i₀)) + Ξ i (a i) (b i₀)) := by
        by_cases hfb : far (b i₀)
        · congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi
          have hna := hne (b i₀) hfb i hii (b i) (hwb i hii)
          simp only [ekSZU, hna, ↓reduceIte, zero_add, sub_add_cancel]
        · have : wf (b i₀) = 0 := by simp [hwf', hfb]
          rw [this]; simp
      rw [hQ, Finset.prod_add, Finset.mul_sum, Finset.sum_mul]
    · simp [hwb]
  -- Step 5: the bounds
  have hempty : ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ (∅ : Finset (Fin n)), (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ ∅, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ δ * (Q ^ n * (Fintype.card X) ^ (n - 1)) := by
    have hn1 : n - 1 + 1 = n := by have := i₀.pos; omega
    set c : X → ℂ := fun x => wf x * ∏ i ∈ Finset.univ.erase i₀, Ξ i (a i) x with hc
    have hcsum : ∑ x, ‖c x‖ ≤ Q ^ n := by
      have hent : ∀ i x, ‖Ξ i (a i) x‖ ≤ Q := fun i x =>
        (Finset.single_le_sum (f := fun y => ‖Ξ i (a i) y‖) (fun y _ => norm_nonneg _)
          (Finset.mem_univ x)).trans (hrow i (a i))
      calc ∑ x, ‖c x‖ ≤ ∑ x, ‖wf x‖ * Q ^ (n - 1) := by
            refine Finset.sum_le_sum fun x _ => ?_
            simp only [hc]
            rw [norm_mul, norm_prod]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            calc ∏ i ∈ Finset.univ.erase i₀, ‖Ξ i (a i) x‖ ≤ ∏ _i ∈ Finset.univ.erase i₀, Q :=
                  Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hent i x
              _ = Q ^ (n - 1) := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
                    Finset.card_univ, Fintype.card_fin]
        _ = (∑ x, ‖wf x‖) * Q ^ (n - 1) := (Finset.sum_mul _ _ _).symm
        _ ≤ Q * Q ^ (n - 1) := mul_le_mul_of_nonneg_right hwfQ (pow_nonneg hQ0 _)
        _ = Q ^ n := by rw [← pow_succ', hn1]
    have := ekSZ_fempty_bound i₀ A Win c hδ htail hsz hcsum
    simpa only [Finset.prod_empty, Finset.sdiff_empty, one_mul, hc] using this
  have hterms : ∀ B ∈ (Finset.univ.erase i₀).powerset.erase ∅,
      ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
        ≤ M * (Snon ^ (n - 2) * Ψ) := by
    intro B hB
    have hBS : B ⊆ Finset.univ.erase i₀ := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hB)
    have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hB)
    exact ekSZ_fB_bound i₀ Ξ a A Win far wf hwf hM0 hSnon0 hM hX hΔ hΨ B hBS hBne
  have hsumB : ‖∑ B ∈ (Finset.univ.erase i₀).powerset.erase ∅, ∑ b : Fin n → X,
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ 2 ^ (n - 1) * (M * (Snon ^ (n - 2) * Ψ)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hterms).trans ?_
    rw [nsmul_eq_mul]
    have hcard : (((Finset.univ.erase i₀).powerset.erase ∅).card : ℝ) ≤ 2 ^ (n - 1) := by
      have h1 : ((Finset.univ.erase i₀).powerset.erase ∅).card ≤ 2 ^ (n - 1) := by
        calc ((Finset.univ.erase i₀).powerset.erase ∅).card
            ≤ (Finset.univ.erase i₀).powerset.card := Finset.card_erase_le
          _ = 2 ^ (n - 1) := by
              rw [Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ i₀),
                Finset.card_univ, Fintype.card_fin]
      exact_mod_cast h1
    exact mul_le_mul_of_nonneg_right hcard
      (mul_nonneg hM0 (mul_nonneg (pow_nonneg hSnon0 _) hΨ0))
  -- Step 6: assemble
  have hP2 : ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, ekSZU Ξ a i (b i)) * A b else 0)‖
      ≤ δ * (Q ^ n * (Fintype.card X) ^ (n - 1)) + 2 ^ (n - 1) * (M * (Snon ^ (n - 2) * Ψ)) := by
    rw [hexp, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset (Finset.univ.erase i₀))]
    refine (norm_add_le _ _).trans ?_
    exact add_le_add hempty hsumB
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [hWT]
  refine le_trans (add_le_add hP1 ((norm_add_le _ _).trans (add_le_add hP2 hP3))) ?_
  linarith


end Core

/-! ### Part II: the lattice estimates -/

section Concrete

variable {d L : ℕ} [NeZero L]

/-- the `ℓ¹` ball of radius `N` has at most `(2N+1)^d` points. -/
private theorem ekSZ_card_ball (N : ℕ) (x : Zd d L) :
    (Finset.univ.filter (fun y : Zd d L => zdistD d L (x - y) ≤ N)).card ≤ (2 * N + 1) ^ d := by
  classical
  have h1 : (Finset.univ.filter (fun y : Zd d L => zdistD d L (x - y) ≤ N)).card
      ≤ (Finset.univ.filter (fun z : Zd d L => zdistD d L z ≤ N)).card := by
    refine Finset.card_le_card_of_injOn (fun y => x - y) ?_ ?_
    · intro y hy
      simpa using hy
    · intro y _ y' _ h
      simpa using h
  have h2 : Finset.univ.filter (fun z : Zd d L => zdistD d L z ≤ N)
      ⊆ Fintype.piFinset
        (fun _ : Fin d => Finset.univ.filter (fun u : ZMod L => zdist L u ≤ N)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset] at hz ⊢
    intro i
    have : zdist L (z i) ≤ zdistD d L z :=
      Finset.single_le_sum (f := fun i => zdist L (z i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  calc (Finset.univ.filter (fun y : Zd d L => zdistD d L (x - y) ≤ N)).card
      ≤ (Finset.univ.filter (fun z : Zd d L => zdistD d L z ≤ N)).card := h1
    _ ≤ (Fintype.piFinset
        (fun _ : Fin d => Finset.univ.filter (fun u : ZMod L => zdist L u ≤ N))).card :=
        Finset.card_le_card h2
    _ = ∏ _i : Fin d, (Finset.univ.filter (fun u : ZMod L => zdist L u ≤ N)).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (2 * N + 1) := Finset.prod_le_prod (fun i _ => card_zdist_le_le N)
    _ = (2 * N + 1) ^ d := by simp

/-- the window `{y : |x - y| < R}` has at most `(2R+1)^d` points. -/
private theorem ekSZ_card_win (x : Zd d L) {R : ℝ} (hR : 0 ≤ R) :
    (((Finset.univ.filter (fun y : Zd d L => (zdistD d L (x - y) : ℝ) < R)).card : ℕ) : ℝ)
      ≤ (2 * R + 1) ^ d := by
  classical
  have hsub : Finset.univ.filter (fun y : Zd d L => (zdistD d L (x - y) : ℝ) < R)
      ⊆ Finset.univ.filter (fun y : Zd d L => zdistD d L (x - y) ≤ ⌊R⌋₊) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact Nat.le_floor hy.le
  have h1 := (Finset.card_le_card hsub).trans (ekSZ_card_ball (d := d) (L := L) ⌊R⌋₊ x)
  calc (((Finset.univ.filter (fun y : Zd d L => (zdistD d L (x - y) : ℝ) < R)).card : ℕ) : ℝ)
      ≤ (((2 * ⌊R⌋₊ + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (2 * (⌊R⌋₊ : ℝ) + 1) ^ d := by push_cast; ring
    _ ≤ (2 * R + 1) ^ d := by
        gcongr
        exact Nat.floor_le hR

/-- **The first difference of `Ξ` from `(prop:BD1)`** (`(eq:Xibb)`, second bound): for `|y - b|` at most
`(|a - b| - 1)/2`,
`|Ξ_{a y} - Ξ_{a b}| ≤ (t-s) C₆ (g²+|1-t|)⁻¹ |y - b| |a - b|^{-(d-1)}`.  The input `h6` is the
bound of `Prop6Diff1` at `c = 1/2` for this `μ`; `S^{(B)}` has nearest-neighbour support, so
`|b - c| + 1 ≥ |a - b|` for the `c` in the support of row `a`. -/
private theorem ekSZ_dXi_le (hL : 3 ≤ L) {g : ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {C6 : ℝ} (hC6 : 0 ≤ C6)
    (h6 : ∀ a r : Zd d L, (zdistD d L r : ℝ) ≤ 1 / 2 * (zdistD d L a : ℝ) →
      ‖Theta d L g ((t : ℂ) * μ) 0 (a + r) - Theta d L g ((t : ℂ) * μ) 0 a‖
        ≤ C6 * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹)
    (a b y : Zd d L) (hay : 2 * (zdistD d L (y - b) : ℝ) + 1 ≤ (zdistD d L (a - b) : ℝ)) :
    ‖XiKer d L g μ s t a y - XiKer d L g μ s t a b‖
      ≤ (t - s) * (C6 * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L (y - b) : ℝ)
          * ((zdistD d L (a - b) : ℝ) ^ (d - 1))⁻¹) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hξ : ‖(t : ℂ) * μ‖ < 1 := norm_t_mul_lt_one ht0 ht hμ
  have hΘ : ∀ c z : Zd d L,
      Theta d L g ((t : ℂ) * μ) c z = Theta d L g ((t : ℂ) * μ) 0 (z - c) := by
    intro c z
    have h := Theta_apply_add_right_of_three_le (g := g) hL hξ 0 (z - c) c
    simpa using h
  have hdiff : XiKer d L g μ s t a y - XiKer d L g μ s t a b
      = (((t : ℂ) - s) * μ) * ∑ c : Zd d L, SB d L g a c *
          (Theta d L g ((t : ℂ) * μ) c y - Theta d L g ((t : ℂ) * μ) c b) := by
    simp only [XiKer, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hdiff, norm_mul]
  have hcoef : ‖((t : ℂ) - s) * μ‖ = t - s := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hcoef]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  set Bnd : ℝ := C6 * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L (y - b) : ℝ)
    * ((zdistD d L (a - b) : ℝ) ^ (d - 1))⁻¹ with hBnd
  have hterm : ∀ c : Zd d L, ‖SB d L g a c * (Theta d L g ((t : ℂ) * μ) c y
      - Theta d L g ((t : ℂ) * μ) c b)‖ ≤ ‖SB d L g a c‖ * Bnd := by
    intro c
    rw [norm_mul]
    by_cases hc : zdistD d L (a - c) ≤ 1
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [hΘ c y, hΘ c b]
      have htri : zdistD d L (a - b) ≤ zdistD d L (a - c) + zdistD d L (b - c) := by
        have h := zdistD_add_le d L (a - c) (c - b)
        rw [sub_add_sub_cancel, show c - b = -(b - c) by abel, zdistD_neg] at h
        exact h
      have htri' : (zdistD d L (a - b) : ℝ) ≤ 1 + (zdistD d L (b - c) : ℝ) := by
        have : zdistD d L (a - b) ≤ 1 + zdistD d L (b - c) := by omega
        exact_mod_cast this
      have hr : (zdistD d L (y - b) : ℝ) ≤ 1 / 2 * (zdistD d L (b - c) : ℝ) := by linarith
      have h6c := h6 (b - c) (y - b) hr
      have e : (b - c) + (y - b) = y - c := by abel
      rw [e] at h6c
      refine h6c.trans ?_
      have hab1 : (1 : ℝ) ≤ (zdistD d L (a - b) : ℝ) := by
        have : (0 : ℝ) ≤ (zdistD d L (y - b) : ℝ) := Nat.cast_nonneg _
        linarith
      have hpow : (zdistD d L (a - b) : ℝ) ^ (d - 1) ≤ (((zdistD d L (b - c) : ℝ) + 1)) ^ (d - 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      have hinv : ((((zdistD d L (b - c) : ℝ) + 1)) ^ (d - 1))⁻¹
          ≤ ((zdistD d L (a - b) : ℝ) ^ (d - 1))⁻¹ :=
        inv_anti₀ (by positivity) hpow
      have hpre : 0 ≤ C6 * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L (y - b) : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hinv hpre
    · rw [SB_apply_eq_zero_of_one_lt (by omega)]
      simp
  calc ‖∑ c : Zd d L, SB d L g a c * (Theta d L g ((t : ℂ) * μ) c y
        - Theta d L g ((t : ℂ) * μ) c b)‖
      ≤ ∑ c : Zd d L, ‖SB d L g a c * (Theta d L g ((t : ℂ) * μ) c y
        - Theta d L g ((t : ℂ) * μ) c b)‖ := norm_sum_le _ _
    _ ≤ ∑ c : Zd d L, ‖SB d L g a c‖ * Bnd := Finset.sum_le_sum fun c _ => hterm c
    _ = Bnd := by rw [← Finset.sum_mul, sum_norm_SB_row (d := d) (L := L) (g := g) hL a, one_mul]

/-- window count against a polynomial gain: `N (c R^{-(k+1)}) ≤ 3^{k+3} c R²` for `N ≤ (2R+1)^{k+3}`. -/
private theorem ekSZ_ar_win {R c N : ℝ} {k : ℕ} (hR : 1 ≤ R) (hc : 0 ≤ c)
    (hN : N ≤ (2 * R + 1) ^ (k + 3)) :
    N * (c * (R ^ (k + 1))⁻¹) ≤ 3 ^ (k + 3) * (c * R ^ 2) := by
  have hR0 : 0 < R := by linarith
  have hpow : (2 * R + 1) ^ (k + 3) ≤ (3 * R) ^ (k + 3) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hRk : 0 < R ^ (k + 1) := by positivity
  have h0 : 0 ≤ c * (R ^ (k + 1))⁻¹ := by positivity
  calc N * (c * (R ^ (k + 1))⁻¹) ≤ (3 * R) ^ (k + 3) * (c * (R ^ (k + 1))⁻¹) :=
        mul_le_mul_of_nonneg_right (hN.trans hpow) h0
    _ = 3 ^ (k + 3) * (c * R ^ 2) := by
        field_simp
        ring

/-- the arithmetic of the lattice sum of the distinguished index. -/
private theorem ekSZ_ar_psi {k : ℕ} {R Rn κX r ρ CD C6 lat lg : ℝ} (hR : 1 ≤ R) (hRn : R ≤ Rn)
    (hκ0 : 0 ≤ κX) (hκ : κX * R ^ 2 ≤ ρ ^ 2 * r) (hCD : 0 ≤ CD) (hC6 : 0 ≤ C6) (hlat : 0 ≤ lat)
    (hlg : 0 ≤ lg) :
    CD * C6 * κX ^ 2 * ((2 * R + 1) ^ (k + 3) * R) * (lat * lg / Rn ^ k)
      ≤ 3 ^ (k + 3) * C6 * CD * lat * lg * ρ ^ 4 * r ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hRn0 : 0 < Rn := lt_of_lt_of_le hR0 hRn
  have hRk : 0 < R ^ k := by positivity
  have hRnk : R ^ k ≤ Rn ^ k := pow_le_pow_left₀ hR0.le hRn _
  have hpow : (2 * R + 1) ^ (k + 3) ≤ (3 * R) ^ (k + 3) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hinv : (Rn ^ k)⁻¹ ≤ (R ^ k)⁻¹ := inv_anti₀ hRk hRnk
  have hlatlg : 0 ≤ lat * lg := mul_nonneg hlat hlg
  have h1 : lat * lg / Rn ^ k ≤ lat * lg * (R ^ k)⁻¹ := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv hlatlg
  have hκsq : (κX * R ^ 2) ^ 2 ≤ (ρ ^ 2 * r) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hκ 2
  have hcoef : 0 ≤ CD * C6 * κX ^ 2 := by positivity
  calc CD * C6 * κX ^ 2 * ((2 * R + 1) ^ (k + 3) * R) * (lat * lg / Rn ^ k)
      ≤ CD * C6 * κX ^ 2 * ((3 * R) ^ (k + 3) * R) * (lat * lg * (R ^ k)⁻¹) := by
        have h2 : (2 * R + 1) ^ (k + 3) * R ≤ (3 * R) ^ (k + 3) * R :=
          mul_le_mul_of_nonneg_right hpow hR0.le
        have hc3 : 0 ≤ lat * lg / Rn ^ k := by positivity
        have hc4 : 0 ≤ CD * C6 * κX ^ 2 * ((3 * R) ^ (k + 3) * R) := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hcoef) h1 hc3 hc4
    _ = 3 ^ (k + 3) * C6 * CD * lat * lg * ((κX * R ^ 2) ^ 2) := by
        field_simp
        ring
    _ ≤ 3 ^ (k + 3) * C6 * CD * lat * lg * ((ρ ^ 2 * r) ^ 2) :=
        mul_le_mul_of_nonneg_left hκsq (by positivity)
    _ = 3 ^ (k + 3) * C6 * CD * lat * lg * ρ ^ 4 * r ^ 2 := by ring

/-- **`(eq:latticesum_d3)` over the far set** `{x : R₂ < |a₁ - x|, R₂ < |a₂ - x|}`, `R₂ ≥ 1`, with the
cutoff `⌊R₂⌋`. -/
private theorem ekSZ_lattice (k : ℕ) (hL : 3 ≤ L) {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {R₂ : ℝ}
    (hR₂ : 1 ≤ R₂) (a₁ a₂ : Zd (k + 3) L) :
    ∑ x ∈ Finset.univ.filter (fun x : Zd (k + 3) L =>
        R₂ < (zdistD (k + 3) L (a₁ - x) : ℝ) ∧ R₂ < (zdistD (k + 3) L (a₂ - x) : ℝ)),
      Real.exp (-(c * (zdistD (k + 3) L (a₁ - x) : ℝ)) / ℓ)
        / (((zdistD (k + 3) L (a₁ - x) : ℝ) ^ (k + 1)) * ((zdistD (k + 3) L (a₂ - x) : ℝ) ^ (k + 2)))
      ≤ latC k * Real.log L / (⌊R₂⌋₊ : ℝ) ^ k := by
  classical
  have hRn : 1 ≤ ⌊R₂⌋₊ := Nat.le_floor (by simpa using hR₂)
  have h := latticesum_d3 (L := L) k hc hℓ hRn hL a₁ a₂
  refine le_trans ?_ h
  have hsub : Finset.univ.filter (fun x : Zd (k + 3) L =>
        R₂ < (zdistD (k + 3) L (a₁ - x) : ℝ) ∧ R₂ < (zdistD (k + 3) L (a₂ - x) : ℝ))
      ⊆ Finset.univ.filter (fun x : Zd (k + 3) L =>
        ⌊R₂⌋₊ < zdistD (k + 3) L (a₁ - x) ∧ ⌊R₂⌋₊ < zdistD (k + 3) L (a₂ - x)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hfl : (⌊R₂⌋₊ : ℝ) ≤ R₂ := Nat.floor_le (by linarith)
    constructor
    · exact_mod_cast lt_of_le_of_lt hfl hx.1
    · exact_mod_cast lt_of_le_of_lt hfl hx.2
  have hnn : ∀ x ∈ Finset.univ.filter (fun x : Zd (k + 3) L =>
        ⌊R₂⌋₊ < zdistD (k + 3) L (a₁ - x) ∧ ⌊R₂⌋₊ < zdistD (k + 3) L (a₂ - x)),
      x ∉ Finset.univ.filter (fun x : Zd (k + 3) L =>
        R₂ < (zdistD (k + 3) L (a₁ - x) : ℝ) ∧ R₂ < (zdistD (k + 3) L (a₂ - x) : ℝ)) →
      0 ≤ Real.exp (-(c * (zdistD (k + 3) L (a₁ - x) : ℝ)) / ℓ)
        / (((zdistD (k + 3) L (a₁ - x) : ℝ) ^ (k + 1)) * ((zdistD (k + 3) L (a₂ - x) : ℝ) ^ (k + 2))) := by
    intro x _ _
    positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [neg_div]

/-- **The deterministic bound of `(sumAzero) ⟹ (sum_res_2)`, constants explicit.**  Inputs: the ball
sums and the decay of `Ξ` (`hball`, `hdec`: `EKXiBall`, `EKXiDecay`, i.e. pin 5) and the first
difference of `Θ` (`h6`: pin 6 at `c = 1/2`); the output is the sum of the five terms of `ekSZ_core`
with `M = ‖A‖`, `δ = W^{-D}`, `Q = (t-s)/(1-t)`, `Sξ = C_B ρ² r`, `Rn = n C_B ρ⁴ r`,
`Snon = 3^d (C_D + C₆) ρ² r`, `Ψ = 3^d C₆ C_D C_lat log L ρ⁴ r²`, `ρ = W^ε`. -/
private theorem ekSZ_concrete (k : ℕ) (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) {n : ℕ} (hn : 2 ≤ n) (μ : Fin n → ℂ) (hμ : ∀ i, ‖μ i‖ = 1)
    {CB CD c C6 : ℝ} (hCB : 0 ≤ CB) (hCD : 0 ≤ CD) (hc : 0 < c) (hC6 : 0 ≤ C6)
    (hball : ∀ i, ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
        ∀ (a ctr : Zd (k + 3) L) (D : Finset (Zd (k + 3) L)),
          (∀ b ∈ D, (zdistD (k + 3) L (ctr - b) : ℝ) ≤ R) →
          ∑ b ∈ D, ‖XiKer (k + 3) L g (μ i) s t a b‖
            ≤ CB * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)))
    (hdec : ∀ i, ∀ x y : Zd (k + 3) L, ‖XiKer (k + 3) L g (μ i) s t x y‖
          ≤ CD * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD (k + 3) L (x - y) : ℝ) + 1) ^ (k + 1))⁻¹
            * Real.exp (-(c * (zdistD (k + 3) L (x - y) : ℝ)) / ellT L g t))
    (h6 : ∀ i, ∀ a r : Zd (k + 3) L, (zdistD (k + 3) L r : ℝ) ≤ 1 / 2 * (zdistD (k + 3) L a : ℝ) →
      ‖Theta (k + 3) L g ((t : ℂ) * μ i) 0 (a + r) - Theta (k + 3) L g ((t : ℂ) * μ i) 0 a‖
        ≤ C6 * (g ^ 2 + |1 - t|)⁻¹ * (zdistD (k + 3) L r : ℝ)
          * (((zdistD (k + 3) L a : ℝ) + 1) ^ (k + 2))⁻¹)
    {W ε D ρ r Q Sξ Rn Snon Ψ : ℝ} (hρdef : ρ = W ^ ε) (hρ : 4 ≤ ρ)
    (hr : r = (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) (hQ : Q = (t - s) / (1 - t))
    (hSξ : Sξ = CB * ρ ^ 2 * r) (hRn : Rn = n * (CB * (ρ ^ 2) ^ 2 * r))
    (hSnon : Snon = 3 ^ (k + 3) * (CD + C6) * ρ ^ 2 * r)
    (hΨdef : Ψ = 3 ^ (k + 3) * C6 * CD * latC k * Real.log L * ρ ^ 4 * r ^ 2)
    (hWD : 0 ≤ W ^ (-D)) (A : (Fin n → Zd (k + 3) L) → ℂ) (hA : EKFastDecay g s W ε D A)
    (hz : EKSumZero A) (a : Fin n → Zd (k + 3) L) :
    ‖∑ b : Fin n → Zd (k + 3) L, (∏ i, uKer (k + 3) L g (μ i) s t (a i) (b i)) * A b‖ ≤
      (‖A‖ * ((1 + Rn) * (1 + Sξ) ^ (n - 1)) + W ^ (-D) * ((1 + Rn) * (1 + Q) ^ (n - 1)))
        + W ^ (-D) * (Q * (1 + Q) ^ (n - 1)) + W ^ (-D) * (Q ^ n * ((L : ℝ) ^ (k + 3)) ^ (n - 1))
        + 2 ^ (n - 1) * (‖A‖ * (Snon ^ (n - 2) * Ψ)) := by
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have ht0 : 0 ≤ t := hs.trans hst
  have hu : 0 < 1 - t := by linarith
  have hv : 0 < 1 - s := by linarith
  have hgt0 : 0 < g ^ 2 + |1 - t| := by positivity
  have hρ0 : 0 < ρ := by linarith
  have hℓs1 : 1 ≤ ellT L g s := one_le_ellT hL1
  have hℓt0 : 0 < ellT L g t := ellT_pos hL1
  have hr1 : 1 ≤ r := by
    rw [hr, abs_of_pos hu, abs_of_pos hv, le_div_iff₀ (by positivity)]
    linarith
  have hr0 : 0 < r := by linarith
  -- the radii
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ρ * ellT L g s := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hRdef]; nlinarith
  have hR0 : 0 < R := by linarith
  have hRρ : 4 * R ≤ ρ * R := by nlinarith
  have hR₂1 : 1 ≤ ρ * R := by nlinarith
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ (by linarith)
  -- `κX = (1-s)/(g²+|1-t|)` and `κX R² ≤ ρ² r`
  obtain ⟨κX, hκX⟩ : ∃ κX : ℝ, κX = (1 - s) * (g ^ 2 + |1 - t|)⁻¹ := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κX := by rw [hκX]; positivity
  have hκR : κX * R ^ 2 ≤ ρ ^ 2 * r := by
    have h := one_sub_mul_ellT_sq_le (L := L) (g := g) (s := s) hg.le (by linarith)
    rw [abs_of_pos hv] at h
    rw [hκX, hRdef, hr, abs_of_pos hv]
    calc (1 - s) * (g ^ 2 + |1 - t|)⁻¹ * (ρ * ellT L g s) ^ 2
        = ρ ^ 2 * ((1 - s) * ellT L g s ^ 2) * (g ^ 2 + |1 - t|)⁻¹ := by ring
      _ ≤ ρ ^ 2 * (g ^ 2 + (1 - s)) * (g ^ 2 + |1 - t|)⁻¹ := by gcongr
      _ = ρ ^ 2 * ((g ^ 2 + (1 - s)) / (g ^ 2 + |1 - t|)) := by rw [div_eq_mul_inv]; ring
  -- the objects of the abstract core
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : Fin n → Zd (k + 3) L → Zd (k + 3) L → ℂ,
      Ξ = fun i x y => XiKer (k + 3) L g (μ i) s t x y := ⟨_, rfl⟩
  have hΞ' : ∀ i x y, Ξ i x y = XiKer (k + 3) L g (μ i) s t x y := by
    intro i x y; simp [hΞ]
  obtain ⟨Win, hWin⟩ : ∃ Win : Zd (k + 3) L → Finset (Zd (k + 3) L),
      Win = fun x => Finset.univ.filter (fun y => (zdistD (k + 3) L (x - y) : ℝ) < R) := ⟨_, rfl⟩
  have hmemWin : ∀ x y, y ∈ Win x ↔ (zdistD (k + 3) L (x - y) : ℝ) < R := by
    intro x y; simp [hWin]
  obtain ⟨far, hfar⟩ : ∃ far : Zd (k + 3) L → Prop,
      far = fun x => ∀ j : Fin n, ρ * R < (zdistD (k + 3) L (a j - x) : ℝ) := ⟨_, rfl⟩
  have hfar' : ∀ x, far x ↔ ∀ j : Fin n, ρ * R < (zdistD (k + 3) L (a j - x) : ℝ) := by
    intro x; simp [hfar]
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  have hu_eq : ∀ b : Fin n → Zd (k + 3) L,
      ∏ i, uKer (k + 3) L g (μ i) s t (a i) (b i) = ∏ i, ekSZU Ξ a i (b i) := by
    intro b
    refine Finset.prod_congr rfl fun i _ => ?_
    have hξi : ‖(t : ℂ) * μ i‖ < 1 := norm_t_mul_lt_one ht0 ht (hμ i)
    rw [uKer_eq_one_add_XiKer hL hξi, Matrix.add_apply, Matrix.one_apply]
    simp only [ekSZU, hΞ']
  -- nonnegativity
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact div_nonneg (by linarith) hu.le
  have hSξ0 : 0 ≤ Sξ := by rw [hSξ]; positivity
  have hSnon0 : 0 ≤ Snon := by rw [hSnon]; positivity
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlat0 : 0 ≤ latC k := (latC_pos k).le
  have hΨ0 : 0 ≤ Ψ := by rw [hΨdef]; positivity
  -- `(deccA0)`, `(sumAzero)`
  have htail : ∀ b : Fin n → Zd (k + 3) L, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ W ^ (-D) := by
    intro b hb
    push Not at hb
    obtain ⟨i, hi, hbi⟩ := hb
    rw [hmemWin, not_lt] at hbi
    exact hA b ⟨i₀, i, by rw [← hρdef, ← hRdef]; exact hbi⟩
  have hsz : ∀ x, ∑ b ∈ Finset.univ.filter (fun b : Fin n → Zd (k + 3) L => b i₀ = x), A b = 0 :=
    fun x => hz i₀ rfl x
  -- the rows of `Ξ`
  have hrow : ∀ i x, ∑ y, ‖Ξ i x y‖ ≤ Q := by
    intro i x
    have h1 := sum_norm_row_le (XiKer (k + 3) L g (μ i) s t) x
    rw [hQ]
    simp only [hΞ']
    exact h1.trans (norm_Xi_le hL hs hst ht (hμ i))
  -- the window sums of `Ξ` (pin 5, ball sums)
  have hwin : ∀ i, i ≠ i₀ → ∀ x, ∑ y ∈ Win x, ‖Ξ i (a i) y‖ ≤ Sξ := by
    intro i _ x
    rw [hSξ, hr]
    simp only [hΞ']
    refine hball i ρ (by linarith) R hR1 (le_of_eq hRdef) (a i) x (Win x) ?_
    intro y hy
    exact ((hmemWin x y).mp hy).le
  -- the near set
  have hfar_not : ∀ x, ¬ far x ↔ ∃ j, (zdistD (k + 3) L (a j - x) : ℝ) ≤ ρ * R := by
    intro x; rw [hfar']; simp only [not_forall, not_lt]
  have hnear : ∑ x ∈ Finset.univ.filter (fun x => ¬ far x), ‖Ξ i₀ (a i₀) x‖ ≤ Rn := by
    have hballj : ∀ j : Fin n, ∑ x ∈ Finset.univ.filter
        (fun x : Zd (k + 3) L => (zdistD (k + 3) L (a j - x) : ℝ) ≤ ρ * R), ‖Ξ i₀ (a i₀) x‖
        ≤ CB * (ρ ^ 2) ^ 2 * r := by
      intro j
      rw [hr]
      simp only [hΞ']
      refine hball i₀ (ρ ^ 2) hρ2 (ρ * R) hR₂1 (le_of_eq (by rw [hRdef]; ring))
        (a i₀) (a j) _ ?_
      intro x hx
      simpa using hx
    calc ∑ x ∈ Finset.univ.filter (fun x => ¬ far x), ‖Ξ i₀ (a i₀) x‖
        = ∑ x : Zd (k + 3) L, (if ¬ far x then ‖Ξ i₀ (a i₀) x‖ else 0) := Finset.sum_filter _ _
      _ ≤ ∑ x : Zd (k + 3) L, ∑ j : Fin n,
            (if (zdistD (k + 3) L (a j - x) : ℝ) ≤ ρ * R then ‖Ξ i₀ (a i₀) x‖ else 0) := by
          refine Finset.sum_le_sum fun x _ => ?_
          by_cases hx : far x
          · simp only [hx, not_true_eq_false, ↓reduceIte]
            exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp
          · obtain ⟨j₀, hj₀⟩ := (hfar_not x).mp hx
            simp only [hx, not_false_eq_true, ↓reduceIte]
            have := Finset.single_le_sum
              (f := fun j => if (zdistD (k + 3) L (a j - x) : ℝ) ≤ ρ * R then ‖Ξ i₀ (a i₀) x‖ else 0)
              (fun j _ => by split_ifs <;> simp) (Finset.mem_univ j₀)
            simpa [hj₀] using this
      _ = ∑ j : Fin n, ∑ x : Zd (k + 3) L,
            (if (zdistD (k + 3) L (a j - x) : ℝ) ≤ ρ * R then ‖Ξ i₀ (a i₀) x‖ else 0) :=
          Finset.sum_comm
      _ = ∑ j : Fin n, ∑ x ∈ Finset.univ.filter
            (fun x : Zd (k + 3) L => (zdistD (k + 3) L (a j - x) : ℝ) ≤ ρ * R), ‖Ξ i₀ (a i₀) x‖ := by
          simp only [Finset.sum_filter]
      _ ≤ ∑ _j : Fin n, CB * (ρ ^ 2) ^ 2 * r := Finset.sum_le_sum fun j _ => hballj j
      _ = Rn := by rw [hRn]; simp
  -- far points are not equal to any `a_i` inside the window
  have hne : ∀ x, far x → ∀ i, i ≠ i₀ → ∀ y ∈ Win x, a i ≠ y := by
    intro x hfx i _ y hy hay
    have hy' := (hmemWin x y).mp hy
    have h1 := (hfar' x).mp hfx i
    have h2 : zdistD (k + 3) L (x - y) = zdistD (k + 3) L (a i - x) := by
      rw [← hay, show x - a i = -(a i - x) by abel, zdistD_neg]
    rw [h2] at hy'
    linarith
  -- pointwise decay of `Ξ` (pin 5)
  have hEpt : ∀ i x, ‖Ξ i (a i) x‖ ≤ CD * κX
      * (((zdistD (k + 3) L (a i - x) : ℝ) + 1) ^ (k + 1))⁻¹
      * Real.exp (-(c * (zdistD (k + 3) L (a i - x) : ℝ)) / ellT L g t) := by
    intro i x
    rw [hΞ']
    refine (hdec i (a i) x).trans (le_of_eq ?_)
    rw [hκX]; ring
  have hexp1 : ∀ i x, Real.exp (-(c * (zdistD (k + 3) L (a i - x) : ℝ)) / ellT L g t) ≤ 1 := by
    intro i x
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * (zdistD (k + 3) L (a i - x) : ℝ) := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hℓt0.le
  have hEpt2 : ∀ i x, ρ * R < (zdistD (k + 3) L (a i - x) : ℝ) →
      ‖Ξ i (a i) x‖ ≤ CD * κX * (R ^ (k + 1))⁻¹ := by
    intro i x hZ
    have hpow : (((zdistD (k + 3) L (a i - x) : ℝ) + 1) ^ (k + 1))⁻¹ ≤ (R ^ (k + 1))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hR0.le (by linarith) _)
    have h0 : 0 ≤ CD * κX := mul_nonneg hCD hκ0
    calc ‖Ξ i (a i) x‖ ≤ CD * κX * (((zdistD (k + 3) L (a i - x) : ℝ) + 1) ^ (k + 1))⁻¹
          * Real.exp (-(c * (zdistD (k + 3) L (a i - x) : ℝ)) / ellT L g t) := hEpt i x
      _ ≤ CD * κX * (R ^ (k + 1))⁻¹ * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hpow h0) (hexp1 i x) (Real.exp_pos _).le ?_
          positivity
      _ = CD * κX * (R ^ (k + 1))⁻¹ := mul_one _
  -- the first difference (pin 6)
  have hDpt : ∀ i, ∀ x, far x → ∀ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖
      ≤ C6 * κX * R * (((zdistD (k + 3) L (a i - x) : ℝ) ^ (k + 2))⁻¹) := by
    intro i x hfx y hy
    have hy' := (hmemWin x y).mp hy
    have hz : ρ * R < (zdistD (k + 3) L (a i - x) : ℝ) := (hfar' x).mp hfx i
    have hyx : zdistD (k + 3) L (y - x) = zdistD (k + 3) L (x - y) := by
      rw [← zdistD_neg, neg_sub]
    have hyx' : (zdistD (k + 3) L (y - x) : ℝ) = (zdistD (k + 3) L (x - y) : ℝ) := by rw [hyx]
    have h2R : 2 * (zdistD (k + 3) L (y - x) : ℝ) + 1 ≤ (zdistD (k + 3) L (a i - x) : ℝ) := by
      rw [hyx']; linarith
    have hdx := ekSZ_dXi_le hL (hμ i) hs hst ht hC6 (h6 i) (a i) x y h2R
    simp only [← hΞ'] at hdx
    refine hdx.trans ?_
    have hzR : (zdistD (k + 3) L (y - x) : ℝ) ≤ R := by rw [hyx']; exact hy'.le
    have hZR : R ≤ (zdistD (k + 3) L (a i - x) : ℝ) := by linarith
    have hts : t - s ≤ 1 - s := by linarith
    have hinv : (((zdistD (k + 3) L (a i - x) : ℝ)) ^ (k + 3 - 1))⁻¹
        = (((zdistD (k + 3) L (a i - x) : ℝ)) ^ (k + 2))⁻¹ := by
      congr 2
    rw [hinv]
    have hz0 : 0 ≤ (zdistD (k + 3) L (y - x) : ℝ) := Nat.cast_nonneg _
    have hpre : 0 ≤ C6 * (g ^ 2 + |1 - t|)⁻¹ := by positivity
    calc (t - s) * (C6 * (g ^ 2 + |1 - t|)⁻¹ * (zdistD (k + 3) L (y - x) : ℝ)
            * (((zdistD (k + 3) L (a i - x) : ℝ)) ^ (k + 2))⁻¹)
        ≤ (1 - s) * (C6 * (g ^ 2 + |1 - t|)⁻¹ * R
            * (((zdistD (k + 3) L (a i - x) : ℝ)) ^ (k + 2))⁻¹) := by
          refine mul_le_mul hts ?_ (by positivity) hv.le
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hzR hpre
      _ = C6 * κX * R * (((zdistD (k + 3) L (a i - x) : ℝ) ^ (k + 2))⁻¹) := by
          rw [hκX]; ring
  -- the window count
  have hcard : ∀ x, (((Win x).card : ℕ) : ℝ) ≤ (2 * R + 1) ^ (k + 3) := by
    intro x
    have := ekSZ_card_win (d := k + 3) (L := L) x hR0.le
    simpa [hWin] using this
  -- the constants `Snon`
  have hSnon_ge : ∀ c' : ℝ, 0 ≤ c' → c' ≤ CD + C6 → 3 ^ (k + 3) * (c' * κX * R ^ 2) ≤ Snon := by
    intro c' hc' hc'le
    rw [hSnon]
    calc 3 ^ (k + 3) * (c' * κX * R ^ 2) = 3 ^ (k + 3) * c' * (κX * R ^ 2) := by ring
      _ ≤ 3 ^ (k + 3) * c' * (ρ ^ 2 * r) := mul_le_mul_of_nonneg_left hκR (by positivity)
      _ ≤ 3 ^ (k + 3) * (CD + C6) * (ρ ^ 2 * r) := by gcongr
      _ = 3 ^ (k + 3) * (CD + C6) * ρ ^ 2 * r := by ring
  have hX : ∀ x, far x → ∀ i, i ≠ i₀ → ((Win x).card : ℝ) * ‖Ξ i (a i) x‖ ≤ Snon := by
    intro x hfx i _
    have hz : ρ * R < (zdistD (k + 3) L (a i - x) : ℝ) := (hfar' x).mp hfx i
    calc ((Win x).card : ℝ) * ‖Ξ i (a i) x‖ ≤ ((Win x).card : ℝ) * (CD * κX * (R ^ (k + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left (hEpt2 i x hz) (Nat.cast_nonneg _)
      _ ≤ 3 ^ (k + 3) * (CD * κX * R ^ 2) :=
          ekSZ_ar_win hR1 (mul_nonneg hCD hκ0) (hcard x)
      _ ≤ Snon := hSnon_ge CD hCD (by linarith)
  have hΔ : ∀ x, far x → ∀ i, i ≠ i₀ → ∑ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖ ≤ Snon := by
    intro x hfx i _
    have hz : ρ * R < (zdistD (k + 3) L (a i - x) : ℝ) := (hfar' x).mp hfx i
    have hZR : R ≤ (zdistD (k + 3) L (a i - x) : ℝ) := by linarith
    have hpt : ∀ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖ ≤ C6 * κX * (R ^ (k + 1))⁻¹ := by
      intro y hy
      refine (hDpt i x hfx y hy).trans ?_
      have hinv : (((zdistD (k + 3) L (a i - x) : ℝ)) ^ (k + 2))⁻¹ ≤ (R ^ (k + 2))⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hR0.le hZR _)
      have h0 : 0 ≤ C6 * κX * R := by positivity
      calc C6 * κX * R * (((zdistD (k + 3) L (a i - x) : ℝ)) ^ (k + 2))⁻¹
          ≤ C6 * κX * R * (R ^ (k + 2))⁻¹ := mul_le_mul_of_nonneg_left hinv h0
        _ = C6 * κX * (R ^ (k + 1))⁻¹ := by field_simp; ring
    calc ∑ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖ ≤ ∑ _y ∈ Win x, C6 * κX * (R ^ (k + 1))⁻¹ :=
          Finset.sum_le_sum hpt
      _ = ((Win x).card : ℝ) * (C6 * κX * (R ^ (k + 1))⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 ^ (k + 3) * (C6 * κX * R ^ 2) := ekSZ_ar_win hR1 (by positivity) (hcard x)
      _ ≤ Snon := hSnon_ge C6 hC6 (by linarith)
  -- the lattice sum of the distinguished pair `(i₀, j)`
  have hΨ' : ∀ j, j ≠ i₀ → ∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
      ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ ≤ Ψ := by
    intro j hj
    set T : ℝ := CD * C6 * κX ^ 2 * ((2 * R + 1) ^ (k + 3) * R) with hT
    set G : Zd (k + 3) L → ℝ := fun x =>
      Real.exp (-(c * (zdistD (k + 3) L (a i₀ - x) : ℝ)) / ellT L g t)
        / (((zdistD (k + 3) L (a i₀ - x) : ℝ) ^ (k + 1))
          * ((zdistD (k + 3) L (a j - x) : ℝ) ^ (k + 2))) with hG
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hpt : ∀ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
        ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ ≤ T * G x := by
      intro x hx
      have hfx : far x := (Finset.mem_filter.mp hx).2
      have hz0 : ρ * R < (zdistD (k + 3) L (a i₀ - x) : ℝ) := (hfar' x).mp hfx i₀
      have hzj : ρ * R < (zdistD (k + 3) L (a j - x) : ℝ) := (hfar' x).mp hfx j
      have hz0pos : 0 < (zdistD (k + 3) L (a i₀ - x) : ℝ) := by linarith
      have hzjpos : 0 < (zdistD (k + 3) L (a j - x) : ℝ) := by linarith
      have h1 : ‖Ξ i₀ (a i₀) x‖ ≤ CD * κX *
          (Real.exp (-(c * (zdistD (k + 3) L (a i₀ - x) : ℝ)) / ellT L g t)
            / (zdistD (k + 3) L (a i₀ - x) : ℝ) ^ (k + 1)) := by
        refine (hEpt i₀ x).trans ?_
        have hinv : (((zdistD (k + 3) L (a i₀ - x) : ℝ) + 1) ^ (k + 1))⁻¹
            ≤ ((zdistD (k + 3) L (a i₀ - x) : ℝ) ^ (k + 1))⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hz0pos.le (by linarith) _)
        calc CD * κX * (((zdistD (k + 3) L (a i₀ - x) : ℝ) + 1) ^ (k + 1))⁻¹
              * Real.exp (-(c * (zdistD (k + 3) L (a i₀ - x) : ℝ)) / ellT L g t)
            ≤ CD * κX * ((zdistD (k + 3) L (a i₀ - x) : ℝ) ^ (k + 1))⁻¹
              * Real.exp (-(c * (zdistD (k + 3) L (a i₀ - x) : ℝ)) / ellT L g t) := by
              gcongr
          _ = CD * κX * (Real.exp (-(c * (zdistD (k + 3) L (a i₀ - x) : ℝ)) / ellT L g t)
              / (zdistD (k + 3) L (a i₀ - x) : ℝ) ^ (k + 1)) := by
              rw [div_eq_mul_inv]; ring
      have h2 : ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖
          ≤ (2 * R + 1) ^ (k + 3) * (C6 * κX * R
            * (((zdistD (k + 3) L (a j - x) : ℝ) ^ (k + 2))⁻¹)) := by
        calc ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖
            ≤ ∑ _y ∈ Win x, C6 * κX * R * (((zdistD (k + 3) L (a j - x) : ℝ) ^ (k + 2))⁻¹) :=
              Finset.sum_le_sum fun y hy => hDpt j x hfx y hy
          _ = ((Win x).card : ℝ) * (C6 * κX * R
              * (((zdistD (k + 3) L (a j - x) : ℝ) ^ (k + 2))⁻¹)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 * R + 1) ^ (k + 3) * (C6 * κX * R
              * (((zdistD (k + 3) L (a j - x) : ℝ) ^ (k + 2))⁻¹)) :=
              mul_le_mul_of_nonneg_right (hcard x) (by positivity)
      calc ‖Ξ i₀ (a i₀) x‖ * ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖
          ≤ (CD * κX * (Real.exp (-(c * (zdistD (k + 3) L (a i₀ - x) : ℝ)) / ellT L g t)
              / (zdistD (k + 3) L (a i₀ - x) : ℝ) ^ (k + 1)))
            * ((2 * R + 1) ^ (k + 3) * (C6 * κX * R
              * (((zdistD (k + 3) L (a j - x) : ℝ) ^ (k + 2))⁻¹))) :=
            mul_le_mul h1 h2 (Finset.sum_nonneg fun y _ => norm_nonneg _) (by positivity)
        _ = T * G x := by
            rw [hT, hG]
            simp only [div_eq_mul_inv, mul_inv]
            ring
    have hlat := ekSZ_lattice k hL hc hℓt0 hR₂1 (a i₀) (a j)
    have hfl : R ≤ (⌊ρ * R⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (ρ * R)
      linarith
    have hpsi := ekSZ_ar_psi (k := k) (R := R) (Rn := (⌊ρ * R⌋₊ : ℝ)) (κX := κX) (r := r) (ρ := ρ)
      (CD := CD) (C6 := C6) (lat := latC k) (lg := Real.log L) hR1 hfl hκ0 hκR hCD hC6 hlat0 hlog0
    calc ∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
          ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖
        ≤ ∑ x ∈ Finset.univ.filter far, T * G x := Finset.sum_le_sum hpt
      _ = T * ∑ x ∈ Finset.univ.filter far, G x := by rw [Finset.mul_sum]
      _ ≤ T * ∑ x ∈ Finset.univ.filter (fun x : Zd (k + 3) L =>
            ρ * R < (zdistD (k + 3) L (a i₀ - x) : ℝ) ∧ ρ * R < (zdistD (k + 3) L (a j - x) : ℝ)),
            G x := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hT0
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact ⟨(hfar' x).mp hx i₀, (hfar' x).mp hx j⟩
          · intro x _ _
            rw [hG]
            positivity
      _ ≤ T * (latC k * Real.log L / (⌊ρ * R⌋₊ : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left hlat hT0
      _ ≤ Ψ := by rw [hΨdef, hT]; exact hpsi
  -- the conclusion
  have hcore := ekSZ_core i₀ Ξ a A Win far (M := ‖A‖) (δ := W ^ (-D)) (Q := Q) (Sξ := Sξ)
    (Rn := Rn) (Snon := Snon) (Ψ := Ψ) (norm_nonneg _) hWD hQ0 hSξ0 hSnon0 hΨ0
    (fun b => norm_le_pi_norm A b) htail hsz hrow hwin hnear hne hX hΔ hΨ'
  simp only [hu_eq]
  refine hcore.trans (le_of_eq ?_)
  rw [card_Zd, Nat.cast_pow]

end Concrete

/-! ### Part III: the constants -/

section Arith

/-- the `‖A‖`-coefficient: constants and powers of `ρ = W^ε` and `r` (the pin's `W^{Cε} r^n`);
`lg` is the `log L` of `(eq:latticesum_d3)`, absorbed by `ρ ≥ log L`. -/
private theorem ekSZ_arith_M {n : ℕ} (hn : 2 ≤ n) {CB a₁ a₂ lg ρ r : ℝ} (hCB : 0 ≤ CB) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (hρ : 4 ≤ ρ) (hr : 1 ≤ r) (hlg : lg ≤ ρ) :
    (1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (n - 1)
      + 2 ^ (n - 1) * ((a₁ * ρ ^ 2 * r) ^ (n - 2) * (a₂ * lg * ρ ^ 4 * r ^ 2))
      ≤ ((1 + n * CB) * (1 + CB) ^ (n - 1) + 2 ^ (n - 1) * a₁ ^ (n - 2) * a₂)
          * ρ ^ (2 * n + 2) * r ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  have hρ0 : 0 < ρ := by linarith
  have hr0 : 0 < r := by linarith
  have hρ1 : 1 ≤ ρ := by linarith
  have hX1 : 1 ≤ ρ ^ 2 * r := by
    have : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ1
    nlinarith
  have hY1 : 1 ≤ ρ ^ 4 * r := by
    have : 1 ≤ ρ ^ 4 := one_le_pow₀ hρ1
    nlinarith
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- (i)
  have h1 : 1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r) ≤ (1 + ((m : ℝ) + 2) * CB) * (ρ ^ 4 * r) := by
    have : ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r) = ((m : ℝ) + 2) * CB * (ρ ^ 4 * r) := by ring
    rw [this]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 2) * CB) (by positivity : (0 : ℝ) ≤ ρ ^ 4 * r)]
  -- (ii)
  have h2 : (1 + CB * ρ ^ 2 * r) ^ (m + 1) ≤ ((1 + CB) * (ρ ^ 2 * r)) ^ (m + 1) := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    nlinarith
  have hpos1 : 0 ≤ 1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r) := by positivity
  have hterm1 : (1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (m + 1)
      ≤ (1 + ((m : ℝ) + 2) * CB) * (1 + CB) ^ (m + 1) * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2) := by
    calc (1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (m + 1)
        ≤ ((1 + ((m : ℝ) + 2) * CB) * (ρ ^ 4 * r)) * ((1 + CB) * (ρ ^ 2 * r)) ^ (m + 1) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (1 + ((m : ℝ) + 2) * CB) * (1 + CB) ^ (m + 1) * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2) := by
          rw [mul_pow, mul_pow]
          ring
  -- (iv)
  have hterm2 : 2 ^ (m + 1) * ((a₁ * ρ ^ 2 * r) ^ m * (a₂ * lg * ρ ^ 4 * r ^ 2))
      ≤ 2 ^ (m + 1) * a₁ ^ m * a₂ * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2) := by
    have hlgρ : lg * ρ ^ (2 * (m + 2)) ≤ ρ ^ (2 * (m + 2) + 2) := by
      calc lg * ρ ^ (2 * (m + 2)) ≤ ρ * ρ ^ (2 * (m + 2)) :=
            mul_le_mul_of_nonneg_right hlg (by positivity)
        _ = ρ ^ (2 * (m + 2) + 1) := by ring
        _ ≤ ρ ^ (2 * (m + 2) + 2) := pow_le_pow_right₀ hρ1 (by omega)
    calc 2 ^ (m + 1) * ((a₁ * ρ ^ 2 * r) ^ m * (a₂ * lg * ρ ^ 4 * r ^ 2))
        = 2 ^ (m + 1) * a₁ ^ m * a₂ * (lg * ρ ^ (2 * (m + 2))) * r ^ (m + 2) := by
          rw [mul_pow, mul_pow]; ring
      _ ≤ 2 ^ (m + 1) * a₁ ^ m * a₂ * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2) := by
          have h0 : 0 ≤ 2 ^ (m + 1) * a₁ ^ m * a₂ := by positivity
          have h3 : 0 ≤ r ^ (m + 2) := by positivity
          calc 2 ^ (m + 1) * a₁ ^ m * a₂ * (lg * ρ ^ (2 * (m + 2))) * r ^ (m + 2)
              ≤ 2 ^ (m + 1) * a₁ ^ m * a₂ * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2) := by
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlgρ h0) h3
            _ = _ := rfl
  calc (1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (m + 1)
        + 2 ^ (m + 1) * ((a₁ * ρ ^ 2 * r) ^ m * (a₂ * lg * ρ ^ 4 * r ^ 2))
      ≤ (1 + ((m : ℝ) + 2) * CB) * (1 + CB) ^ (m + 1) * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2)
        + 2 ^ (m + 1) * a₁ ^ m * a₂ * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2) := add_le_add hterm1 hterm2
    _ = ((1 + ((m : ℝ) + 2) * CB) * (1 + CB) ^ (m + 1) + 2 ^ (m + 1) * a₁ ^ m * a₂)
          * ρ ^ (2 * (m + 2) + 2) * r ^ (m + 2) := by ring


/-- the `W^{-D}`-coefficient: powers of `W` and the complement count `V^{n-1}` with `V = W^K`. -/
private theorem ekSZ_arith_D {n : ℕ} (hn : 2 ≤ n) {CB Q W V Lk ρ r : ℝ} (hCB : 0 ≤ CB) (hQ0 : 0 ≤ Q)
    (hW : 1 ≤ W) (hQW : 1 + Q ≤ W) (hr1 : 1 ≤ r) (hrQ : r ≤ 1 + Q) (hρ : 4 ≤ ρ) (hρW : ρ ≤ W)
    (hV : 1 ≤ V) (hLk0 : 0 ≤ Lk) (hLk : Lk ≤ V) :
    (1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (n - 1) + Q * (1 + Q) ^ (n - 1)
        + Q ^ n * Lk ^ (n - 1)
      ≤ (3 + n * CB) * (W ^ (n + 4) * V ^ (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  rw [e1]
  have hW0 : 0 < W := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hr0 : 0 < r := by linarith
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hrW : r ≤ W := hrQ.trans hQW
  have hQW' : Q ≤ W := by linarith
  have hW5 : 1 ≤ W ^ 5 := one_le_pow₀ hW
  have hρ4 : ρ ^ 4 ≤ W ^ 4 := pow_le_pow_left₀ hρ0.le hρW 4
  -- the first factor
  have hRn : 1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r) ≤ (1 + ((m : ℝ) + 2) * CB) * W ^ 5 := by
    have h1 : (ρ ^ 2) ^ 2 * r ≤ W ^ 5 := by
      calc (ρ ^ 2) ^ 2 * r = ρ ^ 4 * r := by ring
        _ ≤ W ^ 4 * W := mul_le_mul hρ4 hrW hr0.le (by positivity)
        _ = W ^ 5 := by ring
    have h2 : CB * (ρ ^ 2) ^ 2 * r ≤ CB * W ^ 5 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hCB
    have h3 : ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r) ≤ ((m : ℝ) + 2) * (CB * W ^ 5) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have hpow : (1 + Q) ^ (m + 1) ≤ W ^ (m + 1) := pow_le_pow_left₀ (by linarith) hQW _
  have hterm1 : (1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (m + 1)
      ≤ (1 + ((m : ℝ) + 2) * CB) * (W ^ (m + 2 + 4) * V ^ (m + 1)) := by
    have hV1 : 1 ≤ V ^ (m + 1) := one_le_pow₀ hV
    calc (1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (m + 1)
        ≤ ((1 + ((m : ℝ) + 2) * CB) * W ^ 5) * W ^ (m + 1) :=
          mul_le_mul hRn hpow (by positivity) (by positivity)
      _ = (1 + ((m : ℝ) + 2) * CB) * W ^ (m + 2 + 4) := by ring
      _ ≤ (1 + ((m : ℝ) + 2) * CB) * (W ^ (m + 2 + 4) * V ^ (m + 1)) := by
          have h0 : 0 ≤ (1 + ((m : ℝ) + 2) * CB) := by positivity
          refine mul_le_mul_of_nonneg_left ?_ h0
          have : 0 ≤ W ^ (m + 2 + 4) := by positivity
          nlinarith
  have hterm2 : Q * (1 + Q) ^ (m + 1) ≤ W ^ (m + 2 + 4) * V ^ (m + 1) := by
    have hV1 : 1 ≤ V ^ (m + 1) := one_le_pow₀ hV
    calc Q * (1 + Q) ^ (m + 1) ≤ (1 + Q) * (1 + Q) ^ (m + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1 + Q) ^ (m + 2) := by ring
      _ ≤ W ^ (m + 2) := pow_le_pow_left₀ (by linarith) hQW _
      _ ≤ W ^ (m + 2 + 4) := pow_le_pow_right₀ hW (by omega)
      _ = W ^ (m + 2 + 4) * 1 := (mul_one _).symm
      _ ≤ W ^ (m + 2 + 4) * V ^ (m + 1) :=
          mul_le_mul_of_nonneg_left hV1 (by positivity)
  have hterm3 : Q ^ (m + 2) * Lk ^ (m + 1) ≤ W ^ (m + 2 + 4) * V ^ (m + 1) := by
    calc Q ^ (m + 2) * Lk ^ (m + 1) ≤ W ^ (m + 2) * V ^ (m + 1) :=
          mul_le_mul (pow_le_pow_left₀ hQ0 hQW' _) (pow_le_pow_left₀ hLk0 hLk _)
            (by positivity) (by positivity)
      _ ≤ W ^ (m + 2 + 4) * V ^ (m + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hW (by omega)) (by positivity)
  have hfin : (1 + ((m : ℝ) + 2) * CB) * (W ^ (m + 2 + 4) * V ^ (m + 1)) + W ^ (m + 2 + 4) * V ^ (m + 1)
      + W ^ (m + 2 + 4) * V ^ (m + 1) = (3 + ((m : ℝ) + 2) * CB) * (W ^ (m + 2 + 4) * V ^ (m + 1)) := by
    ring
  calc (1 + ((m : ℝ) + 2) * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (m + 1) + Q * (1 + Q) ^ (m + 1)
        + Q ^ (m + 2) * Lk ^ (m + 1)
      ≤ (1 + ((m : ℝ) + 2) * CB) * (W ^ (m + 2 + 4) * V ^ (m + 1)) + W ^ (m + 2 + 4) * V ^ (m + 1)
        + W ^ (m + 2 + 4) * V ^ (m + 1) := add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = (3 + ((m : ℝ) + 2) * CB) * (W ^ (m + 2 + 4) * V ^ (m + 1)) := hfin

/-- `W^a (W^K)^b = W^{a + K b}`. -/
private theorem ekSZ_rpow_combine {W K : ℝ} (hW : 0 < W) (a b : ℕ) :
    W ^ a * (W ^ K) ^ b = W ^ ((a : ℝ) + K * (b : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hW.le, ← Real.rpow_add hW]

/-- the final arithmetic of the pin: the two coefficients of `(‖A‖, W^{-D})` against the pin's
`W^{Cε} r^n ‖A‖ + W^{-D+C}`, `C = (m₁ + 2n + 2) + (m₂ + n + 4 + K(n-1))`. -/
private theorem ekSZ_final_arith {n : ℕ} (hn : 2 ≤ n)
    {CB a₁ a₂ K W ε D ρ r Q lg Lk A' : ℝ} {m₁ m₂ : ℕ}
    (hCB : 0 ≤ CB) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hK : 0 < K) (hW1 : 1 ≤ W) (hε0 : 0 < ε)
    (hρdef : ρ = W ^ ε) (hρ4 : 4 ≤ ρ) (hρW : ρ ≤ W) (hr1 : 1 ≤ r) (hrP : r ≤ 1 + Q)
    (hQ0 : 0 ≤ Q) (hPW : 1 + Q ≤ W) (hlog : lg ≤ ρ)
    (hm₁ : (1 + n * CB) * (1 + CB) ^ (n - 1) + 2 ^ (n - 1) * a₁ ^ (n - 2) * a₂ < 4 ^ m₁)
    (hm₂ : 3 + n * CB < 4 ^ m₂) (hLK : Lk ≤ W ^ K) (hLk0 : 0 ≤ Lk) (hWD : 0 ≤ W ^ (-D))
    (hA' : 0 ≤ A') :
    A' * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (n - 1)
          + 2 ^ (n - 1) * ((a₁ * ρ ^ 2 * r) ^ (n - 2) * (a₂ * lg * ρ ^ 4 * r ^ 2)))
        + W ^ (-D) * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (n - 1)
          + Q * (1 + Q) ^ (n - 1) + Q ^ n * Lk ^ (n - 1))
      ≤ W ^ ((((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) * ε) * r ^ n * A'
        + W ^ (-D + (((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1)))) := by
  have hW0 : 0 < W := by linarith
  have hW4 : 4 ≤ W := hρ4.trans hρW
  have hM := ekSZ_arith_M hn hCB ha₁ ha₂ hρ4 hr1 hlog
  have hV1 : 1 ≤ W ^ K := Real.one_le_rpow hW1 hK.le
  have hD := ekSZ_arith_D hn hCB hQ0 hW1 hPW hr1 hrP hρ4 hρW (V := W ^ K) (Lk := Lk) hV1 hLk0 hLK
  have hE₂0 : (0 : ℝ) ≤ (m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 ≤ K * ((n : ℝ) - 1) := mul_nonneg hK.le (by linarith)
    have : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg m₂
    linarith
  have hE₁0 : (0 : ℝ) ≤ (m₁ : ℝ) + 2 * n + 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg m₁
    linarith
  -- `A'`-coefficient
  have h1 : A' * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (n - 1)
        + 2 ^ (n - 1) * ((a₁ * ρ ^ 2 * r) ^ (n - 2) * (a₂ * lg * ρ ^ 4 * r ^ 2)))
      ≤ W ^ ((((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) * ε) * r ^ n * A' := by
    have hQ1 : (1 + n * CB) * (1 + CB) ^ (n - 1) + 2 ^ (n - 1) * a₁ ^ (n - 2) * a₂ ≤ ρ ^ m₁ :=
      hm₁.le.trans (pow_le_pow_left₀ (by norm_num) hρ4 m₁)
    have hρN : ρ ^ (m₁ + (2 * n + 2)) = W ^ (((m₁ : ℝ) + 2 * n + 2) * ε) := by
      rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      congr 1
      push_cast
      ring
    have hρ0 : 0 < ρ := by linarith
    have hr0 : 0 < r := by linarith
    have hrn : 0 ≤ r ^ n := by positivity
    have hρpow : 0 ≤ ρ ^ (2 * n + 2) := by positivity
    have hexp : W ^ (((m₁ : ℝ) + 2 * n + 2) * ε)
        ≤ W ^ ((((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) * ε) := by
      refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
      have := mul_nonneg hE₂0 hε0.le
      linarith
    calc A' * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (n - 1)
          + 2 ^ (n - 1) * ((a₁ * ρ ^ 2 * r) ^ (n - 2) * (a₂ * lg * ρ ^ 4 * r ^ 2)))
        ≤ A' * (((1 + n * CB) * (1 + CB) ^ (n - 1) + 2 ^ (n - 1) * a₁ ^ (n - 2) * a₂)
            * ρ ^ (2 * n + 2) * r ^ n) := mul_le_mul_of_nonneg_left hM hA'
      _ ≤ A' * (ρ ^ m₁ * ρ ^ (2 * n + 2) * r ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ hA'
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ1 hρpow) hrn
      _ = W ^ (((m₁ : ℝ) + 2 * n + 2) * ε) * r ^ n * A' := by
          rw [← pow_add, hρN]; ring
      _ ≤ W ^ ((((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) * ε) * r ^ n
            * A' := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hrn) hA'
  -- `W^{-D}`-coefficient
  have h2 : W ^ (-D) * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (n - 1)
        + Q * (1 + Q) ^ (n - 1) + Q ^ n * Lk ^ (n - 1))
      ≤ W ^ (-D + (((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1)))) := by
    have hQ2 : 3 + n * CB ≤ W ^ m₂ := hm₂.le.trans (pow_le_pow_left₀ (by norm_num) hW4 m₂)
    have hWm : (3 + (n : ℝ) * CB) * (W ^ (n + 4) * (W ^ K) ^ (n - 1))
        ≤ W ^ (((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) := by
      calc (3 + (n : ℝ) * CB) * (W ^ (n + 4) * (W ^ K) ^ (n - 1))
          ≤ W ^ m₂ * (W ^ (n + 4) * (W ^ K) ^ (n - 1)) :=
            mul_le_mul_of_nonneg_right hQ2 (by positivity)
        _ = W ^ (m₂ + (n + 4)) * (W ^ K) ^ (n - 1) := by rw [pow_add]; ring
        _ = W ^ (((m₂ + (n + 4) : ℕ) : ℝ) + K * ((n - 1 : ℕ) : ℝ)) := ekSZ_rpow_combine hW0 _ _
        _ = W ^ (((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) := by
            congr 1
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            push_cast
            ring
    calc W ^ (-D) * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (n - 1)
          + Q * (1 + Q) ^ (n - 1) + Q ^ n * Lk ^ (n - 1))
        ≤ W ^ (-D) * W ^ (((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left (hD.trans hWm) hWD
      _ = W ^ (-D + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1))) := (Real.rpow_add hW0 _ _).symm
      _ ≤ W ^ (-D + (((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1)))) := by
          refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
          linarith
  exact add_le_add h1 h2

end Arith

/-! ### Part IV: the pin -/

/-- **`(sumAzero) ⟹ (sum_res_2)` of `lem:sum_decay`** for every `n ≥ 2`, `d ≥ 3`, uniform in
`g ∈ (0, Λ]`: the pin `EKSumDecay2` (amended by DECISIONS §21: `L^d ≤ W^K`, candidate `T2042a`).
The route is the paper's `(sum_res_2_red)` (`A_deterministic_estimates.tex:155-199`): `b₁` is split
into `S_near` and `S_far`; on `S_far` the product `∏_i Ξ_i(a_i, b_i)` is expanded around `b₁`, the
leading term dies by `(sumAzero)`, the other terms carry the first differences of `Ξ` (pin 6) and the
lattice sum `(eq:latticesum_d3)`.  The exponent of `W^ε` proved is `m₁ + 2n + 2`, a natural `m₁`
with `Q₁ < 4^{m₁}`, `Q₁ = (1 + n C_B)(1 + C_B)^{n-1} + 2^{n-1} a₁^{n-2} a₂`, `a₁ = 3^d (C_D + C₆)`,
`a₂ = 3^d C₆ C_D C_lat` (`C_B`, `C_D`: `ekXiBall_holds`, `ekXiDecay_holds`; `C₆`: `Prop6Diff1`;
`C_lat = latC (d-3)`); the exponent of the complement is `m₂ + n + 4 + K(n-1)`, `m₂` with
`3 + n C_B < 4^{m₂}`; the constant is `C = (m₁ + 2n + 2) + (m₂ + n + 4 + K(n-1))`. -/
theorem ekSumDecay2_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecay2 d n Λ κ := by
  intro h5 _h5s h6 hd hn hΛ hκ K hK
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
  obtain ⟨CB, hCB, hball⟩ := ekXiBall_holds (k + 3) Λ h5 hd hΛ
  obtain ⟨CD, c, hCD, hc, hdec⟩ := ekXiDecay_holds (k + 3) Λ h5 hd hΛ
  obtain ⟨C6, hC6, h6'⟩ := h6 hd hΛ hκ (by norm_num) (by norm_num)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlat0 : 0 ≤ latC k := (latC_pos k).le
  -- the constants
  obtain ⟨a₁, ha₁def⟩ : ∃ a₁ : ℝ, a₁ = 3 ^ (k + 3) * (CD + C6) := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂def⟩ : ∃ a₂ : ℝ, a₂ = 3 ^ (k + 3) * C6 * CD * latC k := ⟨_, rfl⟩
  have ha₁ : 0 ≤ a₁ := by rw [ha₁def]; positivity
  have ha₂ : 0 ≤ a₂ := by rw [ha₂def]; positivity
  obtain ⟨m₁, hm₁⟩ := pow_unbounded_of_one_lt
    ((1 + n * CB) * (1 + CB) ^ (n - 1) + 2 ^ (n - 1) * a₁ ^ (n - 2) * a₂) (by norm_num : (1 : ℝ) < 4)
  obtain ⟨m₂, hm₂⟩ := pow_unbounded_of_one_lt (3 + n * CB) (by norm_num : (1 : ℝ) < 4)
  have hK1 : 0 ≤ K * ((n : ℝ) - 1) := mul_nonneg hK.le (by linarith)
  have hm₁0 : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg m₁
  have hm₂0 : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg m₂
  refine ⟨((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1)), by linarith, ?_⟩
  intro L hL g hg hgΛ W ε D hW1 hε0 hε1 hD hρ4 hlog hLK s t hs hst ht hWt m hm hκm σ A
  have : NeZero L := ⟨by omega⟩
  intro hA hz
  -- basic facts
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t := by linarith
  have ht1 : t < 1 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
    linarith
  have ht0 : 0 ≤ t := hs.trans hst
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  have hW0 : 0 < W := by linarith
  have hW1' : (1 : ℝ) ≤ W := hW1.le
  have hρW : W ^ ε ≤ W := by
    have h1 : W ^ ε ≤ W ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1' hε1.le
    rwa [Real.rpow_one] at h1
  have hW4 : 4 ≤ W := hρ4.trans hρW
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  -- `r`, `P = 1 + Q`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (t - s) / (1 - t) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = W ^ ε := ⟨_, rfl⟩
  rw [← hr]
  have hr1 : 1 ≤ r := by
    rw [hr, abs_of_pos hu, abs_of_pos hv, le_div_iff₀ (by positivity)]
    linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact div_nonneg (by linarith) hu.le
  have hPeq : 1 + Q = (1 - s) / (1 - t) := by rw [hQ]; field_simp; ring
  have hPW : 1 + Q ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rw [inv_div] at h1
    rw [hPeq]; exact h1
  have hrP : r ≤ 1 + Q := by
    rw [hr, hPeq, abs_of_pos hu, abs_of_pos hv, div_le_div_iff₀ (by positivity) hu]
    have : 0 ≤ g ^ 2 * (t - s) := mul_nonneg (sq_nonneg g) (by linarith)
    nlinarith
  have hρ4' : 4 ≤ ρ := by rw [hρdef]; exact hρ4
  have hρW' : ρ ≤ W := by rw [hρdef]; exact hρW
  have hlog' : Real.log L ≤ ρ := by rw [hρdef]; exact hlog
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  -- the analytic inputs at `μ_i = m(σ_i) m(σ_{i+1})`
  have hμ : ∀ i : Fin n, ‖cycProd (EKsgn m σ) i‖ = 1 := fun i =>
    norm_cycProd (fun j => ek_norm_spin hm (σ j)) i
  have hball' : ∀ i : Fin n, ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
      ∀ (a ctr : Zd (k + 3) L) (D : Finset (Zd (k + 3) L)),
        (∀ b ∈ D, (zdistD (k + 3) L (ctr - b) : ℝ) ≤ R) →
        ∑ b ∈ D, ‖XiKer (k + 3) L g (cycProd (EKsgn m σ) i) s t a b‖
          ≤ CB * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := by
    intro i Λ' hΛ' R hR hRℓ a ctr D hD
    exact hball L hL g hg hgΛ _ (hμ i) s t hs hst ht1 hgt Λ' hΛ' R hR hRℓ a ctr D hD
  have hdec' : ∀ i : Fin n, ∀ x y : Zd (k + 3) L,
      ‖XiKer (k + 3) L g (cycProd (EKsgn m σ) i) s t x y‖
        ≤ CD * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
          * (((zdistD (k + 3) L (x - y) : ℝ) + 1) ^ (k + 1))⁻¹
          * Real.exp (-(c * (zdistD (k + 3) L (x - y) : ℝ)) / ellT L g t) := by
    intro i x y
    exact hdec L hL g hg hgΛ _ (hμ i) s t hs hst ht1 hgt x y
  have h6'' : ∀ i : Fin n, ∀ a r : Zd (k + 3) L,
      (zdistD (k + 3) L r : ℝ) ≤ 1 / 2 * (zdistD (k + 3) L a : ℝ) →
      ‖Theta (k + 3) L g ((t : ℂ) * cycProd (EKsgn m σ) i) 0 (a + r)
          - Theta (k + 3) L g ((t : ℂ) * cycProd (EKsgn m σ) i) 0 a‖
        ≤ C6 * (g ^ 2 + |1 - t|)⁻¹ * (zdistD (k + 3) L r : ℝ)
          * (((zdistD (k + 3) L a : ℝ) + 1) ^ (k + 2))⁻¹ := by
    intro i a r hr'
    exact h6' L hL g hg hgΛ t ht0 ht1 m hm hκm (σ i) (σ (finRotate n i)) a r hr'
  -- the pointwise claim
  have hpos : 0 ≤ W ^ (((((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1)))) * ε)
        * r ^ n * ‖A‖
      + W ^ (-D + (((m₁ : ℝ) + 2 * n + 2) + ((m₂ : ℝ) + n + 4 + K * ((n : ℝ) - 1)))) := by
    positivity
  refine (pi_norm_le_iff_of_nonneg hpos).mpr fun a => ?_
  have hconc := ekSZ_concrete (L := L) k hL hg hs hst ht1 hn (fun i => cycProd (EKsgn m σ) i) hμ
    hCB.le hCD.le hc hC6.le hball' hdec' h6'' (W := W) (ε := ε) (D := D) (ρ := ρ) (r := r) (Q := Q)
    (Sξ := CB * ρ ^ 2 * r) (Rn := n * (CB * (ρ ^ 2) ^ 2 * r)) (Snon := a₁ * ρ ^ 2 * r)
    (Ψ := a₂ * Real.log L * ρ ^ 4 * r ^ 2) hρdef hρ4' hr hQ rfl rfl
    (by rw [ha₁def]) (by rw [ha₂def]) hWD A hA hz a
  calc ‖UN (k + 3) L g (EKsgn m σ) s t A a‖
      = ‖∑ b : Fin n → Zd (k + 3) L, (∏ i, uKer (k + 3) L g (cycProd (EKsgn m σ) i) s t (a i) (b i))
          * A b‖ := rfl
    _ ≤ _ := hconc
    _ = ‖A‖ * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + CB * ρ ^ 2 * r) ^ (n - 1)
          + 2 ^ (n - 1) * ((a₁ * ρ ^ 2 * r) ^ (n - 2) * (a₂ * Real.log L * ρ ^ 4 * r ^ 2)))
        + W ^ (-D) * ((1 + n * (CB * (ρ ^ 2) ^ 2 * r)) * (1 + Q) ^ (n - 1)
          + Q * (1 + Q) ^ (n - 1) + Q ^ n * ((L : ℝ) ^ (k + 3)) ^ (n - 1)) := by
        rw [ha₁def, ha₂def]; ring
    _ ≤ _ := ekSZ_final_arith hn hCB.le ha₁ ha₂ hK hW1' hε0 hρdef hρ4' hρW' hr1 hrP hQ0 hPW
        hlog' hm₁ hm₂ hLK (by positivity) hWD (norm_nonneg _)

/-! ### Compiled nonempty instances

`d = 3`, `L = 5`, `g = 1/2`, `Λ = 1`, `κ = 1/2`, `K = 2` (`5^3 = 125 ≤ 25² = 625`), `m = i`
(`‖m‖ = 1`, `Im m = 1 ≥ κ`), `s = 1/2`, `t = 9/10` (`g²/L² = 1/100 ≤ 1 - t = 1/10`), `W = 25`,
`ε = 1/2` (`W^ε = 5 ≥ 4`, `log 5 ≤ 5`; the window radius `W^ε ℓ_s = 5` is below the torus diameter
`6`), `D = 2` (`W⁻¹ = 1/25 ≤ (1-t)/(1-s) = 1/5`).  Tensors: the sum-zero product tensors
`δ₀ ⊗ (δ₀ - δ_e)` (`n = 2`) and `δ₀ ⊗ (δ₀ - δ_e) ⊗ δ₀` (`n = 3`), `e = (1,0,0)`.  The three
propagator pins are discharged by the proved `prop5Decay_holds`, `prop5Short_holds`,
`prop6Diff1_holds`: no hypothesis of the pin is left open. -/

section Instances

private abbrev ekSZe : Zd 3 5 := ![1, 0, 0]

/-- a product tensor `A_b = ∏_i f_i(b_i)` -/
private noncomputable def ekSZprod {n : ℕ} (f : Fin n → Zd 3 5 → ℂ) : (Fin n → Zd 3 5) → ℂ :=
  fun b => ∏ i, f i (b i)

/-- the factors: `δ₀` and `δ₀ - δ_e` -/
private noncomputable def ekSZd0 : Zd 3 5 → ℂ := fun y => if y = 0 then 1 else 0

private noncomputable def ekSZde : Zd 3 5 → ℂ := fun y =>
  (if y = 0 then 1 else 0) - (if y = ekSZe then 1 else 0)

/-- `δ₀ ⊗ (δ₀ - δ_e)` on `(Z_5^3)^2` -/
private noncomputable def ekSZAz2 : (Fin 2 → Zd 3 5) → ℂ := ekSZprod ![ekSZd0, ekSZde]

/-- `δ₀ ⊗ (δ₀ - δ_e) ⊗ δ₀` on `(Z_5^3)^3` -/
private noncomputable def ekSZAz3 : (Fin 3 → Zd 3 5) → ℂ := ekSZprod ![ekSZd0, ekSZde, ekSZd0]

private theorem ekSZ_zdistD_E : zdistD 3 5 ekSZe = 1 := by
  unfold zdistD
  simp only [zdist, ekSZe, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, ZMod.val_zero, tsub_zero, zero_le, inf_of_le_left, add_zero,
    Matrix.cons_val]
  decide

private theorem ekSZ_zero_ne_E : (0 : Zd 3 5) ≠ ekSZe := by
  intro h
  have := congrFun h 0
  simp only [ekSZe, Pi.zero_apply, Matrix.cons_val_zero] at this
  exact absurd this (by decide)

private theorem ekSZ_sqrt25 : (25 : ℝ) ^ ((1 : ℝ) / 2) = 5 := by
  rw [← Real.sqrt_eq_rpow, show (25 : ℝ) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

private theorem ekSZ_ellT_s : ellT 5 (1 / 2 : ℝ) (1 / 2) = 1 := by
  unfold ellT
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt |1 - 1 / 2| := by
    rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by rw [abs_of_pos (by norm_num)]; norm_num]
    have h4 : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact (Real.sqrt_sq (by norm_num)).symm
    calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := h4
      _ ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt (by norm_num)
  have h : (1 / 2 : ℝ) / Real.sqrt |1 - 1 / 2| ≤ 1 := by
    rw [div_le_one (lt_of_lt_of_le (by norm_num) hs)]
    exact hs
  rw [max_eq_right h]
  norm_num

private theorem ekSZ_zdistD_far : zdistD 3 5 (![2, 2, 1] : Zd 3 5) = 5 := by
  unfold zdistD
  simp only [Fin.sum_univ_three, zdist]
  decide

private theorem ekSZ_log5 : Real.log ((5 : ℕ) : ℝ) ≤ (25 : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [ekSZ_sqrt25]
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < ((5 : ℕ) : ℝ))
  push_cast at this ⊢
  linarith

/-- the points of `{0, e}` are at distance `≤ 1` from each other -/
private theorem ekSZ_dist_le_one {x y : Zd 3 5} (hx : x = 0 ∨ x = ekSZe) (hy : y = 0 ∨ y = ekSZe) :
    zdistD 3 5 (x - y) ≤ 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp
  · rw [zero_sub, zdistD_neg, ekSZ_zdistD_E]
  · rw [sub_zero, ekSZ_zdistD_E]
  · simp

/-- `δ₀ ⊗ (δ₀ - δ_e) ⊗ …`: a nonzero value forces every coordinate into `{0, e}` -/
private theorem ekSZ_support {n : ℕ} (f : Fin n → Zd 3 5 → ℂ)
    (hf : ∀ i y, f i y ≠ 0 → y = 0 ∨ y = ekSZe) (b : Fin n → Zd 3 5) (hb : ekSZprod f b ≠ 0)
    (i : Fin n) : b i = 0 ∨ b i = ekSZe := by
  refine hf i (b i) ?_
  intro h
  apply hb
  unfold ekSZprod
  exact Finset.prod_eq_zero (Finset.mem_univ i) h

private theorem ekSZ_d0_supp : ∀ y, ekSZd0 y ≠ 0 → y = 0 ∨ y = ekSZe := by
  intro y hy
  left
  by_contra h
  exact hy (by simp [ekSZd0, h])

private theorem ekSZ_de_supp : ∀ y, ekSZde y ≠ 0 → y = 0 ∨ y = ekSZe := by
  intro y hy
  by_contra h
  push Not at h
  exact hy (by simp [ekSZde, h.1, h.2])

/-- the product tensor with a factor of zero sum at an index `≠ i₀` is sum-zero. -/
private theorem ekSZ_prod_sumzero {n : ℕ} (f : Fin n → Zd 3 5 → ℂ) (i₀ j : Fin n) (hj : j ≠ i₀)
    (hjs : ∑ y, f j y = 0) (x : Zd 3 5) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin n → Zd 3 5 => b i₀ = x), ekSZprod f b = 0 := by
  classical
  set f' : Fin n → Zd 3 5 → ℂ := fun i y => if i = i₀ then (if y = x then f i y else 0) else f i y
    with hf'
  have h1 : ∑ b ∈ Finset.univ.filter (fun b : Fin n → Zd 3 5 => b i₀ = x), ekSZprod f b
      = ∑ b : Fin n → Zd 3 5, ∏ i, f' i (b i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold ekSZprod
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (b i)) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ (fun i => f' i (b i)) (Finset.mem_univ i₀)]
    have hrest : ∏ i ∈ Finset.univ.erase i₀, f' i (b i) = ∏ i ∈ Finset.univ.erase i₀, f i (b i) :=
      Finset.prod_congr rfl fun i hi => by simp [hf', Finset.ne_of_mem_erase hi]
    rw [hrest]
    by_cases hb : b i₀ = x <;> simp [hf', hb]
  have h2 : ∑ b : Fin n → Zd 3 5, ∏ i, f' i (b i) = ∏ i, ∑ y, f' i y := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [h1, h2]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hf', hj, hjs])

/-- `δ₀ - δ_e` has zero sum. -/
private theorem ekSZ_de_sum : ∑ y, ekSZde y = 0 := by
  simp [ekSZde, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- the product tensors of the instances satisfy `(deccA0)` at the instance data: a far pair of
indices forces the value `0`. -/
private theorem ekSZ_fastDecay {n : ℕ} (f : Fin n → Zd 3 5 → ℂ)
    (hf : ∀ i y, f i y ≠ 0 → y = 0 ∨ y = ekSZe) :
    EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 (ekSZprod f) := by
  intro a ⟨i, j, hij⟩
  by_cases h : ekSZprod f a = 0
  · rw [h]; simp only [norm_zero]; positivity
  · exfalso
    have hdist := ekSZ_dist_le_one (ekSZ_support f hf a h i) (ekSZ_support f hf a h j)
    rw [ekSZ_sqrt25, ekSZ_ellT_s] at hij
    have h1 : (zdistD 3 5 (a i - a j) : ℝ) ≤ 1 := by exact_mod_cast hdist
    linarith

private theorem ekSZ_fastDecay2 : EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 ekSZAz2 := by
  refine ekSZ_fastDecay _ ?_
  intro i y hy
  fin_cases i
  · exact ekSZ_d0_supp y hy
  · exact ekSZ_de_supp y hy

private theorem ekSZ_fastDecay3 : EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 ekSZAz3 := by
  refine ekSZ_fastDecay _ ?_
  intro i y hy
  fin_cases i
  · exact ekSZ_d0_supp y hy
  · exact ekSZ_de_supp y hy
  · exact ekSZ_d0_supp y hy

private theorem ekSZ_sumZero2 : EKSumZero ekSZAz2 := by
  intro i₀ hi₀ x
  have hi : i₀ = 0 := Fin.ext hi₀
  subst hi
  exact ekSZ_prod_sumzero _ 0 1 (by decide) ekSZ_de_sum x

private theorem ekSZ_sumZero3 : EKSumZero ekSZAz3 := by
  intro i₀ hi₀ x
  have hi : i₀ = 0 := Fin.ext hi₀
  subst hi
  exact ekSZ_prod_sumzero _ 0 1 (by decide) ekSZ_de_sum x

/-- the tensors are nonzero: `A_{(0,0)} = 1`, `A_{(0,e)} = -1` -/
example : ekSZAz2 ![0, 0] = 1 ∧ ekSZAz2 ![0, ekSZe] = -1 := by
  simp [ekSZAz2, ekSZprod, Fin.prod_univ_two, ekSZd0, ekSZde, ekSZ_zero_ne_E,
    ekSZ_zero_ne_E.symm]

example : ekSZAz3 ![0, 0, 0] = 1 ∧ ekSZAz3 ![0, ekSZe, 0] = -1 := by
  simp [ekSZAz3, ekSZprod, Fin.prod_univ_three, ekSZd0, ekSZde, ekSZ_zero_ne_E,
    ekSZ_zero_ne_E.symm]

/-- the far premise of `(deccA0)` is not vacuous at the instance data, for every `n ≥ 2`: two
indices at `ℓ¹` distance `5 = W^ε ℓ_s`. -/
example (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : Fin n → Zd 3 5, ∃ i j, (25 : ℝ) ^ ((1 : ℝ) / 2) * ellT 5 (1 / 2 : ℝ) (1 / 2)
      ≤ (zdistD 3 5 (a i - a j) : ℝ) := by
  refine ⟨fun i => if i.val = 0 then 0 else ![2, 2, 1], ⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  rw [ekSZ_sqrt25, ekSZ_ellT_s]
  simp only [↓reduceIte, one_ne_zero, zero_sub, zdistD_neg, ekSZ_zdistD_far]
  norm_num

/-- **Instance of `ekSumDecay2_holds`**, `n = 2`, `σ = (+,-)`, `K = 2`, `A = δ₀ ⊗ (δ₀ - δ_e)`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekSZAz2‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) *
        (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2 * ‖ekSZAz2‖
      + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := ekSumDecay2_holds 3 2 1 (1 / 2) (prop5Decay_holds 3 1)
    (prop5Short_holds 3 1 (1 / 2)) (prop6Diff1_holds 3 1 (1 / 2) (1 / 2)) le_rfl le_rfl one_pos
    (by norm_num) 2 two_pos
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ekSZ_sqrt25]; norm_num)
    ekSZ_log5 (by norm_num [Real.rpow_two]) (1 / 2) (9 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Complex.I Complex.norm_I (by norm_num [Complex.I_im])
    ![true, false] ekSZAz2 ekSZ_fastDecay2 ekSZ_sumZero2⟩

/-- **Instance of `ekSumDecay2_holds`**, `n = 3`, `σ = (+,-,+)`, `K = 2`,
`A = δ₀ ⊗ (δ₀ - δ_e) ⊗ δ₀`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false, true]) (1 / 2) (9 / 10) ekSZAz3‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) *
        (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 3 * ‖ekSZAz3‖
      + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := ekSumDecay2_holds 3 3 1 (1 / 2) (prop5Decay_holds 3 1)
    (prop5Short_holds 3 1 (1 / 2)) (prop6Diff1_holds 3 1 (1 / 2) (1 / 2)) le_rfl (by norm_num)
    one_pos (by norm_num) 2 two_pos
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ekSZ_sqrt25]; norm_num)
    ekSZ_log5 (by norm_num [Real.rpow_two]) (1 / 2) (9 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Complex.I Complex.norm_I (by norm_num [Complex.I_im])
    ![true, false, true] ekSZAz3 ekSZ_fastDecay3 ekSZ_sumZero3⟩

end Instances

end RBM
