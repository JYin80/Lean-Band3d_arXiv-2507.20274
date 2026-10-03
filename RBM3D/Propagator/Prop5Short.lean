/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Pins
import RBM3D.Propagator.Gap

/-!
# `(prop:ThfadC_short)`: the strong decay of `Θ_t^{(σ,σ)}` (proved)

`prop5Short_holds : ∀ d Λ κ, Prop5Short d Λ κ`.  The proof is the gap + Neumann series argument
of Appendix A.1 (`A_deterministic_estimates.tex:20-55`), made exact for the random band model.

Write `s = S^{(B)}_{00} = (1+2dλ²)⁻¹` and `μ = m(σ)²`, `ξ = tμ`.  Then
`S^{(B)} = s·1 + λ²s·Adj` (`Adj` the nearest-neighbour adjacency), so with `w = 1 - ξ s` and
`K = (ξ λ² s / w) Adj` one has `1 - ξ S^{(B)} = w (1 - K)` and `Θ = w⁻¹ Σ_k K^k`.

* gap: `|w|² = (1-ts)² + 4ts (Im m)² ≥ κ'²`, `κ' = min κ 1`, uniformly in `t ∈ [0,1)`;
* ratio: `ρ = ‖K‖_{∞→∞} = 2d t λ² s/|w| = t(1-s)/|w|`, and
  `ρ² ≤ 1/(1 + 4 s_min κ'²) =: q` with `s_min = (1+2dΛ²)⁻¹`; hence `ρ ≤ (1+q)/2 =: r₁ < 1`;
* locality: `Adj^k(0,a) = 0` for `k < |a|`; for `k ≥ 1`, `|K^k(0,a)| ≤ ‖K‖ ρ^{k-1}` and
  `‖K‖ ≤ 2dλ²/κ'`, which extracts the factor `λ²` of the pin for `a ≠ 0`.

The constants depend on `(d, Λ, κ)` only.
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

/-! ### The adjacency matrix and the decomposition of `S^{(B)}` -/

/-- The nearest-neighbour adjacency matrix of `Z_L^d` (complex entries). -/
private noncomputable def P5s_adj (d L : ℕ) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun x y => if zdistD d L (x - y) = 1 then 1 else 0

private theorem P5s_SB_eq (d L : ℕ) [NeZero L] (g : ℝ) :
    SB d L g = (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ)
      + ((g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ) • P5s_adj d L := by
  ext x y
  rw [SB_apply]
  by_cases h0 : x - y = 0
  · have hxy : x = y := sub_eq_zero.mp h0
    subst hxy
    simp [sbKernel, P5s_adj]
  · have hne : x ≠ y := fun h => h0 (sub_eq_zero.mpr h)
    by_cases h1 : zdistD d L (x - y) = 1
    · simp [sbKernel, P5s_adj, h0, h1, hne]
    · simp [sbKernel, P5s_adj, h0, h1, hne]

/-- `Adj^k(x,y) = 0` for `k < |x - y|`. -/
private theorem P5s_adj_pow_eq_zero (d L : ℕ) [NeZero L] :
    ∀ (k : ℕ) (x y : Zd d L), k < zdistD d L (x - y) → (P5s_adj d L ^ k) x y = 0 := by
  intro k
  induction k with
  | zero =>
    intro x y h
    have hne : x ≠ y := by
      intro hxy
      subst hxy
      simp at h
    simp [Matrix.one_apply_ne hne]
  | succ k ih =>
    intro x y h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : zdistD d L (z - y) = 1
    · have h1 : zdistD d L (x - y) ≤ zdistD d L (x - z) + zdistD d L (z - y) := by
        simpa using zdistD_add_le d L (x - z) (z - y)
      have hk : k < zdistD d L (x - z) := by omega
      rw [ih x z hk, zero_mul]
    · simp [P5s_adj, hz]

/-! ### Row sums and the `ℓ^∞` operator norm -/

private theorem P5s_rowsum_le_norm {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (x : n) : ∑ y, ‖M x y‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i : n => ∑ j : n, ‖M i j‖₊) (Finset.mem_univ x)
  have h2 := NNReal.coe_le_coe.mpr h
  simpa [NNReal.coe_sum] using h2

private theorem P5s_norm_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x, ∑ y, ‖M x y‖ ≤ c) : ‖M‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have hsup : (Finset.univ.sup fun i : n => ∑ j : n, ‖M i j‖₊) ≤ (⟨c, hc⟩ : ℝ≥0) := by
    refine Finset.sup_le fun x _ => ?_
    have h2 : ((∑ j : n, ‖M x j‖₊ : ℝ≥0) : ℝ) ≤ c := by simpa [NNReal.coe_sum] using h x
    exact NNReal.coe_le_coe.mp h2
  exact le_of_le_of_eq (NNReal.coe_le_coe.mpr hsup) rfl

private theorem P5s_entry_le_norm {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (x y : n) : ‖M x y‖ ≤ ‖M‖ :=
  le_trans (Finset.single_le_sum (f := fun j => ‖M x j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)) (P5s_rowsum_le_norm M x)

/-- Row sums of `ν • Adj`: `2d |ν|` (needs `3 ≤ L`). -/
private theorem P5s_rowsum_adj (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (ν : ℂ) (x : Zd d L) :
    ∑ y, ‖(ν • P5s_adj d L) x y‖ = 2 * d * ‖ν‖ := by
  have h1 : ∀ y : Zd d L, ‖(ν • P5s_adj d L) x y‖
      = if zdistD d L (x - y) = 1 then ‖ν‖ else 0 := by
    intro y
    by_cases hy : zdistD d L (x - y) = 1 <;> simp [P5s_adj, hy]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter fun a : Zd d L => zdistD d L (x - a) = 1).card = 2 * d := by
    convert card_adj d L hL x using 3
    exact Iff.rfl
  rw [hc]
  push_cast
  ring

/-! ### The Neumann operator -/

/-- `K = (ξ λ² s / w) Adj`, `w = 1 - ξ s`, `s = (1 + 2dλ²)⁻¹`. -/
private noncomputable def P5s_K (d L : ℕ) (g : ℝ) (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
  ((ξ * ((g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ))
      / (1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ))) • P5s_adj d L

private theorem P5s_one_sub_eq (d L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ)
    (hw : 1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0) :
    (1 : Matrix (Zd d L) (Zd d L) ℂ) - ξ • SB d L g
      = (1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ)) • (1 - P5s_K d L g ξ) := by
  have hν : (1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ))
      * ((ξ * ((g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ))
          / (1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ)))
      = ξ * ((g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ) := mul_div_cancel₀ _ hw
  rw [P5s_SB_eq, P5s_K, smul_sub, smul_smul, hν]
  module

private theorem P5s_tsum_mul_one_sub {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ)
    (hK : ‖K‖ < 1) : (∑' k : ℕ, K ^ k) * (1 - K) = 1 := by
  have h : Ring.inverse (1 - K) = ∑' k : ℕ, K ^ k := by
    rw [NormedRing.inverse_one_sub K hK]
    rfl
  rw [← h]
  exact Ring.inverse_mul_cancel _ ⟨Units.oneSub K hK, Units.val_oneSub _ _⟩

/-- `Θ_ξ = w⁻¹ Σ_k K^k` for `K = P5s_K`, `w = 1 - ξ s`. -/
private theorem P5s_Theta_eq (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (hw : 1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0)
    (hK : ‖P5s_K d L g ξ‖ < 1) :
    Theta d L g ξ = (1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ))⁻¹
      • ∑' k : ℕ, P5s_K d L g ξ ^ k := by
  symm
  refine eq_Theta_of_mul d L g (norm_SB d L g hL) hξ ?_
  rw [P5s_one_sub_eq d L g ξ hw, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hw, one_smul, P5s_tsum_mul_one_sub _ hK]

private theorem P5s_Theta_apply (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (hw : 1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0)
    (hK : ‖P5s_K d L g ξ‖ < 1) (a : Zd d L) :
    Theta d L g ξ 0 a = (1 - ξ * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ))⁻¹
      * ∑' k : ℕ, (P5s_K d L g ξ ^ k) 0 a := by
  have hs := summable_geometric_of_norm_lt_one hK
  have h := Pi.hasSum.mp (Pi.hasSum.mp hs.hasSum 0) a
  rw [P5s_Theta_eq d L hL g hξ hw hK, Matrix.smul_apply, smul_eq_mul]
  congr 1
  exact h.tsum_eq.symm

/-! ### Entry bounds for the powers of `ν • Adj` -/

private theorem P5s_pow_entry_le (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (ν : ℂ) {r : ℝ}
    (hr : 2 * (d : ℝ) * ‖ν‖ ≤ r) (k : ℕ) (x y : Zd d L) :
    ‖((ν • P5s_adj d L) ^ k) x y‖ ≤ r ^ k := by
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  have hK : ‖ν • P5s_adj d L‖ ≤ r :=
    P5s_norm_le _ hr0 fun z => (P5s_rowsum_adj d L hL ν z).le.trans hr
  exact (P5s_entry_le_norm _ x y).trans
    ((norm_pow_le _ k).trans (pow_le_pow_left₀ (norm_nonneg _) hK k))

private theorem P5s_pow_succ_entry_le (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (ν : ℂ) {r : ℝ}
    (hr : 2 * (d : ℝ) * ‖ν‖ ≤ r) (k : ℕ) (a : Zd d L) :
    ‖((ν • P5s_adj d L) ^ (k + 1)) 0 a‖ ≤ 2 * (d : ℝ) * ‖ν‖ * r ^ k := by
  rw [pow_succ', Matrix.mul_apply]
  calc ‖∑ b, (ν • P5s_adj d L) 0 b * ((ν • P5s_adj d L) ^ k) b a‖
      ≤ ∑ b, ‖(ν • P5s_adj d L) 0 b * ((ν • P5s_adj d L) ^ k) b a‖ := norm_sum_le _ _
    _ ≤ ∑ b, ‖(ν • P5s_adj d L) 0 b‖ * r ^ k := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (P5s_pow_entry_le d L hL ν hr k b a) (norm_nonneg _)
    _ = 2 * (d : ℝ) * ‖ν‖ * r ^ k := by
        rw [← Finset.sum_mul, P5s_rowsum_adj d L hL ν 0]

private theorem P5s_pow_entry_zero (d L : ℕ) [NeZero L] (ν : ℂ) (k : ℕ) (x y : Zd d L)
    (h : k < zdistD d L (x - y)) : ((ν • P5s_adj d L) ^ k) x y = 0 := by
  rw [smul_pow, Matrix.smul_apply, P5s_adj_pow_eq_zero d L k x y h, smul_zero]

/-! ### The core estimate, for a unit spectral parameter `μ` with a gap -/

/-- `|Θ_{tμ}(0,a)| ≤ κ⁻¹ (1-r₂)⁻¹ (1_{a=0} + (2dg²/(κ r)) θ^{|a|})`, `r₂ = (1+r)/2`, `θ = r/r₂`,
provided the gap `κ ≤ |1 - tsμ|` and the ratio bound `t(1-s) ≤ r |1 - tsμ|` hold. -/
private theorem P5s_core (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g t : ℝ) (hg : 0 < g) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (μ : ℂ) (hμ : ‖μ‖ = 1) (κ r : ℝ) (hκ : 0 < κ) (hr0 : 0 < r) (hr1 : r < 1)
    (hgap : κ ≤ ‖1 - ((t : ℂ) * μ) * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ)‖)
    (hrho : t * (1 - (1 + 2 * (d : ℝ) * g ^ 2)⁻¹)
      ≤ r * ‖1 - ((t : ℂ) * μ) * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ)‖)
    (a : Zd d L) :
    ‖Theta d L g ((t : ℂ) * μ) 0 a‖ ≤ κ⁻¹ * (1 - (1 + r) / 2)⁻¹ *
      ((if a = 0 then (1 : ℝ) else 0) +
        (2 * d * g ^ 2 / (κ * r)) * (r / ((1 + r) / 2)) ^ zdistD d L a) := by
  set s : ℝ := (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ with hs
  set ξ : ℂ := (t : ℂ) * μ with hξdef
  set w : ℂ := 1 - ξ * (s : ℂ) with hwdef
  have hξn : ‖ξ‖ = t := by
    rw [hξdef, norm_mul, hμ, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]
  have hξ1 : ‖ξ‖ < 1 := by rw [hξn]; exact ht1
  have hA0 : 0 < ‖w‖ := lt_of_lt_of_le hκ hgap
  have hw : w ≠ 0 := norm_pos_iff.mp hA0
  have hpos : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  have hs0 : 0 < s := inv_pos.mpr hpos
  have hs1 : s ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg g, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hsid : 2 * (d : ℝ) * (g ^ 2 * s) = 1 - s := by
    rw [hs]
    field_simp
    ring
  set ν : ℂ := (ξ * ((g ^ 2 * s : ℝ) : ℂ)) / w with hν
  have hKdef : P5s_K d L g ξ = ν • P5s_adj d L := rfl
  have hνn : ‖ν‖ = t * (g ^ 2 * s) / ‖w‖ := by
    rw [hν, norm_div, norm_mul, hξn, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hρ : 2 * (d : ℝ) * ‖ν‖ = t * (1 - s) / ‖w‖ := by
    rw [hνn, ← hsid]
    ring
  have hρr : 2 * (d : ℝ) * ‖ν‖ ≤ r := by
    rw [hρ, div_le_iff₀ hA0]
    linarith
  have hts : t * s ≤ 1 := by nlinarith
  have hρE : 2 * (d : ℝ) * ‖ν‖ ≤ 2 * d * g ^ 2 / κ := by
    rw [hνn]
    have h2 : 2 * (d : ℝ) * (t * (g ^ 2 * s) / ‖w‖) = (2 * d * g ^ 2) * (t * s) / ‖w‖ := by
      ring
    rw [h2]
    have h0 : 0 ≤ 2 * (d : ℝ) * g ^ 2 := by positivity
    calc (2 * (d : ℝ) * g ^ 2) * (t * s) / ‖w‖ ≤ (2 * (d : ℝ) * g ^ 2) * 1 / ‖w‖ := by
          gcongr
      _ ≤ 2 * d * g ^ 2 / κ := by
          rw [mul_one]
          exact div_le_div_of_nonneg_left h0 hκ hgap
  have hKlt : ‖P5s_K d L g ξ‖ < 1 := by
    have hK : ‖ν • P5s_adj d L‖ ≤ r :=
      P5s_norm_le _ hr0.le fun z => (P5s_rowsum_adj d L hL ν z).le.trans hρr
    rw [hKdef]
    exact lt_of_le_of_lt hK hr1
  have hΘ := P5s_Theta_apply d L hL g hξ1 hw hKlt a
  rw [hKdef] at hΘ
  -- the geometric majorant
  set r₂ : ℝ := (1 + r) / 2 with hr₂
  have hr₂0 : 0 < r₂ := by rw [hr₂]; positivity
  have hr₂1 : r₂ < 1 := by rw [hr₂]; linarith
  have hrr₂ : r < r₂ := by rw [hr₂]; linarith
  set θ : ℝ := r / r₂ with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hr₂0]; exact hrr₂.le
  have hrθ : r = r₂ * θ := by rw [hθdef]; field_simp
  set n := zdistD d L a with hn
  set E' : ℝ := 2 * d * g ^ 2 / (κ * r) with hE'
  have hE'0 : 0 ≤ E' := by positivity
  have hent : ∀ j : ℕ, ‖((ν • P5s_adj d L) ^ j) 0 a‖
      ≤ ((if a = 0 then (1 : ℝ) else 0) + E' * θ ^ n) * r₂ ^ j := by
    intro j
    have hpow0 : 0 ≤ (E' * θ ^ n) * r₂ ^ j := by positivity
    cases j with
    | zero =>
      by_cases ha : a = 0
      · have hι : (if a = 0 then (1 : ℝ) else 0) = 1 := by simp [ha]
        rw [hι, ha]
        simp only [pow_zero, mul_one, one_apply_eq, norm_one, le_add_iff_nonneg_right]
        positivity
      · have : (0 : Zd d L) ≠ a := fun h => ha h.symm
        have hι : (if a = 0 then (1 : ℝ) else 0) = 0 := by simp [ha]
        rw [hι]
        simp only [pow_zero, zero_add, mul_one, Matrix.one_apply_ne this, norm_zero]
        positivity
    | succ k =>
      by_cases ha : a = 0
      · have h1 := P5s_pow_entry_le d L hL ν hρr (k + 1) 0 a
        have h2 : r ^ (k + 1) ≤ r₂ ^ (k + 1) := pow_le_pow_left₀ hr0.le hrr₂.le _
        have hι : (if a = 0 then (1 : ℝ) else 0) = 1 := by simp [ha]
        rw [hι]
        calc ‖((ν • P5s_adj d L) ^ (k + 1)) 0 a‖ ≤ r₂ ^ (k + 1) := h1.trans h2
          _ ≤ (1 + E' * θ ^ n) * r₂ ^ (k + 1) := by
              have : 0 ≤ E' * θ ^ n := by positivity
              nlinarith [pow_pos hr₂0 (k + 1)]
      · by_cases hk : k + 1 < n
        · have hz := P5s_pow_entry_zero d L ν (k + 1) 0 a (by rw [zero_sub, zdistD_neg]; exact hk)
          have hι : (if a = 0 then (1 : ℝ) else 0) = 0 := by simp [ha]
          rw [hz, norm_zero, hι, zero_add]
          positivity
        · have hnk : n ≤ k + 1 := not_lt.mp hk
          have h1 := P5s_pow_succ_entry_le d L hL ν hρr k a
          have h3 : 2 * (d : ℝ) * ‖ν‖ * r ^ k ≤ (2 * d * g ^ 2 / κ) * r ^ k :=
            mul_le_mul_of_nonneg_right hρE (by positivity)
          have h4 : (2 * d * g ^ 2 / κ) * r ^ k = E' * r ^ (k + 1) := by
            rw [hE']
            field_simp
            ring
          have h5 : r ^ (k + 1) = r₂ ^ (k + 1) * θ ^ (k + 1) := by
            rw [← mul_pow, ← hrθ]
          have h6 : θ ^ (k + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0 hθ1 hnk
          have hι : (if a = 0 then (1 : ℝ) else 0) = 0 := by simp [ha]
          rw [hι, zero_add]
          calc ‖((ν • P5s_adj d L) ^ (k + 1)) 0 a‖ ≤ 2 * (d : ℝ) * ‖ν‖ * r ^ k := h1
            _ ≤ E' * r ^ (k + 1) := h3.trans h4.le
            _ = E' * (r₂ ^ (k + 1) * θ ^ (k + 1)) := by rw [h5]
            _ ≤ E' * (r₂ ^ (k + 1) * θ ^ n) := by gcongr
            _ = E' * θ ^ n * r₂ ^ (k + 1) := by ring
  have hsum : Summable (fun j : ℕ =>
      ((if a = 0 then (1 : ℝ) else 0) + E' * θ ^ n) * r₂ ^ j) :=
    (summable_geometric_of_lt_one hr₂0.le hr₂1).mul_left _
  have hbd := norm_tsum_le_of_le hsum hent
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr₂0.le hr₂1] at hbd
  have hw1 : ‖w⁻¹‖ ≤ κ⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hκ hgap
  rw [hΘ, norm_mul]
  calc _ ≤ κ⁻¹ * (((if a = 0 then (1 : ℝ) else 0) + E' * θ ^ n) * (1 - r₂)⁻¹) :=
        mul_le_mul hw1 hbd (norm_nonneg _) (inv_nonneg.mpr hκ.le)
    _ = _ := by ring

/-! ### The gap and the ratio for `μ = m(σ)²` -/

private theorem P5s_norm_spin (m : ℂ) (hm : ‖m‖ = 1) (σ : Bool) : ‖PropSpin m σ‖ = 1 := by
  cases σ <;> simp [PropSpin, hm]

/-- `|1 - xμ|² = (1-x)² + 4x (Im m)²` for `μ = m(σ)²`, `‖m‖ = 1`. -/
private theorem P5s_gap_sq (m : ℂ) (hm : ‖m‖ = 1) (σ : Bool) (x : ℝ) :
    ‖1 - (x : ℂ) * (PropSpin m σ * PropSpin m σ)‖ ^ 2 = (1 - x) ^ 2 + 4 * x * m.im ^ 2 := by
  have hm2 : m.re ^ 2 + m.im ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hm
    simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    nlinarith [h]
  rw [Complex.sq_norm, Complex.normSq_apply]
  cases σ
  · simp only [PropSpin, Bool.false_eq_true, ite_false, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_im, Complex.one_im, Complex.mul_im]
    linear_combination (-2 * x + x ^ 2 * (m.re ^ 2 + m.im ^ 2 + 1)) * hm2
  · simp only [PropSpin, ite_true, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
    linear_combination (-2 * x + x ^ 2 * (m.re ^ 2 + m.im ^ 2 + 1)) * hm2

/-- The real arithmetic of the gap `κ' ≤ A` and the ratio `t(1-s) ≤ r A`, with `A² = (1-ts)² +
4ts u`, `u ≥ κ'²`, `s ≥ s_min`, `q = (1 + 4 s_min κ'²)⁻¹`, `r = (1+q)/2`. -/
private theorem P5s_arith (t s smin κ' u A q r : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hsmin : smin ≤ s) (hsmin0 : 0 < smin) (hκ'0 : 0 < κ') (hκ'1 : κ' ≤ 1)
    (hu : κ' ^ 2 ≤ u) (hA0 : 0 ≤ A) (hA2 : A ^ 2 = (1 - t * s) ^ 2 + 4 * (t * s) * u)
    (hq : q = (1 + 4 * smin * κ' ^ 2)⁻¹) (hr : r = (1 + q) / 2) :
    κ' ≤ A ∧ t * (1 - s) ≤ r * A := by
  have hts0 : 0 ≤ t * s := mul_nonneg ht0 hs0.le
  have hts1 : t * s < 1 := by nlinarith
  have hκ'2 : κ' ^ 2 ≤ 1 := pow_le_one₀ hκ'0.le hκ'1
  have hgap : κ' ≤ A := by
    refine (pow_le_pow_iff_left₀ hκ'0.le hA0 two_ne_zero).mp ?_
    rw [hA2]
    have h1 : κ' ^ 2 * (1 - t * s) ^ 2 ≤ (1 - t * s) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hκ'2
    have h2 : 4 * (t * s) * κ' ^ 2 ≤ 4 * (t * s) * u :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    nlinarith [mul_nonneg (sq_nonneg κ') hts0, mul_nonneg (sq_nonneg κ') (sq_nonneg (t * s))]
  refine ⟨hgap, ?_⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have hP0 : 0 ≤ t * (1 - s) := mul_nonneg ht0 (by linarith)
  have hP1 : (t * (1 - s)) ^ 2 ≤ (1 - t * s) ^ 2 := by
    have : t * (1 - s) ≤ 1 - t * s := by nlinarith
    exact pow_le_pow_left₀ hP0 this 2
  have hP2 : (t * (1 - s)) ^ 2 ≤ t := by
    have h1 : t * (1 - s) ≤ t := by nlinarith
    nlinarith
  have hP3 : (t * (1 - s)) ^ 2 * (smin * κ' ^ 2) ≤ t * s * u := by
    calc (t * (1 - s)) ^ 2 * (smin * κ' ^ 2) ≤ t * (s * u) := by gcongr
      _ = t * s * u := by ring
  have hP4 : (t * (1 - s)) ^ 2 * (1 + 4 * smin * κ' ^ 2) ≤ A ^ 2 := by
    rw [hA2]
    nlinarith
  have hP5 : (t * (1 - s)) ^ 2 ≤ q * A ^ 2 := by
    rw [hq, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    exact hP4
  by_contra hcon
  push Not at hcon
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have h1 : (r * A) ^ 2 < (t * (1 - s)) ^ 2 :=
    pow_lt_pow_left₀ hcon (mul_nonneg hr0 hA0) two_ne_zero
  have hrq : q ≤ r ^ 2 := by rw [hr]; nlinarith [sq_nonneg (1 - q)]
  nlinarith [mul_le_mul_of_nonneg_right hrq (sq_nonneg A)]

private theorem P5s_final (M F g2 ι : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F) (hg2 : 0 ≤ g2) (hι : 0 ≤ ι) :
    M * (ι + F * g2) ≤ M * (1 + F) * (ι + g2) := by
  have h1 : 0 ≤ M * (F * ι) := by positivity
  have h2 : 0 ≤ M * g2 := by positivity
  nlinarith

/-- **`(prop:ThfadC_short)`** (`σ₁ = σ₂ = σ`): `|Θ_t(0,a)| ≤ C_κ (1_{a=0} + g² e^{-c_κ|a|})`
with `C_κ, c_κ` depending on `(d, Λ, κ)` only.  Gap + Neumann series
(`A_deterministic_estimates.tex:20-55`); constants
`κ' = min κ 1`, `s_min = (1+2dΛ²)⁻¹`, `q = (1 + 4 s_min κ'²)⁻¹`, `r = (1+q)/2`,
`r₂ = (1+r)/2`, `θ = r/r₂`, `c = -log θ`, `C = κ'⁻¹(1-r₂)⁻¹(1 + 2d/(κ' r))`. -/
theorem prop5Short_holds (d : ℕ) (Λ κ : ℝ) : Prop5Short d Λ κ := by
  intro _ hΛ hκ
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, κ' = min κ 1 := ⟨_, rfl⟩
  have hκ'0 : 0 < κ' := by rw [hκ']; exact lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := by rw [hκ']; exact min_le_right _ _
  have hκ'κ : κ' ≤ κ := by rw [hκ']; exact min_le_left _ _
  obtain ⟨smin, hsmin⟩ : ∃ smin : ℝ, smin = (1 + 2 * (d : ℝ) * Λ ^ 2)⁻¹ := ⟨_, rfl⟩
  have hsmin0 : 0 < smin := by rw [hsmin]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 + 4 * smin * κ' ^ 2)⁻¹ := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq]
    exact inv_lt_one_of_one_lt₀ (by nlinarith [mul_pos hsmin0 (pow_pos hκ'0 2)])
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 + q) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : ℝ, r₂ = (1 + r) / 2 := ⟨_, rfl⟩
  have hr₂0 : 0 < r₂ := by rw [hr₂]; positivity
  have hr₂1 : r₂ < 1 := by rw [hr₂]; linarith
  have hrr₂ : r < r₂ := by rw [hr₂]; linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = r / r₂ := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hr₂0]; exact hrr₂
  have h1r₂ : 0 < 1 - r₂ := by linarith
  have hM : 0 ≤ κ'⁻¹ * (1 - r₂)⁻¹ := by positivity
  refine ⟨κ'⁻¹ * (1 - r₂)⁻¹ * (1 + 2 * d / (κ' * r)), by positivity, -Real.log θ,
    neg_pos.mpr (Real.log_neg hθ0 hθ1), ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 m hm hκm σ a
  have : NeZero L := ⟨by omega⟩
  have hμ : ‖PropSpin m σ * PropSpin m σ‖ = 1 := by
    rw [norm_mul, P5s_norm_spin m hm σ, one_mul]
  have hpos : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  have hs0 : 0 < (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := inv_pos.mpr hpos
  have hs1 : (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg g, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hsmin_le : smin ≤ (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by
    rw [hsmin]
    refine inv_anti₀ hpos ?_
    have : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hwc : ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) * (((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ)
      = ((t * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ) * (PropSpin m σ * PropSpin m σ) := by
    push_cast
    ring
  have hA2 := P5s_gap_sq m hm σ (t * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹)
  rw [← hwc] at hA2
  have hu : κ' ^ 2 ≤ m.im ^ 2 := pow_le_pow_left₀ hκ'0.le (hκ'κ.trans hκm) 2
  obtain ⟨hgap, hrho⟩ := P5s_arith t _ smin κ' (m.im ^ 2) _ q r ht0 ht1 hs0 hs1 hsmin_le hsmin0
    hκ'0 hκ'1 hu (norm_nonneg _) hA2 hq hr
  have key := P5s_core d L hL g t hg ht0 ht1 _ hμ κ' r hκ'0 hr0 hr1 hgap hrho a
  have hexp : Real.exp (-(-Real.log θ) * (zdistD d L a : ℝ)) = θ ^ zdistD d L a := by
    rw [neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hθ0]
  rw [hexp]
  have hι : 0 ≤ (if a = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hF : 0 ≤ 2 * (d : ℝ) / (κ' * r) := by positivity
  have hg2 : 0 ≤ g ^ 2 * θ ^ zdistD d L a := by positivity
  refine key.trans ?_
  have hfin := P5s_final (κ'⁻¹ * (1 - r₂)⁻¹) (2 * (d : ℝ) / (κ' * r))
    (g ^ 2 * θ ^ zdistD d L a) (if a = 0 then (1 : ℝ) else 0) hM hF hg2 hι
  refine le_trans (le_of_eq ?_) hfin
  rw [← hr₂, ← hθ]
  ring

/-! ### Compiled nonempty instances

`prop5Short_holds 3 1 (1/2)` applied at `L = 5`, `g = 1/2`, `t = 9/10`, `m = I` (`‖I‖ = 1`,
`1/2 ≤ Im I = 1`), `σ = true` (`ξ = t m²`), at `a = 0` and at `a = (1,0,0) ≠ 0`, `|a| = 1`;
every hypothesis is discharged. -/

example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
        0 0‖
      ≤ C * ((if (0 : Zd 3 5) = 0 then (1 : ℝ) else 0)
        + (1 / 2 : ℝ) ^ 2 * Real.exp (-c * (zdistD 3 5 (0 : Zd 3 5) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Short_holds 3 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨C, hC, c, hc, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) Complex.I Complex.norm_I (by norm_num) true 0⟩

example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ (![1, 0, 0] : Zd 3 5) ≠ 0
    ∧ zdistD 3 5 (![1, 0, 0] : Zd 3 5) = 1 ∧
    ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
        0 ![1, 0, 0]‖
      ≤ C * ((if (![1, 0, 0] : Zd 3 5) = 0 then (1 : ℝ) else 0)
        + (1 / 2 : ℝ) ^ 2 * Real.exp (-c * (zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Short_holds 3 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨C, hC, c, hc, by decide, by decide, H 5 (by norm_num) (1 / 2) (by norm_num)
    (by norm_num) (9 / 10) (by norm_num) (by norm_num) Complex.I Complex.norm_I (by norm_num)
    true ![1, 0, 0]⟩

/-- The pin proves the merged consumer interface `ThetaDecayShort` for every `d`, `g`, `m`
(`Loop/*` and `Kernel/*` assume it). -/
example : ∀ (d : ℕ) (g : ℝ) (m : ℂ), ThetaDecayShort d g m :=
  fun d g m => (prop5Short_holds d g m.im).thetaDecayShort

example : ThetaDecayShort 3 (1 / 2) Complex.I :=
  (prop5Short_holds 3 (1 / 2) Complex.I.im).thetaDecayShort

/-- With `Prop5Decay` and `Prop8ZeroMode` still hypotheses, the bundle `Prop5to8` has its
`short` field proved. -/
example (h5 : Prop5Decay 3 1) (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2))
    (h7 : Prop7Diff2 3 1 (1 / 2) (1 / 2)) (h8 : Prop8ZeroMode 3 1 (1 / 2)) :
    Prop5to8 3 1 (1 / 2) (1 / 2) :=
  ⟨h5, prop5Short_holds 3 1 (1 / 2), h6, h7, h8⟩

end RBM
