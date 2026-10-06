/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Ward

/-!
# The Combes-Thomas item of `lem:propM` for the block Anderson model (BA-D4)

Ticket T2290.  Paper `7_8_light_weight.tex:1847-1912` (`lem:propM`, item (3), `(Mbound_AO)` `:1891`,
`(Mbound_AO2)` `:1902`).  The bounds on `M^{(B)} = (g Ψ^{(B)} - E - m)⁻¹` and the merged pin
`BAPropM` (`RBM3D/BA/MFixedPoint.lean`, all items) from `baPropM12_holds` (`Ward.lean`),
unconditionally.

The one analytic estimate is `BAMB_ct_core`: for `Im w ≥ κ`, `w = z + m`, and a weight
`e^{ν |x - b|}` with `2 d g (e^ν - 1) ≤ κ/2`, the column `M_{· b}` obeys
`|M_ab| ≤ (2/κ) e^{-ν |a - b|}` (the weighted `ℓ²` resolvent bound plus a Schur bound on the
torus; no Taylor series, no `Matrix` norm instance).  Both halves of `(Mbound_AO)` and
`(Mbound_AO2)` follow from the core at `ν = log((C₁ g)⁻¹)`, resp. `ν = log(1 + κ/(4dΛ))`.

Constants: `C = 16 d² / κ³` (depends on `d, κ`), `c = min (log (1 + κ/(4dΛ))) (κ/2)` (depends on
`d, Λ, κ`).  No statement mentions a law.  Premises not used: `(2C)⁻¹ ≤ g` in `BAMB_decay_large`;
`3 ≤ d` beyond `0 < d`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The constants -/

/-- The constant `C` of `(Mbound_AO)` (`7_8:1888-1891`; "depending only on `d` and `κ`"): `C = 16 d² / κ³`. -/
def BAct_C (d : ℕ) (κ : ℝ) : ℝ := 16 * (d : ℝ) ^ 2 / κ ^ 3

/-- The rate `c` of `(Mbound_AO2)` (`7_8:1902`): `c = min (log (1 + κ/(4dΛ))) (κ/2)`. -/
def BAct_rate (d : ℕ) (Λ κ : ℝ) : ℝ := min (Real.log (1 + κ / (4 * (d : ℝ) * Λ))) (κ / 2)

theorem BAct_C_pos (d : ℕ) (κ : ℝ) (hd : 0 < d) (hκ : 0 < κ) : 0 < BAct_C d κ := by
  unfold BAct_C
  have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  positivity

theorem BAct_rate_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAct_rate d Λ κ := by
  unfold BAct_rate
  have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  refine lt_min (Real.log_pos ?_) (by positivity)
  have : 0 < κ / (4 * (d : ℝ) * Λ) := by positivity
  linarith

/-! ## 2. Edge-Lipschitz weight and the row equation -/

section Row

variable (d L : ℕ) [NeZero L]

private theorem CT_adj_symm (x y : Zd d L) (h : Adj d L x y) : Adj d L y x := by
  simp only [Adj] at h ⊢
  rw [show y - x = -(x - y) by ring, zdistD_neg]
  exact h

/-- `x ↦ |x - b|` is 1-Lipschitz along edges (any `L`). -/
theorem BAzdist_adj_lip (x y b : Zd d L) (h : Adj d L x y) :
    zdistD d L (x - b) ≤ zdistD d L (y - b) + 1 := by
  have h1 : x - b = (x - y) + (y - b) := by ring
  have h2 := zdistD_add_le d L (x - y) (y - b)
  have h3 : zdistD d L (x - y) = 1 := h
  rw [h1]
  omega

/-- The entries of `(g Ψ - w) M = 1`, `w = z + m`, `Im w ≠ 0`. -/
theorem BAMB_resolvent_row (g : ℝ) (z m : ℂ) (hz : (z + m).im ≠ 0) (a b : Zd d L) :
    (g : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), BAMB d L g z m c b
        - (z + m) * BAMB d L g z m a b = if a = b then 1 else 0 := by
  have hunit := isUnit_sub_smul_of_isHermitian (BAPsi_isHermitian d L g) hz
  set A : Matrix (Zd d L) (Zd d L) ℂ := (g : ℂ) • PsiB d L - (z + m) • 1 with hA
  have hB : BAMB d L g z m = Ring.inverse A := rfl
  set G := Ring.inverse A with hG
  have hmul : A * G = 1 := Ring.mul_inverse_cancel _ hunit
  have hAe : ∀ a c : Zd d L, A a c = (g : ℂ) * (if Adj d L a c then 1 else 0) - (z + m) * (if a = c then 1 else 0) := by
    intro a c
    simp [hA, PsiB, Matrix.one_apply]
  have hentry := congrFun (congrFun hmul a) b
  rw [Matrix.mul_apply] at hentry
  simp only [hAe, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at hentry
  rw [hB]
  rw [Matrix.one_apply] at hentry
  have e1 : ∑ i, (if Adj d L a i then (1 : ℂ) else 0) * G i b
      = ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), G c b := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp
  have e2 : ∑ i, (if a = i then (1 : ℂ) else 0) * G i b = G a b := by
    simp [ite_mul, Finset.sum_ite_eq]
  rw [e1, e2] at hentry
  exact hentry

end Row


/-! ## 3. The Combes-Thomas core -/

private theorem CT_exp_sub_one_le (ν s : ℝ) (hν : 0 ≤ ν) (hs : |s| ≤ 1) :
    |Real.exp (ν * s) - 1| ≤ Real.exp ν - 1 := by
  rcases abs_le.mp hs with ⟨hs1, hs2⟩
  rcases le_or_gt 0 s with h0 | h0
  · have h1 : 1 ≤ Real.exp (ν * s) := Real.one_le_exp (mul_nonneg hν h0)
    have h2 : Real.exp (ν * s) ≤ Real.exp ν := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h1 : Real.exp (ν * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : Real.exp (-ν) ≤ Real.exp (ν * s) := Real.exp_le_exp.mpr (by nlinarith)
    have h3 := Real.add_one_le_exp (-ν)
    have h4 := Real.add_one_le_exp ν
    rw [abs_of_nonpos (by linarith)]
    linarith

section Core

variable (d L : ℕ) [NeZero L]

/-- Summing a function over the neighbours of `x` and then over `x` counts each point `2d` times. -/
private theorem CT_sum_adj (hL : 3 ≤ L) (f : Zd d L → ℝ) :
    ∑ x : Zd d L, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), f c
      = 2 * (d : ℝ) * ∑ c : Zd d L, f c := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : ∑ x : Zd d L, (if Adj d L x c then f c else 0)
      = ∑ x ∈ Finset.univ.filter (fun x : Zd d L => Adj d L c x), f c := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : Adj d L c x
    · simp [h, CT_adj_symm d L c x h]
    · have : ¬ Adj d L x c := fun h' => h (CT_adj_symm d L x c h')
      simp [h, this]
  rw [h1, Finset.sum_const, card_adj d L hL c, nsmul_eq_mul]
  push_cast
  ring


/-- The abstract Combes-Thomas estimate: a column `u` of `(gΨ - w)⁻¹` (row equation `hrow`), `Im w ≥ κ`,
weight `e^{ν |x - b|}` with `2 d g (e^ν - 1) ≤ κ/2`. -/
private theorem CT_core_abs (hL : 3 ≤ L) (g κ ν : ℝ) (w : ℂ) (hg : 0 ≤ g) (hκ : 0 < κ)
    (hw : κ ≤ w.im) (hν : 0 ≤ ν) (hgap : 2 * (d : ℝ) * g * (Real.exp ν - 1) ≤ κ / 2)
    (b : Zd d L) (u : Zd d L → ℂ)
    (hrow : ∀ x : Zd d L, (g : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), u c
        - w * u x = if x = b then 1 else 0) (a : Zd d L) :
    ‖u a‖ ≤ 2 / κ * Real.exp (-(ν * (zdistD d L (a - b) : ℝ))) := by
  classical
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Zd d L → ℝ, ∀ x, ψ x = (zdistD d L (x - b) : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Zd d L → ℝ, ∀ x, E x = Real.exp (ν * ψ x) := ⟨_, fun _ => rfl⟩
  obtain ⟨kk, hkk⟩ : ∃ kk : Zd d L → Zd d L → ℝ, ∀ x c, kk x c = Real.exp (ν * (ψ x - ψ c)) - 1 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨vf, hvf⟩ : ∃ vf : Zd d L → ℂ, ∀ x, vf x = (E x : ℂ) * u x := ⟨_, fun _ => rfl⟩
  obtain ⟨Kf, hKf⟩ : ∃ Kf : Zd d L → ℂ, ∀ x, Kf x = (g : ℂ) *
      ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), (kk x c : ℂ) * vf c := ⟨_, fun _ => rfl⟩
  have hψb : ψ b = 0 := by rw [hψ]; simp
  have hEpos : ∀ x, 0 < E x := fun x => by rw [hE]; exact Real.exp_pos _
  -- the weighted row equation
  have hkE : ∀ x c, (kk x c : ℂ) * (E c : ℂ) = (E x : ℂ) - (E c : ℂ) := by
    intro x c
    have : kk x c * E c = E x - E c := by
      simp only [hkk, hE]
      rw [sub_mul, ← Real.exp_add, one_mul]
      congr 2
      ring
    exact_mod_cast this
  have hcoord : ∀ x, (g : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), vf c
      - w * vf x = (if x = b then 1 else 0) - Kf x := by
    intro x
    have h1 : (E x : ℂ) * ((g : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), u c
        - w * u x) = (E x : ℂ) * (if x = b then 1 else 0) := by rw [hrow x]
    have hEx : (E x : ℂ) * (if x = b then 1 else 0) = if x = b then 1 else 0 := by
      split_ifs with h
      · subst h; simp [hE, hψb]
      · simp
    rw [hEx, mul_sub] at h1
    have h2 : ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), (kk x c : ℂ) * vf c
        = (E x : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), u c
          - ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), (E c : ℂ) * u c := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hvf, ← mul_assoc, hkE]
      ring
    rw [hKf, h2, hvf x]
    simp only [hvf]
    linear_combination h1
  -- the Euclidean vectors
  have hkey : Matrix.toEuclideanLin ((g : ℂ) • PsiB d L) (WithLp.toLp 2 vf) - w • (WithLp.toLp 2 vf)
      = EuclideanSpace.single b (1 : ℂ) - WithLp.toLp 2 Kf := by
    ext x
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PsiB]
    rw [← hcoord x, Finset.sum_filter, Finset.mul_sum]
    simp only [mul_ite, mul_zero]
  have hlow := norm_sub_smul_ge_of_isHermitian (BAPsi_isHermitian d L g) w (WithLp.toLp 2 vf)
  rw [hkey] at hlow
  -- the Schur bound on `K`
  have hlip : ∀ x c : Zd d L, Adj d L x c → |ψ x - ψ c| ≤ 1 := by
    intro x c hxc
    have h1 := BAzdist_adj_lip d L x c b hxc
    have h2 := BAzdist_adj_lip d L c x b (CT_adj_symm d L x c hxc)
    rw [hψ, hψ, abs_le]
    constructor
    · have : (zdistD d L (c - b) : ℝ) ≤ (zdistD d L (x - b) : ℝ) + 1 := by exact_mod_cast h2
      linarith
    · have : (zdistD d L (x - b) : ℝ) ≤ (zdistD d L (c - b) : ℝ) + 1 := by exact_mod_cast h1
      linarith
  have hkk_le : ∀ x c : Zd d L, Adj d L x c → |kk x c| ≤ Real.exp ν - 1 := by
    intro x c hxc
    rw [hkk]
    exact CT_exp_sub_one_le ν _ hν (hlip x c hxc)
  set ρ : ℝ := g * (Real.exp ν - 1) with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg hg (by linarith [Real.add_one_le_exp ν])
  have hKx : ∀ x, ‖Kf x‖ ≤ ρ * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), ‖vf c‖ := by
    intro x
    rw [hKf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg, hρ, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hg
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hkk_le x c (Finset.mem_filter.mp hc).2) (norm_nonneg _)
  have hKx2 : ∀ x, ‖Kf x‖ ^ 2 ≤ ρ ^ 2 * (2 * (d : ℝ)) *
      ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), ‖vf c‖ ^ 2 := by
    intro x
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.filter (fun c : Zd d L => Adj d L x c))
      (fun _ => (1 : ℝ)) (fun c => ‖vf c‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    rw [card_adj d L hL x] at h1
    have h2 : ‖Kf x‖ ^ 2 ≤ (ρ * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), ‖vf c‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hKx x) 2
    refine h2.trans ?_
    rw [mul_pow, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    push_cast at h1
    exact h1
  have hK2 : ‖WithLp.toLp 2 Kf‖ ^ 2 ≤ (2 * (d : ℝ) * ρ * ‖WithLp.toLp 2 vf‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq (WithLp.toLp 2 vf), EuclideanSpace.norm_sq_eq (WithLp.toLp 2 Kf)]
    simp only [WithLp.ofLp_toLp]
    calc ∑ x, ‖Kf x‖ ^ 2
        ≤ ∑ x : Zd d L, ρ ^ 2 * (2 * (d : ℝ)) *
            ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L x c), ‖vf c‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => hKx2 x
      _ = ρ ^ 2 * (2 * (d : ℝ)) * (2 * (d : ℝ) * ∑ c, ‖vf c‖ ^ 2) := by
          rw [← Finset.mul_sum, CT_sum_adj d L hL (fun c => ‖vf c‖ ^ 2)]
      _ = (2 * (d : ℝ) * ρ) ^ 2 * ∑ c, ‖vf c‖ ^ 2 := by ring
  have hρd : 2 * (d : ℝ) * ρ ≤ κ / 2 := by rw [hρ]; linarith
  have hKle : ‖WithLp.toLp 2 Kf‖ ≤ κ / 2 * ‖WithLp.toLp 2 vf‖ := by
    have h0 : 0 ≤ 2 * (d : ℝ) * ρ * ‖WithLp.toLp 2 vf‖ := by positivity
    have := (abs_le_of_sq_le_sq' hK2 h0).2
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right hρd (norm_nonneg _)
  -- conclusion
  have hv_le : ‖WithLp.toLp 2 vf‖ ≤ 2 / κ := by
    have h1 : κ * ‖WithLp.toLp 2 vf‖ ≤ |w.im| * ‖WithLp.toLp 2 vf‖ :=
      mul_le_mul_of_nonneg_right (hw.trans (le_abs_self _)) (norm_nonneg _)
    have h2 : ‖EuclideanSpace.single b (1 : ℂ) - WithLp.toLp 2 Kf‖ ≤ 1 + ‖WithLp.toLp 2 Kf‖ := by
      refine (norm_sub_le _ _).trans ?_
      have : ‖EuclideanSpace.single b (1 : ℂ)‖ = 1 := by simp
      rw [this]
    rw [le_div_iff₀ hκ]
    nlinarith
  have hva : ‖vf a‖ ≤ 2 / κ := by
    have := PiLp.norm_apply_le (WithLp.toLp 2 vf) a
    simpa using this.trans hv_le
  have hua : ‖vf a‖ = E a * ‖u a‖ := by
    rw [hvf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hEpos a)]
  have hEa : Real.exp (-(ν * (zdistD d L (a - b) : ℝ))) = (E a)⁻¹ := by
    rw [hE, hψ, Real.exp_neg]
  rw [hEa]
  rw [hua] at hva
  rw [← div_eq_mul_inv, le_div_iff₀ (hEpos a)]
  have : ‖u a‖ * E a = E a * ‖u a‖ := mul_comm _ _
  rw [this]
  exact hva

/-- **The Combes-Thomas estimate** for `M = (g Ψ^{(B)} - w)⁻¹`, `w = z + m`, `Im w ≥ κ`, weight `e^{ν |x - b|}`
(`7_8:1911`, `[Aizenman_book, Thm 10.5]`): `|M_ab| ≤ (2/κ) e^{-ν |a - b|}` when `2 d g (e^ν - 1) ≤ κ/2`. -/
theorem BAMB_ct_core (hL : 3 ≤ L) (g κ ν : ℝ) (z m : ℂ) (hg : 0 ≤ g) (hκ : 0 < κ)
    (hw : κ ≤ (z + m).im) (hν : 0 ≤ ν) (hgap : 2 * (d : ℝ) * g * (Real.exp ν - 1) ≤ κ / 2)
    (a b : Zd d L) :
    ‖BAMB d L g z m a b‖ ≤ 2 / κ * Real.exp (-(ν * (zdistD d L (a - b) : ℝ))) :=
  CT_core_abs d L hL g κ ν (z + m) hg hκ hw hν hgap b (fun c => BAMB d L g z m c b)
    (fun x => BAMB_resolvent_row d L g z m (by linarith) x b) a

end Core

/-! ## 4. The two halves of `(Mbound_AO)` and `(Mbound_AO2)` -/

section Bounds

variable (d L : ℕ) [NeZero L]

private theorem CT_norm_m (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) : κ ≤ ‖m‖ ∧ ‖m‖ ≤ 1 :=
  ⟨hr.2.trans ((le_abs_self _).trans (Complex.abs_im_le_norm m)),
    BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1⟩

private theorem CT_rate_le_log (d : ℕ) (Λ κ : ℝ) :
    BAct_rate d Λ κ ≤ Real.log (1 + κ / (4 * (d : ℝ) * Λ)) := min_le_left _ _

private theorem CT_rate_le_half (d : ℕ) (Λ κ : ℝ) : BAct_rate d Λ κ ≤ κ / 2 := min_le_right _ _

/-- The smallness consequences of `g < (2C)⁻¹`, `C = 16 d² / κ³`, for `0 < κ ≤ 1`, `d ≥ 1`. -/
private theorem CT_small (d : ℕ) (hd : 0 < d) (g κ : ℝ) (hg : 0 < g) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hsm : g < (2 * BAct_C d κ)⁻¹) :
    32 * (d : ℝ) ^ 2 * g < κ ^ 3 ∧ 4 * (d : ℝ) * g ≤ κ := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hC : (2 * BAct_C d κ)⁻¹ = κ ^ 3 / (32 * (d : ℝ) ^ 2) := by
    unfold BAct_C
    field_simp
    norm_num
  rw [hC, lt_div_iff₀ (by positivity)] at hsm
  have h1 : 32 * (d : ℝ) ^ 2 * g < κ ^ 3 := by linarith
  refine ⟨h1, ?_⟩
  have hκ3 : κ ^ 3 ≤ κ := by
    have : κ ^ 3 = κ * (κ * κ) := by ring
    nlinarith [mul_pos hκ hκ]
  by_contra h
  have h := not_le.mp h
  nlinarith [mul_pos hdpos hg]

/-- `n ≥ 1`: `|M_ab| ≤ (8 d g / κ²)^n` for `g < (2C)⁻¹`. -/
private theorem CT_upper_C2 (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L)
    (hn : 1 ≤ zdistD d L (a - b)) :
    ‖BAMB d L g (E : ℂ) m a b‖ ≤ (8 * (d : ℝ) * g / κ ^ 2) ^ zdistD d L (a - b) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hκ1 : κ ≤ 1 := (CT_norm_m d L g κ E m hr).1.trans (CT_norm_m d L g κ E m hr).2
  obtain ⟨h32, h4⟩ := CT_small d hd g κ hg hκ hκ1 hsm
  set C1g : ℝ := 4 * (d : ℝ) / κ * g with hC1g
  have hC1pos : 0 < C1g := by positivity
  have hC1le : C1g ≤ 1 := by
    rw [hC1g, div_mul_eq_mul_div, div_le_one hκ]
    exact h4
  set ν : ℝ := Real.log (C1g⁻¹) with hν
  have hexp : Real.exp ν = C1g⁻¹ := Real.exp_log (inv_pos.mpr hC1pos)
  have hν0 : 0 ≤ ν := Real.log_nonneg ((one_le_inv₀ hC1pos).mpr hC1le)
  have hgap : 2 * (d : ℝ) * g * (Real.exp ν - 1) ≤ κ / 2 := by
    have h1 : 2 * (d : ℝ) * g * (Real.exp ν - 1) ≤ 2 * (d : ℝ) * g * C1g⁻¹ := by
      rw [hexp]
      have : 0 ≤ 2 * (d : ℝ) * g := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) this
    refine h1.trans (le_of_eq ?_)
    rw [hC1g]
    field_simp
    norm_num
  have hcore := BAMB_ct_core d L hL g κ ν (E : ℂ) m hg.le hκ (by simpa using hr.2) hν0 hgap a b
  have hexpn : Real.exp (-(ν * (zdistD d L (a - b) : ℝ))) = C1g ^ zdistD d L (a - b) := by
    rw [mul_comm ν, Real.exp_neg, Real.exp_nat_mul, hexp, inv_pow, inv_inv]
  rw [hexpn] at hcore
  refine hcore.trans ?_
  have h2k : 1 ≤ 2 / κ := by rw [le_div_iff₀ hκ]; linarith
  calc 2 / κ * C1g ^ zdistD d L (a - b)
      ≤ (2 / κ) ^ zdistD d L (a - b) * C1g ^ zdistD d L (a - b) :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ h2k (by omega)) (by positivity)
    _ = (8 * (d : ℝ) * g / κ ^ 2) ^ zdistD d L (a - b) := by
        rw [← mul_pow]
        congr 1
        rw [hC1g]
        field_simp
        ring

/-- The upper half of `(Mbound_AO)` at a real-axis datum, `g < (2C)⁻¹`. -/
theorem BAMB_upper_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) :
    ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_C d κ * g) ^ zdistD d L (a - b) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hκm, hm1⟩ := CT_norm_m d L g κ E m hr
  rcases Nat.eq_zero_or_pos (zdistD d L (a - b)) with h0 | h0
  · have hab : a = b := sub_eq_zero.mp ((zdistD_eq_zero_iff d L).mp h0)
    subst hab
    rw [h0, pow_zero, BAMB_diag_eq d L g (E : ℂ) m hr.1 a]
    exact hm1
  · refine (CT_upper_C2 d L hL hd g κ E m hg hκ hr hsm a b h0).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ _
    unfold BAct_C
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : κ ≤ 2 * (d : ℝ) := by linarith
    have h3 : 0 ≤ 8 * (d : ℝ) * g * κ ^ 2 * (2 * (d : ℝ) - κ) := by
      have : 0 ≤ 2 * (d : ℝ) - κ := by linarith
      positivity
    nlinarith [h3]

/-- The lower half of `(Mbound_AO)` (nearest neighbours), `g < (2C)⁻¹`. -/
theorem BAMB_lower_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) (hab : Adj d L a b) :
    (BAct_C d κ)⁻¹ * g ≤ ‖BAMB d L g (E : ℂ) m a b‖ := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  obtain ⟨hκm, hm1⟩ := CT_norm_m d L g κ E m hr
  have hκ1 : κ ≤ 1 := hκm.trans hm1
  obtain ⟨h32, h4⟩ := CT_small d hd g κ hg hκ hκ1 hsm
  have hwim : ((E : ℂ) + m).im ≠ 0 := by
    have : ((E : ℂ) + m).im = m.im := by simp
    rw [this]; have := hr.2; linarith
  have hne : a ≠ b := by
    intro h; subst h; simp [Adj] at hab
  -- the row equation at `(a, b)`
  have hrow := BAMB_resolvent_row d L g (E : ℂ) m hwim a b
  simp only [hne, ↓reduceIte] at hrow
  have hmem : b ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c) := by simpa using hab
  rw [← Finset.add_sum_erase _ _ hmem, BAMB_diag_eq d L g (E : ℂ) m hr.1 b] at hrow
  set R : ℂ := ∑ c ∈ (Finset.univ.filter (fun c : Zd d L => Adj d L a c)).erase b, BAMB d L g (E : ℂ) m c b
    with hR
  have hwM : ((E : ℂ) + m) * BAMB d L g (E : ℂ) m a b = (g : ℂ) * (m + R) := by
    linear_combination -hrow
  -- `‖R‖ < κ / 2`
  set C2 : ℝ := 8 * (d : ℝ) * g / κ ^ 2 with hC2
  have hC2nn : 0 ≤ C2 := by positivity
  have hC2lt : C2 * (4 * (d : ℝ)) < κ := by
    rw [hC2, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hC2le : C2 ≤ 1 := by nlinarith
  have hRle : ‖R‖ ≤ 2 * (d : ℝ) * C2 := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ c ∈ (Finset.univ.filter (fun c : Zd d L => Adj d L a c)).erase b,
        ‖BAMB d L g (E : ℂ) m c b‖ ≤ C2 := by
      intro c hc
      have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
      have hn : 1 ≤ zdistD d L (c - b) := by
        by_contra h0
        have h0 : zdistD d L (c - b) = 0 := by omega
        exact hcb (sub_eq_zero.mp ((zdistD_eq_zero_iff d L).mp h0))
      exact (CT_upper_C2 d L hL hd g κ E m hg hκ hr hsm c b hn).trans
        (pow_le_of_le_one hC2nn hC2le (by omega))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Finset.univ.filter (fun c : Zd d L => Adj d L a c)).erase b).card : ℝ) ≤ 2 * (d : ℝ) := by
      have := Finset.card_erase_le (s := Finset.univ.filter (fun c : Zd d L => Adj d L a c)) (a := b)
      rw [card_adj d L hL a] at this
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hcard hC2nn
  have hRlt : ‖R‖ < κ / 2 := by nlinarith
  have hmR : κ / 2 < ‖m + R‖ := by
    have h1 : ‖m‖ ≤ ‖m + R‖ + ‖R‖ := by
      have := norm_sub_le (m + R) R
      rw [add_sub_cancel_right] at this
      exact this
    linarith
  -- `‖w‖ ≤ 2 / κ`
  have hrow2 := BAMB_resolvent_row d L g (E : ℂ) m hwim a a
  simp only [↓reduceIte] at hrow2
  rw [BAMB_diag_eq d L g (E : ℂ) m hr.1 a] at hrow2
  have hM1 : ∀ c : Zd d L, ‖BAMB d L g (E : ℂ) m c a‖ ≤ 1 := by
    intro c
    rw [BAMB_symm d L g (E : ℂ) m c a]
    have h1 := BAMB_row_sq_real d L g E m hr.1 a
    have h2 : ‖BAMB d L g (E : ℂ) m a c‖ ^ 2 ≤ ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b => ‖BAMB d L g (E : ℂ) m a b‖ ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ c)
    rw [h1] at h2
    by_contra h3
    have h3 := not_le.mp h3
    nlinarith [norm_nonneg (BAMB d L g (E : ℂ) m a c)]
  have hsumM : ‖∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), BAMB d L g (E : ℂ) m c a‖
      ≤ 2 * (d : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ => hM1 c).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_adj d L hL a]
    push_cast
    simp
  have hwm : ((E : ℂ) + m) * m = (g : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c),
      BAMB d L g (E : ℂ) m c a - 1 := by
    linear_combination -hrow2
  have hwm_norm : ‖(E : ℂ) + m‖ * ‖m‖ ≤ 2 := by
    rw [← norm_mul, hwm]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg, norm_one]
    have : g * ‖∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), BAMB d L g (E : ℂ) m c a‖
        ≤ g * (2 * (d : ℝ)) := mul_le_mul_of_nonneg_left hsumM hg.le
    nlinarith
  have hwκ : κ * ‖(E : ℂ) + m‖ ≤ 2 := by
    nlinarith [norm_nonneg ((E : ℂ) + m)]
  -- conclusion
  have hnorm_eq : ‖(E : ℂ) + m‖ * ‖BAMB d L g (E : ℂ) m a b‖ = g * ‖m + R‖ := by
    rw [← norm_mul, hwM, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  have hX : g * κ ^ 2 ≤ 4 * ‖BAMB d L g (E : ℂ) m a b‖ := by
    have hXn := norm_nonneg (BAMB d L g (E : ℂ) m a b)
    have h1 : g * (κ / 2) * κ ≤ g * ‖m + R‖ * κ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmR.le hg.le) hκ.le
    have h2 : g * ‖m + R‖ * κ = κ * ‖(E : ℂ) + m‖ * ‖BAMB d L g (E : ℂ) m a b‖ := by
      rw [← hnorm_eq]; ring
    have h3 : κ * ‖(E : ℂ) + m‖ * ‖BAMB d L g (E : ℂ) m a b‖ ≤ 2 * ‖BAMB d L g (E : ℂ) m a b‖ :=
      mul_le_mul_of_nonneg_right hwκ hXn
    nlinarith
  have hCinv : (BAct_C d κ)⁻¹ = κ ^ 3 / (16 * (d : ℝ) ^ 2) := by
    unfold BAct_C
    rw [inv_div]
  rw [hCinv]
  have hκd : κ ≤ 4 * (d : ℝ) ^ 2 := by nlinarith
  have h5 : κ ^ 3 / (16 * (d : ℝ) ^ 2) ≤ κ ^ 2 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_pos hκ 2]
  calc κ ^ 3 / (16 * (d : ℝ) ^ 2) * g ≤ κ ^ 2 / 4 * g := mul_le_mul_of_nonneg_right h5 hg.le
    _ ≤ ‖BAMB d L g (E : ℂ) m a b‖ := by linarith

/-- `(Mbound_AO2)` at a real-axis datum, for every `0 < g ≤ Λ` (the branch premise `(2C)⁻¹ ≤ g` is not used). -/
theorem BAMB_decay_large (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a b : Zd d L) :
    ‖BAMB d L g (E : ℂ) m a b‖ ≤
      (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpos : 0 < κ / (4 * (d : ℝ) * Λ) := by positivity
  set ν₀ : ℝ := Real.log (1 + κ / (4 * (d : ℝ) * Λ)) with hν₀
  have hexp : Real.exp ν₀ = 1 + κ / (4 * (d : ℝ) * Λ) := Real.exp_log (by linarith)
  have hν0 : 0 ≤ ν₀ := Real.log_nonneg (by linarith)
  have hgap : 2 * (d : ℝ) * g * (Real.exp ν₀ - 1) ≤ κ / 2 := by
    rw [hexp]
    have h1 : 2 * (d : ℝ) * g * (1 + κ / (4 * (d : ℝ) * Λ) - 1) = g * κ / (2 * Λ) := by
      field_simp
      ring
    rw [h1, div_le_iff₀ (by positivity)]
    nlinarith
  have hcore := BAMB_ct_core d L hL g κ ν₀ (E : ℂ) m hg.le hκ (by simpa using hr.2) hν0 hgap a b
  have hc := BAct_rate_pos d Λ κ hd hΛ hκ
  have hn : (0 : ℝ) ≤ (zdistD d L (a - b) : ℝ) := Nat.cast_nonneg _
  have h1 : 2 / κ ≤ (BAct_rate d Λ κ)⁻¹ := by
    have := inv_anti₀ hc (CT_rate_le_half d Λ κ)
    rwa [inv_div] at this
  have h2 : Real.exp (-(ν₀ * (zdistD d L (a - b) : ℝ))) ≤
      Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_right (CT_rate_le_log d Λ κ) hn
    linarith
  exact hcore.trans (mul_le_mul h1 h2 (Real.exp_pos _).le (inv_nonneg.mpr hc.le))

/-- Item (3) of `BAPropM` at one datum, with `C := BAct_C d κ`, `c := BAct_rate d Λ κ`. -/
theorem BAPropM3_of_real (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) :
    (g < (2 * BAct_C d κ)⁻¹ → ∀ a b : Zd d L,
      (BAct_C d κ)⁻¹ * g * (if Adj d L a b then 1 else 0) ≤ ‖BAMB d L g (E : ℂ) m a b‖ ∧
        ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_C d κ * g) ^ zdistD d L (a - b)) ∧
    ((2 * BAct_C d κ)⁻¹ ≤ g → ∀ a b : Zd d L,
      ‖BAMB d L g (E : ℂ) m a b‖ ≤
        (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) := by
  refine ⟨fun hsm a b => ⟨?_, BAMB_upper_small d L hL hd g κ E m hg hκ hr hsm a b⟩, fun _ a b =>
    BAMB_decay_large d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr a b⟩
  by_cases hab : Adj d L a b
  · simp only [hab, ↓reduceIte, mul_one]
    exact BAMB_lower_small d L hL hd g κ E m hg hκ hr hsm a b hab
  · simp only [hab, ↓reduceIte, mul_zero]
    exact norm_nonneg _

end Bounds

/-! ## 5. The pin `BAPropM` -/

/-- **`BAPropM` is proved** (`lem:propM`, `7_8:1847-1912`), all items, with `C = 16 d² / κ³`,
`c = min (log (1 + κ/(4dΛ))) (κ/2)`.  Items (1)(2) are `baPropM12_holds` (`Ward.lean`), item (3) is
`BAPropM3_of_real`. -/
theorem baPropM_holds (d : ℕ) (Λ κ : ℝ) : BAPropM d Λ κ := by
  intro hd hΛ hκ
  have hd0 : 0 < d := by omega
  refine ⟨BAct_C d κ, BAct_C_pos d κ hd0 hκ, BAct_rate d Λ κ, BAct_rate_pos d Λ κ hd0 hΛ hκ, ?_⟩
  intro L hL g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr
  obtain ⟨h1, h2, h3, h4⟩ := baPropM12_holds d L hL g hg E m hr.1
  obtain ⟨h5, h6⟩ := BAPropM3_of_real d L hL hd0 Λ g κ E m hΛ hg hgΛ hκ hr
  exact ⟨h1, h2, h3, h4, h5, h6⟩



/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 4`, `card (Zd 3 4) = 64`)

The data are those of `MFixedPointInst` (T2189): the complex point `(z_S, m_S)` with `z_S + m_S = w_I = 6i/5`
(`Im w = κ = 6/5`) and the real-axis flow point `P` of `(L, g) = (4, 10)` (`BAReal 3 4 g₀ (Im m₀) E m₀`).
No hypothesis is left open except the data condition `g₀ < (2C)⁻¹` of the small branch (small-branch
statements are instantiated as implications: no merged real-axis datum has a provable `g₀ < κ³/288`). -/

namespace CombesThomasInst

open RBM.BA.MFixedPointInst

private theorem CT_zSmS : zS 4 10 + mS 4 10 = wI := sub_add_cancel _ _

private theorem CT_wI_im : wI.im = 6 / 5 := rfl

/-- `(z_S + m_S).im = 6/5 = κ`. -/
theorem gap_im : (6 / 5 : ℝ) ≤ (zS 4 10 + mS 4 10).im := by
  rw [CT_zSmS, CT_wI_im]

/-- The weight `ν = log (1 + 1/100) > 0` of the core instance. -/
theorem nu_pos : 0 < Real.log (1 + 1 / 100) := Real.log_pos (by norm_num)

/-- The gap condition at `g = 10`, `ν = log (1 + 1/100)`: `2 · 3 · 10 · (1/100) = 3/5 = κ/2` (equality). -/
theorem gap_cond : 2 * ((3 : ℕ) : ℝ) * 10 * (Real.exp (Real.log (1 + 1 / 100)) - 1) ≤ (6 / 5 : ℝ) / 2 := by
  rw [Real.exp_log (by norm_num)]
  norm_num

/-- `BAMB_ct_core` at the complex point `(z_S, m_S)`, `g = 10`, `κ = 6/5`, `ν = log (1 + 1/100) > 0`. -/
theorem core_at_point (a b : Zd 3 4) :
    ‖BAMB 3 4 10 (zS 4 10) (mS 4 10) a b‖ ≤
      2 / (6 / 5) * Real.exp (-(Real.log (1 + 1 / 100) * (zdistD 3 4 (a - b) : ℝ))) :=
  BAMB_ct_core 3 4 (by norm_num) 10 (6 / 5) (Real.log (1 + 1 / 100)) (zS 4 10) (mS 4 10)
    (by norm_num) (by norm_num) gap_im nu_pos.le gap_cond a b

/-- `BAMB_resolvent_row` at the complex point `(z_S, m_S)`. -/
theorem row_at_point (a b : Zd 3 4) :
    (10 : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd 3 4 => Adj 3 4 a c), BAMB 3 4 10 (zS 4 10) (mS 4 10) c b
        - (zS 4 10 + mS 4 10) * BAMB 3 4 10 (zS 4 10) (mS 4 10) a b = if a = b then 1 else 0 := by
  have h := BAMB_resolvent_row 3 4 10 (zS 4 10) (mS 4 10)
    (by rw [CT_zSmS, CT_wI_im]; norm_num) a b
  simpa using h

/-- `BAzdist_adj_lip` at `x = (1,0,0)`, `y = 0`, `b = (0,0,2)`: `|x - b| = 3 ≤ |y - b| + 1 = 3`. -/
theorem lip_at_point :
    zdistD 3 4 ((![1, 0, 0] : Zd 3 4) - ![0, 0, 2]) ≤ zdistD 3 4 ((0 : Zd 3 4) - ![0, 0, 2]) + 1 :=
  BAzdist_adj_lip 3 4 ![1, 0, 0] 0 ![0, 0, 2] (by decide)

/-- `BAMB_decay_large` at the flow point `P` (`L = 4`, `g = g₀ ≤ 10 = Λ`, `κ = Im m₀`). -/
theorem decay_large_at_P (a b : Zd 3 4) :
    ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ≤
      (BAct_rate 3 10 P.m0.im)⁻¹ * Real.exp (-BAct_rate 3 10 P.m0.im * (zdistD 3 4 (a - b) : ℝ)) :=
  BAMB_decay_large 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real a b

/-- Item (3) of `BAPropM` at the flow point `P`, both branches (as implications). -/
theorem propM3_at_P :
    (P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹ → ∀ a b : Zd 3 4,
      (BAct_C 3 P.m0.im)⁻¹ * P.g0 * (if Adj 3 4 a b then 1 else 0) ≤ ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ∧
        ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ≤ (BAct_C 3 P.m0.im * P.g0) ^ zdistD 3 4 (a - b)) ∧
    ((2 * BAct_C 3 P.m0.im)⁻¹ ≤ P.g0 → ∀ a b : Zd 3 4,
      ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ≤
        (BAct_rate 3 10 P.m0.im)⁻¹ * Real.exp (-BAct_rate 3 10 P.m0.im * (zdistD 3 4 (a - b) : ℝ))) :=
  BAPropM3_of_real 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real

/-- The upper half of `(Mbound_AO)` at `P`, as an implication in the data condition `g₀ < (2C)⁻¹`. -/
theorem upper_small_at_P (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) (a b : Zd 3 4) :
    ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ≤ (BAct_C 3 P.m0.im * P.g0) ^ zdistD 3 4 (a - b) :=
  BAMB_upper_small 3 4 (by norm_num) (by norm_num) P.g0 P.m0.im P.E P.m0 P.g0_pos P.real.1.1 P.real h a b

/-- The lower half of `(Mbound_AO)` at `P`, as an implication in the data condition `g₀ < (2C)⁻¹`. -/
theorem lower_small_at_P (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) (a b : Zd 3 4) (hab : Adj 3 4 a b) :
    (BAct_C 3 P.m0.im)⁻¹ * P.g0 ≤ ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ :=
  BAMB_lower_small 3 4 (by norm_num) (by norm_num) P.g0 P.m0.im P.E P.m0 P.g0_pos P.real.1.1 P.real h a b hab

/-- `baPropM_holds` at `d = 3`, `Λ = 10`, `κ = Im m₀`, applied at `L = 4` and the flow point `P`. -/
theorem propM_at_P :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      (∀ a b r : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (a + r) (b + r) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b) ∧
      (∀ a : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a a = P.m0) ∧
      (∀ a : Zd 3 4, ∑ b, ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ^ 2 = 1) ∧ ‖P.m0‖ ≤ 1 ∧
      (P.g0 < (2 * C)⁻¹ → ∀ a b : Zd 3 4,
        C⁻¹ * P.g0 * (if Adj 3 4 a b then 1 else 0) ≤ ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ∧
          ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ≤ (C * P.g0) ^ zdistD 3 4 (a - b)) ∧
      ((2 * C)⁻¹ ≤ P.g0 → ∀ a b : Zd 3 4,
        ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ≤ c⁻¹ * Real.exp (-c * (zdistD 3 4 (a - b) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := baPropM_holds 3 10 P.m0.im (le_refl 3) (by norm_num) P.real.1.1
  exact ⟨C, hC, c, hc, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real⟩

/-- `BAct_C_pos` at `d = 3`, `κ = 1/2`. -/
theorem C_pos_at : 0 < BAct_C 3 (1 / 2) := BAct_C_pos 3 (1 / 2) (by norm_num) (by norm_num)

/-- `BAct_rate_pos` at `d = 3`, `Λ = 10`, `κ = 1/2`. -/
theorem rate_pos_at : 0 < BAct_rate 3 10 (1 / 2) := BAct_rate_pos 3 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num)

end CombesThomasInst

end RBM.BA

end
