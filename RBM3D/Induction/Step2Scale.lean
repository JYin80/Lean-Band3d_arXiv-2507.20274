/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Core
import RBM3D.Induction.ScaleFacts
import RBM3D.Green.Pins

/-!
# ST2-05 (ticket T2081): the scale family of `(eq:def_ell1)`

Paper: `paper/tex/3_5_Loop_Hierarchy.tex:512-577` (`(kwr3juw)`, `(eq:monotone_Ku)`,
`(eq:def_ell1)`).  Proves the pin `STScaleExists` (`Induction/Step2Defs.lean:656`).

## Construction

For `u` and `n` fixed write `T(r) = 𝒯_u(r)` (`RBM.tailT`), `β = W^{-d} B_{u,0}` (`Sizes.Bctl`) and
`q = β^{1/6}`.  `K^{(0)} = 0`.  Given `K = K^{(m)}`: if some `r ≥ K` has `T(r) = q T(K)` (the
solution of `(eq:def_ell1)`; it exists by the intermediate value theorem on `[K, R]` when
`0 < β ≤ 1`, `T` being continuous on `[0, ∞)` with `T(R) → 0`), `K^{(m+1)} := min(r, L)`, else
`K^{(m+1)} := K` (never used in the regime where the pin asserts anything).  Then
`T(K^{(m+1)}) = max(q T(K), T(L))` (`T` antitone), which gives `u ↦ 𝒯_u(K_u)` nondecreasing (by
induction on `m`, from `𝒯_u(r)` and `β_u` nondecreasing in `u`), the cut at `L` is absorbing, and
`K^{(m)} = L ∨ 𝒯_u(K^{(m)}) ≤ q^m B_{u,0}`.

Every property is a statement for `n ≥ n₀` only (the pin's `∀ᶠ n`), `n₀` being the point after which
`β ≤ 1` (`scaleFacts_R1`, `N → ∞`), `W ≥ ` the constants, `ilambda ≥ 0`.  `STFlow` enters through
`v3_premises_of_stFlow` (`t_n < 1`, `RangeCond (ε/2)`), `Admissible` (`W ≥ N^𝔠`, `N → ∞`,
`(eq:WO)`) and `scaleFacts_R1` (`β_u ≤ 2 N^{-c₀}`, `c₀ = min(2𝔠𝔡, ε/2)`).

Continuity of `r ↦ 𝒯_u(r)` on `[0, ∞)` was not merged: `st2s_tailT_continuousOn` proves it here and
is used only for the intermediate value argument of `st2s_exists_eq`.
-/

set_option linter.style.longLine false

noncomputable section

open Filter RBM RBM.Gauss

namespace RBM.Gauss.Sizes

/-! ## 1. Real-variable facts about `r ↦ 𝒯_u(r)` -/

section TailFacts

variable {d L : ℕ} {g u : ℝ}

/-- `r ↦ 𝒯_u(r)` is continuous on `[0, ∞)` (`(r+1)^{d-2} ≠ 0` there). -/
private theorem st2s_tailT_continuousOn (d L : ℕ) (g u : ℝ) :
    ContinuousOn (fun r : ℝ => tailT d L g u r) (Set.Ici 0) := by
  unfold tailT BparamR
  refine ContinuousOn.mul (ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_)
    continuousOn_const) ?_
  · refine ContinuousOn.inv₀ (by fun_prop) (fun r hr => ?_)
    exact (pow_pos (by have : (0 : ℝ) ≤ r := hr; linarith) _).ne'
  · fun_prop

/-- `B_{u,r} > 0` for `u < 1`, `L ≥ 1`, `r ≥ 0`. -/
private theorem st2s_BparamR_pos (hL : 1 ≤ (L : ℝ)) (hu : u < 1) {r : ℝ} (hr : 0 ≤ r) :
    0 < BparamR d L g u r := by
  unfold BparamR
  have hx : 0 < 1 - u := by linarith
  rw [abs_of_pos hx]
  have hL0 : (0 : ℝ) < L := by linarith
  have h1 : 0 ≤ (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ := by
    refine mul_nonneg (inv_nonneg.mpr (by positivity)) (inv_nonneg.mpr ?_)
    exact pow_nonneg (by linarith) _
  have h2 : 0 < ((L : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  linarith

/-- `𝒯_u(r) > 0` for `u < 1`, `L ≥ 1`, `r ≥ 0`. -/
private theorem st2s_tailT_pos (hL : 1 ≤ (L : ℝ)) (hu : u < 1) {r : ℝ} (hr : 0 ≤ r) :
    0 < tailT d L g u r :=
  mul_pos (st2s_BparamR_pos hL hu hr) (Real.exp_pos _)

/-- The intermediate value step: `0 ≤ K`, `0 < y ≤ 𝒯_u(K)` give `r ≥ K` with `𝒯_u(r) = y`
(`R = max K (ℓ_u (log (B_{u,0}/y))²)` has `𝒯_u(R) ≤ B_{u,0} e^{-√(R/ℓ_u)} ≤ y`). -/
private theorem st2s_exists_eq (hL : 1 ≤ (L : ℝ)) (hu : u < 1) {K y : ℝ} (hK : 0 ≤ K)
    (hy : 0 < y) (hyK : y ≤ tailT d L g u K) : ∃ r, K ≤ r ∧ tailT d L g u r = y := by
  set ℓ := ellT L g u with hℓdef
  have hℓ : 0 < ℓ := ellT_pos hL
  set B0 := BparamR d L g u 0 with hB0def
  have hB0 : 0 < B0 := st2s_BparamR_pos hL hu le_rfl
  set R := max K (ℓ * (Real.log (B0 / y)) ^ 2) with hRdef
  have hKR : K ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := hK.trans hKR
  have hTR : tailT d L g u R ≤ y := by
    have h1 : BparamR d L g u R ≤ B0 := BparamR_antitone le_rfl hR0
    have h2 : (Real.log (B0 / y)) ^ 2 ≤ R / ℓ := by
      rw [le_div_iff₀ hℓ]
      calc (Real.log (B0 / y)) ^ 2 * ℓ = ℓ * (Real.log (B0 / y)) ^ 2 := by ring
        _ ≤ R := le_max_right _ _
    have h3 : Real.log (B0 / y) ≤ Real.sqrt (R / ℓ) := by
      calc Real.log (B0 / y) ≤ |Real.log (B0 / y)| := le_abs_self _
        _ = Real.sqrt ((Real.log (B0 / y)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (R / ℓ) := Real.sqrt_le_sqrt h2
    have h4 : Real.exp (-Real.sqrt (R / ℓ)) ≤ y / B0 := by
      calc Real.exp (-Real.sqrt (R / ℓ)) ≤ Real.exp (-Real.log (B0 / y)) :=
            Real.exp_le_exp.mpr (neg_le_neg h3)
        _ = y / B0 := by
          rw [Real.exp_neg, Real.exp_log (div_pos hB0 hy), inv_div]
    unfold tailT
    calc BparamR d L g u R * Real.exp (-Real.sqrt (R / ℓ))
        ≤ B0 * (y / B0) :=
          mul_le_mul h1 h4 (Real.exp_pos _).le hB0.le
      _ = y := by field_simp
  have hcont : ContinuousOn (fun r : ℝ => tailT d L g u r) (Set.Icc K R) :=
    (st2s_tailT_continuousOn d L g u).mono (fun r hr => le_trans hK hr.1)
  obtain ⟨r, hr, hrT⟩ := intermediate_value_Icc' hKR hcont ⟨hTR, hyK⟩
  exact ⟨r, hr.1, hrT⟩

end TailFacts

/-! ## 2. The scale iteration `(eq:def_ell1)` at one `(n, u)` -/

section Iteration

variable {d L : ℕ} {g u β : ℝ}

open Classical in
/-- One step of `(eq:def_ell1)`: a solution `r ≥ K` of `𝒯_u(r) = β^{1/6} 𝒯_u(K)` (the paper's
`K'_u` is the unique one; uniqueness is neither needed nor proved here), cut at `L`; `K` itself if
there is none (never the case when `0 < β ≤ 1`, `u < 1`, `K ≥ 0`: `st2s_step_exists`). -/
private def st2sStep (d L : ℕ) (g u β K : ℝ) : ℝ :=
  if h : ∃ r : ℝ, K ≤ r ∧ tailT d L g u r = β ^ (1 / 6 : ℝ) * tailT d L g u K then
    min (Classical.choose h) (L : ℝ) else K

/-- The scale levels `K^{(0)} = 0`, `K^{(m+1)} = st2sStep K^{(m)}`. -/
private def st2sSeq (d L : ℕ) (g u β : ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => st2sStep d L g u β (st2sSeq d L g u β m)

private theorem st2sSeq_zero : st2sSeq d L g u β 0 = 0 := rfl

private theorem st2sSeq_succ (m : ℕ) :
    st2sSeq d L g u β (m + 1) = st2sStep d L g u β (st2sSeq d L g u β m) := rfl

/-- `0 < β ≤ 1` gives `0 < q ≤ 1` for `q = β^{1/6}`. -/
private theorem st2s_q_pos (hβ : 0 < β) : 0 < β ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hβ _

private theorem st2s_q_le_one (hβ : 0 < β) (hβ1 : β ≤ 1) : β ^ (1 / 6 : ℝ) ≤ 1 :=
  Real.rpow_le_one hβ.le hβ1 (by norm_num)

/-- The solution of the step exists (`0 < β ≤ 1`, `u < 1`, `K ≥ 0`). -/
private theorem st2s_step_exists (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ r : ℝ, K ≤ r ∧ tailT d L g u r = β ^ (1 / 6 : ℝ) * tailT d L g u K := by
  have hT : 0 < tailT d L g u K := st2s_tailT_pos hL hu hK
  refine st2s_exists_eq hL hu hK (mul_pos (st2s_q_pos hβ) hT) ?_
  calc β ^ (1 / 6 : ℝ) * tailT d L g u K ≤ 1 * tailT d L g u K :=
        mul_le_mul_of_nonneg_right (st2s_q_le_one hβ hβ1) hT.le
    _ = tailT d L g u K := one_mul _

/-- **The facts of one step** (`3_5:570-577`): for `0 ≤ K ≤ L`, the new level `K'` is `min r L` for
a solution `r ≥ K` of `T(r) = q T(K)`; so `K ≤ K' ≤ min r L`, `T(K') = max (q T(K)) (T(L))`, either
`K' = L` or `T(K') = q T(K)`, and `K = L` gives `K' = L`. -/
private theorem st2s_step_facts (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {K : ℝ} (hK : 0 ≤ K) (hKL : K ≤ L) :
    ∃ r : ℝ, K ≤ r ∧ tailT d L g u r = β ^ (1 / 6 : ℝ) * tailT d L g u K ∧
      st2sStep d L g u β K = min r L ∧
      K ≤ st2sStep d L g u β K ∧ st2sStep d L g u β K ≤ L ∧ st2sStep d L g u β K ≤ r ∧
      0 ≤ st2sStep d L g u β K ∧
      tailT d L g u (st2sStep d L g u β K) =
        max (β ^ (1 / 6 : ℝ) * tailT d L g u K) (tailT d L g u L) ∧
      (st2sStep d L g u β K = L ∨
        tailT d L g u (st2sStep d L g u β K) = β ^ (1 / 6 : ℝ) * tailT d L g u K) ∧
      (K = L → st2sStep d L g u β K = L) := by
  have hex := st2s_step_exists (d := d) (g := g) hL hu hβ hβ1 hK
  have hstep : st2sStep d L g u β K = min (Classical.choose hex) (L : ℝ) := by
    unfold st2sStep; rw [dite_eq_left hex]
  obtain ⟨hrK, hrT⟩ := Classical.choose_spec hex
  set r := Classical.choose hex with hr
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hr0 : 0 ≤ r := hK.trans hrK
  refine ⟨r, hrK, hrT, hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep]; exact le_min hrK hKL
  · rw [hstep]; exact min_le_right _ _
  · rw [hstep]; exact min_le_left _ _
  · rw [hstep]; exact le_min hr0 hL0
  · rw [hstep]
    rcases le_total r (L : ℝ) with h | h
    · rw [min_eq_left h, ← hrT]
      exact (max_eq_left (tailT_antitone hr0 h)).symm
    · rw [min_eq_right h, ← hrT]
      exact (max_eq_right (tailT_antitone hL0 h)).symm
  · rw [hstep]
    rcases le_total r (L : ℝ) with h | h
    · right; rw [min_eq_left h, hrT]
    · left; exact min_eq_right h
  · intro hKeq
    rw [hstep]
    exact min_eq_right (hKeq ▸ hrK)

/-- The levels are in `[0, L]`. -/
private theorem st2sSeq_bounds (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∀ m, 0 ≤ st2sSeq d L g u β m ∧ st2sSeq d L g u β m ≤ L := by
  intro m
  induction m with
  | zero => exact ⟨le_rfl, by rw [st2sSeq_zero]; linarith⟩
  | succ m ih =>
    obtain ⟨_, -, -, -, -, h5, -, h7, -, -, -⟩ := st2s_step_facts (g := g) hL hu hβ hβ1 ih.1 ih.2
    rw [st2sSeq_succ]
    exact ⟨h7, h5⟩

/-- Levels are nondecreasing. -/
private theorem st2sSeq_mono_succ (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (m : ℕ) : st2sSeq d L g u β m ≤ st2sSeq d L g u β (m + 1) := by
  obtain ⟨hb0, hbL⟩ := st2sSeq_bounds (g := g) hL hu hβ hβ1 m
  obtain ⟨_, -, -, -, h4, -, -, -, -, -, -⟩ := st2s_step_facts (g := g) hL hu hβ hβ1 hb0 hbL
  rw [st2sSeq_succ]; exact h4

/-- The profile recursion `T(K^{(m+1)}) = max (q T(K^{(m)})) (T(L))`. -/
private theorem st2sSeq_tailT_succ (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (m : ℕ) : tailT d L g u (st2sSeq d L g u β (m + 1)) =
      max (β ^ (1 / 6 : ℝ) * tailT d L g u (st2sSeq d L g u β m)) (tailT d L g u L) := by
  obtain ⟨hb0, hbL⟩ := st2sSeq_bounds (g := g) hL hu hβ hβ1 m
  obtain ⟨_, -, -, -, -, -, -, -, h9, -, -⟩ := st2s_step_facts (g := g) hL hu hβ hβ1 hb0 hbL
  rw [st2sSeq_succ]; exact h9

/-- `(kwr3juw)`: `q T(K^{(m)}) ≤ T(K^{(m+1)})`. -/
private theorem st2sSeq_clause4 (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (m : ℕ) : β ^ (1 / 6 : ℝ) * tailT d L g u (st2sSeq d L g u β m) ≤
      tailT d L g u (st2sSeq d L g u β (m + 1)) := by
  rw [st2sSeq_tailT_succ hL hu hβ hβ1]; exact le_max_left _ _

/-- The cut at `L` is absorbing. -/
private theorem st2sSeq_cut (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (m : ℕ) (h : st2sSeq d L g u β m = L) : st2sSeq d L g u β (m + 1) = L := by
  obtain ⟨hb0, hbL⟩ := st2sSeq_bounds (g := g) hL hu hβ hβ1 m
  obtain ⟨_, -, -, -, -, -, -, -, -, -, h11⟩ := st2s_step_facts (g := g) hL hu hβ hβ1 hb0 hbL
  rw [st2sSeq_succ]; exact h11 h

/-- `T(K^{(m)}) ≥ q^m B_{u,0}`. -/
private theorem st2sSeq_lower (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∀ m : ℕ, (β ^ (1 / 6 : ℝ)) ^ m * tailT d L g u 0 ≤ tailT d L g u (st2sSeq d L g u β m) := by
  intro m
  induction m with
  | zero => simp [st2sSeq_zero]
  | succ m ih =>
    have hq := st2s_q_pos hβ
    calc (β ^ (1 / 6 : ℝ)) ^ (m + 1) * tailT d L g u 0
        = β ^ (1 / 6 : ℝ) * ((β ^ (1 / 6 : ℝ)) ^ m * tailT d L g u 0) := by ring
      _ ≤ β ^ (1 / 6 : ℝ) * tailT d L g u (st2sSeq d L g u β m) :=
        mul_le_mul_of_nonneg_left ih hq.le
      _ ≤ _ := st2sSeq_clause4 hL hu hβ hβ1 m

/-- **The floor, before the arithmetic**: `K^{(m)} = L` or `T(K^{(m)}) ≤ q^m B_{u,0}`. -/
private theorem st2sSeq_floor (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∀ m : ℕ, st2sSeq d L g u β m = L ∨
      tailT d L g u (st2sSeq d L g u β m) ≤ (β ^ (1 / 6 : ℝ)) ^ m * tailT d L g u 0 := by
  intro m
  induction m with
  | zero => right; simp [st2sSeq_zero]
  | succ m ih =>
    rcases ih with h | h
    · left; exact st2sSeq_cut hL hu hβ hβ1 m h
    · obtain ⟨hb0, hbL⟩ := st2sSeq_bounds (g := g) hL hu hβ hβ1 m
      obtain ⟨_, -, -, -, -, -, -, -, -, h10, -⟩ := st2s_step_facts (g := g) hL hu hβ hβ1 hb0 hbL
      rw [st2sSeq_succ]
      rcases h10 with h' | h'
      · left; exact h'
      · right
        rw [h', pow_succ]
        have hq := st2s_q_pos hβ
        calc β ^ (1 / 6 : ℝ) * tailT d L g u (st2sSeq d L g u β m)
            ≤ β ^ (1 / 6 : ℝ) * ((β ^ (1 / 6 : ℝ)) ^ m * tailT d L g u 0) :=
              mul_le_mul_of_nonneg_left h hq.le
          _ = (β ^ (1 / 6 : ℝ)) ^ m * β ^ (1 / 6 : ℝ) * tailT d L g u 0 := by ring

/-- **The cap, before the arithmetic**: `K^{(m)} ≤ ℓ_u ((m/6) (-log β))²`.  From
`T(K^{(m+1)}) ≤ T(r) = q T(K^{(m)}) ≥ q^{m+1} B_{u,0}` and `T(r) ≤ B_{u,0} e^{-√(r/ℓ_u)}`. -/
private theorem st2sSeq_cap (hL : 1 ≤ (L : ℝ)) (hu : u < 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∀ m : ℕ, st2sSeq d L g u β m ≤ ellT L g u * (((m : ℝ) / 6) * (-Real.log β)) ^ 2 := by
  have hℓ : 0 < ellT L g u := ellT_pos hL
  intro m
  cases m with
  | zero => rw [st2sSeq_zero]; simp
  | succ m =>
    obtain ⟨hb0, hbL⟩ := st2sSeq_bounds (g := g) hL hu hβ hβ1 m
    obtain ⟨r, hrK, hrT, -, -, -, h6, -, -, -, -⟩ := st2s_step_facts (g := g) hL hu hβ hβ1 hb0 hbL
    rw [st2sSeq_succ]
    refine h6.trans ?_
    have hr0 : 0 ≤ r := hb0.trans hrK
    set q := β ^ (1 / 6 : ℝ) with hqdef
    have hq : 0 < q := st2s_q_pos hβ
    have hB0 : 0 < tailT d L g u 0 := st2s_tailT_pos hL hu le_rfl
    have hBpos : 0 < BparamR d L g u 0 := st2s_BparamR_pos hL hu le_rfl
    -- `q^{m+1} B_0 ≤ T(r) ≤ B_0 e^{-√(r/ℓ)}`
    have h1 : q ^ (m + 1) * tailT d L g u 0 ≤ tailT d L g u r := by
      rw [hrT]
      calc q ^ (m + 1) * tailT d L g u 0 = q * (q ^ m * tailT d L g u 0) := by ring
        _ ≤ q * tailT d L g u (st2sSeq d L g u β m) :=
            mul_le_mul_of_nonneg_left (st2sSeq_lower hL hu hβ hβ1 m) hq.le
    have h2 : tailT d L g u r ≤ BparamR d L g u 0 * Real.exp (-Real.sqrt (r / ellT L g u)) := by
      unfold tailT
      exact mul_le_mul_of_nonneg_right (BparamR_antitone le_rfl hr0) (Real.exp_pos _).le
    have hT0 : tailT d L g u 0 = BparamR d L g u 0 * Real.exp (-Real.sqrt (0 / ellT L g u)) := rfl
    have hT0' : tailT d L g u 0 = BparamR d L g u 0 := by
      rw [hT0]; simp
    rw [hT0'] at h1
    have h3 : q ^ (m + 1) ≤ Real.exp (-Real.sqrt (r / ellT L g u)) := by
      have := h1.trans h2
      rw [mul_comm] at this
      exact le_of_mul_le_mul_left this hBpos
    -- take logarithms: `(m+1) log q ≤ -√(r/ℓ)`, `log q = log β / 6`
    have h4 : ((m + 1 : ℕ) : ℝ) * Real.log q ≤ -Real.sqrt (r / ellT L g u) := by
      have := Real.log_le_log (pow_pos hq _) h3
      rwa [Real.log_pow, Real.log_exp] at this
    have hlogq : Real.log q = Real.log β / 6 := by
      rw [hqdef, Real.log_rpow hβ]; ring
    have h5 : Real.sqrt (r / ellT L g u) ≤ ((m + 1 : ℕ) : ℝ) / 6 * (-Real.log β) := by
      rw [hlogq] at h4; linarith
    have hs0 : 0 ≤ Real.sqrt (r / ellT L g u) := Real.sqrt_nonneg _
    have h6' : r / ellT L g u ≤ (((m + 1 : ℕ) : ℝ) / 6 * (-Real.log β)) ^ 2 := by
      calc r / ellT L g u = (Real.sqrt (r / ellT L g u)) ^ 2 :=
            (Real.sq_sqrt (div_nonneg hr0 hℓ.le)).symm
        _ ≤ _ := pow_le_pow_left₀ hs0 h5 2
    rw [div_le_iff₀ hℓ] at h6'
    linarith

/-- **Monotonicity in time** (`(eq:monotone_Ku)`, `3_5:525-527`): `u ↦ 𝒯_u(K^{(m)}_u)` is nondecreasing
(`u ≤ v < 1`, `g ≥ 0`, both controls in `(0, 1]`, `β_u ≤ β_v`): by induction on `m` from
`T_u(K^{(m+1)}_u) = max (q_u T_u(K^{(m)}_u)) (T_u(L))`, `ST_tailT_mono_time` and `q_u ≤ q_v`. -/
private theorem st2sSeq_tailT_mono_time {g v βu βv : ℝ} (hL : 1 ≤ (L : ℝ)) (hg : 0 ≤ g)
    (huv : u ≤ v) (hv : v < 1) (hβu : 0 < βu) (hβu1 : βu ≤ 1) (hβv : 0 < βv) (hβv1 : βv ≤ 1)
    (hβ : βu ≤ βv) :
    ∀ m : ℕ, tailT d L g u (st2sSeq d L g u βu m) ≤ tailT d L g v (st2sSeq d L g v βv m) := by
  have hu : u < 1 := lt_of_le_of_lt huv hv
  have hL0 : (0 : ℝ) ≤ L := by linarith
  intro m
  induction m with
  | zero =>
    rw [st2sSeq_zero, st2sSeq_zero]
    exact ST_tailT_mono_time hL hg huv hv le_rfl
  | succ m ih =>
    rw [st2sSeq_tailT_succ hL hu hβu hβu1, st2sSeq_tailT_succ hL hv hβv hβv1]
    have hqq : βu ^ (1 / 6 : ℝ) ≤ βv ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow hβu.le hβ (by norm_num)
    have hY0 : 0 ≤ tailT d L g u (st2sSeq d L g u βu m) :=
      tailT_nonneg (st2sSeq_bounds (g := g) hL hu hβu hβu1 m).1
    refine max_le_max ?_ (ST_tailT_mono_time hL hg huv hv hL0)
    exact mul_le_mul hqq ih hY0 (st2s_q_pos hβv).le

end Iteration

/-! ## 3. Arithmetic of the floor and of the cap -/

section Arith

/-- The floor arithmetic: `W^d β^{j+1} ≤ W^{-D}` from `W^d ≤ N`, `W ≤ N`, `β ≤ 2 N^{-c}`,
`c (j + 1) ≥ 2 + D` and `2^{j+1} ≤ N`. -/
private theorem st2s_floor_arith {N W β c D : ℝ} {d j : ℕ} (hW1 : 1 ≤ W) (hWd : W ^ d ≤ N)
    (hWN : W ≤ N) (hβ0 : 0 ≤ β) (hβ : β ≤ 2 * N ^ (-c)) (hD : 0 < D)
    (hj : 2 + D ≤ c * ((j : ℝ) + 1)) (hN : (2 : ℝ) ^ (j + 1) ≤ N) :
    W ^ d * β ^ (j + 1) ≤ W ^ (-D) := by
  have hN1 : 1 ≤ N := hW1.trans hWN
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := by linarith
  have h1 : β ^ (j + 1) ≤ (2 * N ^ (-c)) ^ (j + 1) := pow_le_pow_left₀ hβ0 hβ _
  have h2 : (2 * N ^ (-c)) ^ (j + 1) = 2 ^ (j + 1) * N ^ (-(c * ((j : ℝ) + 1))) := by
    rw [mul_pow, ← Real.rpow_natCast (N ^ (-c)) (j + 1), ← Real.rpow_mul hN0.le]
    congr 2; push_cast; ring
  have h3 : N ^ (-(c * ((j : ℝ) + 1))) ≤ N ^ (-(2 + D)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h4 : N * N ^ (-(2 + D)) = N⁻¹ * N ^ (-D) := by
    rw [← Real.rpow_one_add' hN0.le (by linarith : (1 : ℝ) + -(2 + D) ≠ 0)]
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1; ring
  have h5 : (2 : ℝ) ^ (j + 1) * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  have hNW : N ^ (-D) ≤ W ^ (-D) := Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
  have hNn : 0 ≤ N ^ (-D) := Real.rpow_nonneg hN0.le _
  have hpos2 : 0 ≤ (2 : ℝ) ^ (j + 1) := by positivity
  have hpos3 : 0 ≤ N ^ (-(2 + D)) := Real.rpow_nonneg hN0.le _
  calc W ^ d * β ^ (j + 1) ≤ N * (2 ^ (j + 1) * N ^ (-(c * ((j : ℝ) + 1)))) := by
        rw [← h2]; exact mul_le_mul hWd h1 (by positivity) hN0.le
    _ ≤ N * (2 ^ (j + 1) * N ^ (-(2 + D))) := by gcongr
    _ = (2 ^ (j + 1) * N⁻¹) * N ^ (-D) := by rw [← mul_assoc, mul_comm N, mul_assoc, h4]; ring
    _ ≤ 1 * N ^ (-D) := mul_le_mul_of_nonneg_right h5 hNn
    _ ≤ W ^ (-D) := by rw [one_mul]; exact hNW

/-- The cap arithmetic: with `(W^d Cc)⁻¹ ≤ β ≤ 1`, `Cc ≤ W` and `log W ≥ max 1 ((m (d+1)/6)²)`,
`((m/6) (-log β))² ≤ (log W)^{10}`. -/
private theorem st2s_cap_arith {W β Cc : ℝ} {d m : ℕ} (hW1 : 1 ≤ W) (hCc : Cc ≤ W)
    (hCc1 : 1 ≤ Cc) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hlow : (W ^ d * Cc)⁻¹ ≤ β)
    (hx : 1 ≤ Real.log W) (hA : ((m : ℝ) * ((d : ℝ) + 1) / 6) ^ 2 ≤ Real.log W) :
    (((m : ℝ) / 6) * (-Real.log β)) ^ 2 ≤ (Real.log W) ^ 10 := by
  set x := Real.log W with hxdef
  have hW0 : 0 < W := by linarith
  have hCc0 : 0 < Cc := by linarith
  have hlogβ0 : Real.log β ≤ 0 := Real.log_nonpos hβ0.le hβ1
  have hlogCc : Real.log Cc ≤ x := Real.log_le_log hCc0 hCc
  have hlow' : -(Real.log (W ^ d * Cc)) ≤ Real.log β := by
    have := Real.log_le_log (by positivity) hlow
    rwa [Real.log_inv] at this
  have hlogWd : Real.log (W ^ d * Cc) = (d : ℝ) * x + Real.log Cc := by
    rw [Real.log_mul (by positivity) hCc0.ne', Real.log_pow]
  have hup : -Real.log β ≤ ((d : ℝ) + 1) * x := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith
  have hlo : 0 ≤ -Real.log β := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) / 6 := by positivity
  have h1 : ((m : ℝ) / 6) * (-Real.log β) ≤ ((m : ℝ) * ((d : ℝ) + 1) / 6) * x := by
    calc ((m : ℝ) / 6) * (-Real.log β) ≤ ((m : ℝ) / 6) * (((d : ℝ) + 1) * x) :=
          mul_le_mul_of_nonneg_left hup hm0
      _ = ((m : ℝ) * ((d : ℝ) + 1) / 6) * x := by ring
  have h2 : (((m : ℝ) / 6) * (-Real.log β)) ^ 2 ≤ (((m : ℝ) * ((d : ℝ) + 1) / 6) * x) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hm0 hlo) h1 2
  have hx0 : 0 ≤ x := by linarith
  calc (((m : ℝ) / 6) * (-Real.log β)) ^ 2 ≤ (((m : ℝ) * ((d : ℝ) + 1) / 6) * x) ^ 2 := h2
    _ = ((m : ℝ) * ((d : ℝ) + 1) / 6) ^ 2 * x ^ 2 := by ring
    _ ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = x ^ 3 := by ring
    _ ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)

end Arith

/-! ## 4. The pin `STScaleExists` -/

/-- **The scale family of `(eq:def_ell1)`** (`3_5:521-527`, `3_5:571-577`): the pin `STScaleExists`
(`Induction/Step2Defs.lean:656`) is true, for every `d`.  The levels are `st2sSeq`
(`K^{(0)} = 0`, `𝒯_u(K^{(m+1)}_u) = (W^{-d} B_{u,0})^{1/6} 𝒯_u(K^{(m)}_u)` cut at `L`); every
clause but `K^{(0)} = 0` holds for `n ≥ n₀`, `n₀` depending on `m` (resp. `D`) and the data of the
flow, as the pin states (DECISIONS §29 (4)).  `STFlow` gives `t_n < 1`, `RangeCond (ε/2)`
(`v3_premises_of_stFlow`), `(eq:WO)`, `W ≥ N^𝔠` and `N → ∞`; the control satisfies
`W^{-d} B_{u,0} ≤ 2 N^{-c₀}`, `c₀ = min(2𝔠𝔡, ε/2)` (`scaleFacts_R1`); `d ≥ 1` follows from `N → ∞`.
`M(D) = 6 ⌈(2 + D)/c₀⌉`. -/
theorem stScaleExists_holds (d : ℕ) : STScaleExists d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htz
  obtain ⟨hA, -, ht1, hR⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htz
  obtain ⟨h𝔠, -, hsize, hBand, hWO⟩ := hA
  -- `d ≥ 1`: for `d = 0` the size `N = 1` does not tend to infinity
  have hd1 : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    obtain ⟨n, hn⟩ := (hsize.eventually_ge_atTop 2).exists
    have h1 : ((sz.size n : ℕ) : ℝ) = 1 := by simp [Sizes.size, hd0]
    linarith
  set c₀ : ℝ := min (2 * 𝔠 * 𝔡) (ε / 2) with hc₀
  have hc₀pos : 0 < c₀ := lt_min (by positivity) (by linarith)
  have hR1 := RBM.Ind.scaleFacts_R1 sz 𝔠 𝔡 (ε / 2) t h𝔡 hBand hWO hR
  have hL : ∀ n, 1 ≤ ((sz.L n : ℕ) : ℝ) := fun n => by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hWdN : ∀ n, ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := fun n => by
    have h : (sz.W n) ^ d ≤ sz.size n :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    exact_mod_cast h
  have hWN : ∀ n, ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by
    have h : ((sz.W n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
      exact_mod_cast Nat.le_self_pow (by omega : d ≠ 0) (sz.W n)
    exact h.trans (hWdN n)
  -- eventual facts
  have hsmall : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-c₀) ≤ 1 / 2 :=
    ((tendsto_rpow_neg_atTop hc₀pos).comp hsize).eventually (Iic_mem_nhds (by norm_num))
  have hWlarge : ∀ B : ℝ, ∀ᶠ n in atTop, B ≤ ((sz.W n : ℕ) : ℝ) := by
    intro B
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hsize
    filter_upwards [hBand, h1.eventually_ge_atTop B] with n hn1 hn2 using hn2.trans hn1
  have hNlarge : ∀ B : ℝ, ∀ᶠ n in atTop, B ≤ ((sz.size n : ℕ) : ℝ) := fun B =>
    hsize.eventually_ge_atTop B
  have hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ :=
    hWO.mono fun n hn => ⟨le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn.1, hn.2⟩
  -- the controls `W^{-d} B_{u,0} ∈ (0, 1]`, `≤ 2 N^{-c₀}`, for `u ∈ [s_n, t_n]`
  have hgood : ∀ᶠ n in atTop, 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ ∧ ∀ u, s n ≤ u → u ≤ t n →
      0 < sz.Bctl n u ∧ sz.Bctl n u ≤ 1 ∧
        sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀) := by
    filter_upwards [hlam, hR1, hsmall] with n hl hb hsm
    refine ⟨hl.1, hl.2, fun u _ hut => ⟨STBctl_pos sz n (hut.trans_lt (ht1 n)), ?_, hb u hut⟩⟩
    linarith [hb u hut]
  refine ⟨fun m n u => st2sSeq d (sz.L n) (sz.lam n) u (sz.Bctl n u) m, fun n u => rfl,
    ?_, ?_, ?_, ?_⟩
  · -- `STScaleOk`
    intro m
    refine ⟨?_, ?_⟩
    · set A : ℝ := ((m : ℝ) * ((d : ℝ) + 1) / 6) ^ 2 with hAdef
      set Cc : ℝ := (𝔡⁻¹) ^ 2 + 1 with hCc
      filter_upwards [hgood, hWlarge (Real.exp (max 1 A)), hWlarge Cc] with n hg hW2 hW3 u hsu hut
      obtain ⟨hl0, hl1, hb⟩ := hg
      obtain ⟨hβ, hβ1, -⟩ := hb u hsu hut
      have hu : u < 1 := hut.trans_lt (ht1 n)
      obtain ⟨h0, hLm⟩ := st2sSeq_bounds (g := sz.lam n) (hL n) hu hβ hβ1 m
      refine ⟨h0, hLm, ?_⟩
      have hcap := st2sSeq_cap (d := d) (g := sz.lam n) (hL n) hu hβ hβ1 m
      have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith [hW1 n]
      have hlogW : max 1 A ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
        (Real.le_log_iff_exp_le hWpos).2 hW2
      have hCc1 : 1 ≤ Cc := by have : 0 ≤ (𝔡⁻¹) ^ 2 := sq_nonneg _; linarith
      have hlam2 : sz.lam n ^ 2 + 1 ≤ Cc := by
        have := pow_le_pow_left₀ hl0 hl1 2; linarith
      have hlow : ((((sz.W n : ℕ) : ℝ) ^ d) * Cc)⁻¹ ≤ sz.Bctl n u := by
        have h1 := STBctl_ge sz n ((hs n).trans hsu) hu
        calc ((((sz.W n : ℕ) : ℝ) ^ d) * Cc)⁻¹ = ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * Cc⁻¹ :=
              mul_inv _ _
          _ ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ :=
              mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hlam2) (by positivity)
          _ ≤ _ := h1
      have hcapA := st2s_cap_arith (d := d) (m := m) (hW1 n) hW3 hCc1 hβ hβ1 hlow
        (le_trans (le_max_left _ _) hlogW) (le_trans (le_max_right _ _) hlogW)
      calc st2sSeq d (sz.L n) (sz.lam n) u (sz.Bctl n u) m
          ≤ ellT (sz.L n) (sz.lam n) u * (((m : ℝ) / 6) * (-Real.log (sz.Bctl n u))) ^ 2 := hcap
        _ ≤ ellT (sz.L n) (sz.lam n) u * (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 :=
            mul_le_mul_of_nonneg_left hcapA ellT_nonneg
        _ = _ := mul_comm _ _
    · filter_upwards [hgood] with n hg u v hsu huv hvt
      obtain ⟨hl0, -, hb⟩ := hg
      have hsv : s n ≤ v := hsu.trans huv
      obtain ⟨hβu, hβu1, -⟩ := hb u hsu (huv.trans hvt)
      obtain ⟨hβv, hβv1, -⟩ := hb v hsv hvt
      exact st2sSeq_tailT_mono_time (L := sz.L n) (hL n) hl0 huv (hvt.trans_lt (ht1 n))
        hβu hβu1 hβv hβv1 (STBctl_mono sz n huv (hvt.trans_lt (ht1 n))) m
  · -- `0 ≤ K_m ≤ K_{m+1}`
    intro m
    filter_upwards [hgood] with n hg u hsu hut
    obtain ⟨-, -, hb⟩ := hg
    obtain ⟨hβ, hβ1, -⟩ := hb u hsu hut
    have hu : u < 1 := hut.trans_lt (ht1 n)
    exact ⟨(st2sSeq_bounds (g := sz.lam n) (hL n) hu hβ hβ1 m).1,
      st2sSeq_mono_succ (hL n) hu hβ hβ1 m⟩
  · -- `(kwr3juw)`
    intro m
    filter_upwards [hgood] with n hg u hsu hut
    obtain ⟨-, -, hb⟩ := hg
    obtain ⟨hβ, hβ1, -⟩ := hb u hsu hut
    exact st2sSeq_clause4 (hL n) (hut.trans_lt (ht1 n)) hβ hβ1 m
  · -- the floor
    intro D hD
    set j : ℕ := ⌈(2 + D) / c₀⌉₊ with hj
    have hjc : 2 + D ≤ c₀ * ((j : ℝ) + 1) := by
      have h1 : (2 + D) / c₀ ≤ j := Nat.le_ceil _
      rw [div_le_iff₀ hc₀pos] at h1
      nlinarith
    refine ⟨6 * j, ?_⟩
    filter_upwards [hgood, hNlarge ((2 : ℝ) ^ (j + 1))] with n hg hN u hsu hut
    obtain ⟨-, -, hb⟩ := hg
    obtain ⟨hβ, hβ1, hβ2⟩ := hb u hsu hut
    have hu : u < 1 := hut.trans_lt (ht1 n)
    rcases st2sSeq_floor (g := sz.lam n) (hL n) hu hβ hβ1 (6 * j) with h | h
    · right; exact le_of_eq h.symm
    · left
      have hq : (sz.Bctl n u ^ (1 / 6 : ℝ)) ^ (6 * j) = sz.Bctl n u ^ j := by
        have hq6 : (sz.Bctl n u ^ (1 / 6 : ℝ)) ^ 6 = sz.Bctl n u := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]; norm_num
        rw [pow_mul, hq6]
      rw [hq] at h
      have hWd0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (by linarith [hW1 n]) _
      have hT0 : tailT d (sz.L n) (sz.lam n) u 0 = ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u := by
        rw [tailT_zero]; unfold Sizes.Bctl; field_simp
      rw [hT0] at h
      refine h.trans ?_
      calc sz.Bctl n u ^ j * (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u)
          = ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u ^ (j + 1) := by ring
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
            st2s_floor_arith (hW1 n) (hWdN n) (hWN n) hβ.le hβ2 hD hjc hN

/-! ## 5. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`), admissible at `𝔠 = 1/6`,
`𝔡 = 1/10`, `κ = ε = 1/10`, the flow points `z_n = 1/2 + i N_n^{-4/5}` (`flow_z0`), and the times
`s ≡ 0 < t ≡ 1/16 ≤ lemT z_n` (a window of positive length).  Every hypothesis of
`stScaleExists_holds` is discharged; the second instance is at the lower end of `(eq:WO)`
(`sz1`, `ilambda_n = W_n^{-3/2+1/10}`), the third reads two clauses of `STScaleAdm` at the interior
time `u = 1/32`. -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- **Instance 1** (`d = 3`, `sz0`, `s ≡ 0`, `t ≡ 1/16`): the scale family exists. -/
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq :=
  stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => sixteenth_le_lemT n)

/-- **Instance 2** (`d = 3`, `sz1`: the coupling at the lower end of `(eq:WO)`). -/
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz1 sInst tInst Kseq :=
  stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz1 z0 flow_z1 sInst tInst (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => sixteenth_le_lemT n)

/-- **Instance 3**: two clauses of `STScaleAdm` at the interior time `u = 1/32 ∈ (0, 1/16)`. -/
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq ∧
    ∀ᶠ n in atTop, 0 ≤ Kseq 1 n (1 / 32) ∧ Kseq 1 n (1 / 32) ≤ Kseq 2 n (1 / 32) := by
  obtain ⟨K, hK⟩ := stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by norm_num [sInst, tInst]) (fun n => sixteenth_le_lemT n)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hK.2.2.1 1] with n hn
  exact hn (1 / 32) (by norm_num [sInst]) (by norm_num [tInst])

end Instances

end RBM.Gauss.Sizes
