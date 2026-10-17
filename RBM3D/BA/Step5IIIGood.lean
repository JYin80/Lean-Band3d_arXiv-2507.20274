/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Step34Gen
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.KBound
import RBM3D.BA.KInduct
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenSchur
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Induction.Step5Pins

/-!
# Step 5, case `1 - t ≥ λ²`, block Anderson model: the realized parameter `J♯` and the good event

Paper: the good event behind Lemma 5.4 (`lem:pf_step5`): the parameter `𝒥*_{u,D}` (`eq:def_new_J*`,
(5.42)), the stopping time (`eq:def_TTT`, (5.47)) and the hypotheses of Lemma 5.2 (`lem_dec_calE`).
For the block Anderson model the paper omits the details (proof of Steps 3-6 for Theorem 8.2,
`lem:main_ind_BA`).  The band-model counterparts are `lemDecCalEPrec_good`, `lemDecCalEPrec_prob`,
`LemDecCalELip_Jsharp` and `PfStep5Grid_JsharpM`.

The matrix part of the hypothesis bundle of Lemma 5.2, `BAStep5IIIEMatrix`, is written inline.  At
the matrix `H` and the time `u` it says: `H` is Hermitian and (i) `‖(𝓛-𝒦)^{(2)}‖ ≤ J T_{u,D}`; (ii)
`‖𝒦^{(2)}_{(+,-)}‖ ≤ K₀ M_u⁻¹`; (iii) the far field of `𝒦^{(2)}_{(+,-)}` beyond
`ℓ* = (log W)^{3/2}`; (iv) the bound on `STavgMg`; (v) the bounds on `𝓛^{(k)}`, `k = 2, 3, 4, 6`;
(vi) the `J`-free decay of `(𝓛-𝒦)^{(2)}`.

1. `BAStep5IIIJsharp`, `baStep5IIIJsharp_spec`:
   `J♯_{u,D}(H) = max(1, max_{σ,a} ‖(𝓛-𝒦)^{(2)}‖ / T_{u,D}(a))` is `≥ 1` and dominates conjunct (i)
   at every level `D`.
2. `baStep5III_matrix_level`: the matrix part at `(D, J)` gives it at `(D', J♯(D'))` for `D' ≤ D`.
3. `BAStep5IIIGood`, `BAStep5IIIGoodThm`, `baStep5IIIGoodThm_holds`: for `τ', D₁ > 0` and
   `0 < θ < 1`, eventually, at every `u ∈ [s_n, t_n]`, there is an event `G` with
   `seqP (sz.withLam 0) Gᶜ ≤ N^{-D₁}` on which the matrix part holds at `H = seqHflowBA`,
   `Λ = K₀ = N^{τ'}`, `J = J♯`.  Steps 2-4 enter as the four carrier predicates `STAvgUgL`,
   `STLmaxUgL`, `STLKUgL`, `STGdecayWgL`; `STKboundgL` (`baKbound_holds`), the far field
   (`baEMn2ExpHK`) and `𝒦^{(1)} = m(σ)` (`baKsol_one`) are used by name.

The seven failure events (iv), (v) for `k = 2, 3, 4, 6`, and the two events of (vi) (from `STLKUgL`
and `STGdecayWgL`) carry the union over `u` inside, so one event `G` serves every `u`; (ii) and
(iii) are deterministic and made uniform in `u` through a violator sequence.  The scalar part of the
bundle along a flow is in `RBM3D/BA/Step5IIIGood2.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ}

/-! ## 1. Real-analysis helpers -/

section Helpers

/-- `min(x, y) ≤ x^{1-θ} y^θ` for `x, y ≥ 0`, `0 ≤ θ ≤ 1`. -/
theorem Step5IIIGood_min_rpow {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min x y ≤ x ^ (1 - θ) * y ^ θ := by
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hsum : (1 - θ) + θ = 1 := by ring
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    calc x = x ^ (1 - θ) * x ^ θ := by
          rw [← Real.rpow_add' hx (by rw [hsum]; norm_num), hsum, Real.rpow_one]
      _ ≤ x ^ (1 - θ) * y ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx h hθ0) (Real.rpow_nonneg hx _)
  · rw [min_eq_right h]
    calc y = y ^ (1 - θ) * y ^ θ := by
          rw [← Real.rpow_add' hy (by rw [hsum]; norm_num), hsum, Real.rpow_one]
      _ ≤ x ^ (1 - θ) * y ^ θ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy h hθ') (Real.rpow_nonneg hy _)

/-- **The interpolation behind (vi)**: `a ≤ A₁` and `a ≤ A₂ e^{-√r} + F` give
`a ≤ A₁^{1-θ} A₂^θ e^{-θ√r} + F` (`0 < θ < 1`, `A₁, A₂, F ≥ 0`). -/
theorem Step5IIIGood_interp {a A₁ A₂ F θ r : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hF : 0 ≤ F) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (h1 : a ≤ A₁) (h2 : a ≤ A₂ * Real.exp (-Real.sqrt r) + F) :
    a ≤ A₁ ^ (1 - θ) * A₂ ^ θ * Real.exp (-(θ * Real.sqrt r)) + F := by
  have hE : 0 < Real.exp (-Real.sqrt r) := Real.exp_pos _
  have hx : Real.exp (-(θ * Real.sqrt r)) = Real.exp (-Real.sqrt r) ^ θ := by
    rw [← Real.exp_mul]; congr 1; ring
  have hmin : a - F ≤ min A₁ (A₂ * Real.exp (-Real.sqrt r)) := le_min (by linarith) (by linarith)
  have hm := Step5IIIGood_min_rpow hA₁ (mul_nonneg hA₂ hE.le) hθ0.le hθ1.le
  have hmul : (A₂ * Real.exp (-Real.sqrt r)) ^ θ = A₂ ^ θ * Real.exp (-Real.sqrt r) ^ θ :=
    Real.mul_rpow hA₂ hE.le
  have : a - F ≤ A₁ ^ (1 - θ) * A₂ ^ θ * Real.exp (-(θ * Real.sqrt r)) := by
    calc a - F ≤ A₁ ^ (1 - θ) * (A₂ * Real.exp (-Real.sqrt r)) ^ θ := hmin.trans hm
      _ = A₁ ^ (1 - θ) * A₂ ^ θ * Real.exp (-(θ * Real.sqrt r)) := by rw [hmul, hx]; ring
  linarith

/-- `Bctl ≥ 0` for `0 ≤ L`-type data (positivity). -/
theorem Step5IIIGood_Bctl_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) : 0 ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  positivity

/-- `W^{-d} B_{u,0} ≤ 2 (W^d (1-u))⁻¹` for `u < 1` (`B_{u,0} = (g²+1-u)⁻¹ + (L^d(1-u))⁻¹ ≤ 2 (1-u)⁻¹`, `L ≥ 1`). -/
theorem Step5IIIGood_Bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
    sz.Bctl n u ≤ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
  have hv : 0 < 1 - u := by linarith
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL
  have h1 : (sz.lam n ^ 2 + |1 - u|)⁻¹ ≤ (1 - u)⁻¹ := by
    rw [abs_of_pos hv]
    exact inv_anti₀ hv (by nlinarith [sq_nonneg (sz.lam n)])
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ≤ (1 - u)⁻¹ := by
    rw [abs_of_pos hv]
    exact inv_anti₀ hv (le_mul_of_one_le_left hv.le hLd)
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hrhs : 2 * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (1 - u)⁻¹) := by
    rw [mul_inv]; ring
  rw [hrhs]
  unfold Sizes.Bctl Bparam
  refine mul_le_mul_of_nonneg_left ?_ hWd
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  linarith

/-- `STWB(K) ≤ Bctl` (`((K+1)^{d-2})⁻¹ ≤ 1`), and `STWB ≥ 0`. -/
theorem Step5IIIGood_STWB_le {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (K : ℕ) :
    0 ≤ STWB sz n u K ∧ STWB sz n u K ≤ sz.Bctl n u := by
  refine ⟨by unfold STWB Bparam; positivity, ?_⟩
  unfold STWB Sizes.Bctl
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold Bparam
  have h1 : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ (d - 2) := one_le_pow₀ (by have := (Nat.cast_nonneg K : (0 : ℝ) ≤ K); linarith)
  have h2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one]
    exact inv_le_one_of_one_le₀ h1
  have h3 : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  linarith [mul_le_mul_of_nonneg_left h2 h3]

/-- In the regime `g² ≤ 1 - u` the range is `ℓ_u = 1` (`L ≥ 1`). -/
theorem Step5IIIGood_ellT_eq_one {L : ℕ} {g u : ℝ} (hL : 1 ≤ L) (hu : u < 1) (h : g ^ 2 ≤ 1 - u) :
    ellT L g u = 1 := by
  have hv : 0 < 1 - u := by linarith
  have hsq : 0 < Real.sqrt |1 - u| := Real.sqrt_pos.mpr (by rw [abs_of_pos hv]; exact hv)
  have hg : g ≤ Real.sqrt |1 - u| := by
    rw [abs_of_pos hv]
    calc g ≤ |g| := le_abs_self g
      _ = Real.sqrt (g ^ 2) := (Real.sqrt_sq_eq_abs g).symm
      _ ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt h
  have hx : g / Real.sqrt |1 - u| ≤ 1 := (div_le_one hsq).2 hg
  unfold ellT
  rw [max_eq_right hx, min_eq_left (by exact_mod_cast hL)]

/-- A statement about all times `u ∈ [s_n, t_n]` follows from its sequence form (a violator sequence). -/
theorem Step5IIIGood_uniform {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (Q : ∀ n : ℕ, ℝ → Prop)
    (h : ∀ τ : ℕ → ℝ, (∀ n, s n ≤ τ n ∧ τ n ≤ t n) → ∀ᶠ n in atTop, Q n (τ n)) :
    ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, Q n (u : ℝ) := by
  classical
  let τ : ℕ → ℝ := fun n =>
    if hv : ∃ u : TimeIcc s t n, ¬ Q n (u : ℝ) then ((Classical.choose hv : TimeIcc s t n) : ℝ) else s n
  have hτ : ∀ n, s n ≤ τ n ∧ τ n ≤ t n := by
    intro n
    by_cases hv : ∃ u : TimeIcc s t n, ¬ Q n (u : ℝ)
    · simp only [τ, hv, dite_true]; exact (Classical.choose hv).2
    · simp only [τ, hv, dite_false]; exact ⟨le_rfl, hst n⟩
  filter_upwards [h τ hτ] with n hn u
  by_contra hu
  have hv : ∃ u : TimeIcc s t n, ¬ Q n (u : ℝ) := ⟨u, hu⟩
  have e : τ n = ((Classical.choose hv : TimeIcc s t n) : ℝ) := by simp only [τ, hv, dite_true]
  exact (Classical.choose_spec hv) (e ▸ hn)

/-- A `≺` between deterministic quantities holds with the scale factor (the bad set is `∅` or the whole space, of mass `1`). -/
theorem Step5IIIGood_det_of_prec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (size : ℕ → ℕ) {U : ℕ → Type*} (ξ ζ : ∀ n, U n → ℝ)
    (h : StochDomAt P size (fun n u _ => ξ n u) (fun n u _ => ζ n u)) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, 2 ≤ size n → ∀ u, ξ n u ≤ (size n : ℝ) ^ τ * ζ n u := by
  filter_upwards [h τ hτ 1 one_pos] with n hn h2 u
  by_contra hlt0
  have hlt := not_le.1 hlt0
  have hset : badSetAt (Ω := Ω) size (fun n u _ => ξ n u) (fun n u _ => ζ n u) τ n = Set.univ := by
    ext ω; simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact ⟨u, hlt⟩
  rw [hset, measure_univ] at hn
  have h2' : (2 : ℝ) ≤ (size n : ℝ) := by exact_mod_cast h2
  have hlt1 : (size n : ℝ) ^ (-1 : ℝ) < 1 := by
    rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have := (ENNReal.one_le_ofReal).1 hn
  linarith

/-- The failure event of a `≺`, packaged: eventually, an event `B` of mass `≤ N^{-D}` off which `ξ ≤ N^τ ζ` for every index. -/
theorem Step5IIIGood_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → Ω → ℝ} (h : StochDomAt P size ξ ζ) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ n in atTop, ∃ B : Set Ω, P B ≤ ENNReal.ofReal ((size n : ℝ) ^ (-D)) ∧
      ∀ ω, ω ∉ B → ∀ u : U n, ξ n u ω ≤ (size n : ℝ) ^ τ * ζ n u ω := by
  filter_upwards [h τ hτ D hD] with n hn
  refine ⟨badSetAt size ξ ζ τ n, hn, fun ω hω u => ?_⟩
  by_contra hlt0
  exact hω ⟨u, not_le.1 hlt0⟩

/-- Union bound for seven events of probability `≤ c` (as the private `lemDecCalEPrec_union7` of the band model). -/
theorem Step5IIIGood_union7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B₁ B₂ B₃ B₄ B₅ B₆ B₇ : Set Ω} {c : ℝ} (h₁ : P B₁ ≤ ENNReal.ofReal c)
    (h₂ : P B₂ ≤ ENNReal.ofReal c) (h₃ : P B₃ ≤ ENNReal.ofReal c) (h₄ : P B₄ ≤ ENNReal.ofReal c)
    (h₅ : P B₅ ≤ ENNReal.ofReal c) (h₆ : P B₆ ≤ ENNReal.ofReal c) (h₇ : P B₇ ≤ ENNReal.ofReal c) :
    P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ B₇) ≤ ENNReal.ofReal (7 * c) := by
  have e : ∀ A B : Set Ω, P (A ∪ B) ≤ P A + P B := fun A B => measure_union_le A B
  calc P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ B₇)
      ≤ P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆) + P B₇ := e _ _
    _ ≤ (P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) + P B₆) + P B₇ := add_le_add (e _ _) le_rfl
    _ ≤ ((P (B₁ ∪ B₂ ∪ B₃ ∪ B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (e _ _) le_rfl) le_rfl
    _ ≤ (((P (B₁ ∪ B₂ ∪ B₃) + P B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (add_le_add (e _ _) le_rfl) le_rfl) le_rfl
    _ ≤ ((((P (B₁ ∪ B₂) + P B₃) + P B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (add_le_add (add_le_add (e _ _) le_rfl) le_rfl) le_rfl) le_rfl
    _ ≤ (((((P B₁ + P B₂) + P B₃) + P B₄) + P B₅) + P B₆) + P B₇ :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (e _ _) le_rfl) le_rfl) le_rfl)
          le_rfl) le_rfl
    _ ≤ (((((ENNReal.ofReal c + ENNReal.ofReal c) + ENNReal.ofReal c) + ENNReal.ofReal c) +
          ENNReal.ofReal c) + ENNReal.ofReal c) + ENNReal.ofReal c := by gcongr
    _ = ENNReal.ofReal (7 * c) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring

/-- **The power-of-`W` chain of (vi)**: with `T = 2τ`, `Bc ≤ T`, `y ≤ Bc`, `ρ ≤ W^d`, `τ⁻¹ ≤ W^d`,
`(Bc²)^{1-θ} (ρ^{Cd} Bc^{1/5} y)^θ ≤ 4 (W^d)^{θ(Cd+1)} τ²`. -/
theorem Step5IIIGood_vi_core {Bc y ρ Wd τ θ Cd : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hCd : 0 < Cd)
    (hτ : 0 < τ) (hBc0 : 0 ≤ Bc) (hBc : Bc ≤ 2 * τ) (hy0 : 0 ≤ y) (hy : y ≤ Bc)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Wd) (hτW : τ⁻¹ ≤ Wd) (hWd1 : 1 ≤ Wd) :
    (Bc ^ 2) ^ (1 - θ) * (ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y) ^ θ ≤ 4 * Wd ^ (θ * (Cd + 1)) * τ ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * τ := ⟨_, rfl⟩
  rw [← hT] at hBc
  have hT0 : 0 < T := by rw [hT]; positivity
  have hWd0 : 0 < Wd := by linarith
  have e1 : (Bc ^ 2) ^ (1 - θ) ≤ (T ^ 2) ^ (1 - θ) :=
    Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ hBc0 hBc 2) (by linarith)
  have e2 : ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y ≤ Wd ^ Cd * T ^ (1 / 5 : ℝ) * T := by
    have a1 : ρ ^ Cd ≤ Wd ^ Cd := Real.rpow_le_rpow hρ0 hρ hCd.le
    have a2 : Bc ^ (1 / 5 : ℝ) ≤ T ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hBc0 hBc (by norm_num)
    exact mul_le_mul (mul_le_mul a1 a2 (Real.rpow_nonneg hBc0 _) (Real.rpow_nonneg hWd0.le _)) (hy.trans hBc) hy0
      (by positivity)
  have e3 : (ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y) ^ θ ≤ (Wd ^ Cd * T ^ (1 / 5 : ℝ) * T) ^ θ :=
    Real.rpow_le_rpow (by positivity) e2 hθ0.le
  have hT2 : (T ^ 2) ^ (1 - θ) = T ^ (2 * (1 - θ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hm : (Wd ^ Cd * T ^ (1 / 5 : ℝ) * T) ^ θ = Wd ^ (Cd * θ) * (T ^ (1 / 5 * θ) * T ^ θ) := by
    rw [Real.mul_rpow (by positivity) hT0.le, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hWd0.le, ← Real.rpow_mul hT0.le]; ring
  have hTe : T ^ (2 * (1 - θ)) * (T ^ (1 / 5 * θ) * T ^ θ) = T ^ 2 * T ^ (-(4 * θ / 5)) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
    have : T ^ (2 : ℝ) = T ^ 2 := by rw [Real.rpow_two]
    rw [← this, ← Real.rpow_add hT0]; congr 1; ring
  have hTinv : T ^ (-(4 * θ / 5)) ≤ Wd ^ (4 * θ / 5) := by
    rw [Real.rpow_neg hT0.le, ← Real.inv_rpow hT0.le]
    refine Real.rpow_le_rpow (inv_nonneg.2 hT0.le) ?_ (by positivity)
    calc T⁻¹ ≤ τ⁻¹ := by rw [hT]; exact inv_anti₀ hτ (by linarith)
      _ ≤ Wd := hτW
  have hWe : Wd ^ (Cd * θ) * Wd ^ (4 * θ / 5) ≤ Wd ^ (θ * (Cd + 1)) := by
    rw [← Real.rpow_add hWd0]
    exact Real.rpow_le_rpow_of_exponent_le hWd1 (by nlinarith)
  calc (Bc ^ 2) ^ (1 - θ) * (ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y) ^ θ
      ≤ (T ^ 2) ^ (1 - θ) * (Wd ^ Cd * T ^ (1 / 5 : ℝ) * T) ^ θ :=
        mul_le_mul e1 e3 (by positivity) (by positivity)
    _ = Wd ^ (Cd * θ) * (T ^ (2 * (1 - θ)) * (T ^ (1 / 5 * θ) * T ^ θ)) := by rw [hT2, hm]; ring
    _ = Wd ^ (Cd * θ) * (T ^ 2 * T ^ (-(4 * θ / 5))) := by rw [hTe]
    _ ≤ Wd ^ (Cd * θ) * (T ^ 2 * Wd ^ (4 * θ / 5)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTinv (by positivity)) (by positivity)
    _ = T ^ 2 * (Wd ^ (Cd * θ) * Wd ^ (4 * θ / 5)) := by ring
    _ ≤ T ^ 2 * Wd ^ (θ * (Cd + 1)) := mul_le_mul_of_nonneg_left hWe (by positivity)
    _ = 4 * Wd ^ (θ * (Cd + 1)) * τ ^ 2 := by rw [hT]; ring


/-- **(vi) as a real-number statement**: `a ≤ q Bc²` and `a ≤ q (A₂ e^{-√r} + F)` (`A₂ = ρ^{Cd} Bc^{1/5} y`) give
`a ≤ (W^d)^{θ(Cd+1)} Q τ² e^{-θ√r} + W_f` once `4q ≤ Q` and `qF ≤ W_f`. -/
theorem Step5IIIGood_vi_alg {a q Bc y ρ Wd τ θ Cd F r Wf Q : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hCd : 0 < Cd)
    (hτ : 0 < τ) (hBc0 : 0 ≤ Bc) (hBc : Bc ≤ 2 * τ) (hy0 : 0 ≤ y) (hy : y ≤ Bc)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Wd) (hτW : τ⁻¹ ≤ Wd) (hWd1 : 1 ≤ Wd) (hq : 0 < q) (hF : 0 ≤ F)
    (ha1 : a ≤ q * Bc ^ 2) (ha2 : a ≤ q * (ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y * Real.exp (-Real.sqrt r) + F))
    (hq4 : 4 * q ≤ Q) (hFW : q * F ≤ Wf) :
    a ≤ Wd ^ (θ * (Cd + 1)) * Q * τ ^ 2 * Real.exp (-(θ * Real.sqrt r)) + Wf := by
  have hWd0 : 0 < Wd := by linarith
  have hA₂ : 0 ≤ ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y := by positivity
  have h := Step5IIIGood_interp (a := a / q) (A₁ := Bc ^ 2) (A₂ := ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y) (F := F) (θ := θ) (r := r)
    (by positivity) hA₂ hF hθ0 hθ1 ((div_le_iff₀ hq).2 (by linarith)) ((div_le_iff₀ hq).2 (by linarith))
  have hc := Step5IIIGood_vi_core hθ0 hθ1 hCd hτ hBc0 hBc hy0 hy hρ0 hρ hτW hWd1
  have hE : 0 ≤ Real.exp (-(θ * Real.sqrt r)) := (Real.exp_pos _).le
  have hP : 0 ≤ Wd ^ (θ * (Cd + 1)) * τ ^ 2 * Real.exp (-(θ * Real.sqrt r)) := by positivity
  calc a ≤ ((Bc ^ 2) ^ (1 - θ) * (ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y) ^ θ * Real.exp (-(θ * Real.sqrt r)) + F) * q :=
        (div_le_iff₀ hq).1 h
    _ = (Bc ^ 2) ^ (1 - θ) * (ρ ^ Cd * Bc ^ (1 / 5 : ℝ) * y) ^ θ * Real.exp (-(θ * Real.sqrt r)) * q + q * F := by ring
    _ ≤ 4 * Wd ^ (θ * (Cd + 1)) * τ ^ 2 * Real.exp (-(θ * Real.sqrt r)) * q + Wf := by
        refine add_le_add ?_ hFW
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hE) hq.le
    _ = (Wd ^ (θ * (Cd + 1)) * τ ^ 2 * Real.exp (-(θ * Real.sqrt r))) * (4 * q) + Wf := by ring
    _ ≤ (Wd ^ (θ * (Cd + 1)) * τ ^ 2 * Real.exp (-(θ * Real.sqrt r))) * Q + Wf := by
        gcongr
    _ = Wd ^ (θ * (Cd + 1)) * Q * τ ^ 2 * Real.exp (-(θ * Real.sqrt r)) + Wf := by ring

end Helpers

/-! ## 2. The realized parameter `J♯` -/

section Jsharp

/-- **The realized parameter** `J♯_{u,D}(H) = max(1, max_{σ,a} ‖(𝓛-𝒦)^{(2)}_{u,σ,a}(H)‖ / T_{u,D}(|a₁-a₂|))` at the block Anderson
carrier (`eq:def_new_J*`, (5.42); the band counterpart is `PfStep5Grid_JsharpM`). -/
def BAStep5IIIJsharp {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩ (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
    ‖STLKMg (baStep2Mat sz lam0 E) n u H p.1 p.2‖ / STtailTD sz n u D p.2))

/-- `T_{u,D}(a) > 0` (`W^{-D} > 0`). -/
theorem Step5IIIGood_tail_pos {d : ℕ} (sz : Sizes d) (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    0 < STtailTD sz n u D a := by
  unfold STtailTD tailTD
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact add_pos_of_nonneg_of_pos (by positivity) (Real.rpow_pos_of_pos hW _)

/-- `1 ≤ J♯` and conjunct (i) `‖(𝓛-𝒦)^{(2)}‖ ≤ J♯ T_{u,D}` at every level `D`. -/
theorem baStep5IIIJsharp_spec (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      1 ≤ BAStep5IIIJsharp sz lam0 E n D u H ∧
        ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
          ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ BAStep5IIIJsharp sz lam0 E n D u H * STtailTD sz n u D a := by
  intro sz lam0 E n D u H
  refine ⟨le_max_left _ _, fun σ a => ?_⟩
  have hT := Step5IIIGood_tail_pos sz n u D a
  have h : ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ / STtailTD sz n u D a ≤ BAStep5IIIJsharp sz lam0 E n D u H :=
    (Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKMg (baStep2Mat sz lam0 E) n u H p.1 p.2‖ / STtailTD sz n u D p.2) (Finset.mem_univ (σ, a))).trans (le_max_right _ _)
  exact (div_le_iff₀ hT).1 h

end Jsharp

/-! ## 3. Level monotonicity of the matrix part -/

section Level

/-- The matrix part of the bundle (written inline) at `(D, J)` gives it at
`(D', J♯(D'))` for every `D' ≤ D`.  (i) is `baStep5IIIJsharp_spec`; (iii) and (vi) carry the floor `W^{-D} ≤ W^{-D'}`; the
other conjuncts carry neither `D` nor `J`. -/
theorem baStep5III_matrix_level (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D D' Λ K₀ J θ Cd : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      D' ≤ D →
      (H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ J * STtailTD sz n u D a) ∧
        (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
        (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
          ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
        (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
        (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
        (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) ∧
        (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
        (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) ∧
        (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ *
          ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))) →
      (H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ BAStep5IIIJsharp sz lam0 E n D' u H * STtailTD sz n u D' a) ∧
        (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
        (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
          ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
        (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
        (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
        (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) ∧
        (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
        (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) ∧
        (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ *
          ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D'))) := by
  intro sz lam0 E n u D D' Λ K₀ J θ Cd H hD h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hfl : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  refine ⟨h0, (baStep5IIIJsharp_spec d sz lam0 E n D' u H).2, h2, fun a b hab => (h3 a b hab).trans hfl, h4, h5, h6, h7, h8,
    fun σ a => (h9 σ a).trans (add_le_add_right hfl _)⟩

end Level

/-! ## 4. The per-time good event -/

section Good

/-- **The per-time good event of Step 5, case (iii), at the block Anderson model** (the law is written out, `J♯` is the realized
parameter and the matrix part is written inline): for `τ', D₁ > 0` and `0 < θ < 1`, eventually, at every
`u ∈ [s_n, t_n]`, there is an event `G` with `seqP (sz.withLam 0) Gᶜ ≤ N^{-D₁}` on which the matrix part of the bundle holds at
`H = seqHflowBA`, `Λ = K₀ = N^{τ'}`, `J = J♯_{u,D}(H)`. -/
def BAStep5IIIGood (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (D Cd : ℝ) : Prop :=
  ∀ τ' D₁ θ : ℝ, 0 < τ' → 0 < D₁ → 0 < θ → θ < 1 → ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, ∃ G : Set sz.SeqΩ,
    Sizes.seqP (sz.withLam 0) Gᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G,
      let H := sz.seqHflowBA (BAflowLam0 sz z) n (u : ℝ) ω;
      let J := BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n D (u : ℝ) H;
      H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ a‖ ≤ J * STtailTD sz n (u : ℝ) D a) ∧
      (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).K n (u : ℝ) ![true, false] ![a, b]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) ∧
      (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).K n (u : ℝ) ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
      (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) ∧
      (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LM n (u : ℝ) H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) ∧
      (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LM n (u : ℝ) H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) ^ 2) ∧
      (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LM n (u : ℝ) H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) ^ 3) ∧
      (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LM n (u : ℝ) H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) ^ 5) ∧
      (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (((d : ℕ) : ℝ) * (Cd + 1))) * ((sz.size n : ℕ) : ℝ) ^ τ' *
        ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **The per-time good event holds** (`BAStep5IIIGood` at every level `D > 0`) for a block Anderson flow with `t_n ≤ t₀` in the
regime `lam² ≤ 1 - t`, given the four carrier predicates of Steps 2-4 (`STAvgUgL`, `STLmaxUgL`, `STLKUgL`,
`STGdecayWgL`).  The hypotheses `0 < ε`, `0 < 𝔡` serve `baEMn2ExpHK` and `baKbound_holds`, and `0 < Cd` serves (vi);
`STKboundgL` is not a hypothesis (it is `baKbound_holds`). -/
def BAStep5IIIGoodThm (d : ℕ) : Prop :=
  3 ≤ d → ∀ (κ ε 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
      STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
        ∀ D : ℝ, 0 < D → BAStep5IIIGood sz z s t D Cd

/-- The scale step of (ii), (iv), (v): `x ≤ q Bc^m`, `Bc ≤ 2τ`, `2^m q ≤ Q` give `x ≤ Q τ^m`. -/
theorem Step5IIIGood_scale {x q Bc τ Q : ℝ} (m : ℕ) (hq : 0 ≤ q) (hBc0 : 0 ≤ Bc) (hBc : Bc ≤ 2 * τ) (hτ : 0 ≤ τ)
    (hQ : 2 ^ m * q ≤ Q) (hx : x ≤ q * Bc ^ m) : x ≤ Q * τ ^ m := by
  calc x ≤ q * Bc ^ m := hx
    _ ≤ q * (2 * τ) ^ m := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBc0 hBc m) hq
    _ = (2 ^ m * q) * τ ^ m := by rw [mul_pow]; ring
    _ ≤ Q * τ ^ m := mul_le_mul_of_nonneg_right hQ (by positivity)

/-- `(W^d)^{θ(Cd+1)} = W^{θ(d(Cd+1))}`. -/
theorem Step5IIIGood_Wpow (d : ℕ) {W : ℝ} (hW : 0 ≤ W) (θ Cd : ℝ) :
    (W ^ d) ^ (θ * (Cd + 1)) = W ^ (θ * ((d : ℝ) * (Cd + 1))) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]; congr 1; ring

theorem baStep5IIIGoodThm_holds (d : ℕ) : BAStep5IIIGoodThm d := by
  intro hd κ ε 𝔠 𝔡 Cd sz z hκ hε h𝔡 hCd hflow s t hs hst hT hReg hAvg hLmax hLK hDec D hD τ' D₁ θ hτ' hD₁ hθ0 hθ1
  obtain ⟨h𝔠, -, hsize, hband, hWO⟩ := hflow.1
  have hτ₀ : 0 < τ' / 2 := by linarith
  have hD1 : 0 < D₁ + 1 := by linarith
  have hD'' : 0 < D + τ' / 𝔠 := by have := div_pos hτ' h𝔠; linarith
  have eAvg := Step5IIIGood_event hAvg hτ₀ hD1
  have eL2 := Step5IIIGood_event (hLmax 2 (by norm_num)) hτ₀ hD1
  have eL3 := Step5IIIGood_event (hLmax 3 (by norm_num)) hτ₀ hD1
  have eL4 := Step5IIIGood_event (hLmax 4 (by norm_num)) hτ₀ hD1
  have eL6 := Step5IIIGood_event (hLmax 6 (by norm_num)) hτ₀ hD1
  have eLK := Step5IIIGood_event (hLK 2 (by norm_num)) hτ₀ hD1
  have eDec := Step5IIIGood_event (hDec (D + τ' / 𝔠) hD'') hτ₀ hD1
  have hT1 : ∀ n, t n < 1 := fun n => (hT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  -- (ii): `‖𝒦^{(2)}_{(+,-)}‖ ≤ N^{τ'/2} Bctl`, deterministic, uniform in `u` (violator sequence)
  have hii : ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, 2 ≤ sz.size n → ∀ a b : Zd d (sz.L n),
      ‖(baFMz sz z).K n (u : ℝ) ![true, false] ![a, b]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * sz.Bctl n (u : ℝ) ^ 1 := by
    refine Step5IIIGood_uniform (fun n => (hst n).le) (fun n u => 2 ≤ sz.size n → ∀ a b : Zd d (sz.L n),
      ‖(baFMz sz z).K n u ![true, false] ![a, b]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * sz.Bctl n u ^ 1) fun τ hτ => ?_
    have hK := baKbound_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow τ (fun n => (hs n).trans (hτ n).1)
      (fun n => ((hτ n).2.trans (hT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)) 2 (by norm_num)
    have := Step5IIIGood_det_of_prec (Sizes.seqP (sz.withLam 0)) sz.size
      (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ‖(baFMz sz z).K n (τ n) p.1 p.2‖)
      (fun n _ => sz.Bctl n (τ n) ^ (2 - 1)) hK hτ₀
    filter_upwards [this] with n hn h2 a b
    exact hn h2 (![true, false], ![a, b])
  -- (iii): the far field, deterministic, uniform in `u`
  have hiii : ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, ∀ (x x' : Zd d (sz.L n)) (b : Bool),
      emn2ExpEllStar sz n (u : ℝ) ≤ (zdistInf d (sz.L n) (x - x') : ℝ) →
        ‖(baFMz sz z).K n (u : ℝ) ![b, !b] ![x, x']‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(D + ((d : ℕ) : ℝ))) := by
    refine Step5IIIGood_uniform (fun n => (hst n).le) (fun n u => ∀ (x x' : Zd d (sz.L n)) (b : Bool),
      emn2ExpEllStar sz n u ≤ (zdistInf d (sz.L n) (x - x') : ℝ) →
        ‖(baFMz sz z).K n u ![b, !b] ![x, x']‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(D + ((d : ℕ) : ℝ)))) fun τ hτ => ?_
    exact baEMn2ExpHK hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow τ (fun n => (hs n).trans (hτ n).1) (fun n => (hτ n).2.trans (hT n)) D hD
  have hN7 := hsize.eventually_ge_atTop 7
  have hq32 : ∀ᶠ n in atTop, (32 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop hτ₀).comp hsize).eventually_ge_atTop 32
  have hlam0 := BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow
  filter_upwards [eAvg, eL2, eL3, eL4, eL6, eLK, eDec, hii, hiii, hN7, hq32, hlam0, hWO, hband] with n
    ⟨B1, hB1, h1⟩ ⟨B2, hB2, h2⟩ ⟨B3, hB3, h3⟩ ⟨B4, hB4, h4⟩ ⟨B5, hB5, h5⟩ ⟨B6, hB6, h6⟩ ⟨B7, hB7, h7⟩ hii' hiii' hN7' hq32'
    hlam0' hWO' hband' u
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  refine ⟨(B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7)ᶜ, ?_, ?_⟩
  · refine le_of_eq_of_le (congrArg (Sizes.seqP (sz.withLam 0)) (compl_compl _)) ?_
    refine (Step5IIIGood_union7 _ hB1 hB2 hB3 hB4 hB5 hB6 hB7).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) = ((sz.size n : ℕ) : ℝ) ^ (-D₁) * ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [e, Real.rpow_neg_one]
    have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have : 7 * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN7'
    nlinarith
  · intro ω hω
    have hω7 : ω ∉ B7 := fun h => hω (Or.inr h)
    have hω6 : ω ∉ B6 := fun h => hω (Or.inl (Or.inr h))
    have hω5 : ω ∉ B5 := fun h => hω (Or.inl (Or.inl (Or.inr h)))
    have hω4 : ω ∉ B4 := fun h => hω (Or.inl (Or.inl (Or.inl (Or.inr h))))
    have hω3 : ω ∉ B3 := fun h => hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    have hω2 : ω ∉ B2 := fun h => hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
    have hω1 : ω ∉ B1 := fun h => hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
    intro H J
    -- scalar facts at `(n, u)`
    have hu0 : 0 ≤ (u : ℝ) := (hs n).trans u.2.1
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (hT1 n)
    have hureg : sz.lam n ^ 2 ≤ 1 - (u : ℝ) := by have := hReg n; linarith [u.2.2]
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
    have hell : ellT (sz.L n) (sz.lam n) (u : ℝ) = 1 := Step5IIIGood_ellT_eq_one hL1 hu1 hureg
    have hq0 : 0 < ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) := Real.rpow_pos_of_pos hN0 _
    have hQ : ((sz.size n : ℕ) : ℝ) ^ τ' = ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hQ2 : ∀ m : ℕ, m ≤ 5 → 2 ^ m * ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by
      intro m hm
      have : (2 : ℝ) ^ m ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) hm
      rw [hQ]; nlinarith
    have hBc0 := Step5IIIGood_Bctl_nonneg sz n (u : ℝ)
    have hBc := Step5IIIGood_Bctl_le sz n hu1
    have hτ0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹ := by
      have : 0 < 1 - (u : ℝ) := by linarith
      positivity
    have hN2 : 2 ≤ sz.size n := by
      have : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    refine ⟨RBM.Graph.BAAuxGraph2_seqHflowBA_herm sz n (BAflowLam0 sz z) (u : ℝ) ω,
      (baStep5IIIJsharp_spec d sz (BAflowLam0 sz z) (BAflowEs sz z) n D (u : ℝ) H).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (ii)
      intro a b
      have h := Step5IIIGood_scale 1 hq0.le hBc0 hBc hτ0 (hQ2 1 (by norm_num)) (hii' u hN2 a b)
      rw [pow_one] at h
      exact h
    · -- (iii)
      intro a b hab
      have h := hiii' u a b true (by unfold emn2ExpEllStar; rw [hell, mul_one]; exact hab)
      refine h.trans ?_
      have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
      have hWm : ((sz.W n : ℕ) : ℝ) ^ (-(D + ((d : ℕ) : ℝ))) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (by have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d; linarith)
      have hWm0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D + ((d : ℕ) : ℝ))) := Real.rpow_nonneg (by linarith) _
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(D + ((d : ℕ) : ℝ)))
          ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-(D + ((d : ℕ) : ℝ))) := mul_le_mul_of_nonneg_right hWd hWm0
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by rw [one_mul]; exact hWm
    · -- (iv): `𝒦^{(1)} = m(σ)` (`baKsol_one`) and `STAvgUgL`
      intro σ a
      have hg : 0 < BAflowLam0 sz z n := hlam0'.1
      have hreal := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
      have hK1 : (baFMz sz z).K n (u : ℝ) (fun _ : Fin 1 => σ) (fun _ => a) =
          PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) σ :=
        baKsol_one d hκ hg (sz.three_le_L n) (sz.W n) hreal ⟨hu0, hu1⟩ (fun _ => σ) (fun _ => a)
      have h := Step5IIIGood_scale 1 hq0.le hBc0 hBc hτ0 (hQ2 1 (by norm_num)) (h1 ω hω1 (u, (fun _ : Fin 1 => σ), (fun _ => a)))
      rw [pow_one] at h
      have e : STavgMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ a =
          (baFMz sz z).L n (u : ℝ) (fun _ : Fin 1 => σ) (fun _ => a) ω - (baFMz sz z).K n (u : ℝ) (fun _ : Fin 1 => σ) (fun _ => a) := by
        rw [hK1]; rfl
      rw [e]; exact h
    · -- (v), `k = 2`
      intro σ a
      have h := Step5IIIGood_scale 1 hq0.le hBc0 hBc hτ0 (hQ2 1 (by norm_num)) (h2 ω hω2 (u, σ, a))
      rw [pow_one] at h; exact h
    · -- (v), `k = 3`
      intro σ a
      exact Step5IIIGood_scale 2 hq0.le hBc0 hBc hτ0 (hQ2 2 (by norm_num)) (h3 ω hω3 (u, σ, a))
    · -- (v), `k = 4`
      intro σ a
      exact Step5IIIGood_scale 3 hq0.le hBc0 hBc hτ0 (hQ2 3 (by norm_num)) (h4 ω hω4 (u, σ, a))
    · -- (v), `k = 6`
      intro σ a
      exact Step5IIIGood_scale 5 hq0.le hBc0 hBc hτ0 (hQ2 5 (by norm_num)) (h5 ω hω5 (u, σ, a))
    · -- (vi): interpolation of `STLKUgL` and `STGdecayWgL`
      intro σ a
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
      have hv : 0 < 1 - (u : ℝ) := by linarith
      have hWd3 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
      have hτpos : 0 < (((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹ := by positivity
      -- `1 ≤ lam² W^d` from `(eq:WO)`
      have hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
        (Real.one_le_rpow hW1 (by linarith)).trans (sz.lam_sq_mul_pow_ge n hWO'.1)
      have hρ0 : 0 ≤ (1 - s n) / (1 - (u : ℝ)) := div_nonneg (by linarith [u.2.1]) hv.le
      have hρ : (1 - s n) / (1 - (u : ℝ)) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
        rw [div_le_iff₀ hv]
        nlinarith [mul_le_mul_of_nonneg_right hureg (by linarith : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d), hs n]
      have hτW : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
        rw [inv_inv]; nlinarith
      have hq4 : 4 * ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by rw [hQ]; nlinarith
      have hFW : ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(D + τ' / 𝔠)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
        have h1' := sz.size_rpow_le_W_rpow h𝔠 n hband' hτ₀.le
        calc ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(D + τ' / 𝔠))
            ≤ ((sz.W n : ℕ) : ℝ) ^ (τ' / 2 / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-(D + τ' / 𝔠)) :=
              mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg hW0.le _)
          _ = ((sz.W n : ℕ) : ℝ) ^ (τ' / 2 / 𝔠 + -(D + τ' / 𝔠)) := (Real.rpow_add hW0 _ _).symm
          _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
              refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
              have : τ' / 2 / 𝔠 = τ' / 𝔠 / 2 := by ring
              have h2 : 0 < τ' / 𝔠 := div_pos hτ' h𝔠
              linarith
      have hLK1 := h6 ω hω6 (u, σ, a)
      have hDec1 := h7 ω hω7 (u, σ, a)
      rw [hell, div_one, ← Real.sqrt_eq_rpow] at hDec1
      obtain ⟨hy0, hy⟩ := Step5IIIGood_STWB_le sz n (u : ℝ) (zdistInf d (sz.L n) (a 0 - a 1))
      have hvi := Step5IIIGood_vi_alg (a := ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ a‖)
        (q := ((sz.size n : ℕ) : ℝ) ^ (τ' / 2)) (Bc := sz.Bctl n (u : ℝ))
        (y := STWB sz n (u : ℝ) (zdistInf d (sz.L n) (a 0 - a 1))) (ρ := (1 - s n) / (1 - (u : ℝ)))
        (Wd := ((sz.W n : ℕ) : ℝ) ^ d) (τ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - (u : ℝ)))⁻¹) (θ := θ) (Cd := Cd)
        (F := ((sz.W n : ℕ) : ℝ) ^ (-(D + τ' / 𝔠))) (r := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))
        (Wf := ((sz.W n : ℕ) : ℝ) ^ (-D)) (Q := ((sz.size n : ℕ) : ℝ) ^ τ')
        hθ0 hθ1 hCd hτpos hBc0 hBc hy0 hy hρ0 hρ hτW hWd3 hq0 (Real.rpow_nonneg hW0.le _) hLK1 hDec1 hq4 hFW
      rw [Step5IIIGood_Wpow d hW0.le θ Cd] at hvi
      exact hvi

end Good

end RBM.BA
