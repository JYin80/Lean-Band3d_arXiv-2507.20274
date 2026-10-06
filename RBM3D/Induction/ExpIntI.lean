/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ExpWardI
import RBM3D.Induction.ExpIntII
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpEtermsB
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpDuhamel
import RBM3D.Evolution.Prec

/-!
# S6-09a (T2239): the integrated estimate of regime (i), `σ₁ = σ₂`, and the primed consumer

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:97,104-132` (regime (i)),
`paper/tex/3_5_Loop_Hierarchy.tex:1630-1662` (`lem:sum_decay`, `(sum_res_2_NAL)` `3_5:1649`,
`(sum_res_2)` `3_5:1659`).

This file (first half of the split S6-09, DECISIONS §9, §73 (3)) contains:
* the primed definitions `STExpIntQConcl'` (the merged `STExpIntQConcl`, `Step6Pins.lean:409`, with
  `0 < C → 0 < c →`) and `STExpIntI'` (the merged `STExpIntI`, `Step6Pins.lean:449`, with the primed
  Ward premise `STExpWardIConcl'` and the second conjunct `STExpIntQConcl'`); the merged pin
  `STExpIntI` is not changed;
* the regime-(i) arithmetic: `expIntI_ratio_le` (`(ilambda² + 1-v)/(ilambda² + 1-u) ≤ 2`) and
  `expIntI_log_ratio` (`∫_s^u (1-v)⁻¹ dv ≤ 2 log L`);
* `expIntI_kernel_unif`: `(sum_res_2_NAL)` (for `σ₁ = σ₂`) or `(sum_res_2)` (for a sum-zero
  deterministic family) with `n = 2` applied per end-time sequence `u` to a deterministic decaying
  family `𝒜_v`, lifted over `u` (the failing-sequence argument of `st6_precU_of_forall_seq`,
  deterministic on both sides);
* `expIntI_concl_of_kernel`, `expIntI_same`: the first conjunct of `STExpIntI'` (the plain Duhamel
  integral for `σ₁ = σ₂`);
* the consumer `ST_step6_caseI_of_pins''` (the proof of the merged `ST_step6_caseI_of_pins'`,
  `ExpIniI.lean:1127`, with the primed Ward and integrated pins) and `ST_step6I_of_LW_Int`, which
  discharges every other regime-(i) pin by its merged proof.
The second conjunct `STExpIntQConcl'` of `STExpIntI'` (the `𝒬` part) is S6-09b.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. The primed definitions (DECISIONS §73 (3)) -/

/-- `STExpIntQConcl` (`Step6Pins.lean:409-421`) with `0 < C → 0 < c →` after `∀ (C c : ℝ)` (the paper's mollifier has `c > 0`,
`Def:QtPt` `3_5:1214`; the consumer's family `st6_mollifier_family` has `0 < C`, `0 < c`). -/
def STExpIntQConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → STExpDuhEqQ sz E s t ϑ →
    ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) →
      Prec sz (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => F n p) →
      Prec sz (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
          (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
        (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))

/-- The merged `STExpIntI` (`Step6Pins.lean:449-452`) with the premise `STExpWardIConcl'` and the second conjunct
`STExpIntQConcl'`. -/
def STExpIntI' (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t =>
    STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl' sz E s t →
      STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t)

/-! ## 2. Regime-(i) arithmetic (targets 1, 2) -/

/-- **Target 1: the ratio of `(sum_res_2_NAL)`/`(sum_res_2)` in regime (i)** (`1 - s ≤ g²`, `s ≤ v ≤ u < 1`): `g² + (1-v) ≤ 2g² ≤
2 (g² + (1-u))`. -/
theorem expIntI_ratio_le {g s v u : ℝ} (hsv : s ≤ v) (hvu : v ≤ u) (hu : u < 1) (hs : 1 - s ≤ g ^ 2) :
    (g ^ 2 + |1 - v|) / (g ^ 2 + |1 - u|) ≤ 2 := by
  have hx : 0 < 1 - u := by linarith
  have hv : 0 < 1 - v := by linarith
  have hg : 0 ≤ g ^ 2 := sq_nonneg g
  rw [abs_of_pos hv, abs_of_pos hx, div_le_iff₀ (by linarith)]
  linarith

/-- **Target 2: the `u`-integral of regime (i)** (`6:97`): `∫_s^u (1-v)⁻¹ dv = log((1-s)/(1-u)) ≤ 2 log L` for `1-s ≤ g²`,
`1-u ≥ g²/L²`; the merged `expIntII_log_ratio` (`ExpIntII.lean:71`) at `d := 4`, `g := g L`. -/
theorem expIntI_log_ratio {L : ℕ} {g s u : ℝ} (hL : 1 ≤ L) (hsu : s ≤ u) (hu : u < 1) (h1 : 1 - s ≤ g ^ 2)
    (h2 : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) : ∫ v in s..u, (1 - v)⁻¹ ≤ 2 * Real.log (L : ℝ) := by
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  have e1 : (g * (L : ℝ)) ^ 2 / (L : ℝ) ^ 2 = g ^ 2 := by field_simp
  have e2 : (g * (L : ℝ)) ^ 2 / (L : ℝ) ^ 4 = g ^ 2 / (L : ℝ) ^ 2 := by field_simp
  have h := expIntII_log_ratio (d := 4) (L := L) (g := g * (L : ℝ)) (by norm_num) hL hsu hu (by rw [e1]; exact h1)
    (by rw [e2]; exact h2)
  refine h.trans (le_of_eq ?_)
  norm_num


/-! ## 3. The kernel, uniformly in the end time (target 3) -/

section Kernel

/-- The window `STEKWin sz s u` of the kernel pins on `u ∈ [s,t]` in regime (i): `u ≤ t ≤ 1 - ilambda²/L²` from
`STReg5I`, and `W⁻¹ ≤ (1-t)/(1-s) ≤ (1-u)/(1-s)` from `(con_st_ind)` (`st_window`, `d 𝔠_d < 1`); copy of the `private`
`expIniI_window` (`ExpIniI.lean:513`). -/
private theorem expIntI_window {d : ℕ} {𝔠d 𝔡 : ℝ} (sz : Sizes d) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (hWO : sz.WO 𝔡) (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop) {s t u : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hcon : STConStInd sz 𝔠d s t) (hR : STReg5I sz s t) : STEKWin sz s u := by
  refine ⟨hs0, hsu, fun n => by linarith [(hR n).1, hut n], fun n => lt_of_le_of_lt (hut n) (ht1 n), ?_⟩
  filter_upwards [st_window sz h𝔠d hdc hcon hWO hW hs0 ht1] with n hn
  refine hn.trans ?_
  have hxs : 0 < 1 - s n := by linarith [hst n, ht1 n]
  exact div_le_div_of_nonneg_right (by linarith [hut n]) hxs.le

/-- `Ugen` at the energy `E` is the merged `UN` with the signs `EKsgn (mE E) σ` (as in `st6_ini_nonzero`, `Step6Kit.lean:680`). -/
private theorem expIntI_Ugen_eq {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (σ : Fin 2 → Bool) (v w : ℝ)
    (A : (Fin 2 → Zd d (sz.L n)) → ℂ) :
    RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v w A = UN d (sz.L n) (sz.lam n) (EKsgn (mE E) σ) v w A := rfl

/-- **(g) with a second time `v ≤ u`**: if for every time sequence `u ∈ [s,t]` a property `Φ n (u n) v` holds eventually for all
`v ∈ [s_n, u_n]`, then eventually it holds for all `u ∈ [s_n,t_n]` and `v ∈ [s_n, u]` (a failing `(n, u_n, v_n)` for infinitely
many `n` is a time sequence: the argument of `st6_precU_of_forall_seq`, for a deterministic property; copy of the `private`
`expIntII_lift`, `ExpIntII.lean:357`). -/
private theorem expIntI_lift {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (Φ : ℕ → ℝ → ℝ → Prop)
    (h : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → Φ n (u n) v) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) → Φ n (u : ℝ) v := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  let u : ℕ → ℝ := fun n =>
    if hn : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2
    then ((Classical.choose hn).1 : ℝ) else s n
  have hu1 : ∀ n, s n ≤ u n := by
    intro n
    by_cases hn : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.1
    · simp only [u, hn, ↓reduceDIte]; exact le_rfl
  have hu2 : ∀ n, u n ≤ t n := by
    intro n
    by_cases hn : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.2
    · simp only [u, hn, ↓reduceDIte]; exact hst n
  have h' := h u hu1 hu2
  obtain ⟨n, hn1, hn2⟩ := (hcon.and_eventually h').exists
  push Not at hn1
  obtain ⟨w, v, hv1, hv2, hv3⟩ := hn1
  have hex : ∃ q : TimeIcc s t n × ℝ, s n ≤ q.2 ∧ q.2 ≤ (q.1 : ℝ) ∧ ¬ Φ n (q.1 : ℝ) q.2 :=
    ⟨(w, v), hv1, hv2, hv3⟩
  have hun : u n = ((Classical.choose hex).1 : ℝ) := by simp only [u, hex, ↓reduceDIte]
  obtain ⟨c1, c2, c3⟩ := Classical.choose_spec hex
  have := hn2 (Classical.choose hex).2 c1 (by rw [hun]; exact c2)
  rw [hun] at this
  exact c3 this

/-- **The kernel at one end-time sequence `u ∈ [s,t]`** (`(sum_res_2_NAL)` `3_5:1649` for `σ₁ = σ₂`, `(sum_res_2)` `3_5:1659` for a
sum-zero family; `n = 2`): the merged `stek_sumRes2NAL_holds` / `stek_sumRes2_holds` at the window `STEKWin sz s u`, applied to the
deterministic family `𝒜_v`, then `Prec` of a deterministic family is the pointwise bound (`st6_prec_det_iff`), and the ratio
`(ilambda² + 1-v)/(ilambda² + 1-u) ≤ 2` (`expIntI_ratio_le`, `1 - s ≤ ilambda²`), so the factor is `≤ 2` (NAL, exponent `n-1 = 1`)
or `≤ 4` (sum-zero, exponent `n = 2`). -/
private theorem expIntI_kernel_seq {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (h𝔠d : 0 < 𝔠d)
    (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t)
    (hcon : STConStInd sz 𝔠d s t) (σ : Fin 2 → Bool) (𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (X : ℕ → ℝ → ℝ) (hcase : σ 0 = σ 1 ∨ ∀ n v, EKSumZero (𝒜 n v))
    (hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v))
    (hX0 : ∀ n v, 0 ≤ X n v)
    (hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v)
    (hbd : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (τ : ℝ) (hτ : 0 < τ) (u : ℕ → ℝ) (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n →
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u n) (𝒜 n v)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (4 * X n v) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have hκ' : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  have hwin := expIntI_window sz h𝔠d hdc hflow.1.2.2.2.2 (scaleFacts3_W_tendsto sz hflow.1) hs0 hst hsu hut ht1 hcon hR
  have hdec' : STEKDecay sz s u (fun n v _ => 𝒜 n (v : ℝ)) := by
    intro ε' D hε' hD
    refine HighProbAt.of_eventually_univ ?_
    filter_upwards [hdec ε' D hε' hD] with n hn ω v
    exact hn v v.2.1 (v.2.2.trans (hut n))
  obtain ⟨b, hb⟩ := hlow
  have hlow' : STEKLow sz s u (fun n v _ => X n (v : ℝ)) := by
    refine ⟨b, HighProbAt.of_eventually_univ ?_⟩
    filter_upwards [hb] with n hn ω v
    exact hn v v.2.1 (v.2.2.trans (hut n))
  have hdom : sz.Prec (U := fun n => TimeIcc s u n) (fun n v _ => ‖𝒜 n (v : ℝ)‖) (fun n v _ => X n (v : ℝ)) := by
    refine (st6_prec_det_iff sz hsz (V := fun n => TimeIcc s u n) (fun n v => ‖𝒜 n (v : ℝ)‖)
      (fun n v => X n (v : ℝ))).2 ?_
    intro τ' hτ'
    filter_upwards [hbd τ' hτ'] with n hn v
    exact hn v v.2.1 (v.2.2.trans (hut n))
  have hratio : ∀ n, ∀ v : ℝ, s n ≤ v → v ≤ u n →
      (sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - u n|) ≤ 2 :=
    fun n v h1 h2 => expIntI_ratio_le h1 h2 (hu1 n) (hR n).2
  have hr0 : ∀ n, ∀ v : ℝ, s n ≤ v → v ≤ u n → 0 ≤ (sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - u n|) := by
    intro n v _ _
    positivity
  rcases hcase with hσ | hzero
  · -- `(sum_res_2_NAL)`: exponent `n - 1 = 1`
    have hσ' : ∃ k, σ k = σ (finRotate 2 k) := by
      refine ⟨0, ?_⟩
      have : finRotate 2 (0 : Fin 2) = 1 := by decide
      rw [this]; exact hσ
    have hk := stek_sumRes2NAL_holds d hd 2 le_rfl (Real.sqrt (2 * κ) / 2) 𝔠 𝔡 hκ' sz hflow.1 s u hwin
      (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le)
      (fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n)) σ hσ' (fun n v _ => 𝒜 n (v : ℝ)) hdec'
      (fun n v _ => X n (v : ℝ)) hlow' hdom
    have hk' := ((st6_prec_det_iff sz hsz (V := fun n => TimeIcc s u n)
      (fun n v => ‖UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ) (v : ℝ) (u n) (𝒜 n (v : ℝ))‖)
      (fun n v => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - u n|)) ^ (2 - 1) * X n (v : ℝ))).1 hk) τ hτ
    filter_upwards [hk'] with n hn v hv1 hv2
    rw [expIntI_Ugen_eq sz n (STflowE z n) σ v (u n)]
    refine (hn ⟨v, hv1, hv2⟩).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h2 := hratio n v hv1 hv2
    have hx := hX0 n v
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    nlinarith
  · -- `(sum_res_2)`: exponent `n = 2`
    have hk := stek_sumRes2_holds d hd 2 le_rfl (Real.sqrt (2 * κ) / 2) 𝔠 𝔡 hκ' sz hflow.1 s u hwin
      (fun n => mE (STflowE z n)) (fun n => norm_mE (st6_flowE_lt_two sz hκ hflow n).le)
      (fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n)) σ (fun n v _ => 𝒜 n (v : ℝ)) hdec'
      (fun n v _ => hzero n (v : ℝ)) (fun n v _ => X n (v : ℝ)) hlow' hdom
    have hk' := ((st6_prec_det_iff sz hsz (V := fun n => TimeIcc s u n)
      (fun n v => ‖UN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ) (v : ℝ) (u n) (𝒜 n (v : ℝ))‖)
      (fun n v => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - u n|)) ^ 2 * X n (v : ℝ))).1 hk) τ hτ
    filter_upwards [hk'] with n hn v hv1 hv2
    rw [expIntI_Ugen_eq sz n (STflowE z n) σ v (u n)]
    refine (hn ⟨v, hv1, hv2⟩).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h2 := hratio n v hv1 hv2
    have h0 := hr0 n v hv1 hv2
    have hx := hX0 n v
    have hsq : ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - u n|)) ^ 2 ≤ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq hx

end Kernel

/-- **Target 3: the kernel, uniformly in the end time** (`(sum_res_2_NAL)` `3_5:1649` for `σ₁ = σ₂`, `(sum_res_2)` `3_5:1659` for a
sum-zero family, `n = 2`, regime (i)): for a deterministic family `𝒜_v` with the decay `(deccA0)` on `[s,t]`, a control `X ≥ N^{-b}`
and `‖𝒜_v‖ ≺ X`, eventually for all `u ∈ [s_n,t_n]` and `v ∈ [s_n,u]`, `‖𝒰_{v,u} 𝒜_v‖ ≤ N^τ · 4 X_v` (ratio `≤ 2`, exponent
`n-1 = 1` or `n = 2`).  For every time sequence `u` the merged kernel pin is applied at the window `STEKWin sz s u`; the lift over `u`
is the failing-sequence argument (deterministic on both sides, DECISIONS §64 (4)). -/
theorem expIntI_kernel_unif {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (_hε : 0 < ε) (_h𝔡 : 0 < 𝔡)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t)
    (hcon : STConStInd sz 𝔠d s t) (σ : Fin 2 → Bool) (𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (X : ℕ → ℝ → ℝ) (hcase : σ 0 = σ 1 ∨ ∀ n v, EKSumZero (𝒜 n v))
    (hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v))
    (hX0 : ∀ n v, 0 ≤ X n v)
    (hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v)
    (hbd : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
      ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u : ℝ) (𝒜 n v)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (4 * X n v) :=
  expIntI_lift (fun n => (hst n).le)
    (fun n u v => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v u (𝒜 n v)‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (4 * X n v))
    (fun u hsu hut => expIntI_kernel_seq hd hκ h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon σ 𝒜 X hcase hdec hX0 hlow hbd
      τ hτ u hsu hut)


/-! ## 4. The drift integral and the assembly (target 4) -/

section Assembly

/-- **The drift integral at one size**, regime (i) (`6:97`, `6:104`): a kernel bound `‖𝒰_{v,u} D_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} +
B_v^{5/2})` on `[s,u]` gives `‖∫_s^u 𝒰_{v,u} D_v dv‖ ≤ M · 3 T_u · 2 log L` (`B_v ≤ B_u`, `∫_s^u (1-v)⁻¹ ≤ 2 log L`, `expIntI_log_ratio`;
the rates need only `ilambda²/L^d ≤ 1-u`, which holds since `L^d ≥ L²`; no integrability of the integrand is needed,
`intervalIntegral.norm_integral_le_of_norm_le`).  Regime-(i) analogue of `expIntII_drift_integral_le` (`ExpIntII.lean:202`). -/
private theorem expIntI_drift_integral_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E s u M : ℝ} (hd : 2 ≤ d) (hM : 0 ≤ M)
    (hsu : s ≤ u) (hu : u < 1) (hwin : 1 - s ≤ sz.lam n ^ 2)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u) (σ : Fin 2 → Bool)
    (hker : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b)‖ ≤
        M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ v in s..u, zeroModeSet d (sz.L n) ∅
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b)) a‖ ≤
      M * (3 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by
  simp only [st5_zeroModeSet_empty]
  have hx : 0 < 1 - u := by linarith
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hLr : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL1
  -- `ilambda ≠ 0`: `0 < 1 - u ≤ 1 - s ≤ ilambda²`
  have hl : sz.lam n ≠ 0 := by
    intro h0
    rw [h0] at hwin
    norm_num at hwin
    linarith
  have hlo' : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u := by
    refine le_trans ?_ hlo
    have h2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hLr hd
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h2
  have hT0 : 0 ≤ STExpTarget sz n u := st6_target_nonneg sz n hu
  have hrate := expIntII_rates_le_target sz n hu hl hlo'
  have hlogL : 0 ≤ 2 * Real.log ((sz.L n : ℕ) : ℝ) := mul_nonneg (by norm_num) (Real.log_nonneg hLr)
  -- the bound `g v = M (3 T_u) (1-v)⁻¹`
  have hbound : ∀ v : ℝ, s ≤ v → v ≤ u →
      M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) ≤
        (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹ := by
    intro v hv1 hv2
    have hvu : v < 1 := lt_of_le_of_lt hv2 hu
    have hmono := STBctl_mono sz n hv2 hu
    have hBv := (STBctl_pos sz n hvu).le
    have h1 : sz.Bctl n v ^ (11 / 5 : ℝ) ≤ sz.Bctl n u ^ (11 / 5 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have h2 : sz.Bctl n v ^ (5 / 2 : ℝ) ≤ sz.Bctl n u ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have hinv : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
    calc M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
        ≤ M * ((1 - v)⁻¹ * (3 * STExpTarget sz n u)) := by
          gcongr
          linarith
      _ = (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹ := by ring
  have hint : IntervalIntegrable (fun v : ℝ => (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹) volume s u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro v hv
    rw [Set.uIcc_of_le hsu] at hv
    have : v ≤ u := hv.2
    change 1 - v ≠ 0
    linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun v => RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b) a)
    (g := fun v : ℝ => (M * (3 * STExpTarget sz n u)) * (1 - v)⁻¹) hsu
    (Filter.Eventually.of_forall fun v hv =>
      ((norm_le_pi_norm _ a).trans (hker v hv.1.le hv.2)).trans (hbound v hv.1.le hv.2)) hint
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hlog := expIntI_log_ratio (L := sz.L n) (g := sz.lam n) hL1 hsu hu hwin hlo
  calc M * (3 * STExpTarget sz n u) * ∫ v in s..u, (1 - v)⁻¹
      ≤ M * (3 * STExpTarget sz n u) * (2 * Real.log ((sz.L n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = M * (3 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by ring

/-- **Target 4: `(iisuwjyys_exp)` closed in regime (i)** (`6:97`, `6:104`), `σ₁ = σ₂` (any class `P`, `A = ∅`): the Duhamel identity
(`STExpDuhEq` at `A = ∅`), the uniform kernel bound `‖𝒰_{v,u} D_v‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2})`, the one-size integral
bound (`M = N^{τ/2}`, `expIntI_drift_integral_le`) and `log L ≺ 1` (`expIntII_log_eventually`, constant `6 = 3 · 2`) give
`‖f_u‖ ≤ N^τ F + N^τ T_u` for the control `F` of the initial term.  Regime-(i) analogue of `STExpIntConcl_of_kernel`
(`ExpIntII.lean:472`, `∫ ≤ 2 log L` for `(d-2) log L`). -/
theorem expIntI_concl_of_kernel {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) (hd : 3 ≤ d) {E s t : ℕ → ℝ}
    (_hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t) (hduh : STExpDuhEq sz E s t)
    (P : (Fin 2 → Bool) → Prop)
    (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) :
    STExpIntConcl sz ∅ P E s t := by
  intro F hF hini
  have hini' := ((st6_prec_det_iff sz hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) ∅
      (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b)) p.2.2‖)
    (fun n p => F n p)).1 hini)
  refine (st6_prec_det_iff sz hsz (V := STIdx2P sz P s t)
    (fun n p => ‖zeroModeSet d (sz.L n) ∅ (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
    (fun n p => F n p + STExpTarget sz n (p.1 : ℝ))).2 ?_
  intro τ hτ
  have h3 := expIntII_log_eventually sz hsz (by omega) 6 (half_pos hτ)
  filter_upwards [hini' τ hτ, hker (τ / 2) (half_pos hτ), h3] with n hn1 hn2 hn3
  rintro ⟨u, ⟨σ, hP⟩, a⟩
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hwin := (hR n).2
  have hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - (u : ℝ) := by
    have := (hR n).1
    have h2 : (u : ℝ) ≤ t n := u.2.2
    linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hP0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  have hint := expIntI_drift_integral_le sz n (E := E n) (s := s n) (u := (u : ℝ))
    (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (by omega) hP0 u.2.1 hu1 hwin hlo σ
    (fun v hv1 hv2 => hn2 u v hv1 hv2 σ hP) a
  have hT0 : 0 ≤ STExpTarget sz n (u : ℝ) := st6_target_nonneg sz n hu1
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  change ‖zeroModeSet d (sz.L n) ∅ (fun b => STExpErr sz n (E n) (u : ℝ) σ b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (F n (u, ⟨σ, hP⟩, a) + STExpTarget sz n (u : ℝ))
  rw [hduh n u σ ∅ a]
  refine (norm_add_le _ _).trans ?_
  have hn1' := hn1 (u, ⟨σ, hP⟩, a)
  have hlog : 6 * Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := hn3
  calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          (3 * STExpTarget sz n (u : ℝ) * (2 * Real.log ((sz.L n : ℕ) : ℝ))) :=
        add_le_add hn1' hint
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) *
          (6 * Real.log ((sz.L n : ℕ) : ℝ))) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * F n (u, ⟨σ, hP⟩, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) := by
        gcongr
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (F n (u, ⟨σ, hP⟩, a) + STExpTarget sz n (u : ℝ)) := by
        rw [hrpow]; ring

end Assembly


/-! ## 5. The `σ₁ = σ₂` conjunct from the flow (target 5) -/

section Same

/-- `W^{-d} B_{u,0} ≥ 0` for every `u` (all terms of `B` are nonnegative; `Bparam` uses `|1-u|`). -/
private theorem expIntI_Bctl_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (v : ℝ) : 0 ≤ sz.Bctl n v := by
  unfold Sizes.Bctl Bparam
  positivity

/-- **(eq:Exp(L-K)1) + (eq:ExpLWn=2) for the drift tensor** (premise `STExpDriftHiConcl`): `‖D_v^σ‖_∞ ≤ N^τ (1-v)⁻¹ (B_v^{11/5} +
B_v^{5/2})` for all large `n`, all `v ∈ [s_n, t_n]` and `σ` (`st6_prec_det_iff` for the two summands, the triangle inequality); copy of
the `private` `expIntII_drift_pi` (`ExpIntII.lean:323`). -/
private theorem expIntI_drift_pi {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STExpDriftHiConcl sz E s t) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (v : TimeIcc s t n) (σ : Fin 2 → Bool),
      ‖fun b => STExpDrift sz n (E n) (v : ℝ) σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by
  have h1 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))).1 h.1 τ hτ
  have h2 := (st6_prec_det_iff sz hsz (V := STIdx2 sz s t)
    (fun n p => ‖STExpEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))).1 h.2 τ hτ
  filter_upwards [h1, h2] with n hn1 hn2
  intro v σ
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (ht1 n)
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB0 := (STBctl_pos sz n hv1).le
  have hinv : 0 ≤ (1 - (v : ℝ))⁻¹ := inv_nonneg.2 (by linarith)
  have hX : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) :=
    mul_nonneg hN0 (mul_nonneg hinv (add_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hB0 _)))
  rw [pi_norm_le_iff_of_nonneg hX]
  intro a
  calc ‖STExpDrift sz n (E n) (v : ℝ) σ a‖
      = ‖STExpELKLK sz n (E n) (v : ℝ) σ a + STExpEGt sz n (E n) (v : ℝ) σ a‖ := rfl
    _ ≤ ‖STExpELKLK sz n (E n) (v : ℝ) σ a‖ + ‖STExpEGt sz n (E n) (v : ℝ) σ a‖ := norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ)) +
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (v : ℝ))⁻¹ * sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ)) :=
        add_le_add (hn1 (v, σ, a)) (hn2 (v, σ, a))
    _ = ((sz.size n : ℕ) : ℝ) ^ τ *
        ((1 - (v : ℝ))⁻¹ * (sz.Bctl n (v : ℝ) ^ (11 / 5 : ℝ) + sz.Bctl n (v : ℝ) ^ (5 / 2 : ℝ))) := by ring

/-- **Target 5: the first conjunct of `STExpIntI'` from the flow** (`6:97`: `(sum_res_2_NAL)`, `n = 2`, `σ₁ = σ₂`): the control
`X_v = |1-v|⁻¹ (B_v^{11/5} + B_v^{5/2})` of the drift (`STExpDriftHiConcl`, the decay `STExpDriftDecayConcl` of the deterministic tensors
`D_v^σ` through `HighProbAt.nonempty`) in the kernel `expIntI_kernel_unif` (loss `4`, absorbed by `4 ≤ N^{τ/2}`) and the assembly
`expIntI_concl_of_kernel`.  Lower control `X ≥ N^{-3}` from `W^{-d}B_{v,0} ≥ N⁻¹` (`expAvg_Bctl_ge`).  The premises `STLK`,
`STDecay`, `STExp2`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW … 0` of `STIngR6` are not used. -/
theorem expIntI_same {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t)
    (hcon : STConStInd sz 𝔠d s t) (hduh : STExpDuhEq sz (STflowE z) s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t)
    (hdd : STExpDriftDecayConcl sz (STflowE z) s t) : STExpIntConcl sz ∅ STSigSame (STflowE z) s t := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 := st5_t_lt_one sz hflow htT
  refine expIntI_concl_of_kernel sz hsz hd hst ht1 hR hduh STSigSame ?_
  intro τ hτ
  have h4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop _
  have hdrift := expIntI_drift_pi sz hsz ht1 hdr (half_pos hτ)
  have key : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, STSigSame σ → ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u : ℝ)
          (fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
    intro σ
    by_cases hσ : STSigSame σ
    · -- the deterministic family `D_v^σ`, the control `X_v`
      have hdecay : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
          EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (fun b => STExpDrift sz n (STflowE z n) v σ b) := by
        intro ε' D hε' hD
        filter_upwards [HighProbAt.nonempty (tendsto_size sz hsz) measure_univ (hdd σ ε' D hε' hD)]
          with n hn v hv1 hv2
        obtain ⟨ω, hω⟩ := hn
        exact hω ⟨v, hv1, hv2⟩
      have hX0 : ∀ n v, 0 ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) := by
        intro n v
        have hB0 := expIntI_Bctl_nonneg sz n v
        positivity
      have hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
          ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) := by
        refine ⟨3, Filter.Eventually.of_forall fun n v hv1 hv2 => ?_⟩
        have hv0 : 0 ≤ v := (hs0 n).trans hv1
        have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
        have hB := expAvg_Bctl_ge sz n hv0 hvl
        have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
        have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
        have hxpos : 0 < |1 - v| := abs_pos.2 (by linarith)
        have hx1 : 1 ≤ |1 - v|⁻¹ := by
          rw [abs_of_pos (by linarith : 0 < 1 - v)]
          exact (one_le_inv₀ (by linarith)).2 (by linarith)
        have hB0 := expIntI_Bctl_nonneg sz n v
        have h1 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ (11 / 5 : ℝ) ≤ sz.Bctl n v ^ (11 / 5 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hN0.le) hB (by norm_num)
        have h2 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ (11 / 5 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (-(11 / 5 : ℝ)) := by
          rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]
        have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(11 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        have h5 : 0 ≤ sz.Bctl n v ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0 _
        have h6 : 0 ≤ sz.Bctl n v ^ (11 / 5 : ℝ) := Real.rpow_nonneg hB0 _
        calc ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(11 / 5 : ℝ)) := h3
          _ ≤ sz.Bctl n v ^ (11 / 5 : ℝ) := h2 ▸ h1
          _ ≤ sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) := by linarith
          _ ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) :=
              le_mul_of_one_le_left (by linarith) hx1
      have hbd : ∀ τ' : ℝ, 0 < τ' → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
          ‖fun b => STExpDrift sz n (STflowE z n) v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' *
            (|1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
        intro τ' hτ'
        filter_upwards [expIntI_drift_pi sz hsz ht1 hdr hτ'] with n hn v hv1 hv2
        have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
        rw [abs_of_pos (by linarith : 0 < 1 - v)]
        exact hn ⟨v, hv1, hv2⟩ σ
      have hk := expIntI_kernel_unif hd hκ hε h𝔡 h𝔠d hdc sz z hflow s t hs0 hst htT hR hcon σ
        (fun n v b => STExpDrift sz n (STflowE z n) v σ b)
        (fun n v => |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
        (Or.inl hσ) hdecay hX0 hlow hbd (τ / 2) (half_pos hτ)
      filter_upwards [hk, h4] with n hn h4n _ u v hv1 hv2
      have hvl : v < 1 := lt_of_le_of_lt (hv2.trans u.2.2) (ht1 n)
      have hn' := hn u v hv1 hv2
      have hx0 : 0 ≤ (1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) := by
        have hB0 := expIntI_Bctl_nonneg sz n v
        have : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
        positivity
      have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hrpow : ((sz.size n : ℕ) : ℝ) ^ τ =
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_add (by exact_mod_cast sz.one_le_size n)]
        congr 1
        ring
      rw [abs_of_pos (by linarith : 0 < 1 - v)] at hn'
      refine hn'.trans ?_
      rw [hrpow]
      calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (4 * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) +
            sz.Bctl n v ^ (5 / 2 : ℝ))))
          ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hN0
            exact mul_le_mul_of_nonneg_right h4n hx0
        _ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by ring
    · exact Filter.Eventually.of_forall fun n h => absurd h hσ
  filter_upwards [Filter.eventually_all.2 key] with n hn u v hv1 hv2 σ hP
  exact hn σ hP u v hv1 hv2

end Same


/-! ## 6. The consumer (target 6; DECISIONS §73 (3), supervisor 2347 "Consumer") -/

/-- **Step 6, regime (i), from its pins, with the primed Ward and integrated pins** (target 6a): the proof of the merged
`ST_step6_caseI_of_pins'` (`ExpIniI.lean:1127-1208`, copied) with `hWd : STExpWardI' d` (was `STExpWardI d`) and `hInt : STExpIntI' d`
(was `STExpIntI d`).  Exactly two lines of the proof differ: `hint.2 C c' hC hc' ϑ hϑ hduhQ …` (the primed second conjunct takes the
positivity of the constants of the family `st6_mollifier_family`) and `(hward C c' hC hc' ϑ hϑ).1` (the primed Ward conclusion likewise);
`hward := H₃ … hAvgU` and `hint := H₅ … hduh ⟨hlk, hegt⟩ hdec hward` are unchanged and typecheck against the primed premise.
`σ₁ = σ₂`: the plain Duhamel (`STExpIntI'.1`) with the initial term `STExpIniI'.1`; `σ₁ ≠ σ₂`: the `𝒬`-Duhamel (`STExpIntI'.2`) with the
initial term `STExpIniI'.2` and `f_u = 𝒬_u f_u + (𝒫 f_u) ϑ_u`, `(𝒫 f_u) ϑ_u ≺ B³` from `STExpWardI'`. -/
theorem ST_step6_caseI_of_pins'' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI' d)
    (hIni : STExpIniI' d) (hInt : STExpIntI' d) : STStep6I d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hDec hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := hIni hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ (min c₃ (min c₄ c₅))) :=
    lt_min hc₁ (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ hc₅)))
  refine ⟨min c₁ (min c₂ (min c₃ (min c₄ c₅))), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5
  have ht1 := st5_t_lt_one sz hflow htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have m : ∀ c', min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c' → STConStInd sz c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hm1 := m c₁ (min_le_left _ _)
  have hm2 := m c₂ ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 := m c₃ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 := m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hm5 := m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hHi := st6_hi_of_reg5I sz (by omega) hR
  have hAvgU := st6_expAvgU_of_pin sz hAvg hd hκ hε h𝔡 hflow hs0 hst htT hS2 hLKU
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec0 hExp hm1 hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LW sz hLW hd hκ hε h𝔡 hflow hs0 hst htT hHi hS2 hLmax hLKU hS5
  have hdec := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm2 hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm3 hS2 hLmax hLKU hS5 hAvgU
  have hini := H₄ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm4 hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_pin sz hDu hd hκ hflow hs0 htT
  have hint := H₅ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm5 hS2 hLmax hLKU hS5
    hduh ⟨hlk, hegt⟩ hdec hward
  have hT0 : ∀ n (u : ℝ), u ≤ t n → 0 ≤ STExpTarget sz n u := fun n u hu =>
    st6_target_nonneg sz n (lt_of_le_of_lt hu (ht1 n))
  -- `σ₁ = σ₂`
  have hS : sz.Prec (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hiniS : sz.Prec (U := STIdx2P sz STSigSame s t)
        (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n)
          (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
      simp only [st5_zeroModeSet_empty]
      exact hini.1
    have hmainS := hint.1 (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2) hiniS
    simp only [st5_zeroModeSet_empty] at hmainS
    refine st5_prec_mono sz hsz (c := 2) hmainS (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    linarith
  -- `σ₁ ≠ σ₂`
  obtain ⟨C, c', hC, hc', ϑ, hϑ⟩ := st6_mollifier_family sz hd h𝔡 hflow.1.2.2.2.2
  have hduhQ := st6_duhEqQ_of_pin sz hDuQ hd hκ hflow hs0 htT C c' ϑ hϑ
  have hmainQ := hint.2 C c' hC hc' ϑ hϑ hduhQ (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2)
    (hini.2 C c' hC hc' ϑ hϑ)
  have hw := (hward C c' hC hc' ϑ hϑ).1
  have hM : sz.Prec (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hsum := StochDomAt.add (tendsto_size sz hsz) hmainQ hw
    have hsum' : sz.Prec (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖)
        (fun n p _ => (STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ)) + (sz.Bctl n (p.1 : ℝ)) ^ 3) := by
      refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
      change ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖ ≤
        ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
          ϑ n (p.1 : ℝ) p.2.2‖
      calc ‖STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 p.2.2‖
          = ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2 +
            STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
              ϑ n (p.1 : ℝ) p.2.2‖ := by
            unfold STQop; ring_nf
        _ ≤ _ := norm_add_le _ _
    refine st5_prec_mono sz hsz (c := 3) hsum' (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have h2 := st6_cube_le_target sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ 3 ≤
      3 * STExpTarget sz n (p.1 : ℝ)
    linarith
  exact st6_cover_exp2U sz (ξ := fun n u σ a => ‖STExpErr sz n (STflowE z n) (u : ℝ) σ a‖)
    (ζ := fun n u _ _ => STExpTarget sz n (u : ℝ)) hsz (P₁ := STSigSame) (P₂ := STSigMixed)
    (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h]) hS hM

/-- **Target 6b: regime (i) of Step 6 with only `LWtermEXP` and `STExpIntI'` open**: every other ingredient of
`ST_step6_caseI_of_pins''` is discharged by its merged proof (`stExpLKLKHi_holds`, `stImproveExpAver_holds`, `stExpDuhamelZ_holds`,
`stExpDuhamelQ_holds`, `stExpDriftDecay_holds`, `stExpWardI'_holds`, `stExpIniI'_holds`).  `LWtermEXP` is LW-14; `STExpIntI'` is
proved in part b (S6-09b), the first conjunct is `expIntI_same`. -/
theorem ST_step6I_of_LW_Int (d : ℕ) (hLW : LWtermEXP d) (hInt : STExpIntI' d) : STStep6I d :=
  ST_step6_caseI_of_pins'' (stExpLKLKHi_holds d) hLW (stImproveExpAver_holds d) (stExpDuhamelZ_holds d)
    (stExpDuhamelQ_holds d) (stExpDriftDecay_holds d) (stExpWardI'_holds d) (stExpIniI'_holds d) hInt

end RBM.Gauss.Sizes

/-! ## 7. Compiled nonempty instances (`d = 3`, `szB`, `zB`, regime (i) times `(7/8, 15/16)`)

Data (merged, `Step34Inst`, `Step5Inst`): `L = 4`, `W_n = n + 4`, `ilambda = 1`, `z = 1/2 + i/64`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`𝔠_d = 1/300` (`d 𝔠_d = 1/100 < 1`); `1/16 = ilambda²/L² ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`.  Every deterministic hypothesis (flow, times,
regime, `(con_st_ind)` by `conStInd_const`, the Duhamel identity by `st6_duhEq_of_pin`) is discharged; what stays a hypothesis is
another gate's pin (`LWtermEXP 3`, `STExpIntI' 3`, the drift conclusions `STExpDriftHiConcl`, `STExpDriftDecayConcl`). -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- The regime-(i) skeleton with every proved ingredient pin and the primed integrated pin: only `LWtermEXP 3` (LW-14) and
`STExpIntI' 3` (S6-09b) stay open. -/
theorem inst_skeleton6I'' (hLW : LWtermEXP 3) (hInt : STExpIntI' 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I (ST_step6I_of_LW_Int 3 hLW hInt)

/-- `expIntI_same` at `szB`, `zB` (`κ = 1/10`), `(7/8, 15/16)`, `𝔠_d = 1/300`: the Duhamel identity is discharged with the merged
`st6_duhEq_of_pin (stExpDuhamelZ_holds 3)`, `(con_st_ind)` by `conStInd_const`; the drift conclusions (`(eq:Exp(L-K)1)`,
`(eq:ExpLWn=2)`, `(deccA0)` of the drift: S6-06, LW-14, S6-07) stay hypotheses. -/
theorem inst_expIntI_same
    (hdr : STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hdd : STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  expIntI_same (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) (𝔠d := 1 / 300) (by norm_num) (by norm_num) szB zB flow_zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
    szB_reg5I (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num))
    (st6_duhEq_of_pin szB (stExpDuhamelZ_holds 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (szB_flow_ht (by norm_num)))
    hdr hdd

/-- `expIntI_log_ratio` at `d = 3`, `L = 4`, `g = 1`, `(s, u) = (7/8, 15/16)`: `1 - s = 1/8 ≤ g² = 1`, `g²/L² = 1/16 = 1 - u` is the
boundary of the window, `log 2 = 0.693 ≤ 2 log 4 = 2.773`. -/
theorem inst_expIntI_log_ratio :
    ∫ v in (7 / 8 : ℝ)..(15 / 16), (1 - v)⁻¹ ≤ 2 * Real.log (((szB.L 0 : ℕ) : ℝ)) :=
  expIntI_log_ratio (L := szB.L 0) (g := szB.lam 0) (by simp [szB]) (by norm_num) (by norm_num)
    (by simp [szB]; norm_num) (by simp [szB]; norm_num)

/-- `expIntI_ratio_le` at `g = ilambda = 1`, `(s, v, u) = (7/8, 7/8, 15/16)`: `(1 + 1/8)/(1 + 1/16) = 18/17 ≤ 2`. -/
theorem inst_expIntI_ratio_le :
    ((szB.lam 0) ^ 2 + |1 - (7 / 8 : ℝ)|) / ((szB.lam 0) ^ 2 + |1 - (15 / 16 : ℝ)|) ≤ 2 :=
  expIntI_ratio_le (g := szB.lam 0) (s := 7 / 8) (v := 7 / 8) (u := 15 / 16) le_rfl (by norm_num) (by norm_num)
    (by simp [szB]; norm_num)

/-- The deterministic tensor `A_a = 1_{a₁ = a₂}` of `inst_expIniI_fastDecay_mono` has the decay `(deccA0)` at every time and size of
`szB` (a far pair has `a₁ ≠ a₂`). -/
private theorem inst_expIntI_diag_decay (n : ℕ) (v ε' D : ℝ) :
    EKFastDecay (szB.lam n) v ((szB.W n : ℕ) : ℝ) ε' D (fun a : Fin 2 → Zd 3 (szB.L n) => if a 0 = a 1 then (1 : ℂ) else 0) := by
  have hW0 : (0 : ℝ) < ((szB.W n : ℕ) : ℝ) := by exact_mod_cast szB.W_pos n
  have hL1 : (1 : ℝ) ≤ ((szB.L n : ℕ) : ℝ) := by
    have := szB.three_le_L n
    exact_mod_cast (by omega : 1 ≤ szB.L n)
  have hpos : 0 < ((szB.W n : ℕ) : ℝ) ^ ε' * ellT (szB.L n) (szB.lam n) v :=
    mul_pos (Real.rpow_pos_of_pos hW0 _) (ellT_pos hL1)
  intro a ⟨i, j, hij⟩
  have hne : a 0 ≠ a 1 := by
    intro h
    have hz : a i - a j = 0 := by fin_cases i <;> fin_cases j <;> simp [h]
    rw [hz] at hij
    simp at hij
    linarith
  have hnn : 0 ≤ ((szB.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  simpa [hne] using hnn

/-- `expIntI_kernel_unif` at `szB`, `zB`, `(7/8, 15/16)`, `𝔠_d = 1/300`, `σ = (+,+)` (`σ₁ = σ₂`, `(sum_res_2_NAL)`), the nonzero
deterministic family `𝒜_v = 1_{a₁ = a₂}` (nonzero, `inst_expIntI_tensors_ne_zero`; decay `(deccA0)` proved, `‖𝒜_v‖ ≤ 1`) and the control `X ≡ 1`
(`N^0 ≤ X`, `‖𝒜_v‖ ≤ N^τ X`): every hypothesis is discharged. -/
theorem inst_expIntI_kernel_unif (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ), 7 / 8 ≤ v → v ≤ (u : ℝ) →
      ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) (fun _ => true) v (u : ℝ)
          (fun a : Fin 2 → Zd 3 (szB.L n) => if a 0 = a 1 then (1 : ℂ) else 0)‖ ≤
        ((szB.size n : ℕ) : ℝ) ^ τ * (4 * (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) n v) := by
  refine expIntI_kernel_unif (d := 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) (𝔠d := 1 / 300) (by norm_num) (by norm_num) szB zB flow_zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
    szB_reg5I (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) (fun _ => true)
    (fun n _ => fun a : Fin 2 → Zd 3 (szB.L n) => if a 0 = a 1 then (1 : ℂ) else 0) (fun _ _ => 1) (Or.inl rfl) ?_
    (fun _ _ => zero_le_one) ⟨0, Filter.Eventually.of_forall fun n v _ _ => by simp⟩ ?_ τ hτ
  · intro ε' D _ _
    exact Filter.Eventually.of_forall fun n v _ _ => inst_expIntI_diag_decay n v ε' D
  · intro τ' hτ'
    refine Filter.Eventually.of_forall fun n v _ _ => ?_
    have hN1 : (1 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) := by exact_mod_cast szB.one_le_size n
    have h1 : (1 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
    have hnorm : ‖fun a : Fin 2 → Zd 3 (szB.L n) => if a 0 = a 1 then (1 : ℂ) else 0‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
      by_cases h : a 0 = a 1 <;> simp [h]
    linarith

/-- The dipole tensor `A_a = 1_{a₂ = a₁} - 1_{a₂ = a₁ + e}` is sum-zero (`(sumAzero)`): for fixed `a₁ = x` the two indicators sum to `1`. -/
private theorem inst_expIntI_sumZero (L : ℕ) [NeZero L] (e : Zd 3 L) :
    EKSumZero (fun b : Fin 2 → Zd 3 L =>
      (if b 1 = b 0 then (1 : ℂ) else 0) - (if b 1 = b 0 + e then (1 : ℂ) else 0)) := by
  intro i₀ hi x
  have hi0 : i₀ = 0 := Fin.ext hi
  subst hi0
  have key : ∀ y : Zd 3 L, ∑ b ∈ Finset.univ.filter (fun b : Fin 2 → Zd 3 L => b 0 = x),
      (if b 1 = y then (1 : ℂ) else 0) = 1 := by
    intro y
    rw [Finset.sum_eq_single ![x, y]]
    · simp
    · intro b hb hne
      have h0 : b 0 = x := (Finset.mem_filter.1 hb).2
      have h1 : ¬ b 1 = y := fun h1 => hne (by funext i; fin_cases i <;> simp [h0, h1])
      simp [h1]
    · intro h
      exfalso
      apply h
      simp
  have e1 : ∑ b ∈ Finset.univ.filter (fun b : Fin 2 → Zd 3 L => b 0 = x),
        ((if b 1 = b 0 then (1 : ℂ) else 0) - (if b 1 = b 0 + e then (1 : ℂ) else 0)) =
      ∑ b ∈ Finset.univ.filter (fun b : Fin 2 → Zd 3 L => b 0 = x),
        ((if b 1 = x then (1 : ℂ) else 0) - (if b 1 = x + e then (1 : ℂ) else 0)) :=
    Finset.sum_congr rfl fun b hb => by rw [(Finset.mem_filter.1 hb).2]
  rw [e1, Finset.sum_sub_distrib, key, key]
  ring


/-- The dipole tensor (`e = e₁` a unit vector) has the decay `(deccA0)` at every time and size of `szB` once `W^{ε'} ℓ > 1`
(`W ≥ 4`, `ℓ ≥ 1`): a far pair has `a₂ - a₁ ∉ {0, e}`. -/
private theorem inst_expIntI_dipole_decay (n : ℕ) (v ε' D : ℝ) (hε' : 0 < ε') :
    EKFastDecay (szB.lam n) v ((szB.W n : ℕ) : ℝ) ε' D
      (fun a : Fin 2 → Zd 3 (szB.L n) =>
        (if a 1 = a 0 then (1 : ℂ) else 0) - (if a 1 = a 0 + Pi.single 0 1 then (1 : ℂ) else 0)) := by
  have hW1 : (1 : ℝ) < ((szB.W n : ℕ) : ℝ) := by
    have : 4 ≤ szB.W n := by simp [szB]
    exact_mod_cast (by omega : 1 < szB.W n)
  have hL1 : (1 : ℝ) ≤ ((szB.L n : ℕ) : ℝ) := by
    have := szB.three_le_L n
    exact_mod_cast (by omega : 1 ≤ szB.L n)
  have hgt : 1 < ((szB.W n : ℕ) : ℝ) ^ ε' * ellT (szB.L n) (szB.lam n) v :=
    lt_of_lt_of_le (Real.one_lt_rpow hW1 hε')
      (le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) (one_le_ellT hL1))
  have he : zdistD 3 (szB.L n) (Pi.single 0 1 : Zd 3 (szB.L n)) = 1 := by
    change zdistD 3 4 (Pi.single 0 1 : Zd 3 4) = 1
    decide
  intro a ⟨i, j, hij⟩
  have hclose : (a 1 = a 0 ∨ a 1 = a 0 + Pi.single 0 1) → zdistD 3 (szB.L n) (a i - a j) ≤ 1 := by
    rintro (h1 | h2)
    · have : a i - a j = 0 := by fin_cases i <;> fin_cases j <;> simp [h1]
      rw [this]; simp
    · fin_cases i <;> fin_cases j
      · simp
      · have : a 0 - a 1 = -(Pi.single 0 1 : Zd 3 (szB.L n)) := by rw [h2]; ring
        simp only [Fin.zero_eta, Fin.mk_one]
        rw [this, zdistD_neg, he]
      · have : a 1 - a 0 = (Pi.single 0 1 : Zd 3 (szB.L n)) := by rw [h2]; ring
        simp only [Fin.zero_eta, Fin.mk_one]
        rw [this, he]
      · simp
  have hA : (if a 1 = a 0 then (1 : ℂ) else 0) - (if a 1 = a 0 + Pi.single 0 1 then (1 : ℂ) else 0) = 0 := by
    by_cases h1 : a 1 = a 0
    · exfalso
      have h3 := hclose (Or.inl h1)
      have h4 : ((zdistD 3 (szB.L n) (a i - a j) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h3
      linarith
    · by_cases h2 : a 1 = a 0 + Pi.single 0 1
      · exfalso
        have h3 := hclose (Or.inr h2)
        have h4 : ((zdistD 3 (szB.L n) (a i - a j) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h3
        linarith
      · simp [h1, h2]
  dsimp only
  rw [hA, norm_zero]
  exact Real.rpow_nonneg (by linarith) _


/-- `expIntI_kernel_unif` at the same data with `σ = (+,-)` (`σ₁ ≠ σ₂`, so the branch `(sum_res_2)` of the hypothesis is the one used,
for the sum-zero deterministic family `𝒜_v = 1_{a₂ = a₁} - 1_{a₂ = a₁ + e}`, nonzero by `inst_expIntI_tensors_ne_zero`, `‖𝒜_v‖ ≤ 1`) and
`X ≡ 1`: every hypothesis is discharged. -/
theorem inst_expIntI_kernel_unif_sumzero (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ), 7 / 8 ≤ v → v ≤ (u : ℝ) →
      ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) ![true, false] v (u : ℝ)
          (fun a : Fin 2 → Zd 3 (szB.L n) => (if a 1 = a 0 then (1 : ℂ) else 0) -
            (if a 1 = a 0 + (Pi.single 0 1 : Zd 3 (szB.L n)) then (1 : ℂ) else 0))‖ ≤
        ((szB.size n : ℕ) : ℝ) ^ τ * (4 * (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) n v) := by
  refine expIntI_kernel_unif (d := 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) (𝔠d := 1 / 300) (by norm_num) (by norm_num) szB zB flow_zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
    szB_reg5I (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) ![true, false]
    (fun n (_ : ℝ) => fun a : Fin 2 → Zd 3 (szB.L n) => (if a 1 = a 0 then (1 : ℂ) else 0) -
      (if a 1 = a 0 + (Pi.single 0 1 : Zd 3 (szB.L n)) then (1 : ℂ) else 0)) (fun _ _ => 1)
    (Or.inr fun n _ => inst_expIntI_sumZero (szB.L n) _) ?_
    (fun _ _ => zero_le_one) ⟨0, Filter.Eventually.of_forall fun n v _ _ => by simp⟩ ?_ τ hτ
  · intro ε' D hε' _
    exact Filter.Eventually.of_forall fun n v _ _ => inst_expIntI_dipole_decay n v ε' D hε'
  · intro τ' hτ'
    refine Filter.Eventually.of_forall fun n v _ _ => ?_
    have hN1 : (1 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) := by exact_mod_cast szB.one_le_size n
    have h1 : (1 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
    have hnorm : ‖fun a : Fin 2 → Zd 3 (szB.L n) => (if a 1 = a 0 then (1 : ℂ) else 0) -
        (if a 1 = a 0 + (Pi.single 0 1 : Zd 3 (szB.L n)) then (1 : ℂ) else 0)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
      by_cases h1 : a 1 = a 0
      · by_cases h2 : a 1 = a 0 + (Pi.single 0 1 : Zd 3 (szB.L n))
        · simp only [eq_true h1, eq_true h2, ↓reduceIte]; norm_num
        · simp only [eq_true h1, eq_false h2, ↓reduceIte]; norm_num
      · by_cases h2 : a 1 = a 0 + (Pi.single 0 1 : Zd 3 (szB.L n))
        · simp only [eq_false h1, eq_true h2, ↓reduceIte]; norm_num
        · simp only [eq_false h1, eq_false h2, ↓reduceIte]; norm_num
    linarith

/-- The two deterministic tensors of the kernel instances are nonzero: both have the value `1` at `a = 0` (`e ≠ 0` in `Z_4^3`). -/
theorem inst_expIntI_tensors_ne_zero :
    (fun a : Fin 2 → Zd 3 (szB.L 0) => if a 0 = a 1 then (1 : ℂ) else 0) 0 ≠ 0 ∧
    (fun a : Fin 2 → Zd 3 (szB.L 0) => (if a 1 = a 0 then (1 : ℂ) else 0) -
      (if a 1 = a 0 + (Pi.single 0 1 : Zd 3 (szB.L 0)) then (1 : ℂ) else 0)) 0 ≠ 0 := by
  have h : (Pi.single 0 1 : Zd 3 (szB.L 0)) ≠ 0 := by
    change (Pi.single 0 1 : Zd 3 4) ≠ 0
    decide
  refine ⟨by simp, ?_⟩
  simp [h.symm]

/-- `expIntI_concl_of_kernel` at `szB`, `zB`, `(7/8, 15/16)`, `P = STSigSame` (`σ 0 = σ 1`): the Duhamel identity is discharged by
`st6_duhEq_of_pin`; the uniform drift-kernel bound `hker` (the output of `expIntI_kernel_unif` for the drift tensors, other gates'
drift pins) stays a hypothesis, written with `σ 0 = σ 1` so that `STSigSame` is not a premise of a theorem (`scanPremises`). -/
theorem inst_expIntI_concl_of_kernel
    (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      ∀ (u : TimeIcc (fun _ : ℕ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) (v : ℝ), 7 / 8 ≤ v → v ≤ (u : ℝ) →
        ∀ σ : Fin 2 → Bool, σ 0 = σ 1 →
          ‖RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) σ v (u : ℝ)
              (fun b => szB.STExpDrift n (STflowE zB n) v σ b)‖ ≤
            ((szB.size n : ℕ) : ℝ) ^ τ *
              ((1 - v)⁻¹ * (szB.Bctl n v ^ (11 / 5 : ℝ) + szB.Bctl n v ^ (5 / 2 : ℝ)))) :
    STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  expIntI_concl_of_kernel szB flow_zB.1.2.2.1 (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    szB_reg5I
    (st6_duhEq_of_pin szB (stExpDuhamelZ_holds 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (szB_flow_ht (by norm_num)))
    STSigSame hker

end RBM.Gauss.Step6Inst

end
