/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.EMn2Exp2
import RBM3D.Induction.NewKLKL
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.EtermsMid2

/-!
# S5-13 (ticket T2328): the three error terms at `ℓ = L`, over the flow carrier (T2496, row U4s3a)

`stEtermsMidgL_of`, the pin `STEtermsMidgL` (`Chain/Step5Gen.lean`; paper
`paper/tex/3_5_Loop_Hierarchy.tex:1961-1979`, inputs `(eq:Step2_inputs)` `3_5:1340-1357`) over a
carrier tuple `(law, Flow, mkM, T0)`: in the window `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²`
(`STReg5Mid`), uniformly in `u ∈ [s,t]` and every `D > 0`:
`ℰ^{LK×LK} ≺ A^{-1/3} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `ℰ^{G̃} ≺ A^{-1/2} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`,
`(ℰ⊗ℰ)^{M,(2;k)} ≺ A^{-1/2} η_u⁻¹ (W^{-d}𝒯̃^L_{u,D})²`, `A = ilambda² W^d`.
`STLWTgL` stays a hypothesis (LW gate).  The band theorem `stEtermsMid_of_LWT` (`STEtermsMid`,
`Induction/Step5Pins.lean:275`) is its corollary through `STEtermsMid_iff_gL`.

Layout (T2496 1a-audit, cut A3, 1,800 rule): sections 1-7 (scalars, profile, glue, control, slow
variation, `EEk`, time sections) are in `Induction/EtermsMid2`; this file keeps section 8 (the net
lift), section 9 (the targets) and section 10 (instances).  Route: `Ĵ^L ≺ A^{-1/6}` from
`STGdecayWgL`; `ℰ^{LK×LK}` from `EtermsMid_NewKLKL`; the sections from `ST_LW_sectionsg`; the net
lift is `cont_core` at the law `μ` and the event of D2 (moduli `LemDecCalELip_EGtgL`,
`etermsMid_EEk_sub`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open private etermsMid_Bctl_window etermsMid_q_le etermsMid_A_big etermsMid_lam etermsMid_J etermsMid_A_prec etermsMid_zeta_ratio
  etermsMid_EEk_sub etermsMid_L2 etermsMid_S1W etermsMid_eta_pos etermsMid_sections from RBM3D.Induction.EtermsMid2
open private lemDecCalELipG_absorb from RBM3D.Induction.LemDecCalELip

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.BA

/-! ## 8. The net lift from the time sections to `u ∈ [s,t]` -/

section Lift

open RBM.Ind.ContinuityNet

variable {d : ℕ} (sz : Sizes d)

/-- `L ≤ N`. -/
private theorem etermsMid_L_le_size (hd : 1 ≤ d) (n : ℕ) : ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW : 1 ≤ sz.W n := sz.W_pos n
  have h1 : sz.L n ≤ sz.L n ^ d := Nat.le_self_pow (by omega) _
  have h2 : sz.L n ^ d ≤ (sz.W n * sz.L n) ^ d :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  exact_mod_cast h1.trans h2

/-- **The net lift** (`1_2:1400`, the standard `N^{-C}`-net argument; `cont_core` at the law `μ` and the event `G` of D2, `ε = N^{-CR}`): a
per-section domination with a deterministic control `ζ ≥ N^{-CR}` that moves by at most a factor `2` under a time change of size `N^{-A}`,
for a family that moves by at most `N^{-CR}` on `G`, is uniform in `u ∈ [s,t]`. -/
private theorem etermsMid_lift {μ : Measure sz.SeqΩ} {G : ℕ → Set sz.SeqΩ} (hG : HighProbAt μ sz.size G) {s t : ℕ → ℝ} {V : ℕ → Type}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (hsize : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) (hlen : ∀ n, t n - s n ≤ 1) {Cv A CR : ℝ} (hCv : 0 ≤ Cv)
    (hA : 0 ≤ A) (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv)
    (ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ)
    (hsec : ∀ tt : ∀ n, TimeIcc s t n,
      PrecL sz μ (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω))
    (hlow : ∀ᶠ n in atTop, ∀ p ω, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ ζ n p ω)
    (hclose : ∀ᶠ n in atTop, ∀ ω ∈ G n, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-A) → ∀ v : V n,
        ξ n (u, v) ω ≤ ξ n (u', v) ω + ((sz.size n : ℕ) : ℝ) ^ (-CR) ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) :
    PrecL sz μ ξ ζ := by
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_size sz hsize
  have hU : ∀ n, Nonempty (TimeIcc s t n × V n) := fun n => ⟨(⟨s n, le_rfl, hst n⟩, Classical.arbitrary (V n))⟩
  have hpt : PerTimeDomAt μ sz.size ξ ζ := (perTimeDomAt_iff_forall_section μ sz.size hU ξ ζ).mpr fun p =>
    StochDomAt.precomp_param (V := fun _ => Unit) (hsec fun n => (p n).1) (fun n _ => (p n).2)
  exact cont_core (V := V) (P := μ) (size := sz.size) hsizeN hst hlen hA hCv hcard hpt hG
    (ε := fun n => ((sz.size n : ℕ) : ℝ) ^ (-CR)) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hlow hclose

/-- **The time change at the mesh `N^{-A}`** (`A ≥ 6`): `η_{u'}⁻¹ (W^{-d} 𝒯̃^L_{u',D})^m ≤ 2 η_u⁻¹ (W^{-d} 𝒯̃^L_{u,D})^m`
for `m ≤ 2`, `|u-u'| ≤ N^{-A}`, `u, u' ≤ t`, `(1-t)⁻¹ ≤ N`, `ilambda ≤ 𝔡⁻¹`, `256 𝔡⁻¹ ≤ N`, `L ≤ N`. -/
private theorem etermsMid_zeta_close (n : ℕ) {C : FlowFM sz} {t u u' D A 𝔡 : ℝ} (hd : 1 ≤ d) (m : ℕ) (hm : m ≤ 2)
    (him : 0 < (C.m n).im) (hηC : ∀ v, C.eta n v = (1 - v) * (C.m n).im) (hg : 0 ≤ sz.lam n) (hg' : sz.lam n ≤ 𝔡⁻¹) (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t)
    (hN : (1 - t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hN2 : 2 ≤ ((sz.size n : ℕ) : ℝ))
    (hbig : 256 * 𝔡⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hA : 6 ≤ A)
    (hΔ : |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-A)) (a b : Zd d (sz.L n)) :
    (C.eta n u')⁻¹ * STprof sz n u' D ((sz.L n : ℕ) : ℝ) a b ^ m ≤
      2 * ((C.eta n u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hΔ
  have h1t : 0 < 1 - t := by linarith
  have hy : N ^ (-A / 2) ≤ (N ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hz : N ^ (-A) ≤ (N ^ 6)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hN3 : (0 : ℝ) < N ^ 3 := by positivity
  have hN6 : (0 : ℝ) < N ^ 6 := by positivity
  -- `x = 1/32`
  have hx : (1 - t)⁻¹ * |u - u'| ≤ 1 / 32 := by
    calc (1 - t)⁻¹ * |u - u'| ≤ N * (N ^ 6)⁻¹ := mul_le_mul hN (hΔ.trans hz) (abs_nonneg _) hN0.le
      _ ≤ N * (N ^ 5 * 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hN0.le
          calc N ^ 5 * 2 ≤ N ^ 5 * N := mul_le_mul_of_nonneg_left hN2 (by positivity)
            _ = N ^ 6 := by ring
      _ = 1 / 2 * (N ^ 4)⁻¹ := by field_simp
      _ ≤ 1 / 32 := by
          have h4 : (16 : ℝ) ≤ N ^ 4 := by
            calc (16 : ℝ) = 2 ^ 4 := by norm_num
              _ ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN2 4
          have : (N ^ 4)⁻¹ ≤ 1 / 16 := by rw [one_div]; exact inv_anti₀ (by norm_num) h4
          linarith
  -- `δ = 1/16`
  have hr : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤ N :=
    (ST_zdistInf_le sz n (a - b)).trans (etermsMid_L_le_size sz hd n)
  have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hδ : Real.sqrt (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) *
      (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|))) ≤ 1 / 16 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have hprod : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) * (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|)) ≤
        N * (𝔡⁻¹ * (N * (N ^ 3)⁻¹)) :=
      mul_le_mul hr (mul_le_mul hg' (mul_le_mul hN (hsq.trans hy) (Real.sqrt_nonneg _) hN0.le)
        (by positivity) (by linarith [hg, hg'])) (by positivity) hN0.le
    refine hprod.trans ?_
    have hinv : N * (𝔡⁻¹ * (N * (N ^ 3)⁻¹)) = 𝔡⁻¹ * (N ^ 2 * (N ^ 3)⁻¹) := by ring
    rw [hinv]
    have h5 : N ^ 2 * (N ^ 3)⁻¹ = N⁻¹ := by field_simp
    rw [h5]
    have : 𝔡⁻¹ * N⁻¹ ≤ 1 / 256 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hN0]
      linarith
    nlinarith
  exact etermsMid_zeta_ratio sz n m hm him hηC hg ht hut hu't (by norm_num) hx a b hδ (by norm_num)

/-- The net lift in the form used below: the Hölder-`1/2` modulus of `ξ` on `G` (any constant `CH`) and the
factor-`2` slow variation of `ζ` at every mesh `N^{-A}`, `A ≥ 6`, give the uniform domination. -/
private theorem etermsMid_lift2 {μ : Measure sz.SeqΩ} {G : ℕ → Set sz.SeqΩ} (hG : HighProbAt μ sz.size G) {s t : ℕ → ℝ} {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (hsize : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) (hlen : ∀ n, t n - s n ≤ 1) {Cv CR : ℝ} (hCv : 0 ≤ Cv)
    (hCR : 0 ≤ CR) (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv)
    (ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ)
    (hsec : ∀ tt : ∀ n, TimeIcc s t n,
      PrecL sz μ (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω))
    (hlow : ∀ᶠ n in atTop, ∀ p ω, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ ζ n p ω)
    (hH : ∃ CH : ℝ, 0 ≤ CH ∧ ∀ᶠ n in atTop, ∀ ω ∈ G n, ∀ (u u' : TimeIcc s t n) (v : V n),
      |ξ n (u, v) ω - ξ n (u', v) ω| ≤ ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)|)
    (hζ : ∀ A : ℝ, 6 ≤ A → ∀ᶠ n in atTop, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-A) → ∀ (v : V n) (ω : sz.SeqΩ),
        ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) :
    PrecL sz μ ξ ζ := by
  obtain ⟨CH, hCH0, hH'⟩ := hH
  have hA : (6 : ℝ) ≤ 2 * (CH + CR) + 6 := by linarith
  refine etermsMid_lift sz hG hsize hst hlen hCv (A := 2 * (CH + CR) + 6) (by linarith) hcard ξ ζ hsec hlow ?_
  filter_upwards [hH', hζ _ hA, hsize.eventually_ge_atTop 1] with n hn hz hN1
  intro ω hω u u' hΔ v
  refine ⟨?_, hz u u' hΔ v ω⟩
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hsq : Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * (CH + CR) + 6) / 2) :=
    cont_sqrt_abs_le hN0.le hΔ
  have h1 := (abs_le.1 (hn ω hω u u' v)).2
  have h2 : ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-CR) := by
    calc ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)|
        ≤ ((sz.size n : ℕ) : ℝ) ^ CH * ((sz.size n : ℕ) : ℝ) ^ (-(2 * (CH + CR) + 6) / 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (CH + -(2 * (CH + CR) + 6) / 2) := (Real.rpow_add hN0 _ _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-CR) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  linarith

/-- The floor of the control: `N^{-(3+2D)} ≤ A^{-1/2} η_u⁻¹ (W^{-d} 𝒯̃^L_{u,D})^m` for `m ∈ {1,2}`, `N ≥ 𝔡⁻²`. -/
private theorem etermsMid_floor (hd : 1 ≤ d) (n : ℕ) {C : FlowFM sz} {u D 𝔡 : ℝ} (m : ℕ) (hm2 : m ≤ 2)
    (hm : ‖C.m n‖ ≤ 1) (him : 0 < (C.m n).im) (hηC : C.eta n u = (1 - u) * (C.m n).im) (hu0 : 0 ≤ u) (hu1 : u < 1) (h𝔡 : 0 < 𝔡) (hl : 0 < sz.lam n) (hl' : sz.lam n ≤ 𝔡⁻¹)
    (hD : 0 ≤ D) (hbig : (𝔡⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (a b : Zd d (sz.L n)) :
    ((sz.size n : ℕ) : ℝ) ^ (-(3 + 2 * D)) ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (C.eta n u)⁻¹ *
      STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ N := ST_Wpow_le_size sz n
  have hA0 : 0 < STAI sz n := by unfold STAI; positivity
  have hAle : STAI sz n ≤ N ^ 2 := by
    unfold STAI
    calc sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ (𝔡⁻¹) ^ 2 * N :=
          mul_le_mul (pow_le_pow_left₀ hl.le hl' 2) hWd (by positivity) (by positivity)
      _ ≤ N * N := mul_le_mul hbig le_rfl hN0.le hN0.le
      _ = N ^ 2 := by ring
  have hA6 : N ^ (-1 : ℝ) ≤ STAI sz n ^ (-(1 / 2) : ℝ) := by
    have h := Real.rpow_le_rpow_of_nonpos hA0 hAle (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
    refine le_trans (le_of_eq ?_) h
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hη : 1 ≤ (C.eta n u)⁻¹ := by
    have hpos := etermsMid_eta_pos sz him hηC hu1
    refine (one_le_inv₀ hpos).2 ?_
    have hm1 : (C.m n).im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm)
    rw [hηC]; nlinarith
  have hP := ST_prof_lower_N sz (by omega : 0 < d) n hD u ((sz.L n : ℕ) : ℝ) a b
  have hP0 : 0 < N ^ (-(1 + D)) := Real.rpow_pos_of_pos hN0 _
  have hPm : (N ^ (-(1 + D))) ^ m ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m := pow_le_pow_left₀ hP0.le hP m
  have hPm' : (N ^ (-(1 + D))) ^ m = N ^ (-(1 + D) * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have hA6' : 0 ≤ STAI sz n ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hA0.le _
  have hm2' : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
  calc N ^ (-(3 + 2 * D)) ≤ N ^ (-1 : ℝ) * N ^ (-(1 + D) * m) := by
        rw [← Real.rpow_add hN0]
        refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
        nlinarith
    _ = N ^ (-1 : ℝ) * 1 * (N ^ (-(1 + D))) ^ m := by rw [hPm']; ring
    _ ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (C.eta n u)⁻¹ * STprof sz n u D ((sz.L n : ℕ) : ℝ) a b ^ m :=
        mul_le_mul (mul_le_mul hA6 hη (by norm_num) hA6') hPm (by positivity) (by positivity)

/-- `(1-t)⁻¹ ≤ N` in the window: `1 - t ≥ ilambda²/L^d`, `A ≥ 1`. -/
private theorem etermsMid_htN (n : ℕ) {t : ℝ} (hl : 0 < sz.lam n) (hA : 1 ≤ STAI sz n)
    (hRegt : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t) :
    (1 - t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have h1 : (1 - t)⁻¹ ≤ (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := inv_anti₀ (div_pos hg2 hLd) hRegt
  refine h1.trans ?_
  rw [inv_div, hsz]
  have hA' : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hA
  rw [div_le_iff₀ hg2]
  nlinarith [mul_pos hWd hLd]

/-- **The three error terms, uniformly in `u ∈ [s,t]`** (`(S5WG+M)`, the last two conjuncts): the net lift of
`etermsMid_sections` for `ℰ^{G̃}` (Hölder: `LemDecCalELip_EGt`) and for `(ℰ⊗ℰ)^{M,(2;k)}` (Hölder: `etermsMid_EEk_sub`). -/
private theorem etermsMid_BC_prec (hd : 3 ≤ d) {Cm : Step2Mat sz} {E : ℕ → ℝ} {μ : Measure sz.SeqΩ}
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {G : ℕ → Set sz.SeqΩ}
    {c κm 𝔡 𝔠 : ℝ} {s t : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω)
    (hc : 0 ≤ c) (hG : HighProbAt μ sz.size G) (hmod : LemDecCalELipG_Mod Hm G c) (hAd : sz.Admissible 𝔠 𝔡)
    (hκm : 0 < κm) (h𝔡 : 0 < 𝔡) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hS : ∀ n a, ∑ b, ‖Cm.S n a b‖ ≤ 1)
    (hIm : ∀ n, κm ≤ (Cm.m n).im) (hη : ∀ n u, Cm.eta n u = (1 - u) * (Cm.m n).im)
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hReg : STReg5Mid sz s t) {D : ℝ} (hD : 0 < D)
    (hsecG : ∀ tt : ∀ n, TimeIcc s t n,
      PrecL sz μ (U := STLab sz) (fun n v ω => ‖STEGtg Cm.toFlowFM n (tt n : ℝ) v.1 v.2 ω‖)
        (fun n v _ => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (tt n : ℝ))⁻¹ *
          STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1)))
    (hsecE : ∀ tt : ∀ n, TimeIcc s t n,
      PrecL sz μ (U := fun n => Fin 2 × STLab sz n)
        (fun n v ω => ‖STEEg Cm.toFlowFM n (tt n : ℝ) v.1 v.2.1 v.2.2 ω‖)
        (fun n v _ => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (tt n : ℝ))⁻¹ *
          STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2.2 0) (v.2.2 1) ^ 2)) :
    PrecL sz μ (U := STIdx2 sz s t) (fun n p ω => ‖STEGtg Cm.toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    PrecL sz μ (U := fun n => STIdx2 sz s t n × Fin 2)
      (fun n p ω => ‖STEEg Cm.toFlowFM n (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (p.1.1 : ℝ))⁻¹ *
        STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hsize : sz.SizeTendsto := hAd.2.2.1
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_size sz hsize
  have him : ∀ n, 0 < (Cm.m n).im := fun n => hκm.trans_le (hIm n)
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [ht1 n, hs n]
  have hevent : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [etermsMid_lam sz hAd, etermsMid_A_big sz hAd 1] with n hl hA1
    exact etermsMid_htN sz n hl.1 hA1 (hReg n).1
  have hbigN : ∀ᶠ n in atTop, 4 ≤ sz.size n ∧ (𝔡⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ∧
      256 * 𝔡⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ 2 ≤ ((sz.size n : ℕ) : ℝ) ∧ 18 ≤ ((sz.size n : ℕ) : ℝ) ∧
      1 ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hsize.eventually_ge_atTop (max 4 (max ((𝔡⁻¹) ^ 2) (max (256 * 𝔡⁻¹) 18)))] with n hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hn
      exact_mod_cast this
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hn
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
    · exact (by norm_num : (2 : ℝ) ≤ 4).trans ((le_max_left _ _).trans hn)
    · exact (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
    · exact (by norm_num : (1 : ℝ) ≤ 4).trans ((le_max_left _ _).trans hn)
  have hQ : ∀ᶠ n in atTop, (Cm.eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 :=
    (LemDecCalELip_envg hκm hIm hη hsize hevent 0).mono fun n h => h.2.2.1
  refine ⟨?_, ?_⟩
  · -- `ℰ^{G̃}`
    obtain ⟨C₁, hC0, hCH⟩ := LemDecCalELip_EGtgL hL hLM hc hmod hm hS hs ht1 hsize hQ
    refine etermsMid_lift2 sz hG (V := STLab sz) hsize hst hlen (Cv := 3) (CR := 3 + 2 * D) (by norm_num)
      (by linarith) ?_ (fun n p ω => ‖STEGtg Cm.toFlowFM n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) hsecG ?_ ⟨C₁, hC0, ?_⟩ ?_
    · filter_upwards [hbigN] with n hb
      exact ST_card_lab_le sz n hb.1
    · filter_upwards [etermsMid_lam sz hAd, hbigN] with n hl hb p ω
      obtain ⟨⟨u, hsu, hut⟩, v⟩ := p
      have := etermsMid_floor sz hd1 n 1 (by norm_num) (hm n) (him n) (hη n _) ((hs n).trans hsu) (lt_of_le_of_lt hut (ht1 n)) h𝔡
        hl.1 hl.2 hD.le hb.2.1 hb.2.2.2.2.2 (v.2 0) (v.2 1)
      simpa only [pow_one] using this
    · filter_upwards [hCH, hsizeN.eventually (eventually_ge_atTop 1)] with n hn hN1 ω hω u u' v
      exact (abs_norm_sub_norm_le _ _).trans (hn ω hω u u' v.1 v.2)
    · intro A hA
      filter_upwards [etermsMid_lam sz hAd, hevent, hbigN] with n hl hN hb u u' hΔ v ω
      have := etermsMid_zeta_close sz n (D := D) hd1 1 (by norm_num) (him n) (hη n) hl.1.le hl.2 (ht1 n) u.2.2 u'.2.2
        hN hb.2.2.2.1 hb.2.2.1 hA hΔ (v.2 0) (v.2 1)
      simp only [pow_one] at this
      change STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (u' : ℝ))⁻¹ * _ ≤ 2 * (STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (u : ℝ))⁻¹ * _)
      have hA6 : 0 ≤ STAI sz n ^ (-(1 / 2) : ℝ) := by
        unfold STAI; exact Real.rpow_nonneg (by positivity) _
      calc _ = STAI sz n ^ (-(1 / 2) : ℝ) * ((Cm.eta n (u' : ℝ))⁻¹ * _) := by ring
        _ ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (2 * ((Cm.eta n (u : ℝ))⁻¹ * _)) :=
          mul_le_mul_of_nonneg_left this hA6
        _ = _ := by ring
  · -- `(ℰ⊗ℰ)^{M}`
    have h := etermsMid_lift2 sz hG (V := fun n => Fin 2 × STLab sz n) hsize hst hlen (Cv := 4) (CR := 3 + 2 * D)
      (by norm_num) (by linarith) ?_ (fun n p ω => ‖STEEg Cm.toFlowFM n (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2 ω‖)
      (fun n p _ => STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2.2 0) (p.2.2.2 1) ^ 2) hsecE ?_ ⟨((19 + 1 : ℕ) : ℝ) + c, by positivity, ?_⟩ ?_
    · have h' := StochDomAt.precomp_param h (fun n (p : STIdx2 sz s t n × Fin 2) => (p.1.1, (p.2, p.1.2.1, p.1.2.2)))
      exact h'
    · filter_upwards [hbigN] with n hb
      exact ST_card_fin2_lab_le sz n hb.1
    · filter_upwards [etermsMid_lam sz hAd, hbigN] with n hl hb p ω
      obtain ⟨⟨u, hsu, hut⟩, v⟩ := p
      exact etermsMid_floor sz hd1 n 2 (le_refl 2) (hm n) (him n) (hη n _) ((hs n).trans hsu) (lt_of_le_of_lt hut (ht1 n)) h𝔡
        hl.1 hl.2 hD.le hb.2.1 hb.2.2.2.2.2 (v.2.2 0) (v.2.2 1)
    · filter_upwards [lemDecCalELipG_loops hL hLM hc hmod hm ht1 hQ, LemDecCalELip_envg hκm hIm hη hsize hevent 18] with n hlp hn ω hω u u' v
      obtain ⟨h18, h1, -, -⟩ := hn
      have hsub := etermsMid_EEk_sub sz Cm.toFlowFM n ω rfl h1 (Real.one_le_rpow h1 hc) (hS n)
        (fun σ a => (hlp ω hω).1 u u' ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 σ a) v.1 v.2.1 v.2.2
      exact (abs_norm_sub_norm_le _ _).trans (hsub.trans (lemDecCalELipG_absorb (e := 19) (k := 18) h18 h1 (Real.sqrt_nonneg _)))
    · intro A hA
      filter_upwards [etermsMid_lam sz hAd, hevent, hbigN] with n hl hN hb u u' hΔ v ω
      have := etermsMid_zeta_close sz n (D := D) hd1 2 (le_refl 2) (him n) (hη n) hl.1.le hl.2 (ht1 n) u.2.2 u'.2.2
        hN hb.2.2.2.1 hb.2.2.1 hA hΔ (v.2.2 0) (v.2.2 1)
      change STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (u' : ℝ))⁻¹ * _ ≤ 2 * (STAI sz n ^ (-(1 / 2) : ℝ) * (Cm.eta n (u : ℝ))⁻¹ * _)
      have hA6 : 0 ≤ STAI sz n ^ (-(1 / 2) : ℝ) := by
        unfold STAI; exact Real.rpow_nonneg (by positivity) _
      calc _ = STAI sz n ^ (-(1 / 2) : ℝ) * ((Cm.eta n (u' : ℝ))⁻¹ * _) := by ring
        _ ≤ STAI sz n ^ (-(1 / 2) : ℝ) * (2 * ((Cm.eta n (u : ℝ))⁻¹ * _)) :=
          mul_le_mul_of_nonneg_left this hA6
        _ = _ := by ring

end Lift

/-! ## 9. The target -/

/-- **`(S5WG+M000)`, `(S5WG+M)` over a flow carrier** (`3_5:1961-1979`; the pin `STEtermsMidgL`, `Chain/Step5Gen.lean:239`; band `stEtermsMid_of_LWT`,
re-derived below): in the window `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²`, uniformly in `u ∈ [s,t]` and every `D > 0`,
`ℰ^{LK×LK} ≺ A^{-1/3} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `ℰ^{G̃} ≺ A^{-1/2} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `(ℰ⊗ℰ)^{M,(2;k)} ≺ A^{-1/2} η_u⁻¹ (W^{-d}𝒯̃^L_{u,D})²`.
Family premises (rows of the ticket table): `hF` flow facts (row 1), `hLW` the light-weight pin (row 5; the LW gate), `hEMe, hHK, hBd` the facts of
`lem: EMn2_N` and the size data (row 6), `hK2, hNew` the decay of `𝒦^{(2)}` and `lem:newKLK` at `ℓ = L` (A9, row 7), `hFM` the flow modulus D2
(row 8, `∃ c` before `(sz, z)`), `hmn, hSr` the inline `‖m‖ ≤ 1` and `Σ_b |S_{ab}| ≤ 1` (A7), `hLF` the loop form (row 10). -/
theorem _root_.RBM.BA.stEtermsMidgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ)
    (hF : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hLW : STLWTgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hEMe : emn2ExpFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0 Hf ζf)
    (hHK : emn2ExpHK d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hBd : STBdatagL d Flow T0)
    (hK2 : Step2IterGen_K2 d Flow mkM) (hNew : EtermsMid_NewKLKL d Flow mkM)
    (hFM : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c)
    (hmn : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSr : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b, ‖(mkM sz z).S n a b‖ ≤ 1)
    (hLF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z)) :
    STEtermsMidgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨min (1 / 100) (1 / (30 * Cd)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _hKb _hKw _hLKs _hDec _hDecS hCon _hStep1 hStep2 _hLmax _hLKU D hD
  obtain ⟨hLoc, -, hGd⟩ := hStep2
  have h𝔠d : 0 < min (1 / 100) (1 / (30 * Cd)) := lt_min (by norm_num) (by positivity)
  have hcC : min (1 / 100) (1 / (30 * Cd)) * Cd ≤ 1 / 30 := by
    calc min (1 / 100) (1 / (30 * Cd)) * Cd ≤ (1 / (30 * Cd)) * Cd :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hCd.le
      _ = 1 / 30 := by field_simp
  obtain ⟨κm, hκm, hFm⟩ := hF κ hκ
  obtain ⟨hAd, hT1, hIm, hηeq⟩ := hFm sz ε 𝔠 𝔡 z hflow
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hAd.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htz n) (hT1 n)
  have hd0 : 0 < d := by omega
  have ht0 : ∀ n, 0 ≤ t n := fun n => (hs n).trans (hst n).le
  have hm := hmn sz κ ε 𝔠 𝔡 z hκ hflow
  have him : ∀ n, 0 < ((mkM sz z).m n).im := fun n => hκm.trans_le (hIm n)
  -- the size data `cB W^{-d} ≤ W^{-d} B_{u,0} ≤ N^{-c}`
  obtain ⟨cB, hcB, hBdata⟩ := hBd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hBdz⟩ := hBdata 𝔠
  have hBdd := hBdz sz z hflow t ht0 htz
  have hB1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → sz.Bctl n u ≤ 1 := by
    filter_upwards [hBdd, hsize.eventually (eventually_ge_atTop 1)] with n hn hN1 u hu0 hut
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    exact (hn u hu0 hut).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  have hBdc : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBdd] with n hn u hu0 hut using (hn u hu0 hut).2
  -- the decay of `𝒦^{(2)}`, `lem:newKLK` at `ℓ = L` (A9) and D2
  obtain ⟨CK, hCK, hK2d⟩ := hK2 hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow s t hs ht1
  obtain ⟨Ck, δ₀, hC, hδ₀, hnew⟩ := hNew hd κ 𝔡 hκ h𝔡
  obtain ⟨c₀, hc₀, hFMz⟩ := hFM κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Hm, G, hLM, hGMM, hG, hmod⟩ := hFMz sz 𝔠 z hflow
  -- the light-weight pins on the flow guarded by `0 < κ` (the form of `ST_LW_sectionsg`)
  have hFl : Step2EventsGen_Flow d (fun sz κ ε 𝔠 𝔡 z => 0 < κ ∧ Flow sz κ ε 𝔠 𝔡 z) T0 :=
    ⟨fun sz' κ' ε' 𝔠' 𝔡' z' h => by obtain ⟨_, _, H⟩ := hF κ' h.1; exact (H sz' ε' 𝔠' 𝔡' z' h.2).1,
     fun sz' κ' ε' 𝔠' 𝔡' z' hκ' h n => by obtain ⟨_, _, H⟩ := hF κ' hκ'; exact (H sz' ε' 𝔠' 𝔡' z' h.2).2.1 n⟩
  have hEM := stEMn2ExpgL_of law hd hEMe hHK
  have hS1W := etermsMid_S1W sz hLoc hB1 hs
  have hL2 := fun D (hD : 0 < D) => etermsMid_L2 sz hAd hReg hCon h𝔠d hCd hcC hGd hCK hK2d hD
  have hJ := fun D (hD : 0 < D) => etermsMid_J sz hAd hReg hCon h𝔠d hCd hcC hGd hD
  have hsec := fun (tt : ∀ n, TimeIcc s t n) =>
    etermsMid_sections sz hFl (fun κ' ε' 𝔡' hκ' hε' h𝔡' 𝔠' sz' z' hf => hLW κ' ε' 𝔡' hκ' hε' h𝔡' 𝔠' sz' z' hf.2)
      (fun κ' ε' 𝔡' hκ' hε' h𝔡' 𝔠' sz' z' hf => hEM κ' ε' 𝔡' hκ' hε' h𝔡' 𝔠' sz' z' hf.2) hd0 hκ hε h𝔡 ⟨hκ, hflow⟩ hs htz hReg
      hS1W hcB hc hBdd him hηeq hL2 hJ tt hD
  have hBC := etermsMid_BC_prec sz hd (hLF sz κ ε 𝔠 𝔡 z hκ hflow) hLM hc₀ hG hmod hAd hκm h𝔡 hm (hSr sz κ ε 𝔠 𝔡 z hκ hflow) hIm hηeq
    hs (fun n => (hst n).le) ht1 hReg hD (fun tt => (hsec tt).1) (fun tt => (hsec tt).2)
  exact ⟨etermsMid_A_prec sz hLM hGMM hG hmod hAd hReg hCon h𝔠d hCd hcC hGd hLoc (hnew ε 𝔠 sz z hflow) hC hδ₀ hm him hηeq hs ht1 h𝔡 hc hBdc hD,
    hBC.1, hBC.2⟩

/-- **The band tuple of the pin `STEtermsMidgL`**: `stEtermsMidgL_of` at `(seqP, STFlow, bandStep2Mat ∘ STflowE, lemT)`, with the energy `STflowE z`, the
model matrix `seqHflow`, the spectral parameter `zt`; every premise besides `STLWTgL` is discharged by a merged band result (`step5CasesGen_flowFacts_band`,
`emn2Exp_bandFacts`, `emn2Exp2_bandHK`, `bandFM_STBdata`, `step2IterGen_K2_band`, `etermsMid_newKLKL_band`, D2 `lemDecCalELipG_flowMod_band`,
`norm_mE`, `sum_norm_SB_row`, `stepDecompGen_loopForm_band`). -/
theorem etermsMid_band_gL (d : ℕ) (hd : 3 ≤ d)
    (hLW : STLWTgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    STEtermsMidgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  RBM.BA.stEtermsMidgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun _ z => STflowE z)
    (fun sz _ n u ω => sz.seqHflow n u ω) (fun _ z n u => zt (STflowE z n) u) (step5CasesGen_flowFacts_band d) hLW
    (emn2Exp_bandFacts d) (emn2Exp2_bandHK d hd) ((bandFM_STBdata d).1 (ST_Bdata_holds (by omega)))
    (step2IterGen_K2_band d) (etermsMid_newKLKL_band d)
    (fun _ _ _ _ _ _ => ⟨1, zero_le_one, fun sz _ z h => lemDecCalELipG_flowMod_band sz (tendsto_size sz h.1.2.2.1) _⟩)
    (fun sz κ ε 𝔠 𝔡 z _ h n => (norm_mE (abs_lemE_lt_two (ST_flow_im_pos sz h n)).le).le)
    (fun sz _ _ _ _ z _ _ n a => (sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) a).le)
    (fun sz _ _ _ _ z _ h => stepDecompGen_loopForm_band sz (STflowE z) fun n => abs_lemE_lt_two (ST_flow_im_pos sz h n))

/-- **`(S5WG+M000)`, `(S5WG+M)`** (`3_5:1961-1979`; the target `STEtermsMid`, `Induction/Step5Pins.lean:275`, S5-13) from the light-weight pin `STLWT`
(the LW gate proves it, `STLWT_of_LWtermExp`): the band corollary, name and type unchanged (G1), of `stEtermsMidgL_of` through `STEtermsMid_iff_gL`. -/
theorem stEtermsMid_of_LWT (d : ℕ) (hLWT : STLWT d) : STEtermsMid d :=
  (RBM.BA.STEtermsMid_iff_gL d).2 fun hd => etermsMid_band_gL d hd ((RBM.BA.bandFM_STLWT d).1 hLWT) hd

end RBM.Gauss.Sizes

/-! ## 10. Compiled nonempty instances (`d = 3`)

The merged Step-5 data of case (i) (`RBM.Gauss.Step5Inst`): `szB` (`L = 4`, `W_n = n + 4`, `ilambda = 1`), the flow
`zB_n = 1/2 + i/64`, `(s, t) = (7/8, 15/16)`, i.e. `1/64 = ilambda²/L^3 ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ ilambda² = 1`
(`STReg5Mid`).  Every deterministic hypothesis (flow, time ranges, window, `(con_st_ind)` at every `𝔠_d > 0`) is discharged
by the merged `inst_ing5_I`; what stays a hypothesis is `STLWT 3` (the LW gate's pin) and the stochastic premises of
Steps 1-4 inside `InstIng5Concl`. -/

namespace RBM.Gauss.EtermsMidInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

/-- **The target `stEtermsMid_of_LWT` at `d = 3`**: at `(szB, zB, 7/8, 15/16)` and `C_d = 1`, the constant `𝔠_d` of the pin
exists, and the three bounds follow from the Step 1-4 premises (hypotheses) and `STLWT 3` (hypothesis). -/
example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 1 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 1 one_pos

/-- The same at `C_d = 100`. -/
example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 100 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 100 (by norm_num)

/-- The window `1/(2A) ≤ W^{-d}B_{u,0} ≤ 2/A` at `(szB, n, u = 15/16)`, `A = (n+4)^3`. -/
example (n : ℕ) : 1 / (2 * STAI szB n) ≤ szB.Bctl n (15 / 16) ∧ szB.Bctl n (15 / 16) ≤ 2 / STAI szB n :=
  etermsMid_Bctl_window szB n (by simp [szB]) (by norm_num [szB]) (by norm_num [szB])

/-- The exponent arithmetic `ρ^{C_d} Δ^{1/5} ≤ 2 A^{-1/6}` (`𝔠_d C_d ≤ 1/30`, `ρ ≤ Δ_t^{-𝔠_d}`) at `A = 8`, `C_d = 1`,
`𝔠_d = 1/100`, `ρ = 101/100`, `Δ_t = 1/12 ∈ [1/(2A), 2/A]`, `Δ_u = 1/8 ≤ 2/A`. -/
example : ((101 / 100 : ℝ)) ^ (1 : ℝ) * (1 / 8 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * (8 : ℝ) ^ (-(1 / 6) : ℝ) := by
  refine etermsMid_q_le (A := 8) (ρ := 101 / 100) (b := 1 / 8) (bt := 1 / 12) (Cd := 1) (c := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (1 / 12 : ℝ) = 12⁻¹ by norm_num, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  calc (101 / 100 : ℝ) = ((101 / 100 : ℝ) ^ 100) ^ (((100 : ℕ) : ℝ)⁻¹) := by
        rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    _ ≤ 12 ^ (1 / 100 : ℝ) := by
        rw [show (1 / 100 : ℝ) = ((100 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)


/-- **The generic pin at the band tuple, instantiated** (target 5): `stEtermsMidgL_of` at `(seqP, STFlow, bandStep2Mat ∘ STflowE, lemT)`, every premise
discharged by a band result except `STLWTgL` (the LW gate's pin), gives through `STEtermsMid_iff_gL` the same instance `InstIng5Concl` at
`(szB, zB, 7/8, 15/16)` and every `C_d > 0`. -/
example (hLW : RBM.BA.STLWTgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => RBM.BA.bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_etermsMid ((RBM.BA.STEtermsMid_iff_gL 3).2 (etermsMid_band_gL 3 (by norm_num) hLW)) Cd hCd

end RBM.Gauss.EtermsMidInst
