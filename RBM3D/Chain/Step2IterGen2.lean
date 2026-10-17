/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2IterGen

/-!
# The Step 2 iteration over the carrier, second half (BA-T row T1a, ticket T2478)

Continuation of `Chain/Step2IterGen.lean` (targets 1-3).  The band file `Induction/Step2Iterate.lean` is **not** edited; this file states
the generic forms of its iteration over the scale family, the per-time outputs, the averaged law and the skeleton `ST_step2_of_pins`
over a carrier family `(law, Flow, mk, T0)` with `mk` valued in `Step2Mat`.  No `BA/` import, no kernel is defined.

* **Target 4.**  `ST_iterateg`, `ST_decay_ptg` (concludes `STStep2DecayPTgL`), `ST_L2_decay_ptg` (concludes `STL2decayPTgL`),
  `ST_base_invg`.
* **Target 5.**  `ST_avgU_of_avgg` (`STStep2AvggL → STAvgUgL`, under `Step2IterGen_OneLoop`), `ST_concl_of_step2g`.
* **Target 6.**  `ST_step2_of_pinsg`: conclusion `STStep2G d law Flow (fun sz z => (mk sz z).toFlowFM) T0`.  The only grid premise is
  `STGridMartgL` (loop length 2 only); `STBdatagL` replaces `ST_Bdata_holds`.  Band readings `stBdatagL_band`, `stScaleExistsgL_band`,
  the band re-derivation `step2IterGen_step2_of_pins_band`.
* **Band re-derivations and instances** (section 8): `example : type_of% @<band name>` for `ST_iterate`, `ST_decay_pt`,
  `ST_L2_decay_pt`, `ST_base_inv`; compiled nonempty instances of targets 4-6 at `d = 3`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 4. Target 4: the iteration over scales and the per-time outputs (`Step2Iterate:725-1013`, `1316-1374`) -/

/-- **The iteration over the scale family** (band `ST_iterate`, `Step2Iterate.lean:725`; `3_5:570–577`): `Inv(K_m) ⇒ SelfImp(K_m) ⇒
Inv(K_{m+1})` for every level `m` of an admissible family, from the base `Inv(K_0)`, the one-step improvement `hSelf` and the
deterministic `𝒦^{(2)}` bound. -/
theorem ST_iterateg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ} {Cd C_K : ℝ}
    (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n)
    (hCK : 0 < C_K)
    (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInvgL C μ s t Kf → STSelfImpgL C μ Cd s t Kf)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖C.K n u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1)
    (Kseq : ℕ → ℕ → ℝ → ℝ) (hAdm : STScaleAdm sz s t Kseq)
    (hbase : STScaleInvgL C μ s t (Kseq 0)) :
    ∀ m, STScaleInvgL C μ s t (Kseq m) ∧ STSelfImpgL C μ Cd s t (Kseq m) := by
  intro m
  induction m with
  | zero => exact ⟨hbase, hSelf _ (hAdm.2.1 0) hbase⟩
  | succ m ih =>
    have hinv' : STScaleInvgL C μ s t (Kseq (m + 1)) :=
      ST_nextg C μ hsz hst hCK (Kseq m) (Kseq (m + 1)) hK2
        (hAdm.2.2.1 m) (hAdm.2.2.2.1 m)
        hq ih.2
    exact ⟨hinv', hSelf _ (hAdm.2.1 (m + 1)) hinv'⟩

/-- **`(Eq:Gdecay_w)` from the iteration** (band `ST_decay_pt`, `Step2Iterate.lean:752`; `3_5:575–577`): after `M(D)` steps the scale family
is at the floor, and `ST_decay_of_finalg` turns the last self-improving bound into the per-time `(Eq:Gdecay_w)`.  Concludes
`STStep2DecayPTgL`. -/
theorem ST_decay_ptg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ} {Cd C_K : ℝ}
    (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n)
    (hCK : 0 < C_K)
    (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInvgL C μ s t Kf → STSelfImpgL C μ Cd s t Kf)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖C.K n u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1)
    (Kseq : ℕ → ℕ → ℝ → ℝ) (hAdm : STScaleAdm sz s t Kseq)
    (hbase : STScaleInvgL C μ s t (Kseq 0)) :
    STStep2DecayPTgL C μ Cd s t := by
  have hit := ST_iterateg C μ hsz hst hCK hSelf hK2 hq Kseq hAdm hbase
  refine ST_decay_of_finalg C μ (fun D hD => ?_) ?_ ?_
  · obtain ⟨M, hM⟩ := hAdm.2.2.2.2 D hD
    refine ⟨Kseq M, (hit M).2, ?_⟩
    filter_upwards [hM, hAdm.2.2.1 M] with n hn hr u hsu hut
    exact ⟨(hr u hsu hut).1, hn u hsu hut⟩
  · filter_upwards [hq] with n hn u hsu hut
    obtain ⟨h1, h2, h3⟩ := hn u hsu hut
    have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ hW)
    calc ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 * 1 :=
          mul_le_mul (h1.trans h3) hWd (inv_nonneg.mpr (pow_nonneg (by linarith) d)) zero_le_one
      _ = 1 := one_mul 1
  · filter_upwards [hq] with n hn u hsu hut using (hn u hsu hut).2.1

/-- **`(eq:L2_decay)`** (band `ST_L2_decay_pt`, `Step2Iterate.lean:924`; `3_5:455–462`) from `(Eq:Gdecay_w)` and the `𝒦^{(2)}` bound, per time,
at the floor `D₁ = 1/𝔠` (`W^{-D₁} ≤ N⁻¹`).  Concludes `STL2decayPTgL`. -/
theorem ST_L2_decay_ptg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ} {Cd C_K : ℝ}
    (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hCK : 0 < C_K) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hband : sz.Bandwidth 𝔠) (hdec : STStep2DecayPTgL C μ Cd s t)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖C.K n u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1) :
    STL2decayPTgL C μ s t := by
  have hsize := tendsto_size sz hsz
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = 1 / 𝔠 := ⟨_, rfl⟩
  have hD₁pos : 0 < D₁ := by rw [hD₁]; positivity
  have hWD : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ ((sz.size n : ℕ) : ℝ)⁻¹ := by
    filter_upwards [hband] with n hn
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    calc ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-D₁) :=
          Real.rpow_le_rpow_of_nonpos hNc hn (by linarith)
      _ = ((sz.size n : ℕ) : ℝ)⁻¹ := by
          rw [← Real.rpow_mul hN0.le, ← Real.rpow_neg_one]; congr 1; rw [hD₁]; field_simp
  have hcard : ∀ᶠ n in atTop,
      (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 4)] with n hn using ST_card_lab_le sz n hn
  refine Step2EventsGen_PT_of_sections μ (V := fun n => Fin 2 → Zd d (sz.L n)) hst
    (fun n p ω => ‖C.L n (p.1 : ℝ) ![false, true] p.2 ω‖)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2 0 - p.2 1))) (fun tt => ?_)
  have hsec := Step2EventsGen_sections_of_PT μ (V := STLab sz) (s := s) (t := t)
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω -
      C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
      STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
      Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D₁))
    (by norm_num) hcard (hdec D₁ hD₁pos) tt
  have h1 := StochDomAt.precomp_param (V := fun n => Fin 2 → Zd d (sz.L n))
    (show StochDomAt μ sz.size (U := STLab sz) _ _ from hsec)
    (fun n a => (![false, true], a))
  have hKp : StochDomAt μ sz.size (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a ω => ‖C.K n (tt n : ℝ) ![false, true] a‖)
      (fun n a _ => C_K * STprof sz n (tt n : ℝ) D₁ ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) :=
    Step2EventsGen_prec_of_le_ev μ (fun n a _ => mul_nonneg hCK.le (ST_STprof_pos sz _ _ _ _ _ _).le)
      (by
        filter_upwards [hK2] with n hn a ω
        exact hn (tt n : ℝ) D₁ _ a (tt n).2.1 (tt n).2.2 hD₁pos.le)
  have hsum := StochDomAt.add hsize hKp h1
  have hL : StochDomAt μ sz.size (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a ω => ‖C.L n (tt n : ℝ) ![false, true] a ω‖)
      (fun n a ω => C_K * STprof sz n (tt n : ℝ) D₁ ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
        (((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (tt n : ℝ) (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (tt n : ℝ)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D₁))) := by
    refine StochDomAt.of_le_left (fun n a ω => ?_) hsum
    have := norm_add_le (C.K n (tt n : ℝ) ![false, true] a)
      (C.L n (tt n : ℝ) ![false, true] a ω -
        C.K n (tt n : ℝ) ![false, true] a)
    simpa [add_sub_cancel] using this
  have hmono : PrecL sz μ (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a ω => ‖C.L n (tt n : ℝ) ![false, true] a ω‖)
      (fun n a _ => (2 + 2 * C_K) * STWB sz n (tt n : ℝ) (zdistInf d (sz.L n) (a 0 - a 1))) := by
    refine Step2EventsGen_prec_mono_eventually μ ?_ hL
    filter_upwards [hq, hWD] with n hn hW a ω
    obtain ⟨h1, h2, h3⟩ := hn (tt n : ℝ) (tt n).2.1 (tt n).2.2
    exact ST_L2_cmp sz n hCK ((hs0 n).trans (tt n).2.1)
      (lt_of_le_of_lt (tt n).2.2 (ht1 n)) h2 (h1.trans h3) hW a
  have hpos : ∀ (n : ℕ) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ),
      0 ≤ STWB sz n (tt n : ℝ) (zdistInf d (sz.L n) (a 0 - a 1)) := fun n a _ => by
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact (inv_nonneg.mpr hN0.le).trans (ST_STWB_lower sz n ((hs0 n).trans (tt n).2.1)
      (lt_of_le_of_lt (tt n).2.2 (ht1 n)) _)
  have hcst := StochDomAt.const_mul_left (P := μ) hsize
    (show 0 ≤ 2 + 2 * C_K by linarith) hpos (StochDomAt.refl (P := μ) hsize hpos)
  exact StochDomAt.trans hsize hmono hcst

/-- **The base of the iteration** (band `ST_base_inv`, `Step2Iterate.lean:1316`; `(ksjjuw)`, `3_5:512–518`): `(eq:opt_L2)` and
`(eq:simpleboundK)` give `𝓛^{(2)}_{u,σ,(a,b)} ≺ W^{-d} 𝒯̃^{0}_{u,D}(|a-b|)`, i.e. `Inv(K_0 = 0)`. -/
theorem ST_base_invg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ}
    (hsz : sz.SizeTendsto) (hst : ∀ n, s n ≤ t n) {C_K : ℝ}
    (hCK : 0 < C_K)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖C.K n u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hOpt : PrecPTL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => sz.Bctl n (p.1 : ℝ))) :
    STScaleInvgL C μ s t (fun n u => 0) := by
  intro tt D hD
  have hsize := tendsto_size sz hsz
  have hcard : ∀ᶠ n in atTop,
      (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 4)] with n hn using ST_card_lab_le sz n hn
  have hsec := Step2EventsGen_sections_of_PT μ (V := STLab sz) (s := s) (t := t)
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω -
      C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ)) (by norm_num) hcard hOpt tt
  have hres := StochDomAt.precomp_param
    (V := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (show StochDomAt μ sz.size (U := STLab sz) _ _ from hsec)
    (fun n p => (p.1.1, p.2))
  have hnonneg : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) :=
    fun n p _ => mul_nonneg hCK.le (ST_STprof_pos sz n _ _ _ _ _).le
  have hKp : StochDomAt μ sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.K n (tt n : ℝ) p.1.1 p.2‖)
      (fun n p _ => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1)) :=
    Step2EventsGen_prec_of_le_ev μ hnonneg (by
      filter_upwards [hK2] with n hn p ω
      exact hn (tt n : ℝ) D p.1.1 p.2 (tt n).2.1 (tt n).2.2 hD.le)
  have hsum := StochDomAt.add hsize hKp hres
  have hL : StochDomAt μ sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p ω => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) +
        sz.Bctl n (tt n : ℝ)) := by
    refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
    have := norm_add_le (C.K n (tt n : ℝ) p.1.1 p.2)
      (C.L n (tt n : ℝ) p.1.1 p.2 ω - C.K n (tt n : ℝ) p.1.1 p.2)
    simpa [add_sub_cancel] using this
  have hmono : PrecL sz μ
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p _ => (C_K + 1) * STprof sz n (tt n : ℝ) D 0 (p.2 0) (p.2 1)) := by
    refine Step2EventsGen_prec_mono_eventually μ (Eventually.of_forall fun n p ω => ?_) hL
    have h1 := ST_prof_L_le_zero sz n (tt n : ℝ) D (p.2 0) (p.2 1)
    have h2 := ST_prof_zero_ge sz n (tt n : ℝ) D (p.2 0) (p.2 1)
    nlinarith [mul_le_mul_of_nonneg_left h1 hCK.le]
  have hpos : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ STprof sz n (tt n : ℝ) D 0 (p.2 0) (p.2 1) :=
    fun n p _ => (ST_STprof_pos sz n _ _ _ _ _).le
  have hcst := StochDomAt.const_mul_left (P := μ) hsize (show 0 ≤ C_K + 1 by linarith)
    hpos (StochDomAt.refl (P := μ) hsize hpos)
  exact StochDomAt.trans hsize hmono hcst

/-! ## 5. Target 5: the averaged law and the bundle (`Step2Iterate:1261-1289`) -/

/-- Both charges of the one-loop error have the same modulus: from `𝒦^{(1)} = m(σ)` and `𝓛^{(1)}_- = conj 𝓛^{(1)}_+` (the facts
of `Step2IterGen_OneLoop`), `|𝓛^{(1)}_{σ,a} - 𝒦^{(1)}_{σ,a}| = |𝓛^{(1)}_{+,a₀} - m|` (band `ST_avg_pointwise`, `Step2Iterate.lean:1247`). -/
private theorem Step2IterGen2_avg_pointwise {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (u : ℝ)
    (σ : Fin 1 → Bool) (a : Fin 1 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hK : ∀ (b : Bool) (x : Zd d (sz.L n)), C.K n u (fun _ : Fin 1 => b) (fun _ => x) =
      if b then C.m n else (starRingEnd ℂ) (C.m n))
    (hL : C.L n u (fun _ : Fin 1 => false) (fun _ => a 0) ω =
      (starRingEnd ℂ) (C.L n u (fun _ : Fin 1 => true) (fun _ => a 0) ω)) :
    ‖C.L n u σ a ω - C.K n u σ a‖ = ‖C.L n u (fun _ : Fin 1 => true) (fun _ => a 0) ω - C.m n‖ := by
  obtain ⟨b, rfl⟩ : ∃ b, σ = fun _ => b := ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨x, rfl⟩ : ∃ x, a = fun _ => x := ⟨a 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  rw [hK b x]
  cases b
  · rw [hL]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← map_sub, Complex.norm_conj]
  · simp

/-- **`STAvgUgL` from `STStep2AvggL`** (band `ST_avgU_of_avg`, `Step2Iterate.lean:1261`; both charges): the single-charge averaged law
gives the uniform law of both charges, under the one-loop facts (`Step2IterGen_OneLoop`) and the window `0 ≤ s_n`, `t_n < 1`.  The
hypothesis is the unfolded `STStep2AvggL C μ s t` (its `PrecL` statement, `Iff.rfl`), so that no premise outside the registry enters
the signature (premise scan). -/
theorem ST_avgU_of_avgg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ}
    (hOne : Step2IterGen_OneLoop C) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (h : PrecL sz μ (U := fun n => TimeIcc s t n × Zd d (sz.L n))
      (fun n p ω => ‖C.L n (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - C.m n‖)
      (fun n p _ => sz.Bctl n (p.1 : ℝ))) : STAvgUgL C μ s t := by
  refine Step2EventsGen_prec_dom μ h ?_
  filter_upwards [hOne.1] with n hn p
  refine ⟨(p.1, p.2.2 0), fun ω => ?_, fun ω => by simp⟩
  exact (Step2IterGen2_avg_pointwise C n (p.1 : ℝ) p.2.1 p.2.2 ω
    (fun b x => hn (p.1 : ℝ) ((hs0 n).trans p.1.2.1) (lt_of_le_of_lt p.1.2.2 (ht1 n)) b x)
    (hOne.2 n (p.1 : ℝ) (p.2.2 0) ω)).le

/-- **The conclusions of `STStep2` imply the bundle `STStep2ConclgL`** (band `ST_concl_of_step2`, `Step2Iterate.lean:1273`; the same `C_d`).
The hypotheses are the unfolded `STStep2LocalgL` (`= STLocalEntryUgL`), `STStep2AvggL` (its `PrecL` statement) and `STStep2DecaygL`
(`= STGdecayWgL`), all `Iff.rfl` (premise scan, as `ST_avgU_of_avgg`). -/
theorem ST_concl_of_step2g {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ} {Cd : ℝ}
    (hL : STLocalEntryUgL C μ s t)
    (hA : PrecL sz μ (U := fun n => TimeIcc s t n × Zd d (sz.L n))
      (fun n p ω => ‖C.L n (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - C.m n‖)
      (fun n p _ => sz.Bctl n (p.1 : ℝ)))
    (hD : STGdecayWgL C μ s t Cd)
    (hOne : Step2IterGen_OneLoop C) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) : STStep2ConclgL C μ s t Cd :=
  ⟨hL, ST_avgU_of_avgg C μ hOne hs0 ht1 hA, hD⟩

/-! ## 6. Target 6: the skeleton `ST_step2_of_pinsg` (`Step2Iterate:1393`) -/

/-! ## 7. Band readings of the pins and the band re-derivation of the skeleton -/

/-! ## 8. Compiled nonempty instances (targets 4-6; CLAUDE.md §4 step 2)

Data as in `Chain/Step2IterGen.lean` §4: the band carrier `bandFM sz0 (STflowE z0)` (`d = 3`), the law `seqP sz0`, the window `[0, 1/16]`, the
scale family `Kseq0` (`stScaleExists_holds`), `C_d = 3 · 1 + 1`.  Deterministic hypotheses are discharged with the merged instance data of
`Induction/Step2Iterate.lean` (`hK2_sz0`, `hq_sz0`, `Kseq0_adm`, ...); what stays a hypothesis is a pin of another gate or a stochastic
premise (`STSelfImpgL`, `STScaleInvgL`, the conclusions of Step 1, `STLWTgL`, `STEMn2ExpgL`, `STGridMartgL`, `STOptL2gL`,
`STLocalAvgOfL2gL`). -/

end RBM.BA

end
