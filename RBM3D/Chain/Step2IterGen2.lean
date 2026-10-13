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

/-- **Step 2 of `lem:main_ind` from its pinned ingredients, over a carrier family** (band `ST_step2_of_pins`, `Step2Iterate.lean:1393`;
`3_5:345–609`), conclusion `STStep2G d law Flow (fun sz z => (mk sz z).toFlowFM) T0`.  Carrier facts: F1-F2 (`Step2EventsGen_Flow`), F3
(`DecayGen_Spec`, family form), F9 (`Step2EventsGen_Grid`), the Hermitian walk (inline), the one-loop facts (`Step2IterGen_OneLoop`).
Pins: the light-weight lemmas `STLWTgL`; the martingale estimate `STEMn2ExpgL` (the `Ĵ` form); `lem:newKLK` (`Step2IterGen_NewKLK`); `Sol_CalL`
+ `lem:DIfREP` for the loop length 2 (`STGridMartgL`, the only grid premise); the deterministic `𝒦^{(2)}` decay (`Step2IterGen_K2`); the
scale family `STScaleExistsgL`; the base `STOptL2gL`; the closing paragraph `STLocalAvgOfL2gL`; the net lift `STNetLift2gL`; the size data
`STBdatagL` (replacing `ST_Bdata_holds`).  Constants: `C_d = 3C + 1`, `𝔠_d = min(1/100, 1/(60 C_d), 𝔠₀)`. -/
theorem ST_step2_of_pinsg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hFl : Step2EventsGen_Flow d Flow T0)
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz))
    (hSpec : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm)
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian)
    (hOne : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2IterGen_OneLoop (mk sz z).toFlowFM)
    (hBdata : STBdatagL d Flow T0)
    (hLWT : STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hEMe : STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hNew : Step2IterGen_NewKLK d Flow mk)
    (hMart : STGridMartgL d Flow mk T0)
    (hK2 : Step2IterGen_K2 d Flow mk)
    (hNet : STNetLift2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hScale : STScaleExistsgL d Flow T0)
    (hOpt : STOptL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hClos : STLocalAvgOfL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0) :
    STStep2G d law Flow (fun sz z => (mk sz z).toFlowFM) T0 := by
  intro hd3 κ ε 𝔡 hκ hε h𝔡
  have hd : 0 < d := by omega
  obtain ⟨C, δ₀, hC, hδ₀, hnew⟩ := hNew hd3 κ 𝔡 hκ h𝔡
  obtain ⟨κm, hκm⟩ := hSpec κ hκ
  obtain ⟨cB, hcB, hBc⟩ := hBdata κ ε 𝔡 hκ hε h𝔡
  obtain ⟨𝔠₀, h𝔠₀, hOptat⟩ := hOpt κ ε 𝔡 hκ hε h𝔡
  have hCd : 0 < 3 * C + 1 := by positivity
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min (min (1 / 100) (1 / (60 * (3 * C + 1)))) 𝔠₀ :=
    ⟨_, rfl⟩
  have h𝔠dpos : 0 < 𝔠d := by
    rw [h𝔠d]; exact lt_min (lt_min (by norm_num) (by positivity)) h𝔠₀
  have h𝔠d1 : 𝔠d ≤ 1 / 100 := by
    rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_left _ _)
  have h𝔠d3 : 𝔠d ≤ 𝔠₀ := by rw [h𝔠d]; exact min_le_right _ _
  have h𝔠d2 : (3 * C + 1) * 𝔠d ≤ 1 / 60 := by
    have h : 𝔠d ≤ 1 / (60 * (3 * C + 1)) := by
      rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_right _ _)
    calc (3 * C + 1) * 𝔠d ≤ (3 * C + 1) * (1 / (60 * (3 * C + 1))) :=
          mul_le_mul_of_nonneg_left h hCd.le
      _ = 1 / 60 := by field_simp
  refine ⟨3 * C + 1, hCd, 𝔠d, h𝔠dpos, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hsl hst htT hLK hDec hCon hS1L hS1W
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hadm := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hband : sz.Bandwidth 𝔠 := hadm.2.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨c, hc, hBc'⟩ := hBc 𝔠
  have hBd := hBc' sz z hflow t (fun n => (hs n).trans (hst' n)) htT
  -- the deterministic `𝒦^{(2)}` bound, eventually
  obtain ⟨C_K, hCK, hK2e⟩ := hK2 hd3 κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow s t hs ht1
  -- the closure arithmetic `r^{C_d} b^{1/5} ≤ b^{1/6}`
  have hq := ST_hq_of_data sz hsz hs hst' ht1 hC h𝔠dpos h𝔠d2 hBd hc hCon
  -- the base of the iteration and the scale family
  have hbase0 := hOptat 𝔠d h𝔠dpos h𝔠d3 𝔠 sz z hflow s t hs hst' htT hLK hCon hS1L hS1W
  have hbase : STScaleInvgL (mk sz z).toFlowFM (law sz) s t (fun n u => 0) :=
    ST_base_invg (mk sz z).toFlowFM (law sz) hsz hst' hCK hK2e hbase0
  obtain ⟨Kseq, hAdm⟩ := hScale κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT
  have hKz : Kseq 0 = fun n u => 0 := funext fun n => funext fun u => hAdm.1 n u
  have hbase' : STScaleInvgL (mk sz z).toFlowFM (law sz) s t (Kseq 0) := by rw [hKz]; exact hbase
  -- one self-improving step at every level
  have hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
      STSelfImpgL (mk sz z).toFlowFM (law sz) (3 * C + 1) s t Kf := fun Kf hKok hinv =>
    ST_selfImproveg d law Flow mk T0 hFl hLWT hEMe hd hκ hε h𝔡 hflow (hκm sz ε 𝔠 𝔡 z hflow) (hGrid sz z)
      (hHerm sz z) hs hst' htT hC hδ₀ (hnew ε 𝔠 sz z hflow) hMart h𝔠dpos h𝔠d2 hDec hCon hS1W hcB hc hBd
      Kf hKok hinv
  have hdec := ST_decay_ptg (mk sz z).toFlowFM (law sz) hsz hst' hCK hSelf hK2e hq Kseq hAdm hbase'
  have hL2 := ST_L2_decay_ptg (mk sz z).toFlowFM (law sz) hsz hst' hs ht1 hCK h𝔠 hband hdec hK2e hq
  obtain ⟨hLocPT, hAvgPT⟩ := hClos κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT hS1W hL2
  obtain ⟨hl, ha, hd'⟩ := hNet κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT (3 * C + 1) hLocPT hAvgPT hdec
  exact ST_concl_of_step2g _ _ hl ha hd' (hOne sz z) hs ht1

/-! ## 7. Band readings of the pins and the band re-derivation of the skeleton -/

/-- **Band reading of `STBdatagL`** (concluded head for the premise scan): the size data of `ST_Bdata_holds` (`Step2Iterate.lean:1049`),
`Iff.rfl` through `bandFM_STBdata`. -/
theorem stBdatagL_band (d : ℕ) (hd : 0 < d) :
    STBdatagL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n)) :=
  (bandFM_STBdata d).1 (ST_Bdata_holds hd)

/-- **Band reading of `STScaleExistsgL`** (concluded head for the premise scan): `stScaleExists_holds` (`Induction/Step2Scale.lean:430`),
`Iff.rfl` through `bandFM_STScaleExists`. -/
theorem stScaleExistsgL_band (d : ℕ) :
    STScaleExistsgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n)) :=
  (bandFM_STScaleExists d).1 (stScaleExists_holds d)

/-- **The band skeleton re-derived from `ST_step2_of_pinsg`** (the statement of `ST_step2_of_pins'`, `Step2Iterate.lean:1779`, without the
pins that are proved: `STNewKLK` by `stNewKLK_holds` through `step2IterGen_newKLK_band`).  The generic inputs are discharged by the
merged band producers: F1-F2 `Step2EventsGen_bandFlow`, F3 `DecayGen_bandSpec`, F9 `Step2EventsGen_bandGrid`, the Hermitian walk
`pathH_isHermitian`, the one-loop facts `step2IterGen_oneLoop_band`, the size data `stBdatagL_band`, `Step2IterGen_NewKLK` and
`Step2IterGen_K2` by their band discharges, and `STNetLift2gL`, `STScaleExistsgL` by `stNetLift2_holds`, `stScaleExists_holds`; the
remaining pins go through `STStep2_iff` and `bandStep2_STGridMart`, `bandFM_STLWT`, `bandFM_STEMn2Exp`, `bandFM_STOptL2`,
`bandFM_STLocalAvgOfL2`. -/
theorem step2IterGen_step2_of_pins_band (d : ℕ) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hMart : STGridMart d)
    (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d := by
  intro hd3
  have hd : 0 < d := by omega
  exact (STStep2_iff d).2 (ST_step2_of_pinsg d (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))
    (Step2EventsGen_bandFlow d) (fun sz z => Step2EventsGen_bandGrid sz (STflowE z))
    (fun κ hκ => ⟨Real.sqrt κ / 2, fun sz ε 𝔠 𝔡 z hflow =>
      DecayGen_bandSpec sz hκ fun n => (abs_lemE_le (ST_flow_im_pos sz hflow n)).trans (hflow.2 n).1⟩)
    (fun sz z s t K n k ω => pathH_isHermitian sz s t K n k ω)
    (fun sz z => step2IterGen_oneLoop_band sz (STflowE z)) (stBdatagL_band d hd)
    ((bandFM_STLWT d).1 hLWT) ((bandFM_STEMn2Exp d).1 hEMe) (step2IterGen_newKLK_band d)
    (bandStep2_STGridMart.1 hMart) (step2IterGen_K2_band d) ((bandFM_STNetLift2 d).1 (stNetLift2_holds d))
    (stScaleExistsgL_band d) ((bandFM_STOptL2 d).1 hOpt) ((bandFM_STLocalAvgOfL2 d).1 hClos)) hd3

/-! ## 8. Compiled nonempty instances (targets 4-6; CLAUDE.md §4 step 2)

Data as in `Chain/Step2IterGen.lean` §4: the band carrier `bandFM sz0 (STflowE z0)` (`d = 3`), the law `seqP sz0`, the window `[0, 1/16]`, the
scale family `Kseq0` (`stScaleExists_holds`), `C_d = 3 · 1 + 1`.  Deterministic hypotheses are discharged with the merged instance data of
`Induction/Step2Iterate.lean` (`hK2_sz0`, `hq_sz0`, `Kseq0_adm`, ...); what stays a hypothesis is a pin of another gate or a stochastic
premise (`STSelfImpgL`, `STScaleInvgL`, the conclusions of Step 1, `STLWTgL`, `STEMn2ExpgL`, `STGridMartgL`, `STOptL2gL`,
`STLocalAvgOfL2gL`). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step2DefsInst RBM.Gauss.Step2IterateInst

/-- **Target 4, `ST_iterateg`** at the band carrier -/
example (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz0 sInst tInst Kf →
      STScaleInvgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Kf →
      STSelfImpgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (3 * 1 + 1) sInst tInst Kf)
    (hbase : STScaleInvgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst (Kseq0 0)) :
    ∀ m, STScaleInvgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst (Kseq0 m) ∧
      STSelfImpgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (3 * 1 + 1) sInst tInst (Kseq0 m) :=
  ST_iterateg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sz0_tendsto hst CK0_pos hSelf hK2_sz0 hq_sz0 Kseq0
    Kseq0_adm hbase

example (hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz0 sInst tInst Kf →
      STScaleInvgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Kf →
      STSelfImpgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (3 * 1 + 1) sInst tInst Kf)
    (hbase : STScaleInvgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst (Kseq0 0)) :
    STStep2DecayPTgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (3 * 1 + 1) sInst tInst :=
  ST_decay_ptg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sz0_tendsto hst CK0_pos hSelf hK2_sz0 hq_sz0 Kseq0
    Kseq0_adm hbase

example (hdec : STStep2DecayPTgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (3 * 1 + 1) sInst tInst) :
    STL2decayPTgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  ST_L2_decay_ptg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sz0_tendsto hst hs0 ht1 CK0_pos (𝔠 := 1 / 6)
    (by norm_num) sz0_bandwidth hdec hK2_sz0 hq_sz0

example (hOpt : PrecPTL sz0 (Sizes.seqP sz0)
      (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖(bandFM sz0 (STflowE z0)).L n (p.1 : ℝ) p.2.1 p.2.2 ω -
        (bandFM sz0 (STflowE z0)).K n (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => sz0.Bctl n (p.1 : ℝ))) :
    STScaleInvgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst (fun n u => 0) :=
  ST_base_invg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sz0_tendsto hst CK0_pos hK2_sz0 hOpt

/-- **Target 5** -/
example (h : STStep2AvggL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) :
    STAvgUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  ST_avgU_of_avgg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (step2IterGen_oneLoop_band sz0 (STflowE z0)) hs0 ht1 h

example {Cd : ℝ} (hL : STStep2LocalgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hA : STStep2AvggL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hD : STStep2DecaygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) Cd sInst tInst) :
    STStep2ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd :=
  ST_concl_of_step2g (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) hL hA hD
    (step2IterGen_oneLoop_band sz0 (STflowE z0)) hs0 ht1


/-- The conclusion `STStep2G` of the skeleton at the band carrier, specialised to the data `(sz0, z0, s ≡ 0, t ≡ 1/16)`
(as `inst_step2`, `Induction/Step2Defs.lean:880`): the constants `C_d`, `𝔠_d`, then `(con_st_ind)`; the premises `STLKgL`, `STDecaygL`
at `s` and Step 1's conclusions stay hypotheses. -/
private theorem Step2IterGen2_inst_step2
    (h : STStep2G 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n))) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst →
        STDecaygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst →
        STStep1LoopgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst →
        STStep1WeakgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst →
        STStep2ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd) := by
  obtain ⟨Cd, hCd, 𝔠d, h0, h1, hall⟩ :=
    h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cd, hCd, 𝔠d, h0, h1, fun hLK hDec hS1L hS1W => ?_⟩
  exact hall (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl) (fun n => zero_le_lemT n)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hLK hDec
    (conStInd_inst h0) hS1L hS1W

/-- **Target 6, `ST_step2_of_pinsg`** at the band carrier family `(seqP, STFlow, bandStep2Mat sz (STflowE z), lemT)`, `d = 3`, specialised
to `(sz0, z0, s ≡ 0, t ≡ 1/16)`.  Discharged: F1-F2, F3, F9, the Hermitian walk, the one-loop facts, the size data (`stBdatagL_band`),
the classes `Step2IterGen_NewKLK`, `Step2IterGen_K2` (band discharges), `STNetLift2gL` (`stNetLift2_holds`), `STScaleExistsgL`.  The
pins `STLWTgL`, `STEMn2ExpgL`, `STGridMartgL`, `STOptL2gL`, `STLocalAvgOfL2gL` stay hypotheses (stage L, other rows). -/
example (hLWT : bandPin STLWTgL 3) (hEMe : bandPin STEMn2ExpgL 3)
    (hMart : STGridMartgL 3 (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
      (fun _ z n => lemT (z n)))
    (hOpt : bandPin STOptL2gL 3) (hClos : bandPin STLocalAvgOfL2gL 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst →
        STDecaygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst →
        STStep1LoopgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst →
        STStep1WeakgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst →
        STStep2ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd) :=
  Step2IterGen2_inst_step2 (ST_step2_of_pinsg 3 (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))
    (Step2EventsGen_bandFlow 3) (fun sz z => Step2EventsGen_bandGrid sz (STflowE z))
    (fun κ hκ => ⟨Real.sqrt κ / 2, fun sz ε 𝔠 𝔡 z hflow =>
      DecayGen_bandSpec sz hκ fun n => (abs_lemE_le (ST_flow_im_pos sz hflow n)).trans (hflow.2 n).1⟩)
    (fun sz z s t K n k ω => pathH_isHermitian sz s t K n k ω)
    (fun sz z => step2IterGen_oneLoop_band sz (STflowE z)) (stBdatagL_band 3 (by norm_num))
    hLWT hEMe (step2IterGen_newKLK_band 3) hMart (step2IterGen_K2_band 3)
    ((bandFM_STNetLift2 3).1 (stNetLift2_holds 3)) (stScaleExistsgL_band 3) hOpt hClos)

/-- **The band re-derivation** (`step2IterGen_step2_of_pins_band`) at `d = 3`: the five remaining band pins are hypotheses. -/
example (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3) (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (step2IterGen_step2_of_pins_band 3 hLWT hEMe hMart hOpt hClos)

/-- **Band re-derivations of target 4**: the statements of `ST_iterate`, `ST_decay_pt`, `ST_L2_decay_pt`, `ST_base_inv`
(`Induction/Step2Iterate.lean:725, 752, 924, 1316`) from the generic results at `bandFM sz E`, law `seqP sz`. -/
example : type_of% @RBM.Gauss.Sizes.ST_iterate := by
  intro d sz E s t Cd C_K hsz hst hCK hSelf hK2 hq Kseq hAdm hbase
  exact ST_iterateg (bandFM sz E) (Sizes.seqP sz) hsz hst hCK hSelf hK2 hq Kseq hAdm hbase

example : type_of% @RBM.Gauss.Sizes.ST_decay_pt := by
  intro d sz E s t Cd C_K hsz hst hCK hSelf hK2 hq Kseq hAdm hbase
  exact ST_decay_ptg (bandFM sz E) (Sizes.seqP sz) hsz hst hCK hSelf hK2 hq Kseq hAdm hbase

example : type_of% @RBM.Gauss.Sizes.ST_L2_decay_pt := by
  intro d sz E s t Cd C_K hsz hst hs0 ht1 hCK 𝔠 h𝔠 hband hdec hK2 hq
  exact ST_L2_decay_ptg (bandFM sz E) (Sizes.seqP sz) hsz hst hs0 ht1 hCK h𝔠 hband hdec hK2 hq

example : type_of% @RBM.Gauss.Sizes.ST_base_inv := by
  intro d sz E s t hsz hst C_K hCK hK2 hOpt
  exact ST_base_invg (bandFM sz E) (Sizes.seqP sz) hsz hst hCK hK2 hOpt

end Instances

end RBM.BA

end
