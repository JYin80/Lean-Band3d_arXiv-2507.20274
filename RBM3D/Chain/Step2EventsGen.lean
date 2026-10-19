/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Core
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.LWGen
import RBM3D.Chain.DecayGen

/-!
# The Step 2 events over the flow carrier

The band files `Induction/Step2Events`, `Induction/Step2Core` restated over a carrier `Cm : Step2Mat sz`
(and `C : FlowFM sz`) and a law `μ`, with bridges to the band.  There is no `BA/` import (the block
Anderson side is `Chain/Step2EventsGenTw`) and nothing downstream of `Induction/Step2Iterate`.

* **Carrier facts (hypothesis predicates, not fields).**  `Step2EventsGen_Flow` (the flow setting
  contains `Admissible`; `T0 < 1`), `Step2EventsGen_Rot3` (trace cyclicity of the 3-loop; proved
  generically for a fine matrix as `Step2EventsGen_loopFine_rot3`), `Step2EventsGen_Grid` (a model matrix
  `Hm` with `LM`, `GMM` reading `L`, `G - M`, both measurable in the matrix, and the law of the grid
  state).  The spectral data is `DecayGen_Spec` (`Chain/DecayGen`).
* **The statements** `STScaleInvgL`, `ST_LW_sectionsg`; the event sets `STEvWeakg`, `STEvInitg`, `STEvLWg`,
  `STEvMGg` and the events `ST_event_weakg`, `ST_event_initg`, `ST_event_lwg`, `ST_event_mgg`;
  `STGoodAtg` and `ST_good_probg`; `STBdatagL` and the generic L-bridges `stLWBgL_of_LWtermG`,
  `stLWTgL_of_LWtermExpG`.
* **Generic helpers** of the band helpers that name `sz.Prec`, `pathP`, `seqHflow`
  (`Step2EventsGen_prec_*`, `Step2EventsGen_PT_of_sections`, `Step2EventsGen_sections_of_PT`,
  `Step2EventsGen_whp_grid`, `Step2EventsGen_grid_whp_of_sections`, `Step2EventsGen_grid_whp_zero`,
  `Step2EventsGen_model_le_path`, the matrix-level measurability and readings under
  `Step2EventsGen_Grid`).
* **Band readings** `bandFM_STBdata` (`Iff.rfl`),
  `Step2EventsGen_bandLaw`, `Step2EventsGen_bandGrid`.

Opened private names of `Induction/Step2Events` (`open private`): `STB_trace_six` (trace cyclicity of six
matrices), `STB_eps_le` (`ε₀ ≤ d/2` from `STPsiClass`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false

open private STB_trace_six STB_eps_le from RBM3D.Induction.Step2Events

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The carrier facts `Step2EventsGen_Flow`, `Step2EventsGen_Rot3`, `Step2EventsGen_Grid` -/

/-- **`Step2EventsGen_Flow`** in family shape (the fields `flowOK_adm`, `flowOK_T` of `Step2Data`): the flow setting contains the admissibility of the sizes;
`T0 < 1`. -/
def Step2EventsGen_Flow (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  (∀ sz κ ε 𝔠 𝔡 z, Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡) ∧
    (∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, T0 sz z n < 1)

/-- **`Step2EventsGen_Rot3`**: trace cyclicity of the 3-loop (band `STB_loop_rot`, private). -/
def Step2EventsGen_Rot3 {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (t : ℝ) (σ₀ σ₁ : Bool) (a₀ y a₁ : Zd d (sz.L n)) (ω : sz.SeqΩ),
    C.L n t ![σ₀, σ₁, σ₁] ![a₀, y, a₁] ω = C.L n t ![σ₁, σ₁, σ₀] ![y, a₁, a₀] ω

/-- **`Step2EventsGen_Grid`**: a model matrix `Hm` (band `seqHflow`) at which `LM`, `GMM` read `L`, `G - M`; `LM`, `GMM` measurable
in the matrix; and the law (`ST_pathP_eq_seqP`): the grid state at index `k` has the law of the model at the grid time. -/
def Step2EventsGen_Grid {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) : Prop :=
  ∃ Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
    (∀ n u ω x y, Cm.GMM n u (Hm n u ω) x y = Cm.GM n u ω x y) ∧
    (∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω) ∧
    (∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Measurable fun H => Cm.LM n u H σ a) ∧
    (∀ n u x y, Measurable fun H => Cm.GMM n u H x y) ∧
    ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), 0 ≤ s n → s n ≤ t n → K n ≠ 0 → ∀ S, MeasurableSet S →
      Cm.Pp {ω | Cm.Hpath s t K n k ω ∈ S} = μ {ω | Hm n (gridTime s t K n k) ω ∈ S}

/-- The last conjunct of `Step2EventsGen_Grid`: the law of the grid state at index `k` against the model matrix `Hm` at the grid time. -/
def Step2EventsGen_Law {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n)  (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), 0 ≤ s n → s n ≤ t n → K n ≠ 0 → ∀ S, MeasurableSet S →
    Cm.Pp {ω | Cm.Hpath s t K n k ω ∈ S} = μ {ω | Hm n (gridTime s t K n k) ω ∈ S}

/-! ## 2. Trace cyclicity of the 3-loop, for a fine matrix -/

/-- **Trace cyclicity of the 3-loop for a fine matrix** (band `STB_loop_rot`): `loopFine` of the 3-loop is invariant under
the cyclic rotation `(σ₀, σ₁, σ₁), (a₀, y, a₁) ↦ (σ₁, σ₁, σ₀), (y, a₁, a₀)` (cyclicity of the trace). -/
theorem Step2EventsGen_loopFine_rot3 {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (σ₀ σ₁ : Bool) (a₀ y a₁ : Zd d L) :
    loopFine d L W H z ![σ₀, σ₁, σ₁] ![a₀, y, a₁] = loopFine d L W H z ![σ₁, σ₁, σ₀] ![y, a₁, a₀] := by
  unfold loopFine loopM
  simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, List.ofFn_succ, Fin.isValue,
    Fin.cast_eq_self, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_assoc]
  exact (STB_trace_six _ _ _ _ _ _).symm

/-! ## 3. The transfer helpers over `PrecL` and `Cm.Pp` -/

section Helpers

variable {d : ℕ} {sz : Sizes d}

/-- Enlarging the bound pointwise (eventually in `n`, for all sample points) preserves `PrecL` (band `ST_prec_mono_eventually`). -/
theorem Step2EventsGen_prec_mono_eventually (μ : Measure sz.SeqΩ) {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) (h : PrecL sz μ ξ ζ) : PrecL sz μ ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hle] with n hn hle'
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨u, hu⟩
  exact ⟨u, lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hle' u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- Deterministic domination, eventually in `n`, implies `PrecL` (band `ST_prec_of_le_ev`). -/
theorem Step2EventsGen_prec_of_le_ev (μ : Measure sz.SeqΩ) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hle : ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ζ n u ω) : PrecL sz μ ξ ζ := by
  intro τ hτ D _
  filter_upwards [hle] with n hn
  have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
  have hempty : badSetAt (sz.size) ξ ζ τ n = ∅ := by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    nlinarith [hn u ω, hζ n u ω]
  rw [hempty, measure_empty]
  exact zero_le

/-- The supremum over a finite family of labels of a dominated family is dominated (band `ST_prec_sup`). -/
theorem Step2EventsGen_prec_sup (μ : Measure sz.SeqΩ) {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (ξ : ∀ n, V n → sz.SeqΩ → ℝ) (ζ : ℕ → ℝ) (h : PrecL sz μ (U := V) ξ (fun n _ _ => ζ n)) :
    PrecL sz μ (U := fun _ => Unit)
      (fun n _ ω => Finset.univ.sup' Finset.univ_nonempty (fun v : V n => ξ n v ω))
      (fun n _ _ => ζ n) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨_, hu⟩
  obtain ⟨v, -, hv⟩ := (Finset.lt_sup'_iff Finset.univ_nonempty).1 hu
  exact ⟨v, hv⟩

/-- Transport of `PrecL` along a pointwise domination of the families (eventually in `n`) (band `STB_prec_dom`, private). -/
theorem Step2EventsGen_prec_dom (μ : Measure sz.SeqΩ) {U U' : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    {ξ' ζ' : ∀ n, U' n → sz.SeqΩ → ℝ} (h : PrecL sz μ ξ ζ)
    (hdom : ∀ᶠ n in atTop, ∀ u' : U' n, ∃ u : U n, (∀ ω, ξ' n u' ω ≤ ξ n u ω) ∧
      ∀ ω, ζ n u ω ≤ ζ' n u' ω) : PrecL sz μ ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hdom] with n h1 hn
  refine le_trans (measure_mono ?_) h1
  intro ω hω
  obtain ⟨u', hu'⟩ := hω
  obtain ⟨u, h2, h3⟩ := hn u'
  refine ⟨u, ?_⟩
  have hr : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := mul_le_mul_of_nonneg_left (h3 ω) hr
  linarith [h2 ω]

/-- **Per-time `PrecPTL` from the single-time statements at every section** (band `ST_PT_of_sections`). -/
theorem Step2EventsGen_PT_of_sections (μ : Measure sz.SeqΩ) {V : ℕ → Type} [∀ n, Nonempty (V n)]
    {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ)
    (h : ∀ tt : ∀ n, TimeIcc s t n,
      PrecL sz μ (U := V) (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω)) :
    PrecPTL sz μ (U := fun n => TimeIcc s t n × V n) ξ ζ := by
  have hU : ∀ n, Nonempty (TimeIcc s t n × V n) := fun n =>
    ⟨(⟨s n, le_rfl, hst n⟩, Classical.arbitrary (V n))⟩
  refine (perTimeDomAt_iff_forall_section μ sz.size hU ξ ζ).mpr ?_
  intro p
  have h1 := h (fun n => (p n).1)
  have h2 := StochDomAt.precomp_param (V := fun _ => Unit) h1 (fun n _ => (p n).2)
  exact h2

/-- **The converse of `Step2EventsGen_PT_of_sections`** (band `ST_sections_of_PT`). -/
theorem Step2EventsGen_sections_of_PT (μ : Measure sz.SeqΩ) {V : ℕ → Type} [∀ n, Fintype (V n)] {s t : ℕ → ℝ}
    (ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (h : PrecPTL sz μ (U := fun n => TimeIcc s t n × V n) ξ ζ) (tt : ∀ n, TimeIcc s t n) :
    PrecL sz μ (U := V) (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω) := by
  refine stochDomAt_of_perTimeDomAt μ sz.size hC0 hC ?_
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn v
  exact hn (tt n, v)

/-- **From the model to the grid walk, under `Step2EventsGen_Grid`** (band `ST_whp_grid`).  If, for every `D > 0`,
eventually in `n`, every grid index `j ∈ J_n` and every label `v ∈ V_n` satisfy
`μ(N^τ Z(H^m_{u_j}) < F(H^m_{u_j})) ≤ N^{-D}` (`H^m` the model matrix of `Step2EventsGen_Grid`), then w.h.p. the grid walk satisfies
`F ≤ N^τ Z` at all `j ∈ J_n`, `v ∈ V_n` simultaneously. -/
theorem Step2EventsGen_whp_grid (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hlaw : Step2EventsGen_Law Cm μ Hm) {V : ℕ → Type} [∀ n, Fintype (V n)] (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hK : ∀ n, K n ≠ 0) (J : ℕ → Finset ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop,
      (((J n).card * Fintype.card (V n) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) (τ : ℝ)
    (h : ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ j ∈ J n, ∀ v : V n,
      μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ *
            Z n v (gridTime s t K n j) (Hm n (gridTime s t K n j) ω) <
          F n v (gridTime s t K n j) (Hm n (gridTime s t K n j) ω)} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ∈ J n, ∀ v : V n,
      F n v (gridTime s t K n j) (Cm.Hpath s t K n j ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s t K n j) (Cm.Hpath s t K n j ω)}) := by
  have hmain := highProbAt_iInter Cm.Pp sz.size (K := fun n => ↥(J n) × V n)
    (Ξ := fun n p => {ω | F n p.2 (gridTime s t K n p.1) (Cm.Hpath s t K n p.1 ω) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * Z n p.2 (gridTime s t K n p.1) (Cm.Hpath s t K n p.1 ω)})
    hC0 (by
      filter_upwards [hcard] with n hn
      simpa [Fintype.card_prod, Fintype.card_coe] using hn) (by
      intro D hD
      filter_upwards [h D hD] with n hn p
      have hS : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
          ((sz.size n : ℕ) : ℝ) ^ τ * Z n p.2 (gridTime s t K n p.1) H <
            F n p.2 (gridTime s t K n p.1) H} :=
        measurableSet_lt (measurable_const.mul (hZ _ _ _)) (hF _ _ _)
      have hc : {ω : PathΩ sz | F n p.2 (gridTime s t K n p.1) (Cm.Hpath s t K n p.1 ω) ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * Z n p.2 (gridTime s t K n p.1) (Cm.Hpath s t K n p.1 ω)}ᶜ =
          {ω | Cm.Hpath s t K n p.1 ω ∈ {H : Matrix (Idx d (sz.L n) (sz.W n))
            (Idx d (sz.L n) (sz.W n)) ℂ | ((sz.size n : ℕ) : ℝ) ^ τ *
              Z n p.2 (gridTime s t K n p.1) H < F n p.2 (gridTime s t K n p.1) H}} := by
        ext ω; simp [not_le]
      rw [hc, hlaw s t K n p.1 (hs n) (hst n) (hK n) _ hS]
      exact hn p.1 p.1.2 p.2)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj v
  exact Set.mem_iInter.mp hω (⟨j, hj⟩, v)

/-- **From single-time statements at every time section to the grid walk, under `Step2EventsGen_Grid`** (band `ST_grid_whp_of_sections`; Subsection 3.3, `subsec:step2_pf`).  If, for every time section `tt n ∈ [s_n, t_n]`, the labelled family
`F ≺ Z` holds for the single-time model at `tt`, and `K_n · #labels ≤ N^C`, then for every `τ > 0` w.h.p. the grid walk
satisfies `F ≤ N^τ Z` at all grid indices `j ≤ K_n` and all labels simultaneously. -/
theorem Step2EventsGen_grid_whp_of_sections (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hlaw : Step2EventsGen_Law Cm μ Hm) {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hK : ∀ n, K n ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop,
      ((((K n + 1) * Fintype.card (V n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) (τ : ℝ) (hτ : 0 < τ)
    (h : ∀ tt : ∀ n, TimeIcc s t n,
      PrecL sz μ (U := V) (fun n v ω => F n v (tt n : ℝ) (Hm n (tt n : ℝ) ω))
        (fun n v ω => Z n v (tt n : ℝ) (Hm n (tt n : ℝ) ω))) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ∈ Finset.range (K n + 1), ∀ v : V n,
      F n v (gridTime s t K n j) (Cm.Hpath s t K n j ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s t K n j) (Cm.Hpath s t K n j ω)}) := by
  have hPT := Step2EventsGen_PT_of_sections μ (V := V) hst
    (fun n p ω => F n p.2 (p.1 : ℝ) (Hm n (p.1 : ℝ) ω))
    (fun n p ω => Z n p.2 (p.1 : ℝ) (Hm n (p.1 : ℝ) ω)) h
  refine Step2EventsGen_whp_grid Cm μ hlaw s t K hs hst hK (fun n => Finset.range (K n + 1)) hC0 ?_ F Z hF hZ τ ?_
  · filter_upwards [hcard] with n hn
    simpa using hn
  · intro D hD
    filter_upwards [hPT τ hτ D hD] with n hn j hj v
    exact hn (⟨gridTime s t K n j, ST_gridTime_mem s t K n j (hst n) (hK n)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))⟩, v)

/-- **A single-time statement at the initial time `s_n` gives the grid walk at the index `0`, under `Step2EventsGen_Grid`** (band
`ST_grid_whp_zero`). -/
theorem Step2EventsGen_grid_whp_zero (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hlaw : Step2EventsGen_Law Cm μ Hm) {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hK : ∀ n, K n ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) (τ : ℝ) (hτ : 0 < τ)
    (h : PrecL sz μ (U := V) (fun n v ω => F n v (s n) (Hm n (s n) ω))
        (fun n v ω => Z n v (s n) (Hm n (s n) ω))) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ v : V n,
      F n v (gridTime s t K n 0) (Cm.Hpath s t K n 0 ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s t K n 0) (Cm.Hpath s t K n 0 ω)}) := by
  have hmain := Step2EventsGen_whp_grid Cm μ hlaw s t K hs hst hK (fun _ => {0}) hC0 (by
      filter_upwards [hcard] with n hn
      simpa using hn) F Z hF hZ τ (by
      intro D hD
      filter_upwards [h τ hτ D hD] with n hn j hj v
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have hg : gridTime s t K n 0 = s n := by simp [gridTime]
      rw [hg]
      refine le_trans (measure_mono ?_) hn
      intro ω hω
      exact ⟨v, hω⟩)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω v
  exact hω 0 (by simp) v

/-- **From the grid endpoint back to the model, under `Step2EventsGen_Grid`** (band `ST_model_le_path`): a single-`D`
form. -/
theorem Step2EventsGen_model_le_path (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hlaw : Step2EventsGen_Law Cm μ Hm) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (hK : ∀ n, K n ≠ 0) (n : ℕ)
    (F Z : ∀ n, ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n u, Measurable (F n u)) (hZ : ∀ n u, Measurable (Z n u)) (τ : ℝ)
    (Bad : Set (PathΩ sz))
    (hBad : {ω : PathΩ sz | ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (Cm.Hpath s t K n (K n) ω) <
      F n (t n) (Cm.Hpath s t K n (K n) ω)} ⊆ Bad) :
    μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (Hm n (t n) ω) < F n (t n) (Hm n (t n) ω)} ≤ Cm.Pp Bad := by
  have hS : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) H < F n (t n) H} :=
    measurableSet_lt (measurable_const.mul (hZ _ _)) (hF _ _)
  have hlast := gridTime_last s t K n (hK n)
  have hq := hlaw s t K n (K n) (hs n) (hst n) (hK n) _ hS
  rw [hlast] at hq
  exact le_trans (le_of_eq hq.symm) (measure_mono hBad)

/-- `3 + 3/Im m ≤ 3 + 3/κm` from `DecayGen_Spec` (band `ST_cstar_le`: `c₁ = 3 + 3/Im m` of the engine
`ST_good_engine`, with `Im m ≥ κm` from `DecayGen_Spec`). -/
theorem Step2EventsGen_cstar_le {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {κm : ℝ} (hS : DecayGen_Spec C κm) (n : ℕ) :
    3 + 3 * ((C.m n).im)⁻¹ ≤ 3 + 3 * κm⁻¹ := by
  have := inv_anti₀ hS.1 (hS.2.1 n)
  linarith

end Helpers

/-! ## 4. The matrix-level functionals under `Step2EventsGen_Grid`: measurability and the reading of the model-level objects -/

section MatrixFacts

variable {d : ℕ} {sz : Sizes d}

/-- `Step2EventsGen_Grid`, third clause: `H ↦ 𝓛^{(k)}_{u,σ,a}(H)` is measurable. -/
theorem Step2EventsGen_Grid.meas_LM {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ) (u : ℝ)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : Measurable fun H => Cm.LM n u H σ a := by
  obtain ⟨_, _, _, h, _, _⟩ := hG
  exact h n u k σ a

/-- `Step2EventsGen_Grid`, fourth clause: `H ↦ (G_u - M)_{xy}(H)` is measurable. -/
theorem Step2EventsGen_Grid.meas_GMM {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ) (u : ℝ)
    (x y : Idx d (sz.L n) (sz.W n)) : Measurable fun H => Cm.GMM n u H x y := by
  obtain ⟨_, _, _, _, h, _⟩ := hG
  exact h n u x y

theorem Step2EventsGen_STLMg_measurable {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ) (u : ℝ)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STLMg Cm n u H σ a :=
  hG.meas_LM n u σ a

theorem Step2EventsGen_STLKMg_measurable {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ) (u : ℝ)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STLKMg Cm n u H σ a :=
  (hG.meas_LM n u σ a).sub measurable_const

theorem Step2EventsGen_STGMMg_measurable {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ) (u : ℝ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STGMMg Cm n u H x y :=
  hG.meas_GMM n u x y

theorem Step2EventsGen_STJhatMg_measurable {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ)
    (u D ℓ : ℝ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STJhatMg Cm n D ℓ u H := by
  have hne : (Finset.univ : Finset ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))).Nonempty :=
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
  have h := Finset.measurable_sup' (s := Finset.univ) hne
    (f := fun (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
        ‖STLKMg Cm n u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))
    (fun p _ => ((Step2EventsGen_STLKMg_measurable hG n u p.1 p.2).norm).div_const _)
  convert h using 1
  funext H
  simp [STJhatMg, Finset.sup'_apply]

theorem Step2EventsGen_STEGtMg_measurable {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ)
    (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STEGtMg Cm n u H σ a := by
  unfold STEGtMg
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
  have hav : ∀ (s : Bool) (x : Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STavgMg Cm n u H s x := fun s x => (Step2EventsGen_STLMg_measurable hG n u _ _).sub measurable_const
  exact ((((hav _ x).mul measurable_const).mul (Step2EventsGen_STLMg_measurable hG n u _ _)).add
    (((hav _ x).mul measurable_const).mul (Step2EventsGen_STLMg_measurable hG n u _ _)))

theorem Step2EventsGen_STEEkMg_measurable {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ)
    (u : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STEEkMg Cm n u H k σ a := by
  unfold STEEkMg
  refine measurable_const.mul (Finset.measurable_sum _ fun c _ => Finset.measurable_sum _ fun c' _ => ?_)
  refine measurable_const.mul ?_
  by_cases hk : k = 0
  · simp only [hk, ite_true]; exact Step2EventsGen_STLMg_measurable hG n u _ _
  · simp only [hk, ite_false]; exact Step2EventsGen_STLMg_measurable hG n u _ _

variable (Cm : Step2Mat sz)
  {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω)
include hLM

/-- The matrix-level `STEGtMg` at the model matrix `Hm` is the model-level `STEGtg` (`Step2EventsGen_Grid`, second clause). -/
theorem Step2EventsGen_STEGtMg_eq (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STEGtMg Cm n u (Hm n u ω) σ a = STEGtg Cm.toFlowFM n u σ a ω := by
  unfold STEGtMg STEGtg STavgMg STLMg STmsigg
  simp only [hLM]

/-- `STEEkMg` at the model matrix is `STEEg`. -/
theorem Step2EventsGen_STEEkMg_eq (n : ℕ) (u : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STEEkMg Cm n u (Hm n u ω) k σ a = STEEg Cm.toFlowFM n u k σ a ω := by
  unfold STEEkMg STEEg STLMg
  simp only [hLM]

/-- `STJhatMg` at the model matrix is `STJhatg`. -/
theorem Step2EventsGen_STJhatMg_eq (n : ℕ) (D ℓ u : ℝ) (ω : sz.SeqΩ) :
    STJhatMg Cm n D ℓ u (Hm n u ω) = STJhatg Cm.toFlowFM n D ℓ u ω := by
  unfold STJhatMg STJhatg STLKMg STLMg
  simp only [hLM]

/-- `STLKMg` at the model matrix is `𝓛 - 𝒦`. -/
theorem Step2EventsGen_STLKMg_eq (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STLKMg Cm n u (Hm n u ω) σ a = Cm.L n u σ a ω - Cm.K n u σ a := by
  unfold STLKMg STLMg
  simp only [hLM]

end MatrixFacts

/-! ## 5. `STScaleInvgL` and `ST_LW_sectionsg` -/

/-- **`STScaleInvgL`** (`Inv(Kf)`, (3.31) `eq:LW_assm_exp` at the scale family at every time section; band `STScaleInv`).  Definitional at `bandFM`. -/
def STScaleInvgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  ∀ (tt : ∀ n, TimeIcc s t n) (D : ℝ), 0 < D → STLWassmExpgL C μ (fun n => (tt n : ℝ)) D (fun n => Kf n (tt n : ℝ))

/-- **`ST_LW_sectionsg`** (band `ST_LW_sections`): at every time section `tt n ∈ [s_n, t_n]` the
hypotheses of `STLWTgL`, `STEMn2ExpgL` hold ((3.4) `initialGT2` from the weak law of Step 1 and (3.31) `eq:LW_assm_exp` at the scale family)
and their conclusions are returned.  The flow enters through `Step2EventsGen_Flow` (`Admissible`, `T0 < 1`) only. -/
theorem ST_LW_sectionsg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
  Step2EventsGen_Flow d Flow T0 → STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  0 < d → ∀ (sz : Sizes d) (κ ε 𝔡 𝔠 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z →
  ∀ (s t : ℕ → ℝ) (cB c : ℝ) (Kf : ℕ → ℝ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, t n ≤ T0 sz z n) → STStep1WeakgL (mk sz z).toFlowFM (law sz) s t → 0 < cB → 0 < c →
    (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ Kf n u ∧ Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) →
    STScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
    ∀ tt : ∀ n, TimeIcc s t n,
      (∀ D : ℝ, 0 < D → PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEGtg (mk sz z).toFlowFM n (tt n : ℝ) p.1 p.2 ω‖)
        (fun n p _ => ((mk sz z).eta n (tt n : ℝ))⁻¹ * (sz.Bctl n (tt n : ℝ)) ^ (1 / 2 : ℝ) *
          STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1))) ∧
      (∀ D : ℝ, 0 < D → PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEEg (mk sz z).toFlowFM n (tt n : ℝ) p.1 p.2.1 p.2.2 ω‖)
        (fun n p ω => ((mk sz z).eta n (tt n : ℝ))⁻¹ * ((sz.Bctl n (tt n : ℝ)) ^ (1 / 2 : ℝ) +
          (STJhatg (mk sz z).toFlowFM n D (Kf n (tt n : ℝ)) (tt n : ℝ) ω) ^ 3) *
          (STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2.2 0) (p.2.2 1)) ^ 2)) := by
  classical
  intro hFl hLWT hEMe hd sz κ ε 𝔡 𝔠 z hκ hε h𝔡 hflow s t cB c Kf hs htT hS1W hcB hc hBd hKcap hinv tt
  have hA := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hsz : sz.SizeTendsto := hA.2.2.1
  have hWt := ST_W_tendsto sz hsz hA.1 hA.2.2.2.1
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hbd : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (tt n : ℝ) ∧
      sz.Bctl n (tt n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBd] with n hn
    exact hn (tt n : ℝ) ((hs n).trans (tt n).2.1) (tt n).2.2
  have hcap : ∀ᶠ n in atTop, 0 ≤ Kf n (tt n : ℝ) ∧ Kf n (tt n : ℝ) ≤
      (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (tt n : ℝ) := by
    filter_upwards [hKcap] with n hn
    exact hn (tt n : ℝ) (tt n).2.1 (tt n).2.2
  have hp : 0 < (d : ℝ) * c := mul_pos hd' hc
  -- the exponent `ε₀` and the bound `Ψ`
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℕ → ℝ,
      Ψ = fun n => Real.sqrt ((1 + cB⁻¹) * sz.Bctl n (tt n : ℝ)) := ⟨_, rfl⟩
  have hbpos : ∀ n, 0 ≤ sz.Bctl n (tt n : ℝ) := fun n =>
    (STBctl_pos sz n (lt_of_le_of_lt ((tt n).2.2.trans (htT n)) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n))).le
  have hΨsq : ∀ n, Ψ n ^ 2 = (1 + cB⁻¹) * sz.Bctl n (tt n : ℝ) := by
    intro n
    rw [hΨdef]
    exact Real.sq_sqrt (mul_nonneg (by positivity) (hbpos n))
  have hWbig : ∀ᶠ n in atTop, (1 + cB⁻¹) ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < (d : ℝ) * c / 2)).comp hWt).eventually
      (eventually_ge_atTop _)
  have hΨ : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
      Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
    filter_upwards [hbd, hWbig, hWt.eventually (eventually_ge_atTop 1)] with n hn hWb hW1
    obtain ⟨hlo, hhi⟩ := hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
    have hΨ0 : 0 ≤ Ψ n := by rw [hΨdef]; exact Real.sqrt_nonneg _
    constructor
    · rw [ST_rpow_neg_half hW.le]
      have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Ψ n ^ 2 := by
        rw [hΨsq]
        calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
            ≤ (1 + cB⁻¹) * (cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
              have : (1 + cB⁻¹) * cB = cB + 1 := by field_simp
              nlinarith [inv_pos.mpr hWd]
          _ ≤ (1 + cB⁻¹) * sz.Bctl n (tt n : ℝ) :=
              mul_le_mul_of_nonneg_left hlo (by positivity)
      calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) ≤ (Ψ n ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (inv_nonneg.mpr hWd.le) h1 (by norm_num)
        _ = Ψ n := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hΨ0]
    · have hsq : Ψ n ^ 2 ≤ (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ^ 2 := by
        rw [hΨsq, ST_rpow_sq hW.le]
        have hb' : sz.Bctl n (tt n : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) :=
          hhi.trans (ST_size_rpow_neg_le sz n hc.le)
        calc (1 + cB⁻¹) * sz.Bctl n (tt n : ℝ)
            ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c / 2) * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) :=
              mul_le_mul hWb hb' (hbpos n) (Real.rpow_nonneg hW.le _)
          _ = ((sz.W n : ℕ) : ℝ) ^ (2 * -ε₀) := by
              rw [← Real.rpow_add hW, hε₀]; congr 1; ring
      exact (pow_le_pow_iff_left₀ hΨ0 (Real.rpow_nonneg hW.le _) (by norm_num)).1 hsq
  -- `(initialGT2)` at the section
  have hInit1 : PrecL sz (law sz) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(mk sz z).GM n (tt n : ℝ) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) := by
    have h1 := StochDomAt.precomp_param
      (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hS1W
      (fun n p => (tt n, p.1, p.2))
    refine Step2EventsGen_prec_mono_eventually (law sz) ?_ h1
    filter_upwards [hbd] with n hn u ω
    have hb0 := hbpos n
    have := ST_quarter_le sz n hb0 hc.le hn.2
    rw [hε₀]
    exact this
  have hInit2 : PrecL sz (law sz) (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2g (mk sz z).toFlowFM n (tt n : ℝ) ω) (fun n _ _ => Ψ n ^ 2) := by
    have h1 := hinv tt 1 one_pos
    have h2 := StochDomAt.precomp_param (V := fun n => Zd d (sz.L n) × Zd d (sz.L n)) h1
      (fun n p => ((⟨![false, true], by simp⟩ : {σ : Fin 2 → Bool // σ 0 ≠ σ 1}), ![p.1, p.2]))
    have h3 : PrecL sz (law sz) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖(mk sz z).L n (tt n : ℝ) ![false, true] ![p.1, p.2] ω‖)
        (fun n _ _ => Ψ n ^ 2) := by
      refine Step2EventsGen_prec_mono_eventually (law sz) ?_ h2
      filter_upwards [hbd, hcap] with n hn hcn u ω
      rw [hΨsq]
      exact ST_prof_le_Bctl sz n hcB hcn.1 one_pos hn.1 _ _
    exact Step2EventsGen_prec_sup (law sz) _ _ h3
  have hinit : STInitialGT2gL (mk sz z).toFlowFM (law sz) (fun n => (tt n : ℝ)) ε₀ Ψ := ⟨hInit1, hInit2⟩
  have ht0 : ∀ n, 0 ≤ (tt n : ℝ) := fun n => (hs n).trans (tt n).2.1
  have htT' : ∀ n, (tt n : ℝ) ≤ T0 sz z n := fun n => (tt n).2.2.trans (htT n)
  refine ⟨fun D hD => ?_, fun D hD => ?_⟩
  · exact hLWT κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ)) ht0 htT' ε₀ hε₀pos Ψ hΨ hinit
      (fun n => Kf n (tt n : ℝ)) hcap (hinv tt) D hD
  · exact hEMe κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ)) ht0 htT' ε₀ hε₀pos Ψ hΨ hinit
      (fun n => Kf n (tt n : ℝ)) hcap (hinv tt) D hD

/-! ## 6. The events over `Cm : Step2Mat sz` -/

/-- **`STEvWeakg`**: the weak law on the grid (band `ST_event_weak`). -/
def STEvWeakg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (δ₀ : ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ x y,
    ‖STGMMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) x y‖ ≤ δ₀})

/-- **`STEvInitg`**: the initial value on the grid (band `ST_event_init`). -/
def STEvInitg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ)
    (a₀ : ℕ → ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ i : STLab sz n, ‖STgAg Cm s T K n i.1 i.2 0 ω‖ ≤
    a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)})

/-- **`STEvLWg`**: the light-weight term on the grid (band `ST_event_lw`); the band factor
`(mE E).im * (1 - u)` is the carrier's `eta`. -/
def STEvLWg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ)
    (Λ : ℕ → ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
    ‖STEGtMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ ≤
      Λ n / Cm.eta n (gridTime s T K n j) * (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)})

/-- **`STEvMGg`**: the quadratic variation on the grid with the random bound `Ĵ` (band `ST_event_mg`). -/
def STEvMGg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ)
    (Λ : ℕ → ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
    ‖STEEMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ ≤
      Λ n / Cm.eta n (gridTime s T K n j) * ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
        (STJhatMg Cm n D (Kf n (gridTime s T K n j)) (gridTime s T K n j) (Cm.Hpath s T K n j ω)) ^ 3) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2})

/-- `Ĵ ≥ 0` for a fine matrix (band `ST_JhatM_nonneg`). -/
theorem Step2EventsGen_JhatMg_nonneg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (D ℓ u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : 0 ≤ STJhatMg Cm n D ℓ u H := by
  unfold STJhatMg
  refine le_trans ?_ (Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
    ‖STLKMg Cm n u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))
    (Finset.mem_univ ((fun _ => true), (fun _ => 0))))
  exact div_nonneg (norm_nonneg _) (ST_STprof_pos sz _ _ _ _ _ _).le

/-- **`ST_event_weakg`** (band `ST_event_weak`): the weak local law on the grid, from (2.86) `Gtmwc` of
Step 1 at every time section. -/
theorem ST_event_weakg :
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ), Step2EventsGen_Grid Cm μ → ∀ (s t T : ℕ → ℝ) (K : ℕ → ℕ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ t n) → (∀ n, K n ≠ 0) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℕ)) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ C₁) →
    STStep1WeakgL Cm.toFlowFM μ s t → ∀ ε₁ δ₀ : ℝ, 0 < ε₁ →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n u) ^ (1 / 4 : ℝ) ≤ δ₀) →
    STEvWeakg Cm s T K δ₀ := by
  intro d sz Cm μ hG s t T K hs hsT hTt hK C₁ hC₁ hcard hS1W ε₁ δ₀ hε₁ hsmall
  have hG' := hG
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hG
  have hmain := Step2EventsGen_grid_whp_of_sections Cm μ hlaw
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) s T K hs hsT hK hC₁ hcard
    (fun n v u H => ‖STGMMg Cm n u H v.1 v.2‖) (fun n v u H => (sz.Bctl n u) ^ (1 / 4 : ℝ))
    (fun n v u => (Step2EventsGen_STGMMg_measurable hG' n u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt => by
      have h := StochDomAt.precomp_param
        (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hS1W
        (fun n p => (⟨(tt n : ℝ), (tt n).2.1, (tt n).2.2.trans (hTt n)⟩, p.1, p.2))
      have e : ∀ n ω (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)),
          STGMMg Cm n (tt n : ℝ) (Hm n (tt n : ℝ) ω) v.1 v.2 = Cm.GM n (tt n : ℝ) ω v.1 v.2 :=
        fun n ω v => hGMM n _ ω v.1 v.2
      unfold PrecL
      simpa only [e] using h)
  unfold STEvWeakg
  refine hmain.mono ?_
  filter_upwards [hsmall] with n hn ω hω j hj x y
  have hmem := ST_gridTime_mem s T K n j (hsT n) (hK n) hj
  have h1 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (x, y)
  exact h1.trans (hn _ hmem.1 (hmem.2.trans (hTt n)))

/-- **`ST_event_initg`** (band `ST_event_init`): the initial value on the grid, from (2.79) `Eq:Gdecay+IND`
at `s`, with the floor `D_i`; the deterministic comparison `hcmp` turns its profile into the profile of the scale family. -/
theorem ST_event_initg :
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ), Step2EventsGen_Grid Cm μ → ∀ (s T : ℕ → ℝ) (K : ℕ → ℕ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, K n ≠ 0) → STDecaygL Cm.toFlowFM μ s → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁) → ∀ ε₁ : ℝ, 0 < ε₁ → ∀ Di : ℝ, 0 < Di →
    ∀ (D : ℝ) (Kf : ℕ → ℝ → ℝ) (a₀ : ℕ → ℝ),
    (∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
      STWB sz n (s n) (zdistInf d (sz.L n) (i.2 0 - i.2 1)) * Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Di)) ≤
      a₀ n * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1)) → STEvInitg Cm s T K D Kf a₀ := by
  intro d sz Cm μ hG s T K hs hsT hK hDec C₁ hC₁ hcard ε₁ hε₁ Di hDi D Kf a₀ hcmp
  have hG' := hG
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hG
  have hmain := Step2EventsGen_grid_whp_zero Cm μ hlaw (V := fun n => STLab sz n) s T K hs hsT hK hC₁ hcard
    (fun n v u H => ‖STLKMg Cm n u H v.1 v.2‖)
    (fun n v u H => (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (v.2 0 - v.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (v.2 0 - v.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Di))
    (fun n v u => (Step2EventsGen_STLKMg_measurable hG' n u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (by
      have h := hDec Di hDi
      simpa only [Step2EventsGen_STLKMg_eq Cm hLM] using h)
  unfold STEvInitg
  refine hmain.mono ?_
  filter_upwards [hcmp] with n hn ω hω i
  have h1 := hω i
  have e0 := ST_gridTime_zero s T K n
  change ‖STLKMg Cm n (gridTime s T K n 0) (Cm.Hpath s T K n 0 ω) i.1 i.2‖ ≤
    a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)
  rw [e0] at h1 ⊢
  exact h1.trans (hn i)

/-- **`ST_event_lwg`** (band `ST_event_lw`): the light-weight term on the grid (Lemma 3.11 `lem: EWGn2_N` at every
grid time).  The hypotheses of `ST_LW_sectionsg`, `DecayGen_Spec` (only `eta > 0` is read) and `Step2EventsGen_Grid`. -/
theorem ST_event_lwg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
  Step2EventsGen_Flow d Flow T0 → STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  0 < d → ∀ (sz : Sizes d) (κ ε 𝔡 𝔠 κm : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z →
  DecayGen_Spec (mk sz z).toFlowFM κm → Step2EventsGen_Grid (mk sz z) (law sz) →
  ∀ (s t T : ℕ → ℝ) (K : ℕ → ℕ) (cB c : ℝ) (Kf : ℕ → ℝ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, t n ≤ T0 sz z n) → STStep1WeakgL (mk sz z).toFlowFM (law sz) s t → 0 < cB → 0 < c →
    (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ Kf n u ∧ Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) →
    STScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
    (∀ n, s n ≤ T n) → (∀ n, T n ≤ t n) → (∀ n, K n ≠ 0) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (STLab sz n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁) →
    ∀ ε₁ : ℝ, 0 < ε₁ → ∀ Λ : ℕ → ℝ, (∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n) → ∀ D : ℝ, 0 < D →
      STEvLWg (mk sz z) s T K D Kf Λ := by
  intro hFl hLWT hEMe hd sz κ ε 𝔡 𝔠 κm z hκ hε h𝔡 hflow hSpec hG s t T K cB c Kf hs htT hS1W hcB hc hBd hKcap hinv
    hsT hTt hK C₁ hC₁ hcard ε₁ hε₁ Λ hΛ D hD
  have hG' := hG
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hG
  have hmain := Step2EventsGen_grid_whp_of_sections (mk sz z) (law sz) hlaw (V := fun n => STLab sz n) s T K hs hsT hK
    hC₁ hcard
    (fun n v u H => ‖STEGtMg (mk sz z) n u H v.1 v.2‖)
    (fun n v u H => ((mk sz z).eta n u)⁻¹ * (sz.Bctl n u) ^ (1 / 2 : ℝ) *
      STprof sz n u D (Kf n u) (v.2 0) (v.2 1))
    (fun n v u => (Step2EventsGen_STEGtMg_measurable hG' n u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt => by
      have h := (ST_LW_sectionsg d law Flow mk T0 hFl hLWT hEMe hd sz κ ε 𝔡 𝔠 z hκ hε h𝔡 hflow s t cB c Kf hs htT hS1W
        hcB hc hBd hKcap hinv (fun n => ⟨(tt n : ℝ), (tt n).2.1, (tt n).2.2.trans (hTt n)⟩)).1 D hD
      simpa only [Step2EventsGen_STEGtMg_eq (mk sz z) hLM] using h)
  unfold STEvLWg
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  have h1 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) i
  refine h1.trans ?_
  have hmem := ST_gridTime_mem s T K n j (hsT n) (hK n) hj
  have hlt : gridTime s T K n j < 1 :=
    lt_of_le_of_lt (hmem.2.trans ((hTt n).trans (htT n))) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  have hpos : 0 < (mk sz z).eta n (gridTime s T K n j) := by
    rw [hSpec.2.2]
    exact mul_pos (by linarith) (lt_of_lt_of_le hSpec.1 (hSpec.2.1 n))
  have hb := (STBctl_pos sz n hlt).le
  have hnn : 0 ≤ ((mk sz z).eta n (gridTime s T K n j))⁻¹ *
      (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
      STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hpos.le) (Real.rpow_nonneg hb _))
      (ST_STprof_pos sz _ _ _ _ _ _).le
  calc ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
        (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1))
      ≤ Λ n * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
        (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)) :=
        mul_le_mul_of_nonneg_right (hΛ n) hnn
    _ = Λ n / (mk sz z).eta n (gridTime s T K n j) *
        (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) := by
        rw [div_eq_mul_inv]; ring

/-- **`ST_event_mgg`** (band `ST_event_mg`): the quadratic variation on the grid (Lemma 3.13 `lem: EMn2_N`, third
estimate), with the random bound `Ĵ` of the grid state. -/
theorem ST_event_mgg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
  Step2EventsGen_Flow d Flow T0 → STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  0 < d → ∀ (sz : Sizes d) (κ ε 𝔡 𝔠 κm : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z →
  DecayGen_Spec (mk sz z).toFlowFM κm → Step2EventsGen_Grid (mk sz z) (law sz) →
  ∀ (s t T : ℕ → ℝ) (K : ℕ → ℕ) (cB c : ℝ) (Kf : ℕ → ℝ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, t n ≤ T0 sz z n) → STStep1WeakgL (mk sz z).toFlowFM (law sz) s t → 0 < cB → 0 < c →
    (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ Kf n u ∧ Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) →
    STScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
    (∀ n, s n ≤ T n) → (∀ n, T n ≤ t n) → (∀ n, K n ≠ 0) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Fin 2 × STLab sz n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁) →
    ∀ ε₁ : ℝ, 0 < ε₁ → ∀ Λ : ℕ → ℝ, (∀ n, 2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n) → ∀ D : ℝ, 0 < D →
      STEvMGg (mk sz z) s T K D Kf Λ := by
  intro hFl hLWT hEMe hd sz κ ε 𝔡 𝔠 κm z hκ hε h𝔡 hflow hSpec hG s t T K cB c Kf hs htT hS1W hcB hc hBd hKcap hinv
    hsT hTt hK C₁ hC₁ hcard ε₁ hε₁ Λ hΛ D hD
  have hG' := hG
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hG
  have hmain := Step2EventsGen_grid_whp_of_sections (mk sz z) (law sz) hlaw (V := fun n => Fin 2 × STLab sz n) s T K hs hsT
    hK hC₁ hcard
    (fun n v u H => ‖STEEkMg (mk sz z) n u H v.1 v.2.1 v.2.2‖)
    (fun n v u H => ((mk sz z).eta n u)⁻¹ *
      ((sz.Bctl n u) ^ (1 / 2 : ℝ) + (STJhatMg (mk sz z) n D (Kf n u) u H) ^ 3) *
      (STprof sz n u D (Kf n u) (v.2.2 0) (v.2.2 1)) ^ 2)
    (fun n v u => (Step2EventsGen_STEEkMg_measurable hG' n u v.1 v.2.1 v.2.2).norm)
    (fun n v u => (((measurable_const.mul (measurable_const.add
      ((Step2EventsGen_STJhatMg_measurable hG' n u D (Kf n u)).pow_const 3))).mul measurable_const)))
    ε₁ hε₁ (fun tt => by
      have h := (ST_LW_sectionsg d law Flow mk T0 hFl hLWT hEMe hd sz κ ε 𝔡 𝔠 z hκ hε h𝔡 hflow s t cB c Kf hs htT hS1W
        hcB hc hBd hKcap hinv (fun n => ⟨(tt n : ℝ), (tt n).2.1, (tt n).2.2.trans (hTt n)⟩)).2 D hD
      simpa only [Step2EventsGen_STEEkMg_eq (mk sz z) hLM, Step2EventsGen_STJhatMg_eq (mk sz z) hLM] using h)
  unfold STEvMGg
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  have h0 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (0, i)
  have h1 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (1, i)
  have hmem := ST_gridTime_mem s T K n j (hsT n) (hK n) hj
  have hlt : gridTime s T K n j < 1 :=
    lt_of_le_of_lt (hmem.2.trans ((hTt n).trans (htT n))) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  have hpos : 0 < (mk sz z).eta n (gridTime s T K n j) := by
    rw [hSpec.2.2]
    exact mul_pos (by linarith) (lt_of_lt_of_le hSpec.1 (hSpec.2.1 n))
  have hb := (STBctl_pos sz n hlt).le
  have hJ := Step2EventsGen_JhatMg_nonneg (mk sz z) n D (Kf n (gridTime s T K n j))
    (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω)
  set Zv := (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
      ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
        (STJhatMg (mk sz z) n D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
          ((mk sz z).Hpath s T K n j ω)) ^ 3) *
      STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2) with hZv
  have hZnn : 0 ≤ Zv := mul_nonneg (mul_nonneg (inv_nonneg.mpr hpos.le)
    (add_nonneg (Real.rpow_nonneg hb _) (pow_nonneg hJ 3))) (sq_nonneg _)
  calc ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖
      ≤ ‖STEEkMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) 0 i.1 i.2‖ +
        ‖STEEkMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) 1 i.1 i.2‖ :=
        norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * Zv + ((sz.size n : ℕ) : ℝ) ^ ε₁ * Zv := add_le_add h0 h1
    _ = (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁) * Zv := by ring
    _ ≤ Λ n * Zv := mul_le_mul_of_nonneg_right (hΛ n) hZnn
    _ = Λ n / (mk sz z).eta n (gridTime s T K n j) *
          ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
            (STJhatMg (mk sz z) n D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
              ((mk sz z).Hpath s T K n j ω)) ^ 3) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2 := by
        rw [hZv, div_eq_mul_inv]; ring

/-! ## 7. The good event `STGoodAtg` and its probability `ST_good_probg` -/

/-- **The good event of one step** (band `STGoodAt`) over a carrier `Cm`: the pathwise facts that the
statements provide for the grid walk.  The band factor `(mE E).im * (1 - u)` is `Cm.eta`; the identity reads the drift `STgDriftg`.
The fields are, in order, the seven conjuncts of the good event. -/
structure STGoodAtg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (D : ℝ) (ℓk : ℕ → ℝ)
    (Λ δ₀ a₀ r₀ ρ₁ : ℝ) (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz) : Prop where
  weak : ∀ j, j ≤ K n → ∀ x y, ‖STGMMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) x y‖ ≤ δ₀
  init : ∀ i : STLab sz n, ‖STgAg Cm s t K n i.1 i.2 0 ω‖ ≤ a₀ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1)
  lw : ∀ j, j ≤ K n → ∀ i : STLab sz n, ‖STEGtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ ≤
    Λ / Cm.eta n (gridTime s t K n j) * (sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) *
      STprof sz n (gridTime s t K n j) D (ℓk j) (i.2 0) (i.2 1)
  mg : ∀ j, j ≤ K n → ∀ i : STLab sz n, ‖STEEMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ ≤
    Λ / Cm.eta n (gridTime s t K n j) * ((sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) +
      (STJhatMg Cm n D (ℓk j) (gridTime s t K n j) (Cm.Hpath s t K n j ω)) ^ 3) *
      STprof sz n (gridTime s t K n j) D (ℓk j) (i.2 0) (i.2 1) ^ 2
  mart : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Mart i k ω‖ ≤ Λ * (∑ j ∈ Finset.range k, gridStep s t K n *
      ‖STEEMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ +
      ρ₁ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1) ^ 2) ^ (1 / 2 : ℝ)
  rem : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ r₀ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1)
  ident : ∀ i : STLab sz n, ∀ k, k ≤ K n → STgAg Cm s t K n i.1 i.2 k ω = STgAg Cm s t K n i.1 i.2 0 ω +
    ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω + Rem i k ω + Mart i k ω

/-- **`ST_good_probg`** (band `ST_good_prob`): `P(¬ STGoodAtg) ≤ N^{-D'}` from the four
events of high probability `STEvWeakg`, `STEvInitg`, `STEvLWg`, `STEvMGg`, the martingale event (probability `N^{-D_m}` per label, `#labels ≤ N^3`) and the a.e. identities
(decomposition and remainder).  The identity reads `STgDriftg`; `Dm = D' + 4` is sharp. -/
theorem ST_good_probg :
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz), Tendsto sz.size atTop atTop → ∀ (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ)
    (Kf : ℕ → ℝ → ℝ) (δ₀ : ℝ) (Λ a₀ r₀ ρ₁ : ℕ → ℝ) (Mart Rem : ∀ n, STLab sz n → ℕ → PathΩ sz → ℂ),
    STEvWeakg Cm s T K δ₀ → STEvInitg Cm s T K D Kf a₀ → STEvLWg Cm s T K D Kf Λ → STEvMGg Cm s T K D Kf Λ →
    (∀ n, 0 ≤ gridStep s T K n) → ∀ D' Dm ε₁ : ℝ, 0 < D' → D' + 1 + 3 ≤ Dm →
    (∀ᶠ n in atTop, ∀ i : STLab sz n, Cm.Pp {ω | ∃ k, k ≤ K n ∧ ((sz.size n : ℕ) : ℝ) ^ ε₁ *
      (∑ j ∈ Finset.range k, gridStep s T K n * ‖STEEMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-Dm))) →
    (∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n) →
    (∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤
      ρ₁ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) ^ 2) →
    (∀ n (i : STLab sz n), ∀ᵐ ω ∂Cm.Pp, ∀ k, k ≤ K n → STgAg Cm s T K n i.1 i.2 k ω = STgAg Cm s T K n i.1 i.2 0 ω +
      ((gridStep s T K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) →
    (∀ᶠ n in atTop, ∀ i : STLab sz n, ∀ᵐ ω ∂Cm.Pp, ∀ k, k ≤ K n →
      ‖Rem n i k ω‖ ≤ r₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)) →
    (∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ)) →
    ∀ᶠ n in atTop, Cm.Pp {ω | ¬ STGoodAtg Cm s T K n D (fun j => Kf n (gridTime s T K n j)) (Λ n) δ₀ (a₀ n) (r₀ n)
        (ρ₁ n) (Mart n) (Rem n) ω} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D')) := by
  intro d sz Cm hsize s T K D Kf δ₀ Λ a₀ r₀ ρ₁ Mart Rem hw hi hl hm hΔ D' Dm ε₁ hD' hDm hmart hΛ hρ hident hrem hcardLab
  classical
  have h14 := Gauss.HighProbAt.inter hsize
    (Gauss.HighProbAt.inter hsize (Gauss.HighProbAt.inter hsize hw hi) hl) hm
  filter_upwards [h14 (D' + 1) (by linarith), hmart, hρ, hrem, hcardLab,
    hsize.eventually (eventually_two_mul_rpow_le D'), hsize.eventually (eventually_ge_atTop 1)]
    with n h14n hmartn hρn hremn hcardn h2 hN1
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  -- the martingale event
  set Nr : ℝ := ((sz.size n : ℕ) : ℝ) with hNr
  let G14 : Set (PathΩ sz) := {ω | ∀ j, j ≤ K n → ∀ x y,
      ‖STGMMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) x y‖ ≤ δ₀} ∩
    {ω | ∀ i : STLab sz n,
      ‖STgAg Cm s T K n i.1 i.2 0 ω‖ ≤
        a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)} ∩
    {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEGtMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ ≤
        Λ n / Cm.eta n (gridTime s T K n j) *
          (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)} ∩
    {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEEMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ ≤
        Λ n / Cm.eta n (gridTime s T K n j) *
          ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
            (STJhatMg Cm n D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
              (Cm.Hpath s T K n j ω)) ^ 3) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2}
  let B : STLab sz n → Set (PathΩ sz) := fun i => {ω | ∃ k, k ≤ K n ∧
      Nr ^ ε₁ * (∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ +
        Nr ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖}
  have hB : Cm.Pp (⋃ i, B i) ≤ ENNReal.ofReal (Nr ^ (-(D' + 1))) :=
    ST_union_prob (Cm.Pp) B hN1' hcardn hDm hmartn
  have hae : ∀ᵐ ω ∂(Cm.Pp), ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgAg Cm s T K n i.1 i.2 k ω =
        STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) := by
    have h1 : ∀ᵐ ω ∂(Cm.Pp), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        STgAg Cm s T K n i.1 i.2 k ω =
          STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
            ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := ae_all_iff.2 fun i => hident n i
    have h2' : ∀ᵐ ω ∂(Cm.Pp), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        ‖Rem n i k ω‖ ≤ r₀ n *
          STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) :=
      ae_all_iff.2 fun i => hremn i
    filter_upwards [h1, h2'] with ω a b i k hk
    exact ⟨a i k hk, b i k hk⟩
  have hnull : Cm.Pp {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgAg Cm s T K n i.1 i.2 k ω =
        STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)} = 0 :=
    ae_iff.1 hae
  -- the bad event is contained in the union of the three bad events
  have hsub : {ω | ¬ STGoodAtg Cm s T K n D (fun j => Kf n (gridTime s T K n j)) (Λ n) δ₀
        (a₀ n) (r₀ n) (ρ₁ n) (Mart n) (Rem n) ω} ⊆
      (G14ᶜ ∪ ⋃ i, B i) ∪ {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgAg Cm s T K n i.1 i.2 k ω =
        STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_or,
      not_not] at hcon
    obtain ⟨⟨hG14, hnB⟩, hid⟩ := hcon
    obtain ⟨⟨⟨hweak, hinit⟩, hlw⟩, hmg⟩ := hG14
    refine hω ⟨hweak, hinit, hlw, hmg, ?_, fun i k hk => (hid i k hk).2, fun i k hk => (hid i k hk).1⟩
    intro i k hk
    have hnB' : ω ∉ B i := fun h => hnB ⟨i, h⟩
    simp only [B, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hnB'
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hΔ n) (norm_nonneg _)
    have hρi := hρn i
    have hΛ0 : 0 ≤ Λ n := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (hΛ n)
    refine (hnB' k hk).trans ?_
    refine mul_le_mul (hΛ n) (Real.rpow_le_rpow (by positivity) ?_ (by norm_num))
      (Real.rpow_nonneg (by positivity) _) hΛ0
    linarith
  have hmeas : Cm.Pp ((G14ᶜ ∪ ⋃ i, B i) ∪ {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgAg Cm s T K n i.1 i.2 k ω =
        STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)}) ≤
      ENNReal.ofReal (Nr ^ (-(D' + 1))) + ENNReal.ofReal (Nr ^ (-(D' + 1))) := by
    refine (measure_union_le _ _).trans ?_
    rw [hnull, add_zero]
    refine (measure_union_le _ _).trans ?_
    exact add_le_add h14n hB
  have hfin : ENNReal.ofReal (Nr ^ (-(D' + 1))) + ENNReal.ofReal (Nr ^ (-(D' + 1))) ≤
      ENNReal.ofReal (Nr ^ (-D')) := by
    have hp : (0 : ℝ) ≤ Nr ^ (-(D' + 1)) := Real.rpow_nonneg (by positivity) _
    rw [← ENNReal.ofReal_add hp hp]
    refine ENNReal.ofReal_le_ofReal ?_
    have := h2
    linarith
  exact (measure_mono hsub).trans (hmeas.trans hfin)

/-! ## 8. `STBdatagL` and the generic L-bridges -/

/-- **`STBdatagL`**: the size data over a flow setting and a horizon (band `STBdata`, proved as
`ST_Bdata_holds`).  Definitional at the band setting; in the block Anderson model it reads
`1 - T0 ≥ Im z / 2` (`cB`, `c` unchanged). -/
def STBdatagL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ cB : ℝ, 0 < cB ∧ ∀ 𝔠 : ℝ, ∃ c : ℝ, 0 < c ∧
    ∀ (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
        cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)

/-- Band bridge of `STBdatagL` (`Iff.rfl`). -/
theorem bandFM_STBdata (d : ℕ) :
    STBdata d ↔ STBdatagL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n)) := Iff.rfl

/-- **`STEGt = LWE`** over a carrier with `Step2EventsGen_Rot3` (band `STB_EGt_eq_LWE`): the two forms of the light-weight
term agree pointwise; the second term of `STEGtg` is the cyclic rotation of the 3-loop. -/
theorem Step2EventsGen_EGt_eq_LWE {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (hR : Step2EventsGen_Rot3 C) (n : ℕ) (t : ℝ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : STEGtg C n t σ a ω = LWEg C n t σ a ω := by
  unfold STEGtg LWEg LWcutg
  have h1 : ∀ s : Bool, (fun _ : Fin 1 => s) = ![s] := fun s => by
    funext i; fin_cases i; rfl
  have h1' : ∀ x : Zd d (sz.L n), (fun _ : Fin 1 => x) = ![x] := fun x => by
    funext i; fin_cases i; rfl
  simp only [h1, h1']
  have hB : ∀ x y : Zd d (sz.L n),
      (C.L n t ![σ 1] ![x] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.L n t ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω =
      C.S n x y * (C.L n t ![σ 1] ![x] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) *
        C.L n t ![σ 1, σ 1, σ 0] ![y, a 1, a 0] ω := fun x y => by
    rw [hR n t (σ 0) (σ 1) (a 0) y (a 1) ω]; ring
  have hA : ∀ x y : Zd d (sz.L n),
      (C.L n t ![σ 0] ![x] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.L n t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω =
      C.S n x y * (C.L n t ![σ 0] ![x] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
        C.L n t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω := fun x y => by ring
  simp only [Finset.sum_add_distrib, hA, hB]
  ring

/-- **The bridge `lem:LWterm` ⇒ `STLWB`** over a carrier family (band `STLWB_of_LWterm`).  With `Φ_t(r) = Ψ_t(⌊r⌋₊)` and `Ψ' = max (Ψ_t(0), W^{-d/2})` the hypotheses of `LWAssmgL` follow from `STPsiClass`,
`STInitialGT2gL`, `STLWassmgL`, and the conclusion of `LWtermG` is that of `STLWBgL` after `Step2EventsGen_EGt_eq_LWE`.  The facts
read: `Step2EventsGen_Flow` (`Admissible`: `W → ∞`, `ε₀ ≤ d/2` by `STB_eps_le`) and `Step2EventsGen_Rot3`. -/
theorem stLWBgL_of_LWtermG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (mkF : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) :
  3 ≤ d → (∀ sz κ ε 𝔠 𝔡 z, Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡) → (∀ sz z, Step2EventsGen_Rot3 (mkF sz z)) →
    LWtermG d law Flow mkF T0 → STLWBgL d law Flow mkF T0 := by
  intro hd hFl hR hLW κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hinit hassm
  have hAd := hFl sz κ ε 𝔠 𝔡 z hflow
  have hWt := ST_W_tendsto sz hAd.2.2.1 hAd.1 hAd.2.2.2.1
  have hε₀d := STB_eps_le sz hΨ hWt
  obtain ⟨hΨ1, hΨ2, hΨ3, C₁, C₂, hC₁, hC₂, hΨ4⟩ := hΨ
  choose c hc hev using hΨ3
  set Ψ' : ℕ → ℝ := fun n => max (Ψ n 0) (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) with hΨ'
  set Φ : ℕ → ℝ → ℝ := fun n r => Ψ n ⌊r⌋₊ with hΦ
  have hΦ0 : ∀ n, Φ n 0 = Ψ n 0 := fun n => by simp [hΦ]
  have hΦk : ∀ n (k : ℕ), Φ n (k : ℝ) = Ψ n k := fun n k => by simp [hΦ]
  have hWge : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hWt.eventually_ge_atTop 1
  have hwin : LWWindow sz ε₀ Ψ' := by
    filter_upwards [hWge] with n hn
    refine ⟨le_max_right _ _, max_le (hΨ1 n 0).2 ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hAssm : LWAssmgL (mkF sz z) (law sz) t ε₀ Ψ' Φ (C₁ * (2 : ℝ) ^ C₂) C₂ (c 0)⁻¹
      (fun C => (c ⌈C⌉₊)⁻¹) := by
    refine ⟨hε₀, hwin, ⟨hinit.1, ?_⟩, ⟨?_, inv_pos.mpr (hc 0), ?_⟩, ⟨?_, ?_, hC₂, ?_, ?_⟩, ?_⟩
    · refine Step2EventsGen_prec_dom (law sz) hinit.2 (Eventually.of_forall fun n u' => ⟨u', fun ω => le_rfl, fun ω => ?_⟩)
      exact pow_le_pow_left₀ (hΨ1 n 0).1.le (le_max_left _ _) 2
    · exact Eventually.of_forall fun n r _ => hΨ1 n _
    · filter_upwards [hev 0] with n hn
      rw [hΦ0]; exact hn.1
    · intro n x _ y _ hxy
      exact hΨ2 n _ _ (Nat.floor_le_floor hxy)
    · have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ C₂ := Real.one_le_rpow (by norm_num) (by linarith)
      nlinarith
    · intro C _
      filter_upwards [hev ⌈C⌉₊] with n hn ℓ hℓ0 hℓC
      have hfl : ⌊ℓ⌋₊ ≤ ⌈C⌉₊ := (Nat.floor_le_floor hℓC).trans (Nat.floor_le_ceil C)
      have := hn.2 ⌊ℓ⌋₊ hfl
      rw [hΦ0]
      exact (le_inv_mul_iff₀ (hc _)).2 this
    · refine Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_
      have hr1 : 1 ≤ ⌊ℓ₁⌋₊ := Nat.le_floor (by simpa using h1)
      have hr12 : ⌊ℓ₁⌋₊ ≤ ⌊ℓ₂⌋₊ := Nat.floor_le_floor h12
      have hr1pos : (0 : ℝ) < (⌊ℓ₁⌋₊ : ℝ) := by exact_mod_cast hr1
      have hℓ₁pos : (0 : ℝ) < ℓ₁ := by linarith
      have hℓ₂pos : (0 : ℝ) < ℓ₂ := by linarith
      have hD := hΨ4 n ⌊ℓ₁⌋₊ ⌊ℓ₂⌋₊ hr1 hr12
      have hΨ2pos := (hΨ1 n ⌊ℓ₂⌋₊).1
      have hlow : ℓ₁ / 2 ≤ (⌊ℓ₁⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one ℓ₁
        have h1' : (1 : ℝ) ≤ (⌊ℓ₁⌋₊ : ℝ) := by exact_mod_cast hr1
        linarith
      have hup : (⌊ℓ₂⌋₊ : ℝ) ≤ ℓ₂ := Nat.floor_le hℓ₂pos.le
      have hq : (⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ) ≤ 2 * (ℓ₂ / ℓ₁) := by
        calc (⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ) ≤ ℓ₂ / (ℓ₁ / 2) := by
              exact div_le_div₀ hℓ₂pos.le hup (by linarith) hlow
          _ = 2 * (ℓ₂ / ℓ₁) := by field_simp
      have hpow : ((⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ)) ^ C₂ ≤ (2 : ℝ) ^ C₂ * (ℓ₂ / ℓ₁) ^ C₂ := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hq (by linarith)
      rw [div_le_iff₀ hΨ2pos] at hD
      change Ψ n ⌊ℓ₁⌋₊ ≤ C₁ * (2 : ℝ) ^ C₂ * (ℓ₂ / ℓ₁) ^ C₂ * Ψ n ⌊ℓ₂⌋₊
      calc Ψ n ⌊ℓ₁⌋₊ ≤ C₁ * (((⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ)) ^ C₂) * Ψ n ⌊ℓ₂⌋₊ := hD
        _ ≤ C₁ * ((2 : ℝ) ^ C₂ * (ℓ₂ / ℓ₁) ^ C₂) * Ψ n ⌊ℓ₂⌋₊ := by
          gcongr
        _ = _ := by ring
    · refine Step2EventsGen_prec_dom (law sz) hassm (Eventually.of_forall fun n u' => ?_)
      refine ⟨(⟨![u'.1, !u'.1], by cases u'.1 <;> simp⟩, ![u'.2.1, u'.2.2]), fun ω => le_rfl, fun ω => ?_⟩
      simp [hΦk]
  have hmain := hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ _ _ _ _ Ψ' Φ hAssm
  refine Step2EventsGen_prec_dom (law sz) hmain (Eventually.of_forall fun n u' => ⟨u', fun ω => ?_, fun ω => ?_⟩)
  · rw [Step2EventsGen_EGt_eq_LWE (mkF sz z) (hR sz z)]
  · rw [hΦ0, hΦk]

/-- **The bridge `lem: EWGn2_N` ⇒ `STLWT`** over a carrier family (band `STLWT_of_LWtermExp`): `ℓ` is replaced by `ℓ' = 0` at the finitely many `n < N₀` where the eventual range of `ℓ` may
fail; `≺` does not see finitely many `n`. -/
theorem stLWTgL_of_LWtermExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (mkF : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) :
  3 ≤ d → (∀ sz κ ε 𝔠 𝔡 z, Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡) → (∀ sz z, Step2EventsGen_Rot3 (mkF sz z)) →
    LWtermExpG d law Flow mkF T0 → STLWTgL d law Flow mkF T0 := by
  intro hd hFl hR hLW κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hwin hinit ℓ hℓ hexp D hD
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hℓ
  set ℓ' : ℕ → ℝ := fun n => if n < N₀ then 0 else ℓ n with hℓ'
  have hℓ'eq : ∀ n, N₀ ≤ n → ℓ' n = ℓ n := fun n hn => by simp [hℓ', not_lt.2 hn]
  have hnn : ∀ n, 0 ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
      ellT (sz.L n) (sz.lam n) (t n) := fun n =>
    mul_nonneg (Even.pow_nonneg (by decide) _) ellT_nonneg
  have hAssm : LWAssmExpgL (mkF sz z) (law sz) t ε₀ Ψ ℓ' := by
    refine ⟨hε₀, hwin, hinit, ?_, ?_, ?_⟩
    · intro n
      by_cases h : n < N₀
      · simp [hℓ', h]
      · rw [hℓ'eq n (not_lt.1 h)]; exact (hN₀ n (not_lt.1 h)).1
    · intro n
      by_cases h : n < N₀
      · simpa [hℓ', h] using hnn n
      · rw [hℓ'eq n (not_lt.1 h)]; exact (hN₀ n (not_lt.1 h)).2
    · intro D' hD'
      refine Step2EventsGen_prec_dom (law sz) (hexp D' hD') (Filter.eventually_atTop.2 ⟨N₀, fun n hn u' => ?_⟩)
      refine ⟨(⟨![u'.1, !u'.1], by cases u'.1 <;> simp⟩, ![u'.2.1, u'.2.2]), fun ω => le_rfl,
        fun ω => ?_⟩
      simp [STprof, hℓ'eq n hn]
  have hmain := hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ' hAssm D hD
  refine Step2EventsGen_prec_dom (law sz) hmain (Filter.eventually_atTop.2 ⟨N₀, fun n hn u' => ⟨u', fun ω => ?_,
    fun ω => ?_⟩⟩)
  · rw [Step2EventsGen_EGt_eq_LWE (mkF sz z) (hR sz z)]
  · simp [STprof, hℓ'eq n hn]

/-! ## 9. The band readings of the carrier facts -/

/-- **The law clause of `Step2EventsGen_Grid` at the band**: `Hm = seqHflow`, the law is `ST_pathP_eq_seqP`. -/
theorem Step2EventsGen_bandLaw {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) :
    Step2EventsGen_Law (bandStep2Mat sz E) (Sizes.seqP sz) (fun n u => sz.seqHflow n u) :=
  fun s t K n k hs hst hK S hS => ST_pathP_eq_seqP sz s t K n k hs hst hK hS

/-- **`Step2EventsGen_Grid` at the band**: `Hm = seqHflow`, the first two clauses are `rfl`, the next two the measurability `STLM_measurable`, `STGMM_measurable`,
and the law clause is `Step2EventsGen_bandLaw`. -/
theorem Step2EventsGen_bandGrid {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) :
    Step2EventsGen_Grid (bandStep2Mat sz E) (Sizes.seqP sz) :=
  ⟨fun n u => sz.seqHflow n u, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun n u _ σ a => STLM_measurable sz n (E n) u σ a, fun n u x y => STGMM_measurable sz n (E n) u x y,
    Step2EventsGen_bandLaw sz E⟩

end RBM.BA

end
