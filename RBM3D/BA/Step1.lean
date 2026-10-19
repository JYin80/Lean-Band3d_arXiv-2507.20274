/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step1Setup
import RBM3D.BA.Step1Boot
import RBM3D.Induction.Continuity
import RBM3D.Induction.PerTimeCalc
import RBM3D.Induction.Step1Setup

/-!
# Block Anderson Step 1: the vocabulary `gmMax` and the helpers

Block Anderson version of the helpers of `Induction/Step1` (all of the sections 1-4 of the band file are private there).  Paper: Step 1 of Theorem 8.2
(`lem:main_ind_BA`), which is the same as in the one-dimensional proof; Lemma 8.4 (`lem_GbEXP_BA`) and Lemma 8.5 (`lem_ConArg_BA`);
the band source is Step 1 of the proof of Theorem 2.24 (`lem:main_ind`).  Namespace `RBM.BA`.

The private helpers are copies of the band helpers of `Induction/Step1`: `s1x`, `s1a`, `s1f`, `s1_wl_seq`,
`s1Net`, `s1Net_mem`, `s1_exists_close`, `s1_forb`,
`s1x_continuousOn`, `s1_boot`, `s1_weakPT`, `s1_perTime_timeIcc`,
`s1_loopPT`, `step1TargetV3_holds`, and of `BASetup_norm_BAmF_le_one` (`BA/Step1Setup`).  The scale facts and the `≺` calculus are
imported, not copied, from `Induction/Step1Setup` (`S1Std`, `s1_F3`-`s1_F8`, `s1_ratio_ev`, `s1_stochDom_unit`) and `Induction/PerTimeCalc`.

* section 0: the vocabulary `FlowFM.gmMax` (`‖G_v - M‖_{max}` of a carrier; the band's `s1x`) and
  the helpers `BAStep1_net`, `BAStep1_exists_close`, `BAStep1_perTime_timeIcc`, `BAStep1_gmMax_continuousOn`, ...;
  the helpers are used in `BA/Step1Prime` by `open private`.

The statements of the weak-law step, of the net and the forbidden region, and of the continuity argument with its two per-time conclusions are in
`BA/Step1Prime` (`baS1_wl_seq'`, `baS1_forb'`, `baS1_boot'`, `baS1_weakPT'`, `baS1_loopPT'`).

The event threshold of the loop input is `C₀ = 1 + κm⁻¹` (`|M_xy| ≤ (Im m)⁻¹`, `baM_entry_le`)
in place of the band's `2`; the loop input at `k = 2` is the uniform `PrecL` (event from
`perTimeCalc_highProbAt_of_stochDomAt`); the vocabulary is `‖G_u - M‖_{max}` over the carrier
`baFMz sz z'`; the net lift is `baNetLift`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 0. Vocabulary: `‖G_v - M‖_{max}` of a carrier -/

/-- `‖G_v - M‖_{max}` of a flow carrier at size index `n`, time `v`, sample `ω` (the band `s1xM`,
`Induction/Step1Setup`, is the `bandFM` case with `llErrMat` entries; the band `s1x`,
`Induction/Step1`, is private). -/
noncomputable def FlowFM.gmMax {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖C.GM n v ω q.1 q.2‖)

section Helpers

variable {d : ℕ}

/-- Each entry is at most `gmMax` (band `s1xM_ge`, `Induction/Step1Setup`). -/
private theorem BAStep1_le_gmMax {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖C.GM n v ω x y‖ ≤ C.gmMax n v ω :=
  Finset.le_sup' (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖C.GM n v ω q.1 q.2‖)
    (Finset.mem_univ (x, y))

/-- `gmMax ≤ B` from the entries (band `s1xM_le`, `Induction/Step1Setup`). -/
private theorem BAStep1_gmMax_le {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) {B : ℝ}
    (h : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n v ω x y‖ ≤ B) : C.gmMax n v ω ≤ B :=
  Finset.sup'_le _ _ fun q _ => h q.1 q.2

/-- One-sided Lipschitz bound of `gmMax` in the resolvent entries (band `s1xM_le_add`,
`Induction/Step1Setup`): `M` is time independent, so `GM_{u} - GM_{u'} = BAGt_{u} - BAGt_{u'}`. -/
private theorem BAStep1_gmMax_le_add (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u u' δ : ℝ) (ω : sz.SeqΩ)
    (h : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖BAGt sz lam0 E n u ω x y - BAGt sz lam0 E n u' ω x y‖ ≤ δ) :
    (baFM sz lam0 E).gmMax n u ω ≤ (baFM sz lam0 E).gmMax n u' ω + δ := by
  refine BAStep1_gmMax_le _ n u ω fun x y => ?_
  have h1 := BAStep1_le_gmMax (baFM sz lam0 E) n u' ω x y
  have h2 := norm_le_norm_sub_add ((baFM sz lam0 E).GM n u ω x y) ((baFM sz lam0 E).GM n u' ω x y)
  have e : (baFM sz lam0 E).GM n u ω x y - (baFM sz lam0 E).GM n u' ω x y =
      BAGt sz lam0 E n u ω x y - BAGt sz lam0 E n u' ω x y := by
    change (BAGt sz lam0 E n u ω x y - BAMfine sz lam0 E n x y) -
      (BAGt sz lam0 E n u' ω x y - BAMfine sz lam0 E n x y) = _
    ring
  rw [e] at h2
  have h3 := h x y
  linarith

/-- `v ↦ gmMax` is continuous on `[a, b]`, `b < 1`, for every sample (a finite `sup'` of `baG_continuousOn`;
band `s1x_continuousOn`, `Induction/Step1`). -/
private theorem BAStep1_gmMax_continuousOn (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hm : 0 < (BAmF sz lam0 E n).im) {a b : ℝ} (hb : b < 1) (ω : sz.SeqΩ) :
    ContinuousOn (fun v : ℝ => (baFM sz lam0 E).gmMax n v ω) (Set.Icc a b) := by
  unfold FlowFM.gmMax
  exact ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun q _ =>
    (baG_continuousOn d sz lam0 E n hm a b hb ω q.1 q.2).norm

/-- `|m| ≤ 1` for `m = m(E, g₀)` when `Im m > 0` (copy of the private `BASetup_norm_BAmF_le_one`,
`BA/Step1Setup`). -/
private theorem BAStep1_norm_BAmF_le_one (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (h : 0 < (BAmF sz lam0 E n).im) : ‖BAmF sz lam0 E n‖ ≤ 1 := by
  have hex : ∃ m, BASelf d (sz.L n) (lam0 n) (E n : ℂ) m := by
    by_contra hne
    have h0 : BAmF sz lam0 E n = 0 := by
      unfold BAmF BAm
      simp [hne]
    rw [h0] at h
    simp at h
  exact BAself_norm_le_one d (sz.L n) (lam0 n) (E n : ℂ) _ (by simp) (BAm_spec hex)

/-- The clamped net of `[s n, t n]` at scale `1/netSize A N` (copy of the private `s1Net`,
`Induction/Step1`). -/
private def BAStep1_net (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

/-- Copy of `s1Net_mem`, `Induction/Step1`. -/
private theorem BAStep1_net_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : BAStep1_net s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

/-- Copy of `s1_exists_close`, `Induction/Step1`. -/
private theorem BAStep1_exists_close {s t : ℕ → ℝ} (hlen : ∀ n, t n - s n ≤ 1) (A : ℝ) (N n : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (s n) (t n)) :
    ∃ k, |u - BAStep1_net s t A N n k| ≤ 1 / (netSize A N : ℝ) := by
  have hmem : u - s n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen n]⟩
  obtain ⟨k, hk⟩ := exists_netPt_close one_pos A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s n + netPt 1 A N k)| ≤ 1 / (netSize A N : ℝ) := by
    have h : u - (s n + netPt 1 A N k) = u - s n - netPt 1 A N k := by ring
    rw [h]; exact hk
  unfold BAStep1_net
  rcases le_or_gt (s n + netPt 1 A N k) (t n) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

/-- `ξ n (u n) p ω` per time over `[s,t]` from its section statements (copy of the private
`s1_perTime_timeIcc`, `Induction/Step1`). -/
private theorem BAStep1_perTime_timeIcc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) {V : ℕ → Type*}
    (hV : ∀ n, Nonempty (V n)) (ξ ζ : ∀ n, ℝ → V n → Ω → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      PerTimeDomAt P size (U := V) (fun n p ω => ξ n (u n) p ω) (fun n p ω => ζ n (u n) p ω)) :
    PerTimeDomAt P size (U := fun n => TimeIcc s t n × V n)
      (fun n p ω => ξ n p.1 p.2 ω) (fun n p ω => ζ n p.1 p.2 ω) := by
  have hne : ∀ n, Nonempty (TimeIcc s t n × V n) :=
    fun n => ⟨(⟨s n, le_rfl, hst n⟩, (hV n).some)⟩
  rw [perTimeDomAt_iff_forall_section P size hne]
  intro sec
  have h1 := h (fun n => ((sec n).1 : ℝ)) (fun n => (sec n).1.2)
  rw [perTimeDomAt_iff_forall_section P size hV] at h1
  exact h1 (fun n => (sec n).2)

end Helpers

end RBM.BA

