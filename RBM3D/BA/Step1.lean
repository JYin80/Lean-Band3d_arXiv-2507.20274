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
# BA-S2b2b (T2269): block Anderson port of `Induction/Step1.lean` §1-§4 and `baBootstrap'_holds`

Ticket T2269; DECISIONS §87 (1), §86, §84 (2), §81 (1), §72 (4); `docs/tickets/T2262.md` "Split"
(S2b2b). Paper: `paper/tex/7_8_light_weight.tex` (`7_8:line`): Step 1 `:1987-1990` ("same as
[RBSO1D, §7.1]"), `lem_GbEXP_BA` `:1916-1946`, `lem_ConArg_BA` `:1956-1981`; band source
`paper/tex/3_5_Loop_Hierarchy.tex` Step 1 `:64-66`.  Namespace `RBM.BA`.

Ports (cited `file:line` at the merged commit): `Induction/Step1.lean` at `b969625` (all of
sections 1-4 are private there): `s1x` `:91`, `s1a` `:95`, `s1f` `:99`, `s1_wl_seq` `:130`,
`s1Net` `:224`, `s1Net_mem` `:228`, `s1_exists_close` `:235`, `s1_forb` `:262`,
`s1x_continuousOn` `:372`, `s1_boot` `:398`, `s1_weakPT` `:431`, `s1_perTime_timeIcc` `:455`,
`s1_loopPT` `:474`, `step1TargetV3_holds` `:525`; `BA/Step1Setup.lean` at `8bb6f82`
(`BASetup_norm_BAmF_le_one` `:1048`).  The scale facts and the `≺` calculus are imported, not
copied: `Induction/Step1Setup.lean` at `4f186cf` (`S1Std` `:237`, `s1_F3`-`s1_F8` `:356-504`,
`s1_ratio_ev` `:340`, `s1_stochDom_unit` `:586`) and `Induction/PerTimeCalc.lean` at `5d1e6b1`.

* section 0: the vocabulary `FlowFM.gmMax` (`‖G_v - M‖_max` of a carrier; the band's `s1x`) and
  helpers;
* section 1: target 1 `baS1_wl_seq` (the weak-law step at one time sequence);
* section 2: target 2 `baS1_forb` (the net and the forbidden region for all `u ∈ [s,t]`);
* section 3: target 3 `baS1_boot` (the continuity argument), target 4 `baS1_weakPT`, target 5
  `baS1_loopPT`;
* section 4: target 6 `baBootstrap'_holds` (the pin `BABootstrap'` of `BA/Step1Boot.lean` from
  the three owed pins `BAFlowMember`, `BAGbEXPii`, `BAGbEXPij`);
* section 5: compiled nonempty instances (`RBM.BA.Step1Inst`).

The event threshold of the loop input is `C₀ = 1 + κm⁻¹` (`|M_xy| ≤ (Im m)⁻¹`, `baM_entry_le`)
in place of the band's `2`; the loop input at `k = 2` is the uniform `PrecL` (event from
`perTimeCalc_highProbAt_of_stochDomAt`); the vocabulary is `‖G_u - M‖_max` over the carrier
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

/-! ## 0. Vocabulary: `‖G_v - M‖_max` of a carrier -/

/-- `‖G_v - M‖_max` of a flow carrier at size index `n`, time `v`, sample `ω` (the band `s1xM`,
`Induction/Step1Setup.lean:913`, is the `bandFM` case with `llErrMat` entries; the band `s1x`,
`Induction/Step1.lean:91`, is private). -/
noncomputable def FlowFM.gmMax {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖C.GM n v ω q.1 q.2‖)

section Helpers

variable {d : ℕ}

/-- Each entry is at most `gmMax` (band `s1xM_ge`, `Induction/Step1Setup.lean:917`). -/
private theorem BAStep1_le_gmMax {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖C.GM n v ω x y‖ ≤ C.gmMax n v ω :=
  Finset.le_sup' (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖C.GM n v ω q.1 q.2‖)
    (Finset.mem_univ (x, y))

/-- `gmMax ≤ B` from the entries (band `s1xM_le`, `Induction/Step1Setup.lean:922`). -/
private theorem BAStep1_gmMax_le {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) {B : ℝ}
    (h : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n v ω x y‖ ≤ B) : C.gmMax n v ω ≤ B :=
  Finset.sup'_le _ _ fun q _ => h q.1 q.2

/-- `0 ≤ gmMax` (band `s1xM_nonneg`, `Induction/Step1Setup.lean:926`). -/
private theorem BAStep1_gmMax_nonneg {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) :
    0 ≤ C.gmMax n v ω := by
  obtain ⟨i⟩ : Nonempty (Idx d (sz.L n) (sz.W n)) := inferInstance
  exact (norm_nonneg _).trans (BAStep1_le_gmMax C n v ω i i)

/-- One-sided Lipschitz bound of `gmMax` in the resolvent entries (band `s1xM_le_add`,
`Induction/Step1Setup.lean:954`): `M` is time independent, so `GM_u - GM_{u'} = BAGt_u - BAGt_{u'}`. -/
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
band `s1x_continuousOn`, `Induction/Step1.lean:372`). -/
private theorem BAStep1_gmMax_continuousOn (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hm : 0 < (BAmF sz lam0 E n).im) {a b : ℝ} (hb : b < 1) (ω : sz.SeqΩ) :
    ContinuousOn (fun v : ℝ => (baFM sz lam0 E).gmMax n v ω) (Set.Icc a b) := by
  unfold FlowFM.gmMax
  exact ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun q _ =>
    (baG_continuousOn d sz lam0 E n hm a b hb ω q.1 q.2).norm

/-- `|m| ≤ 1` for `m = m(E, g₀)` when `Im m > 0` (copy of the private `BASetup_norm_BAmF_le_one`,
`BA/Step1Setup.lean:1048` at `8bb6f82`). -/
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
`Induction/Step1.lean:224` at `b969625`). -/
private def BAStep1_net (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

/-- Copy of `s1Net_mem`, `Induction/Step1.lean:228`. -/
private theorem BAStep1_net_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : BAStep1_net s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

/-- Copy of `s1_exists_close`, `Induction/Step1.lean:235`. -/
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
`s1_perTime_timeIcc`, `Induction/Step1.lean:455`). -/
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

/-! ## 1. Target 1: the weak-law step at one time sequence (band `s1_wl_seq`, `Induction/Step1.lean:130`) -/

section WeakLawSeq

open RBM.Ind FlowFM

/-- **Target 1** (`baS1_wl_seq_stmt`; band `s1_wl_seq`, `Induction/Step1.lean:130`, `5-6:60-63`): the weak-law step at
one time sequence `u ∈ [s,t]`: `1(‖G_u - M‖_max ≤ 2 a_s^{1/4}) ‖G_u - M‖_max ≺ 2·3^d a_s^{7/15}` per time,
`a_s = W^{-d}B_{s,0}`.  The inputs are `(GiiGEX)`, `(GijGEX)` at `ε₀ = c'` of `s1_F5` (so that `Ω(u, c')` holds on the
event), the **uniform** loop input at `k = 2` with `s1_ratio_ev` (the loops `≺ a_s^{14/15}`; its event is
`perTimeCalc_highProbAt_of_stochDomAt`) and the deterministic core `flowFM_wl_det` at `C₀ = 1 + κm⁻¹` (on the event
`‖G - M‖_max ≤ 2a ≤ W^{-c'} ≤ 1`, `‖G_xy‖ ≤ ‖M_xy‖ + 1 ≤ κm⁻¹ + 1` by `baM_entry_le`). -/
theorem baS1_wl_seq (d : ℕ) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun _ => Unit)
        (fun n _ ω => {ω | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}.indicator
          (fun ω => gmMax (baFMz sz z') n (u n) ω) ω)
        (fun n _ _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hLI hGii hGij u hu
  have hsize := s1_hsize sz h.hN
  obtain ⟨c', hc', hF5⟩ := s1_F5 h
  have hGij' := hGij u hu c' hc'
  have hGii' := hGii u hu c' hc'
  have hLI2 := hLI u hu 2 (by norm_num)
  refine s1_pt_of_highProb fun τ' hτ' => ?_
  have Ev1 := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hGij' hτ'
  have Ev2 := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hGii' hτ'
  have Ev3 := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hLI2 hτ'
  have EvAll := PerTimeCalc.perTimeCalc_highProbAt_inter hsize
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize Ev1 Ev2) Ev3
  refine PerTimeCalc.perTimeCalc_highProbAt_mono EvAll ?_
  filter_upwards [hF5, s1_F8 h, s1_ratio_ev h] with n hn5 hn8 hnr
  rintro ω ⟨⟨h1, h2⟩, h3⟩ ⟨⟩
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := s1_one_le_size sz n
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
  have hBs := s1_B_pos h n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hgr : (sz.Bctl n (s n)) ^ ((14 : ℝ) / 15) = ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hBs.le]; norm_num
  have hQ1 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hLoop : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) σ b ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ' * (sz.Bctl n (s n)) ^ ((14 : ℝ) / 15) := fun σ b => by
    have hb := h3 (σ, b)
    have hz : ((1 - s n) / (1 - u n)) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤
        (sz.Bctl n (s n)) ^ ((14 : ℝ) / 15) := by
      have := hnr (u n) (hu n).1 (hu n).2
      simpa [mul_comm] using this
    exact hb.trans (mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  change {ω | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}.indicator
      (fun ω => gmMax (baFMz sz z') n (u n) ω) ω ≤
    ((sz.size n : ℕ) : ℝ) ^ τ' * ((2 * (3 : ℝ) ^ d) * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))
  by_cases hx : gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)
  · rw [Set.indicator_of_mem (s := {ω : sz.SeqΩ | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)})
      (a := ω) hx]
    have hxe : ∀ x y : Idx d (sz.L n) (sz.W n),
        ‖(baFMz sz z').GM n (u n) ω x y‖ ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) :=
      fun x y => (BAStep1_le_gmMax (baFMz sz z') n (u n) ω x y).trans hx
    have hmpos : 0 < (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := hκm.trans_le (hmκ n)
    have hG : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z').G n (u n) ω x y‖ ≤ 1 + κm⁻¹ := by
      intro x y
      have h1' := norm_le_norm_sub_add ((baFMz sz z').G n (u n) ω x y) ((baFMz sz z').M n x y)
      have h2' := hxe x y
      change ‖(baFMz sz z').G n (u n) ω x y - (baFMz sz z').M n x y‖ ≤ _ at h2'
      have h3' : ‖(baFMz sz z').M n x y‖ ≤ ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ :=
        baM_entry_le d sz (BAflowLam0 sz z') (BAflowEs sz z') n hmpos x y
      have h4' : ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ ≤ κm⁻¹ :=
        inv_anti₀ hκm (hmκ n)
      have h5' : ((sz.W n : ℕ) : ℝ) ^ (-c') ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
      linarith
    have hent := flowFM_wl_det d sz (baFMz sz z') n ω (u n) ((sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)) c'
      ((sz.Bctl n (s n)) ^ ((14 : ℝ) / 15)) (((sz.size n : ℕ) : ℝ) ^ τ') (1 + κm⁻¹) hc' hxe hn5 hNτ
      (Real.rpow_nonneg hBs.le _) hn8 hG hLoop (fun p => h2 p) (fun p => h1 p)
    refine BAStep1_gmMax_le (baFMz sz z') n (u n) ω fun i j => ?_
    have hij := hent i j
    rw [hgr, h9] at hij
    have hA0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by linarith
    have hB0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) :=
      mul_nonneg hA0 (by positivity)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 ?_
    have h5 : (2 * ((3 : ℝ) ^ d) ^ 2 + 1) * ((((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
        ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2) ≤
        (((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))) ^ 2 := by
      have e2 : (((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))) ^ 2 =
          (4 * ((3 : ℝ) ^ d) ^ 2) * ((((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
            ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2) := by ring
      rw [e2]
      have h6 : 2 * ((3 : ℝ) ^ d) ^ 2 + 1 ≤ 4 * ((3 : ℝ) ^ d) ^ 2 := by nlinarith
      have h7 : 0 ≤ (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 * ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right h6 h7
    calc ‖(baFMz sz z').GM n (u n) ω i j‖ ^ 2
        ≤ (2 * ((3 : ℝ) ^ d) ^ 2 + 1) * (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
            ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := hij
      _ = (2 * ((3 : ℝ) ^ d) ^ 2 + 1) * ((((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
            ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2) := by ring
      _ ≤ _ := h5
  · rw [Set.indicator_of_notMem (s := {ω : sz.SeqΩ | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)})
      (a := ω) hx]
    exact mul_nonneg (by linarith) (by positivity)

end WeakLawSeq

/-! ## 2. Target 2: the net and the forbidden region for all `u ∈ [s,t]` (band `s1_forb`, `Induction/Step1.lean:262`) -/

section Net

open RBM.Ind FlowFM

/-- **Target 2** (`baS1_forb_stmt`; band `s1_forb`, `Induction/Step1.lean:262`, `5-6:13-16`, `5-6:64-68`): the
forbidden region for all `u ∈ [s,t]` simultaneously: w.h.p. `‖G_u - M‖_max ≠ a_s^{1/4}` for every `u ∈ [s,t]`.  The
per-sequence bound `baS1_wl_seq` is used at the points of a polynomial net (`#net ≤ N^{C'+1}`, `C'` the witness of
`baGopbound` at `C = 1`), the union bound over the net is `Unif.forbidden_region` (the band `[a/2, 2a]`,
`f = 2·3^d a_s^{7/15} ≪ a/2` by `s1_F4`) and the passage to all `u` is `baGopbound` (the mesh `N^{-C'}` moves
`‖G_u - M‖_max` by at most `N⁻¹ ≤ a/2`, `s1_F6`; `M` is time independent, `BAStep1_gmMax_le_add`). -/
theorem baS1_forb (d : ℕ) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) ∨
        (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) < gmMax (baFMz sz z') n (u : ℝ) ω}) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij
  have hsize := s1_hsize sz h.hN
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [h.hs0 n, h.ht1 n]
  obtain ⟨C', hC', hgop⟩ := baGopbound d sz (BAflowLam0 sz z') (BAflowEs sz z') κm hκm hmκ hm1 h.hN 1 one_pos
  obtain ⟨ε, hε, hF4⟩ := s1_F4 h
  -- the net-level forbidden region
  have hpt : PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (U := fun l => Fin (netSize C' (sz.size l) + 1))
      (fun l k ω => {ω : sz.SeqΩ | gmMax (baFMz sz z') l (BAStep1_net s t C' (sz.size l) l k) ω ≤
          2 * (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4)}.indicator
        (fun ω => gmMax (baFMz sz z') l (BAStep1_net s t C' (sz.size l) l k) ω) ω)
      (fun l _ _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl l (s l)) ^ ((7 : ℝ) / 15)) := by
    rw [perTimeDomAt_iff_forall_section (Sizes.seqP (sz.withLam 0)) sz.size (fun l => ⟨0⟩)]
    intro sec
    exact s1_stochDom_unit (baS1_wl_seq d sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hLI hGii hGij
      (fun n => BAStep1_net s t C' (sz.size n) n (sec n))
      (fun n => BAStep1_net_mem h.hst C' (sz.size n) n (sec n)))
  have hnetSD := stochDomAt_of_perTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (C := C' + 1)
    (by linarith) (hsize.eventually (card_net_le hC'.le)) hpt
  have hnet := PerTimeCalc.Unif.forbidden_region hsize
    (x := fun l (k : Fin (netSize C' (sz.size l) + 1)) (ω : sz.SeqΩ) =>
      gmMax (baFMz sz z') l (BAStep1_net s t C' (sz.size l) l k) ω)
    (f := fun l _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl l (s l)) ^ ((7 : ℝ) / 15))
    (a := fun l _ => (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4) / 2)
    (b := fun l _ => 2 * (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4))
    (fun l _ => by
      have := Real.rpow_pos_of_pos (s1_B_pos h l) ((1 : ℝ) / 4)
      positivity) hε
    (by filter_upwards [hF4] with l hl _; exact hl) hnetSD
  -- the good event of `baGopbound`
  have hgood : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω : sz.SeqΩ | ¬ (∃ u u' : ℝ,
        0 ≤ u ∧ 0 ≤ u' ∧ u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
        |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
        ∃ x y : Idx d (sz.L n) (sz.W n),
          ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) <
            ‖BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u ω x y -
              BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u' ω x y‖)}) := by
    intro D hD
    filter_upwards [hgop D hD] with n hn
    refine le_trans (measure_mono ?_) hn
    intro ω hω
    exact not_not.1 hω
  refine PerTimeCalc.perTimeCalc_highProbAt_mono
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize hnet hgood) ?_
  filter_upwards [h.hR, s1_F6 h] with n hR hF6
  rintro ω ⟨hω1, hω2⟩ u
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := s1_one_le_size sz n
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨k, hk⟩ := BAStep1_exists_close hlen C' (sz.size n) n u.2
  have hθ := BAStep1_net_mem h.hst C' (sz.size n) n k
  have hdist : |(u : ℝ) - BAStep1_net s t C' (sz.size n) n k| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') := by
    refine hk.trans ?_
    have h1 : ((sz.size n : ℕ) : ℝ) ^ C' ≤ (netSize C' (sz.size n) : ℝ) :=
      rpow_le_netSize C' (sz.size n)
    calc 1 / (netSize C' (sz.size n) : ℝ) ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ C' :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _) h1
      _ = ((sz.size n : ℕ) : ℝ) ^ (-C') := by rw [Real.rpow_neg hN0.le, one_div]
  have hrange : ∀ v ∈ Set.Icc (s n) (t n), v ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ := by
    intro v hv
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [h.hτ])
    rw [Real.rpow_neg_one] at h1
    linarith [hv.2]
  have hgop1 : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u ω x y -
        BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n (BAStep1_net s t C' (sz.size n) n k) ω x y‖ ≤
      ((sz.size n : ℕ) : ℝ)⁻¹ := by
    intro x y
    by_contra hlt
    push Not at hlt
    refine hω2 ⟨u, BAStep1_net s t C' (sz.size n) n k, (h.hs0 n).trans u.2.1, (h.hs0 n).trans hθ.1,
      hrange u u.2, hrange _ hθ, hdist, x, y, ?_⟩
    rwa [Real.rpow_neg_one]
  have hgop2 : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n (BAStep1_net s t C' (sz.size n) n k) ω x y -
        BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u ω x y‖ ≤ ((sz.size n : ℕ) : ℝ)⁻¹ :=
    fun x y => by rw [norm_sub_rev]; exact hgop1 x y
  have hup : (baFMz sz z').gmMax n u ω ≤
      (baFMz sz z').gmMax n (BAStep1_net s t C' (sz.size n) n k) ω + ((sz.size n : ℕ) : ℝ)⁻¹ :=
    BAStep1_gmMax_le_add sz (BAflowLam0 sz z') (BAflowEs sz z') n u _ _ ω hgop1
  have hdown : (baFMz sz z').gmMax n (BAStep1_net s t C' (sz.size n) n k) ω ≤
      (baFMz sz z').gmMax n u ω + ((sz.size n : ℕ) : ℝ)⁻¹ :=
    BAStep1_gmMax_le_add sz (BAflowLam0 sz z') (BAflowEs sz z') n _ u _ ω hgop2
  have hapos : 0 < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (s1_B_pos h n) _
  have hF6' : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) / 2 := hF6
  rcases hω1 k with h1 | h1
  · left
    change gmMax (baFMz sz z') n (BAStep1_net s t C' (sz.size n) n k) ω <
      (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) / 2 at h1
    linarith
  · right
    change 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) <
      gmMax (baFMz sz z') n (BAStep1_net s t C' (sz.size n) n k) ω at h1
    linarith

end Net

/-! ## 3. Targets 3-5: the continuity argument and the two per-time conclusions
(band `Bootstrap`, `Induction/Step1.lean:362-511`) -/

section Bootstrap

open RBM.Ind FlowFM

/-- **Target 3** (`baS1_boot_stmt`; band `s1_boot`, `Induction/Step1.lean:398`, `5-6:68-70`): the continuity argument:
w.h.p. `‖G_u - M‖_max < a_s^{1/4}` for every `u ∈ [s,t]`.  The initial condition is `STLocalMaxgL` at `s`
(`≺ a_s^{1/2}`, `s1_F3`), the continuity of `u ↦ ‖G_u - M‖_max` is `BAStep1_gmMax_continuousOn` (`baG_continuousOn`),
the forbidden region is `baS1_forb`, the argument is `stepOneBootstrap`. -/
theorem baS1_boot (d : ℕ) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  have hsize := s1_hsize sz h.hN
  -- the initial condition
  have hinit : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size
      (fun n => {ω : sz.SeqΩ | gmMax (baFMz sz z') n (s n) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}) := by
    obtain ⟨τ₀, hτ₀, hF3⟩ := s1_F3 h
    have hev := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hIL hτ₀
    refine PerTimeCalc.perTimeCalc_highProbAt_mono hev ?_
    filter_upwards [hF3] with n hn ω hω
    have hb : (baFMz sz z').gmMax n (s n) ω ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₀ * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 2) :=
      BAStep1_gmMax_le (baFMz sz z') n (s n) ω fun x y => hω (x, y)
    exact lt_of_le_of_lt hb hn
  have hcont : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun l => {ω : sz.SeqΩ | ContinuousOn
      (fun u => gmMax (baFMz sz z') l u ω) (Set.Icc (s l) (t l))}) :=
    PerTimeCalc.perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun l ω _ =>
        BAStep1_gmMax_continuousOn sz (BAflowLam0 sz z') (BAflowEs sz z') l (hκm.trans_le (hmκ l))
          (h.ht1 l) ω)
  exact PerTimeCalc.stepOneBootstrap hsize (M := fun l v (ω : sz.SeqΩ) => gmMax (baFMz sz z') l v ω)
    (a := fun l _ => (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4)) (b := fun l _ => (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4))
    (s := s) (t := t) hcont (fun l => continuousOn_const) (Eventually.of_forall fun l u => le_rfl)
    (baS1_forb d sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij) hinit

/-- **Target 4** (`baS1_weakPT_stmt`; `(Gtmwc)` per time over `[s,t]`; band `s1_weakPT`, `Induction/Step1.lean:431`,
`5-6:70`): `‖(G_u - M)_xy‖ ≺ (W^{-d}B_{u,0})^{1/4}` uniformly in `u ∈ [s,t]`, per time.  `a_s^{1/4} ≤ a_u^{1/4}` is
`STBctl_mono`.  The left side and the bound are those of the second hypothesis of `baNetLift`. -/
theorem baS1_weakPT (d : ℕ) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(baFMz sz z').GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  have hsize := s1_hsize sz h.hN
  have hboot := baS1_boot d sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  refine PerTimeCalc.PerTime.stochDom_of_highProb hsize (fun n p ω =>
    Real.rpow_nonneg (s1_Bu_pos h n p.1.2.2).le _) ?_
  refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot (Eventually.of_forall fun n ω hω p => ?_)
  obtain ⟨u, i, j⟩ := p
  have h1 := BAStep1_le_gmMax (baFMz sz z') n (u : ℝ) ω i j
  have h2 := hω u
  have h3 : sz.Bctl n (s n) ≤ sz.Bctl n u :=
    sz.STBctl_mono n u.2.1 (lt_of_le_of_lt u.2.2 (h.ht1 n))
  have h4 : (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) ≤ (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (s1_B_pos h n).le h3 (by norm_num)
  exact (h1.trans h2.le).trans h4

/-- **Target 5** (`baS1_loopPT_stmt`; `(lRB1)` per time over `[s,t]`; band `s1_loopPT`, `Induction/Step1.lean:474`,
`5-6:70`): `|𝓛_{u,σ,a}| ≺ ((1-s)/(1-u))^{k-1} (W^{-d}B_{s,0})^{k-1}` uniformly in `u ∈ [s,t]`, per time: the
indicator `omegaC (1 + κm⁻¹)` of the `baBoot_LI` output is removed on the event of target 3
(`‖G_u‖_max ≤ ‖M‖_max + ‖G_u - M‖_max < κm⁻¹ + a_s^{1/4} ≤ κm⁻¹ + 1`, `s1_F7`, `baM_entry_le`); the loop input per
`u` is `PrecL` (uniform), made per time by `perTimeOfStochDomAt` and lifted to `TimeIcc s t n × loops` by
`BAStep1_perTime_timeIcc` (copy of the band's private `s1_perTime_timeIcc`).  The left side and the bound are those of
the first hypothesis of `baNetLift`. -/
theorem baS1_loopPT (d : ℕ) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    ∀ k : ℕ, 1 ≤ k →
      PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖(baFMz sz z').L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL k hk
  have hsize := s1_hsize sz h.hN
  have hboot := baS1_boot d sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  refine PerTimeCalc.PerTime.stochDom_of_indicator hsize
    (Ωs := fun n p => {ω : sz.SeqΩ | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖(baFMz sz z').G n (p.1 : ℝ) ω x y‖ ≤ 1 + κm⁻¹}) ?_ ?_
  · refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot ?_
    filter_upwards [s1_F7 h] with n hF7 ω hω p x y
    have hmpos : 0 < (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := hκm.trans_le (hmκ n)
    have h1 := norm_le_norm_sub_add ((baFMz sz z').G n (p.1 : ℝ) ω x y) ((baFMz sz z').M n x y)
    have h2 := BAStep1_le_gmMax (baFMz sz z') n (p.1 : ℝ) ω x y
    have h3 := hω p.1
    have h4 : ‖(baFMz sz z').M n x y‖ ≤ ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ :=
      baM_entry_le d sz (BAflowLam0 sz z') (BAflowEs sz z') n hmpos x y
    have h5 : ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ ≤ κm⁻¹ :=
      inv_anti₀ hκm (hmκ n)
    change ‖(baFMz sz z').G n (p.1 : ℝ) ω x y - (baFMz sz z').M n x y‖ ≤ _ at h2
    change (baFMz sz z').gmMax n (p.1 : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) at h3
    change ‖(baFMz sz z').G n (p.1 : ℝ) ω x y‖ ≤ 1 + κm⁻¹
    linarith
  · have key : PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (p.1 : ℝ) (1 + κm⁻¹) ω *
          ‖(baFMz sz z').L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) :=
      BAStep1_perTime_timeIcc (Sizes.seqP (sz.withLam 0)) sz.size h.hst
        (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
        (fun n v q (ω : sz.SeqΩ) => (baFMz sz z').omegaC n v (1 + κm⁻¹) ω * ‖(baFMz sz z').L n v q.1 q.2 ω‖)
        (fun n v _ _ => ((1 - s n) / (1 - v)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
        (fun u hu => perTimeOfStochDomAt (Sizes.seqP (sz.withLam 0)) sz.size _ _ (hLI u hu k hk))
    refine PerTimeCalc.PerTime.stochDom_of_le_left_eventually
      (Eventually.of_forall fun n p ω => le_of_eq ?_) key
    by_cases hg : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z').G n (p.1 : ℝ) ω x y‖ ≤ 1 + κm⁻¹
    · simp [Set.indicator, FlowFM.omegaC, hg]
    · simp [Set.indicator, FlowFM.omegaC, hg]

end Bootstrap

/-! ## 4. Target 6: `baBootstrap'_holds` (band `step1TargetV3_holds`, `Induction/Step1.lean:525`) -/

section Main

open RBM.Ind FlowFM

/-- **Target 6** (`baBootstrap'_holds_stmt`; band `step1TargetV3_holds`, `Induction/Step1.lean:525`): the merged pin
`BABootstrap'` (`BA/Step1Boot.lean:148`, unchanged) from the owed `BAFlowMember`, `BAGbEXPii`, `BAGbEXPij`.
Proof: `baS1Std` (main flow `z`, `τ = ε/2`, `Ed ≡ 0`); `κm = κ` by `BAFamZ_mono` (to `Fam(0)`) and
`BAFamZ_im_m_ge`; `|m| ≤ 1` (`BAStep1_norm_BAmF_le_one`, copy of `BASetup_norm_BAmF_le_one`); `baBoot_LI` at
`C₀ = 1 + κ⁻¹` with the loop half of the ConArg premise; `baGii_member`, `baGij_member` at `u ∈ [s,t]`; targets 4, 5
and `baNetLift` at `lam0 = BAflowLam0 sz z'`, `E = BAflowEs sz z'`, `τ = ε/2`.  The premises `STKboundgL`, `STLKgL`,
`BAConArgVec` and `s ≤ t₀(z)` of the pin are not used (paper-delta candidate T2269b). -/
theorem baBootstrap'_holds (d : ℕ) : BAFlowMember d → BAGbEXPii d → BAGbEXPij d → BABootstrap' d := by
  intro hmem hii hij κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT z' hfam
    hK hLK hLoc hCond hcon
  have h := baS1Std d κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow s t hs0 (fun n => (hst n).le) htT hCond
  have hfam0 : BAFamZ sz z c₁ (fun _ => 0) z' :=
    BAFamZ_mono (fun n => (hs0 n).trans (hst n).le) hfam
  have him : ∀ n, κ ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im :=
    BAFamZ_im_m_ge hκ hflow hlam hc₁ hc₁' hwin hfam0
  have hm1 : ∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1 := fun n =>
    BAStep1_norm_BAmF_le_one sz _ _ n (hκ.trans_le (him n))
  have hLI := baBoot_LI d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 (fun n => (hst n).le) htT z'
    hfam (fun u h1 h2 => (hcon u h1 h2).1) (1 + κ⁻¹) (by positivity)
  have hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀ :=
    fun u hu ε₀ hε₀ => baGii_member d hii hmem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u
      (fun n => (hs0 n).trans (hu n).1) (fun n => (hu n).2) ε₀ hε₀
  have hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀ :=
    fun u hu ε₀ hε₀ => baGij_member d hij hmem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u
      (fun n => (hs0 n).trans (hu n).1) (fun n => (hu n).2) ε₀ hε₀
  have hnet := baNetLift d sz (BAflowLam0 sz z') (BAflowEs sz z') κ (ε / 2) s t hκ him hm1 (half_pos hε) hs0
    (fun n => (hst n).le) h.ht1 h.hN h.hR
  exact ⟨hnet.1 (baS1_loopPT d sz z' (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d κ (fun _ => 0) s t h hκ him hm1 hLI hGii hGij hLoc),
    hnet.2 (baS1_weakPT d sz z' (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d κ (fun _ => 0) s t h hκ him hm1 hLI hGii hGij hLoc)⟩

end Main

end RBM.BA

/-! ## 5. Compiled nonempty instances (`RBM.BA.Step1Inst`)

The size data are the merged preflight sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`g_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the spectral parameters `zSeq`
(`BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` is `flow_sz0`), the member `z' = zSeq` (`BAFamZ_main`), `κ = 1/2`,
`ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`, `c₁ = 1/3` (so `s₁ = max(s, 2/3) = 2/3`), `s ≡ 1/2` (`sI`), `t ≡ 2/3` (`tI`;
`2/3 ≤ t₀`, `t0_sz0`).  Every deterministic hypothesis is discharged: `S1Std` (`inst_baS1Std`), `Im m ≥ 1/2`
(`inst_im_m_ge`), `|m| ≤ 1` (`inst_norm_m_le`), `STConStInd` (`s1Setup_conStInd_const`, an eventual statement), the
times, and the ConArg premise of `BABootstrap'` (both halves, from `baConArg''_holds 3`, `BATrivialLmax_holds`; only
the window is a hypothesis).  What stays a hypothesis: the owed pins `BAFlowMember 3`, `BAGbEXPii 3`, `BAGbEXPij 3`,
the window `hwin : BAWinBulk sz0 zSeq (1/3) (1/2)` (external; as T2238, T2256), and the initial data `STKboundgL`,
`STLKgL`, `STLocalMaxgL` of `baFMz sz0 zSeq` at `sI` (other gates).  The conclusions of the instances are `∀ᶠ`
statements; they claim no value at a finite `n`. -/

namespace RBM.BA.Step1Inst

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA.FlowPinsInst RBM.Gauss.SizesInst
  RBM.BA.Step1SetupInst RBM.BA.Step1BootInst

/-- The coupling `g_s = √(s₁/u') g₀` with `s₁ = u' = 2/3` is `g₀` (copy of the private `lamS_two_thirds`,
`BA/Step1Boot.lean:740`). -/
private theorem lamS_two_thirds' : BAlamS sz0 zSeq (fun _ => 2 / 3) (fun _ => 2 / 3) = BAflowLam0 sz0 zSeq := by
  funext n
  unfold BAlamS
  norm_num

/-- **The ConArg premise of `BABootstrap'`** at `s ≡ 1/2`, `t ≡ 2/3`, `c₁ = 1/3`, both halves (the range
`{u : s₁ ≤ u ≤ max(t, 1 - c₁)}` is `{u ≡ 2/3}`): the loop half is `inst_hcon`'s, the `BAConArgVec` half is
`(baConArg''_holds 3 ...).2` at the same data (`hκm`, `hL`: `BAFamZ_im_m_ge`, `BATrivialLmax_holds`); only the window
is a hypothesis. -/
theorem inst_hcon_full (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    ∀ u : ℕ → ℝ, (∀ n, max (sI n) (1 - 1 / 3) ≤ u n) → (∀ n, u n ≤ max (tI n) (1 - 1 / 3)) →
      (∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k →
          BAConArgLoop'' sz0 zSeq (fun n => max (sI n) (1 - 1 / 3)) u k C₀) ∧
        BAConArgVec sz0 zSeq (fun n => max (sI n) (1 - 1 / 3)) u := by
  intro u h1 h2
  have hu : u = fun _ => 2 / 3 := by
    funext n
    have a1 := h1 n
    have a2 := h2 n
    norm_num [sI, tI] at a1 a2
    exact le_antisymm a2 a1
  have hs₁ : (fun n : ℕ => max (sI n) (1 - 1 / 3)) = fun _ => (2 / 3 : ℝ) := by
    funext n
    norm_num [sI]
  rw [hu, hs₁]
  have hκm : ∀ n, (1 / 2 : ℝ) ≤
      (BAmF sz0 (BAlamS sz0 zSeq (fun _ => 2 / 3) (fun _ => 2 / 3)) (BAflowEs sz0 zSeq) n).im := by
    intro n
    rw [lamS_two_thirds']
    exact BAFamZ_im_m_ge (by norm_num) flow_sz0 sz0_lam_pos (by norm_num) (by norm_num) hwin
      (BAFamZ_main sz0 zSeq (1 / 3) (fun _ => 0)) n
  have hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 2 / 3) (fun _ => 2 / 3)) (BAflowEs sz0 zSeq))
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 2 / 3) := by
    rw [lamS_two_thirds']
    have h := BATrivialLmax_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
      sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin zSeq
      (BAFamZ_main sz0 zSeq (1 / 3) (fun _ => 0))
    have e : (fun _ : ℕ => (1 : ℝ) - 1 / 3) = fun _ => 2 / 3 := by
      funext n
      norm_num
    rw [e] at h
    exact h
  have key := fun (C₀ : ℝ) (hC₀ : 0 < C₀) => baConArg''_holds 3 (1 / 2) (1 / 10) (1 / 10) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 2 / 3) (fun _ => 2 / 3)
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num) hκm hL C₀ hC₀
  exact ⟨fun C₀ hC₀ k hk => (key C₀ hC₀).1 k hk, (key 1 one_pos).2⟩

/-- The loop input of targets 1-5 at the data: `baBoot_LI` at `C₀ = 1 + (1/2)⁻¹ = 3`, every `u ∈ [1/2, 2/3]`,
every `k ≥ 1`; the ConArg premise is `inst_hcon_full`. -/
theorem inst_hLI (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (sI n) (tI n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => (baFMz sz0 zSeq).omegaC n (u n) (1 + (1 / 2 : ℝ)⁻¹) ω *
          ‖(baFMz sz0 zSeq).L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - sI n) / (1 - u n)) ^ (k - 1) * (sz0.Bctl n (sI n)) ^ (k - 1)) :=
  baBoot_LI 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin sI tI (fun _ => by norm_num [sI])
    (fun _ => by norm_num [sI, tI]) (fun n => t0_sz0 n) zSeq (BAFamZ_main sz0 zSeq (1 / 3) _)
    (fun u h1 h2 => (inst_hcon_full hwin u h1 h2).1) (1 + (1 / 2 : ℝ)⁻¹) (by norm_num)

/-- `(GiiGEX)` of the member `zSeq` at every `u ∈ [1/2, 2/3]` (`baGii_member`; the owed pins and the window are the
hypotheses). -/
theorem inst_hGii (hii : BAGbEXPii 3) (hmem : BAFlowMember 3) (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (sI n) (tI n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz0 zSeq u ε₀ :=
  fun u hu ε₀ hε₀ => baGii_member 3 hii hmem (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin tI (fun n => t0_sz0 n) zSeq
    (BAFamZ_main sz0 zSeq (1 / 3) tI) u (fun n => (show (0 : ℝ) ≤ sI n by norm_num [sI]).trans (hu n).1)
    (fun n => (hu n).2) ε₀ hε₀

/-- `(GijGEX)` of the member `zSeq` at every `u ∈ [1/2, 2/3]` (`baGij_member`). -/
theorem inst_hGij (hij : BAGbEXPij 3) (hmem : BAFlowMember 3) (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (sI n) (tI n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz0 zSeq u ε₀ :=
  fun u hu ε₀ hε₀ => baGij_member 3 hij hmem (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin tI (fun n => t0_sz0 n) zSeq
    (BAFamZ_main sz0 zSeq (1 / 3) tI) u (fun n => (show (0 : ℝ) ≤ sI n by norm_num [sI]).trans (hu n).1)
    (fun n => (hu n).2) ε₀ hε₀

/-- **Instance of `baS1_wl_seq`** (target 1): the data above, the time sequence `u ≡ 2/3 ∈ [1/2, 2/3]`, `κm = 1/2`;
the owed pins `BAGbEXPii 3`, `BAGbEXPij 3`, `BAFlowMember 3` and the window are hypotheses. -/
theorem inst_baS1_wl_seq (hmem : BAFlowMember 3) (hii : BAGbEXPii 3) (hij : BAGbEXPij 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size (U := fun _ => Unit)
      (fun n _ ω => {ω | (baFMz sz0 zSeq).gmMax n ((fun _ => (2 / 3 : ℝ)) n) ω ≤
          2 * (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4)}.indicator
        (fun ω => (baFMz sz0 zSeq).gmMax n ((fun _ => (2 / 3 : ℝ)) n) ω) ω)
      (fun n _ _ => (2 * (3 : ℝ) ^ 3) * (sz0.Bctl n (sI n)) ^ ((7 : ℝ) / 15)) :=
  baS1_wl_seq 3 sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (1 / 2) (fun _ => 0) sI tI
    inst_baS1Std (by norm_num) inst_im_m_ge (inst_hLI hwin) (inst_hGii hii hmem hwin) (inst_hGij hij hmem hwin)
    (fun _ => 2 / 3) (fun _ => ⟨by norm_num [sI], by norm_num [tI]⟩)

/-- **Instance of `baS1_forb`** (target 2): the same data. -/
theorem inst_baS1_forb (hmem : BAFlowMember 3) (hii : BAGbEXPii 3) (hij : BAGbEXPij 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    HighProbAt (Sizes.seqP (sz0.withLam 0)) sz0.size (fun n => {ω | ∀ u : TimeIcc sI tI n,
      (baFMz sz0 zSeq).gmMax n (u : ℝ) ω < (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4) ∨
        (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4) < (baFMz sz0 zSeq).gmMax n (u : ℝ) ω}) :=
  baS1_forb 3 sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (1 / 2) (fun _ => 0) sI tI
    inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI hwin) (inst_hGii hii hmem hwin)
    (inst_hGij hij hmem hwin)

/-- **Instance of `baS1_boot`** (target 3): the same data; `STLocalMaxgL` of the carrier at `sI` (other gate's) is a
hypothesis. -/
theorem inst_baS1_boot (hmem : BAFlowMember 3) (hii : BAGbEXPii 3) (hij : BAGbEXPij 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2))
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    HighProbAt (Sizes.seqP (sz0.withLam 0)) sz0.size (fun n => {ω | ∀ u : TimeIcc sI tI n,
      (baFMz sz0 zSeq).gmMax n (u : ℝ) ω < (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4)}) :=
  baS1_boot 3 sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (1 / 2) (fun _ => 0) sI tI
    inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI hwin) (inst_hGii hii hmem hwin)
    (inst_hGij hij hmem hwin) hLoc

/-- **Instance of `baS1_weakPT`** (target 4): the same data. -/
theorem inst_baS1_weakPT (hmem : BAFlowMember 3) (hii : BAGbEXPii 3) (hij : BAGbEXPij 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2))
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size
      (U := fun n => TimeIcc sI tI n × Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
      (fun n p _ => (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) :=
  baS1_weakPT 3 sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (1 / 2) (fun _ => 0) sI tI
    inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI hwin) (inst_hGii hii hmem hwin)
    (inst_hGij hij hmem hwin) hLoc

/-- **Instance of `baS1_loopPT`** (target 5): the same data, every `k ≥ 1`. -/
theorem inst_baS1_loopPT (hmem : BAFlowMember 3) (hii : BAGbEXPii 3) (hij : BAGbEXPij 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2))
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    ∀ k : ℕ, 1 ≤ k →
      PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size
        (U := fun n => TimeIcc sI tI n × (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => ‖(baFMz sz0 zSeq).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - sI n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz0.Bctl n (sI n)) ^ (k - 1)) :=
  baS1_loopPT 3 sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (1 / 2) (fun _ => 0) sI tI
    inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI hwin) (inst_hGii hii hmem hwin)
    (inst_hGij hij hmem hwin) hLoc

/-- **Instance of `baBootstrap'_holds`** (target 6): `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠d = 1/100`, `𝔠 = 1/6`, `c₁ = 1/3`,
`s ≡ 1/2 < t ≡ 2/3 ≤ t₀`, the member `z' = zSeq`; `STConStInd` (`s1Setup_conStInd_const`) and both halves of the ConArg
premise (`inst_hcon_full`) are discharged.  The owed pins, the window and the initial data `STKboundgL`, `STLKgL`,
`STLocalMaxgL` are hypotheses.  Both conjuncts of the pin's conclusion are produced. -/
theorem inst_baBootstrap' (hmem : BAFlowMember 3) (hii : BAGbEXPii 3) (hij : BAGbEXPij 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2))
    (hK : STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)))
    (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI)
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧
      STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI :=
  baBootstrap'_holds 3 hmem hii hij (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100)
    (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin sI tI
    (fun _ => by norm_num [sI]) (fun n => (show sI n ≤ 2 / 3 by norm_num [sI]).trans (t0_sz0 n))
    (fun _ => by norm_num [sI, tI]) (fun n => t0_sz0 n) zSeq (BAFamZ_main sz0 zSeq (1 / 3) tI) hK hLK hLoc
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (s0 := 1 / 2) (t0 := 2 / 3) (by norm_num) (by norm_num)
      (by norm_num)) (inst_hcon_full hwin)

/-- **Instance of the vocabulary `FlowFM.gmMax`**: at `t = 0` the flow is `M` (`inst_GM_zero`), so `‖G_0 - M‖_max = 0`
(`n = 0`, every sample). -/
theorem inst_gmMax_zero (ω : sz0.SeqΩ) : (baFMz sz0 zSeq).gmMax 0 0 ω = 0 :=
  le_antisymm (BAStep1_gmMax_le (baFMz sz0 zSeq) 0 0 ω fun x y => by rw [inst_GM_zero ω x y, norm_zero])
    (BAStep1_gmMax_nonneg (baFMz sz0 zSeq) 0 0 ω)

end RBM.BA.Step1Inst
