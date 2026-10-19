/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step1Setup
import RBM3D.Induction.Continuity

/-!
# Step 1 of `lem:main_ind`, second part: the weak-law step, the net, the bootstrap, `step1`

Paper: arXiv:2507.20274, Step 1 of Theorem 2.24 (`lem:main_ind`): (2.85) `lRB1` and (2.86)
`Gtmwc`.  The proof of Step 1 (Section 3, with Lemma 3.1 `lem_GbEXP` and Lemma 3.2 `lem_ConArg`)
follows [YY_25, §5.1].  The first part of Step 1 is in `RBM3D/Induction/Step1Setup.lean`, which
is imported and not copied; this file contains the weak-law step, the net argument, the
continuity bootstrap and the assembly `step1`.  The argument follows the two-dimensional
formalization (RBM2D `Induction/Step1`).

## Contents

* `WeakLawSeq`: `s1x`, `s1a`, `s1f` (`s1f = 6 M_s^{-7/15}` is `2·3^d a_s^{7/15}`),
  `s1_card_loops` (`#((σ,a)) ≤ N^{2k}`), `s1_wl_seq` (the weak-law step at one time sequence:
  `lem_GbEXP` with `n = 2`).  The index sets `Unit × BlockIndex` of the two-dimensional version
  do not occur: `STGiiGEX`, `STGijGEX`, `STLocalMax` are `Prec` over `Idx × Idx` (`STGijGEX`:
  its off-diagonal part), so `Prec.whp` gives their events with no counting.
* `Net`: `s1Net`, `s1Net_mem`, `s1_exists_close` (copies of the `private` `contTime`,
  `contTime_mem`, `cont_exists_close` of `ContinuityNet.lean`), `s1_forb` (the forbidden region
  for all `u ∈ [s,t]`: `forbidden_region` on the net, `gopbound` to pass to all `u`).
* `Bootstrap`: `s1x_continuousOn`, `s1_boot` (the continuity argument; the initial event is
  `Prec.whp` of `STLocalMax`), `s1_weakPT` (`(Gtmwc)` per time), `s1_loopPT` (`(lRB1)` per time).
* `step1` is `step1TargetV3_holds : Step1TargetV3 d` (stated in `Step1Setup.lean`):
  `Step1TargetV3 d := STGbEXPii d → STGbEXPij d → STStep1 d`, proved for every `d` from the
  per-time statements and the net lift `step1NetLift` (`Continuity.lean`).

## Differences from the two-dimensional version

* `GbEXPHypV3 d (κ/2) c τ` (per size sequence and per `(c, τ)`) is the pair of hypotheses
  `STGbEXPii d`, `STGbEXPij d`, which quantify over every `κ ε 𝔡 𝔠 sz z t ε₀`; at a time
  sequence `u ∈ [s,t]` (`0 ≤ u ≤ t ≤ lemT z`) they give `STGiiGEX`, `STGijGEX` at
  `E = STflowE z`, `ε₀ = c'`.  The private lemmas take these two instances (`hGii`, `hGij`) as
  hypotheses, so no `z` occurs in them.
* `M_s⁻¹` is `a_s = sz.Bctl n s`, `6` is `C_d = 2·3^d` (`s1_F4`), the constant of `s1_wl_det` is
  `2·9^d + 1 ≤ (2·3^d)²`.  The events of `Prec.whp` replace `s1_highProb_of_pt` for the two
  statements (their index sets are `Idx × Idx` and `{p // p.1 ≠ p.2}`, `≺` is the uniform
  `Prec`); `s1_highProb_of_pt` is kept for `s1_LI` (`PrecPT` over `(σ, a)`), with
  `#((σ,a)) ≤ N^4`.
* `STomegaC` is the indicator `1(‖G‖_max ≤ 2)` of `s1_LI`; `STindMax`, `STmaxLoop2`, `STgexRHS`
  are those of `s1_wl_det`.  `s1_loopPT` removes `STomegaC` by `stochDom_of_indicator` and the
  bootstrap event `‖G_u - m‖_max < a_s^{1/4} ≤ 1`.
* `s1_perTime_timeIcc` is `Green.perTime_timeIcc_of_forall_seq` without the `Unit ×` factor
  (`s1_LI` is over `(σ, a)`).
* The net lift is `step1NetLift` for both halves.

## Time windows

`0 ≤ s` is used for the window length `t - s ≤ 1` (`hlen`), for `0 ≤ u` at the net points and at
the points handed to `gopbound` and to the two hypotheses `STGbEXPii`, `STGbEXPij`, and inside
the imported `s1_F6`, `s1_F8`, `s1_h55`, `s1_LI` (`S1Std.hs0`); `s < t` is only used as `s ≤ t`;
`t ≤ lemT z` gives `u ≤ lemT z` for the two hypotheses and `t < 1` (`S1Std.ht1`, `RangeCond`).
The facts about the net, the mesh and the pointwise bounds on `[s,t]` are `∀ n`, those needing
`a_s → 0` or `(eq:WO)` are `∀ᶠ n` (`s1_F3`-`s1_F8`, `S1Std.hR`).  Every constant (`2·3^d`,
`2·9^d + 1`, `C' = 2C + 14` at `C = 1`, `c₀/8`) depends on `d, κ, 𝔠, 𝔡, ε` only, not on
`W, L, ilambda`; no `ℓ` occurs and no `L^d ≤ W^K` is used (the counts use `L^d ≤ N`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The weak-law step at one time sequence -/

section WeakLawSeq

variable {d : ℕ} {sz : Sizes d} {κ 𝔠 𝔡 τ 𝔠d : ℝ} {E s t : ℕ → ℝ}

/-- `‖G_v - m‖_max` at the size index `n`, time `v`. -/
private abbrev s1x (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) : ℝ :=
  s1xM d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω)

/-- The threshold `a = a_s^{1/4}` (constant in `u`; RBM2D's `s1a`, `M_s^{-1/4}`). -/
private abbrev s1a (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) : ℝ := (s1B sz s n) ^ ((1 : ℝ) / 4)

/-- The bound `f = 2·3^d a_s^{7/15}` (constant in `u`; RBM2D's `s1f`,
`6 M_s^{-7/15}`; `C_d = 2·3^d` as in `s1_F4`). -/
private abbrev s1f (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 * (3 : ℝ) ^ d) * (s1B sz s n) ^ ((7 : ℝ) / 15)

/-- `#((Fin k → Bool) × (Fin k → Z_L^d)) = 2^k (L^d)^k ≤ N^{2k}` for `N ≥ 2`, `N = (W L)^d`
(RBM2D's `s1_card_loops`, `L·L ≤ N`; here `L^d ≤ (W L)^d = N`, no `L^d ≤ W^K`). -/
private theorem s1_card_loops (n k : ℕ) (hN2 : 2 ≤ sz.size n) :
    (Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ ((2 * k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have hZ : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by simp [Zd, ZMod.card]
  have hc : Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) = 2 ^ k * (sz.L n ^ d) ^ k := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      hZ]
  have hLN : sz.L n ^ d ≤ sz.size n := by
    have hW : 0 < sz.W n := sz.W_pos n
    have h1 : 1 ≤ sz.W n ^ d := Nat.one_le_pow d (sz.W n) hW
    have e : sz.size n = sz.W n ^ d * sz.L n ^ d := by simp [Sizes.size, mul_pow]
    rw [e]
    nlinarith [Nat.zero_le (sz.L n ^ d)]
  have key : 2 ^ k * (sz.L n ^ d) ^ k ≤ sz.size n ^ (2 * k) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hN2 k) (Nat.pow_le_pow_left hLN k)
  rw [hc]
  exact_mod_cast key

/-- **The weak-law step at one time sequence** (proof of Step 1 of the `d ≥ 3` paper, [YY_25, §5.1];
RBM2D's `s1_wl_seq`): for every time sequence `u n ∈ [s n, t n]`,
`1(‖G_u - m‖_max ≤ 2 a_s^{1/4}) ‖G_u - m‖_max ≺ 2·3^d a_s^{7/15}`.  The inputs are `lem_GbEXP`
(`(GiiGEX)`, `(GijGEX)` at `ε₀ = c'` from `s1_F5`, so that `Ω(u, c')` holds on the event),
`s1_LI` at `k = 2` with `s1_ratio_ev` (`(lRB1)` with the indicator, the loops `≺ a_s^{14/15}`) and
the deterministic core `s1_wl_det`. -/
private theorem s1_wl_seq (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : S1H55 sz E s)
    (hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGiiGEX sz E u ε₀)
    (hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGijGEX sz E u ε₀)
    (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) :
    PerTimeDomAt (seqP sz) sz.size (U := fun _ => Unit)
      (fun n _ ω => {ω | s1x sz E n (u n) ω ≤ 2 * s1a sz s n}.indicator
        (fun ω => s1x sz E n (u n) ω) ω)
      (fun n _ _ => s1f sz s n) := by
  have hsize := s1_hsize sz h.hN
  obtain ⟨c', hc', hF5⟩ := s1_F5 h
  have hGij' := hGij u hu c' hc'
  have hGii' := hGii u hu c' hc'
  have hLI := s1_LI h h55 u hu (k := 2) (by norm_num)
  have hLI' : sz.PrecPT (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => sz.STomegaC n (E n) (u n) 2 ω * ‖Sizes.Lloop sz n (E n) (u n) p.1 p.2 ω‖)
      (fun n _ _ => (s1B sz s n) ^ ((14 : ℝ) / 15)) := by
    refine PerTimeCalc.PerTime.mono_right_eventually hLI ?_
    filter_upwards [s1_ratio_ev h] with n hn p ω
    have := hn (u n) (hu n).1 (hu n).2
    simpa [mul_comm] using this
  refine s1_pt_of_highProb fun τ' hτ' => ?_
  have hC3 : ∀ᶠ l : ℕ in atTop,
      (Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L l))) : ℝ) ≤
        ((sz.size l : ℕ) : ℝ) ^ ((2 * 2 : ℕ) : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 2)] with l hl
    exact s1_card_loops l 2 hl
  have Ev1 := Sizes.Prec.whp sz hGij' hτ'
  have Ev2 := Sizes.Prec.whp sz hGii' hτ'
  have Ev3 := s1_highProb_of_pt (P := seqP sz) (size := sz.size) (C := ((2 * 2 : ℕ) : ℝ))
    (by positivity) hC3 hLI' hτ'
  have EvAll := PerTimeCalc.perTimeCalc_highProbAt_inter hsize
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize Ev1 Ev2) Ev3
  refine PerTimeCalc.perTimeCalc_highProbAt_mono EvAll ?_
  filter_upwards [hF5, s1_F8 h] with n hn5 hn8
  rintro ω ⟨⟨h1, h2⟩, h3⟩ ⟨⟩
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := s1_one_le_size sz n
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
  have hBs := s1_B_pos h n
  have hgr : (s1B sz s n) ^ ((14 : ℝ) / 15) = ((s1B sz s n) ^ ((7 : ℝ) / 15)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hBs.le]; norm_num
  have hQ1 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  change {ω | s1x sz E n (u n) ω ≤ 2 * s1a sz s n}.indicator (fun ω => s1x sz E n (u n) ω) ω ≤
    ((sz.size n : ℕ) : ℝ) ^ τ' * s1f sz s n
  by_cases hx : s1x sz E n (u n) ω ≤ 2 * s1a sz s n
  · rw [Set.indicator_of_mem (show ω ∈ {ω | s1x sz E n (u n) ω ≤ 2 * s1a sz s n} from hx)]
    have hent := s1_wl_det sz n ω (E := E n) (u := u n) (a := s1a sz s n) (c' := c')
      (g := (s1B sz s n) ^ ((14 : ℝ) / 15)) (Nτ := ((sz.size n : ℕ) : ℝ) ^ τ')
      (s1_bulk h.hκ (h.hE n)).1.le hc' hx hn5 hNτ (Real.rpow_nonneg hBs.le _) hn8
      (fun σ b => h3 (σ, b)) (fun P => h2 P) (fun P => h1 P)
    refine s1xM_le fun i j => ?_
    have hij := hent i j
    rw [hgr, h9] at hij
    have e : Green.llErrMat d (sz.L n) (sz.W n) (E n) (u n) (sz.seqHflow n (u n) ω) i j =
        ‖sz.STGM n (E n) (u n) ω i j‖ := (s1_STGM_norm sz n (E n) (u n) ω i j).symm
    rw [e]
    have hA0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by linarith
    have hB0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (s1B sz s n) ^ ((7 : ℝ) / 15)) :=
      mul_nonneg hA0 (by positivity)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 ?_
    have h5 : (2 * ((3 : ℝ) ^ d) ^ 2 + 1) * ((((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
        ((s1B sz s n) ^ ((7 : ℝ) / 15)) ^ 2) ≤
        (((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (s1B sz s n) ^ ((7 : ℝ) / 15))) ^ 2 := by
      have e2 : (((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (s1B sz s n) ^ ((7 : ℝ) / 15))) ^ 2 =
          (4 * ((3 : ℝ) ^ d) ^ 2) * ((((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
            ((s1B sz s n) ^ ((7 : ℝ) / 15)) ^ 2) := by ring
      rw [e2]
      have h6 : 2 * ((3 : ℝ) ^ d) ^ 2 + 1 ≤ 4 * ((3 : ℝ) ^ d) ^ 2 := by nlinarith
      have h7 : 0 ≤ (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 * ((s1B sz s n) ^ ((7 : ℝ) / 15)) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right h6 h7
    calc ‖sz.STGM n (E n) (u n) ω i j‖ ^ 2
        ≤ (2 * ((3 : ℝ) ^ d) ^ 2 + 1) * (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
            ((s1B sz s n) ^ ((7 : ℝ) / 15)) ^ 2 := hij
      _ = (2 * ((3 : ℝ) ^ d) ^ 2 + 1) * ((((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 *
            ((s1B sz s n) ^ ((7 : ℝ) / 15)) ^ 2) := by ring
      _ ≤ _ := h5
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | s1x sz E n (u n) ω ≤ 2 * s1a sz s n} from hx)]
    exact mul_nonneg (by linarith) (by positivity)

end WeakLawSeq

/-! ## 2. The net and the forbidden region for all `u ∈ [s,t]` -/

section Net

variable {d : ℕ} {sz : Sizes d} {κ 𝔠 𝔡 τ 𝔠d : ℝ} {E s t : ℕ → ℝ}

/-- The clamped net of `[s n, t n]` at scale `1/netSize A N` (RBM2D's `s1Net`, a copy of
the private `contTime` of `ContinuityNet.lean`; compare RBM1D `netTime_mem`). -/
private def s1Net (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

/-- Every net point lies in `[s n, t n]`. -/
private theorem s1Net_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : s1Net s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

/-- Every `u ∈ [s n, t n]` is within `1/netSize A N` of a net point (the window has length `≤ 1`). -/
private theorem s1_exists_close {s t : ℕ → ℝ} (hlen : ∀ n, t n - s n ≤ 1) (A : ℝ) (N n : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (s n) (t n)) :
    ∃ k, |u - s1Net s t A N n k| ≤ 1 / (netSize A N : ℝ) := by
  have hmem : u - s n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen n]⟩
  obtain ⟨k, hk⟩ := exists_netPt_close one_pos A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s n + netPt 1 A N k)| ≤ 1 / (netSize A N : ℝ) := by
    have h : u - (s n + netPt 1 A N k) = u - s n - netPt 1 A N k := by ring
    rw [h]; exact hk
  unfold s1Net
  rcases le_or_gt (s n + netPt 1 A N k) (t n) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

/-- **The forbidden region for all `u ∈ [s,t]` simultaneously** (proof of Step 1, [YY_25, §5.1]; RBM2D's
`s1_forb`; RBM1D's `weakLaw_highProb`): with high probability,
`‖G_u - m‖_max ≠ α` for every `u ∈ [s,t]`, `α = a_s^{1/4}`.  The per-sequence bound `s1_wl_seq`
is used at the points of a polynomial net (`#net ≤ N^{C'+1}`, `C'` the witness of `gopbound` at
`C = 1`, which is `2 + 14` there; no `d` in it), the union bound over the net
is `Unif.forbidden_region` (the band `[α/2, 2α]`, `f = 2·3^d a_s^{7/15} ≪ α/2` by `s1_F4`) and the
passage to all `u` is `gopbound` (the mesh `N^{-C'}` moves `‖G_u - m‖_max` by at most
`N^{-1} ≤ α/2`, `s1_F6`). -/
private theorem s1_forb (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : S1H55 sz E s)
    (hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGiiGEX sz E u ε₀)
    (hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGijGEX sz E u ε₀) :
    HighProbAt (seqP sz) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      s1x sz E n u ω < s1a sz s n ∨ s1a sz s n < s1x sz E n u ω}) := by
  have hsize := s1_hsize sz h.hN
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [h.hs0 n, h.ht1 n]
  obtain ⟨C', hC', hgop⟩ := gopbound sz κ E h.hκ h.hE h.hN 1 one_pos
  obtain ⟨ε, hε, hF4⟩ := s1_F4 h
  -- the net-level forbidden region
  have hpt : PerTimeDomAt (seqP sz) sz.size
      (U := fun l => Fin (netSize C' (sz.size l) + 1))
      (fun l k ω => {ω | s1x sz E l (s1Net s t C' (sz.size l) l k) ω ≤ 2 * s1a sz s l}.indicator
        (fun ω => s1x sz E l (s1Net s t C' (sz.size l) l k) ω) ω)
      (fun l _ _ => s1f sz s l) := by
    rw [perTimeDomAt_iff_forall_section (seqP sz) sz.size (fun l => ⟨0⟩)]
    intro sec
    exact s1_stochDom_unit (s1_wl_seq h h55 hGii hGij (fun n => s1Net s t C' (sz.size n) n (sec n))
      (fun n => s1Net_mem h.hst C' (sz.size n) n (sec n)))
  have hnetSD := stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := C' + 1) (by linarith)
    (hsize.eventually (card_net_le hC'.le)) hpt
  have hnet := PerTimeCalc.Unif.forbidden_region hsize
    (x := fun l (k : Fin (netSize C' (sz.size l) + 1)) ω =>
      s1x sz E l (s1Net s t C' (sz.size l) l k) ω)
    (f := fun l _ => s1f sz s l) (a := fun l _ => s1a sz s l / 2)
    (b := fun l _ => 2 * s1a sz s l)
    (fun l _ => by
      have := Real.rpow_pos_of_pos (s1_B_pos h l) ((1 : ℝ) / 4)
      simp only [s1a]; positivity) hε
    (by filter_upwards [hF4] with l hl _; exact hl) hnetSD
  -- the good event of `gopbound`
  have hgood : HighProbAt (seqP sz) sz.size (fun n => {ω : sz.SeqΩ | ¬ (∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
        u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
        |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
        ∃ i j : Idx d (sz.L n) (sz.W n),
          ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) <
            ‖(sz.seqHflow n u ω - zt (E n) u • 1)⁻¹ i j -
              (sz.seqHflow n u' ω - zt (E n) u' • 1)⁻¹ i j‖)}) := by
    intro D hD
    filter_upwards [hgop D hD] with n hn
    convert hn using 2
    ext ω; simp
  refine PerTimeCalc.perTimeCalc_highProbAt_mono
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize hnet hgood) ?_
  filter_upwards [h.hR, s1_F6 h] with n hR hF6
  rintro ω ⟨hω1, hω2⟩ u
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := s1_one_le_size sz n
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨k, hk⟩ := s1_exists_close hlen C' (sz.size n) n u.2
  have hθ := s1Net_mem h.hst C' (sz.size n) n k
  have hdist : |(u : ℝ) - s1Net s t C' (sz.size n) n k| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') := by
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
  have hgop : ∀ i j, ‖(sz.seqHflow n u ω - zt (E n) u •
        (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ i j -
      (sz.seqHflow n (s1Net s t C' (sz.size n) n k) ω -
        zt (E n) (s1Net s t C' (sz.size n) n k) •
        (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ i j‖ ≤
      ((sz.size n : ℕ) : ℝ)⁻¹ := by
    intro i j
    by_contra hlt
    push Not at hlt
    refine hω2 ⟨u, s1Net s t C' (sz.size n) n k, (h.hs0 n).trans u.2.1, (h.hs0 n).trans hθ.1,
      hrange u u.2, hrange _ hθ, hdist, i, j, ?_⟩
    rwa [Real.rpow_neg_one]
  have hgop' : ∀ i j, ‖(sz.seqHflow n (s1Net s t C' (sz.size n) n k) ω -
        zt (E n) (s1Net s t C' (sz.size n) n k) •
        (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ i j -
      (sz.seqHflow n u ω - zt (E n) u •
        (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ i j‖ ≤
      ((sz.size n : ℕ) : ℝ)⁻¹ := fun i j => by rw [norm_sub_rev]; exact hgop i j
  have hup := s1xM_le_add hgop
  have hdown := s1xM_le_add hgop'
  have hapos : 0 < s1a sz s n := Real.rpow_pos_of_pos (s1_B_pos h n) _
  rcases hω1 k with h1 | h1
  · left
    change s1xM d (sz.L n) (sz.W n) (E n) u (sz.seqHflow n u ω) < s1a sz s n
    change s1xM d (sz.L n) (sz.W n) (E n) (s1Net s t C' (sz.size n) n k)
      (sz.seqHflow n (s1Net s t C' (sz.size n) n k) ω) < s1a sz s n / 2 at h1
    linarith
  · right
    change s1a sz s n < s1xM d (sz.L n) (sz.W n) (E n) u (sz.seqHflow n u ω)
    change 2 * s1a sz s n < s1xM d (sz.L n) (sz.W n) (E n) (s1Net s t C' (sz.size n) n k)
      (sz.seqHflow n (s1Net s t C' (sz.size n) n k) ω) at h1
    linarith

end Net

/-! ## 3. The continuity argument and the two per-time conclusions -/

section Bootstrap

variable {d : ℕ} {sz : Sizes d} {κ 𝔠 𝔡 τ 𝔠d : ℝ} {E s t : ℕ → ℝ}

/-- `u ↦ ‖G_u - m‖_max` is continuous on `[a, b]`, `b < 1`, for every sample point
(`continuous_green_Hflow_moving_time` applied to the clamped path `z(min(u, b))`). -/
private theorem s1x_continuousOn (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| < 2) {a b : ℝ}
    (hb : b < 1) (ω : sz.SeqΩ) :
    ContinuousOn (fun v => s1x sz E n v ω) (Set.Icc a b) := by
  set z : ℝ → ℂ := fun v => zt (E n) (min v b) with hz
  have hzc : Continuous z :=
    (continuous_spectralZ (E n)).comp (continuous_id.min continuous_const)
  have hzi : ∀ v, (z v).im ≠ 0 := by
    intro v
    simp only [hz, zt_im]
    have : 0 < 1 - min v b := by have := min_le_right v b; linarith
    exact (mul_pos this (mE_im_pos hE)).ne'
  have hcont := continuous_green_Hflow_moving_time d (sz.L n) (sz.W n) (sz.slice n ω) hzc hzi
  have hfun : Continuous fun v => Finset.univ.sup' Finset.univ_nonempty
      (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) =>
        ‖Gres (Hflow d (sz.L n) (sz.W n) v (sz.slice n ω)) (z v) true q.1 q.2 -
          (if q.1 = q.2 then mE (E n) else 0)‖) := by
    refine Continuous.finset_sup'_apply _ fun q _ => ?_
    exact ((hcont.matrix_elem q.1 q.2).sub continuous_const).norm
  refine hfun.continuousOn.congr fun v hv => ?_
  simp only [s1x, s1xM, Green.llErrMat, hz, min_eq_left hv.2]
  rfl

/-- **The continuity argument** (proof of Step 1, [YY_25, §5.1]; RBM2D's `s1_boot`): with high probability, `‖G_u - m‖_max < a_s^{1/4}` for every `u ∈ [s,t]`.  The initial
condition is `(c)` at `s` (`STLocalMax`, `≺ a_s^{1/2}`, `s1_F3`), the continuity of `u ↦ ‖G_u - m‖_max`
is `s1x_continuousOn`, the forbidden region is `s1_forb`, the argument is `stepOneBootstrap`. -/
private theorem s1_boot (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : S1H55 sz E s)
    (hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGiiGEX sz E u ε₀)
    (hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGijGEX sz E u ε₀)
    (hIL : STLocalMax sz E s) :
    HighProbAt (seqP sz) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      s1x sz E n u ω < s1a sz s n}) := by
  have hsize := s1_hsize sz h.hN
  -- the initial condition
  have hinit : HighProbAt (seqP sz) sz.size
      (fun n => {ω | s1x sz E n (s n) ω < s1a sz s n}) := by
    obtain ⟨τ₀, hτ₀, hF3⟩ := s1_F3 h
    have hev := Sizes.Prec.whp sz hIL hτ₀
    refine PerTimeCalc.perTimeCalc_highProbAt_mono hev ?_
    filter_upwards [hF3] with n hn ω hω
    have hb : s1xM d (sz.L n) (sz.W n) (E n) (s n) (sz.seqHflow n (s n) ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₀ * (s1B sz s n) ^ ((1 : ℝ) / 2) :=
      s1xM_le fun i j => hω (i, j)
    exact lt_of_le_of_lt hb hn
  have hcont : HighProbAt (seqP sz) sz.size (fun l => {ω | ContinuousOn
      (fun u => s1x sz E l u ω) (Set.Icc (s l) (t l))}) :=
    PerTimeCalc.perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun l ω _ =>
        s1x_continuousOn sz E l (s1_bulk h.hκ (h.hE l)).1 (h.ht1 l) ω)
  exact PerTimeCalc.stepOneBootstrap hsize (M := fun l v ω => s1x sz E l v ω)
    (a := fun l _ => s1a sz s l) (b := fun l _ => s1a sz s l) (s := s) (t := t)
    hcont (fun l => continuousOn_const) (Eventually.of_forall fun l u => le_rfl)
    (s1_forb h h55 hGii hGij) hinit

/-- **(`Gtmwc`) per time** (proof of Step 1; RBM2D's `s1_weakPT`; RBM1D's `weakLaw`): `‖G_u - m‖_max ≺ (W^{-d}B_{u,0})^{1/4}` uniformly in
`u ∈ [s,t]`, per time.  `a_s^{1/4} ≤ a_u^{1/4}` is `STBctl_mono`. -/
private theorem s1_weakPT (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : S1H55 sz E s)
    (hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGiiGEX sz E u ε₀)
    (hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGijGEX sz E u ε₀)
    (hIL : STLocalMax sz E s) : STStep1WeakPT sz E s t := by
  have hsize := s1_hsize sz h.hN
  have hboot := s1_boot h h55 hGii hGij hIL
  unfold STStep1WeakPT
  refine PerTimeCalc.PerTime.stochDom_of_highProb hsize (fun n p ω =>
    Real.rpow_nonneg (s1_Bu_pos h n p.1.2.2).le _) ?_
  refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot (Eventually.of_forall fun n ω hω p => ?_)
  obtain ⟨u, i, j⟩ := p
  have h1 : Green.llErrMat d (sz.L n) (sz.W n) (E n) u (sz.seqHflow n u ω) i j ≤ s1x sz E n u ω :=
    s1xM_ge _ _ _ i j
  have h2 := hω u
  have h3 : sz.Bctl n (s n) ≤ sz.Bctl n u :=
    sz.STBctl_mono n u.2.1 (lt_of_le_of_lt u.2.2 (h.ht1 n))
  have h4 : s1a sz s n ≤ (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (s1_B_pos h n).le h3 (by norm_num)
  exact (h1.trans h2.le).trans h4

/-- `ξ n (u n) p ω` per time over `[s,t]` from its section statements, without the `Unit ×` factor
of `Green.perTime_timeIcc_of_forall_seq` (the family of `s1_LI` is over `(σ, a)` only). -/
private theorem s1_perTime_timeIcc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
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

/-- **(`lRB1`) per time** (proof of Step 1; RBM2D's `s1_loopPT`; RBM1D's `apriori`): `|𝓛_{u,σ,a}| ≺ ((1-s)/(1-u))^{k-1} (W^{-d}B_{s,0})^{k-1}`
uniformly in `u ∈ [s,t]`, per time: the indicator of `{‖G_u‖_max ≤ 2}` is removed by the continuity
argument (`‖G_u‖_max ≤ 1 + ‖G_u - m‖_max < 1 + a_s^{1/4} ≤ 2`). -/
private theorem s1_loopPT (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : S1H55 sz E s)
    (hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGiiGEX sz E u ε₀)
    (hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGijGEX sz E u ε₀)
    (hIL : STLocalMax sz E s) : STStep1LoopPT sz E s t := by
  intro k hk
  have hsize := s1_hsize sz h.hN
  have hboot := s1_boot h h55 hGii hGij hIL
  refine PerTimeCalc.PerTime.stochDom_of_indicator hsize
    (Ωs := fun n p => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖Sizes.Gt sz n (E n) (p.1 : ℝ) true ω x y‖ ≤ 2}) ?_ ?_
  · refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot ?_
    filter_upwards [s1_F7 h] with n hF7 ω hω p x y
    have h1 := s1_gMax_le (d := d) (L := sz.L n) (W := sz.W n) (u := (p.1 : ℝ))
      (s1_bulk h.hκ (h.hE n)).1.le (sz.seqHflow n p.1 ω) x y
    have h2 := hω p.1
    change ‖Gres (sz.seqHflow n p.1 ω) (zt (E n) (p.1 : ℝ)) true x y‖ ≤ 2
    change s1xM d (sz.L n) (sz.W n) (E n) p.1 (sz.seqHflow n p.1 ω) < s1a sz s n at h2
    linarith
  · have key : PerTimeDomAt (seqP sz) sz.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => sz.STomegaC n (E n) (p.1 : ℝ) 2 ω *
          ‖Sizes.Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) :=
      s1_perTime_timeIcc (seqP sz) sz.size h.hst
        (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
        (fun n v q ω => sz.STomegaC n (E n) v 2 ω * ‖Sizes.Lloop sz n (E n) v q.1 q.2 ω‖)
        (fun n v _ _ => ((1 - s n) / (1 - v)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
        (fun u hu => s1_LI h h55 u hu hk)
    refine PerTimeCalc.PerTime.stochDom_of_le_left_eventually
      (Eventually.of_forall fun n p ω => le_of_eq ?_) key
    by_cases hg : ∀ x y : Idx d (sz.L n) (sz.W n), ‖Sizes.Gt sz n (E n) (p.1 : ℝ) true ω x y‖ ≤ 2
    · simp [Set.indicator, Sizes.STomegaC, hg]
    · simp [Set.indicator, Sizes.STomegaC, hg]

end Bootstrap

/-! ## 4. The theorem -/

/-- **Step 1 of `lem:main_ind`** (proof of Step 1; RBM2D's `step1`): `(lRB1)` and `(Gtmwc)`
uniformly in `u ∈ [s,t]`, in the form
`Step1TargetV3 d := STGbEXPii d → STGbEXPij d → STStep1 d`, for every `d`: under the two parts
`(GiiGEX)`, `(GijGEX)` of `lem_GbEXP`, the hypotheses of `STStep1` (`STKbound`, `STLK s`,
`STLocalMax s`, `STConStInd 𝔠_d s t`, the flow, `0 ≤ s < t`, `s, t ≤ lemT z`) give `STStep1Loop`
and `STStep1Weak`.  Proof: the per-time statements `s1_loopPT`, `s1_weakPT` (continuity argument
from `conArg` via `s1_LI`, the two hypotheses `STGbEXPii`, `STGbEXPij`, `gopbound`,
`stepOneBootstrap`) and the net lift `step1NetLift` at `κ`, `τ = ε/2`; `S1Std` is
`s1_std_of_stFlow`.  The two hypotheses are used at `E = STflowE z`, at the time sequences
`u n ∈ [s n, t n]` (so `0 ≤ u n ≤ t n ≤ lemT (z n)`) and at `ε₀ = c'` of `s1_F5`. -/
theorem step1TargetV3_holds (d : ℕ) : RBM.Ind.Step1TargetV3 d := by
  intro hii hij κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow s t hs0 hsT hst htT hK hLK hLoc hCond
  have h := s1_std_of_stFlow hκ hε h𝔠d h𝔠d' hflow hs0 (fun n => (hst n).le) htT hCond
  have h55 := s1_h55 h hLK hK
  have hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGiiGEX sz (STflowE z) u ε₀ := fun u hu ε₀ hε₀ =>
    hii κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hu n).1)
      (fun n => (hu n).2.trans (htT n)) ε₀ hε₀
  have hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ > (0 : ℝ),
      STGijGEX sz (STflowE z) u ε₀ := fun u hu ε₀ hε₀ =>
    hij κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hu n).1)
      (fun n => (hu n).2.trans (htT n)) ε₀ hε₀
  have hnet := step1NetLift sz (STflowE z) κ (ε / 2) s t h.hκ h.hE h.hτ h.hs0 h.hst h.ht1 h.hN h.hR
  exact ⟨hnet.1 (s1_loopPT h h55 hGii hGij hLoc), hnet.2 (s1_weakPT h h55 hGii hGij hLoc)⟩

end RBM.Ind




end
