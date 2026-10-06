/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Events
import RBM3D.Green.Pins
import RBM3D.Gauss.Domination
import RBM3D.Loop.KLFinal
import RBM3D.Loop.KLTreeDeriv
import RBM3D.Loop.KBound
import RBM3D.Loop.TreeRep
import RBM3D.Loop.Unique
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The uniform non-alternating endpoint at the flow (`d ≥ 3`): `stOeqNQ''_holds`

Ticket T2258 (S3-12c2, stochastic layer ST-3, fourth of four after the DECISIONS §80 split;
S3-12c1 = T2246 `Induction/NQEndFlow` proves the per-time pin `stOeqNQPT''_holds`).
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`, `lem:STOeq_NQ` (`3_5:1136`, bound
`(am;asoiuw)` `3_5:1143-1148`, proof `3_5:1152-1190`; the `N^{-C}`-net remark is commented out
at `3_5:1182`, the same remark at `3_5:1764`).

## What is here

* §1 the vocabulary `RBM.Ind.nqFlowSharp`: the monotone envelope
  `X♯(m,n,u) = max 1 (inf_{u' ∈ [u, t_n]} X(m,n,u'))` of a control (`1 ≤ X♯ ≤ X`, non-decreasing
  on `u ≤ t_n`; check file `docs/tickets/checks/T2258-check.lean`, §2);
* §2 the envelope lemmas (private): `1 ≤ X♯`, `X♯ ≤ X`, monotonicity, and the pair hypotheses
  carry over to `X♯` (one `Prec` event: the `X♯`-bad event is inside the `X`-bad event);
* §3 the bootstrap right side `ζ♯` (private): `STbootRHS` is monotone in the controls, `ζ♯ ≤ ζ`,
  `1 ≤ ζ♯`, `ζ♯` non-decreasing in `u`;
* §4 the one-sided net core (private): the merged `ContinuityNet.cont_core`
  (`ContinuityNet.lean:142`) with the floor net point, so that the closeness hypothesis is asked
  only for `u' ≤ u`;
* §5 the time modulus of `𝒦^{(k)}`, every `k ≥ 2` (public `RBM.Gauss.Sizes.stKloop_lip`): tree
  equations `KLK_isKLoop`, the uniform crude bound `KLbound_holds`, the mean value theorem;
* §6 the `ξ` modulus on `contGood`, the lift `STNQConclPT'' → STNQConcl''` (private) and the
  target `RBM.Ind.stOeqNQ''_holds`;
* §7 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.NQEndFlowLiftInst`).

Every helper that the ticket does not pin is `private` or prefixed `nqLift_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The vocabulary: the monotone envelope of a control -/

/-- **The monotone envelope `X♯` of a control** (supervisor `2026-10-05-1955` A2): `X♯(m,n,u) =
inf_{u' ∈ [u, t_n]} X(m,n,u')`, floored at `1` (the floor is inactive for `u ≤ t_n` when `X ≥ 1`; for `u > t_n` the
set is empty and `X♯ = 1`).  `1 ≤ X♯ ≤ X`, non-decreasing in `u ≤ t_n`. -/
noncomputable def nqFlowSharp (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  max 1 (sInf (X m n '' Set.Icc u (t n)))

/-! ## 2. The envelope lemmas -/

/-- Envelope (a): `1 ≤ X♯`. -/
private theorem nqLift_sharp_one_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ),
    1 ≤ nqFlowSharp t X m n u :=
  fun _ _ _ _ _ => le_max_left _ _

/-- Envelope (b): `X♯ ≤ X` for a control `X ≥ 1`. -/
private theorem nqLift_sharp_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u : ℝ), nqFlowSharp t X m n u ≤ X m n u := by
  intro t X hX m n u
  unfold nqFlowSharp
  refine max_le (hX m n u) ?_
  by_cases hu : u ≤ t n
  · exact csInf_le ⟨1, by rintro _ ⟨v, -, rfl⟩; exact hX m n v⟩ ⟨u, ⟨le_rfl, hu⟩, rfl⟩
  · rw [Set.Icc_eq_empty hu, Set.image_empty, Real.sInf_empty]
    exact zero_le_one.trans (hX m n u)

/-- Envelope (c): `X♯` is non-decreasing in `u ≤ t_n`. -/
private theorem nqLift_sharp_mono : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u u' : ℝ), u ≤ u' → u' ≤ t n → nqFlowSharp t X m n u ≤ nqFlowSharp t X m n u' := by
  intro t X hX m n u u' huu' hu't
  unfold nqFlowSharp
  refine max_le_max le_rfl ?_
  refine csInf_le_csInf ⟨1, by rintro _ ⟨v, -, rfl⟩; exact hX m n v⟩
    ⟨X m n u', u', ⟨le_rfl, hu't⟩, rfl⟩ ?_
  exact Set.image_mono (Set.Icc_subset_Icc_left huu')

/-- Envelope (d): the pair hypotheses carry over to `X♯` (one `Prec` event; the left side depends on the pair only
through its first time `q.1.1`).  Off the `X`-bad event, `Ξ̂_w ≤ N^τ X(u')` for every `u' ∈ [u, t_n]` (as `(w, u')`
is a pair), hence `Ξ̂_w ≤ N^τ inf_{u'} X(u') ≤ N^τ X♯(u)`; bad-set inclusion, `StochDomAt.of_subset`. -/
private theorem nqLift_sharp_prec : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ)
    (X : ℕ → ℕ → ℝ → ℝ) (m : ℕ), (∀ m n u, 1 ≤ X m n u) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => X m n q.1.2) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => nqFlowSharp t X m n q.1.2) := by
  intro d sz s t f X m hX h
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨q, hq⟩ := hω
  have hc : 0 < ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _
  have hu : q.1.2 ≤ t n := q.2.2.2
  have hS : (X m n '' Set.Icc q.1.2 (t n)).Nonempty := ⟨X m n q.1.2, q.1.2, ⟨le_rfl, hu⟩, rfl⟩
  have hq' : ((sz.size n : ℕ) : ℝ) ^ τ * max 1 (sInf (X m n '' Set.Icc q.1.2 (t n))) < f n q.1.1 ω := hq
  have hinf : sInf (X m n '' Set.Icc q.1.2 (t n)) < f n q.1.1 ω / ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [lt_div_iff₀ hc]
    have h1 : ((sz.size n : ℕ) : ℝ) ^ τ * sInf (X m n '' Set.Icc q.1.2 (t n)) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * max 1 (sInf (X m n '' Set.Icc q.1.2 (t n))) :=
      mul_le_mul_of_nonneg_left (le_max_right 1 _) hc.le
    linarith
  obtain ⟨y, ⟨u', hu', rfl⟩, hy⟩ := exists_lt_of_csInf_lt hS hinf
  refine ⟨⟨(q.1.1, u'), q.2.1, q.2.2.1.trans hu'.1, hu'.2⟩, ?_⟩
  rw [lt_div_iff₀ hc] at hy
  change ((sz.size n : ℕ) : ℝ) ^ τ * X m n u' < f n q.1.1 ω
  linarith

/-! ## 3. The bootstrap right side `ζ♯` -/

section RightSide

variable {d : ℕ}

/-- `STbootRHS` is monotone in both controls (`B > 0` fixed, all exponents `≥ 0`). -/
private theorem nqLift_bootRHS_mono : ∀ (lo : ℕ) (XL XL' XLK XLK' : ℕ → ℝ) (B : ℝ) (n_ p : ℕ), 0 < B →
    (∀ m, 0 ≤ XL m) → (∀ m, 0 ≤ XLK m) → (∀ m, XL m ≤ XL' m) → (∀ m, XLK m ≤ XLK' m) →
    STbootRHS lo XL XLK B n_ p ≤ STbootRHS lo XL' XLK' B n_ p := by
  intro lo XL XL' XLK XLK' B n_ p hB hXL hXLK hle hleK
  unfold STbootRHS
  have hB0 : (0 : ℝ) ≤ B ^ (-(1 : ℝ) / (4 * (p : ℝ))) := Real.rpow_nonneg hB.le _
  have hexp1 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hexp2 : (0 : ℝ) ≤ 1 / (4 * (p : ℝ)) := by positivity
  have a1 : XL (2 * n_ - 1) ^ (1 / 2 : ℝ) ≤ XL' (2 * n_ - 1) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (hXL _) (hle _) hexp1
  have a2 : XL (4 * p) ^ (1 / (4 * (p : ℝ))) ≤ XL' (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    Real.rpow_le_rpow (hXL _) (hle _) hexp2
  have h1 : B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * n_ - 1) ^ (1 / 2 : ℝ) *
        XL (4 * p) ^ (1 / (4 * (p : ℝ))) ≤
      B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL' (2 * n_ - 1) ^ (1 / 2 : ℝ) *
        XL' (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left a1 hB0) a2 (Real.rpow_nonneg (hXL _) _)
      (mul_nonneg hB0 (Real.rpow_nonneg ((hXL _).trans (hle _)) _))
  have h2 : ∑ m ∈ Finset.Icc lo (n_ - 1), XLK m ≤ ∑ m ∈ Finset.Icc lo (n_ - 1), XLK' m :=
    Finset.sum_le_sum fun m _ => hleK m
  have h3 : ∑ m ∈ Finset.Icc (n_ - 1) (n_ + 1), XL m ≤ ∑ m ∈ Finset.Icc (n_ - 1) (n_ + 1), XL' m :=
    Finset.sum_le_sum fun m _ => hle m
  have h4 : ∑ m ∈ Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1),
        XLK (n_ + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2) ^ (1 / 2 : ℝ) ≤
      ∑ m ∈ Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1),
        XLK' (n_ + 2 - m) * (XL' (STn12 m).1 * XL' (STn12 m).2) ^ (1 / 2 : ℝ) := by
    refine Finset.sum_le_sum fun m _ => ?_
    have hp : XL (STn12 m).1 * XL (STn12 m).2 ≤ XL' (STn12 m).1 * XL' (STn12 m).2 :=
      mul_le_mul (hle _) (hle _) (hXL _) ((hXL _).trans (hle _))
    exact mul_le_mul (hleK _) (Real.rpow_le_rpow (mul_nonneg (hXL _) (hXL _)) hp hexp1)
      (Real.rpow_nonneg (mul_nonneg (hXL _) (hXL _)) _) ((hXLK _).trans (hleK _))
  exact add_le_add h1 (add_le_add (add_le_add h2 h3) h4)

/-- `1 ≤ STbootRHS lo XL XLK B k p` for `XL ≥ 1`, `XLK ≥ 0`, `B ≥ 0`, `k ≥ 1` (copy of the private
`nqFlow_bootRHS_one_le`, `NQEndFlow.lean:804`). -/
private theorem nqLift_bootRHS_one_le {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 1 ≤ k)
    (hXL : ∀ m, 1 ≤ XL m) (hXLK : ∀ m, 0 ≤ XLK m) (hB : 0 ≤ B) : 1 ≤ STbootRHS lo XL XLK B k p := by
  have hXL0 : ∀ m, 0 ≤ XL m := fun m => zero_le_one.trans (hXL m)
  unfold STbootRHS
  have h1 : 0 ≤ B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * k - 1) ^ (1 / 2 : ℝ) *
      XL (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg (hXL0 _) _))
      (Real.rpow_nonneg (hXL0 _) _)
  have h2 : 0 ≤ ∑ m ∈ Finset.Icc lo (k - 1), XLK m := Finset.sum_nonneg fun m _ => hXLK m
  have h3 : XL k ≤ ∑ m ∈ Finset.Icc (k - 1) (k + 1), XL m :=
    Finset.single_le_sum (f := XL) (fun m _ => hXL0 m) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h4 : 0 ≤ ∑ m ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      XLK (k + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2) ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (hXLK _) (Real.rpow_nonneg (mul_nonneg (hXL0 _) (hXL0 _)) _)
  have := hXL k
  linarith

/-- **`ζ♯` is non-decreasing in `u`** (R2*: the first summand of `STbootRHS` is at the fixed `B_s`, so no ratio of
`B` is needed): for `s_n ≤ θ ≤ u ≤ t_n < 1`, the right side of `STNQConclPT''` at the envelope controls
`(XL♯, XLK♯)` at `θ` is at most that at `u` (`B_θ^{1/6} ≤ B_u^{1/6}` by `STBctl_mono`, the envelopes are
non-decreasing, `STbootRHS` is monotone in the controls). -/
private theorem nqLift_zeta_mono (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (n_ p n : ℕ) {θ u : ℝ} (hsθ : s n ≤ θ) (hθu : θ ≤ u) (hut : u ≤ t n) :
    (sz.Bctl n θ) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n θ +
      STbootRHS 2 (fun m => nqFlowSharp t XL m n θ) (fun m => nqFlowSharp t XLK m n θ)
        (sz.Bctl n (s n)) n_ p ≤
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 2 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p := by
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hθ1 : θ < 1 := hθu.trans_lt hu1
  have hs1 : s n < 1 := hsθ.trans_lt hθ1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBθ : 0 < sz.Bctl n θ := st_Bctl_pos sz hθ1
  have hBθu : sz.Bctl n θ ≤ sz.Bctl n u := STBctl_mono sz n hθu hu1
  refine add_le_add ?_ (nqLift_bootRHS_mono 2 _ _ _ _ _ n_ p hBs
    (fun m => zero_le_one.trans (nqLift_sharp_one_le t XL m n θ))
    (fun m => zero_le_one.trans (nqLift_sharp_one_le t XLK m n θ))
    (fun m => nqLift_sharp_mono t XL hXL m n θ u hθu hut)
    (fun m => nqLift_sharp_mono t XLK hXLK m n θ u hθu hut))
  exact mul_le_mul (Real.rpow_le_rpow hBθ.le hBθu (by norm_num))
    (nqLift_sharp_mono t XLK hXLK n_ n θ u hθu hut) (zero_le_one.trans (nqLift_sharp_one_le t XLK n_ n θ))
    (Real.rpow_nonneg (hBθ.le.trans hBθu) _)

/-- **`ζ♯ ≤ ζ`** pointwise (`X♯ ≤ X`, `STbootRHS` monotone in the controls). -/
private theorem nqLift_zeta_le (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (n_ p n : ℕ) {u : ℝ} (hsu : s n ≤ u) (hut : u ≤ t n) :
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 2 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p ≤
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * XLK n_ n u +
      STbootRHS 2 (fun m => XL m n u) (fun m => XLK m n u) (sz.Bctl n (s n)) n_ p := by
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hs1 : s n < 1 := hsu.trans_lt hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  refine add_le_add ?_ (nqLift_bootRHS_mono 2 _ _ _ _ _ n_ p hBs
    (fun m => zero_le_one.trans (nqLift_sharp_one_le t XL m n u))
    (fun m => zero_le_one.trans (nqLift_sharp_one_le t XLK m n u))
    (fun m => nqLift_sharp_le t XL hXL m n u) (fun m => nqLift_sharp_le t XLK hXLK m n u))
  exact mul_le_mul_of_nonneg_left (nqLift_sharp_le t XLK hXLK n_ n u) (Real.rpow_nonneg hBu.le _)

/-- **`1 ≤ ζ♯`** (`ζ♯ ≥ 1` is the floor `ε_n = 1` of the net lift): `XL♯ ≥ 1`, `XLK♯ ≥ 1`, `B ≥ 0`, `n_ ≥ 1`. -/
private theorem nqLift_zeta_one_le (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (n_ p n : ℕ) (hn : 1 ≤ n_) {u : ℝ} (hsu : s n ≤ u) (hut : u ≤ t n) :
    1 ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 2 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p := by
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hs1 : s n < 1 := hsu.trans_lt hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have h0 : 0 ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u :=
    mul_nonneg (Real.rpow_nonneg hBu.le _) (zero_le_one.trans (nqLift_sharp_one_le t XLK n_ n u))
  have := nqLift_bootRHS_one_le (lo := 2) (XL := fun m => nqFlowSharp t XL m n u)
    (XLK := fun m => nqFlowSharp t XLK m n u) (B := sz.Bctl n (s n)) (k := n_) (p := p) hn
    (fun m => nqLift_sharp_one_le t XL m n u)
    (fun m => zero_le_one.trans (nqLift_sharp_one_le t XLK m n u)) hBs.le
  linarith

end RightSide

/-- The pinned statement of `nqLift_bootRHS_mono` (check file `T2258-check.lean`, §3, `T2258_bootRHS_mono`). -/
example : ∀ (lo : ℕ) (XL XL' XLK XLK' : ℕ → ℝ) (B : ℝ) (n_ p : ℕ), 0 < B →
    (∀ m, 0 ≤ XL m) → (∀ m, 0 ≤ XLK m) → (∀ m, XL m ≤ XL' m) → (∀ m, XLK m ≤ XLK' m) →
    STbootRHS lo XL XLK B n_ p ≤ STbootRHS lo XL' XLK' B n_ p := @nqLift_bootRHS_mono

/-! ## 4. The one-sided net core

The merged `ContinuityNet.cont_core` (`ContinuityNet.lean:142`) asks the closeness of `ξ` and `ζ` for every pair of
times at distance `≤ N^{-A}`; the envelope `ζ♯` is non-decreasing, so `ζ♯(θ) ≤ 2 ζ♯(u)` holds only for `θ ≤ u`.  The
net point of `u` is therefore the floor point `θ = s_n + ⌊(u - s_n) m⌋/m ≤ u` (`m = netSize`), and the closeness is asked
only for `u' ≤ u`; the clamp `min (t_n)` of the merged `contTime` is inactive at `θ`.  Everything else is the text of
`cont_core`. -/

section Core

/-- Copy of the private `ContinuityNet.cont_stochDomAt_of_subset` (`ContinuityNet.lean:76`). -/
private theorem nqLift_stochDomAt_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U V : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ' ζ' : ∀ l, V l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (h : StochDomAt P size ξ' ζ') (hΞ : HighProbAt P size Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ∩ Ξ l ⊆ badSetAt size ξ' ζ' τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' (D + 1) (by linarith), hΞ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcover : badSetAt size ξ ζ τ l ⊆ (badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ := by
    intro ω hω
    by_cases hΞω : ω ∈ Ξ l
    · exact Or.inl ⟨hω, hΞω⟩
    · exact Or.inr hΞω
  calc P (badSetAt size ξ ζ τ l) ≤ P ((badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ) :=
        measure_mono hcover
    _ ≤ P (badSetAt size ξ ζ τ l ∩ Ξ l) + P (Ξ l)ᶜ := measure_union_le _ _
    _ ≤ P (badSetAt size ξ' ζ' τ' l) + P (Ξ l)ᶜ := add_le_add (measure_mono h0) le_rfl
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- The clamped net of `[s n, t n]` (copy of the private `ContinuityNet.contTime`, `ContinuityNet.lean:106`). -/
private def nqLift_time (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

/-- Copy of `ContinuityNet.contTime_mem`. -/
private theorem nqLift_time_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : nqLift_time s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

/-- **The floor net point** (`T2258_netPt_floor`; the witness of `exists_netPt_close`, `Domination.lean:171`, at
`T = 1`, with the one-sided information `netPt ≤ x`): `netPt` at `⌊x · netSize⌋` lies in `[x - 1/netSize, x]`. -/
private theorem nqLift_netPt_floor : ∀ (A : ℝ) (N : ℕ) (x : ℝ), 0 ≤ x → x ≤ 1 →
    ∃ k : Fin (netSize A N + 1), netPt 1 A N k ≤ x ∧ x - netPt 1 A N k ≤ 1 / (netSize A N : ℝ) := by
  intro A N x hx0 hx1
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hy0 : 0 ≤ x * (netSize A N : ℝ) := mul_nonneg hx0 hm.le
  have hym : x * (netSize A N : ℝ) ≤ (netSize A N : ℝ) := by nlinarith
  have hkm : ⌊x * (netSize A N : ℝ)⌋₊ ≤ netSize A N := Nat.floor_le_of_le hym
  have hfl : ((⌊x * (netSize A N : ℝ)⌋₊ : ℕ) : ℝ) ≤ x * (netSize A N : ℝ) := Nat.floor_le hy0
  have hfu : x * (netSize A N : ℝ) < ((⌊x * (netSize A N : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨⟨⌊x * (netSize A N : ℝ)⌋₊, Nat.lt_succ_of_le hkm⟩, ?_, ?_⟩
  · change ((⌊x * (netSize A N : ℝ)⌋₊ : ℕ) : ℝ) * 1 / (netSize A N : ℝ) ≤ x
    rw [div_le_iff₀ hm]
    linarith
  · change x - ((⌊x * (netSize A N : ℝ)⌋₊ : ℕ) : ℝ) * 1 / (netSize A N : ℝ) ≤ 1 / (netSize A N : ℝ)
    rw [show x - ((⌊x * (netSize A N : ℝ)⌋₊ : ℕ) : ℝ) * 1 / (netSize A N : ℝ) =
      (x * (netSize A N : ℝ) - ((⌊x * (netSize A N : ℝ)⌋₊ : ℕ) : ℝ)) / (netSize A N : ℝ) by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hm.le

/-- **The one-sided net lift** (`T2258_core_below`): the merged `cont_core` (`ContinuityNet.lean:142`) with the
closeness hypothesis `hclose` asked only for `u' ≤ u` (the floor net point lies below `u`).  Nothing else changes: a
per-time domination on `TimeIcc s t n × V n`, a polynomial bound on `#V n`, a good event `Ξ` of high probability on
which `ξ` moves up by at most `ε n` and `ζ` down by a factor `2` along a downward time change of size `size^{-A}`, and
`ε ≤ ζ`, give the uniform domination. -/
private theorem nqLift_core_below : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ),
    Tendsto size atTop atTop →
    ∀ (s t : ℕ → ℝ), (∀ n, s n ≤ t n) → (∀ n, t n - s n ≤ 1) →
    ∀ (V : ℕ → Type) [∀ n, Fintype (V n)] (ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ) (A Cv : ℝ),
      0 ≤ A → 0 ≤ Cv →
      (∀ᶠ n : ℕ in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ Cv) →
      PerTimeDomAt P size ξ ζ → ∀ Ξ : ℕ → Set Ω, HighProbAt P size Ξ →
      ∀ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) →
      (∀ᶠ n : ℕ in atTop, ∀ (p : TimeIcc s t n × V n) (ω : Ω), ε n ≤ ζ n p ω) →
      (∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ u u' : TimeIcc s t n, (u' : ℝ) ≤ (u : ℝ) →
        (u : ℝ) - (u' : ℝ) ≤ (size n : ℝ) ^ (-A) → ∀ v : V n,
          ξ n (u, v) ω ≤ ξ n (u', v) ω + ε n ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) →
      StochDomAt P size ξ ζ := by
  intro Ω _ P size hsize s t hst hlen V _ ξ ζ A Cv hA hCv hcard hpt Ξ hΞ ε hε hlow hclose
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
  let θ : ∀ n, Fin (netSize (A + 1) (size n) + 1) → TimeIcc s t n := fun n k =>
    ⟨nqLift_time s t (A + 1) (size n) n k, nqLift_time_mem hst _ _ n k⟩
  let ξ' : ∀ n, (Fin (netSize (A + 1) (size n) + 1) × V n) → Ω → ℝ :=
    fun n p ω => ξ n (θ n p.1, p.2) ω
  let ζ' : ∀ n, (Fin (netSize (A + 1) (size n) + 1) × V n) → Ω → ℝ :=
    fun n p ω => ζ n (θ n p.1, p.2) ω
  have hpt' : PerTimeDomAt P size ξ' ζ' := by
    intro τ hτ D hD
    filter_upwards [hpt τ hτ D hD] with l hl p
    exact hl (θ l p.1, p.2)
  have hcard' : ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Fin (netSize (A + 1) (size n) + 1) × V n) : ℝ) ≤
        (size n : ℝ) ^ (A + 1 + 1 + Cv) := by
    filter_upwards [hcard, hsize.eventually (card_net_le hA1),
      hsize.eventually (eventually_ge_atTop 1)] with n h1 h2 h3
    have hpos : (0 : ℝ) < (size n : ℝ) := by exact_mod_cast h3
    rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_add hpos]
    exact mul_le_mul h2 h1 (Nat.cast_nonneg _) (Real.rpow_nonneg hpos.le _)
  have hnet : StochDomAt P size ξ' ζ' :=
    stochDomAt_of_perTimeDomAt P size (C := A + 1 + 1 + Cv) (by linarith) hcard' hpt'
  refine nqLift_stochDomAt_of_subset hsize hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hclose, hlow, hsize.eventually (eventually_ge_atTop 2),
    hsize.eventually (eventually_le_rpow 3 hτ2)] with n hcloseN hlowN hN2 hN3
  rintro ω ⟨⟨⟨u, v⟩, hbad⟩, hωΞ⟩
  have hN2' : (2 : ℝ) ≤ (size n : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (size n : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (netSize (A + 1) (size n) : ℝ) := by
    exact_mod_cast netSize_pos (A + 1) (size n)
  have hmge : (size n : ℝ) ^ (A + 1) ≤ (netSize (A + 1) (size n) : ℝ) :=
    rpow_le_netSize _ _
  have hNA1 : (0 : ℝ) < (size n : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos hNpos _
  -- the floor net point of `u`
  obtain ⟨k, hk1, hk2⟩ := nqLift_netPt_floor (A + 1) (size n) ((u : ℝ) - s n)
    (by linarith [u.2.1]) (by linarith [u.2.2, hlen n])
  have hθle : s n + netPt 1 (A + 1) (size n) k ≤ (u : ℝ) := by linarith
  have hθeq : ((θ n k : TimeIcc s t n) : ℝ) = s n + netPt 1 (A + 1) (size n) k :=
    min_eq_right (hθle.trans u.2.2)
  have hle : ((θ n k : TimeIcc s t n) : ℝ) ≤ (u : ℝ) := by rw [hθeq]; exact hθle
  have hdist : (u : ℝ) - ((θ n k : TimeIcc s t n) : ℝ) ≤ (size n : ℝ) ^ (-A) := by
    rw [hθeq]
    have h0 : (u : ℝ) - (s n + netPt 1 (A + 1) (size n) k) =
        ((u : ℝ) - s n) - netPt 1 (A + 1) (size n) k := by ring
    rw [h0]
    refine hk2.trans ?_
    have h1 : 1 / (netSize (A + 1) (size n) : ℝ) ≤ 1 / (size n : ℝ) ^ (A + 1) := by
      gcongr
    refine h1.trans ?_
    rw [div_le_iff₀ hNA1]
    have hmul : (size n : ℝ) ^ (-A) * (size n : ℝ) ^ (A + 1) = (size n : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    rw [hmul, Real.rpow_one]
    linarith
  obtain ⟨hξ, hζ⟩ := hcloseN ω hωΞ u (θ n k) hle hdist v
  have hzlow : ε n ≤ ζ n (u, v) ω := hlowN (u, v) ω
  have hε0 := hε n
  have hz0 : (0 : ℝ) ≤ ζ n (u, v) ω := le_trans hε0 hzlow
  have hhalf : (size n : ℝ) ^ (τ / 2) * (size n : ℝ) ^ (τ / 2) = (size n : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hbig : (0 : ℝ) ≤ (size n : ℝ) ^ τ - 2 * (size n : ℝ) ^ (τ / 2) - 1 := by
    nlinarith [hhalf, hN3]
  have hprod : (0 : ℝ) ≤ ((size n : ℝ) ^ τ - 2 * (size n : ℝ) ^ (τ / 2) - 1) * ζ n (u, v) ω :=
    mul_nonneg hbig hz0
  have hhalf0 : (0 : ℝ) ≤ (size n : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hz'le : (size n : ℝ) ^ (τ / 2) * ζ n (θ n k, v) ω ≤
      (size n : ℝ) ^ (τ / 2) * (2 * ζ n (u, v) ω) :=
    mul_le_mul_of_nonneg_left hζ hhalf0
  refine ⟨(k, v), ?_⟩
  change (size n : ℝ) ^ (τ / 2) * ζ n (θ n k, v) ω < ξ n (θ n k, v) ω
  nlinarith [hbad, hξ, hprod, hzlow, hz'le]

end Core

/-- The pinned statement of `nqLift_netPt_floor` (check file §3, `T2258_netPt_floor`). -/
example : ∀ (A : ℝ) (N : ℕ) (x : ℝ), 0 ≤ x → x ≤ 1 →
    ∃ k : Fin (netSize A N + 1), netPt 1 A N k ≤ x ∧ x - netPt 1 A N k ≤ 1 / (netSize A N : ℝ) :=
  @nqLift_netPt_floor

/-- The pinned statement of `nqLift_core_below` (check file §3, `T2258_core_below`). -/
example : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ), Tendsto size atTop atTop →
    ∀ (s t : ℕ → ℝ), (∀ n, s n ≤ t n) → (∀ n, t n - s n ≤ 1) →
    ∀ (V : ℕ → Type) [∀ n, Fintype (V n)] (ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ) (A Cv : ℝ),
      0 ≤ A → 0 ≤ Cv →
      (∀ᶠ n : ℕ in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ Cv) →
      PerTimeDomAt P size ξ ζ → ∀ Ξ : ℕ → Set Ω, HighProbAt P size Ξ →
      ∀ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) →
      (∀ᶠ n : ℕ in atTop, ∀ (p : TimeIcc s t n × V n) (ω : Ω), ε n ≤ ζ n p ω) →
      (∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ u u' : TimeIcc s t n, (u' : ℝ) ≤ (u : ℝ) →
        (u : ℝ) - (u' : ℝ) ≤ (size n : ℝ) ^ (-A) → ∀ v : V n,
          ξ n (u, v) ω ≤ ξ n (u', v) ω + ε n ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) →
      StochDomAt P size ξ ζ := @nqLift_core_below

end RBM.Ind

/-! ## 5. The time modulus of `𝒦^{(k)}`, every `k ≥ 2`

The tree equations `(pro_dyncalK)` (`KLK_isKLoop`: `∂_t 𝒦^{(k)} = treeEqRhs`, on `t ∈ [0, 1)`) with the uniform crude
bound `KLbound_holds` (constants depending on `(d, m, κ, gmax, τ)` only, `τ = 1`) for the cut loops (lengths
`i + k - l + 1`, `l - i + 1 ∈ [2, k]`, total `k + 2`) bound the derivative by `k² C² 2^k N^{k+3} ≤ N^{2k+2}`
(eventually), and the mean value theorem on `[0, t_n]` gives the Lipschitz constant (paper-delta candidate
`T2258b`: the paper does not state a time modulus of `𝒦^{(k)}`). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Modulus

/-- A loop index of length `m` is `KLloopOf σ a` for vectors `σ`, `a` (the list bridge of `KLoopBound_KLK`,
`KLFinal.lean:168`). -/
private theorem nqLift_loopOf_eq {d L : ℕ} (J : LoopIdx (Zd d L)) (hJ : J.WF) {m : ℕ} (hm : J.length = m) :
    ∃ (σ : Fin m → Bool) (a : Fin m → Zd d L), J = KLloopOf d L σ a := by
  obtain ⟨σl, al⟩ := J
  have hal : al.length = m := hm
  subst hal
  have hJ' : σl.length = al.length := hJ
  refine ⟨fun i => σl.get (Fin.cast hJ'.symm i), al.get, ?_⟩
  refine LoopIdx.ext ?_ ?_
  · change σl = List.ofFn (fun i : Fin al.length => σl.get (Fin.cast hJ'.symm i))
    apply List.ext_getElem <;> simp [hJ']
  · change al = List.ofFn al.get
    exact (List.ofFn_get al).symm

/-- **The crude bound of `𝒦^{(m)}`** (`ML:Kbound` with `τ = 1`) as a statement about loop indices, with the constant
uniform over `KLPar κ gmax`. -/
private theorem nqLift_KLK_bound {d : ℕ} (hd : 3 ≤ d) {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (J : LoopIdx (Zd d p.L)), J.WF → J.length = m →
      ‖KLK d p.L p.g p.W p.E p.t J‖ ≤
        C * (p.L : ℝ) * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (m - 1) := by
  obtain ⟨C, hC, H⟩ := KLbound_holds d m κ gmax hd hm hκ hg 1 one_pos
  refine ⟨C, hC, fun p J hJ hJm => ?_⟩
  obtain ⟨σ, a, rfl⟩ := nqLift_loopOf_eq J hJ hJm
  have h := H p σ a
  rwa [Real.rpow_one] at h

/-- **The tree-equation right side is bounded by the product bound of its cut loops**: if every loop `J` of length
`2 ≤ |J| ≤ n` has `‖K J‖ ≤ C X^{|J|-1}`, then `‖treeEqRhs K I‖ ≤ W^d n² L^{2d} C² X^n` for `|I| = n` (the two cut
loops of `(k, l)` have lengths `k + n - l + 1`, `l - k + 1 ∈ [2, n]` with `(k + n - l) + (l - k) = n`;
`|S^{(B)}_{ab}| ≤ 1`). -/
private theorem nqLift_treeEq_bound {d L W : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L)
    {K : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)} {n : ℕ} (hI : I.WF) (hn : I.length = n)
    {X C : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hK : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n → ‖K J‖ ≤ C * X ^ (J.length - 1)) :
    ‖treeEqRhs d L W g K I‖ ≤
      (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d)) * (C ^ 2 * X ^ n) := by
  have hcardZ : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_Zd]; push_cast; rfl
  have hterm : ∀ k ∈ Finset.Icc 1 I.length, ∀ l ∈ Finset.Ioc k I.length, ∀ a b : Zd d L,
      ‖K (I.cutGlueL k l a) * SB d L g a b * K (I.cutGlueR k l b)‖ ≤ C ^ 2 * X ^ n := by
    intro k hk l hl a b
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hlenL := LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2
    have hlenR := LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2
    have hwL := LoopIdx.wf_cutGlueL I a hI hk.1 hl.1 hl.2
    have hwR := LoopIdx.wf_cutGlueR I b hI hk.1 hl.1 hl.2
    have h1 := hK _ hwL (by rw [hlenL]; omega) (by rw [hlenL]; omega)
    have h2 := hK _ hwR (by rw [hlenR]; omega) (by rw [hlenR]; omega)
    have hS := norm_SB_apply_le (d := d) (L := L) (g := g) hL a b
    have hX1 : 0 ≤ C * X ^ ((I.cutGlueL k l a).length - 1) := mul_nonneg hC (pow_nonneg hX _)
    have hX2 : 0 ≤ C * X ^ ((I.cutGlueR k l b).length - 1) := mul_nonneg hC (pow_nonneg hX _)
    rw [norm_mul, norm_mul]
    calc ‖K (I.cutGlueL k l a)‖ * ‖SB d L g a b‖ * ‖K (I.cutGlueR k l b)‖
        ≤ (C * X ^ ((I.cutGlueL k l a).length - 1)) * 1 *
            (C * X ^ ((I.cutGlueR k l b).length - 1)) :=
          mul_le_mul (mul_le_mul h1 hS (norm_nonneg _) hX1) h2 (norm_nonneg _) (by positivity)
      _ = C ^ 2 * X ^ n := by
          rw [hlenL, hlenR]
          have hexp : (k + I.length - l + 1 - 1) + (l - k + 1 - 1) = n := by omega
          calc C * X ^ (k + I.length - l + 1 - 1) * 1 * (C * X ^ (l - k + 1 - 1))
              = C ^ 2 * (X ^ (k + I.length - l + 1 - 1) * X ^ (l - k + 1 - 1)) := by ring
            _ = C ^ 2 * X ^ n := by rw [← pow_add, hexp]
  have hrhs : (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d)) * (C ^ 2 * X ^ n) =
      (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d) * (C ^ 2 * X ^ n)) := by ring
  rw [hrhs]
  unfold treeEqRhs
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsum : ‖∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        K (I.cutGlueL k l a) * SB d L g a b * K (I.cutGlueR k l b)‖ ≤
      ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        C ^ 2 * X ^ n := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun l hl => (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hterm k hk l hl a b))))
  refine hsum.trans ?_
  have hT : 0 ≤ (L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)) := by positivity
  calc ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        C ^ 2 * X ^ n
      ≤ ∑ k ∈ Finset.Icc 1 I.length, ((n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardZ, Nat.card_Ioc]
        have hkn : ((I.length - k : ℕ) : ℝ) ≤ n := by
          rw [← hn]; exact_mod_cast Nat.sub_le _ _
        calc ((I.length - k : ℕ) : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))
            ≤ (n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n))) :=
              mul_le_mul_of_nonneg_right hkn hT
          _ = _ := rfl
    _ = (n : ℝ) * ((n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hn]
        simp
    _ = (n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d) * (C ^ 2 * X ^ n) := by ring

/-- `0 ≤ W^{-d} B_{r,0} ≤ 2 N` for `r ≤ t < 1` with `(1 - t)⁻¹ ≤ N` (`W^{-d} B_{r,0} ≤ W^{-d} 2 (1 - r)⁻¹`,
`(1 - r)⁻¹ ≤ (1 - t)⁻¹`; `cont_Bctl_eq`). -/
private theorem nqLift_Bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) {r t : ℝ} (hrt : r ≤ t) (ht : t < 1) {N : ℝ}
    (htN : (1 - t)⁻¹ ≤ N) : sz.Bctl n r ≤ 2 * N := by
  have hr1 : r < 1 := hrt.trans_lt ht
  rw [RBM.Ind.ContinuityNet.cont_Bctl_eq sz n hr1]
  have h1t : 0 < 1 - t := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hy : (1 - r)⁻¹ ≤ N := (inv_anti₀ h1t (by linarith)).trans htN
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have e1 : (sz.lam n ^ 2 + (1 - r))⁻¹ ≤ (1 - r)⁻¹ :=
    inv_anti₀ h1r (by nlinarith [sq_nonneg (sz.lam n)])
  have e2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹ ≤ (1 - r)⁻¹ :=
    inv_anti₀ h1r (by nlinarith)
  have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
  have hsum : (sz.lam n ^ 2 + (1 - r))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹ ≤ 2 * N := by
    linarith
  have hnn : 0 ≤ (sz.lam n ^ 2 + (1 - r))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - r))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹)
      ≤ 1 * (2 * N) := mul_le_mul hWi hsum hnn zero_le_one
    _ = 2 * N := one_mul _

/-- **The time modulus of `𝒦^{(k)}`, every `k ≥ 2`** (`T2258_stKloop_lip`; G3 of the ticket, paper-delta candidate
`T2258b`): Lipschitz in time with the polynomial constant `N^{2k+2}`, uniformly in the labels on `[0, t_n]`, for sequences
with `|E_n| ≤ 2 - κ`, `0 < lam_n ≤ gmax` and `(1 - t_n)⁻¹ ≤ N` eventually (and `N → ∞`).  `KLK_isKLoop` gives
`∂_t 𝒦^{(k)} = treeEqRhs` on `[0, 1)`; the cut loops have lengths in `[2, k]` and `KLbound_holds` (constants depending
on `(d, m, κ, gmax)` only, `τ = 1`) bounds `‖treeEqRhs‖ ≤ k² C² 2^k N^{k+3} ≤ N^{2k+2}` (eventually); then the mean value
theorem on the convex set `[0, t_n]`.  `κ` and `gmax` are fixed before `n` (so the constants do not depend on `n`). -/
theorem stKloop_lip {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hsize : sz.SizeTendsto) (E t : ℕ → ℝ) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) (ht : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ‖STKloop sz n (E n) u σ a - STKloop sz n (E n) u' σ a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) * |u - u'| := by
  -- the constants of `ML:Kbound` (`τ = 1`) for the lengths `0 … k`
  have hC : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ (1 ≤ m → ∀ (p : KLPar κ gmax) (J : LoopIdx (Zd d p.L)), J.WF →
      J.length = m → ‖KLK d p.L p.g p.W p.E p.t J‖ ≤
        C * (p.L : ℝ) * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (m - 1)) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨C, hC0, hCb⟩ := nqLift_KLK_bound hd hκ hg m hm
      exact ⟨C, hC0, fun _ => hCb⟩
    · exact ⟨1, one_pos, fun h => absurd h hm⟩
  choose Cf hCf0 hCf using hC
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = ∑ m ∈ Finset.range (k + 1), Cf m := ⟨_, rfl⟩
  have hCm_ge : ∀ m ≤ k, Cf m ≤ Cm := fun m hm => by
    rw [hCm]
    exact Finset.single_le_sum (f := Cf) (fun i _ => (hCf0 i).le) (Finset.mem_range.2 (by omega))
  have hCm0 : 0 < Cm := lt_of_lt_of_le (hCf0 0) (hCm_ge 0 (Nat.zero_le k))
  filter_upwards [hE, hlam, htN,
    hsize.eventually_ge_atTop (max 1 ((k : ℝ) * k * Cm ^ 2 * 2 ^ k))] with n hEn hlamn htNn hNn
  intro u u' hu0 hut hu'0 hu't σ a
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hNn
  have hNQ : (k : ℝ) * k * Cm ^ 2 * 2 ^ k ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hNn
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hE2 : |E n| < 2 := by linarith
  have hKL := (KLK_isKLoop d (sz.L n) (sz.W n) (sz.lam n) (E n) hL3 hW1 hE2).1
  have hIWF : (KLloopOf d (sz.L n) σ a).WF := by simp [KLloopOf, LoopIdx.WF]
  have hIlen : (KLloopOf d (sz.L n) σ a).length = k := by simp [KLloopOf, LoopIdx.length]
  -- the counting facts
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW1)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hLd1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hLdN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hsz]; nlinarith
  have hL2d : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 (by omega)
  have hcount : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) *
      ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
    have hLd0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    have h1 : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) =
        ((sz.size n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) ^ d := by rw [hsz]; ring
    rw [h1]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ 2
        ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by
          gcongr
          exact hL2d.trans hLdN
      _ = ((sz.size n : ℕ) : ℝ) ^ 3 := by ring
  -- the derivative of `𝒦^{(k)}` is bounded by `N^{2k+2}` on `[0, t_n]`
  have hbound : ∀ r ∈ Set.Icc (0 : ℝ) (t n),
      ‖treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r)
        (KLloopOf d (sz.L n) σ a)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) := by
    intro r hr
    have hr1 : r < 1 := hr.2.trans_lt (ht n)
    have hX0 : 0 ≤ sz.Bctl n r := (st_Bctl_pos sz hr1).le
    have hXle : sz.Bctl n r ≤ 2 * ((sz.size n : ℕ) : ℝ) := nqLift_Bctl_le sz n hr.2 (ht n) htNn
    have hKJ : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r J‖ ≤
          (Cm * ((sz.L n : ℕ) : ℝ)) * (sz.Bctl n r) ^ (J.length - 1) := by
      intro J hJ h2 hJk
      have h := hCf J.length (by omega)
        (⟨sz.L n, sz.W n, hL3, hW1, sz.lam n, hlamn.1, hlamn.2, E n, hEn, r, hr.1, hr1⟩ : KLPar κ gmax)
        J hJ rfl
      refine h.trans ?_
      have hL0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
      have hCle := hCm_ge J.length hJk
      have hXp : 0 ≤ (sz.Bctl n r) ^ (J.length - 1) := pow_nonneg hX0 _
      change Cf J.length * ((sz.L n : ℕ) : ℝ) * (sz.Bctl n r) ^ (J.length - 1) ≤
        (Cm * ((sz.L n : ℕ) : ℝ)) * (sz.Bctl n r) ^ (J.length - 1)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hL0) hXp
    have h1 := nqLift_treeEq_bound (W := sz.W n) (g := sz.lam n) hL3 hIWF hIlen
      (X := sz.Bctl n r) (C := Cm * ((sz.L n : ℕ) : ℝ)) (by positivity) hX0 hKJ
    have hXk : (sz.Bctl n r) ^ k ≤ (2 * ((sz.size n : ℕ) : ℝ)) ^ k := pow_le_pow_left₀ hX0 hXle k
    calc ‖treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r)
          (KLloopOf d (sz.L n) σ a)‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * k * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)) *
            ((Cm * ((sz.L n : ℕ) : ℝ)) ^ 2 * (sz.Bctl n r) ^ k) := h1
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * k * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)) *
            ((Cm * ((sz.L n : ℕ) : ℝ)) ^ 2 * (2 * ((sz.size n : ℕ) : ℝ)) ^ k) := by
          gcongr
      _ = ((k : ℝ) * k * Cm ^ 2 * 2 ^ k) *
            (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) *
              ((sz.L n : ℕ) : ℝ) ^ 2) * ((sz.size n : ℕ) : ℝ) ^ k := by
          rw [mul_pow, mul_pow]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) ^ k := by
          gcongr
      _ = ((sz.size n : ℕ) : ℝ) ^ (k + 4) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) := pow_le_pow_right₀ hN1 (by omega)
  -- the mean value theorem on `[0, t_n]`
  have hf : ∀ r ∈ Set.Icc (0 : ℝ) (t n),
      HasDerivWithinAt (fun r => KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r (KLloopOf d (sz.L n) σ a))
        (treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r)
          (KLloopOf d (sz.L n) σ a)) (Set.Icc (0 : ℝ) (t n)) r :=
    fun r hr => (hKL r ⟨hr.1, hr.2.trans_lt (ht n)⟩ (KLloopOf d (sz.L n) σ a) hIWF
      (by rw [hIlen]; exact hk)).hasDerivWithinAt
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun r => treeEqRhs d (sz.L n) (sz.W n) (sz.lam n)
      (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r) (KLloopOf d (sz.L n) σ a))
    hf hbound (convex_Icc (0 : ℝ) (t n)) ⟨hu'0, hu't⟩ ⟨hu0, hut⟩
  rw [Real.norm_eq_abs] at hmvt
  exact hmvt

end Modulus

end RBM.Gauss.Sizes

/-! ## 6. The `ξ` modulus on `contGood`, the lift, and `stOeqNQ''_holds` -/

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

section Lift

variable {d : ℕ}

/-- **The mesh arithmetic** (`G5` of the ticket): for `δ ≤ N^{-(6 n_ + 20)}` and `N ≥ 3 n_ + 1`,
`N^{n_} (3 n_ N^{2n_+7} √δ + N^{2n_+2} δ) ≤ 1` (the first term is `≤ 3 n_ N^{-3}`, the second `≤ N^{-3}`). -/
private theorem nqLift_arith {N δ : ℝ} {n_ : ℕ} (hN : (3 * n_ + 1 : ℝ) ≤ N) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (N ^ (6 * n_ + 20))⁻¹) :
    N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ + N ^ (2 * n_ + 2) * δ) ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = N ^ (3 * n_ + 10) := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; exact pow_pos hN0 _
  have hMsq : N ^ (6 * n_ + 20) = M ^ 2 := by
    rw [hM, ← pow_mul]; congr 1; ring
  have hsqrt : Real.sqrt δ ≤ M⁻¹ := by
    have h1 : δ ≤ (M ^ 2)⁻¹ := by rw [← hMsq]; exact hδ
    have h2 : Real.sqrt δ ≤ Real.sqrt ((M ^ 2)⁻¹) := Real.sqrt_le_sqrt h1
    rwa [← inv_pow, Real.sqrt_sq (by positivity)] at h2
  have hA : N ^ n_ * (N ^ (2 * n_ + 7)) = N ^ (3 * n_ + 7) := by rw [← pow_add]; congr 1; ring
  have hM3 : M = N ^ (3 * n_ + 7) * N ^ 3 := by rw [hM, ← pow_add]
  have t1 : N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ) ≤ 3 * n_ * (N ^ 3)⁻¹ := by
    calc N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ)
        = 3 * n_ * (N ^ n_ * N ^ (2 * n_ + 7)) * Real.sqrt δ := by ring
      _ = 3 * n_ * N ^ (3 * n_ + 7) * Real.sqrt δ := by rw [hA]
      _ ≤ 3 * n_ * N ^ (3 * n_ + 7) * M⁻¹ := by
          gcongr
      _ = 3 * n_ * (N ^ 3)⁻¹ := by
          rw [hM3]; field_simp
  have hB : N ^ n_ * N ^ (2 * n_ + 2) = N ^ (3 * n_ + 2) := by rw [← pow_add]; congr 1; ring
  have hMM : N ^ (3 * n_ + 2) * N ^ 3 ≤ M ^ 2 := by
    rw [← hMsq, ← pow_add]
    exact pow_le_pow_right₀ hN1 (by omega)
  have t2 : N ^ n_ * (N ^ (2 * n_ + 2) * δ) ≤ (N ^ 3)⁻¹ := by
    calc N ^ n_ * (N ^ (2 * n_ + 2) * δ) = N ^ (3 * n_ + 2) * δ := by rw [← hB]; ring
      _ ≤ N ^ (3 * n_ + 2) * (M ^ 2)⁻¹ := by
          have h1 : δ ≤ (M ^ 2)⁻¹ := by rw [← hMsq]; exact hδ
          gcongr
      _ ≤ N ^ (3 * n_ + 2) * (N ^ (3 * n_ + 2) * N ^ 3)⁻¹ := by
          gcongr
      _ = (N ^ 3)⁻¹ := by field_simp
  have hN3 : (3 * n_ + 1 : ℝ) * (N ^ 3)⁻¹ ≤ 1 := by
    have hN3pos : 0 < N ^ 3 := by positivity
    rw [← div_eq_mul_inv, div_le_one hN3pos]
    have : N ≤ N ^ 3 := le_self_pow₀ hN1 (by norm_num)
    linarith
  calc N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ + N ^ (2 * n_ + 2) * δ)
      = N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ) + N ^ n_ * (N ^ (2 * n_ + 2) * δ) := by ring
    _ ≤ 3 * n_ * (N ^ 3)⁻¹ + (N ^ 3)⁻¹ := add_le_add t1 t2
    _ = (3 * n_ + 1) * (N ^ 3)⁻¹ := by ring
    _ ≤ 1 := hN3

/-- **The `ξ` closeness on `contGood`** (one-sided, for `s ≤ u' ≤ u ≤ t`, `u - u' ≤ N^{-(6 n_ + 20)}`):
`‖(𝓛-𝒦)_u‖ / B_u^{n_} ≤ ‖(𝓛-𝒦)_{u'}‖ / B_{u'}^{n_} + 1`.  `‖Δ𝓛‖ ≤ 3 n_ N^{2n_+7} √δ` (`LemDecCalELip_Lloop_sub`),
`‖Δ𝒦‖ ≤ N^{2n_+2} δ` (`stKloop_lip`), `B_{u'} ≤ B_u` (`STBctl_mono`), `N⁻¹ ≤ B_u` (`cont_inv_size_le_Bctl`); the
ratio term `‖(𝓛-𝒦)_{u'}‖ (B_{u'}^{-n_} - B_u^{-n_}) ≥ 0` of the two-sided estimate has the favourable sign
(`B_{u'} ≤ B_u`) and is dropped. -/
private theorem nqLift_xi_close (sz : Sizes d) (n : ℕ) (E : ℝ) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ)
    (hs0 : 0 ≤ s) (hsu' : s ≤ u') (hu'u : u' ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hM : (3 * n_ + 1 : ℝ) ≤ N) (hE2 : |E| < 2)
    (hQ : (etaT E t)⁻¹ ≤ N ^ 2) (hgood : ω ∈ ContinuityNet.contGood sz n)
    (hΔ : u - u' ≤ N ^ (-((6 * n_ + 20 : ℕ) : ℝ)))
    (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n))
    (hK : ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤ N ^ (2 * n_ + 2) * |u - u'|) :
    ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ / (sz.Bctl n u) ^ n_ ≤
      ‖Lloop sz n E u' σ a ω - STKloop sz n E u' σ a‖ / (sz.Bctl n u') ^ n_ + 1 := by
  have hu1 : u < 1 := hut.trans_lt ht1
  have hu'1 : u' < 1 := hu'u.trans_lt hu1
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hu0 : 0 ≤ u := hu'0.trans hu'u
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hBu' : 0 < sz.Bctl n u' := st_Bctl_pos sz hu'1
  have hBle : sz.Bctl n u' ≤ sz.Bctl n u := STBctl_mono sz n hu'u hu1
  have hBinv : N⁻¹ ≤ sz.Bctl n u := by
    rw [hN]; exact ContinuityNet.cont_inv_size_le_Bctl sz n hu0 hu1
  have hδ0 : 0 ≤ u - u' := sub_nonneg.2 hu'u
  have hL := LemDecCalELip_Lloop_sub sz n E ω hN hN1 hE2 ht1 hu0 hut hu'0 (hu'u.trans hut) hQ
    (fun c => by rw [hN]; exact hgood c) σ a
  rw [abs_of_nonneg hδ0] at hK hL
  have hδ' : u - u' ≤ (N ^ (6 * n_ + 20))⁻¹ := by
    refine hΔ.trans (le_of_eq ?_)
    rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
  have harith := nqLift_arith hM hδ0 hδ'
  have hNn : 0 < N ^ n_ := pow_pos hN0 _
  have hsmall : 3 * (n_ : ℝ) * N ^ (2 * n_ + 7) * Real.sqrt (u - u') + N ^ (2 * n_ + 2) * (u - u') ≤
      (sz.Bctl n u) ^ n_ := by
    have h1 : (N ^ n_)⁻¹ ≤ (sz.Bctl n u) ^ n_ := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hBinv n_
    refine le_trans ?_ h1
    calc 3 * (n_ : ℝ) * N ^ (2 * n_ + 7) * Real.sqrt (u - u') + N ^ (2 * n_ + 2) * (u - u')
        = (N ^ n_)⁻¹ * (N ^ n_ * (3 * (n_ : ℝ) * N ^ (2 * n_ + 7) * Real.sqrt (u - u') +
            N ^ (2 * n_ + 2) * (u - u'))) := by field_simp
      _ ≤ (N ^ n_)⁻¹ * 1 := mul_le_mul_of_nonneg_left harith (inv_nonneg.2 hNn.le)
      _ = (N ^ n_)⁻¹ := mul_one _
  have hsum2 : ‖Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω‖ + ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤
      (sz.Bctl n u) ^ n_ := by
    have : 3 * (n_ : ℝ) * N ^ (2 * n_ + 7) * Real.sqrt (u - u') + N ^ (2 * n_ + 2) * (u - u') ≤
        (sz.Bctl n u) ^ n_ := hsmall
    linarith
  have htri : ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤
      ‖Lloop sz n E u' σ a ω - STKloop sz n E u' σ a‖ +
        (‖Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω‖ + ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖) := by
    have e : Lloop sz n E u σ a ω - STKloop sz n E u σ a =
        (Lloop sz n E u' σ a ω - STKloop sz n E u' σ a) + (Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω) -
          (STKloop sz n E u σ a - STKloop sz n E u' σ a) := by ring
    rw [e]
    calc _ ≤ ‖(Lloop sz n E u' σ a ω - STKloop sz n E u' σ a) +
          (Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω)‖ + ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ :=
          norm_sub_le _ _
      _ ≤ _ := by
          have := norm_add_le (Lloop sz n E u' σ a ω - STKloop sz n E u' σ a)
            (Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω)
          linarith
  have hBpow : 0 < (sz.Bctl n u) ^ n_ := pow_pos hBu _
  calc ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ / (sz.Bctl n u) ^ n_
      ≤ (‖Lloop sz n E u' σ a ω - STKloop sz n E u' σ a‖ +
          (‖Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω‖ +
            ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖)) / (sz.Bctl n u) ^ n_ :=
        div_le_div_of_nonneg_right htri hBpow.le
    _ = ‖Lloop sz n E u' σ a ω - STKloop sz n E u' σ a‖ / (sz.Bctl n u) ^ n_ +
          (‖Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω‖ +
            ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖) / (sz.Bctl n u) ^ n_ := add_div _ _ _
    _ ≤ ‖Lloop sz n E u' σ a ω - STKloop sz n E u' σ a‖ / (sz.Bctl n u') ^ n_ + 1 := by
        refine add_le_add ?_ ((div_le_one hBpow).2 hsum2)
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hBu' _) (pow_le_pow_left₀ hBu'.le hBle _)

/-- `#V_n ≤ N^{2 n_}` for the label set `V_n = {σ non-alternating} × (Z_L^d)^{n_}` (`#σ ≤ 2^{n_}`, `#a = (L^d)^{n_}
≤ N^{n_}`, `N ≥ 2`). -/
private theorem nqLift_card_V (sz : Sizes d) (n_ n : ℕ) (hN2 : 2 ≤ sz.size n) :
    (Fintype.card ({σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d (sz.L n))) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ ((2 * n_ : ℕ) : ℝ) := by
  have h1 : Fintype.card {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ≤ 2 ^ n_ := by
    calc _ ≤ Fintype.card (Fin n_ → Bool) := Fintype.card_subtype_le _
      _ = 2 ^ n_ := by simp
  have h2 : Fintype.card (Fin n_ → Zd d (sz.L n)) = ((sz.L n) ^ d) ^ n_ := by
    simp
  have h3 : (sz.L n) ^ d ≤ sz.size n := by
    rw [Sizes.size]
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  have h4 : Fintype.card ({σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
      (Fin n_ → Zd d (sz.L n))) ≤ sz.size n ^ (2 * n_) := by
    rw [Fintype.card_prod, h2, two_mul, pow_add]
    exact Nat.mul_le_mul (h1.trans (Nat.pow_le_pow_left hN2 n_)) (Nat.pow_le_pow_left h3 n_)
  rw [Real.rpow_natCast]
  exact_mod_cast h4

/-- A pointwise larger right side keeps `≺` (copy of the private `nqFlow_prec_of_le_right`,
`NQEndFlow.lean:206`). -/
private theorem nqLift_prec_of_le_right {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually (copy of the private `KLFinal_flowLam`, `KLFinal.lean:294`). -/
private theorem nqLift_flowLam (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- **The lift `STNQConclPT'' → STNQConcl''`** (private: its binder is the owed per-time pin).  At the envelope controls
`(XL♯, XLK♯)` the per-time pin gives `PrecPT(ξ ≺ ζ♯)`; the one-sided net core (`nqLift_core_below`, `P = seqP`,
`Ξ = contGood`, `ε = 1`, `A = 6 n_ + 20`, `Cv = 2 n_`) gives `Prec(ξ ≺ ζ♯)`, and `ζ♯ ≤ ζ` gives `Prec(ξ ≺ ζ)`. -/
private theorem nqLift_lift (sz : Sizes d) (hd : 3 ≤ d) {E s t : ℕ → ℝ} {κ' gmax : ℝ} (hκ' : 0 < κ')
    (hg : 0 < gmax) (hE : ∀ n, |E n| ≤ 2 - κ') (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) (hPT : STNQConclPT'' sz E s t) :
    STNQConcl'' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsizeN : Tendsto sz.size atTop atTop := sz.tendsto_size hsize
  have hXL' : ∀ m n u, 1 ≤ nqFlowSharp t XL m n u := fun m n u => nqLift_sharp_one_le t XL m n u
  have hXLK' : ∀ m n u, 1 ≤ nqFlowSharp t XLK m n u := fun m n u => nqLift_sharp_one_le t XLK m n u
  have hXLp' : ∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XL m n q.1.2) := fun m hm hl =>
    nqLift_sharp_prec sz s t (fun n w ω => STXiL sz n (E n) w m ω) XL m hXL (hXLp m hm hl)
  have hXLKp' : ∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XLK m n q.1.2) := fun m hm hm' =>
    nqLift_sharp_prec sz s t (fun n w ω => STXiLK sz n (E n) w m ω) XLK m hXLK (hXLKp m hm hm')
  have hPT' := hPT n_ p hn hp (fun m n u => nqFlowSharp t XL m n u) (fun m n u => nqFlowSharp t XLK m n u)
    hXL' hXLK' hXLp' hXLKp'
  have hmain : Prec sz
      (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => nqFlowSharp t XL m n (q.1 : ℝ)) (fun m => nqFlowSharp t XLK m n (q.1 : ℝ))
          (sz.Bctl n (s n)) n_ p) := by
    refine nqLift_core_below (Ω := sz.SeqΩ) sz.seqP sz.size hsizeN s t (fun n => (hst n).le)
      (fun n => by linarith [hs0 n, ht1 n])
      (fun n => {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d (sz.L n))) _ _
      ((6 * n_ + 20 : ℕ) : ℝ) ((2 * n_ : ℕ) : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_ hPT'
      (ContinuityNet.contGood sz) (ContinuityNet.cont_highProbAt_good sz hsizeN) (fun _ => 1)
      (fun _ => zero_le_one) ?_ ?_
    · -- `hcard`
      filter_upwards [hsizeN.eventually_ge_atTop 2] with n hn2 using nqLift_card_V sz n_ n hn2
    · -- `hlow`: `ζ♯ ≥ 1`
      exact Eventually.of_forall fun n q ω =>
        nqLift_zeta_one_le sz ht1 n_ p n (by omega) q.1.2.1 q.1.2.2
    · -- `hclose`
      filter_upwards [LemDecCalELip_env sz E t κ' hκ' hE hsize htN (3 * (n_ : ℝ) + 1),
        stKloop_lip sz hd hκ' hg hsize E t (Eventually.of_forall hE) hlam ht1 htN n_ hn] with n hnum hK
      obtain ⟨hM, hN1, hE2, hQ, -⟩ := hnum
      intro ω hω u u' hle hΔ v
      obtain ⟨⟨σ, hσ⟩, a⟩ := v
      refine ⟨?_, ?_⟩
      · exact nqLift_xi_close sz n (E n) ω (hs0 n) u'.2.1 hle u.2.2 (ht1 n) rfl hM hE2 hQ hω hΔ σ a
          (hK u u' ((hs0 n).trans u.2.1) u.2.2 ((hs0 n).trans u'.2.1) u'.2.2 σ a)
      · have h1 := nqLift_zeta_mono sz ht1 hXL hXLK n_ p n u'.2.1 hle u.2.2
        have h2 := nqLift_zeta_one_le sz ht1 (XL := XL) (XLK := XLK) n_ p n (by omega) u.2.1 u.2.2
        change (sz.Bctl n (u' : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u' : ℝ) +
            STbootRHS 2 (fun m => nqFlowSharp t XL m n (u' : ℝ)) (fun m => nqFlowSharp t XLK m n (u' : ℝ))
              (sz.Bctl n (s n)) n_ p ≤
          2 * ((sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u : ℝ) +
            STbootRHS 2 (fun m => nqFlowSharp t XL m n (u : ℝ)) (fun m => nqFlowSharp t XLK m n (u : ℝ))
              (sz.Bctl n (s n)) n_ p)
        linarith
  exact nqLift_prec_of_le_right hmain fun n q ω =>
    nqLift_zeta_le sz ht1 hXL hXLK n_ p n q.1.2.1 q.1.2.2

end Lift

/-! ### The target -/

/-- **`stOeqNQ''_holds`: `lem:STOeq_NQ`, R2*, uniformly in `u`, for every `d ≥ 3`** (`T2258_stOeqNQ''_holds`;
`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148` with `B_s`; proof `3_5:1152-1190`).  The constant `𝔠_d` is the one of the
per-time pin `stOeqNQPT''_holds d` at the same `(κ, ε, 𝔡, C_d)`; the uniform conclusion `STNQConcl''` follows from the
per-time `STNQConclPT''` by the envelope `X♯` of the controls, the one-sided floor net, the `ξ` modulus on `contGood`
and the time modulus of `𝒦^{(k)}` (`stKloop_lip`).  Paper-delta candidates `T2258a` (the uniform-in-`u` form from the
per-time one: the paper's `N^{-C}`-net remark, `3_5:1182`, commented out; the same remark at `3_5:1764`) and
`T2258b` (the time modulus of `𝒦^{(k)}`; the paper does not state it). -/
theorem stOeqNQ''_holds : ∀ d : ℕ, STOeqNQ'' d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := stOeqNQPT''_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hPT := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  obtain ⟨hA, hE', ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hrange] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    calc (1 - t n)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ))⁻¹ := inv_anti₀ h2 (h1.trans hn)
      _ = ((sz.size n : ℕ) : ℝ) := by rw [Real.rpow_neg_one, inv_inv]
  exact nqLift_lift sz hd (half_pos hκ) (inv_pos.2 hA.2.1) (fun n => (hE' n).le) hA.2.2.1 hs hst ht1 htN
    (nqLift_flowLam sz hflow) hPT

/-! ## 7. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.NQEndFlowLiftInst`.  Data (the merged instance data, as `inst_OeqNQPT''`, `NQEndFlow.lean:974`):
`sz0` (`d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `N = 2^21`), the flow
`z0` (`z_n = 1/2 + i N_n^{-4/5}`, `flow_z0` at `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `s ≡ 0`, `t ≡ 1/16` (`t ≤ lemT z_n`,
`STCaseI`: `sz0_caseI`; `(con_st_ind)` for every `𝔠_d > 0`: `sz0_con`), `C_d = 1`.  `STKbound`, `STKward` are theorems of
the flow (`stKbound_of_flow`, `stKward_of_flow`); what stays a hypothesis of an example is a stochastic premise that is
another gate's pin (`STLK s`, `STStep2Concl`, the pair hypotheses `Ξ̂ ≺ 1` of the pin). -/

namespace NQEndFlowLiftInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- **(1) `stOeqNQ''_holds` at the data**: the uniform R2* pin at `(sz0, z0, s ≡ 0, t ≡ 1/16)`, `C_d = 1`: the constant
`𝔠_d ∈ (0, 1/100]`, then the stochastic premises of `STIngR` (`STKbound`, `STKward`, `STLK`, `STStep2Concl`), then the
conclusion `STNQConcl''`.  Every deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the regime `STCaseI`,
`(con_st_ind)`, `C_d > 0`) is discharged by `inst_ing`. -/
theorem inst_OeqNQ'' : InstIngConcl (fun sz E s t => STNQConcl'' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STNQConcl'' sz E s t) (stOeqNQ''_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos

/-- **(1) with the conclusion applied** at `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`: `STKbound`, `STKward` come from the flow,
the stochastic premises `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` of the pin (the conclusions of
Steps 3-4, other gates' pins) stay hypotheses; the uniform conclusion
`(𝓛-𝒦)^{(3)}_{u,σ,a}/B_u³ ≺ B_u^{1/6} + STbootRHS 2 1 1 B_s 3 1` for every non-alternating `σ`, label `a` and
`u ∈ [0, 1/16]`, with the union over `u` inside `P` (`Prec`), is the conclusion. -/
example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiL sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ))) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin 3 → Bool // ∃ k, σ k = σ (finRotate 3 k)} ×
        (Fin 3 → Zd 3 (sz0.L n)))
      (fun n q ω => ‖Lloop sz0 n (STflowE z0 n) (q.1 : ℝ) q.2.1.1 q.2.2 ω -
        STKloop sz0 n (STflowE z0 n) (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz0.Bctl n (q.1 : ℝ)) ^ 3)
      (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 2 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (sInst n)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqNQ''
  exact hC (stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(2) the envelope at the instance window `[0, 1/16]`**: the constant control `1` has envelope `1` at every time;
the control `2 + |u|` has envelope `2` at `u = 0` (`inf` over `[0, 1/16]`) and `1` at `u = 1 > t` (empty set, the floor);
the control `2 + u` (check file §4) has the same values at `u = 0`, `u = 1`. -/
example : ∀ (m n : ℕ) (u : ℝ), nqFlowSharp tInst (fun _ _ _ => (1 : ℝ)) m n u = 1 := fun m n u =>
  le_antisymm (nqLift_sharp_le tInst (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => le_rfl) m n u)
    (nqLift_sharp_one_le _ _ _ _ _)

example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + u) 0 0 0 = 2 ∧
    nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + u) 0 0 1 = 1 := by
  constructor
  · unfold nqFlowSharp
    have h : sInf ((fun u : ℝ => (2 : ℝ) + u) '' Set.Icc 0 (tInst 0)) = 2 := by
      refine IsLeast.csInf_eq ⟨⟨0, ⟨le_rfl, by simp only [tInst]; norm_num⟩, by norm_num⟩, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      linarith [hv.1]
    change max 1 (sInf ((fun u : ℝ => (2 : ℝ) + u) '' Set.Icc 0 (tInst 0))) = 2
    rw [h]; norm_num
  · unfold nqFlowSharp
    have h : Set.Icc (1 : ℝ) (tInst 0) = ∅ := Set.Icc_eq_empty (by simp only [tInst]; norm_num)
    change max 1 (sInf ((fun u : ℝ => (2 : ℝ) + u) '' Set.Icc 1 (tInst 0))) = 1
    rw [h, Set.image_empty, Real.sInf_empty]; norm_num

example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 0 = 2 ∧
    nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 1 = 1 := by
  constructor
  · unfold nqFlowSharp
    have h : sInf ((fun u : ℝ => (2 : ℝ) + |u|) '' Set.Icc 0 (tInst 0)) = 2 := by
      refine IsLeast.csInf_eq ⟨⟨0, ⟨le_rfl, by simp only [tInst]; norm_num⟩, by norm_num⟩, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      linarith [abs_nonneg v]
    change max 1 (sInf ((fun u : ℝ => (2 : ℝ) + |u|) '' Set.Icc 0 (tInst 0))) = 2
    rw [h]; norm_num
  · unfold nqFlowSharp
    have h : Set.Icc (1 : ℝ) (tInst 0) = ∅ := Set.Icc_eq_empty (by simp only [tInst]; norm_num)
    change max 1 (sInf ((fun u : ℝ => (2 : ℝ) + |u|) '' Set.Icc 1 (tInst 0))) = 1
    rw [h, Set.image_empty, Real.sInf_empty]; norm_num

/-- **(2) the envelope lemmas at `X = 2 + |u|`, `t ≡ 1/16`**: `X♯ ≤ X`, monotone on `u ≤ t`, and the pair hypothesis
`Ξ̂_w = w ≺ 2 + |u|` (a deterministic domination, `prec_of_le`) carries over to `X♯`. -/
example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 (1 / 32) ≤ (2 : ℝ) + |(1 / 32 : ℝ)| :=
  nqLift_sharp_le tInst (fun _ _ u => (2 : ℝ) + |u|) (fun _ _ u => by linarith [abs_nonneg u]) 0 0 (1 / 32)

example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 0 ≤
    nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 (1 / 32) :=
  nqLift_sharp_mono tInst (fun _ _ u => (2 : ℝ) + |u|) (fun _ _ u => by linarith [abs_nonneg u]) 0 0 0 (1 / 32)
    (by norm_num) (by simp only [tInst]; norm_num)

example : Prec sz0 (U := STPair sInst tInst) (fun n q ω => (fun (_ : ℕ) (w : ℝ) (_ : sz0.SeqΩ) => w) n q.1.1 ω)
    (fun n q _ => nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 n q.1.2) :=
  nqLift_sharp_prec sz0 sInst tInst (fun _ w _ => w) (fun _ _ u => (2 : ℝ) + |u|) 0
    (fun _ _ u => by linarith [abs_nonneg u])
    (prec_of_le sz0 (fun n q ω => by linarith [abs_nonneg q.1.2])
      (fun n q ω => by linarith [q.2.2.1, le_abs_self q.1.2]))

/-- **(3) `stKloop_lip` at the data**: `sz0`, `E = STflowE z0`, `t = tInst`, `k = 3`: `N_n → ∞` (`sz0_tendsto`),
`|E_n| < 2 - κ/2` and `0 < lam_n ≤ 𝔡⁻¹` from the flow, `t_n = 1/16 < 1`, `(1 - 1/16)⁻¹ = 16/15 ≤ N_n`; the conclusion
is the Lipschitz bound `N^8 |u - u'|` for `𝒦^{(3)}` on `[0, 1/16]`, eventually in `n`. -/
example : ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ tInst n → 0 ≤ u' → u' ≤ tInst n →
    ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd 3 (sz0.L n)),
      ‖STKloop sz0 n (STflowE z0 n) u σ a - STKloop sz0 n (STflowE z0 n) u' σ a‖ ≤
        ((sz0.size n : ℕ) : ℝ) ^ (2 * 3 + 2) * |u - u'| := by
  obtain ⟨-, hE', -, -⟩ := RBM.Green.v3_premises_of_stFlow sz0 (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_ht
  refine stKloop_lip sz0 (by norm_num) (κ := 1 / 10 / 2) (gmax := (1 / 10 : ℝ)⁻¹) (by norm_num)
    (by norm_num) sz0_tendsto (STflowE z0) tInst (Eventually.of_forall fun n => (hE' n).le)
    (nqLift_flowLam sz0 flow_z0) (fun n => by simp only [tInst]; norm_num) ?_ 3 (by norm_num)
  filter_upwards [sz0_tendsto.eventually_ge_atTop 2] with n hn
  have h : (1 - tInst n)⁻¹ = 16 / 15 := by simp only [tInst]; norm_num
  rw [h]
  linarith

/-- **(4) `nqLift_core_below` at the data**: `P = seqP sz0`, `size = sz0.size`, window `[0, 1/16]`, `V n = Fin 2`,
`ξ n (u, v) = u`, `ζ ≡ 1`, `A = Cv = 1`, `Ξ = contGood sz0`, `ε ≡ 1`: `#V = 2 ≤ N`, the per-time input by `precPT_of_le`
(`u ≤ 1/16 ≤ 1`), `ε ≤ ζ`, and `ξ(u) ≤ ξ(u') + 1`, `ζ(u') ≤ 2 ζ(u)` for `u' ≤ u` (`u ≤ 1/16 ≤ 1 + u'`). -/
example : StochDomAt sz0.seqP sz0.size (U := fun n => TimeIcc sInst tInst n × Fin 2)
    (fun n p _ => (p.1 : ℝ)) (fun _ _ _ => (1 : ℝ)) := by
  refine nqLift_core_below (Ω := sz0.SeqΩ) sz0.seqP sz0.size (sz0.tendsto_size sz0_tendsto) sInst tInst
    (fun n => (sz0_hst n).le) (fun n => by simp only [sInst, tInst]; norm_num) (fun _ => Fin 2)
    (fun n p _ => (p.1 : ℝ)) (fun _ _ _ => (1 : ℝ)) 1 1 zero_le_one zero_le_one ?_
    (precPT_of_le sz0 (fun n p ω => zero_le_one) (fun n p ω => ?_))
    (ContinuityNet.contGood sz0) (ContinuityNet.cont_highProbAt_good sz0 (sz0.tendsto_size sz0_tendsto))
    (fun _ => 1) (fun _ => zero_le_one) (Eventually.of_forall fun n p ω => le_rfl) ?_
  · -- `#V = 2 ≤ N`
    filter_upwards [sz0_tendsto.eventually_ge_atTop 2] with n hn
    rw [Real.rpow_one, Fintype.card_fin]
    exact_mod_cast hn
  · -- the per-time input: `u ≤ 1`
    have := p.1.2.2
    simp only [tInst] at this
    change (p.1 : ℝ) ≤ 1
    linarith
  · -- the one-sided closeness
    refine Eventually.of_forall fun n ω _ u u' hle _ v => ⟨?_, by norm_num⟩
    have h1 := u.2.2
    have h2 := u'.2.1
    simp only [sInst, tInst] at h1 h2
    change (u : ℝ) ≤ (u' : ℝ) + 1
    linarith

/-- **(5) `nqLift_netPt_floor` and `nqLift_bootRHS_mono` at numbers**: the floor net point of `x = 1/2` at `A = 1`,
`N = 4`; `STbootRHS 2 (XL ≡ 1) (XLK ≡ 1) (1/2) 3 1 ≤ STbootRHS 2 (XL ≡ 2) (XLK ≡ 3) (1/2) 3 1`. -/
example : ∃ k : Fin (netSize 1 4 + 1), netPt 1 1 4 k ≤ (1 / 2 : ℝ) ∧
    (1 / 2 : ℝ) - netPt 1 1 4 k ≤ 1 / (netSize 1 4 : ℝ) :=
  nqLift_netPt_floor 1 4 (1 / 2) (by norm_num) (by norm_num)

example : STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) 3 1 ≤
    STbootRHS 2 (fun _ => (2 : ℝ)) (fun _ => (3 : ℝ)) (1 / 2) 3 1 :=
  nqLift_bootRHS_mono 2 _ _ _ _ (1 / 2) 3 1 (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)

/-- **(5) the pinned statements of the check file, section 3** (public ones): `stKloop_lip` and `stOeqNQ''_holds` have
exactly the pinned types. -/
example : ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ gmax : ℝ}, 0 < κ → 0 < gmax → sz.SizeTendsto →
    ∀ (E t : ℕ → ℝ), (∀ᶠ n in atTop, |E n| ≤ 2 - κ) →
      (∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) → (∀ n, t n < 1) →
      (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
      ∀ k : ℕ, 2 ≤ k → ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
        ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
          ‖STKloop sz n (E n) u σ a - STKloop sz n (E n) u' σ a‖ ≤
            ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) * |u - u'| := @stKloop_lip

example : ∀ d : ℕ, STOeqNQ'' d := @stOeqNQ''_holds

end NQEndFlowLiftInst

/-- The pinned statements of the envelope lemmas (check file §3: `T2258_sharp_one_le`, `T2258_sharp_le`,
`T2258_sharp_mono`, `T2258_sharp_prec`). -/
example : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ), 1 ≤ nqFlowSharp t X m n u :=
  @nqLift_sharp_one_le

example : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u : ℝ), nqFlowSharp t X m n u ≤ X m n u := @nqLift_sharp_le

example : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u u' : ℝ), u ≤ u' → u' ≤ t n → nqFlowSharp t X m n u ≤ nqFlowSharp t X m n u' :=
  @nqLift_sharp_mono

example : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m : ℕ),
    (∀ m n u, 1 ≤ X m n u) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => X m n q.1.2) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => nqFlowSharp t X m n q.1.2) :=
  @nqLift_sharp_prec

end RBM.Ind

end

#print axioms RBM.Ind.nqFlowSharp
#print axioms RBM.Gauss.Sizes.stKloop_lip
#print axioms RBM.Ind.stOeqNQ''_holds
#print axioms RBM.Ind.NQEndFlowLiftInst.inst_OeqNQ''
