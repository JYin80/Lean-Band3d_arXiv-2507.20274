/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QEndB1
import RBM3D.Induction.QtNonzeroBoot
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.ScaleFacts
import RBM3D.Green.Pins
import RBM3D.Gauss.Domination

/-!
# The case-(i) round at the flow, uniformly in the pair, and `stOeqQt'_holds` (`d ≥ 3`)

Case (i), `1 - t ≥ ilambda²/L²`.  Paper: Lemma 4.10 (`lem:STOeq_Qt`, (4.36) `am;asoi222`) and its proof in
Subsection 4.5; the `N^{-C}`-net remark with `lem_ConArg` in the proof of Lemma 4.17 (the same remark for
case (ii)).  The per-time statement is in `Induction/QEndB1`.

## What is here

* §2 the envelope lemmas (private, as in `NQEndFlowLift`; `nqFlowSharp` is the
  public vocabulary): the pair hypotheses carry over to `XL♯ = nqFlowSharp t XL`,
  `XLK♯ = nqFlowSharp t XLK`;
* §3 the bootstrap right side `ζ♯` at `lo = 1` (private): `ζ♯` non-decreasing in `u ∈ [s_n, t_n]`, `ζ♯ ≤ ζ`, `1 ≤ ζ♯`;
* §4 the one-sided floor-net core (private);
* §5 the mesh arithmetic and the per-loop closeness, the
  gluing (`qtLift_xiLK_close`: the closeness passes through the finite `sup'` of `STmaxLK`;
  `qtLift_diag_PT`: the restriction of the per-time statement to the diagonal `v = u`;
  `qtLift_diag_to_pair`: the diagonal statement gives the pair statement because `ζ♯` is
  non-decreasing) and the lift `qtLift_lift : STXiRoundPT'' → STXiRound'` (private);
* §6 `RBM.Ind.stXiRoundQt_holds` (the case-(i) round, twin of `stXiRoundNZ_holds`) and
  `RBM.Ind.stOeqQt'_holds` (= `stXiBootR_of_round d STCaseI (stXiRoundQt_holds d)`).

The file adds no drift or good-set level: the current length `n_` enters only
through `STXiRoundPT''` (its self-absorbing summand `B_u^{1/6} XLK n_ u`) and is removed
by `stXiBootR_of_round`.  Every helper that is not part of the statements is `private` with
the prefix `qtLift_`.  The four gluing lemmas of §5 and the two theorems of §6 are specific to this file;
the remaining private lemmas are those of `NQEndFlowLift` (no port from RBM1D/RBM2D).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 2. The envelope lemmas -/

/-- Envelope (a): `1 ≤ X♯`. -/
private theorem qtLift_sharp_one_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ),
    1 ≤ nqFlowSharp t X m n u :=
  fun _ _ _ _ _ => le_max_left _ _

/-- Envelope (b): `X♯ ≤ X` for a bound `X ≥ 1`. -/
private theorem qtLift_sharp_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u : ℝ), nqFlowSharp t X m n u ≤ X m n u := by
  intro t X hX m n u
  unfold nqFlowSharp
  refine max_le (hX m n u) ?_
  by_cases hu : u ≤ t n
  · exact csInf_le ⟨1, by rintro _ ⟨v, -, rfl⟩; exact hX m n v⟩ ⟨u, ⟨le_rfl, hu⟩, rfl⟩
  · rw [Set.Icc_eq_empty hu, Set.image_empty, Real.sInf_empty]
    exact zero_le_one.trans (hX m n u)

/-- Envelope (c): `X♯` is non-decreasing in `u ≤ t_n`. -/
private theorem qtLift_sharp_mono : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
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
private theorem qtLift_sharp_prec : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ)
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

/-- `STbootRHS` is monotone in both bounds (`B > 0` fixed, all exponents `≥ 0`). -/
private theorem qtLift_bootRHS_mono : ∀ (lo : ℕ) (XL XL' XLK XLK' : ℕ → ℝ) (B : ℝ) (n_ p : ℕ), 0 < B →
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

/-- `1 ≤ STbootRHS lo XL XLK B k p` for `XL ≥ 1`, `XLK ≥ 0`, `B ≥ 0`, `k ≥ 1` (as the private
`nqFlow_bootRHS_one_le`). -/
private theorem qtLift_bootRHS_one_le {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 1 ≤ k)
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

/-- **`ζ♯` is non-decreasing in `u`** (the first summand of `STbootRHS` is at the fixed `B_s`, so no ratio of
`B` is needed): for `s_n ≤ θ ≤ u ≤ t_n < 1`, the right side of `STXiRoundPT''` at the envelope bounds
`(XL♯, XLK♯)` at `θ` is at most that at `u` (`B_θ^{1/6} ≤ B_u^{1/6}` by `STBctl_mono`, the envelopes are
non-decreasing, `STbootRHS` is monotone in the bounds). -/
private theorem qtLift_zeta_mono (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (n_ p n : ℕ) {θ u : ℝ} (hsθ : s n ≤ θ) (hθu : θ ≤ u) (hut : u ≤ t n) :
    (sz.Bctl n θ) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n θ +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n θ) (fun m => nqFlowSharp t XLK m n θ)
        (sz.Bctl n (s n)) n_ p ≤
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p := by
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hθ1 : θ < 1 := hθu.trans_lt hu1
  have hs1 : s n < 1 := hsθ.trans_lt hθ1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBθ : 0 < sz.Bctl n θ := st_Bctl_pos sz hθ1
  have hBθu : sz.Bctl n θ ≤ sz.Bctl n u := STBctl_mono sz n hθu hu1
  refine add_le_add ?_ (qtLift_bootRHS_mono 1 _ _ _ _ _ n_ p hBs
    (fun m => zero_le_one.trans (qtLift_sharp_one_le t XL m n θ))
    (fun m => zero_le_one.trans (qtLift_sharp_one_le t XLK m n θ))
    (fun m => qtLift_sharp_mono t XL hXL m n θ u hθu hut)
    (fun m => qtLift_sharp_mono t XLK hXLK m n θ u hθu hut))
  exact mul_le_mul (Real.rpow_le_rpow hBθ.le hBθu (by norm_num))
    (qtLift_sharp_mono t XLK hXLK n_ n θ u hθu hut) (zero_le_one.trans (qtLift_sharp_one_le t XLK n_ n θ))
    (Real.rpow_nonneg (hBθ.le.trans hBθu) _)

/-- **`ζ♯ ≤ ζ`** pointwise (`X♯ ≤ X`, `STbootRHS` monotone in the bounds). -/
private theorem qtLift_zeta_le (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (n_ p n : ℕ) {u : ℝ} (hsu : s n ≤ u) (hut : u ≤ t n) :
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p ≤
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * XLK n_ n u +
      STbootRHS 1 (fun m => XL m n u) (fun m => XLK m n u) (sz.Bctl n (s n)) n_ p := by
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hs1 : s n < 1 := hsu.trans_lt hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  refine add_le_add ?_ (qtLift_bootRHS_mono 1 _ _ _ _ _ n_ p hBs
    (fun m => zero_le_one.trans (qtLift_sharp_one_le t XL m n u))
    (fun m => zero_le_one.trans (qtLift_sharp_one_le t XLK m n u))
    (fun m => qtLift_sharp_le t XL hXL m n u) (fun m => qtLift_sharp_le t XLK hXLK m n u))
  exact mul_le_mul_of_nonneg_left (qtLift_sharp_le t XLK hXLK n_ n u) (Real.rpow_nonneg hBu.le _)

/-- **`1 ≤ ζ♯`** (`ζ♯ ≥ 1` is the floor `ε_n = 1` of the net lift): `XL♯ ≥ 1`, `XLK♯ ≥ 1`, `B ≥ 0`, `n_ ≥ 1`. -/
private theorem qtLift_zeta_one_le (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (n_ p n : ℕ) (hn : 1 ≤ n_) {u : ℝ} (hsu : s n ≤ u) (hut : u ≤ t n) :
    1 ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p := by
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hs1 : s n < 1 := hsu.trans_lt hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have h0 : 0 ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u :=
    mul_nonneg (Real.rpow_nonneg hBu.le _) (zero_le_one.trans (qtLift_sharp_one_le t XLK n_ n u))
  have := qtLift_bootRHS_one_le (lo := 1) (XL := fun m => nqFlowSharp t XL m n u)
    (XLK := fun m => nqFlowSharp t XLK m n u) (B := sz.Bctl n (s n)) (k := n_) (p := p) hn
    (fun m => qtLift_sharp_one_le t XL m n u)
    (fun m => zero_le_one.trans (qtLift_sharp_one_le t XLK m n u)) hBs.le
  linarith

end RightSide

/-! ## 4. The one-sided net core

`ContinuityNet.cont_core` asks the closeness of `ξ` and `ζ` for every pair of
times at distance `≤ N^{-A}`; the envelope `ζ♯` is non-decreasing, so `ζ♯(θ) ≤ 2 ζ♯(u)` holds only for `θ ≤ u`.  The
net point of `u` is therefore the floor point `θ = s_n + ⌊(u - s_n) m⌋/m ≤ u` (`m = netSize`), and the closeness is asked
only for `u' ≤ u`; the clamp `min (t_n)` of `contTime` is inactive at `θ`.  Everything else is the text of
`cont_core`. -/

section Core

/-- as the private `ContinuityNet.cont_stochDomAt_of_subset`. -/
private theorem qtLift_stochDomAt_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
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

/-- The clamped net of `[s n, t n]` (as the private `ContinuityNet.contTime`). -/
private def qtLift_time (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

/-- as `ContinuityNet.contTime_mem`. -/
private theorem qtLift_time_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : qtLift_time s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

/-- **The floor net point** (as `nzLift_netPt_floor`; the witness of `exists_netPt_close`, at
`T = 1`, with the one-sided information `netPt ≤ x`): `netPt` at `⌊x · netSize⌋` lies in `[x - 1/netSize, x]`. -/
private theorem qtLift_netPt_floor : ∀ (A : ℝ) (N : ℕ) (x : ℝ), 0 ≤ x → x ≤ 1 →
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

/-- **The one-sided net lift** (as `nzLift_core_below`): `cont_core` with the
closeness hypothesis `hclose` asked only for `u' ≤ u` (the floor net point lies below `u`).  Nothing else changes: a
per-time domination on `TimeIcc s t n × V n`, a polynomial bound on `#V n`, a good event `Ξ` of high probability on
which `ξ` moves up by at most `ε n` and `ζ` down by a factor `2` along a downward time change of size `size^{-A}`, and
`ε ≤ ζ`, give the uniform domination. -/
private theorem qtLift_core_below : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ),
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
    ⟨qtLift_time s t (A + 1) (size n) n k, qtLift_time_mem hst _ _ n k⟩
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
  refine qtLift_stochDomAt_of_subset hsize hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
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
  obtain ⟨k, hk1, hk2⟩ := qtLift_netPt_floor (A + 1) (size n) ((u : ℝ) - s n)
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

/-! ## 5. The mesh arithmetic, the closeness, the lift -/

section Lift

variable {d : ℕ}

/-- **The mesh arithmetic** (as `nzLift_arith`, without the factor `2^{n_}`): for `δ ≤ N^{-(6 n_ + 20)}` and `N ≥ 3 n_ + 1`,
`N^{n_} (3 n_ N^{2n_+7} √δ + N^{2n_+2} δ) ≤ 1` (the first term is `≤ 3 n_ N^{-3}`, the second `≤ N^{-3}`). -/
private theorem qtLift_arith {N δ : ℝ} {n_ : ℕ} (hN : (3 * n_ + 1 : ℝ) ≤ N) (hδ0 : 0 ≤ δ)
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

/-- **The per-loop `ξ` closeness on `contGood`** (as `nzLift_xi_close`, without the projection; one-sided, for `s ≤ u' ≤ u ≤ t`, `u - u' ≤ N^{-(6 n_ + 20)}`):
`‖(𝓛-𝒦)_u‖ / B_u^{n_} ≤ ‖(𝓛-𝒦)_{u'}‖ / B_{u'}^{n_} + 1`.  `‖Δ𝓛‖ ≤ 3 n_ N^{2n_+7} √δ` (`LemDecCalELip_Lloop_sub`),
`‖Δ𝒦‖ ≤ N^{2n_+2} δ` (`stKloop_lip`), `B_{u'} ≤ B_u` (`STBctl_mono`), `N⁻¹ ≤ B_u` (`cont_inv_size_le_Bctl`); the
ratio term `‖(𝓛-𝒦)_{u'}‖ (B_{u'}^{-n_} - B_u^{-n_}) ≥ 0` of the two-sided estimate has the favourable sign
(`B_{u'} ≤ B_u`) and is dropped. -/
private theorem qtLift_xi_close (sz : Sizes d) (n : ℕ) (E : ℝ) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ)
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
  have harith := qtLift_arith hM hδ0 hδ'
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

/-- A pointwise larger right side keeps `≺` (as the private `nqFlow_prec_of_le_right`). -/
private theorem qtLift_prec_of_le_right {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually (as the private `KLFinal_flowLam`). -/
private theorem qtLift_flowLam (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- **The one-sided closeness of `Ξ̂^{(𝓛-𝒦)}_{·,n_}` on `contGood`**: the
per-loop closeness `qtLift_xi_close` passed through the finite `sup'` of `STmaxLK` (`Finset.sup'_le`, `Finset.le_sup'`):
for `s ≤ u' ≤ u ≤ t`, `u - u' ≤ N^{-(6 n_ + 20)}`, `STXiLK_u ≤ STXiLK_{u'} + 1` (the leading `1` of `STXiLK` cancels). -/
private theorem qtLift_xiLK_close (sz : Sizes d) (n : ℕ) (E : ℝ) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ)
    (hs0 : 0 ≤ s) (hsu' : s ≤ u') (hu'u : u' ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hM : (3 * n_ + 1 : ℝ) ≤ N) (hE2 : |E| < 2)
    (hQ : (etaT E t)⁻¹ ≤ N ^ 2) (hgood : ω ∈ ContinuityNet.contGood sz n)
    (hΔ : u - u' ≤ N ^ (-((6 * n_ + 20 : ℕ) : ℝ)))
    (hK : ∀ (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)),
      ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤ N ^ (2 * n_ + 2) * |u - u'|) :
    STXiLK sz n E u n_ ω ≤ STXiLK sz n E u' n_ ω + 1 := by
  have hu1 : u < 1 := hut.trans_lt ht1
  have hu'1 : u' < 1 := hu'u.trans_lt hu1
  have hBpow : 0 < (sz.Bctl n u) ^ n_ := pow_pos (st_Bctl_pos sz hu1) _
  have hBpow' : 0 < (sz.Bctl n u') ^ n_ := pow_pos (st_Bctl_pos sz hu'1) _
  have key : STmaxLK sz n E u n_ ω / (sz.Bctl n u) ^ n_ ≤
      STmaxLK sz n E u' n_ ω / (sz.Bctl n u') ^ n_ + 1 := by
    rw [div_le_iff₀ hBpow]
    refine Finset.sup'_le _ _ fun p _ => ?_
    rw [← div_le_iff₀ hBpow]
    refine (qtLift_xi_close sz n E ω hs0 hsu' hu'u hut ht1 hN hM hE2 hQ hgood hΔ p.1 p.2 (hK p.1 p.2)).trans ?_
    have h2 : ‖Lloop sz n E u' p.1 p.2 ω - STKloop sz n E u' p.1 p.2‖ ≤ STmaxLK sz n E u' n_ ω :=
      Finset.le_sup' (fun p : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)) =>
        ‖Lloop sz n E u' p.1 p.2 ω - STKloop sz n E u' p.1 p.2‖) (Finset.mem_univ p)
    have h3 := div_le_div_of_nonneg_right h2 hBpow'.le
    linarith
  unfold STXiLK
  linarith

/-- **Diagonal restriction of the per-time statement**: a per-time `≺` over the
pairs, whose left side depends on `q.1.1` only and whose right side on `q.1.2` only, restricts to the diagonal
`w ↦ ((w, w), _)`: a per-time `≺` over `TimeIcc s t n × Unit` (the shape `qtLift_core_below` consumes). -/
private theorem qtLift_diag_PT : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (g : ℕ → ℝ → ℝ),
    PrecPT sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => g n q.1.2) →
    PrecPT sz (U := fun n => TimeIcc s t n × Unit) (fun n w ω => f n (w.1 : ℝ) ω) (fun n w _ => g n (w.1 : ℝ)) := by
  intro d sz s t f g h τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl w
  exact hl ⟨((w.1 : ℝ), (w.1 : ℝ)), w.1.2.1, le_rfl, w.1.2.2⟩

/-- **Diagonal → pair propagation**: for a right side `g` non-decreasing in
the endpoint on `[s_n, t_n]`, the uniform `≺` on the diagonal gives the uniform `≺` over the pairs (`g n q.1.1 ≤ g n q.1.2`:
the pair-bad event is inside the diagonal-bad event at the same `τ`; `measure_mono`). -/
private theorem qtLift_diag_to_pair : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (g : ℕ → ℝ → ℝ),
    (∀ (n : ℕ) (v u : ℝ), s n ≤ v → v ≤ u → u ≤ t n → g n v ≤ g n u) →
    Prec sz (U := fun n => TimeIcc s t n × Unit) (fun n w ω => f n (w.1 : ℝ) ω) (fun n w _ => g n (w.1 : ℝ)) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => g n q.1.2) := by
  intro d sz s t f g hmono h τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  obtain ⟨q, hq⟩ := hω
  have hc : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨(⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩, ()), ?_⟩
  have hq' : ((sz.size n : ℕ) : ℝ) ^ τ * g n q.1.2 < f n q.1.1 ω := hq
  change ((sz.size n : ℕ) : ℝ) ^ τ * g n q.1.1 < f n q.1.1 ω
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hmono n q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) hc) hq'

/-- **The lift `STXiRoundPT'' → STXiRound'`** (private: its binder is the per-time statement, which no public theorem
concludes).  At the envelope bounds `(XL♯, XLK♯)` the per-time statement gives
`PrecPT(Ξ̂ ≺ ζ♯)` over the pairs; restricted to the diagonal (`qtLift_diag_PT`), the one-sided net core
(`qtLift_core_below`, `P = seqP`, `V = Unit`, `Cv = 0`, `Ξ = contGood`, `ε = 1`, `A = 6 n_ + 20`) gives the uniform `Prec`
on the diagonal, `qtLift_diag_to_pair` the uniform `Prec` over the pairs, and `ζ♯ ≤ ζ` gives `STXiRound'`. -/
private theorem qtLift_lift (sz : Sizes d) (hd : 3 ≤ d) {E s t : ℕ → ℝ} {κ' gmax : ℝ} (hκ' : 0 < κ')
    (hg : 0 < gmax) (hE : ∀ n, |E n| ≤ 2 - κ') (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) (hPT : STXiRoundPT'' sz E s t) :
    STXiRound' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsizeN : Tendsto sz.size atTop atTop := sz.tendsto_size hsize
  have hXL' : ∀ m n u, 1 ≤ nqFlowSharp t XL m n u := fun m n u => qtLift_sharp_one_le t XL m n u
  have hXLK' : ∀ m n u, 1 ≤ nqFlowSharp t XLK m n u := fun m n u => qtLift_sharp_one_le t XLK m n u
  have hXLp' : ∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XL m n q.1.2) := fun m hm hl =>
    qtLift_sharp_prec sz s t (fun n w ω => STXiL sz n (E n) w m ω) XL m hXL (hXLp m hm hl)
  have hXLKp' : ∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XLK m n q.1.2) := fun m hm hm' =>
    qtLift_sharp_prec sz s t (fun n w ω => STXiLK sz n (E n) w m ω) XLK m hXLK (hXLKp m hm hm')
  have hPT' := hPT n_ p hn hp (fun m n u => nqFlowSharp t XL m n u) (fun m n u => nqFlowSharp t XLK m n u)
    hXL' hXLK' hXLp' hXLKp'
  have hdiag := qtLift_diag_PT sz s t (fun n w ω => STXiLK sz n (E n) w n_ ω)
    (fun n u => (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p) hPT'
  have hmain : Prec sz (U := fun n => TimeIcc s t n × Unit)
      (fun n w ω => STXiLK sz n (E n) (w.1 : ℝ) n_ ω)
      (fun n w _ => (sz.Bctl n (w.1 : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (w.1 : ℝ) +
        STbootRHS 1 (fun m => nqFlowSharp t XL m n (w.1 : ℝ)) (fun m => nqFlowSharp t XLK m n (w.1 : ℝ))
          (sz.Bctl n (s n)) n_ p) := by
    refine qtLift_core_below (Ω := sz.SeqΩ) sz.seqP sz.size hsizeN s t (fun n => (hst n).le)
      (fun n => by linarith [hs0 n, ht1 n]) (fun _ => Unit) _ _ ((6 * n_ + 20 : ℕ) : ℝ) 0
      (Nat.cast_nonneg _) le_rfl ?_ hdiag (ContinuityNet.contGood sz)
      (ContinuityNet.cont_highProbAt_good sz hsizeN) (fun _ => 1) (fun _ => zero_le_one) ?_ ?_
    · -- `hcard`: `#Unit = 1 ≤ N^0`
      exact Eventually.of_forall fun n => by simp
    · -- `hlow`: `ζ♯ ≥ 1`
      exact Eventually.of_forall fun n q ω =>
        qtLift_zeta_one_le sz ht1 n_ p n (by omega) q.1.2.1 q.1.2.2
    · -- `hclose`
      filter_upwards [LemDecCalELip_env sz E t κ' hκ' hE hsize htN (3 * (n_ : ℝ) + 1),
        stKloop_lip sz hd hκ' hg hsize E t (Eventually.of_forall hE) hlam ht1 htN n_ hn] with n hnum hK
      obtain ⟨hM, hN1, hE2, hQ, -⟩ := hnum
      intro ω hω u u' hle hΔ v
      refine ⟨?_, ?_⟩
      · exact qtLift_xiLK_close sz n (E n) ω (hs0 n) u'.2.1 hle u.2.2 (ht1 n) rfl hM hE2 hQ hω hΔ
          (fun σ a => hK u u' ((hs0 n).trans u.2.1) u.2.2 ((hs0 n).trans u'.2.1) u'.2.2 σ a)
      · have h1 := qtLift_zeta_mono sz ht1 hXL hXLK n_ p n u'.2.1 hle u.2.2
        have h2 := qtLift_zeta_one_le sz ht1 (XL := XL) (XLK := XLK) n_ p n (by omega) u.2.1 u.2.2
        change (sz.Bctl n (u' : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u' : ℝ) +
            STbootRHS 1 (fun m => nqFlowSharp t XL m n (u' : ℝ)) (fun m => nqFlowSharp t XLK m n (u' : ℝ))
              (sz.Bctl n (s n)) n_ p ≤
          2 * ((sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u : ℝ) +
            STbootRHS 1 (fun m => nqFlowSharp t XL m n (u : ℝ)) (fun m => nqFlowSharp t XLK m n (u : ℝ))
              (sz.Bctl n (s n)) n_ p)
        linarith
  have hpair := qtLift_diag_to_pair sz s t (fun n w ω => STXiLK sz n (E n) w n_ ω)
    (fun n u => (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p)
    (fun n v u hsv hvu hut => qtLift_zeta_mono sz ht1 hXL hXLK n_ p n hsv hvu hut) hmain
  exact qtLift_prec_of_le_right hpair fun n q ω =>
    qtLift_zeta_le sz ht1 hXL hXLK n_ p n (q.2.1.trans q.2.2.1) q.2.2.2

end Lift

/-! ## 6. The case-(i) round and `stOeqQt'_holds` -/

/-- **The case-(i) round** (Lemma 4.10 `lem:STOeq_Qt` and its proof in Subsection 4.5, with the `N^{-C}`-net remark): the case-(i) twin of `stXiRoundNZ_holds`.  At every flow
setting of `STIngR d STCaseI` the round statement `STXiRound'` holds, with the constant `𝔠_d` of `stOeqQtRoundPT''_holds d`.
The uniform-in-the-pair conclusion `Prec` follows from the per-time `PrecPT` by the envelope `X♯` of the bounds,
the diagonal restriction, the one-sided floor net, the `ξ` modulus on `contGood` (`LemDecCalELip_Lloop_sub`) and the time
modulus of `𝒦^{(k)}` (`stKloop_lip`), and the diagonal-to-pair propagation by the monotonicity of `ζ♯`.  `STCaseI` enters
only through `stOeqQtRoundPT''_holds`. -/
theorem stXiRoundQt_holds : ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t) := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := stOeqQtRoundPT''_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
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
  exact qtLift_lift sz hd (half_pos hκ) (inv_pos.2 hA.2.1) (fun n => (hE' n).le) hA.2.2.1 hs hst ht1 htN
    (qtLift_flowLam sz hflow) hPT

/-- **`stOeqQt'_holds`: Lemma 4.10 `lem:STOeq_Qt`, uniformly in the pair `(v, u)`, for every `d ≥ 3`** (bound
(4.36) `am;asoi222` with `B_s`): `STOeqQt' d` is
`STIngR d STCaseI (fun … => STXiBoot' …)`; the round is `stXiRoundQt_holds d` and the self-absorbing current-length term is
removed by the deterministic bootstrap `stXiBootR_of_round`.  No hypothesis. -/
theorem stOeqQt'_holds : ∀ d : ℕ, STOeqQt' d := fun d => stXiBootR_of_round d STCaseI (stXiRoundQt_holds d)

end RBM.Ind

end
