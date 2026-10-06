/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QtNonzeroFlow
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.Step2Events
import RBM3D.Green.Pins
import RBM3D.Gauss.Domination

/-!
# The uniform case-(ii) endpoint at the flow (`d ≥ 3`): `stOeqNZ''_holds`

Ticket T2299 (S3-22b2, stochastic layer ST-3, case (ii); the text of the paragraph "Split" of
`docs/tickets/T2292.md`, read with "T2292b" as "T2299"; S3-22b = T2292 = `Induction/QtNonzeroFlow`
proves the per-time pin `stOeqNZPT''_holds`, merged 59a0ab5).  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex`: `lem:STOeq_Qt_nonzero` `3_5:1561-1572`, proof `3_5:1889-1933`,
"the same argument applies to each fixed `u`; a standard `N^{-C}`-net argument" `3_5:1931`.
Format model: `Induction/NQEndFlowLift.lean` (T2258, case (i), d0484be), whose private lemmas are copied
here with the prefix `nzLift_`; `nqFlowSharp` and `stKloop_lip` are reused public.

## What is here

* §1 the pins `STNZConcl''` (`STNZConclPT''` with `PrecPT ↦ Prec`) and `STOeqNZ''` (`STIngR d STCaseII`);
* §2-§4 copies of the envelope lemmas, the right side `ζ♯` and the one-sided net core of
  `NQEndFlowLift.lean:71-418` (prefix `nzLift_`; private);
* §5 the new part: the `Q^{(A)}` modulus on `contGood` (`nzLift_xi_close`, the factor `2^{n_}` of `(normQA2)`,
  `3_5:1466`), the mesh arithmetic with `2^{n_}(3 n_ + 1) ≤ N`, the label count `#V_n ≤ N^{2 n_}`, the
  lift `STNZConclPT'' → STNZConcl''` (private) and the target `RBM.Ind.stOeqNZ''_holds`;
* §6 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.QtNonzeroFlowLiftInst`).

The lift adds no drift or good-set level (DECISIONS §95 (3)): `ζ♯` is a deterministic function of the controls and
`B`, and the only event is `contGood`, a deterministic event of the Gaussian coordinates.
Every helper that the ticket does not pin is `private` or prefixed `nzLift_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The pins (`STNZConclPT''` with `PrecPT ↦ Prec`) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **Uniform case-(ii) projected endpoint, R2*** (`lem:STOeq_Qt_nonzero` `3_5:1561`, bound
`(am;asoiuw_smalleta)` `3_5:1916-1922` for `Q^{(A)}(𝓛-𝒦)^{(n_)}` uniformly in `u`, the `N^{-C}`-net remark `3_5:1931`;
DECISIONS §80 (1), §91 (2); paper-delta candidate `T2299a`): the merged `STNZConclPT''`
(`QtNonzeroFlow.lean:75`) with `PrecPT` replaced by `Prec` in the conclusion (the union over `u ∈ [s_n, t_n]` inside
the probability); hypotheses, index set `{σA // STIdiff σA.1 ⊆ σA.2}`, the quantity
`‖zeroModeSet d L A (fun b => Lloop … b ω - STKloop … b) a‖ / B_u^{n_}` and the right side
`B_u^{1/6} XLK n_ + STbootRHS 2 … B_s n_ p` are unchanged. -/
def STNZConcl'' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

end Pins

/-- The uniform pin in the ingredient shape (case (ii)): the conclusion of `stOeqNZ''_holds` (T2299); consumed by
S3-22c (`newPQ` combination and self-absorption bootstrap, `stOeqQtNZ'_holds`). -/
def STOeqNZ'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConcl'' sz E s t)

end RBM.Gauss.Sizes

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 2. The envelope lemmas -/

/-- Envelope (a): `1 ≤ X♯`. -/
private theorem nzLift_sharp_one_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ),
    1 ≤ nqFlowSharp t X m n u :=
  fun _ _ _ _ _ => le_max_left _ _

/-- Envelope (b): `X♯ ≤ X` for a control `X ≥ 1`. -/
private theorem nzLift_sharp_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u : ℝ), nqFlowSharp t X m n u ≤ X m n u := by
  intro t X hX m n u
  unfold nqFlowSharp
  refine max_le (hX m n u) ?_
  by_cases hu : u ≤ t n
  · exact csInf_le ⟨1, by rintro _ ⟨v, -, rfl⟩; exact hX m n v⟩ ⟨u, ⟨le_rfl, hu⟩, rfl⟩
  · rw [Set.Icc_eq_empty hu, Set.image_empty, Real.sInf_empty]
    exact zero_le_one.trans (hX m n u)

/-- Envelope (c): `X♯` is non-decreasing in `u ≤ t_n`. -/
private theorem nzLift_sharp_mono : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
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
private theorem nzLift_sharp_prec : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ)
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
private theorem nzLift_bootRHS_mono : ∀ (lo : ℕ) (XL XL' XLK XLK' : ℕ → ℝ) (B : ℝ) (n_ p : ℕ), 0 < B →
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
private theorem nzLift_bootRHS_one_le {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 1 ≤ k)
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
`B` is needed): for `s_n ≤ θ ≤ u ≤ t_n < 1`, the right side of `STNZConclPT''` at the envelope controls
`(XL♯, XLK♯)` at `θ` is at most that at `u` (`B_θ^{1/6} ≤ B_u^{1/6}` by `STBctl_mono`, the envelopes are
non-decreasing, `STbootRHS` is monotone in the controls). -/
private theorem nzLift_zeta_mono (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
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
  refine add_le_add ?_ (nzLift_bootRHS_mono 2 _ _ _ _ _ n_ p hBs
    (fun m => zero_le_one.trans (nzLift_sharp_one_le t XL m n θ))
    (fun m => zero_le_one.trans (nzLift_sharp_one_le t XLK m n θ))
    (fun m => nzLift_sharp_mono t XL hXL m n θ u hθu hut)
    (fun m => nzLift_sharp_mono t XLK hXLK m n θ u hθu hut))
  exact mul_le_mul (Real.rpow_le_rpow hBθ.le hBθu (by norm_num))
    (nzLift_sharp_mono t XLK hXLK n_ n θ u hθu hut) (zero_le_one.trans (nzLift_sharp_one_le t XLK n_ n θ))
    (Real.rpow_nonneg (hBθ.le.trans hBθu) _)

/-- **`ζ♯ ≤ ζ`** pointwise (`X♯ ≤ X`, `STbootRHS` monotone in the controls). -/
private theorem nzLift_zeta_le (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
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
  refine add_le_add ?_ (nzLift_bootRHS_mono 2 _ _ _ _ _ n_ p hBs
    (fun m => zero_le_one.trans (nzLift_sharp_one_le t XL m n u))
    (fun m => zero_le_one.trans (nzLift_sharp_one_le t XLK m n u))
    (fun m => nzLift_sharp_le t XL hXL m n u) (fun m => nzLift_sharp_le t XLK hXLK m n u))
  exact mul_le_mul_of_nonneg_left (nzLift_sharp_le t XLK hXLK n_ n u) (Real.rpow_nonneg hBu.le _)

/-- **`1 ≤ ζ♯`** (`ζ♯ ≥ 1` is the floor `ε_n = 1` of the net lift): `XL♯ ≥ 1`, `XLK♯ ≥ 1`, `B ≥ 0`, `n_ ≥ 1`. -/
private theorem nzLift_zeta_one_le (sz : Sizes d) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (n_ p n : ℕ) (hn : 1 ≤ n_) {u : ℝ} (hsu : s n ≤ u) (hut : u ≤ t n) :
    1 ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 2 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p := by
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hs1 : s n < 1 := hsu.trans_lt hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have h0 : 0 ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u :=
    mul_nonneg (Real.rpow_nonneg hBu.le _) (zero_le_one.trans (nzLift_sharp_one_le t XLK n_ n u))
  have := nzLift_bootRHS_one_le (lo := 2) (XL := fun m => nqFlowSharp t XL m n u)
    (XLK := fun m => nqFlowSharp t XLK m n u) (B := sz.Bctl n (s n)) (k := n_) (p := p) hn
    (fun m => nzLift_sharp_one_le t XL m n u)
    (fun m => zero_le_one.trans (nzLift_sharp_one_le t XLK m n u)) hBs.le
  linarith

end RightSide

/-! ## 4. The one-sided net core

The merged `ContinuityNet.cont_core` (`ContinuityNet.lean:142`) asks the closeness of `ξ` and `ζ` for every pair of
times at distance `≤ N^{-A}`; the envelope `ζ♯` is non-decreasing, so `ζ♯(θ) ≤ 2 ζ♯(u)` holds only for `θ ≤ u`.  The
net point of `u` is therefore the floor point `θ = s_n + ⌊(u - s_n) m⌋/m ≤ u` (`m = netSize`), and the closeness is asked
only for `u' ≤ u`; the clamp `min (t_n)` of the merged `contTime` is inactive at `θ`.  Everything else is the text of
`cont_core`. -/

section Core

/-- Copy of the private `ContinuityNet.cont_stochDomAt_of_subset` (`ContinuityNet.lean:76`). -/
private theorem nzLift_stochDomAt_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
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
private def nzLift_time (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

/-- Copy of `ContinuityNet.contTime_mem`. -/
private theorem nzLift_time_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : nzLift_time s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

/-- **The floor net point** (the witness of `exists_netPt_close`, `Domination.lean:171`, at
`T = 1`, with the one-sided information `netPt ≤ x`): `netPt` at `⌊x · netSize⌋` lies in `[x - 1/netSize, x]`. -/
private theorem nzLift_netPt_floor : ∀ (A : ℝ) (N : ℕ) (x : ℝ), 0 ≤ x → x ≤ 1 →
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

/-- **The one-sided net lift** : the merged `cont_core` (`ContinuityNet.lean:142`) with the
closeness hypothesis `hclose` asked only for `u' ≤ u` (the floor net point lies below `u`).  Nothing else changes: a
per-time domination on `TimeIcc s t n × V n`, a polynomial bound on `#V n`, a good event `Ξ` of high probability on
which `ξ` moves up by at most `ε n` and `ζ` down by a factor `2` along a downward time change of size `size^{-A}`, and
`ε ≤ ζ`, give the uniform domination. -/
private theorem nzLift_core_below : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ),
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
    ⟨nzLift_time s t (A + 1) (size n) n k, nzLift_time_mem hst _ _ n k⟩
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
  refine nzLift_stochDomAt_of_subset hsize hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
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
  obtain ⟨k, hk1, hk2⟩ := nzLift_netPt_floor (A + 1) (size n) ((u : ℝ) - s n)
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

/-! ## 5. The `Q^{(A)}` modulus on `contGood`, the lift, and `stOeqNZ''_holds` -/

section Lift

variable {d : ℕ}

/-- **The mesh arithmetic with the factor `2^{n_}` of `(normQA2)`** (paper-delta candidate `T2299b`): for
`δ ≤ N^{-(6 n_ + 20)}` and `2^{n_}(3 n_ + 1) ≤ N`,
`2^{n_} N^{n_} (3 n_ N^{2n_+7} √δ + N^{2n_+2} δ) ≤ 1` (the two summands of the bracket times `N^{n_}` are
`≤ 3 n_ N^{-3}` and `≤ N^{-3}`, as in `NQEndFlowLift.lean:705-750`; then `2^{n_}(3 n_ + 1) N^{-3} ≤ N · N^{-3} ≤ 1`). -/
private theorem nzLift_arith {N δ : ℝ} {n_ : ℕ} (hN : (2 ^ n_ * (3 * n_ + 1) : ℝ) ≤ N) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (N ^ (6 * n_ + 20))⁻¹) :
    2 ^ n_ * (N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ + N ^ (2 * n_ + 2) * δ)) ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have h2n : (1 : ℝ) ≤ 2 ^ n_ := one_le_pow₀ (by norm_num)
  have h3n : (1 : ℝ) ≤ 3 * n_ + 1 := by linarith
  have hprod1 : (1 : ℝ) ≤ 2 ^ n_ * (3 * n_ + 1) := by nlinarith
  have hN1 : (1 : ℝ) ≤ N := hprod1.trans hN
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
  have hmid : N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ + N ^ (2 * n_ + 2) * δ) ≤
      (3 * n_ + 1) * (N ^ 3)⁻¹ := by
    calc N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ + N ^ (2 * n_ + 2) * δ)
        = N ^ n_ * (3 * n_ * N ^ (2 * n_ + 7) * Real.sqrt δ) + N ^ n_ * (N ^ (2 * n_ + 2) * δ) := by ring
      _ ≤ 3 * n_ * (N ^ 3)⁻¹ + (N ^ 3)⁻¹ := add_le_add t1 t2
      _ = (3 * n_ + 1) * (N ^ 3)⁻¹ := by ring
  have hN3 : 2 ^ n_ * ((3 * n_ + 1 : ℝ) * (N ^ 3)⁻¹) ≤ 1 := by
    have hN3pos : 0 < N ^ 3 := by positivity
    have e : 2 ^ n_ * ((3 * n_ + 1 : ℝ) * (N ^ 3)⁻¹) = (2 ^ n_ * (3 * n_ + 1)) / N ^ 3 := by
      field_simp
    rw [e, div_le_one hN3pos]
    have : N ≤ N ^ 3 := le_self_pow₀ hN1 (by norm_num)
    linarith
  exact (mul_le_mul_of_nonneg_left hmid (by positivity)).trans hN3

/-- **`(normQA2)` on the loops** (`3_5:1466`, `norm_zeroModeSet_le`; copy of `nzFlow_proj_le`,
`QtNonzeroFlow.lean:467`): if every entry of the tensor `T` has norm at most `x`, then
`‖(Q^{(A)} T)_a‖ ≤ 2^{|A|} ‖T‖ ≤ 2^k x` (`|A| ≤ k`). -/
private theorem nzLift_proj_le {L k : ℕ} [NeZero L] (A : Finset (Fin k)) (T : (Fin k → Zd d L) → ℂ)
    {x : ℝ} (hx : 0 ≤ x) (hT : ∀ b, ‖T b‖ ≤ x) (a : Fin k → Zd d L) :
    ‖zeroModeSet d L A T a‖ ≤ 2 ^ k * x := by
  have h1 : ‖T‖ ≤ x := (pi_norm_le_iff_of_nonneg hx).2 hT
  have hA : A.card ≤ k := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ A
  calc ‖zeroModeSet d L A T a‖ ≤ ‖zeroModeSet d L A T‖ := norm_le_pi_norm _ a
    _ ≤ 2 ^ A.card * ‖T‖ := norm_zeroModeSet_le A T
    _ ≤ 2 ^ k * x :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hA) h1 (norm_nonneg _) (by positivity)

/-- **The `ξ` closeness of the projected tensor on `contGood`** (one-sided, for `s ≤ u' ≤ u ≤ t`,
`u - u' ≤ N^{-(6 n_ + 20)}`; paper-delta candidate `T2299b`):
`‖(Q^{(A)}(𝓛-𝒦)_u)_a‖ / B_u^{n_} ≤ ‖(Q^{(A)}(𝓛-𝒦)_{u'})_a‖ / B_{u'}^{n_} + 1`.  `Q^{(A)}` is linear
(`zeroModeSet_sub`), so `Q^{(A)}(𝓛-𝒦)_u = Q^{(A)}(𝓛-𝒦)_{u'} + Q^{(A)}Δ` with `Δ_b = (𝓛_u - 𝓛_{u'})_b - (𝒦_u - 𝒦_{u'})_b`;
`‖(Q^{(A)}Δ)_a‖ ≤ 2^{n_} sup_b ‖Δ_b‖` (`nzLift_proj_le`) and `‖Δ_b‖ ≤ 3 n_ N^{2n_+7} √δ + N^{2n_+2} δ`
(`LemDecCalELip_Lloop_sub`, `stKloop_lip`, uniformly in `b`); `2^{n_} N^{n_} (…) ≤ 1` (`nzLift_arith`),
`N⁻¹ ≤ B_u` (`cont_inv_size_le_Bctl`); the ratio term has the favourable sign (`B_{u'} ≤ B_u`, `STBctl_mono`) and is
dropped. -/
private theorem nzLift_xi_close (sz : Sizes d) (n : ℕ) (E : ℝ) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ)
    (hs0 : 0 ≤ s) (hsu' : s ≤ u') (hu'u : u' ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hM : (2 ^ n_ * (3 * n_ + 1) : ℝ) ≤ N) (hE2 : |E| < 2)
    (hQ : (etaT E t)⁻¹ ≤ N ^ 2) (hgood : ω ∈ ContinuityNet.contGood sz n)
    (hΔ : u - u' ≤ N ^ (-((6 * n_ + 20 : ℕ) : ℝ)))
    (A : Finset (Fin n_)) (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n))
    (hK : ∀ b : Fin n_ → Zd d (sz.L n),
      ‖STKloop sz n E u σ b - STKloop sz n E u' σ b‖ ≤ N ^ (2 * n_ + 2) * |u - u'|) :
    ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u σ b ω - STKloop sz n E u σ b) a‖ /
        (sz.Bctl n u) ^ n_ ≤
      ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) a‖ /
        (sz.Bctl n u') ^ n_ + 1 := by
  have hu1 : u < 1 := hut.trans_lt ht1
  have hu'1 : u' < 1 := hu'u.trans_lt hu1
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hu0 : 0 ≤ u := hu'0.trans hu'u
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have h2n : (1 : ℝ) ≤ 2 ^ n_ := one_le_pow₀ (by norm_num)
  have h3n : (1 : ℝ) ≤ 3 * n_ + 1 := by linarith
  have hprod1 : (1 : ℝ) ≤ 2 ^ n_ * (3 * n_ + 1) := by nlinarith
  have hN1 : 1 ≤ N := hprod1.trans hM
  have hN0 : 0 < N := by linarith
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hBu' : 0 < sz.Bctl n u' := st_Bctl_pos sz hu'1
  have hBle : sz.Bctl n u' ≤ sz.Bctl n u := STBctl_mono sz n hu'u hu1
  have hBinv : N⁻¹ ≤ sz.Bctl n u := by
    rw [hN]; exact ContinuityNet.cont_inv_size_le_Bctl sz n hu0 hu1
  have hδ0 : 0 ≤ u - u' := sub_nonneg.2 hu'u
  have hL := fun b => LemDecCalELip_Lloop_sub sz n E ω hN hN1 hE2 ht1 hu0 hut hu'0 (hu'u.trans hut) hQ
    (fun c => by rw [hN]; exact hgood c) σ b
  have hK' := hK
  simp only [abs_of_nonneg hδ0] at hK'
  have hL' : ∀ b, ‖Lloop sz n E u σ b ω - Lloop sz n E u' σ b ω‖ ≤
      3 * (n_ : ℝ) * N ^ (2 * n_ + 7) * Real.sqrt (u - u') := by
    intro b
    have := hL b
    rwa [abs_of_nonneg hδ0] at this
  have hδ' : u - u' ≤ (N ^ (6 * n_ + 20))⁻¹ := by
    refine hΔ.trans (le_of_eq ?_)
    rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
  have harith := nzLift_arith hM hδ0 hδ'
  have hNn : 0 < N ^ n_ := pow_pos hN0 _
  -- the entrywise bound of `Δ`
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 3 * (n_ : ℝ) * N ^ (2 * n_ + 7) * Real.sqrt (u - u') +
      N ^ (2 * n_ + 2) * (u - u') := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hent : ∀ b : Fin n_ → Zd d (sz.L n),
      ‖(Lloop sz n E u σ b ω - STKloop sz n E u σ b) - (Lloop sz n E u' σ b ω - STKloop sz n E u' σ b)‖ ≤ x := by
    intro b
    have e : (Lloop sz n E u σ b ω - STKloop sz n E u σ b) - (Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) =
        (Lloop sz n E u σ b ω - Lloop sz n E u' σ b ω) - (STKloop sz n E u σ b - STKloop sz n E u' σ b) := by
      ring
    rw [e, hx]
    calc _ ≤ ‖Lloop sz n E u σ b ω - Lloop sz n E u' σ b ω‖ + ‖STKloop sz n E u σ b - STKloop sz n E u' σ b‖ :=
          norm_sub_le _ _
      _ ≤ _ := add_le_add (hL' b) (hK' b)
  have hproj := nzLift_proj_le A
    (fun b => (Lloop sz n E u σ b ω - STKloop sz n E u σ b) - (Lloop sz n E u' σ b ω - STKloop sz n E u' σ b))
    hx0 hent a
  -- `2^{n_} x ≤ B_u^{n_}`
  have hsmall : 2 ^ n_ * x ≤ (sz.Bctl n u) ^ n_ := by
    have h1 : (N ^ n_)⁻¹ ≤ (sz.Bctl n u) ^ n_ := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hBinv n_
    refine le_trans ?_ h1
    have harith' : 2 ^ n_ * (N ^ n_ * x) ≤ 1 := by rw [hx]; exact harith
    calc 2 ^ n_ * x = (N ^ n_)⁻¹ * (2 ^ n_ * (N ^ n_ * x)) := by field_simp
      _ ≤ (N ^ n_)⁻¹ * 1 := mul_le_mul_of_nonneg_left harith' (inv_nonneg.2 hNn.le)
      _ = (N ^ n_)⁻¹ := mul_one _
  -- linearity of `Q^{(A)}`
  have hlin : zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u σ b ω - STKloop sz n E u σ b) a =
      zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) a +
        zeroModeSet d (sz.L n) A
          (fun b => (Lloop sz n E u σ b ω - STKloop sz n E u σ b) -
            (Lloop sz n E u' σ b ω - STKloop sz n E u' σ b)) a := by
    have h := zeroModeSet_sub (d := d) (L := sz.L n) A
      (fun b => Lloop sz n E u σ b ω - STKloop sz n E u σ b)
      (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b)
    have h2 := congrFun h a
    change zeroModeSet d (sz.L n) A (fun b => (Lloop sz n E u σ b ω - STKloop sz n E u σ b) -
        (Lloop sz n E u' σ b ω - STKloop sz n E u' σ b)) a =
      zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u σ b ω - STKloop sz n E u σ b) a -
        zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) a at h2
    rw [h2]; ring
  have htri : ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u σ b ω - STKloop sz n E u σ b) a‖ ≤
      ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) a‖ +
        (sz.Bctl n u) ^ n_ := by
    rw [hlin]
    refine (norm_add_le _ _).trans (add_le_add le_rfl (hproj.trans hsmall))
  have hBpow : 0 < (sz.Bctl n u) ^ n_ := pow_pos hBu _
  calc ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u σ b ω - STKloop sz n E u σ b) a‖ /
        (sz.Bctl n u) ^ n_
      ≤ (‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) a‖ +
          (sz.Bctl n u) ^ n_) / (sz.Bctl n u) ^ n_ := div_le_div_of_nonneg_right htri hBpow.le
    _ = ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) a‖ /
          (sz.Bctl n u) ^ n_ + 1 := by
        rw [add_div, div_self hBpow.ne']
    _ ≤ ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n E u' σ b ω - STKloop sz n E u' σ b) a‖ /
          (sz.Bctl n u') ^ n_ + 1 := by
        refine add_le_add ?_ le_rfl
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hBu' _) (pow_le_pow_left₀ hBu'.le hBle _)

/-- `#V_n ≤ N^{2 n_}` for the label set `V_n = {(σ, A) // I_diff(σ) ⊆ A} × (Z_L^d)^{n_}`
(`#{(σ, A)} ≤ 2^{n_} · 2^{n_} = 4^{n_}`, `#a = (L^d)^{n_} ≤ N^{n_}`, `N ≥ 4`). -/
private theorem nzLift_card_V (sz : Sizes d) (n_ n : ℕ) (hN4 : 4 ≤ sz.size n) :
    (Fintype.card ({σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n))) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ((2 * n_ : ℕ) : ℝ) := by
  have h1 : Fintype.card {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ≤ 4 ^ n_ := by
    calc _ ≤ Fintype.card ((Fin n_ → Bool) × Finset (Fin n_)) := Fintype.card_subtype_le _
      _ = 4 ^ n_ := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_finset,
          Fintype.card_fin, ← mul_pow]
        norm_num
  have h2 : Fintype.card (Fin n_ → Zd d (sz.L n)) = ((sz.L n) ^ d) ^ n_ := by
    simp
  have h3 : (sz.L n) ^ d ≤ sz.size n := by
    rw [Sizes.size]
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  have h4 : Fintype.card ({σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
      (Fin n_ → Zd d (sz.L n))) ≤ sz.size n ^ (2 * n_) := by
    rw [Fintype.card_prod, h2, two_mul, pow_add]
    exact Nat.mul_le_mul (h1.trans (Nat.pow_le_pow_left hN4 n_)) (Nat.pow_le_pow_left h3 n_)
  rw [Real.rpow_natCast]
  exact_mod_cast h4

/-- A pointwise larger right side keeps `≺` (copy of `NQEndFlowLift.lean:851`). -/
private theorem nzLift_prec_of_le_right {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually (copy of `NQEndFlowLift.lean:859`). -/
private theorem nzLift_flowLam (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- **The eventual closeness of `ξ` on `contGood`** (the environment of `nzLift_xi_close` for sequences): for
`n_ ≥ 2`, eventually in `n`, every `ω ∈ contGood`, every `s_n ≤ u' ≤ u ≤ t_n` with `u - u' ≤ N^{-(6 n_ + 20)}`, every
`σ`, `A`, `a`: `ξ(u) ≤ ξ(u') + 1`.  The facts of `LemDecCalELip_env` (at `M = 2^{n_}(3 n_ + 1)`) and the time
modulus `stKloop_lip` of `𝒦^{(n_)}` are the inputs. -/
private theorem nzLift_xi_close_ev (sz : Sizes d) (hd : 3 ≤ d) {E s t : ℕ → ℝ} {κ' gmax : ℝ} (hκ' : 0 < κ')
    (hg : 0 < gmax) (hE : ∀ n, |E n| ≤ 2 - κ') (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n)
    (ht1 : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) {n_ : ℕ} (hn : 2 ≤ n_) :
    ∀ᶠ n in atTop, ∀ ω ∈ ContinuityNet.contGood sz n, ∀ u u' : ℝ, s n ≤ u' → u' ≤ u → u ≤ t n →
      u - u' ≤ ((sz.size n : ℕ) : ℝ) ^ (-((6 * n_ + 20 : ℕ) : ℝ)) →
      ∀ (A : Finset (Fin n_)) (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)),
        ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n (E n) u σ b ω - STKloop sz n (E n) u σ b) a‖ /
            (sz.Bctl n u) ^ n_ ≤
          ‖zeroModeSet d (sz.L n) A (fun b => Lloop sz n (E n) u' σ b ω - STKloop sz n (E n) u' σ b) a‖ /
            (sz.Bctl n u') ^ n_ + 1 := by
  filter_upwards [LemDecCalELip_env sz E t κ' hκ' hE hsize htN (2 ^ n_ * (3 * (n_ : ℝ) + 1)),
    stKloop_lip sz hd hκ' hg hsize E t (Eventually.of_forall hE) hlam ht1 htN n_ hn] with n hnum hK
  obtain ⟨hM, hN1, hE2, hQ, -⟩ := hnum
  intro ω hω u u' hsu' hu'u hut hΔ A σ a
  exact nzLift_xi_close sz n (E n) ω (hs0 n) hsu' hu'u hut (ht1 n) rfl hM hE2 hQ hω hΔ A σ a
    (fun b => hK u u' ((hs0 n).trans (hsu'.trans hu'u)) hut ((hs0 n).trans hsu') (hu'u.trans hut) σ b)

/-- **The lift `STNZConclPT'' → STNZConcl''`** (private: its binder is the per-time pin).  At the envelope controls
`(XL♯, XLK♯)` the per-time pin gives `PrecPT(ξ ≺ ζ♯)`; the one-sided net core (`nzLift_core_below`, `P = seqP`,
`Ξ = contGood`, `ε = 1`, `A = 6 n_ + 20`, `Cv = 2 n_`) gives `Prec(ξ ≺ ζ♯)`, and `ζ♯ ≤ ζ` gives `Prec(ξ ≺ ζ)`.
Only the label set `V_n`, the `ξ`-modulus (`nzLift_xi_close_ev`) and the cardinality (`nzLift_card_V`) differ from
the case-(i) lift `NQEndFlowLift.lean:868`. -/
private theorem nzLift_lift (sz : Sizes d) (hd : 3 ≤ d) {E s t : ℕ → ℝ} {κ' gmax : ℝ} (hκ' : 0 < κ')
    (hg : 0 < gmax) (hE : ∀ n, |E n| ≤ 2 - κ') (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) (hPT : STNZConclPT'' sz E s t) :
    STNZConcl'' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsizeN : Tendsto sz.size atTop atTop := sz.tendsto_size hsize
  have hXL' : ∀ m n u, 1 ≤ nqFlowSharp t XL m n u := fun m n u => nzLift_sharp_one_le t XL m n u
  have hXLK' : ∀ m n u, 1 ≤ nqFlowSharp t XLK m n u := fun m n u => nzLift_sharp_one_le t XLK m n u
  have hXLp' : ∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XL m n q.1.2) := fun m hm hl =>
    nzLift_sharp_prec sz s t (fun n w ω => STXiL sz n (E n) w m ω) XL m hXL (hXLp m hm hl)
  have hXLKp' : ∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XLK m n q.1.2) := fun m hm hm' =>
    nzLift_sharp_prec sz s t (fun n w ω => STXiLK sz n (E n) w m ω) XLK m hXLK (hXLKp m hm hm')
  have hPT' := hPT n_ p hn hp (fun m n u => nqFlowSharp t XL m n u) (fun m n u => nqFlowSharp t XLK m n u)
    hXL' hXLK' hXLp' hXLKp'
  have hmain : Prec sz
      (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => nqFlowSharp t XL m n (q.1 : ℝ)) (fun m => nqFlowSharp t XLK m n (q.1 : ℝ))
          (sz.Bctl n (s n)) n_ p) := by
    refine nzLift_core_below (Ω := sz.SeqΩ) sz.seqP sz.size hsizeN s t (fun n => (hst n).le)
      (fun n => by linarith [hs0 n, ht1 n])
      (fun n => {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} × (Fin n_ → Zd d (sz.L n)))
      _ _ ((6 * n_ + 20 : ℕ) : ℝ) ((2 * n_ : ℕ) : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_ hPT'
      (ContinuityNet.contGood sz) (ContinuityNet.cont_highProbAt_good sz hsizeN) (fun _ => 1)
      (fun _ => zero_le_one) ?_ ?_
    · -- `hcard`
      filter_upwards [hsizeN.eventually_ge_atTop 4] with n hn4 using nzLift_card_V sz n_ n hn4
    · -- `hlow`: `ζ♯ ≥ 1`
      exact Eventually.of_forall fun n q ω =>
        nzLift_zeta_one_le sz ht1 n_ p n (by omega) q.1.2.1 q.1.2.2
    · -- `hclose`
      filter_upwards [nzLift_xi_close_ev sz hd hκ' hg hE hsize hs0 ht1 htN hlam hn] with n hev
      intro ω hω u u' hle hΔ v
      obtain ⟨⟨⟨σ, A⟩, hσA⟩, a⟩ := v
      refine ⟨?_, ?_⟩
      · exact hev ω hω u u' u'.2.1 hle u.2.2 hΔ A σ a
      · have h1 := nzLift_zeta_mono sz ht1 hXL hXLK n_ p n u'.2.1 hle u.2.2
        have h2 := nzLift_zeta_one_le sz ht1 (XL := XL) (XLK := XLK) n_ p n (by omega) u.2.1 u.2.2
        change (sz.Bctl n (u' : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u' : ℝ) +
            STbootRHS 2 (fun m => nqFlowSharp t XL m n (u' : ℝ)) (fun m => nqFlowSharp t XLK m n (u' : ℝ))
              (sz.Bctl n (s n)) n_ p ≤
          2 * ((sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u : ℝ) +
            STbootRHS 2 (fun m => nqFlowSharp t XL m n (u : ℝ)) (fun m => nqFlowSharp t XLK m n (u : ℝ))
              (sz.Bctl n (s n)) n_ p)
        linarith
  exact nzLift_prec_of_le_right hmain fun n q ω =>
    nzLift_zeta_le sz ht1 hXL hXLK n_ p n q.1.2.1 q.1.2.2

end Lift

/-! ### The target -/

/-- **`stOeqNZ''_holds`: `lem:STOeq_Qt_nonzero`, R2*, uniformly in `u`, for every `d ≥ 3`**
(`T2292b_stOeqNZ''_holds` of the check file; `3_5:1561-1572`, bound `(am;asoiuw_smalleta)` `3_5:1916-1922` with the
first summand at `B_s`; the uniform form `3_5:1931`).  The constant `𝔠_d` is the one of the per-time pin
`stOeqNZPT''_holds d` at the same `(κ, ε, 𝔡, C_d)`; the uniform conclusion `STNZConcl''` follows from the per-time
`STNZConclPT''` by the envelope `X♯` of the controls, the one-sided floor net, the `ξ` modulus of the projected tensor
on `contGood` (the factor `2^{n_}` of `(normQA2)`) and the time modulus of `𝒦^{(k)}` (`stKloop_lip`).
Paper-delta candidates `T2299a` (the uniform-in-`u` form from the per-time one before the `newPQ` bootstrap; the paper
lifts after it, `3_5:1931`; equivalent, as `T2258a` in case (i)) and `T2299b` (the `Q^{(A)}` modulus). -/
theorem stOeqNZ''_holds : ∀ d : ℕ, STOeqNZ'' d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := stOeqNZPT''_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
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
  exact nzLift_lift sz hd (half_pos hκ) (inv_pos.2 hA.2.1) (fun n => (hE' n).le) hA.2.2.1 hs hst ht1 htN
    (nzLift_flowLam sz hflow) hPT

/-! ## 6. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.QtNonzeroFlowLiftInst`.  Data: the case-(ii) data of the merged `inst_OeqQtNZ`
(`Step34Pins.lean:1006`) and of `QtNonzeroFlowInst` (`QtNonzeroFlow.lean:~870`): `szB` (`d = 3`, `L = 4`,
`W = n + 4`, `ilambda = 1`, `N = (4(n+4))^3`, `N_0 = 4096`), the flow `zB` (`z_n = 1/2 + i/64`, `flow_zB` at
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `s ≡ 15/16`, `t ≡ 31/32` (`szB_flow_ht`; `szB_caseII`: `1 - s = 1/16 = ilambda²/L²`,
the boundary of case (ii); `conStInd_const`: `(con_st_ind)` for every `𝔠_d > 0`), `C_d = 1`.  `STKbound`, `STKward`
are theorems of the flow (`stKbound_of_flow`, `stKward_of_flow`); what stays a hypothesis of an example is a
stochastic premise that is another gate's pin (`STLK s`, `STStep2Concl`, the pair hypotheses `Ξ̂ ≺ 1` of the pin). -/

namespace QtNonzeroFlowLiftInst

open RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst RBM.Ind.QtNonzeroEndInst

/-- **(1) `stOeqNZ''_holds` at the data**: the uniform case-(ii) projected R2* pin at
`(szB, zB, s ≡ 15/16, t ≡ 31/32)`, `C_d = 1`: the constant `𝔠_d ∈ (0, 1/100]`, then the stochastic premises of `STIngR`
(`STKbound`, `STKward`, `STLK`, `STStep2Concl`), then the conclusion `STNZConcl''`.  Every deterministic hypothesis
(`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the regime `STCaseII`, `(con_st_ind)`, `C_d > 0`) is discharged by `inst_ing`. -/
theorem inst_OeqNZ'' :
    InstIngConcl (fun sz E s t => STNZConcl'' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STNZConcl'' sz E s t) (stOeqNZ''_holds 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- **(2) the conclusion applied** at `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`: `STKbound`, `STKward` come from the flow, the
stochastic premises `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` of the pin (the conclusions of Steps 3-4,
other gates' pins) stay hypotheses; the uniform conclusion
`(Q^{(A)}(𝓛-𝒦)^{(3)})_{u,σ,a}/B_u³ ≺ B_u^{1/6} + STbootRHS 2 1 1 B_s 3 1` for every sign vector `σ`, every
`A ⊇ I_diff(σ)`, every label `a` and `u ∈ [15/16, 31/32]`, with the union over `u` inside `P` (`Prec`), is the
conclusion. -/
example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
    (hStep2 : STStep2Concl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiL szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ))) :
    Prec szB (U := fun n => TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
        {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} × (Fin 3 → Zd 3 (szB.L n)))
      (fun n q ω => ‖zeroModeSet 3 (szB.L n) q.2.1.1.2
          (fun b : Fin 3 → Zd 3 (szB.L n) =>
            Lloop szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1.1 b ω -
              STKloop szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (szB.Bctl n (q.1 : ℝ)) ^ 3)
      (fun n q _ => (szB.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 2 (fun _ => 1) (fun _ => 1) (szB.Bctl n (15 / 16)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqNZ''
  exact hC (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(3) `nzLift_xi_close_ev` at the data, unfolded at a size index** (`szB`, `E = STflowE zB`,
`[s, t] = [15/16, 31/32]`, `n_ = 3`): all deterministic hypotheses are discharged (`3 ≤ d`, `κ' = 1/20`, `gmax = 10`,
`|E_n| ≤ 2 - κ'` from the flow, `SizeTendsto`, `(1 - t)⁻¹ = 32 ≤ N_n`, `lam = 1 ∈ (0, 10]`); the conclusion is the
`Q^{(A)}` closeness `ξ(u) ≤ ξ(u') + 1` on `contGood` for every `A`, `σ`, `a` and every pair of times at distance
`≤ N^{-38}`, and `.exists` unfolds it at one size index. -/
example : ∃ n : ℕ, ∀ ω ∈ ContinuityNet.contGood szB n, ∀ u u' : ℝ, (15 / 16 : ℝ) ≤ u' → u' ≤ u →
    u ≤ 31 / 32 → u - u' ≤ ((szB.size n : ℕ) : ℝ) ^ (-((6 * 3 + 20 : ℕ) : ℝ)) →
    ∀ (A : Finset (Fin 3)) (σ : Fin 3 → Bool) (a : Fin 3 → Zd 3 (szB.L n)),
      ‖zeroModeSet 3 (szB.L n) A
          (fun b => Lloop szB n (STflowE zB n) u σ b ω - STKloop szB n (STflowE zB n) u σ b) a‖ /
          (szB.Bctl n u) ^ 3 ≤
        ‖zeroModeSet 3 (szB.L n) A
          (fun b => Lloop szB n (STflowE zB n) u' σ b ω - STKloop szB n (STflowE zB n) u' σ b) a‖ /
          (szB.Bctl n u') ^ 3 + 1 := by
  obtain ⟨-, hE', -, -⟩ := RBM.Green.v3_premises_of_stFlow szB (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_zB (t := fun _ : ℕ => (31 / 32 : ℝ)) (szB_flow_ht (by norm_num))
  have htN : ∀ᶠ n in atTop, (1 - (fun _ : ℕ => (31 / 32 : ℝ)) n)⁻¹ ≤ ((szB.size n : ℕ) : ℝ) := by
    filter_upwards [szB_tendsto.eventually_ge_atTop 32] with n hn
    have h : (1 - (fun _ : ℕ => (31 / 32 : ℝ)) n)⁻¹ = 32 := by norm_num
    rw [h]
    exact hn
  exact (nzLift_xi_close_ev szB (by norm_num) (E := STflowE zB) (s := fun _ : ℕ => (15 / 16 : ℝ))
    (t := fun _ : ℕ => (31 / 32 : ℝ)) (κ' := 1 / 10 / 2) (gmax := (1 / 10 : ℝ)⁻¹) (by norm_num) (by norm_num)
    (fun n => (hE' n).le) szB_tendsto (fun _ => by norm_num) (fun _ => by norm_num) htN
    (nzLift_flowLam szB flow_zB) (n_ := 3) (by norm_num)).exists

/-- **(3) the good event is nonempty at every size index**: the zero configuration lies in `contGood`. -/
example (n : ℕ) : (0 : szB.SeqΩ) ∈ ContinuityNet.contGood szB n := fun c => by simp

/-- **(4) the label count at the data** (`nzLift_card_V`, `szB`, `n_ = 3`, size index `0`, `N_0 = 4096`):
`#V ≤ N^6` for `V = {(σ, A) // I_diff(σ) ⊆ A} × (Z_4^3)^3`. -/
example : (Fintype.card ({σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} ×
      (Fin 3 → Zd 3 (szB.L 0))) : ℝ) ≤ ((szB.size 0 : ℕ) : ℝ) ^ ((2 * 3 : ℕ) : ℝ) :=
  nzLift_card_V szB 3 0 (by have := szB_size_ge 0; omega)

/-- **(4) the index set of the pin is nonempty and has the intended members**: `σ = sig3 = (+,-,+)` with `A = {0, 1}`
(`I_diff(sig3) = {0, 1}`, `QtNonzeroEndInst.σ3_idiff`), the constant `σ ≡ +` with `A = ∅` (`I_diff = ∅`); the parameter
type of `STNZConcl''` at `szB` is nonempty at every size index. -/
example (n : ℕ) : Nonempty (TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
    {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} × (Fin 3 → Zd 3 (szB.L n))) :=
  ⟨(⟨15 / 16, le_rfl, by norm_num⟩, ⟨(sig3, {0, 1}), by rw [σ3_idiff]⟩, fun _ => 0)⟩

example : ∃ x : {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2},
    x.1 = ((fun _ => true), (∅ : Finset (Fin 3))) :=
  ⟨⟨((fun _ => true), ∅), by decide⟩, rfl⟩

/-- **(5) the mesh arithmetic at numbers** (`nzLift_arith`, `n_ = 3`, `N = 4096`, `δ = N^{-38}`; the threshold is
`2^3 · 10 = 80 ≤ 4096`). -/
example : (2 : ℝ) ^ 3 * ((4096 : ℝ) ^ 3 * (3 * ((3 : ℕ) : ℝ) * (4096 : ℝ) ^ (2 * 3 + 7) *
      Real.sqrt (((4096 : ℝ) ^ (6 * 3 + 20))⁻¹) + (4096 : ℝ) ^ (2 * 3 + 2) * ((4096 : ℝ) ^ (6 * 3 + 20))⁻¹)) ≤ 1 :=
  nzLift_arith (n_ := 3) (by norm_num) (by positivity) le_rfl

/-- **(5) the zero-mode bound at numbers** (`nzLift_proj_le`): `‖(Q^{(A)} 1)_a‖ ≤ 2^3` for the constant tensor `1` on
`3` indices over `Z_4^3` and every `A ⊆ Fin 3`. -/
example (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 4) :
    ‖zeroModeSet 3 4 A (fun _ : Fin 3 → Zd 3 4 => (1 : ℂ)) a‖ ≤ 2 ^ 3 * 1 :=
  nzLift_proj_le A _ zero_le_one (fun _ => by simp) a

/-- **(6) `nzLift_core_below` at the data**: `P = seqP szB`, `size = szB.size`, window `[15/16, 31/32]`, `V n = Fin 2`,
`ξ n (u, v) = u`, `ζ ≡ 1`, `A = Cv = 1`, `Ξ = contGood szB`, `ε ≡ 1`: `#V = 2 ≤ N`, the per-time input by `precPT_of_le`
(`u ≤ 31/32 ≤ 1`), `ε ≤ ζ`, and `ξ(u) ≤ ξ(u') + 1`, `ζ(u') ≤ 2 ζ(u)` for `u' ≤ u` (`u ≤ 31/32 ≤ 1 + u'`). -/
example : StochDomAt szB.seqP szB.size (U := fun n => TimeIcc (fun _ : ℕ => (15 / 16 : ℝ))
      (fun _ : ℕ => (31 / 32 : ℝ)) n × Fin 2) (fun n p _ => (p.1 : ℝ)) (fun _ _ _ => (1 : ℝ)) := by
  refine nzLift_core_below (Ω := szB.SeqΩ) szB.seqP szB.size (szB.tendsto_size szB_tendsto)
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => by norm_num) (fun n => by norm_num) (fun _ => Fin 2)
    (fun n p _ => (p.1 : ℝ)) (fun _ _ _ => (1 : ℝ)) 1 1 zero_le_one zero_le_one ?_
    (precPT_of_le szB (fun n p ω => zero_le_one) (fun n p ω => ?_))
    (ContinuityNet.contGood szB) (ContinuityNet.cont_highProbAt_good szB (szB.tendsto_size szB_tendsto))
    (fun _ => 1) (fun _ => zero_le_one) (Eventually.of_forall fun n p ω => le_rfl) ?_
  · -- `#V = 2 ≤ N`
    filter_upwards [szB_tendsto.eventually_ge_atTop 2] with n hn
    rw [Real.rpow_one, Fintype.card_fin]
    exact_mod_cast hn
  · -- the per-time input: `u ≤ 1`
    have := p.1.2.2
    change (p.1 : ℝ) ≤ 1
    linarith
  · -- the one-sided closeness
    refine Eventually.of_forall fun n ω _ u u' hle _ v => ⟨?_, by norm_num⟩
    have h1 := u.2.2
    have h2 := u'.2.1
    change (u : ℝ) ≤ (u' : ℝ) + 1
    linarith

/-- **(7) `nzLift_netPt_floor` and `nzLift_bootRHS_mono` at numbers**: the floor net point of `x = 1/2` at `A = 1`,
`N = 4`; `STbootRHS 2 (XL ≡ 1) (XLK ≡ 1) (1/2) 3 1 ≤ STbootRHS 2 (XL ≡ 2) (XLK ≡ 3) (1/2) 3 1`. -/
example : ∃ k : Fin (netSize 1 4 + 1), netPt 1 1 4 k ≤ (1 / 2 : ℝ) ∧
    (1 / 2 : ℝ) - netPt 1 1 4 k ≤ 1 / (netSize 1 4 : ℝ) :=
  nzLift_netPt_floor 1 4 (1 / 2) (by norm_num) (by norm_num)

example : STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) 3 1 ≤
    STbootRHS 2 (fun _ => (2 : ℝ)) (fun _ => (3 : ℝ)) (1 / 2) 3 1 :=
  nzLift_bootRHS_mono 2 _ _ _ _ (1 / 2) 3 1 (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)

/-- **(8) the envelope at the instance window `[15/16, 31/32]`**: the constant control `1` has envelope `1` at every
time; the control `2 + u` has envelope `2 + 15/16` at `u = 15/16` (the infimum over the window is attained at the left
end) and `1` at `u = 1 > t` (empty set, the floor). -/
example : ∀ (m n : ℕ) (u : ℝ), nqFlowSharp (fun _ : ℕ => (31 / 32 : ℝ)) (fun _ _ _ => (1 : ℝ)) m n u = 1 :=
  fun m n u =>
    le_antisymm (nzLift_sharp_le (fun _ : ℕ => (31 / 32 : ℝ)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => le_rfl) m n u)
      (nzLift_sharp_one_le _ _ _ _ _)

example : nqFlowSharp (fun _ : ℕ => (31 / 32 : ℝ)) (fun _ _ u => (2 : ℝ) + u) 0 0 (15 / 16) = 2 + 15 / 16 ∧
    nqFlowSharp (fun _ : ℕ => (31 / 32 : ℝ)) (fun _ _ u => (2 : ℝ) + u) 0 0 1 = 1 := by
  constructor
  · unfold nqFlowSharp
    have h : sInf ((fun u : ℝ => (2 : ℝ) + u) '' Set.Icc (15 / 16) (31 / 32)) = 2 + 15 / 16 := by
      refine IsLeast.csInf_eq ⟨⟨15 / 16, ⟨le_rfl, by norm_num⟩, rfl⟩, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      linarith [hv.1]
    change max 1 (sInf ((fun u : ℝ => (2 : ℝ) + u) '' Set.Icc (15 / 16) (31 / 32))) = 2 + 15 / 16
    rw [h]; norm_num
  · unfold nqFlowSharp
    have h : Set.Icc (1 : ℝ) (31 / 32) = ∅ := Set.Icc_eq_empty (by norm_num)
    change max 1 (sInf ((fun u : ℝ => (2 : ℝ) + u) '' Set.Icc 1 (31 / 32))) = 1
    rw [h, Set.image_empty, Real.sInf_empty]; norm_num

/-- **(9) the pinned statements of the check file, section 3**: `stOeqNZ''_holds` has exactly the type
`∀ d : ℕ, STOeqNZ'' d` (check `T2292b_stOeqNZ''_holds`), and `STOeqNZ'' 3` is the ingredient form of `STNZConcl''`. -/
example : ∀ d : ℕ, STOeqNZ'' d := @stOeqNZ''_holds

example : STOeqNZ'' 3 = STIngR 3 STCaseII (fun sz E s t => STNZConcl'' sz E s t) := rfl

end QtNonzeroFlowLiftInst

end RBM.Ind

end

#print axioms RBM.Gauss.Sizes.STNZConcl''
#print axioms RBM.Gauss.Sizes.STOeqNZ''
#print axioms RBM.Ind.stOeqNZ''_holds
#print axioms RBM.Ind.QtNonzeroFlowLiftInst.inst_OeqNZ''
