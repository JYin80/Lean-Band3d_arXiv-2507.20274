/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QtNonzeroFlowLift
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Induction.NewPQ
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.NQGood1
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.KDecay
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ExpWardII
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Events
import RBM3D.Green.Pins

/-!
# The regime-generic self-absorption bootstrap and `stOeqQtNZ'_holds` (`d ≥ 3`)

Ticket T2304 (S3-22c, stochastic layer ST-3, case (ii) `1 - s ≤ ilambda²/L²`; last of the chain
S3-21 = T2274, S3-22a = T2284, S3-22b = T2292 `Induction/QtNonzeroFlow`, S3-22b2 = T2299
`Induction/QtNonzeroFlowLift`).  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`:
`lem:STOeq_Qt_nonzero` `3_5:1561-1572`, proof `3_5:1889-1933` (`(eq:expandQAempty)` `3_5:1893`,
`(am;asoiuw_smalleta)` `3_5:1916-1922`, "with `n` replaced by `k_α`; `(Nη_t)^{-1} ≤ W^{-d}B_{t,0}`"
`3_5:1923-1926`, "solving which" `3_5:1929-1930`), `lem:STOeq_Qt` `3_5:1362-1378`
(`(am;asoi222)` `3_5:1366`), `(normQA2)` `3_5:1466`, `lem: newPQ` `3_5:1482-1507`.
DECISIONS §62 (1), (2), (4), §80, §85, §90, §91 (2), §95 (3), §105 (1) (supervisor
`2026-10-06-1356` O1, O2).

## What is here

* §1 the pin `STXiRound'` (namespace `RBM.Gauss.Sizes`): `STXiBoot'` with the `XLK` hypotheses for
  `m ≤ n_` (the current length included) and the right side
  `B_u^{1/6} XLK n_ u + STbootRHS 1 … B_s n_ p` (`u = q.1.2`; R2* unchanged);
* §2 `stBoot_rounds`, the abstract finite deterministic bootstrap: crude start `ξ ≺ N^{C₀}`, round
  `ξ ≺ Y ⇒ ξ ≺ N^{-c} Y + R`, conclusion `ξ ≺ R` after `⌈C₀/c⌉ + 1` rounds (`r` depends on `C₀, c`
  only);
* §3 setting facts (private, prefix `qtBoot_`): the contraction `(W^{-d} B_{u,0})^{1/6} ≤ N^{-c}`,
  `c = min(2 𝔡 𝔠, ε/2)/12`, uniformly in `u ∈ [0, t_n]` and in both regimes (from `(eq:WO)`,
  `W ≥ N^𝔠`, `1 - t ≥ N^{-1+ε/2}`; no regime predicate, no `(con_st_ind)`); the crude start
  `Ξ̂ ≺ N^{2 n_ + 1}`; the `STbootRHS` facts (`XLK` is read at lengths `≤ n_ - 1` only: the
  §95 (3) fact in Lean);
* §4 `stXiBoot'_of_round` (flow setting), `stXiBootR_of_round` (`STIngR`, the regime `R` a
  parameter; S3-18b2 instantiates it at `STCaseI`);
* §5 `stXiRoundNZ_holds`: the `newPQ` combination on the uniform projected endpoint `STNZConcl''`
  (`stOeqNZ''_holds`, T2299): envelope copies, `zeroModeCalc_LK_expansion_empty` per `σ`, the lower
  terms `k_α ∈ [1, n_ - 1]` bounded by the hypotheses, finite max and sums;
* §6 `stOeqQtNZ'_holds : ∀ d, STOeqQtNZ' d`;
* §7 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.QtNonzeroBootInst`).

Paper-delta candidates (see the report): `T2304a` ("solving which" is a finite deterministic
bootstrap with an a priori crude start that the paper does not state), `T2304b` (the lower terms of
`(eq:expandQAempty)`, `k_α = 1` included, follow from the hypotheses with `(normQA2)` and
`(Nη_t)^{-1} ≤ C W^{-d}B_{t,0}`; neither `(eq:kalpha1)` nor `(am;asoiuw_smalleta)` at length `k_α`
is used).

The file adds no drift or good-set level (DECISIONS §95 (3)): the current length `n_` enters only
as the self-absorbing summand `B_u^{1/6} XLK n_` of `STXiRound'`, removed by deterministic rounds
(`Y_j` are deterministic functions of `(n, u)`).  Every helper that the ticket does not pin is
`private` or prefixed `qtBoot_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The pin -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **One round of `(am;asoi222)` with the current-length control** (T2304; `lem:STOeq_Qt` and `(am;asoi222)`
`3_5:1361-1366`; the bound `(am;asoiuw_smalleta)` and the display before "solving which" `3_5:1916-1930`;
DECISIONS §62 (1), §105 (1); R2* §80): under `Ξ̂ ≺ Ξ` for every length `m ≤ n_` (the current one included), over the
pairs `(v, u)`: `Ξ̂^{(𝓛-𝒦)}_{v,n_} ≺ B_u^{1/6} XLK n_ u + STbootRHS 1 XL XLK B_s n_ p`.  It is `STXiBoot'`
(`NQEndFlow.lean:95`) with two changes: the hypotheses `m + 1 ≤ n_` ↦ `m ≤ n_`, and the extra summand
`B_u^{1/6} XLK n_ u`. -/
def STXiRound' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

end Pins

end RBM.Gauss.Sizes

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 2. The abstract self-absorption bootstrap -/

/-- A pointwise larger right side keeps `≺`, eventually in `n` (copy of `NQEndFlow.lean:206`, with the comparison
only for large `n`). -/
private theorem qtBoot_prec_of_le_ev {d : ℕ} {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, hle.mono fun n hn ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- The pointwise form of `qtBoot_prec_of_le_ev`. -/
private theorem qtBoot_prec_of_le_right {d : ℕ} {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' :=
  qtBoot_prec_of_le_ev h (Eventually.of_forall hle)

/-- The rounds `Y_0 = N^{C₀}`, `Y_{j+1} = N^{-c} Y_j + R` (deterministic functions of `(n, u)`). -/
private noncomputable def qtBoot_Y {d : ℕ} (sz : Sizes d) (c C₀ : ℝ) (R : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0 => fun n _ => ((sz.size n : ℕ) : ℝ) ^ C₀
  | j + 1 => fun n u => ((sz.size n : ℕ) : ℝ) ^ (-c) * qtBoot_Y sz c C₀ R j n u + R n u

/-- **The abstract self-absorption bootstrap** (DECISIONS §62 (1), §105 (1) O2; paper `3_5:1923-1930`, "solving
which"): from a crude start `ξ ≺ N^{C₀}` and a round `ξ ≺ Y ⇒ ξ ≺ N^{-c} Y + R` (every deterministic `Y ≥ 1` of the
endpoint `π q`), `ξ ≺ R` after `⌈C₀/c⌉ + 1` rounds.  The round count depends on `C₀, c` only, never on `n`
(paper-delta candidate `T2304a`). -/
theorem stBoot_rounds {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {U : ℕ → Type} (π : ∀ n, U n → ℝ)
    (ξ : ∀ n, U n → sz.SeqΩ → ℝ) (R : ℕ → ℝ → ℝ) (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    (hR : ∀ n u, 1 ≤ R n u)
    (h0 : Prec sz (U := U) ξ (fun n _ _ => ((sz.size n : ℕ) : ℝ) ^ C₀))
    (hround : ∀ Y : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ Y n u) →
      Prec sz (U := U) ξ (fun n q _ => Y n (π n q)) →
      Prec sz (U := U) ξ (fun n q _ => ((sz.size n : ℕ) : ℝ) ^ (-c) * Y n (π n q) + R n (π n q))) :
    Prec sz (U := U) ξ (fun n q _ => R n (π n q)) := by
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hNc : ∀ n, ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ 1 := fun n =>
    Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)
  have hNc0 : ∀ n, 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := fun n => Real.rpow_nonneg (by linarith [hN1 n]) _
  -- (a) `Y_j ≥ 1`
  have hY1 : ∀ j n u, 1 ≤ qtBoot_Y sz c C₀ R j n u := by
    intro j
    induction j with
    | zero => intro n u; exact Real.one_le_rpow (hN1 n) hC₀
    | succ j ih =>
      intro n u
      have := mul_nonneg (hNc0 n) (zero_le_one.trans (ih n u))
      have := hR n u
      change 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) * qtBoot_Y sz c C₀ R j n u + R n u
      linarith
  -- (b) `ξ ≺ Y_j`
  have hYp : ∀ j, Prec sz (U := U) ξ (fun n q _ => qtBoot_Y sz c C₀ R j n (π n q)) := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ih => exact hround (qtBoot_Y sz c C₀ R j) (hY1 j) ih
  -- (c) `Y_j ≤ N^{C₀ - j c} + j R`
  have hYb : ∀ j n u, qtBoot_Y sz c C₀ R j n u ≤
      ((sz.size n : ℕ) : ℝ) ^ (C₀ - j * c) + j * R n u := by
    intro j
    induction j with
    | zero => intro n u; simp [qtBoot_Y]
    | succ j ih =>
      intro n u
      have hR0 : 0 ≤ R n u := zero_le_one.trans (hR n u)
      have hpow : ((sz.size n : ℕ) : ℝ) ^ (-c) * ((sz.size n : ℕ) : ℝ) ^ (C₀ - j * c) =
          ((sz.size n : ℕ) : ℝ) ^ (C₀ - ((j + 1 : ℕ) : ℝ) * c) := by
        rw [← Real.rpow_add (by linarith [hN1 n])]
        congr 1
        push_cast
        ring
      have h1 : ((sz.size n : ℕ) : ℝ) ^ (-c) * qtBoot_Y sz c C₀ R j n u ≤
          ((sz.size n : ℕ) : ℝ) ^ (-c) * (((sz.size n : ℕ) : ℝ) ^ (C₀ - j * c) + j * R n u) :=
        mul_le_mul_of_nonneg_left (ih n u) (hNc0 n)
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (-c) * ((j : ℝ) * R n u) ≤ (j : ℝ) * R n u := by
        have := mul_le_mul_of_nonneg_right (hNc n) (mul_nonneg (Nat.cast_nonneg j) hR0)
        linarith
      change ((sz.size n : ℕ) : ℝ) ^ (-c) * qtBoot_Y sz c C₀ R j n u + R n u ≤
        ((sz.size n : ℕ) : ℝ) ^ (C₀ - ((j + 1 : ℕ) : ℝ) * c) + ((j + 1 : ℕ) : ℝ) * R n u
      rw [← hpow]
      push_cast
      nlinarith
  -- (d) at `r = ⌈C₀/c⌉₊ + 1`
  set r : ℕ := ⌈C₀ / c⌉₊ + 1 with hr
  have hrc : C₀ - (r : ℝ) * c ≤ -c := by
    have h1 : C₀ / c ≤ (⌈C₀ / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : C₀ ≤ (⌈C₀ / c⌉₊ : ℝ) * c := by
      have := (div_le_iff₀ hc).1 h1
      linarith
    rw [hr]
    push_cast
    nlinarith
  have hYr : ∀ n u, qtBoot_Y sz c C₀ R r n u ≤ ((r : ℝ) + 1) * R n u := by
    intro n u
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (C₀ - (r : ℝ) * c) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)
    have h2 := hYb r n u
    have h3 := hR n u
    nlinarith
  -- (e) the constant `r + 1` is absorbed
  have hrp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hmain : Prec sz (U := U) ξ (fun n q _ => ((r : ℝ) + 1) * R n (π n q)) :=
    qtBoot_prec_of_le_right (hYp r) fun n q ω => hYr n (π n q)
  have hmain' := StochDomAt.const_mul_right (sz.tendsto_size hsz) (inv_pos.2 hrp)
    (fun n q ω => mul_nonneg hrp.le (zero_le_one.trans (hR n (π n q)))) hmain
  refine (show (fun n (q : U n) (ω : sz.SeqΩ) => ((r : ℝ) + 1)⁻¹ * (((r : ℝ) + 1) * R n (π n q))) =
    fun n (q : U n) _ => R n (π n q) from ?_) ▸ hmain'
  funext n q ω
  field_simp


/-! ## 3. Setting facts (private) -/

section Setting

variable {d : ℕ}

/-- The contraction exponent `c = min(2 𝔡 𝔠, ε/2)/12` (DECISIONS §105 (1) O2): `(W^{-d} B_{u,0})^{1/6} ≤ N^{-c}`
for every `u ∈ [0, t_n]` and `n` large, in both regimes (the source bound is `B_u ≤ W^{-2𝔡} + N^{-ε/2}`,
from `(eq:WO)`, `W ≥ N^𝔠` and `1 - t ≥ N^{-1+ε/2}`; no regime predicate and no `(con_st_ind)`). -/
private noncomputable def qtBoot_c (𝔠 𝔡 ε : ℝ) : ℝ := min (2 * 𝔡 * 𝔠) (ε / 2) / 12

private theorem qtBoot_c_pos {𝔠 𝔡 ε : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (hε : 0 < ε) : 0 < qtBoot_c 𝔠 𝔡 ε := by
  unfold qtBoot_c
  have : 0 < min (2 * 𝔡 * 𝔠) (ε / 2) := lt_min (by positivity) (by linarith)
  positivity

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually (copy of `NQEndFlowLift.lean:859`). -/
private theorem qtBoot_flowLam (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- **The contraction** (`qtBoot_contraction`): eventually in `n`, for every `u ∈ [0, t_n]`,
`W^{-d} B_{u,0} ≤ N^{-c₁/2}` with `c₁ = min(2 𝔡 𝔠, ε/2)`; hence `B_u ≤ 1` and `B_u^{1/6} ≤ N^{-c}`,
`c = c₁/12 = qtBoot_c 𝔠 𝔡 ε`. -/
private theorem qtBoot_contraction (sz : Sizes d) {𝔠 𝔡 ε : ℝ} {t : ℕ → ℝ} (hA : sz.Admissible 𝔠 𝔡) (hε : 0 < ε)
    (ht1 : ∀ n, t n < 1) (hrange : sz.RangeCond (ε / 2) t) :
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      sz.Bctl n u ≤ 1 ∧ (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(qtBoot_c 𝔠 𝔡 ε)) := by
  obtain ⟨h𝔠, h𝔡, hsize, hband, hWO⟩ := hA
  have hc₁ : 0 < min (2 * 𝔡 * 𝔠) (ε / 2) := lt_min (by positivity) (by linarith)
  set c₁ := min (2 * 𝔡 * 𝔠) (ε / 2) with hc₁def
  have hN := sz.tendsto_size hsize
  filter_upwards [hband, hWO, hrange, hN.eventually (RBM.eventually_le_rpow 2 (half_pos hc₁))] with n hb hw hr h2
  intro u hu0 hut
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hw.1
  have h1u : 0 < 1 - u := by linarith
  have h1t : 0 < 1 - t n := by linarith [ht1 n]
  -- the source bound `B ≤ N^{-2𝔡𝔠} + N^{-ε/2}`
  have hsq := Sizes.lam_sq_mul_pow_ge sz n hw.1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hlam2 : 0 < sz.lam n ^ 2 := by positivity
  have hterm1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤
      ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
    have hWb : ((sz.size n : ℕ) : ℝ) ^ (2 * 𝔡 * 𝔠) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le 𝔠) hb (by positivity : (0 : ℝ) ≤ 2 * 𝔡)
      rwa [← Real.rpow_mul hN0.le, mul_comm 𝔠 (2 * 𝔡)] at this
    rw [← mul_inv, Real.rpow_neg hN0.le]
    refine inv_anti₀ (by positivity) ?_
    calc ((sz.size n : ℕ) : ℝ) ^ (2 * 𝔡 * 𝔠) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := hWb
      _ ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hsq
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (sz.lam n ^ 2 + (1 - u)) := by nlinarith
  have hterm2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
      ((sz.size n : ℕ) : ℝ) ^ (-(ε / 2)) := by
    have hsz : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ =
        (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
      rw [← mul_inv]
      congr 1
      simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
      ring
    rw [hsz, Real.rpow_neg hN0.le]
    have hNe : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) = ((sz.size n : ℕ) : ℝ) ^ (ε / 2) := by
      calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2)
          = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) := by rw [Real.rpow_one]
        _ = ((sz.size n : ℕ) : ℝ) ^ ((1 : ℝ) + (-1 + ε / 2)) := (Real.rpow_add hN0 _ _).symm
        _ = ((sz.size n : ℕ) : ℝ) ^ (ε / 2) := by congr 1; ring
    refine inv_anti₀ (Real.rpow_pos_of_pos hN0 _) ?_
    rw [← hNe]
    exact mul_le_mul_of_nonneg_left (hr.trans (by linarith)) hN0.le
  have hB : sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₁) := by
    rw [ContinuityNet.cont_Bctl_eq sz n hu1, mul_add]
    have e1 : ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₁) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_left (2 * 𝔡 * 𝔠) (ε / 2)])
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (-(ε / 2)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₁) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_right (2 * 𝔡 * 𝔠) (ε / 2)])
    linarith
  -- `2 N^{-c₁} ≤ N^{-c₁/2}`
  have hy : 2 * ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) ≤ 1 := by
    rw [Real.rpow_neg hN0.le]
    have hpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (c₁ / 2) := Real.rpow_pos_of_pos hN0 _
    calc 2 * (((sz.size n : ℕ) : ℝ) ^ (c₁ / 2))⁻¹
        ≤ ((sz.size n : ℕ) : ℝ) ^ (c₁ / 2) * (((sz.size n : ℕ) : ℝ) ^ (c₁ / 2))⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hpos.le)
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have hy0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) := Real.rpow_nonneg hN0.le _
  have hyy : ((sz.size n : ℕ) : ℝ) ^ (-c₁) =
      ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) * ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hBy : sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) := by
    calc sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₁) := hB
      _ = (2 * ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2))) * ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) := by rw [hyy]; ring
      _ ≤ 1 * ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) := mul_le_mul_of_nonneg_right hy hy0
      _ = _ := one_mul _
  have hy1 : ((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  refine ⟨hBy.trans hy1, ?_⟩
  have hB0 : 0 ≤ sz.Bctl n u := (STBctl_pos sz n hu1).le
  calc (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ (((sz.size n : ℕ) : ℝ) ^ (-(c₁ / 2))) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow hB0 hBy (by norm_num)
    _ = ((sz.size n : ℕ) : ℝ) ^ (-(qtBoot_c 𝔠 𝔡 ε)) := by
        rw [← Real.rpow_mul hN0.le]
        congr 1
        unfold qtBoot_c
        ring

/-- **The crude start** (DECISIONS §62 (1); paper `3_5:1923-1926` supplies no a priori bound, T2304a): for `n_ ≥ 1`,
`Ξ̂^{(𝓛-𝒦)}_{v,n_} ≺ N^{2 n_ + 1}` over the pairs (indeed `Ξ̂ ≤ N^{2 n_ + 1}` for every sample, once `N` is large).
Hermitian crude loop bound `|𝓛| ≤ η^{-ℓ}` (`STXiLKM_crudeN`), `|𝒦| ≤ N` (`stKbound_timeIcc` at `τ = 1`, `B ≤ 1`),
`η⁻¹ ≤ μ N` (`expWII_inv_Neta_le`, `B ≤ 1`, `Im m ≥ √(κ/2)/2`, `ST_mE_im_ge`), `B⁻¹ ≤ N` (`cont_inv_size_le_Bctl`). -/
private theorem qtBoot_crude (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) {n_ : ℕ} (hn : 1 ≤ n_) :
    Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (STflowE z n) q.1.1 n_ ω)
      (fun n _ _ => ((sz.size n : ℕ) : ℝ) ^ (((2 * n_ + 1 : ℕ) : ℝ))) := by
  obtain ⟨hA, hE', ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hsize := hA.2.2.1
  have hN := sz.tendsto_size hsize
  have hcon := qtBoot_contraction sz hA hε ht1 hrange
  have hKb := stKbound_timeIcc sz hd (E := STflowE z) (κ := κ / 2) (gmax := 𝔡⁻¹) (half_pos hκ)
    (inv_pos.2 hA.2.1) hsize (Eventually.of_forall fun n => (hE' n).le) (qtBoot_flowLam sz hflow) hs
    (fun n => (hst n).le) ht1 n_ hn
  have hKdet := ((st6_prec_det_iff sz hsize _ _).1 hKb) 1 one_pos
  have hμ0 : 0 < (Real.sqrt (κ / 2) / 2)⁻¹ := by
    have : 0 < Real.sqrt (κ / 2) := Real.sqrt_pos.2 (half_pos hκ)
    positivity
  set μ : ℝ := (Real.sqrt (κ / 2) / 2)⁻¹ with hμ
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  filter_upwards [hcon, hKdet, hsize.eventually_ge_atTop (2 + μ ^ n_)] with n hc hK hN2
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro q
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hv0 : 0 ≤ q.1.1 := (hs n).trans q.2.1
  have hvt : q.1.1 ≤ t n := q.2.2.1.trans q.2.2.2
  have hv1 : q.1.1 < 1 := hvt.trans_lt (ht1 n)
  have hB1 : sz.Bctl n q.1.1 ≤ 1 := (hc q.1.1 hv0 hvt).1
  have hBpos : 0 < sz.Bctl n q.1.1 := STBctl_pos sz n hv1
  have hE2 : |STflowE z n| < 2 := by linarith [hE' n]
  -- `|𝒦| ≤ N`
  have hKN : ∀ (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)),
      ‖sz.STKloop n (STflowE z n) q.1.1 σ a‖ ≤ ((sz.size n : ℕ) : ℝ) := by
    intro σ a
    have h1 := hK (⟨q.1.1, q.2.1, hvt⟩, σ, a)
    have h2 : (sz.Bctl n q.1.1) ^ (n_ - 1) ≤ 1 := pow_le_one₀ hBpos.le hB1
    rw [Real.rpow_one] at h1
    have h3 : ((sz.size n : ℕ) : ℝ) * (sz.Bctl n q.1.1) ^ (n_ - 1) ≤ ((sz.size n : ℕ) : ℝ) := by
      calc ((sz.size n : ℕ) : ℝ) * (sz.Bctl n q.1.1) ^ (n_ - 1)
          ≤ ((sz.size n : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h2 hN0.le
        _ = _ := mul_one _
    exact h1.trans h3
  -- the loop bound
  have hcr := STXiLKM_crudeN sz n hE2 (seqHflow_isHermitian sz n q.1.1 ω) hv0 hv1 hB1 hn (le_refl n_) hKN
  rw [gridGood_STXiLKM_seqHflow] at hcr
  -- `η⁻¹ ≤ μ N`
  have hη : (etaT (STflowE z n) q.1.1)⁻¹ ≤ μ * ((sz.size n : ℕ) : ℝ) := by
    have hηpos := etaT_pos hE2 hv1
    have h1 := expWII_inv_Neta_le sz n hE2 hv1
    have hm : Real.sqrt (κ / 2) / 2 ≤ (mE (STflowE z n)).im := ST_mE_im_ge (half_pos hκ) (hE' n).le
    have hmpos : 0 < Real.sqrt (κ / 2) / 2 := by
      have : 0 < Real.sqrt (κ / 2) := Real.sqrt_pos.2 (half_pos hκ)
      positivity
    have h2 : ((mE (STflowE z n)).im)⁻¹ ≤ μ := inv_anti₀ hmpos hm
    have h3 : (etaT (STflowE z n) q.1.1)⁻¹ =
        ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) * etaT (STflowE z n) q.1.1)⁻¹ := by
      rw [mul_inv, mul_inv_cancel_left₀ hN0.ne']
    rw [h3]
    calc ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) * etaT (STflowE z n) q.1.1)⁻¹
        ≤ ((sz.size n : ℕ) : ℝ) * (((mE (STflowE z n)).im)⁻¹ * sz.Bctl n q.1.1) :=
          mul_le_mul_of_nonneg_left h1 hN0.le
      _ ≤ ((sz.size n : ℕ) : ℝ) * (μ * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hN0.le
          exact mul_le_mul h2 hB1 hBpos.le hμ0.le
      _ = μ * ((sz.size n : ℕ) : ℝ) := by ring
  -- `B⁻¹ ≤ N`
  have hBinv : (sz.Bctl n q.1.1)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    have h1 := ContinuityNet.cont_inv_size_le_Bctl sz n hv0 hv1
    have h2 := inv_anti₀ (inv_pos.2 hN0) h1
    rwa [inv_inv] at h2
  have hηn : (etaT (STflowE z n) q.1.1)⁻¹ ^ n_ ≤ μ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ n_ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 (etaT_pos hE2 hv1).le) hη n_
  have hBn : 1 / (sz.Bctl n q.1.1) ^ n_ ≤ ((sz.size n : ℕ) : ℝ) ^ n_ := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hBpos.le) hBinv n_
  have hμn : 0 ≤ μ ^ n_ := pow_nonneg hμ0.le n_
  have hX1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := one_le_pow₀ hN1
  have hX2 : ((sz.size n : ℕ) : ℝ) ^ (n_ + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_) :=
    pow_le_pow_right₀ hN1 (by omega)
  have hX3 : ((sz.size n : ℕ) : ℝ) ^ (n_) * ((sz.size n : ℕ) : ℝ) ^ (n_) = ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by
    rw [← pow_add]; congr 1; ring
  have hX4 : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (n_) = ((sz.size n : ℕ) : ℝ) ^ (n_ + 1) := by
    rw [pow_succ]; ring
  have hfinal : sz.STXiLK n (STflowE z n) q.1.1 n_ ω ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) := by
    refine hcr.trans ?_
    have hnum : ((etaT (STflowE z n) q.1.1)⁻¹ ^ n_ + ((sz.size n : ℕ) : ℝ)) / (sz.Bctl n q.1.1) ^ n_ ≤
        (μ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ n_ + ((sz.size n : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ n_ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith) hBn (by positivity) (by positivity)
    have hexp : (μ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ n_ + ((sz.size n : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ n_ =
        μ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) + ((sz.size n : ℕ) : ℝ) ^ (n_ + 1) := by
      rw [← hX3, ← hX4]; ring
    have hpow : ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by
      rw [pow_succ]; ring
    have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by positivity
    calc 1 + ((etaT (STflowE z n) q.1.1)⁻¹ ^ n_ + ((sz.size n : ℕ) : ℝ)) / (sz.Bctl n q.1.1) ^ n_
        ≤ 1 + (μ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) + ((sz.size n : ℕ) : ℝ) ^ (n_ + 1)) := by
          rw [← hexp]; linarith
      _ ≤ (2 + μ ^ n_) * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by nlinarith
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := mul_le_mul_of_nonneg_right hN2 hX0
      _ = _ := hpow.symm
  have hτ1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hC : ((sz.size n : ℕ) : ℝ) ^ (((2 * n_ + 1 : ℕ) : ℝ)) = ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) :=
    Real.rpow_natCast _ _
  rw [hC]
  have : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) := by positivity
  nlinarith

/-! ### `STbootRHS` -/

/-- **`STbootRHS` reads `XLK` only at lengths `≤ n_ - 1`** (the §95 (3) fact in Lean): for `lo ≥ 1`, the control
`XLK` may be changed at every length `m ≥ n_` without changing the value (the indices that occur are `m ∈ Icc lo (n_-1)`
and `n_ + 2 - m` for `m ∈ Icc ((n_+1)/2+1) (n_-1)`, and in the second range `1 ≤ n_ + 2 - m ≤ n_ - 1`: the range is
empty for `n_ ≤ 3`, and `(n_+1)/2 ≥ 2` for `n_ ≥ 4`). -/
private theorem qtBoot_bootRHS_update {lo : ℕ} (hlo : 1 ≤ lo) {XL XLK XLK' : ℕ → ℝ} {B : ℝ} {n_ p : ℕ}
    (h : ∀ m, 1 ≤ m → m + 1 ≤ n_ → XLK' m = XLK m) :
    STbootRHS lo XL XLK' B n_ p = STbootRHS lo XL XLK B n_ p := by
  unfold STbootRHS
  have h1 : ∑ m ∈ Finset.Icc lo (n_ - 1), XLK' m = ∑ m ∈ Finset.Icc lo (n_ - 1), XLK m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    exact h m (by omega) (by omega)
  have h2 : ∑ m ∈ Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1),
        XLK' (n_ + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2) ^ (1 / 2 : ℝ) =
      ∑ m ∈ Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1),
        XLK (n_ + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2) ^ (1 / 2 : ℝ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    rw [h (n_ + 2 - m) (by omega) (by omega)]
  rw [h1, h2]

/-- `1 ≤ STbootRHS lo XL XLK B k p` for `XL ≥ 1`, `XLK ≥ 0`, `B ≥ 0`, `k ≥ 1` (copy of `nzLift_bootRHS_one_le`,
`QtNonzeroFlowLift.lean:193`). -/
private theorem qtBoot_bootRHS_one_le {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 1 ≤ k)
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

/-- `STbootRHS 2 ≤ STbootRHS 1` for `XLK ≥ 0` (the summand `XLK 1` is added). -/
private theorem qtBoot_bootRHS_two_le_one {XL XLK : ℕ → ℝ} {B : ℝ} {n_ p : ℕ} (hXLK : ∀ m, 0 ≤ XLK m) :
    STbootRHS 2 XL XLK B n_ p ≤ STbootRHS 1 XL XLK B n_ p := by
  unfold STbootRHS
  have : ∑ m ∈ Finset.Icc 2 (n_ - 1), XLK m ≤ ∑ m ∈ Finset.Icc 1 (n_ - 1), XLK m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (by norm_num)) fun m _ _ => hXLK m
  linarith

/-- Each `XLK k`, `1 ≤ k ≤ n_ - 1`, is at most `STbootRHS 1 XL XLK B n_ p` (`XL, XLK, B ≥ 0`). -/
private theorem qtBoot_XLK_le_bootRHS {XL XLK : ℕ → ℝ} {B : ℝ} {n_ p k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n_ - 1)
    (hXL : ∀ m, 0 ≤ XL m) (hXLK : ∀ m, 0 ≤ XLK m) (hB : 0 ≤ B) : XLK k ≤ STbootRHS 1 XL XLK B n_ p := by
  unfold STbootRHS
  have h1 : 0 ≤ B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * n_ - 1) ^ (1 / 2 : ℝ) *
      XL (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg (hXL _) _))
      (Real.rpow_nonneg (hXL _) _)
  have h2 : XLK k ≤ ∑ m ∈ Finset.Icc 1 (n_ - 1), XLK m :=
    Finset.single_le_sum (f := XLK) (fun m _ => hXLK m) (Finset.mem_Icc.2 ⟨hk1, hkn⟩)
  have h3 : 0 ≤ ∑ m ∈ Finset.Icc (n_ - 1) (n_ + 1), XL m := Finset.sum_nonneg fun m _ => hXL m
  have h4 : 0 ≤ ∑ m ∈ Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1),
      XLK (n_ + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2) ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (hXLK _) (Real.rpow_nonneg (mul_nonneg (hXL _) (hXL _)) _)
  linarith

end Setting

/-! ## 4. The bootstrap at a flow setting and at `STIngR` -/

/-- **`STXiRound' → STXiBoot'` at a flow setting** (regime-free; DECISIONS §62 (1), (2), (4), §105 (1) O2; paper
`3_5:1923-1930`, "solving which"): the abstract bootstrap `stBoot_rounds` with `ξ = Ξ̂^{(𝓛-𝒦)}_{v,n_}`, `π q = q.1.2`,
`R n u = STbootRHS 1 (XL u) (XLK u) B_s n_ p` (`≥ 1`), `C₀ = 2 n_ + 1` (`qtBoot_crude`), `c = qtBoot_c 𝔠 𝔡 ε`
(`qtBoot_contraction`); the round for a control `Y ≥ 1` is `STXiRound'` at `XLK' := Y` in the slot `m = n_`
(`STbootRHS` reads `XLK` at lengths `≤ n_ - 1` only, `qtBoot_bootRHS_update`) followed by `B_u^{1/6} Y ≤ N^{-c} Y`.
No regime predicate, no `STConStInd`, no `STKbound`-type premise of the pin enters.  Paper-delta candidate `T2304a`. -/
theorem stXiBoot'_of_round {d : ℕ} (hd : 3 ≤ d) (κ ε 𝔠 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (sz : Sizes d)
    (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (hround : STXiRound' sz (STflowE z) s t) :
    STXiBoot' sz (STflowE z) s t := by
  obtain ⟨hA, hE', ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hsize := hA.2.2.1
  have hcon := qtBoot_contraction sz hA hε ht1 hrange
  have hc := qtBoot_c_pos hA.1 hA.2.1 hε
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => STBctl_pos sz n ((hst n).trans (ht1 n))
  have hR1 : ∀ n u, 1 ≤ STbootRHS 1 (fun m => XL m n u) (fun m => XLK m n u) (sz.Bctl n (s n)) n_ p := fun n u =>
    qtBoot_bootRHS_one_le (by omega) (fun m => hXL m n u) (fun m => zero_le_one.trans (hXLK m n u)) (hBs n).le
  refine stBoot_rounds sz hsize (U := STPair s t) (fun n q => q.1.2)
    (fun n q ω => STXiLK sz n (STflowE z n) q.1.1 n_ ω)
    (fun n u => STbootRHS 1 (fun m => XL m n u) (fun m => XLK m n u) (sz.Bctl n (s n)) n_ p)
    (qtBoot_c 𝔠 𝔡 ε) (((2 * n_ + 1 : ℕ) : ℝ)) hc (Nat.cast_nonneg _) hR1
    (qtBoot_crude hd sz hκ hε hflow hs hst ht (by omega)) ?_
  intro Y hY1 hYp
  -- the round at `XLK' = Y` in the slot `n_`
  set XLK' : ℕ → ℕ → ℝ → ℝ := fun m n u => if m = n_ then Y n u else XLK m n u with hXLK'
  have hXLK'n : ∀ n u, XLK' n_ n u = Y n u := fun n u => by simp [hXLK']
  have hXLK'm : ∀ m, m ≠ n_ → ∀ n u, XLK' m n u = XLK m n u := fun m hm n u => by simp [hXLK', hm]
  have hXLK'1 : ∀ m n u, 1 ≤ XLK' m n u := by
    intro m n u
    by_cases hm : m = n_
    · rw [hm, hXLK'n]; exact hY1 n u
    · rw [hXLK'm m hm]; exact hXLK m n u
  have hXLK'p : ∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (STflowE z n) q.1.1 m ω)
        (fun n q _ => XLK' m n q.1.2) := by
    intro m hm1 hmn
    by_cases hm : m = n_
    · rw [hm]
      simp only [hXLK'n]
      exact hYp
    · have h1 : m + 1 ≤ n_ := by omega
      simp only [hXLK'm m hm]
      exact hXLKp m hm1 h1
  have h := hround n_ p hn hp XL XLK' hXL hXLK'1 hXLp hXLK'p
  refine qtBoot_prec_of_le_ev h ?_
  filter_upwards [hcon] with n hcn
  intro q ω
  have hu0 : 0 ≤ q.1.2 := (hs n).trans (q.2.1.trans q.2.2.1)
  have hcq := (hcn q.1.2 hu0 q.2.2.2).2
  have hupd : STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK' m n q.1.2) (sz.Bctl n (s n)) n_ p =
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p :=
    qtBoot_bootRHS_update (by norm_num) (fun m hm1 hm2 => hXLK'm m (by omega) n q.1.2)
  change (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK' n_ n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK' m n q.1.2) (sz.Bctl n (s n)) n_ p ≤
    ((sz.size n : ℕ) : ℝ) ^ (-(qtBoot_c 𝔠 𝔡 ε)) * Y n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p
  rw [hXLK'n, hupd]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hcq (zero_le_one.trans (hY1 n q.1.2))) _

/-- **The regime-generic bootstrap** (supervisor `2026-10-06-1356` O2; reused by S3-18b2 at `R := STCaseI`): the round
pin `STXiRound'` over an ingredient setting `STIngR d R` gives `STXiBoot'` over the same setting.  The constant
`𝔠_d` of the hypothesis is kept; the regime `R`, `STKbound`, `STKward`, `STLK s`, `STConStInd`, `STStep2Concl` go to the
round only (paper-delta candidate `T2304a`).  Case (i) consumer shape (S3-18b2): `stOeqQt'_holds d :=
stXiBootR_of_round d STCaseI H`, `H : STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t)`. -/
theorem stXiBootR_of_round (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (h : STIngR d R (fun sz E s t => STXiRound' sz E s t)) :
    STIngR d R (fun sz E s t => STXiBoot' sz E s t) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  exact stXiBoot'_of_round hd κ ε 𝔠 𝔡 hκ hε sz z hflow s t hs hst ht
    (H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2)

/-! ## 5. The case-(ii) round: the `newPQ` combination on `STNZConcl''` -/

section Combine

variable {d : ℕ}

/-! ### The envelope (copies of `QtNonzeroFlowLift.lean:98-149`; `nqFlowSharp` is the public vocabulary) -/

/-- Envelope (a): `1 ≤ X♯`. -/
private theorem qtBoot_sharp_one_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ),
    1 ≤ nqFlowSharp t X m n u :=
  fun _ _ _ _ _ => le_max_left _ _

/-- Envelope (b): `X♯ ≤ X` for a control `X ≥ 1`. -/
private theorem qtBoot_sharp_le : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u : ℝ), nqFlowSharp t X m n u ≤ X m n u := by
  intro t X hX m n u
  unfold nqFlowSharp
  refine max_le (hX m n u) ?_
  by_cases hu : u ≤ t n
  · exact csInf_le ⟨1, by rintro _ ⟨v, -, rfl⟩; exact hX m n v⟩ ⟨u, ⟨le_rfl, hu⟩, rfl⟩
  · rw [Set.Icc_eq_empty hu, Set.image_empty, Real.sInf_empty]
    exact zero_le_one.trans (hX m n u)

/-- Envelope (c): `X♯` is non-decreasing in `u ≤ t_n`. -/
private theorem qtBoot_sharp_mono : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u u' : ℝ), u ≤ u' → u' ≤ t n → nqFlowSharp t X m n u ≤ nqFlowSharp t X m n u' := by
  intro t X hX m n u u' huu' hu't
  unfold nqFlowSharp
  refine max_le_max le_rfl ?_
  refine csInf_le_csInf ⟨1, by rintro _ ⟨v, -, rfl⟩; exact hX m n v⟩
    ⟨X m n u', u', ⟨le_rfl, hu't⟩, rfl⟩ ?_
  exact Set.image_mono (Set.Icc_subset_Icc_left huu')

/-- Envelope (d): the pair hypotheses carry over to `X♯` (copy of `nzLift_sharp_prec`). -/
private theorem qtBoot_sharp_prec : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ)
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

/-- `STbootRHS` is monotone in both controls (copy of `nzLift_bootRHS_mono`, `QtNonzeroFlowLift.lean:158`). -/
private theorem qtBoot_bootRHS_mono : ∀ (lo : ℕ) (XL XL' XLK XLK' : ℕ → ℝ) (B : ℝ) (n_ p : ℕ), 0 < B →
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

/-! ### `≺` algebra for the combination -/

/-- **The supremum over a finite inner index**: if `f(q, p) ≺ ζ(q)` over the product `(q, p)` (`P n` a finite non-empty
type), then `max_p f(q, p) ≺ ζ(q)` over `q` (the failure sets coincide: the maximum is attained). -/
private theorem qtBoot_prec_sup {sz : Sizes d} {Q P : ℕ → Type*} [∀ n, Fintype (P n)]
    (hne : ∀ n, (Finset.univ : Finset (P n)).Nonempty)
    {f : ∀ n, Q n → P n → sz.SeqΩ → ℝ} {ζ : ∀ n, Q n → sz.SeqΩ → ℝ}
    (h : sz.Prec (U := fun n => Q n × P n) (fun n x ω => f n x.1 x.2 ω) (fun n x ω => ζ n x.1 ω)) :
    sz.Prec (U := Q) (fun n q ω => (Finset.univ : Finset (P n)).sup' (hne n) (fun p => f n q p ω)) ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup' (hne n) (fun p => f n q p ω)
  refine ⟨(q, p), ?_⟩
  change ((sz.size n : ℕ) : ℝ) ^ τ * ζ n q ω < f n q p ω
  rw [← hp]
  exact hq

/-- `ξ ≤ ξ₁ + ξ₂ + ζ`, `ξ₁ ≺ ζ`, `ξ₂ ≺ ζ`, `ζ ≥ 0` give `ξ ≺ ζ` (the failure of `ξ` forces the failure of `ξ₁` or `ξ₂` at
`τ/2`, once `N^{τ/2} ≥ 3`). -/
private theorem qtBoot_prec_of_add_le {sz : Sizes d} (hsz : sz.SizeTendsto) {U : ℕ → Type*}
    {ξ ξ₁ ξ₂ ζ : ∀ n, U n → sz.SeqΩ → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (h₁ : sz.Prec ξ₁ ζ) (h₂ : sz.Prec ξ₂ ζ) (hle : ∀ n u ω, ξ n u ω ≤ ξ₁ n u ω + ξ₂ n u ω + ζ n u ω) :
    sz.Prec ξ ζ := by
  have hsize := sz.tendsto_size hsz
  refine StochDomAt.of_subset_union hsize h₁ h₂ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (RBM.eventually_le_rpow 3 (half_pos hτ))] with n h3
  rintro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have hhalf : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
  have hζ0 := hζ n u ω
  have h1 := hno.1 u
  have h2 := hno.2 u
  have h4 := hle n u ω
  have hP : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
  nlinarith [mul_nonneg hP hζ0, mul_le_mul_of_nonneg_right h3 hζ0]

/-- A finite sum of `≺ ζ` families is `≺ ζ` (induction; `ξ₁ + ξ₂ ≤ ξ₁ + ξ₂ + ζ`). -/
private theorem qtBoot_prec_sum {sz : Sizes d} (hsz : sz.SizeTendsto) {U : ℕ → Type*} {ι : Type*}
    (S : Finset ι) {f : ι → ∀ n, U n → sz.SeqΩ → ℝ} {ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (h : ∀ i ∈ S, sz.Prec (f i) ζ) :
    sz.Prec (fun n u ω => ∑ i ∈ S, f i n u ω) ζ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact Sizes.prec_of_le sz hζ fun n u ω => by simpa using hζ n u ω
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine qtBoot_prec_of_add_le hsz hζ h1 h2 fun n u ω => ?_
    rw [Finset.sum_insert ha]
    linarith [hζ n u ω]

/-! ### The lower terms of `(eq:expandQAempty)` -/

/-- `(2 N η_v)⁻¹ ≤ (√(κ/2))⁻¹ B_v` for `|E| ≤ 2 - κ/2`, `v < 1` (`expWII_inv_Neta_le`, `Im m(E) ≥ √(κ/2)/2` by
`ST_mE_im_ge` at `κ/2`): the `(Nη_t)^{-1} ≤ C W^{-d}B_{t,0}` of `3_5:1925`. -/
private theorem qtBoot_inv_Neta (sz : Sizes d) (n : ℕ) {E v κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ / 2)
    (hv : v < 1) :
    (2 * (((sz.size n : ℕ) : ℝ) * etaT E v))⁻¹ ≤ (Real.sqrt (κ / 2))⁻¹ * sz.Bctl n v := by
  have hE2 : |E| < 2 := by linarith
  have hr : 0 < Real.sqrt (κ / 2) := Real.sqrt_pos.2 (half_pos hκ)
  have h1 := expWII_inv_Neta_le sz n hE2 hv
  have hm : Real.sqrt (κ / 2) / 2 ≤ (mE E).im := ST_mE_im_ge (half_pos hκ) hE
  have h2 : ((mE E).im)⁻¹ ≤ (Real.sqrt (κ / 2) / 2)⁻¹ := inv_anti₀ (by positivity) hm
  have hB : 0 ≤ sz.Bctl n v := (STBctl_pos sz n hv).le
  have h3 : (Real.sqrt (κ / 2) / 2)⁻¹ = 2 * (Real.sqrt (κ / 2))⁻¹ := by
    rw [inv_div]; field_simp
  rw [mul_inv]
  calc (2 : ℝ)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT E v)⁻¹
      ≤ 2⁻¹ * (((mE E).im)⁻¹ * sz.Bctl n v) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 2⁻¹ * ((2 * (Real.sqrt (κ / 2))⁻¹) * sz.Bctl n v) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h2.trans h3.le) hB) (by norm_num)
    _ = (Real.sqrt (κ / 2))⁻¹ * sz.Bctl n v := by ring

/-- **One lower term of `(eq:expandQAempty)`, divided by `B_v^{n_}`**: with `1 ≤ k ≤ n_ - 1` (`k_α = 1` included,
paper-delta candidate `T2304b`),
`|ξ| (2Nη_v)^{-(n_-k)} |(Q^{(A')}(𝓛-𝒦)^{(k)}_{v,σ'})(a ∘ ι)| / B_v^{n_} ≤ |ξ| 2^k (√(κ/2))^{-(n_-k)} Ξ̂^{(𝓛-𝒦)}_{v,k}`:
`(normQA2)` `‖Q^{(A')} T‖ ≤ 2^{#A'} ‖T‖` with `#A' ≤ k`, `‖T‖ ≤ max|(𝓛-𝒦)^{(k)}_v| ≤ B_v^k Ξ̂_{v,k}`, and
`(2Nη_v)⁻¹ ≤ (√(κ/2))⁻¹ B_v`: the powers of `B` cancel exactly (`(n_-k) + k = n_`). -/
private theorem qtBoot_term_le (sz : Sizes d) (n : ℕ) {E v κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ / 2)
    (hv1 : v < 1) (ω : sz.SeqΩ) {n_ k : ℕ} (hkn : k + 1 ≤ n_) (ξc : ℤ) (σ' : Fin k → Bool)
    (ι : Fin k → Fin n_) (A' : Finset (Fin k)) (a : Fin n_ → Zd d (sz.L n)) :
    ‖(ξc : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E v : ℂ)) ^ (n_ - k) *
        zeroModeSet d (sz.L n) A' (fun a' => sz.STLKM n E v (sz.seqHflow n v ω) σ' a') (a ∘ ι)‖ /
        (sz.Bctl n v) ^ n_ ≤
      (|(ξc : ℝ)| * 2 ^ k * ((Real.sqrt (κ / 2))⁻¹) ^ (n_ - k)) * sz.STXiLK n E v k ω := by
  have hE2 : |E| < 2 := by linarith
  have hη : 0 < etaT E v := etaT_pos hE2 hv1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hB : 0 < sz.Bctl n v := STBctl_pos sz n hv1
  have hr : 0 < Real.sqrt (κ / 2) := Real.sqrt_pos.2 (half_pos hκ)
  have hmk : (n_ - k) + k = n_ := by omega
  have hinv := qtBoot_inv_Neta sz n hκ hE hv1
  -- the scalar
  have hnorm : ‖(ξc : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E v : ℂ)) ^ (n_ - k)‖ =
      |(ξc : ℝ)| * ((2 * (((sz.size n : ℕ) : ℝ) * etaT E v))⁻¹) ^ (n_ - k) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast, Complex.norm_real,
      Complex.norm_two, Complex.norm_intCast, Real.norm_of_nonneg hη.le, div_eq_mul_inv, ← inv_pow]
    congr 3
    ring
  -- `max|(𝓛-𝒦)^{(k)}|` and `Ξ̂`
  have hMdef : sz.STmaxLK n E v k ω = (sz.STXiLK n E v k ω - 1) * (sz.Bctl n v) ^ k := by
    unfold STXiLK
    field_simp
    ring
  have hM0 : 0 ≤ sz.STmaxLK n E v k ω :=
    Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))) (norm_nonneg _)
  have hXi1 : 1 ≤ sz.STXiLK n E v k ω := by
    unfold STXiLK
    have : 0 ≤ sz.STmaxLK n E v k ω / (sz.Bctl n v) ^ k := div_nonneg hM0 (pow_nonneg hB.le _)
    linarith
  have hTnorm : ‖fun a' : Fin k → Zd d (sz.L n) => sz.STLKM n E v (sz.seqHflow n v ω) σ' a'‖ ≤
      sz.STmaxLK n E v k ω := by
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun b => ?_
    have := Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω - STKloop sz n E v p.1 p.2‖) (Finset.mem_univ (σ', b))
    exact this
  have hQ : ‖zeroModeSet d (sz.L n) A' (fun a' => sz.STLKM n E v (sz.seqHflow n v ω) σ' a') (a ∘ ι)‖ ≤
      2 ^ k * sz.STmaxLK n E v k ω := by
    have h1 := norm_le_pi_norm (zeroModeSet d (sz.L n) A' (fun a' => sz.STLKM n E v (sz.seqHflow n v ω) σ' a')) (a ∘ ι)
    have h2 := norm_zeroModeSet_le A' (fun a' => sz.STLKM n E v (sz.seqHflow n v ω) σ' a')
    have h3 : (2 : ℝ) ^ A'.card ≤ 2 ^ k := by
      refine pow_le_pow_right₀ (by norm_num) ?_
      simpa using Finset.card_le_univ A'
    calc _ ≤ _ := h1
      _ ≤ 2 ^ A'.card * ‖fun a' : Fin k → Zd d (sz.L n) => sz.STLKM n E v (sz.seqHflow n v ω) σ' a'‖ := h2
      _ ≤ 2 ^ k * sz.STmaxLK n E v k ω :=
          mul_le_mul h3 hTnorm (norm_nonneg _) (by positivity)
  -- assemble
  rw [norm_mul, hnorm, div_le_iff₀ (pow_pos hB _)]
  have hpow : ((2 * (((sz.size n : ℕ) : ℝ) * etaT E v))⁻¹) ^ (n_ - k) ≤
      ((Real.sqrt (κ / 2))⁻¹ * sz.Bctl n v) ^ (n_ - k) :=
    pow_le_pow_left₀ (inv_nonneg.2 (by positivity)) hinv _
  have hXk : sz.STmaxLK n E v k ω ≤ (sz.Bctl n v) ^ k * sz.STXiLK n E v k ω := by
    rw [hMdef]; nlinarith [pow_pos hB k]
  have hBn : (sz.Bctl n v) ^ n_ = (sz.Bctl n v) ^ (n_ - k) * (sz.Bctl n v) ^ k := by
    rw [← pow_add, hmk]
  calc |(ξc : ℝ)| * ((2 * (((sz.size n : ℕ) : ℝ) * etaT E v))⁻¹) ^ (n_ - k) *
        ‖zeroModeSet d (sz.L n) A' (fun a' => sz.STLKM n E v (sz.seqHflow n v ω) σ' a') (a ∘ ι)‖
      ≤ |(ξc : ℝ)| * (((Real.sqrt (κ / 2))⁻¹ * sz.Bctl n v) ^ (n_ - k)) *
        (2 ^ k * ((sz.Bctl n v) ^ k * sz.STXiLK n E v k ω)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) ?_ (norm_nonneg _) (by positivity)
        exact hQ.trans (mul_le_mul_of_nonneg_left hXk (by positivity))
    _ = (|(ξc : ℝ)| * 2 ^ k * ((Real.sqrt (κ / 2))⁻¹) ^ (n_ - k)) * sz.STXiLK n E v k ω *
        (sz.Bctl n v) ^ n_ := by
        rw [hBn, mul_pow]; ring

/-! ### The combination -/

/-- **The case-(ii) round from the uniform projected endpoint** (`lem:STOeq_Qt_nonzero`, proof `3_5:1889-1933`): at the
flow data `|E_n| < 2 - κ/2`, `0 ≤ s`, `t < 1`, `STNZConcl''` (the uniform pin for `Q^{(I_diff σ)}(𝓛-𝒦)`) gives
`STXiRound'`: `lem: newPQ` at `A = ∅` (`zeroModeCalc_LK_expansion_empty`, data chosen per `σ`) writes
`(𝓛-𝒦)^{(n_)}_{v,σ,a}` as `(Q^{(I_diff σ)}(𝓛-𝒦)^{(n_)})_{σ,a}` plus lower terms; the first is `STNZConcl''` at the
envelope controls (compared with the controls of the round on the pairs), every lower term `k_α ∈ [1, n_-1]` is
`≤ C_{n_} Ξ̂_{v,k_α}` (`qtBoot_term_le`) and `Ξ̂_{v,k_α} ≺ XLK k_α u ≤ STbootRHS 1`; the finite max over `(σ, a)` and the finite
sums are `≺` algebra (`qtBoot_prec_sup`, `qtBoot_prec_sum`, `qtBoot_prec_of_add_le`).  Paper-delta candidate `T2304b`
(the lower terms follow from the hypotheses, `k_α = 1` included; no averaged law `(eq:kalpha1)`). -/
private theorem qtBoot_round_of_NZ (sz : Sizes d) (hsz : sz.SizeTendsto) {κ : ℝ} (hκ : 0 < κ) {E s t : ℕ → ℝ}
    (hE : ∀ n, |E n| < 2 - κ / 2) (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hNZ : STNZConcl'' sz E s t) : STXiRound' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsize := sz.tendsto_size hsz
  -- the envelope controls and the uniform endpoint at them
  have hXL' : ∀ m n u, 1 ≤ nqFlowSharp t XL m n u := fun m n u => qtBoot_sharp_one_le t XL m n u
  have hXLK' : ∀ m n u, 1 ≤ nqFlowSharp t XLK m n u := fun m n u => qtBoot_sharp_one_le t XLK m n u
  have hXLp' : ∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XL m n q.1.2) := fun m hm hl =>
    qtBoot_sharp_prec sz s t (fun n w ω => STXiL sz n (E n) w m ω) XL m hXL (hXLp m hm hl)
  have hXLKp' : ∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XLK m n q.1.2) := fun m hm hm' =>
    qtBoot_sharp_prec sz s t (fun n w ω => STXiLK sz n (E n) w m ω) XLK m hXLK (hXLKp m hm hm')
  have hNZ' := hNZ n_ p hn hp (fun m n u => nqFlowSharp t XL m n u) (fun m n u => nqFlowSharp t XLK m n u)
    hXL' hXLK' hXLp' hXLKp'
  -- positivity and the control `ζ`
  have hBs : ∀ n, ∀ q : STPair s t n, 0 < sz.Bctl n (s n) := fun n q =>
    STBctl_pos sz n (q.2.1.trans (q.2.2.1.trans q.2.2.2) |>.trans_lt (ht1 n))
  have hζ1 : ∀ (n : ℕ) (q : STPair s t n),
      1 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p := by
    intro n q
    have hu1 : q.1.2 < 1 := q.2.2.2.trans_lt (ht1 n)
    have h0 : 0 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 :=
      mul_nonneg (Real.rpow_nonneg (STBctl_pos sz n hu1).le _) (zero_le_one.trans (hXLK n_ n q.1.2))
    have := qtBoot_bootRHS_one_le (lo := 1) (XL := fun m => XL m n q.1.2) (XLK := fun m => XLK m n q.1.2)
      (B := sz.Bctl n (s n)) (k := n_) (p := p) (by omega) (fun m => hXL m n q.1.2)
      (fun m => zero_le_one.trans (hXLK m n q.1.2)) (hBs n q).le
    linarith
  have hζ0 : ∀ (n : ℕ) (q : STPair s t n) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p :=
    fun n q ω => zero_le_one.trans (hζ1 n q)
  -- (A) the first term, over the product `(q, σ, a)`
  have hT1 : Prec sz (U := fun n => STPair s t n × ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n))))
      (fun n x ω => ‖zeroModeSet d (sz.L n) (STIdiff x.2.1)
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) x.1.1.1 x.2.1 b ω - STKloop sz n (E n) x.1.1.1 x.2.1 b) x.2.2‖ /
        (sz.Bctl n x.1.1.1) ^ n_)
      (fun n x _ => (sz.Bctl n x.1.1.2) ^ (1 / 6 : ℝ) * XLK n_ n x.1.1.2 +
        STbootRHS 1 (fun m => XL m n x.1.1.2) (fun m => XLK m n x.1.1.2) (sz.Bctl n (s n)) n_ p) := by
    have h := StochDomAt.precomp_param
      (V := fun n => STPair s t n × ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)))) hNZ'
      (fun n x => (⟨x.1.1.1, x.1.2.1, x.1.2.2.1.trans x.1.2.2.2⟩,
        ⟨(x.2.1, STIdiff x.2.1), Finset.Subset.refl _⟩, x.2.2))
    refine qtBoot_prec_of_le_right h fun n x ω => ?_
    have hsv : s n ≤ x.1.1.1 := x.1.2.1
    have hvu : x.1.1.1 ≤ x.1.1.2 := x.1.2.2.1
    have hut : x.1.1.2 ≤ t n := x.1.2.2.2
    have hu1 : x.1.1.2 < 1 := hut.trans_lt (ht1 n)
    have hv1 : x.1.1.1 < 1 := hvu.trans_lt hu1
    have hBsn : 0 < sz.Bctl n (s n) := STBctl_pos sz n (hsv.trans_lt hv1)
    have hBv : 0 < sz.Bctl n x.1.1.1 := STBctl_pos sz n hv1
    have hBvu : sz.Bctl n x.1.1.1 ≤ sz.Bctl n x.1.1.2 := STBctl_mono sz n hvu hu1
    have hsharp : ∀ X : ℕ → ℕ → ℝ → ℝ, (∀ m n u, 1 ≤ X m n u) → ∀ m,
        nqFlowSharp t X m n x.1.1.1 ≤ X m n x.1.1.2 := fun X hX m =>
      (qtBoot_sharp_mono t X hX m n x.1.1.1 x.1.1.2 hvu hut).trans (qtBoot_sharp_le t X hX m n x.1.1.2)
    have h1 : (sz.Bctl n x.1.1.1) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n x.1.1.1 ≤
        (sz.Bctl n x.1.1.2) ^ (1 / 6 : ℝ) * XLK n_ n x.1.1.2 :=
      mul_le_mul (Real.rpow_le_rpow hBv.le hBvu (by norm_num)) (hsharp XLK hXLK n_)
        (zero_le_one.trans (qtBoot_sharp_one_le t XLK n_ n x.1.1.1)) (Real.rpow_nonneg (hBv.le.trans hBvu) _)
    have h2 : STbootRHS 2 (fun m => nqFlowSharp t XL m n x.1.1.1) (fun m => nqFlowSharp t XLK m n x.1.1.1)
          (sz.Bctl n (s n)) n_ p ≤
        STbootRHS 2 (fun m => XL m n x.1.1.2) (fun m => XLK m n x.1.1.2) (sz.Bctl n (s n)) n_ p :=
      qtBoot_bootRHS_mono 2 _ _ _ _ _ n_ p hBsn
        (fun m => zero_le_one.trans (qtBoot_sharp_one_le t XL m n x.1.1.1))
        (fun m => zero_le_one.trans (qtBoot_sharp_one_le t XLK m n x.1.1.1))
        (fun m => hsharp XL hXL m) (fun m => hsharp XLK hXLK m)
    have h3 := qtBoot_bootRHS_two_le_one (XL := fun m => XL m n x.1.1.2) (XLK := fun m => XLK m n x.1.1.2)
      (B := sz.Bctl n (s n)) (n_ := n_) (p := p) (fun m => zero_le_one.trans (hXLK m n x.1.1.2))
    change (sz.Bctl n x.1.1.1) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n x.1.1.1 +
        STbootRHS 2 (fun m => nqFlowSharp t XL m n x.1.1.1) (fun m => nqFlowSharp t XLK m n x.1.1.1)
          (sz.Bctl n (s n)) n_ p ≤
      (sz.Bctl n x.1.1.2) ^ (1 / 6 : ℝ) * XLK n_ n x.1.1.2 +
        STbootRHS 1 (fun m => XL m n x.1.1.2) (fun m => XLK m n x.1.1.2) (sz.Bctl n (s n)) n_ p
    linarith
  -- (B) the finite maximum over `(σ, a)`
  have hne : ∀ n, (Finset.univ : Finset ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)))).Nonempty := fun n =>
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
  have hT2 := qtBoot_prec_sup (sz := sz) (Q := fun n => STPair s t n)
    (P := fun n => (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n))) hne
    (f := fun n q p ω => ‖zeroModeSet d (sz.L n) (STIdiff p.1)
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) q.1.1 p.1 b ω - STKloop sz n (E n) q.1.1 p.1 b) p.2‖ /
        (sz.Bctl n q.1.1) ^ n_)
    (ζ := fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p) hT1
  -- (C) the data of `lem: newPQ` at `A = ∅`, per `σ`
  choose ℓ k ξc σ' ι A' hk hA hexp using fun σ : Fin n_ → Bool => zeroModeCalc_LK_expansion_empty d n_ σ
  set cF : ∀ σ : Fin n_ → Bool, Fin (ℓ σ) → ℝ := fun σ α =>
    |(ξc σ α : ℝ)| * 2 ^ (k σ α) * ((Real.sqrt (κ / 2))⁻¹) ^ (n_ - k σ α) with hcF
  have hcF0 : ∀ σ α, 0 ≤ cF σ α := fun σ α => by positivity
  -- (D) the lower terms, summed
  have hF : ∀ σ : Fin n_ → Bool, Prec sz (U := STPair s t)
      (fun n q ω => ∑ α : Fin (ℓ σ), cF σ α * STXiLK sz n (E n) q.1.1 (k σ α) ω)
      (fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p) := by
    intro σ
    refine qtBoot_prec_sum hsz Finset.univ hζ0 fun α _ => ?_
    have hkα : 1 ≤ k σ α ∧ k σ α + 1 ≤ n_ := hk σ α
    have h1 := hXLKp (k σ α) hkα.1 (by omega)
    have h2 := StochDomAt.const_mul_left hsize (c := cF σ α) (hcF0 σ α)
      (fun (n : ℕ) (q : STPair s t n) (ω : sz.SeqΩ) => zero_le_one.trans (hXLK (k σ α) n q.1.2)) h1
    refine qtBoot_prec_of_le_right h2 fun n q ω => ?_
    have hu1 : q.1.2 < 1 := q.2.2.2.trans_lt (ht1 n)
    have hb := qtBoot_XLK_le_bootRHS (XL := fun m => XL m n q.1.2) (XLK := fun m => XLK m n q.1.2)
      (B := sz.Bctl n (s n)) (n_ := n_) (p := p) hkα.1 (by omega)
      (fun m => zero_le_one.trans (hXL m n q.1.2)) (fun m => zero_le_one.trans (hXLK m n q.1.2)) (hBs n q).le
    have h0 : 0 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 :=
      mul_nonneg (Real.rpow_nonneg (STBctl_pos sz n hu1).le _) (zero_le_one.trans (hXLK n_ n q.1.2))
    change XLK (k σ α) n q.1.2 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p
    linarith
  have hG := qtBoot_prec_sum hsz (Finset.univ : Finset (Fin n_ → Bool)) hζ0 fun σ _ => hF σ
  -- (E) the pointwise inequality
  refine qtBoot_prec_of_add_le hsz hζ0 hT2 hG fun n q ω => ?_
  have hsq : s n ≤ q.1.1 := q.2.1
  have hvt : q.1.1 ≤ t n := q.2.2.1.trans q.2.2.2
  have hv0 : 0 ≤ q.1.1 := (hs n).trans hsq
  have hv1 : q.1.1 < 1 := hvt.trans_lt (ht1 n)
  have hBv : 0 < sz.Bctl n q.1.1 := STBctl_pos sz n hv1
  have hEn : |E n| ≤ 2 - κ / 2 := (hE n).le
  have hE2 : |E n| < 2 := by linarith [hE n]
  set ξ₁ : ℝ := (Finset.univ : Finset ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)))).sup' (hne n)
    (fun p => ‖zeroModeSet d (sz.L n) (STIdiff p.1)
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) q.1.1 p.1 b ω - STKloop sz n (E n) q.1.1 p.1 b) p.2‖ /
        (sz.Bctl n q.1.1) ^ n_) with hξ₁
  set G : ℝ := ∑ σ : Fin n_ → Bool, ∑ α : Fin (ℓ σ), cF σ α * STXiLK sz n (E n) q.1.1 (k σ α) ω with hGdef
  have hXi0 : ∀ σ α, 0 ≤ cF σ α * STXiLK sz n (E n) q.1.1 (k σ α) ω := by
    intro σ α
    refine mul_nonneg (hcF0 σ α) ?_
    unfold STXiLK
    have : 0 ≤ sz.STmaxLK n (E n) q.1.1 (k σ α) ω / (sz.Bctl n q.1.1) ^ (k σ α) :=
      div_nonneg (Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))))
        (norm_nonneg _)) (pow_nonneg hBv.le _)
    linarith
  -- per `(σ, a)`: `‖(𝓛-𝒦)_{σ,a}‖ / B^{n_} ≤ ξ₁ + G`
  have hpt : ∀ p : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)),
      ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω - STKloop sz n (E n) q.1.1 p.1 p.2‖ / (sz.Bctl n q.1.1) ^ n_ ≤
        ξ₁ + G := by
    rintro ⟨σ, a⟩
    have hex := hexp σ sz n (E n) q.1.1 hE2 hv0 hv1 ω a
    have h1 : ‖sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) σ a‖ ≤
        ‖zeroModeSet d (sz.L n) (STIdiff σ)
            (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) σ a') a‖ +
          ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT (E n) q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) (σ' σ α) a') (a ∘ ι σ α)‖ := by
      rw [hex]
      exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    have hfirst : ‖zeroModeSet d (sz.L n) (STIdiff σ)
          (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) σ a') a‖ / (sz.Bctl n q.1.1) ^ n_ ≤ ξ₁ :=
      Finset.le_sup' (fun p : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)) =>
        ‖zeroModeSet d (sz.L n) (STIdiff p.1)
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) q.1.1 p.1 b ω - STKloop sz n (E n) q.1.1 p.1 b) p.2‖ /
        (sz.Bctl n q.1.1) ^ n_) (Finset.mem_univ (σ, a))
    have hlower : ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT (E n) q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) (σ' σ α) a') (a ∘ ι σ α)‖ /
          (sz.Bctl n q.1.1) ^ n_ ≤ G := by
      calc _ ≤ ∑ α : Fin (ℓ σ), cF σ α * STXiLK sz n (E n) q.1.1 (k σ α) ω := by
            refine Finset.sum_le_sum fun α _ => ?_
            exact qtBoot_term_le sz n hκ hEn hv1 ω (hk σ α).2 (ξc σ α) (σ' σ α) (ι σ α) (A' σ α) a
        _ ≤ G := Finset.single_le_sum (f := fun σ : Fin n_ → Bool =>
            ∑ α : Fin (ℓ σ), cF σ α * STXiLK sz n (E n) q.1.1 (k σ α) ω)
          (fun σ _ => Finset.sum_nonneg fun α _ => hXi0 σ α) (Finset.mem_univ σ)
    calc ‖Lloop sz n (E n) q.1.1 σ a ω - STKloop sz n (E n) q.1.1 σ a‖ / (sz.Bctl n q.1.1) ^ n_
        = ‖sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) σ a‖ / (sz.Bctl n q.1.1) ^ n_ := rfl
      _ ≤ (‖zeroModeSet d (sz.L n) (STIdiff σ)
            (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) σ a') a‖ +
          ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT (E n) q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) (σ' σ α) a') (a ∘ ι σ α)‖) /
          (sz.Bctl n q.1.1) ^ n_ := div_le_div_of_nonneg_right h1 (pow_nonneg hBv.le _)
      _ = ‖zeroModeSet d (sz.L n) (STIdiff σ)
            (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) σ a') a‖ / (sz.Bctl n q.1.1) ^ n_ +
          ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT (E n) q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => sz.STLKM n (E n) q.1.1 (sz.seqHflow n q.1.1 ω) (σ' σ α) a') (a ∘ ι σ α)‖ /
          (sz.Bctl n q.1.1) ^ n_ := by rw [add_div, Finset.sum_div]
      _ ≤ ξ₁ + G := add_le_add hfirst hlower
  -- the maximum over `(σ, a)` and `Ξ̂ = 1 + max / B^{n_}`
  have hmax : sz.STmaxLK n (E n) q.1.1 n_ ω ≤ (sz.Bctl n q.1.1) ^ n_ * (ξ₁ + G) := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have := hpt p
    rw [div_le_iff₀ (pow_pos hBv _)] at this
    linarith
  have hXi : sz.STXiLK n (E n) q.1.1 n_ ω ≤ 1 + (ξ₁ + G) := by
    unfold STXiLK
    have : sz.STmaxLK n (E n) q.1.1 n_ ω / (sz.Bctl n q.1.1) ^ n_ ≤ ξ₁ + G :=
      (div_le_iff₀ (pow_pos hBv _)).2 (by linarith)
    linarith
  have := hζ1 n q
  change sz.STXiLK n (E n) q.1.1 n_ ω ≤ ξ₁ + G +
    ((sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
  linarith

end Combine

/-- **The case-(ii) round** (`lem:STOeq_Qt_nonzero` `3_5:1561-1572`, proof `3_5:1889-1933`): at every flow setting of
`STIngR d STCaseII` the round pin `STXiRound'` holds, with the constant `𝔠_d` of `stOeqNZ''_holds d` (T2299).  The
combination is `qtBoot_round_of_NZ`: `lem: newPQ` at `A = ∅` on the uniform projected endpoint `STNZConcl''`, the lower terms
`k_α ∈ [1, n_-1]` from the hypotheses (paper-delta candidate `T2304b`).  `STCaseII` enters only through
`stOeqNZ''_holds`. -/
theorem stXiRoundNZ_holds : ∀ d : ℕ, STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t) := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := stOeqNZ''_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hNZ := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  obtain ⟨hA, hE', ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  exact qtBoot_round_of_NZ sz hA.2.2.1 hκ hE' hs ht1 hNZ

/-! ## 6. The target -/

/-- **`stOeqQtNZ'_holds`: `lem:STOeq_Qt_nonzero`, R2*, for every `d`** (`3_5:1561-1572`; DECISIONS §80 (1), §91 (2), §105 (1);
paper-delta candidates `T2304a`, `T2304b`): `STOeqQtNZ' d` is `STIngR d STCaseII (fun … => STXiBoot' …)`; the round is
`stXiRoundNZ_holds d` and the self-absorbing current-length term is removed by the deterministic bootstrap
`stXiBootR_of_round`.  No hypothesis. -/
theorem stOeqQtNZ'_holds : ∀ d : ℕ, STOeqQtNZ' d := fun d => stXiBootR_of_round d STCaseII (stXiRoundNZ_holds d)

/-! ## 7. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.QtNonzeroBootInst`.  Data: the case-(ii) data of the merged `inst_OeqQtNZ` (`Step34Pins.lean:1006`) and of
`QtNonzeroFlowLiftInst` (`QtNonzeroFlowLift.lean:791`): `szB` (`d = 3`, `L = 4`, `W = n + 4`, `ilambda = 1`,
`N = (4(n+4))^3 ≥ 4096`), the flow `zB` (`z_n = 1/2 + i/64`, `flow_zB` at `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `s ≡ 15/16`,
`t ≡ 31/32` (`szB_flow_ht`, `szB_caseII`: `1 - s = ilambda²/L² = 1/16`; `conStInd_const`), `C_d = 1`.  `STKbound`, `STKward` are
theorems of the flow; what stays a hypothesis of an example is a stochastic premise that is another gate's pin
(`STLK s`, `STStep2Concl`, the pair hypotheses `Ξ̂ ≺ 1`, the round `STXiRound'` at the case-(i) data). -/

namespace QtNonzeroBootInst

open RBM.Gauss.Step34Inst

/-- **(1) `stOeqQtNZ'_holds` at the data**: the constant `𝔠_d ∈ (0, 1/100]`, then the stochastic premises of `STIngR`
(`STKbound`, `STKward`, `STLK`, `STStep2Concl`), then the conclusion `STXiBoot'`; every deterministic hypothesis
(`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the regime `STCaseII`, `(con_st_ind)`, `C_d > 0`) is discharged by `inst_ing`. -/
theorem inst_OeqQtNZ' :
    InstIngConcl (fun sz E s t => STXiBoot' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STXiBoot' sz E s t) (stOeqQtNZ'_holds 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- **(2) `stXiRoundNZ_holds` at the data**: the same for the round pin `STXiRound'`. -/
theorem inst_RoundNZ :
    InstIngConcl (fun sz E s t => STXiRound' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STXiRound' sz E s t) (stXiRoundNZ_holds 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- **(1') the target applied** at `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`: `STKbound`, `STKward` come from the flow, the
stochastic premises `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` (lengths `m ≤ 4`, `m = 5`, `m = 4`;
`m + 1 ≤ 3`) stay hypotheses; the conclusion is `Ξ̂^{(𝓛-𝒦)}_{v,3} ≺ STbootRHS 1 1 1 B_s 3 1` over the pairs `(v, u)`,
`15/16 ≤ v ≤ u ≤ 31/32`, `B_s = W^{-3}B_{15/16,0}`. -/
example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
    (hStep2 : STStep2Concl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiL szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m + 1 ≤ 3 →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ))) :
    Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
      (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 3 ω)
      (fun n q _ => STbootRHS 1 (fun _ => 1) (fun _ => 1) (szB.Bctl n (15 / 16)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqQtNZ'
  exact hC (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(2') the round applied** at the same data: the pair hypotheses now include the current length `m = 3`; the
conclusion has the extra summand `B_u^{1/6} · 1`. -/
example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
    (hStep2 : STStep2Concl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiL szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ))) :
    Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
      (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 3 ω)
      (fun n q _ => (szB.Bctl n q.1.2) ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 1 (fun _ => 1) (fun _ => 1) (szB.Bctl n (15 / 16)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_RoundNZ
  exact hC (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(3) `stBoot_rounds` at `szB`** (`U = Unit`, `ξ ≡ 1`, `R ≡ 1`, `π ≡ 0`, `c = 1`, `C₀ = 0`): every hypothesis is
discharged (`SizeTendsto`, the crude start `1 ≤ N^0`, the round `1 ≤ N^{-1} Y + 1` for `Y ≥ 1`). -/
example : Prec szB (U := fun _ => Unit) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  stBoot_rounds szB szB_tendsto (U := fun _ => Unit) (fun _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ))
    (fun _ _ => (1 : ℝ)) 1 0 one_pos le_rfl (fun _ _ => le_rfl)
    (Sizes.prec_of_le szB (fun n _ _ => by positivity) (fun n _ _ => by simp))
    (fun Y hY _ => Sizes.prec_of_le szB
      (fun n _ _ => by have := hY n 0; have : (0 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by positivity
                       nlinarith)
      (fun n _ _ => by have := hY n 0; have : (0 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by positivity
                       nlinarith))

/-- **(3') the same with the constants of the contraction table** (`c = 1/360`, `C₀ = 2 n_ + 1 = 5`, `R ≡ 2`, `ξ ≡ 1`): the
number of rounds is `⌈5 · 360⌉ + 1 = 1801`. -/
example : Prec szB (U := fun _ => Unit) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => (2 : ℝ)) :=
  stBoot_rounds szB szB_tendsto (U := fun _ => Unit) (fun _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ))
    (fun _ _ => (2 : ℝ)) (1 / 360) 5 (by norm_num) (by norm_num) (fun _ _ => by norm_num)
    (Sizes.prec_of_le szB (fun n _ _ => by positivity)
      (fun n _ _ => Real.one_le_rpow (by exact_mod_cast szB.one_le_size n) (by norm_num)))
    (fun Y hY _ => Sizes.prec_of_le szB
      (fun n _ _ => by have := hY n 0; have : (0 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 / 360 : ℝ)) := by positivity
                       nlinarith)
      (fun n _ _ => by have := hY n 0; have : (0 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 / 360 : ℝ)) := by positivity
                       nlinarith))

/-- A random bounded observable of the model `szB` at size `n`: `|sin|` of the `(0,0)` real coordinate (as
`StochDomAtInst.obs`, `Defs/StochDomAt.lean:745`, at `szB`). -/
private def obsB (n : ℕ) (ω : szB.SeqΩ) : ℝ :=
  |Real.sin (ω ⟨n, ((0 : Idx 3 (szB.L n) (szB.W n)), (0 : Idx 3 (szB.L n) (szB.W n)), true)⟩)|

private theorem obsB_nonneg (n : ℕ) (ω : szB.SeqΩ) : 0 ≤ obsB n ω := abs_nonneg _

private theorem obsB_le_one (n : ℕ) (ω : szB.SeqΩ) : obsB n ω ≤ 1 := by
  unfold obsB; exact Real.abs_sin_le_one _

/-- `obsB n` is not constant: `0` at `ω = 0` and `1` at `ω ≡ π/2` (nondegenerate randomness). -/
private theorem obsB_nonconst (n : ℕ) : ∃ ω ω' : szB.SeqΩ, obsB n ω ≠ obsB n ω' := by
  refine ⟨fun _ => 0, fun _ => Real.pi / 2, ?_⟩
  simp [obsB]

/-- **(3'') `stBoot_rounds` with a genuinely random `ξ = 1 + obsB`** (nonconstant, `1 ≤ ξ ≤ 2`), `R ≡ 3`,
`c = 1/360`, `C₀ = 5`: crude start `ξ ≤ 2 ≤ N^5` (`N ≥ 4096`), round `ξ ≤ 2 ≤ N^{-c} Y + 3`. -/
example : Prec szB (U := fun _ => Unit) (fun n _ ω => 1 + obsB n ω) (fun _ _ _ => (3 : ℝ)) :=
  stBoot_rounds szB szB_tendsto (U := fun _ => Unit) (fun _ _ => (0 : ℝ)) (fun n _ ω => 1 + obsB n ω)
    (fun _ _ => (3 : ℝ)) (1 / 360) 5 (by norm_num) (by norm_num) (fun _ _ => by norm_num)
    (Sizes.prec_of_le szB (fun n _ _ => by positivity) (fun n _ ω => by
      have h2 : (2 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) := by exact_mod_cast (szB_size_ge n).trans' (by norm_num)
      have h5 : ((szB.size n : ℕ) : ℝ) ^ (1 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      rw [Real.rpow_one] at h5
      linarith [obsB_le_one n ω]))
    (fun Y hY _ => Sizes.prec_of_le szB (fun n _ _ => by
        have := hY n 0
        have : (0 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 / 360 : ℝ)) := by positivity
        nlinarith)
      (fun n _ ω => by
        have := hY n 0
        have : (0 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 / 360 : ℝ)) := by positivity
        nlinarith [obsB_le_one n ω]))

/-- **(4) `qtBoot_contraction` at the data**, unfolded at `n ≥ n₀` (`szB`, `t ≡ 31/32`, `𝔠 = 1/6`, `𝔡 = ε = 1/10`,
`c = min(2 𝔡 𝔠, ε/2)/12 = 1/360`): all deterministic hypotheses are discharged (`Admissible 1/6 1/10`, `t < 1`,
`RangeCond (ε/2)`); the conclusion is `B_u ≤ 1` and `B_u^{1/6} ≤ N^{-1/360}` for every `u ∈ [0, 31/32]`. -/
example : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ u : ℝ, 0 ≤ u → u ≤ 31 / 32 →
    szB.Bctl n u ≤ 1 ∧ (szB.Bctl n u) ^ (1 / 6 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 / 360 : ℝ)) := by
  obtain ⟨hA, -, ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow szB (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_zB (t := fun _ : ℕ => (31 / 32 : ℝ)) (szB_flow_ht (by norm_num))
  have h := qtBoot_contraction szB hA (by norm_num : (0 : ℝ) < 1 / 10) ht1 hrange
  have hc : qtBoot_c (1 / 6) (1 / 10) (1 / 10) = 1 / 360 := by unfold qtBoot_c; norm_num
  rw [hc] at h
  exact eventually_atTop.1 h

/-- **(4') `qtBoot_crude` at the data** (`n_ = 3`: `Ξ̂^{(𝓛-𝒦)}_{v,3} ≺ N^7` over the pairs): the deterministic hypotheses are
discharged; no stochastic premise is needed (the bound is deterministic). -/
example : Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
    (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 3 ω) (fun n _ _ => ((szB.size n : ℕ) : ℝ) ^ (((2 * 3 + 1 : ℕ) : ℝ))) :=
  qtBoot_crude (by norm_num) szB (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (by norm_num)

/-- **(5) `stXiBoot'_of_round` at the data** `(szB, zB, 15/16, 31/32)`, the round as hypothesis. -/
example (hround : STXiRound' szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    STXiBoot' szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  stXiBoot'_of_round (d := 3) (by norm_num) (1 / 10) (1 / 10) (1 / 6) (1 / 10) (by norm_num) (by norm_num)
    szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) hround

/-- **(6) the consumer shapes**: `stXiBootR_of_round` at the two regimes (case (i) is the shape S3-18b2 instantiates). -/
example : ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t) → STOeqQt' d :=
  fun d h => stXiBootR_of_round d STCaseI h

example : ∀ d : ℕ, STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t) → STOeqQtNZ' d :=
  fun d h => stXiBootR_of_round d STCaseII h

/-- **(7) the target**: `stOeqQtNZ'_holds` has exactly the type `∀ d : ℕ, STOeqQtNZ' d`, and at `d = 3` it is the
ingredient form of `STXiBoot'`. -/
example : ∀ d : ℕ, STOeqQtNZ' d := @stOeqQtNZ'_holds

example : STOeqQtNZ' 3 := stOeqQtNZ'_holds 3

example : STOeqQtNZ' 3 = STIngR 3 STCaseII (fun sz E s t => STXiBoot' sz E s t) := rfl

/-- **(6')** the regime-generic bootstrap applied to the proved case-(ii) round: the term of `stOeqQtNZ'_holds 3`. -/
example : STIngR 3 STCaseII (fun sz E s t => STXiBoot' sz E s t) :=
  stXiBootR_of_round 3 STCaseII (stXiRoundNZ_holds 3)

end QtNonzeroBootInst

end RBM.Ind

end

#print axioms RBM.Gauss.Sizes.STXiRound'
#print axioms RBM.Ind.stBoot_rounds
#print axioms RBM.Ind.stXiBoot'_of_round
#print axioms RBM.Ind.stXiBootR_of_round
#print axioms RBM.Ind.stXiRoundNZ_holds
#print axioms RBM.Ind.stOeqQtNZ'_holds
#print axioms RBM.Ind.QtNonzeroBootInst.inst_OeqQtNZ'
#print axioms RBM.Ind.QtNonzeroBootInst.inst_RoundNZ
