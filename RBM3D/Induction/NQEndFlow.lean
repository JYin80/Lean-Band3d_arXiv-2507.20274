/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQEndLin
import RBM3D.Induction.Step34PinsP
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.NQLin
import RBM3D.Induction.Step2Events
import RBM3D.Green.Pins

/-!
# The non-alternating endpoint at the flow, per time (`d ≥ 3`): the R2* pins, `stOeqNQPT''_holds`

Ticket T2246 (S3-12c1, stochastic layer ST-3, third of four after the DECISIONS §80 split;
S3-12a = T2186 `Induction/Step34PinsP` + `Induction/NQLin`,
S3-12b = T2199 `Induction/NQEndLin`; S3-12c2 lifts the per-time pin to `STOeqNQ''`).
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`,
`lem:STOeq_NQ` (`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148`, proof `3_5:1152-1190`),
`(am;asoi222)` `3_5:1366`, `lem:iterations` `3_5:1407-1417`.

## R2* (DECISIONS §80 (1); supervisor `docs/supervisor/2026-10-05-1955.md` A1)

In the first summand of `STbootRHS` (the only summand containing `B`) the endpoint value `B_u`
is replaced by the window start `B_s`.  Every primed pin is the merged text with the argument
`sz.Bctl n u` of `STbootRHS` replaced by `sz.Bctl n (s n)`; the separate term
`B_u^{1/6} · XLK n_ n u`, the normalisation `/ B_u^{n_}` and all hypotheses are unchanged
(paper-delta candidate `T2246a`).  The consumers use `B` in this summand only through a time-uniform
lower bound, available at `w = s`.

## What is here

* §1 the pins `STNQConcl''`, `STOeqNQ''`, `STXiBoot'`, `STOeqQt'`, `STOeqQtNZ'`, `STIterR'`,
  `STIterations'`, `STIterationsII'`, the per-time `STNQConclPT''`, `STOeqNQPT''` (namespace
  `RBM.Gauss.Sizes`), and the vocabulary `RBM.Ind.nqFlowLam`, `RBM.Ind.nqFlowPhiC` (check file
  `docs/tickets/checks/T2246-check.lean`, section 2, verbatim);
* §2 the trivial bridges `STNQConcl' → STNQConcl''` (private), `STOeqNQ' → STOeqNQ''`,
  `STXiBoot → STXiBoot'`, `STOeqQt → STOeqQt'`, `STOeqQtNZ → STOeqQtNZ'` (`B_s ≤ B_u`, and the
  exponent of `B` in `STbootRHS` is negative);
* §3 window and setting facts (private): `(con_st_ind)` in the exponent, `STStep2Concl` and the pair
  hypotheses restricted from `[s, t]` to `[s, v]` (paper-delta candidate `T2246b`);
* §4 the levels (private): the crude level `Φc` of `GoodSetN` as the sum of the controls
  (paper-delta candidate `T2246c`), the level `Λ_s = max 1 (nqFlowLam X B_s k p)`, `hQ`, the
  degree-1 inequality `Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃ ≤ ζ`;
* §5 the per-section endpoint `nqFlow_core`, `nqFlow_section` (private; the shape of RBM2D
  `gridEnd_to_flow`, `RBM2D/Induction/StoppedEndDefs.lean:280-470` at `c9a24cf`): `nqGridEndLinN` on
  the window `[s, v]`, the good events `gridGoodN_holds` (re-instantiated on `[s, v]`) and
  `nqLinGood_holds`, the initial event from `STLK s`;
* §6 **`stOeqNQPT''_holds`**, the per-time pin;
* §7 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.NQEndFlowInst`).

Every helper that the ticket does not pin is `private` or prefixed `nqFlow_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The pins (R2*, DECISIONS §80 (1)) and the vocabulary -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **`lem:STOeq_NQ`, R2*** (`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148`; DECISIONS §80 (1), supervisor
`2026-10-05-1955` A1; paper-delta candidate `T2246a`): the merged `STNQConcl'` (`Step34PinsP.lean:53`) with the first
summand of `STbootRHS` at the window start `B_s = sz.Bctl n (s n)` in place of `B_u`. -/
def STNQConcl'' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **`(am;asoi222)`, R2*** (`3_5:1366`; DECISIONS §80 (1); paper-delta candidate `T2246a`): the merged `STXiBoot`
(`Step34Pins.lean:414`) with the first summand of `STbootRHS` at `B_s = sz.Bctl n (s n)` in place of `B_u`. -/
def STXiBoot' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- **Per-time R2* conclusion** (the union over `u` outside `P`, DECISIONS §7; target of `stOeqNQPT''_holds`):
`STNQConcl''` with `Prec` ↦ `PrecPT` in the conclusion. -/
def STNQConclPT'' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

end Pins

/-- `lem:STOeq_NQ`, R2* (case (i)): `STOeqNQ'` over the primed conclusion (`3_5:1136`; DECISIONS §80 (1)). -/
def STOeqNQ'' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConcl'' sz E s t)

/-- `lem:STOeq_Qt`, R2* (`3_5:1362`): case (i), `STOeqQt` over `STXiBoot'` (DECISIONS §80 (1)). -/
def STOeqQt' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STXiBoot' sz E s t)

/-- `lem:STOeq_Qt_nonzero`, R2* (`3_5:1561`): case (ii), `STOeqQtNZ` over `STXiBoot'` (DECISIONS §80 (1)). -/
def STOeqQtNZ' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STXiBoot' sz E s t)

/-- **`lem:iterations`, R2*** (`3_5:1407-1417`, `3_5:1575-1595`; DECISIONS §80 (1)): `STIterR` with the hypothesis
`STXiBoot'`.  Proof: S3-24b (copy of `iterationsA_step` with `hlow` at `w = s`; DECISIONS §80 (2)). -/
def STIterR' (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd →
          STXiBoot' sz (STflowE z) s t →
          ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
            (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz (STflowE z) s t (Aof sz s) r k) →
            (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz (STflowE z) s t (Aof sz s) r (k - 1)) →
            STIterHyp sz (STflowE z) s t (Aof sz s) n_ k

/-- `lem:iterations`, case (i), R2* (DECISIONS §80 (1)). -/
def STIterations' (d : ℕ) : Prop := STIterR' d STRegIterI (fun sz _ n => STAI sz n)

/-- The case-(ii) analogue, R2* (DECISIONS §80 (1)). -/
def STIterationsII' (d : ℕ) : Prop := STIterR' d STCaseII (fun sz s n => STAII sz s n)

/-- The per-time pin in the ingredient shape (case (i)): the conclusion of `stOeqNQPT''_holds`. -/
def STOeqNQPT'' (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConclPT'' sz E s t)

end RBM.Gauss.Sizes

namespace RBM.Ind

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- **The level `Λ` of `GoodSetN`'s (D4) clause** (vocabulary): `Λ = XL(2k−1) (XL(4p)/B)^{1/(2p)}`; at `B = B_s`,
`Λ^{1/2}` is the first summand of `STbootRHS … B_s k p` (R2*: exactly, no loss).  The endpoint uses
`max 1 (nqFlowLam X B_s k p)`. -/
noncomputable def nqFlowLam (XL : ℕ → ℝ) (B : ℝ) (k p : ℕ) : ℝ :=
  XL (2 * k - 1) * (XL (4 * p) / B) ^ (1 / (2 * (p : ℝ)))

/-- **The crude level `Φc` of `GoodSetN`** (vocabulary): the sum of the controls of lengths `1 … k+1` at the window
end, so that `hX`, `hY` of `GridGoodNConcl` follow from the pair hypotheses (`nqGridEndLinN` quantifies over every
`Φc`, it enters only the exit time). -/
noncomputable def nqFlowPhiC (X Y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (k + 1), (X m + Y m)

end RBM.Ind

/-! ## 2. The merged pins imply the primed ones (`B_s ≤ B_u`; the exponent of `B` in `STbootRHS` is negative) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Bridges

variable {d : ℕ}

/-- `STbootRHS` is antitone in `B > 0` (only its first summand contains `B`, with the exponent
`-1/(4p) ≤ 0`): `STbootRHS lo XL XLK B n_ p ≤ STbootRHS lo XL XLK B' n_ p` for `0 < B' ≤ B`, `XL ≥ 0`. -/
private theorem nqFlow_bootRHS_anti {lo : ℕ} {XL XLK : ℕ → ℝ} {B B' : ℝ} {n_ p : ℕ} (hB' : 0 < B')
    (hle : B' ≤ B) (hXL : ∀ m, 0 ≤ XL m) :
    STbootRHS lo XL XLK B n_ p ≤ STbootRHS lo XL XLK B' n_ p := by
  unfold STbootRHS
  have hexp : -(1 : ℝ) / (4 * (p : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have h1 : B ^ (-(1 : ℝ) / (4 * (p : ℝ))) ≤ B' ^ (-(1 : ℝ) / (4 * (p : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hB' hle hexp
  have h2 : B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * n_ - 1) ^ (1 / 2 : ℝ) *
        XL (4 * p) ^ (1 / (4 * (p : ℝ))) ≤
      B' ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * n_ - 1) ^ (1 / 2 : ℝ) *
        XL (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hXL _) _))
      (Real.rpow_nonneg (hXL _) _)
  linarith

/-- A pointwise larger right side keeps `≺` (the failure event only shrinks; `N^τ ≥ 0`). -/
private theorem nqFlow_prec_of_le_right {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- **`STNQConcl'` implies `STNQConcl''`** (`T2246_stNQConcl''_of_stNQConcl'`): the right side of the primed
conclusion is `B_u^{1/6} XLK + STbootRHS 2 … B_u`, that of `STNQConcl''` has `B_s ≤ B_u` (`STBctl_mono`, `u ≤ t_n < 1`)
in the first summand of `STbootRHS`, which is larger (`nqFlow_bootRHS_anti`).  Private: a public theorem with
`STNQConcl'` in a binder would make the registry scan (`Test/Axioms.lean`) report it as an unregistered premise. -/
private theorem stNQConcl''_of_stNQConcl' (sz : Sizes d) (E s t : ℕ → ℝ) (ht1 : ∀ n, t n < 1)
    (h : STNQConcl' sz E s t) : STNQConcl'' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  refine nqFlow_prec_of_le_right (h n_ p hn hp XL XLK hXL hXLK hXLp hXLKp) fun n q ω => ?_
  have hu1 : ((q.1 : ℝ)) < 1 := (q.1.2.2).trans_lt (ht1 n)
  have hs1 : s n < 1 := lt_of_le_of_lt q.1.2.1 hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBsu : sz.Bctl n (s n) ≤ sz.Bctl n (q.1 : ℝ) := STBctl_mono sz n q.1.2.1 hu1
  have hb := nqFlow_bootRHS_anti (lo := 2) (XL := fun m => XL m n (q.1 : ℝ))
    (XLK := fun m => XLK m n (q.1 : ℝ)) (n_ := n_) (p := p) hBs hBsu
    (fun m => zero_le_one.trans (hXL _ _ _))
  change (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
      STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p ≤
    (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
      STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p
  linarith

/-- **`STXiBoot` implies `STXiBoot'`** (`T2246_stXiBoot'_of_stXiBoot`): `B_s ≤ B_u` for `s_n ≤ u ≤ t_n < 1`. -/
theorem stXiBoot'_of_stXiBoot {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (ht1 : ∀ n, t n < 1)
    (h : STXiBoot sz E s t) : STXiBoot' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  refine nqFlow_prec_of_le_right (h n_ p hn hp XL XLK hXL hXLK hXLp hXLKp) fun n q ω => ?_
  have hsu : s n ≤ q.1.2 := q.2.1.trans q.2.2.1
  have hu1 : q.1.2 < 1 := q.2.2.2.trans_lt (ht1 n)
  have hs1 : s n < 1 := lt_of_le_of_lt hsu hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hs1
  have hBsu : sz.Bctl n (s n) ≤ sz.Bctl n q.1.2 := STBctl_mono sz n hsu hu1
  exact nqFlow_bootRHS_anti (lo := 1) (XL := fun m => XL m n q.1.2) (XLK := fun m => XLK m n q.1.2)
    (n_ := n_) (p := p) hBs hBsu (fun m => zero_le_one.trans (hXL _ _ _))

/-- A bridge between two conclusions of an ingredient pin (`STIngR`) that needs only `t_n < 1`: unfold `STIngR`, keep
`𝔠_d`, and get `t_n < 1` from `t_n ≤ lemT z_n < 1` (`lemT_lt_one`; the imaginary part of `z_n` is positive by the flow
condition), as `stOeqNQ'_of_stOeqNQ` (`Step34PinsP.lean:156`). -/
private theorem nqFlow_ingR_mono (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (C C' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hCC : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, t n < 1) → C sz E s t → C' sz E s t)
    (h : STIngR d R C) : STIngR d R C' := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hold := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  exact hCC sz (STflowE z) s t ht1 hold

/-- **`lem:STOeq_NQ`, primed, implies its R2* form** (`T2246_stOeqNQ''_of_stOeqNQ'`). -/
theorem stOeqNQ''_of_stOeqNQ' : ∀ d : ℕ, STOeqNQ' d → STOeqNQ'' d := fun d h =>
  nqFlow_ingR_mono d STCaseI (fun sz E s t => STNQConcl' sz E s t) (fun sz E s t => STNQConcl'' sz E s t)
    (fun sz E s t ht1 => stNQConcl''_of_stNQConcl' sz E s t ht1) h

/-- **`lem:STOeq_Qt` implies its R2* form** (`T2246_stOeqQt'_of_stOeqQt`). -/
theorem stOeqQt'_of_stOeqQt : ∀ d : ℕ, STOeqQt d → STOeqQt' d := fun d h =>
  nqFlow_ingR_mono d STCaseI (fun sz E s t => STXiBoot sz E s t) (fun sz E s t => STXiBoot' sz E s t)
    (fun sz E s t ht1 => stXiBoot'_of_stXiBoot sz E s t ht1) h

/-- **`lem:STOeq_Qt_nonzero` implies its R2* form** (`T2246_stOeqQtNZ'_of_stOeqQtNZ`). -/
theorem stOeqQtNZ'_of_stOeqQtNZ : ∀ d : ℕ, STOeqQtNZ d → STOeqQtNZ' d := fun d h =>
  nqFlow_ingR_mono d STCaseII (fun sz E s t => STXiBoot sz E s t) (fun sz E s t => STXiBoot' sz E s t)
    (fun sz E s t ht1 => stXiBoot'_of_stXiBoot sz E s t ht1) h

/-- The statement pinned for the private implication (`T2246_stNQConcl''_of_stNQConcl'`, check file section 3):
the theorem above has exactly this type. -/
example : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, t n < 1) →
    STNQConcl' sz E s t → STNQConcl'' sz E s t := @stNQConcl''_of_stNQConcl'

end Bridges

/-! ## 3. Window and setting facts -/

section Window

variable {d : ℕ}

/-- `(con_st_ind)` is monotone in the exponent: it forces `B_t < 1` (`B_t^a ≥ 1` if `B_t ≥ 1`, against the
ratio `< 1`), and `B^b ≤ B^a` for `B ≤ 1`, `a ≤ b`. -/
private theorem nqFlow_conStInd_exp_mono (sz : Sizes d) {s t : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht1 : ∀ n, t n < 1) (h : sz.STConStInd a s t) : sz.STConStInd b s t := by
  filter_upwards [h] with n hn
  refine ⟨?_, hn.2⟩
  have hBt : 0 < sz.Bctl n (t n) := st_Bctl_pos sz (ht1 n)
  have hlt : sz.Bctl n (t n) < 1 := by
    by_contra hge
    have h1 : (1 : ℝ) ≤ sz.Bctl n (t n) := not_lt.1 hge
    have h2 : (1 : ℝ) ≤ (sz.Bctl n (t n)) ^ a := Real.one_le_rpow h1 ha.le
    linarith [hn.1, hn.2]
  exact (Real.rpow_le_rpow_of_exponent_ge hBt hlt.le hab).trans hn.1

/-- The three parts of `STStep2Concl` restrict from `[s,t]` to `[s,v]`, `v ≤ t` (restriction of the parameter set
along `TimeIcc s v n ⊆ TimeIcc s t n`; the right side of `STGdecayW` depends on `s` and `u` only). -/
private theorem nqFlow_step2_restrict {sz : Sizes d} {E s t v : ℕ → ℝ} {Cd : ℝ} (hvt : ∀ n, v n ≤ t n)
    (h : STStep2Concl sz E s t Cd) : STStep2Concl sz E s v Cd := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact StochDomAt.precomp_param
      (V := fun n => TimeIcc s v n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) h1
      (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))
  · exact StochDomAt.precomp_param
      (V := fun n => TimeIcc s v n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))) h2
      (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))
  · intro D hD
    exact StochDomAt.precomp_param
      (V := fun n => TimeIcc s v n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (h3 D hD)
      (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))

/-- The pair hypotheses `Ξ̂_{w,m} ≺ Z m n u`, `s_n ≤ w ≤ u ≤ t_n`, restricted to the pairs `(w, v_n)`, `w ∈ [s_n, v_n]`
(`v_n ≤ t_n`): the controls become the numbers `Z m n (v n)` (`StochDomAt.precomp_param`). -/
private theorem nqFlow_restrict_pair {sz : Sizes d} {s t v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n)
    {F : ∀ n, ℝ → sz.SeqΩ → ℝ} {Z : ∀ n, ℝ → ℝ}
    (h : sz.Prec (U := STPair s t) (fun n q ω => F n q.1.1 ω) (fun n q _ => Z n q.1.2)) :
    sz.Prec (U := fun n => TimeIcc s v n) (fun n u ω => F n (u : ℝ) ω) (fun n _ _ => Z n (v n)) :=
  StochDomAt.precomp_param (V := fun n => TimeIcc s v n) h
    (fun n w => (⟨((w : ℝ), v n), w.2.1, w.2.2, hvt n⟩ : STPair s t n))

end Window

end RBM.Gauss.Sizes

/-! ## 4. The levels: `Λ_s`, `Φc`, the degree-1 inequality, `hQ` -/

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

section Levels

variable {d : ℕ}

/-- `Ξ̂^{(𝓛)}_{v,k} ≥ 1` (copy of the private `gridGood_one_le_STXiL`, `GridGoodN.lean:655`). -/
private theorem nqFlow_one_le_STXiL (sz : Sizes d) {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiL sz n E v k ω := by
  unfold STXiL
  have h0 : 0 ≤ STmaxL sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

end Levels

/-- **G1, exactly** (R2*): `(XL(2k−1) (XL(4p)/B)^{1/(2p)})^{1/2}` is the first summand of `STbootRHS … B k p`
(`B > 0`, `p ≥ 1`, `XL ≥ 0`): `nqFlowLam` at `B = B_s` has `Λ^{1/2}` equal to it, with no loss. -/
private theorem nqFlow_lam_sqrt {X : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hp : 1 ≤ p) (hB : 0 < B) (hX : ∀ m, 0 ≤ X m) :
    (nqFlowLam X B k p) ^ ((1 : ℝ) / 2) =
      B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * X (2 * k - 1) ^ (1 / 2 : ℝ) * X (4 * p) ^ (1 / (4 * (p : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : 0 ≤ (X (4 * p) / B) := div_nonneg (hX _) hB.le
  unfold nqFlowLam
  rw [Real.mul_rpow (hX _) (Real.rpow_nonneg hr _), ← Real.rpow_mul hr]
  have hc : 1 / (2 * (p : ℝ)) * ((1 : ℝ) / 2) = 1 / (4 * (p : ℝ)) := by field_simp; norm_num
  rw [hc, Real.div_rpow (hX _) hB.le, show -(1 : ℝ) / (4 * (p : ℝ)) = -(1 / (4 * (p : ℝ))) by ring,
    Real.rpow_neg hB.le]
  have : (1 / 2 : ℝ) = (1 : ℝ) / 2 := by norm_num
  rw [this]
  ring

/-- `1 + Φ₃ ≤ Σ_{m=k-1}^{k+1} XL m` for `k ≥ 2`, `XL ≥ 1` (`Φ₃ = (XL(n₁) XL(n₂))^{1/2}`, `(n₁,n₂) = STn12E k ∈
{(k-1,k+1), (k,k)}`: `√(xy) ≤ x + y`). -/
private theorem nqFlow_phi3_le {X : ℕ → ℝ} {k : ℕ} (hk : 2 ≤ k) (hX : ∀ m, 1 ≤ X m) :
    1 + nqLinPhi3 X k ≤ ∑ m ∈ Finset.Icc (k - 1) (k + 1), X m := by
  have e : Finset.Icc (k - 1) (k + 1) = {k - 1, k, k + 1} := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  have h1 := hX (k - 1)
  have h2 := hX k
  have h3 := hX (k + 1)
  unfold nqLinPhi3 STn12E
  split_ifs with h
  · simp only
    rw [← Real.sqrt_eq_rpow]
    have : Real.sqrt (X (k - 1) * X (k + 1)) ≤ X (k - 1) + X (k + 1) :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    linarith
  · simp only
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul_self (by linarith)]
    linarith

/-- **The degree-1 inequality** (R2*): the final loss `Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃` with
`Λ_s = max 1 (nqFlowLam X B_s k p)` is at most the right side `B^{1/6} XLK k + STbootRHS 2 X Y B_s k p` of the
pin.  `Φ₁` is the sum of the controls `XLK 2 … XLK (k-1)`, `Φ₂` is the third sum of `STbootRHS` plus
`B^{1/6} XLK k`, `1 + Φ₃ ≤ Σ_{m=k-1}^{k+1} XL m` (`nqFlow_phi3_le`), and `(nqFlowLam X B_s k p)^{1/2}` is the first
summand of `STbootRHS` (`nqFlow_lam_sqrt`), so `Λ_s^{1/2} ≤ 1 + ` that summand. -/
private theorem nqFlow_level_le {X Y : ℕ → ℝ} {B Bs : ℝ} {k p : ℕ} (hk : 2 ≤ k) (hp : 1 ≤ p)
    (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m) (hBs : 0 < Bs) :
    (max 1 (nqFlowLam X Bs k p)) ^ ((1 : ℝ) / 2) + nqLinPhi1 Y k + nqLinPhi2 X Y B k (Y k) +
        nqLinPhi3 X k ≤
      B ^ (1 / 6 : ℝ) * Y k + STbootRHS 2 X Y Bs k p := by
  have hX0 : ∀ m, 0 ≤ X m := fun m => zero_le_one.trans (hX m)
  have hphi3 := nqFlow_phi3_le hk hX
  have hlam := nqFlow_lam_sqrt (k := k) hp hBs hX0
  have hfirst : 0 ≤ Bs ^ (-(1 : ℝ) / (4 * (p : ℝ))) * X (2 * k - 1) ^ (1 / 2 : ℝ) *
      X (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hBs.le _) (Real.rpow_nonneg (hX0 _) _))
      (Real.rpow_nonneg (hX0 _) _)
  have hmax : (max 1 (nqFlowLam X Bs k p)) ^ ((1 : ℝ) / 2) ≤
      1 + Bs ^ (-(1 : ℝ) / (4 * (p : ℝ))) * X (2 * k - 1) ^ (1 / 2 : ℝ) *
        X (4 * p) ^ (1 / (4 * (p : ℝ))) := by
    rcases le_total 1 (nqFlowLam X Bs k p) with h | h
    · rw [max_eq_right h, hlam]; linarith
    · rw [max_eq_left h, Real.one_rpow]; linarith
  unfold nqLinPhi1 nqLinPhi2 STbootRHS
  linarith

section Levels2

variable {d : ℕ}

/-- **`hQ` at the level `Λ_s`** (the shape of the private `gridGood_prec_Q_one`, `GridGoodN.lean:1045`, with the controls
`Xa, Xb` in place of `1` and `B_s` as the floor): `Ξ̂_a (Ξ̂_b/B_u)^r ≺ max 1 (Xa (Xb/B_s)^r)` for `0 ≤ r ≤ 1` from
`Ξ̂_a ≺ Xa`, `Ξ̂_b ≺ Xb` uniformly in `u ∈ [s,v]` (`B_{u,0}` is non-decreasing in `u`, `STBctl_mono`). -/
private theorem nqFlow_hQ (sz : Sizes d) (hsz : sz.SizeTendsto) {E s v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n)
    (hv1 : ∀ n, v n < 1) {a b p : ℕ} (hp : 1 ≤ p) {Xa Xb : ℕ → ℝ} (hXa : ∀ n, 0 ≤ Xa n)
    (hXb : ∀ n, 0 ≤ Xb n)
    (ha : Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) a ω)
      (fun n _ _ => Xa n))
    (hb : Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) b ω)
      (fun n _ _ => Xb n)) :
    Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) a ω *
        (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))))) := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) ha hb fun τ hτ =>
    ⟨τ / 2, half_pos hτ, Eventually.of_forall fun n => ?_⟩
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨h1, h2⟩ := hno
  have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (hv1 n)
  have hBu : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz ((hsv n).trans_lt (hv1 n))
  have hBsu : sz.Bctl n (s n) ≤ sz.Bctl n (u : ℝ) := STBctl_mono sz n u.2.1 hu1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hXia := h1 u
  have hXib := h2 u
  have hXb0 : 0 ≤ STXiL sz n (E n) (u : ℝ) b ω := zero_le_one.trans (nqFlow_one_le_STXiL sz b ω hBu)
  have hXa0 : 0 ≤ STXiL sz n (E n) (u : ℝ) a ω := zero_le_one.trans (nqFlow_one_le_STXiL sz a ω hBu)
  set Nh : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hNh
  have hNh1 : 1 ≤ Nh := Real.one_le_rpow hN1 (half_pos hτ).le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
  have hr1 : 1 / (2 * (p : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have e1 : (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      (Nh * Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) :=
    Real.rpow_le_rpow (div_nonneg hXb0 hBu.le) (div_le_div_of_nonneg_right hXib hBu.le) hr0
  have e2 : (Nh * Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) =
      Nh ^ (1 / (2 * (p : ℝ))) * (Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) := by
    rw [mul_div_assoc, Real.mul_rpow (by linarith) (div_nonneg (hXb n) hBu.le)]
  have e3 : (Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) :=
    Real.rpow_le_rpow (div_nonneg (hXb n) hBu.le) (div_le_div_of_nonneg_left (hXb n) hBs hBsu) hr0
  have e4 : Nh ^ (1 / (2 * (p : ℝ))) ≤ Nh :=
    (Real.rpow_le_rpow_of_exponent_le hNh1 hr1).trans_eq (Real.rpow_one _)
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ = Nh * Nh := by
    rw [hNh]; exact (UnifDetDom.rpow_half_mul_rpow_half _ hτ).symm
  have hM : 0 ≤ (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) :=
    Real.rpow_nonneg (div_nonneg (hXb n) hBs.le) _
  have hlam : Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) ≤
      max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := le_max_right _ _
  have hlam0 : 0 ≤ Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) := mul_nonneg (hXa n) hM
  have hmax0 : 0 ≤ max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) :=
    zero_le_one.trans (le_max_left _ _)
  have hstep : STXiL sz n (E n) (u : ℝ) a ω *
      (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      (Nh * Xa n) * (Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := by
    refine mul_le_mul hXia ?_ (Real.rpow_nonneg (div_nonneg hXb0 hBu.le) _)
      (mul_nonneg (by linarith) (hXa n))
    calc (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ)))
        ≤ Nh ^ (1 / (2 * (p : ℝ))) * (Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) :=
          e1.trans e2.le
      _ ≤ Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) :=
          mul_le_mul e4 e3 (Real.rpow_nonneg (div_nonneg (hXb n) hBu.le) _) (by linarith)
  have hfin : (Nh * Xa n) * (Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) ≤
      Nh * Nh * max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := by
    have : (Nh * Xa n) * (Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) =
        Nh * Nh * (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hlam (mul_nonneg (by linarith) (by linarith))
  rw [hsq] at hu
  linarith

/-- The `Φ`-levels are nonnegative (`XL, XLK ≥ 1`, `B ≥ 0`). -/
private theorem nqFlow_phi_nonneg {X Y : ℕ → ℝ} {B : ℝ} {k : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m)
    (hB : 0 ≤ B) :
    0 ≤ nqLinPhi1 Y k ∧ 0 ≤ nqLinPhi2 X Y B k (Y k) ∧ 0 ≤ nqLinPhi3 X k := by
  have hX0 : ∀ m, 0 ≤ X m := fun m => zero_le_one.trans (hX m)
  have hY0 : ∀ m, 0 ≤ Y m := fun m => zero_le_one.trans (hY m)
  refine ⟨Finset.sum_nonneg fun m _ => hY0 m, ?_, Real.rpow_nonneg (mul_nonneg (hX0 _) (hX0 _)) _⟩
  exact add_nonneg (Finset.sum_nonneg fun m _ => mul_nonneg (hY0 _)
    (Real.rpow_nonneg (mul_nonneg (hX0 _) (hX0 _)) _)) (mul_nonneg (Real.rpow_nonneg hB _) (hY0 _))

/-- The crude level `Φc` dominates every control of length `1 … k+1` and is `≥ 1`. -/
private theorem nqFlow_phiC_ge {X Y : ℕ → ℝ} {k m : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m)
    (hm : m ∈ Finset.Icc 1 (k + 1)) : X m ≤ nqFlowPhiC X Y k ∧ Y m ≤ nqFlowPhiC X Y k := by
  have h := Finset.single_le_sum (f := fun m => X m + Y m)
    (fun m _ => add_nonneg (zero_le_one.trans (hX m)) (zero_le_one.trans (hY m))) hm
  have := hX m
  have := hY m
  unfold nqFlowPhiC
  constructor <;> linarith

private theorem nqFlow_phiC_one_le {X Y : ℕ → ℝ} {k : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m) :
    1 ≤ nqFlowPhiC X Y k := by
  have := (nqFlow_phiC_ge (k := k) (m := 1) hX hY (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)).1
  exact (hX 1).trans this

/-- The grid of the endpoint: `K_n = max 1 ⌈N^{C}⌉` (so `N^C ≤ K_n ≤ ⌈N^C⌉`, `K_n ≠ 0`; RBM2D `KC`, `NonAltEnd:1469`;
the merged `NQEndLinInst.KC` is at `sz0`). -/
private def nqFlow_K (sz : Sizes d) (C : ℝ) (n : ℕ) : ℕ := max 1 ⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊

private theorem nqFlow_K_ne_zero (sz : Sizes d) (C : ℝ) (n : ℕ) : nqFlow_K sz C n ≠ 0 := by
  unfold nqFlow_K
  exact Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le one_pos (le_max_left _ _))

private theorem nqFlow_K_low (sz : Sizes d) (C : ℝ) (n : ℕ) :
    ((sz.size n : ℕ) : ℝ) ^ C ≤ (nqFlow_K sz C n : ℝ) := by
  unfold nqFlow_K
  have h : ((sz.size n : ℕ) : ℝ) ^ C ≤ (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) := Nat.le_ceil _
  exact h.trans (by exact_mod_cast le_max_right _ _)

private theorem nqFlow_K_up (sz : Sizes d) (C : ℝ) (n : ℕ) :
    nqFlow_K sz C n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ := by
  unfold nqFlow_K
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  exact max_le (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN _)) le_rfl

/-- `K_n + 1 ≤ N^{C+2}` eventually (`C ≥ 0`, `N ≥ 2`): `K_n ≤ ⌈N^C⌉ < N^C + 1`, `N^{C+2} = N^C N² ≥ 4 N^C ≥ N^C + 3`. -/
private theorem nqFlow_K_card (sz : Sizes d) (hsz : sz.SizeTendsto) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ((nqFlow_K sz C n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (C + 2) := by
  filter_upwards [hsz.eventually_ge_atTop 2] with n hN2
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := Real.one_le_rpow hN1 hC
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := by linarith
  have hceil : (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) < ((sz.size n : ℕ) : ℝ) ^ C + 1 :=
    Nat.ceil_lt_add_one hP0
  have hK : (nqFlow_K sz C n : ℝ) ≤ (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) := by
    exact_mod_cast nqFlow_K_up sz C n
  have hsplit : ((sz.size n : ℕ) : ℝ) ^ (C + 2) = ((sz.size n : ℕ) : ℝ) ^ C * ((sz.size n : ℕ) : ℝ) ^ 2 := by
    rw [Real.rpow_add hN0, Real.rpow_two]
  have h4 : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by nlinarith
  push_cast
  rw [hsplit]
  nlinarith

/-- `4 N^{-(D+2)} ≤ N^{-D}` for `N ≥ 2` (the four failure events of the endpoint). -/
private theorem nqFlow_four_pow_le {N D : ℝ} (hN : 2 ≤ N) : 4 * N ^ (-(D + 2)) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have h : N ^ (-(D + 2)) = N ^ (-D) * (N ^ (2 : ℝ))⁻¹ := by
    rw [show -(D + 2) = -D + -2 by ring, Real.rpow_add hN0]
    congr 1
    exact Real.rpow_neg hN0.le 2
  rw [h]
  have h4 : (4 : ℝ) ≤ N ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
  have hp : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hN2 : 0 < N ^ (2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have : 4 * (N ^ (2 : ℝ))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN2]; exact h4
  nlinarith

end Levels2

/-! ## 5. The per-section endpoint -/

section Endpoint

variable {d : ℕ}

private theorem nqFlow_meas_pathH (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH sz s t K n k) :=
  Measurable.of_eval_matrix _ fun i j => measurable_pathH sz s t K n k i j

private theorem nqFlow_meas_seqHflow (sz : Sizes d) (n : ℕ) (u : ℝ) : Measurable (sz.seqHflow n u) :=
  Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry sz n u i j

/-- `(𝓛 - 𝒦)^{(k)}_{u,σ,a}(H)` is measurable in the matrix `H` (as `gridGood_meas_loopFine`,
`GridGoodN.lean:266`, minus the constant `STKloop`). -/
private theorem nqFlow_meas_STLKM (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      sz.STLKM n E u H σ a :=
  (walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E u) σ a).sub_const _

/-- **The transfer** (`map_pathH_eq`, RBM2D `gridTerminal_transfer`, `StoppedEndDefs.lean:254`): a measurable matrix event
has the same probability on `pathP` at the grid index `j` and on `seqP` at the grid time. -/
private theorem nqFlow_transfer (sz : Sizes d) {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (j : ℕ) (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (hK : K n ≠ 0)
    {S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)} (hS : MeasurableSet S) :
    pathP sz (pathH sz s v K n j ⁻¹' S) = sz.seqP (sz.seqHflow n (gridTime s v K n j) ⁻¹' S) := by
  rw [← Measure.map_apply (nqFlow_meas_pathH sz s v K n j) hS,
    ← Measure.map_apply (nqFlow_meas_seqHflow sz n _) hS, map_pathH_eq sz s v K n j hs0 hsv hK]

/-- The union bound for four events of probability at most `x` each. -/
private theorem nqFlow_union4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S A B C D' : Set Ω} {x y : ℝ}
    (hx : 0 ≤ x) (hA : μ A ≤ ENNReal.ofReal x) (hB : μ B ≤ ENNReal.ofReal x) (hC : μ C ≤ ENNReal.ofReal x)
    (hD : μ D' ≤ ENNReal.ofReal x) (hS : S ⊆ A ∪ B ∪ C ∪ D') (hxy : 4 * x ≤ y) :
    μ S ≤ ENNReal.ofReal y := by
  refine (measure_mono hS).trans ?_
  calc μ (A ∪ B ∪ C ∪ D') ≤ μ (A ∪ B ∪ C) + μ D' := measure_union_le _ _
    _ ≤ (μ (A ∪ B) + μ C) + μ D' := add_le_add_left (measure_union_le _ _) _
    _ ≤ ((μ A + μ B) + μ C) + μ D' := add_le_add_left (add_le_add_left (measure_union_le _ _) _) _
    _ ≤ ((ENNReal.ofReal x + ENNReal.ofReal x) + ENNReal.ofReal x) + ENNReal.ofReal x := by gcongr
    _ = ENNReal.ofReal (x + x + x + x) := by
        rw [ENNReal.ofReal_add (by positivity) hx, ENNReal.ofReal_add (by positivity) hx,
          ENNReal.ofReal_add hx hx]
    _ ≤ ENNReal.ofReal y := ENNReal.ofReal_le_ofReal (by linarith)

/-- **The endpoint at one non-collapsed section** (`s_n < v_n ≤ t_n`; the shape of RBM2D `gridEnd_to_flow`,
`StoppedEndDefs.lean:280-470` at `c9a24cf`, with `nqGridEndLinN` in place of `GridEndConcl`): for deterministic
controls `X m n`, `Y m n ≥ 1` with `Ξ̂^{(𝓛)}_{w,m} ≺ X m` (`STlenL n_ p m`) and `Ξ̂^{(𝓛-𝒦)}_{w,m} ≺ Y m` (`m ≤ n_`)
uniformly in `w ∈ [s_n, v_n]`, the non-alternating `(𝓛-𝒦)^{(n_)}_{v,σ_n,a_n}/B_v^{n_}` is `≺ B_v^{1/6} Y n_ +
STbootRHS 2 X Y B_s n_ p`.  The failure event is inside the union of four events of probability `≤ N^{-(D+2)}`:
the grid walk leaving `GoodSetN` (`hGrid`, the good-event lemma on the window `[s, v]`, at the crude level `Φc` and
the level `Λ_s`) or `GoodLinN` (`hLin`), the initial loops (`STLK s`, `map_pathH_eq` at `j = 0`) and the exceptional
event `Gᶜ` of `nqGridEndLinN` at `ε₀ = τ/2`, `D₁ = D + 2`; outside it, `nqGridEndLinN` bounds the terminal loop by
`N^{τ/2}(Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^{n_} ≤ N^{τ} ζ B_v^{n_}` (`nqFlow_level_le`), transferred to `seqHflow` at
`v_n` by `map_pathH_eq` at `j = K_n` (`gridTime_last`). -/
private theorem nqFlow_core (sz : Sizes d) {E s t v : ℕ → ℝ} (hd : 3 ≤ d) {κ' 𝔠 τR 𝔡 : ℝ} (hκ : 0 < κ')
    (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ') (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hsv : ∀ n, s n < v n) (hvt : ∀ n, v n ≤ t n) (hLK : STLK sz E s) (hGrid : GridGoodNConcl sz E s v)
    (hLin : NQLinConcl sz E s t) {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p) {X Y : ℕ → ℕ → ℝ}
    (hX1 : ∀ m n, 1 ≤ X m n) (hY1 : ∀ m n, 1 ≤ Y m n)
    (hX : ∀ m : ℕ, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => X m n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => Y m n))
    (σ : ∀ n, Fin n_ → Bool) (hσ : ∀ n, ∃ k, σ n k = σ n (finRotate n_ k))
    (a : ∀ n, Fin n_ → Zd d (sz.L n)) :
    StochDomAt sz.seqP sz.size
      (fun n (_ : Unit) ω => ‖Lloop sz n (E n) (v n) (σ n) (a n) ω - STKloop sz n (E n) (v n) (σ n) (a n)‖ /
        (sz.Bctl n (v n)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
        STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) := by
  intro τ hτ D hD
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hBv : ∀ n, 0 < sz.Bctl n (v n) := fun n => st_Bctl_pos sz (hv1 n)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hsv n).le.trans_lt (hv1 n))
  -- the levels
  set Λ : ℕ → ℝ := fun n => max 1 (nqFlowLam (fun m => X m n) (sz.Bctl n (s n)) n_ p) with hΛdef
  set Φ₁ : ℕ → ℝ := fun n => nqLinPhi1 (fun m => Y m n) n_ with hΦ₁def
  set Φ₂ : ℕ → ℝ := fun n =>
    nqLinPhi2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (v n)) n_ (Y n_ n) with hΦ₂def
  set Φ₃ : ℕ → ℝ := fun n => nqLinPhi3 (fun m => X m n) n_ with hΦ₃def
  set Φc : ℕ → ℝ := fun n => nqFlowPhiC (fun m => X m n) (fun m => Y m n) n_ with hΦcdef
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => le_max_left _ _
  have hΛ0 : ∀ n, 0 ≤ Λ n := fun n => zero_le_one.trans (hΛ1 n)
  have hΦ : ∀ n, 0 ≤ Φ₁ n ∧ 0 ≤ Φ₂ n ∧ 0 ≤ Φ₃ n := fun n =>
    nqFlow_phi_nonneg (fun m => hX1 m n) (fun m => hY1 m n) (hBv n).le
  have hΦc1 : ∀ n, 1 ≤ Φc n := fun n => nqFlow_phiC_one_le (fun m => hX1 m n) (fun m => hY1 m n)
  -- the endpoint of the grid walk at `ε₀ = τ/2`, `D₁ = D + 2`
  obtain ⟨ε₁, τ', D', C_K, hε₁, hτ', hD', hCK, hend⟩ := nqGridEndLinN sz κ' 𝔠 τR 𝔡 E s t hd hκ h𝔠 hτR h𝔡
    hsize hband hWO hE hs0 hst ht1 hcase hrange hWt n_ hn Λ Φ₁ Φ₂ Φ₃ hΛ0 (Eventually.of_forall hΛ1)
    (fun n => (hΦ n).1) (fun n => (hΦ n).2.1) (fun n => (hΦ n).2.2) v (fun n => (hsv n).le) hvt
    (τ / 2) (half_pos hτ) (D + 2) (by linarith)
  -- the grid
  set K : ℕ → ℕ := nqFlow_K sz C_K with hKdef
  have hK0 : ∀ n, K n ≠ 0 := nqFlow_K_ne_zero sz C_K
  have hKcard := nqFlow_K_card sz hsize hCK
  have hpin := hend Φc K hK0 (Eventually.of_forall (nqFlow_K_low sz C_K))
    (Eventually.of_forall (nqFlow_K_up sz C_K))
  -- the hypotheses of the good-event lemma on `[s, v]` at the crude level `Φc` and the level `Λ_s`
  have hXg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ + 1 →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => Φc n) :=
    fun m hm hm' => nqFlow_prec_of_le_right (hX m hm (Or.inl hm')) fun n u ω =>
      (nqFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, hm'⟩)).1
  have hYg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => Φc n) :=
    fun m hm hm' => nqFlow_prec_of_le_right (hY m hm hm') fun n u ω =>
      (nqFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, by omega⟩)).2
  have hQ : Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) (2 * n_ - 1) ω *
        (STXiL sz n (E n) (u : ℝ) (4 * p) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => Λ n) :=
    nqFlow_hQ sz hsize (fun n => (hsv n).le) hv1 (a := 2 * n_ - 1) (b := 4 * p) hp
      (Xa := fun n => X (2 * n_ - 1) n) (Xb := fun n => X (4 * p) n)
      (fun n => zero_le_one.trans (hX1 _ n)) (fun n => zero_le_one.trans (hX1 _ n))
      (hX (2 * n_ - 1) (by omega) (Or.inr (Or.inl rfl))) (hX (4 * p) (by omega) (Or.inr (Or.inr rfl)))
  have hgood := hGrid v (fun n => (hsv n).le) (fun n => le_rfl) K hK0 n_ hn Λ Φc hΛ1 hΦc1 hXg hYg p hp hQ
    (C_K + 2) hKcard ε₁ hε₁ τ' hτ' D' hD'
  have hlin := hLin v (fun n => (hsv n).le) hvt K hK0 n_ hn X Y hX1 hY1
    (fun m hm hm' => hX m hm (Or.inl hm')) hY (C_K + 2) hKcard ε₁ hε₁
  have hinit := hLK n_ (by omega) ε₁ hε₁ (D + 2) (by linarith)
  filter_upwards [hpin, hgood (D + 2) (by linarith), hlin (D + 2) (by linarith), hinit,
    hsize.eventually_ge_atTop 2] with n hG hGood hLinn hInit hN2
  obtain ⟨G, hGP, hGb⟩ := hG
  have hNn1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg (by linarith) _
  -- the two matrix events: the terminal bound fails / an initial loop is large
  set Sterm : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
        STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) <
      ‖sz.STLKM n (E n) (v n) M (σ n) (a n)‖ / (sz.Bctl n (v n)) ^ n_} with hStermdef
  set Sinit : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ∃ p' : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ < ‖sz.STLKM n (E n) (s n) M p'.1 p'.2‖}
    with hSinitdef
  have hSterm : MeasurableSet Sterm :=
    measurableSet_lt measurable_const
      ((nqFlow_meas_STLKM sz n (E n) (v n) (σ n) (a n)).norm.div_const _)
  have hSinit : MeasurableSet Sinit := by
    have heq : Sinit = ⋃ p' : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)),
        {M | ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ <
          ‖sz.STLKM n (E n) (s n) M p'.1 p'.2‖} := by
      ext M; simp [hSinitdef]
    rw [heq]
    exact MeasurableSet.iUnion fun p' =>
      measurableSet_lt measurable_const (nqFlow_meas_STLKM sz n (E n) (s n) p'.1 p'.2).norm
  -- the transfers at the terminal grid index and at index `0`
  have e1 : sz.seqP (sz.seqHflow n (v n) ⁻¹' Sterm) = pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) := by
    have := nqFlow_transfer sz (s := s) (v := v) (K := K) (n := n) (K n) (hs0 n) (hsv n).le (hK0 n) hSterm
    rw [gridTime_last s v K n (hK0 n)] at this
    exact this.symm
  have e0 : pathP sz (pathH sz s v K n 0 ⁻¹' Sinit) = sz.seqP (sz.seqHflow n (s n) ⁻¹' Sinit) := by
    have := nqFlow_transfer sz (s := s) (v := v) (K := K) (n := n) 0 (hs0 n) (hsv n).le (hK0 n) hSinit
    rw [ST_gridTime_zero] at this
    exact this
  -- the failure event of the terminal bound is inside the union of four events
  have hmain : pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    refine nqFlow_union4 (C := pathH sz s v K n 0 ⁻¹' Sinit) (D' := Gᶜ) hx0 hGood hLinn ?_ ?_ ?_
      (nqFlow_four_pow_le hN2)
    · rw [e0]
      exact hInit
    · rw [← ofReal_measureReal (measure_ne_top (pathP sz) _)]
      exact ENNReal.ofReal_le_ofReal hGP
    · intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_or,
        not_not] at hno
      obtain ⟨⟨⟨hgoodω, hlinω⟩, hinitω⟩, hGω⟩ := hno
      have hinit' : ∀ σ' : Fin n_ → Bool, (∃ i, σ' i = σ' (finRotate n_ i)) →
          ∀ a' : Fin n_ → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ' a'‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ := by
        intro σ' _ a'
        by_contra hcon
        exact hinitω ⟨(σ', a'), not_le.1 hcon⟩
      have hb := hGb ω hGω (fun j hj => ⟨hgoodω j hj, hlinω j hj⟩) hinit' (σ n) (hσ n) (a n)
      have hlev : Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n ≤
          (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
            STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p :=
        nqFlow_level_le hn hp (fun m => hX1 m n) (fun m => hY1 m n) (hBs n)
      have hBk : 0 < (sz.Bctl n (v n)) ^ n_ := pow_pos (hBv n) _
      have hL0 : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have := hΦ n
        linarith [this]
      have hdiv : ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) (σ n) (a n)‖ /
          (sz.Bctl n (v n)) ^ n_ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) := (div_le_iff₀ hBk).2 hb
      have hhalf : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
        Real.rpow_le_rpow_of_exponent_le hNn1 (by linarith)
      have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (by linarith) _
      have hz0 : 0 ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
          STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p := hL0.trans hlev
      have hfin : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
            STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) :=
        calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
              STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) :=
              mul_le_mul_of_nonneg_left hlev hpos
          _ ≤ _ := mul_le_mul_of_nonneg_right hhalf hz0
      exact absurd hω (not_lt.2 (hdiv.trans hfin))
  calc sz.seqP (badSetAt sz.size _ _ τ n) = sz.seqP (sz.seqHflow n (v n) ⁻¹' Sterm) := by
        congr 1
        ext ω
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩
    _ = pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) := e1
    _ ≤ _ := hmain

/-- `1 ≤ STbootRHS lo XL XLK B k p` for `XL ≥ 1`, `XLK ≥ 0`, `B ≥ 0`, `k ≥ 1`: the sum `Σ_{m=k-1}^{k+1} XL m` contains
`XL k ≥ 1` and the other terms are nonnegative. -/
private theorem nqFlow_bootRHS_one_le {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 1 ≤ k)
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

/-- **The endpoint at an arbitrary section** `q n = (u_n, σ_n, a_n)` of the parameter set of `STNQConclPT''`
(`perTimeDomAt_iff_forall_section`): `v_n = u_n` where `s_n < u_n`, `v_n = t_n` elsewhere (so `s < v ≤ t`), the
controls are the numbers `XL m n (v n)`, `XLK m n (v n)` on the window `[s, v]` (`nqFlow_restrict_pair`), and
`nqFlow_core` gives the bound at the indices with `s_n < u_n`; at the collapsed indices `u_n = s_n` the section is
bounded by `STLK s` at length `n_` (`‖𝓛-𝒦‖_s ≤ N^τ B_s^{n_} ≤ N^τ ζ B_s^{n_}`, `ζ ≥ 1`). -/
private theorem nqFlow_section (sz : Sizes d) {E s t : ℕ → ℝ} (hd : 3 ≤ d) {κ' 𝔠 τR 𝔡 : ℝ} (hκ : 0 < κ')
    (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ') (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hLK : STLK sz E s)
    (hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConcl sz E s v)
    (hLin : NQLinConcl sz E s t) {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p) {XL XLK : ℕ → ℕ → ℝ → ℝ}
    (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (hXLp : ∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2))
    (hXLKp : ∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2))
    (q : ∀ n, TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
      (Fin n_ → Zd d (sz.L n))) :
    StochDomAt sz.seqP sz.size
      (fun n (_ : Unit) ω => ‖Lloop sz n (E n) ((q n).1 : ℝ) (q n).2.1.1 (q n).2.2 ω -
        STKloop sz n (E n) ((q n).1 : ℝ) (q n).2.1.1 (q n).2.2‖ / (sz.Bctl n ((q n).1 : ℝ)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n ((q n).1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n ((q n).1 : ℝ) +
        STbootRHS 2 (fun m => XL m n ((q n).1 : ℝ)) (fun m => XLK m n ((q n).1 : ℝ))
          (sz.Bctl n (s n)) n_ p) := by
  classical
  -- the end `v` of the window of the endpoint
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = fun n => if s n < ((q n).1 : ℝ) then ((q n).1 : ℝ) else t n :=
    ⟨_, rfl⟩
  have hsv : ∀ n, s n < v n := fun n => by
    by_cases h : s n < ((q n).1 : ℝ)
    · simp only [hvdef, h, ↓reduceIte]
    · simp only [hvdef, h, ↓reduceIte]; exact hst n
  have hvt : ∀ n, v n ≤ t n := fun n => by
    by_cases h : s n < ((q n).1 : ℝ)
    · simp only [hvdef, h, ↓reduceIte]; exact (q n).1.2.2
    · simp only [hvdef, h, ↓reduceIte]; exact le_rfl
  have hX : ∀ m : ℕ, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => XL m n (v n)) := fun m hm hl =>
    nqFlow_restrict_pair (sz := sz) (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiL sz n (E n) w m ω) (Z := fun n u => XL m n u) (hXLp m hm hl)
  have hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => XLK m n (v n)) := fun m hm hm' =>
    nqFlow_restrict_pair (sz := sz) (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiLK sz n (E n) w m ω) (Z := fun n u => XLK m n u) (hXLKp m hm hm')
  have hcore := nqFlow_core sz hd hκ h𝔠 hτR h𝔡 hsize hband hWO hE hs0 (fun n => (hst n).le) ht1 hcase hrange
    hWt hsv hvt hLK (hGrid v hsv hvt) hLin hn hp (X := fun m n => XL m n (v n))
    (Y := fun m n => XLK m n (v n)) (fun m n => hXL m n _) (fun m n => hXLK m n _) hX hY
    (fun n => (q n).2.1.1) (fun n => (q n).2.1.2) (fun n => (q n).2.2)
  intro τ hτ D hD
  filter_upwards [hcore τ hτ D hD, hLK n_ (by omega) τ hτ D hD] with n h1 h2
  by_cases hn' : s n < ((q n).1 : ℝ)
  · -- the section is not collapsed: `v n = u_n`
    have hv : v n = ((q n).1 : ℝ) := by simp only [hvdef, hn', ↓reduceIte]
    simp only [badSetAt] at h1 ⊢
    rw [hv] at h1
    exact h1
  · -- collapsed: `u_n = s_n`
    have hu : ((q n).1 : ℝ) = s n := le_antisymm (not_lt.1 hn') (q n).1.2.1
    refine le_trans (measure_mono ?_) h2
    intro ω hω
    simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
    obtain ⟨_, hω⟩ := hω
    rw [hu] at hω
    refine ⟨((q n).2.1.1, (q n).2.2), ?_⟩
    have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz ((hst n).trans (ht1 n))
    have hBk : 0 < (sz.Bctl n (s n)) ^ n_ := pow_pos hBs _
    have hz1 : 1 ≤ (sz.Bctl n (s n)) ^ (1 / 6 : ℝ) * XLK n_ n (s n) +
        STbootRHS 2 (fun m => XL m n (s n)) (fun m => XLK m n (s n)) (sz.Bctl n (s n)) n_ p := by
      have h0 : 0 ≤ (sz.Bctl n (s n)) ^ (1 / 6 : ℝ) * XLK n_ n (s n) :=
        mul_nonneg (Real.rpow_nonneg hBs.le _) (zero_le_one.trans (hXLK _ _ _))
      have := nqFlow_bootRHS_one_le (lo := 2) (XL := fun m => XL m n (s n)) (XLK := fun m => XLK m n (s n))
        (B := sz.Bctl n (s n)) (k := n_) (p := p) (by omega) (fun m => hXL _ _ _)
        (fun m => zero_le_one.trans (hXLK _ _ _)) hBs.le
      linarith
    have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hlt := (lt_div_iff₀ hBk).1 hω
    calc ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (s n)) ^ n_
        ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (s n)) ^ (1 / 6 : ℝ) * XLK n_ n (s n) +
          STbootRHS 2 (fun m => XL m n (s n)) (fun m => XLK m n (s n)) (sz.Bctl n (s n)) n_ p) *
            (sz.Bctl n (s n)) ^ n_ := by
          have := mul_le_mul_of_nonneg_left hz1 hN0
          nlinarith
      _ < _ := hlt

end Endpoint

/-! ## 6. The per-time pin `stOeqNQPT''_holds` -/

/-- **`stOeqNQPT''_holds`: the per-time R2* pin for every `d ≥ 3`** (`T2246_stOeqNQPT''_holds`; `lem:STOeq_NQ`
`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148` with `B_s`; proof `3_5:1152-1190`).  `𝔠_d = min (min 𝔠_d^G 𝔠_d^L) (1/(2d))`
with `𝔠_d^G`, `𝔠_d^L` the constants of `gridGoodN_holds d` and `nqLinGood_holds d` at the same `(κ, ε, 𝔡, C_d)`:
`d 𝔠_d ≤ 1/2 < 1` for `st_window`, and `STConStInd` passes to the larger exponents `𝔠_d^G`, `𝔠_d^L`
(`nqFlow_conStInd_exp_mono`).  The premises of `nqGridEndLinN` come from the flow (`v3_premises_of_stFlow` with `κ/2`,
`ε/2`; `st_window`); the good-event lemma `gridGoodN_holds` is re-instantiated on every window `[s, v]` (`st_conStInd_sub`,
`nqFlow_step2_restrict`); then `perTimeDomAt_iff_forall_section` and `nqFlow_section` (paper-delta candidates `T2246a`,
`T2246b`, `T2246c`). -/
theorem stOeqNQPT''_holds : ∀ d : ℕ, STOeqNQPT'' d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠G, hG0, hG1, HG⟩ := gridGoodN_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠L, hL0, hL1, HL⟩ := nqLinGood_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (0 : ℝ) < 1 / (2 * d) := by positivity
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min (min 𝔠G 𝔠L) (1 / (2 * d)) := ⟨_, rfl⟩
  have h𝔠d0 : 0 < 𝔠d := by rw [h𝔠d]; exact lt_min (lt_min hG0 hL0) hd2
  have h𝔠dG : 𝔠d ≤ 𝔠G := by rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_left _ _)
  have h𝔠dL : 𝔠d ≤ 𝔠L := by rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_right _ _)
  have h𝔠dd : 𝔠d ≤ 1 / (2 * d) := by rw [h𝔠d]; exact min_le_right _ _
  refine ⟨𝔠d, h𝔠d0, h𝔠dG.trans hG1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  obtain ⟨hA, hE', ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hconG : sz.STConStInd 𝔠G s t := nqFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dG ht1 hcon
  have hconL : sz.STConStInd 𝔠L s t := nqFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dL ht1 hcon
  have hdc : (d : ℝ) * 𝔠d < 1 := by
    calc (d : ℝ) * 𝔠d ≤ d * (1 / (2 * d)) := mul_le_mul_of_nonneg_left h𝔠dd hd0.le
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have hWt := st_window sz h𝔠d0 hdc hcon hA.2.2.2.2 (scaleFacts3_W_tendsto sz hA) hs ht1
  have hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) →
      GridGoodNConcl sz (STflowE z) s v := fun v hsv hvt =>
    HG 𝔠 sz z hflow s v hs hsv (fun n => (hvt n).trans (ht n)) trivial hK hKw hLK
      (st_conStInd_sub sz hG0 hconG (fun n => le_rfl) hsv hvt ht1) (nqFlow_step2_restrict hvt hStep2)
  have hLin : NQLinConcl sz (STflowE z) s t :=
    HL 𝔠 sz z hflow s t hs hst ht trivial hK hKw hLK hconL hStep2
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  refine (perTimeDomAt_iff_forall_section sz.seqP sz.size
    (fun n => ⟨(⟨s n, le_rfl, (hst n).le⟩, ⟨fun _ => true, ⟨⟨0, by omega⟩, rfl⟩⟩, fun _ => 0)⟩) _ _).2 ?_
  intro q
  exact nqFlow_section sz hd (half_pos hκ) hA.1 (half_pos hε) hA.2.1 hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2
    (fun n => (hE' n).le) hs hst ht1 hR hrange hWt hLK hGrid hLin hn hp hXL hXLK hXLp hXLKp q

/-! ## 7. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.NQEndFlowInst`.  Data (the merged instance data, as `inst_OeqNQ'`, `Step34PinsP.lean:184`): `sz0`
(`d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `N = 2^21`), the flow
`z0` (`z_n = 1/2 + i N_n^{-4/5}`, `flow_z0` at `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `s ≡ 0`, `t ≡ 1/16` (`t ≤ lemT z_n`,
`STCaseI`: `sz0_caseI`; `(con_st_ind)` for every `𝔠_d > 0`: `sz0_con`), `C_d = 1`; the case-(ii) data of the
merged `inst_OeqQtNZ` (`szB`, `zB`, `s ≡ 15/16`, `t ≡ 31/32`).  `STKbound`, `STKward` are theorems of the flow
(`stKbound_of_flow`, `stKward_of_flow`); what stays a hypothesis of an example is a stochastic premise that is another
gate's pin (`STLK s`, `STStep2Concl`, the pair hypotheses `Ξ̂ ≺ 1` of the pin, the owed merged pins `STOeqNQ`,
`STOeqQt`, `STOeqQtNZ`). -/

namespace NQEndFlowInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- **(1) `stOeqNQPT''_holds` at the data**: the per-time R2* pin at `(sz0, z0, s ≡ 0, t ≡ 1/16)`, `C_d = 1`: the
constant `𝔠_d ∈ (0, 1/100]`, then the stochastic premises of `STIngR` (`STKbound`, `STKward`, `STLK`, `STStep2Concl`),
then the conclusion `STNQConclPT''`.  Every deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the
regime `STCaseI`, `(con_st_ind)`, `C_d > 0`) is discharged by `inst_ing`. -/
theorem inst_OeqNQPT'' :
    InstIngConcl (fun sz E s t => STNQConclPT'' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STNQConclPT'' sz E s t) (stOeqNQPT''_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos

/-- **(1) with the conclusion applied** at `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`: `STKbound`, `STKward` come from the
flow, the stochastic premises `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` of the pin (the conclusions
of Steps 3-4, other gates' pins) stay hypotheses; the per-time conclusion
`(𝓛-𝒦)^{(3)}_{u,σ,a}/B_u³ ≺ B_u^{1/6} + STbootRHS 2 1 1 B_s 3 1` for every non-alternating `σ` and label `a`
(`PrecPT`: the union over `u ∈ [0, 1/16]` outside `P`) is the conclusion. -/
example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiL sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ))) :
    PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin 3 → Bool // ∃ k, σ k = σ (finRotate 3 k)} ×
        (Fin 3 → Zd 3 (sz0.L n)))
      (fun n q ω => ‖Lloop sz0 n (STflowE z0 n) (q.1 : ℝ) q.2.1.1 q.2.2 ω -
        STKloop sz0 n (STflowE z0 n) (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz0.Bctl n (q.1 : ℝ)) ^ 3)
      (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 2 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (sInst n)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqNQPT''
  exact hC (stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(2) `stOeqNQ''_of_stOeqNQ'`** at the data: the merged owed pin `STOeqNQ 3` (a hypothesis) gives the R2* pin by
`stOeqNQ'_of_stOeqNQ` (`Step34PinsP.lean:156`) and `stOeqNQ''_of_stOeqNQ'`, applied at the merged data
`sz0, z0` with every deterministic hypothesis discharged by `inst_ing`. -/
example (h : STOeqNQ 3) : InstIngConcl (fun sz E s t => STNQConcl'' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STNQConcl'' sz E s t) (stOeqNQ''_of_stOeqNQ' 3 (stOeqNQ'_of_stOeqNQ 3 h))
    sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos

/-- **(2) with the conclusion applied**: at the data, the stochastic premises of the pin being given, the R2*
conclusion `STNQConcl''` holds for `(sz0, E = STflowE z0, s, t)`. -/
example (h : STOeqNQ 3) (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1) :
    STNQConcl'' sz0 (STflowE z0) sInst tInst := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_ing STCaseI (fun sz E s t => STNQConcl'' sz E s t)
    (stOeqNQ''_of_stOeqNQ' 3 (stOeqNQ'_of_stOeqNQ 3 h)) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht
    sz0_caseI sz0_con 1 one_pos
  exact hC hKb hKw hLK hStep2

/-- **(2) the private implication at the data**: `t_n < 1` is discharged, the merged primed conclusion `STNQConcl'`
(the hypothesis) gives `STNQConcl''`. -/
example (h : STNQConcl' sz0 (STflowE z0) sInst tInst) : STNQConcl'' sz0 (STflowE z0) sInst tInst :=
  stNQConcl''_of_stNQConcl' sz0 (STflowE z0) sInst tInst (fun n => by simp only [tInst]; norm_num) h

/-- **(3) `stXiBoot'_of_stXiBoot`** at `(sz0, STflowE z0, s ≡ 0, t ≡ 1/16)`: `t_n < 1` is discharged; the merged
conclusion `STXiBoot` (the owed `lem:STOeq_Qt`) is the hypothesis. -/
example (h : STXiBoot sz0 (STflowE z0) sInst tInst) : STXiBoot' sz0 (STflowE z0) sInst tInst :=
  stXiBoot'_of_stXiBoot sz0 (STflowE z0) sInst tInst (fun n => by simp only [tInst]; norm_num) h

/-- **`stOeqQt'_of_stOeqQt`** (case (i)) at `(sz0, z0, 0, 1/16)`, applied through `inst_ing`. -/
example (h : STOeqQt 3) : InstIngConcl (fun sz E s t => STXiBoot' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STXiBoot' sz E s t) (stOeqQt'_of_stOeqQt 3 h) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos

/-- **`stOeqQtNZ'_of_stOeqQtNZ`** (case (ii)) at `(szB, zB, 15/16, 31/32)` (the data of the merged `inst_OeqQtNZ`),
applied through `inst_ing`. -/
example (h : STOeqQtNZ 3) :
    InstIngConcl (fun sz E s t => STXiBoot' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STXiBoot' sz E s t) (stOeqQtNZ'_of_stOeqQtNZ 3 h) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- **(4) the vocabulary at numbers**: `Λ = XL(2k-1)(XL(4p)/B)^{1/(2p)} = 2^{1/2}` at `XL ≡ 1`, `B = 1/2`,
`k = 3`, `p = 1` (so `Λ^{1/2}` is the first summand `B^{-1/4}` of `STbootRHS`), and `STbootRHS 2 1 1 B 3 1` is
antitone in `B` (`B = 1/2 ≥ 1/4`). -/
example : nqFlowLam (fun _ => 1) (1 / 2) 3 1 = (2 : ℝ) ^ (1 / 2 : ℝ) := by
  unfold nqFlowLam
  norm_num

example : (nqFlowLam (fun _ => (1 : ℝ)) (1 / 2) 3 1) ^ ((1 : ℝ) / 2) =
    (1 / 2 : ℝ) ^ (-(1 : ℝ) / (4 * ((1 : ℕ) : ℝ))) * (1 : ℝ) ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (1 / (4 * ((1 : ℕ) : ℝ))) :=
  nqFlow_lam_sqrt (k := 3) le_rfl (by norm_num) (fun _ => zero_le_one)

example : STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 2) 3 1 ≤
    STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 4) 3 1 :=
  nqFlow_bootRHS_anti (by norm_num) (by norm_num) (fun _ => zero_le_one)

example : nqFlowPhiC (fun _ => (1 : ℝ)) (fun _ => 1) 3 = 8 := by
  unfold nqFlowPhiC
  rw [show Finset.Icc 1 (3 + 1) = {1, 2, 3, 4} by decide]
  norm_num [Finset.sum_insert]

/-- **(5) the four statements of the check file, section 3** (statement equalities): the public bridges have
exactly the pinned types; the private one is `stNQConcl''_of_stNQConcl'` above. -/
example : ∀ d : ℕ, STOeqNQ' d → STOeqNQ'' d := @stOeqNQ''_of_stOeqNQ'
example : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, t n < 1) →
    STXiBoot sz E s t → STXiBoot' sz E s t := @stXiBoot'_of_stXiBoot
example : ∀ d : ℕ, STOeqQt d → STOeqQt' d := @stOeqQt'_of_stOeqQt
example : ∀ d : ℕ, STOeqQtNZ d → STOeqQtNZ' d := @stOeqQtNZ'_of_stOeqQtNZ
example : ∀ d : ℕ, STOeqNQPT'' d := @stOeqNQPT''_holds

end NQEndFlowInst

end RBM.Ind

end

#print axioms RBM.Gauss.Sizes.STNQConcl''
#print axioms RBM.Gauss.Sizes.STXiBoot'
#print axioms RBM.Gauss.Sizes.STNQConclPT''
#print axioms RBM.Gauss.Sizes.STOeqNQ''
#print axioms RBM.Gauss.Sizes.STOeqQt'
#print axioms RBM.Gauss.Sizes.STOeqQtNZ'
#print axioms RBM.Gauss.Sizes.STIterR'
#print axioms RBM.Gauss.Sizes.STIterations'
#print axioms RBM.Gauss.Sizes.STIterationsII'
#print axioms RBM.Gauss.Sizes.STOeqNQPT''
#print axioms RBM.Ind.nqFlowLam
#print axioms RBM.Ind.nqFlowPhiC
#print axioms RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot
#print axioms RBM.Gauss.Sizes.stOeqNQ''_of_stOeqNQ'
#print axioms RBM.Gauss.Sizes.stOeqQt'_of_stOeqQt
#print axioms RBM.Gauss.Sizes.stOeqQtNZ'_of_stOeqQtNZ
#print axioms RBM.Ind.stOeqNQPT''_holds
#print axioms RBM.Ind.NQEndFlowInst.inst_OeqNQPT''
