/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NQEndLinGen
import RBM3D.Induction.NQEndFlowLift

/-!
# The non-alternating endpoint at the flow, per time, over the carrier family

Generic forms of `Induction/NQEndFlow` and the `𝒦` modulus of `Induction/NQEndFlowLift` over a carrier family
`(law, Flow, mkM, T0)`, namespace `RBM.BA`, no `BA/*` import.  Paper: Lemma 4.6 (`lem:STOeq_NQ`),
(4.22) `am;asoiuw` and the proof of Lemma 4.6; Lemma 4.11 (`lem:iterations`).

* **The statements with `STbootRHS` at the window start `B_s`**: `STXiBootgL'`, `STNQConclgL''`,
  `STNQConclPTgL''`, `STOeqNQPTgL''`, `STOeqQtgL'`, `STOeqQtNZgL'`, `STIterRgL'`, `STIterationsgL'`,
  `STIterationsIIgL'`; `nqFlowLam`, `nqFlowPhiC`, `nqFlowSharp` are reused by name.
* **`stOeqNQPTgL''_of`**: the per-section endpoint `NQEndFlowGen_core`, `NQEndFlowGen_section`
  (the good event `gridGoodNgL_of` on every window `[s, v]`, the linear event `nqLinGoodgL_of`, the endpoint
  `nqGridEndLinNg`, the initial event from `STLKgL s`).
* **The time modulus of `𝒦`**: `NQEndFlowGen_KLip`, `NQEndFlowGen_KLipFam`, with the band discharge from
  `stKloop_lip`.

The model-free privates of `NQEndFlow` are reused by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private GridGoodGen_one_le_STXiLg from RBM3D.Chain.GridGoodGen

open private nqFlow_level_le nqFlow_phi_nonneg nqFlow_phiC_ge nqFlow_phiC_one_le nqFlow_K nqFlow_K_ne_zero nqFlow_K_low nqFlow_K_up
  nqFlow_K_card nqFlow_four_pow_le nqFlow_union4 nqFlow_bootRHS_one_le nqFlow_conStInd_exp_mono from RBM3D.Induction.NQEndFlow

open private nqEnd_rangeCond_mono from RBM3D.Induction.NQEndLin

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The statements with `STbootRHS` at the window start `B_s` -/

section Texts

/-- **`STXiBootgL'`** (band `STXiBoot'`): the bootstrap statement with the first summand of
`STbootRHS` at the window start `B_s = sz.Bctl n (s n)`. -/
def STXiBootgL' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- **`STNQConclgL''`** (band `STNQConcl''`): the non-alternating conclusion with `B_s` in the
first summand of `STbootRHS`. -/
def STNQConclgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Cf.L n (q.1 : ℝ) q.2.1.1 q.2.2 ω - Cf.K n (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **`STNQConclPTgL''`** (band `STNQConclPT''`): the per-time form (`PrecPTL` in the
conclusion). -/
def STNQConclPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Cf.L n (q.1 : ℝ) q.2.1.1 q.2.2 ω - Cf.K n (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **`STOeqNQPTgL''`** (band `STOeqNQPT''`): the per-time statement of Lemma 4.6 (`lem:STOeq_NQ`), case (i). -/
def STOeqNQPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => STNQConclPTgL'' (mk sz z) (law sz) s t)

/-- **`STOeqQtgL'`** (band `STOeqQt'`). -/
def STOeqQtgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => STXiBootgL' (mk sz z) (law sz) s t)

/-- **`STOeqQtNZgL'`** (band `STOeqQtNZ'`). -/
def STOeqQtNZgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseII law Flow mk T0 (fun sz z s t => STXiBootgL' (mk sz z) (law sz) s t)

/-- **`STIterRgL'`** (band `STIterR'`): the iteration statement with the hypothesis `STXiBootgL'`. -/
def STIterRgL' (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Aof : ∀ sz : Sizes d, (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t →
          STStep1LoopgL (mk sz z) (law sz) s t → STStep2ConclgL (mk sz z) (law sz) s t Cd →
          STXiBootgL' (mk sz z) (law sz) s t →
          ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
            (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHypgL (mk sz z) (law sz) s t (Aof sz s) r k) →
            (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHypgL (mk sz z) (law sz) s t (Aof sz s) r (k - 1)) →
            STIterHypgL (mk sz z) (law sz) s t (Aof sz s) n_ k

/-- **`STIterationsgL'`** (band `STIterations'`). -/
def STIterationsgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIterRgL' d STRegIterI law Flow mk T0 (fun sz _ n => STAI sz n)

/-- **`STIterationsIIgL'`** (band `STIterationsII'`). -/
def STIterationsIIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIterRgL' d STCaseII law Flow mk T0 (fun sz s n => STAII sz s n)
end Texts

/-! ## 2. The time modulus of `𝒦`

The conclusion of `stKloop_lip` (`Induction/NQEndFlowLift`) with `STKloop` read as `C.K`.  The band discharge is `stKloop_lip` through `bandFM` and `Green.v3_premises_of_stFlow`; the block Anderson versions are
`BAKsol_isKLoopS`, `baKbound_holds`. -/

section D2

/-- **`NQEndFlowGen_KLip`**: the time modulus of `𝒦^{(k)}` on `[0, t_n]` (the conclusion of `stKloop_lip`,
with `STKloop` read as `C.K`). -/
def NQEndFlowGen_KLip {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (t : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
    ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖C.K n u σ a - C.K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) * |u - u'|

/-- **The family form of `NQEndFlowGen_KLip`** (guarded). -/
def NQEndFlowGen_KLipFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, t n ≤ T0 sz z n) → ∀ k : ℕ, 2 ≤ k → NQEndFlowGen_KLip (mk sz z) t k

end D2

/-! ## 3. The levels, the grid and the facts of a carrier (generic forms of the private lemmas of `NQEndFlow`) -/

section Core

variable {d : ℕ}

/-- A pointwise larger right side keeps `≺` (the failure event only shrinks; band `nqFlow_prec_of_le_right`, over `PrecL`). -/
private theorem NQEndFlowGen_prec_of_le_right {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*}
    {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ} (h : PrecL sz μ ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : PrecL sz μ ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- **`hQ` at the level `Λ_s`** (band `nqFlow_hQ`, over `PrecL` and `STXiLg`): `Ξ̂_a (Ξ̂_b/B_u)^r ≺ max 1 (Xa (Xb / B_s)^r)` for
`0 ≤ r ≤ 1` from `Ξ̂_a ≺ Xa`, `Ξ̂_b ≺ Xb` uniformly in `u ∈ [s,v]`. -/
private theorem NQEndFlowGen_hQ {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (hsz : sz.SizeTendsto) {s v : ℕ → ℝ}
    (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) {a b p : ℕ} (hp : 1 ≤ p) {Xa Xb : ℕ → ℝ} (hXa : ∀ n, 0 ≤ Xa n)
    (hXb : ∀ n, 0 ≤ Xb n)
    (ha : PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cf n (u : ℝ) a ω) (fun n _ _ => Xa n))
    (hb : PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cf n (u : ℝ) b ω) (fun n _ _ => Xb n)) :
    PrecL sz μ (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLg Cf n (u : ℝ) a ω * (STXiLg Cf n (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
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
  have hXb0 : 0 ≤ STXiLg Cf n (u : ℝ) b ω := zero_le_one.trans (GridGoodGen_one_le_STXiLg Cf b ω hBu)
  have hXa0 : 0 ≤ STXiLg Cf n (u : ℝ) a ω := zero_le_one.trans (GridGoodGen_one_le_STXiLg Cf a ω hBu)
  set Nh : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hNh
  have hNh1 : 1 ≤ Nh := Real.one_le_rpow hN1 (half_pos hτ).le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
  have hr1 : 1 / (2 * (p : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have e1 : (STXiLg Cf n (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
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
  have hstep : STXiLg Cf n (u : ℝ) a ω * (STXiLg Cf n (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      (Nh * Xa n) * (Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := by
    refine mul_le_mul hXia ?_ (Real.rpow_nonneg (div_nonneg hXb0 hBu.le) _)
      (mul_nonneg (by linarith) (hXa n))
    calc (STXiLg Cf n (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ)))
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

/-- The bounds `Ξ̂ ≺ Z` on `[s, t]` restrict to the pairs `(w, v_n)`, `w ∈ [s_n, v_n]` (band `nqFlow_restrict_pair`, over `PrecL`). -/
private theorem NQEndFlowGen_restrict_pair {sz : Sizes d} {μ : Measure sz.SeqΩ} {s t v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n)
    {F : ∀ n, ℝ → sz.SeqΩ → ℝ} {Z : ∀ n, ℝ → ℝ}
    (h : PrecL sz μ (U := STPair s t) (fun n q ω => F n q.1.1 ω) (fun n q _ => Z n q.1.2)) :
    PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => F n (u : ℝ) ω) (fun n _ _ => Z n (v n)) :=
  StochDomAt.precomp_param (V := fun n => TimeIcc s v n) h
    (fun n w => (⟨((w : ℝ), v n), w.2.1, w.2.2, hvt n⟩ : STPair s t n))

/-- The three parts of `STStep2ConclgL` restrict from `[s,t]` to `[s,v]`, `v ≤ t` (band `nqFlow_step2_restrict`). -/
private theorem NQEndFlowGen_step2_restrict {sz : Sizes d} {Cf : FlowFM sz} {μ : Measure sz.SeqΩ} {s t v : ℕ → ℝ} {Cd : ℝ}
    (hvt : ∀ n, v n ≤ t n) (h : STStep2ConclgL Cf μ s t Cd) : STStep2ConclgL Cf μ s v Cd := by
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

end Core

section CoreProof

variable {d : ℕ}

/-- The carrier facts of one flow `(sz, z)` that the endpoint `nqGridEndLinNg` reads (the spectral data, the variance law and row sums of `Cm.S`, `GridRepTailGen_Ker`, the drift classes, plus the law and
`Step34Gen_LCompat` of the flow matrix `Hf`); a private bundle. -/
private structure NQEndFlowGen_Facts {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ℕ → ℝ) (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (κm A : ℝ) : Prop where
  hL : StepDecompGen_LoopForm Cm E
  hW : StepDecompGen_WalkForm Cm lam' Ψ
  hspec : DecayGen_Spec Cm.toFlowFM κm
  hm : ∀ n, ‖Cm.m n‖ ≤ 1
  hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n)
  hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1
  hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n
  hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a
  hExp : ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand Cm s' t' K' n
  hKL : ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop Cm n
  hKT : ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo Cm n
  hU : ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep Cm.toFlowFM n
  hLaw : Step2EventsGen_Law Cm μ Hf
  hC : Step34Gen_LCompat Cm Hf
  hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2
  hA : 1 ≤ A

/-- The model law is a probability measure when the carrier's is (the law `Step2EventsGen_Law` at the full set). -/
private theorem NQEndFlowGen_isProb {sz : Sizes d} {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} [IsProbabilityMeasure Cm.Pp]
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hLaw : Step2EventsGen_Law Cm μ Hf) : IsProbabilityMeasure μ := by
  refine ⟨?_⟩
  have h := hLaw (fun _ => 0) (fun _ => 0) (fun _ => 1) 0 0 le_rfl le_rfl one_ne_zero Set.univ MeasurableSet.univ
  simp only [Set.mem_univ, Set.ofPred_true, measure_univ] at h
  exact h.symm

/-- **The endpoint at one non-collapsed section** (band `nqFlow_core`; following RBM2D `gridEnd_to_flow`, with `nqGridEndLinNg` as the grid endpoint): for deterministic bounds `X m n`, `Y m n ≥ 1` with
`Ξ̂^{(𝓛)}_{w,m} ≺ X m` (`STlenL n_ p m`) and `Ξ̂^{(𝓛-𝒦)}_{w,m} ≺ Y m` (`m ≤ n_`) uniformly in `w ∈ [s_n, v_n]`, the non-alternating
`(𝓛-𝒦)^{(n_)}_{v,σ_n,a_n}/B_v^{n_}` is `≺ B_v^{1/6} Y n_ + STbootRHS 2 X Y B_s n_ p`.  The failure event is inside the union of four
events of probability `≤ N^{-(D+2)}`: the carrier walk leaving `GoodSetNg` (`hGrid`, the good event on `[s, v]` at the crude level `Φc` and the
level `Λ_s`) or `GoodLinNg` (`hLin`), the initial loops (`STLKgL s`, the law at `j = 0`) and the exceptional event `Gᶜ` of `nqGridEndLinNg` at
`ε₀ = τ/2`, `D₁ = D + 2`; outside it, `nqGridEndLinNg` bounds the terminal loop by `N^{τ/2}(Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^{n_} ≤ N^τ ζ B_v^{n_}`,
transferred to the flow matrix `Hf` at `v_n` by the law at `j = K_n` (`gridTime_last`). -/
private theorem NQEndFlowGen_core {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {κm A 𝔠 τR 𝔡 : ℝ}
    (F : NQEndFlowGen_Facts Cm μ Hf E lam' gK Ψ κm A) {s t v : ℕ → ℝ} (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡)
    (hKb : STKboundgL Cm.toFlowFM μ) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hsv : ∀ n, s n < v n) (hvt : ∀ n, v n ≤ t n) (hLK : STLKgL Cm.toFlowFM μ s)
    (hGrid : GridGoodNConclg Cm μ s v) (hLin : NQLinConclg Cm μ s t) {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p)
    {Ck Cv : ℝ} (hCk : 0 < Ck) (hCkCv : Ck ≤ Cv) (hAk0 : Ck < Cv ∨ A = 1)
    (hKer : ∀ᶠ n : ℕ in atTop, NQGoodGen_KerNAL Cm.toFlowFM gK n_ Ck n)
    {X Y : ℕ → ℕ → ℝ} (hX1 : ∀ m n, 1 ≤ X m n) (hY1 : ∀ m n, 1 ≤ Y m n)
    (hX : ∀ m : ℕ, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => X m n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Y m n))
    (σ : ∀ n, Fin n_ → Bool) (hσ : ∀ n, ∃ k, σ n k = σ n (finRotate n_ k)) (a : ∀ n, Fin n_ → Zd d (sz.L n)) :
    StochDomAt μ sz.size
      (fun n (_ : Unit) ω => ‖Cm.L n (v n) (σ n) (a n) ω - Cm.K n (v n) (σ n) (a n)‖ / (sz.Bctl n (v n)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
        STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) := by
  have : IsProbabilityMeasure Cm.Pp := by rw [F.hW.2.1]; exact isProbabilityMeasure_pathP _
  have := NQEndFlowGen_isProb F.hLaw
  intro τ hτ D hD
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hBv : ∀ n, 0 < sz.Bctl n (v n) := fun n => st_Bctl_pos sz (hv1 n)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hsv n).le.trans_lt (hv1 n))
  -- the levels
  set Λ : ℕ → ℝ := fun n => max 1 (RBM.Ind.nqFlowLam (fun m => X m n) (sz.Bctl n (s n)) n_ p) with hΛdef
  set Φ₁ : ℕ → ℝ := fun n => nqLinPhi1 (fun m => Y m n) n_ with hΦ₁def
  set Φ₂ : ℕ → ℝ := fun n =>
    nqLinPhi2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (v n)) n_ (Y n_ n) with hΦ₂def
  set Φ₃ : ℕ → ℝ := fun n => nqLinPhi3 (fun m => X m n) n_ with hΦ₃def
  set Φc : ℕ → ℝ := fun n => RBM.Ind.nqFlowPhiC (fun m => X m n) (fun m => Y m n) n_ with hΦcdef
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => le_max_left _ _
  have hΛ0 : ∀ n, 0 ≤ Λ n := fun n => zero_le_one.trans (hΛ1 n)
  have hΦ : ∀ n, 0 ≤ Φ₁ n ∧ 0 ≤ Φ₂ n ∧ 0 ≤ Φ₃ n := fun n =>
    nqFlow_phi_nonneg (fun m => hX1 m n) (fun m => hY1 m n) (hBv n).le
  have hΦc1 : ∀ n, 1 ≤ Φc n := fun n => nqFlow_phiC_one_le (fun m => hX1 m n) (fun m => hY1 m n)
  -- the endpoint of the grid walk at `ε₀ = τ/2`, `D₁ = D + 2`
  obtain ⟨ε₁, τ', D', C_K, hε₁, hτ', hD', hCK, hend⟩ := nqGridEndLinNg Cm μ s t hd h𝔠 hτR h𝔡 F.hL F.hW F.hspec F.hm F.hSeq F.hS
    F.hRow F.hKK hKb F.hExp F.hKL F.hKT F.hU hsize hband hWO hs0 hst ht1 hcase hrange hWt F.hcmp F.hA n_ hn Ck Cv hCk hCkCv hAk0
    hKer Λ Φ₁ Φ₂ Φ₃ hΛ0 (Eventually.of_forall hΛ1) (fun n => (hΦ n).1) (fun n => (hΦ n).2.1) (fun n => (hΦ n).2.2) v
    (fun n => (hsv n).le) hvt (τ / 2) (half_pos hτ) (D + 2) (by linarith)
  -- the grid
  set K : ℕ → ℕ := nqFlow_K sz C_K with hKdef
  have hK0 : ∀ n, K n ≠ 0 := nqFlow_K_ne_zero sz C_K
  have hKcard := nqFlow_K_card sz hsize hCK
  have hpin := hend Φc K hK0 (Eventually.of_forall (nqFlow_K_low sz C_K)) (Eventually.of_forall (nqFlow_K_up sz C_K))
  -- the hypotheses of the good-event lemma on `[s, v]` at the crude level `Φc` and the level `Λ_s`
  have hXg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ + 1 →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φc n) :=
    fun m hm hm' => NQEndFlowGen_prec_of_le_right (hX m hm (Or.inl hm')) fun n u ω =>
      (nqFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, hm'⟩)).1
  have hYg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φc n) :=
    fun m hm hm' => NQEndFlowGen_prec_of_le_right (hY m hm hm') fun n u ω =>
      (nqFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, by omega⟩)).2
  have hQ : PrecL sz μ (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) (2 * n_ - 1) ω *
        (STXiLg Cm.toFlowFM n (u : ℝ) (4 * p) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => Λ n) :=
    NQEndFlowGen_hQ Cm.toFlowFM μ hsize (fun n => (hsv n).le) hv1 (a := 2 * n_ - 1) (b := 4 * p) hp
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
      ‖Cm.LM n (v n) M (σ n) (a n) - Cm.K n (v n) (σ n) (a n)‖ / (sz.Bctl n (v n)) ^ n_} with hStermdef
  set Sinit : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ∃ p' : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ < ‖Cm.LM n (s n) M p'.1 p'.2 - Cm.K n (s n) p'.1 p'.2‖}
    with hSinitdef
  have hmeasLM := fun u => (GridGoodGen_meas_of_loopForm F.hL n u).1
  have hSterm : MeasurableSet Sterm :=
    measurableSet_lt measurable_const
      (((hmeasLM (v n) n_ (σ n) (a n)).sub_const _).norm.div_const _)
  have hSinit : MeasurableSet Sinit := by
    have heq : Sinit = ⋃ p' : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)),
        {M | ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ <
          ‖Cm.LM n (s n) M p'.1 p'.2 - Cm.K n (s n) p'.1 p'.2‖} := by
      ext M; simp [hSinitdef]
    rw [heq]
    exact MeasurableSet.iUnion fun p' =>
      measurableSet_lt measurable_const ((hmeasLM (s n) n_ p'.1 p'.2).sub_const _).norm
  -- the transfers at the terminal grid index and at index `0` (the law of the grid state)
  have e1 : μ {ω | Hf n (v n) ω ∈ Sterm} = Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) := by
    have := F.hLaw s v K n (K n) (hs0 n) (hsv n).le (hK0 n) Sterm hSterm
    rw [gridTime_last s v K n (hK0 n)] at this
    exact this.symm
  have e0 : Cm.Pp (Cm.Hpath s v K n 0 ⁻¹' Sinit) = μ {ω | Hf n (s n) ω ∈ Sinit} := by
    have := F.hLaw s v K n 0 (hs0 n) (hsv n).le (hK0 n) Sinit hSinit
    rw [ST_gridTime_zero] at this
    exact this
  have hLM0 : ∀ (ω : sz.SeqΩ) (σ' : Fin n_ → Bool) (a' : Fin n_ → Zd d (sz.L n)),
      Cm.LM n (s n) (Hf n (s n) ω) σ' a' = Cm.L n (s n) σ' a' ω := fun ω σ' a' =>
    GridGoodGen_LM_eq_L F.hL F.hC n (s n) σ' a' ω
  -- the failure event of the terminal bound is inside the union of four events
  have hmain : Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    refine nqFlow_union4 (C := Cm.Hpath s v K n 0 ⁻¹' Sinit) (D' := Gᶜ) hx0 hGood hLinn ?_ ?_ ?_
      (nqFlow_four_pow_le hN2)
    · rw [e0]
      refine le_trans (le_of_eq ?_) hInit
      congr 1
      ext ω
      simp only [badSetAt, Set.mem_ofPred_eq, hSinitdef, hLM0]
    · rw [← ofReal_measureReal (measure_ne_top Cm.Pp _)]
      exact ENNReal.ofReal_le_ofReal hGP
    · intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_or,
        not_not] at hno
      obtain ⟨⟨⟨hgoodω, hlinω⟩, hinitω⟩, hGω⟩ := hno
      have hinit' : ∀ σ' : Fin n_ → Bool, (∃ i, σ' i = σ' (finRotate n_ i)) →
          ∀ a' : Fin n_ → Zd d (sz.L n),
            ‖STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ' a'‖ ≤
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
      have hdiv : ‖STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) (σ n) (a n)‖ /
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
  have hLM : ∀ ω, Cm.LM n (v n) (Hf n (v n) ω) (σ n) (a n) = Cm.L n (v n) (σ n) (a n) ω := fun ω =>
    GridGoodGen_LM_eq_L F.hL F.hC n (v n) (σ n) (a n) ω
  calc μ (badSetAt sz.size _ _ τ n) = μ {ω | Hf n (v n) ω ∈ Sterm} := by
        congr 1
        ext ω
        simp only [badSetAt, Set.mem_ofPred_eq, hStermdef, hLM ω]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩
    _ = Cm.Pp (Cm.Hpath s v K n (K n) ⁻¹' Sterm) := e1
    _ ≤ _ := hmain

end CoreProof

section SectionProof

variable {d : ℕ}

/-- **The endpoint at an arbitrary section** `q n = (u_n, σ_n, a_n)` of the parameter set of `STNQConclPTgL''` (band `nqFlow_section`;
`perTimeDomAt_iff_forall_section`): `v_n = u_n` where `s_n < u_n`, `v_n = t_n` elsewhere (so `s < v ≤ t`), the bounds are the numbers
`XL m n (v n)`, `XLK m n (v n)` on the window `[s, v]` (`NQEndFlowGen_restrict_pair`), and `NQEndFlowGen_core` gives the bound at the indices with
`s_n < u_n`; at the collapsed indices `u_n = s_n` the section is bounded by `STLKgL s` at length `n_` (`‖𝓛-𝒦‖_s ≤ N^τ B_s^{n_} ≤ N^τ ζ B_s^{n_}`, `ζ ≥ 1`). -/
private theorem NQEndFlowGen_section {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {κm A 𝔠 τR 𝔡 : ℝ}
    (F : NQEndFlowGen_Facts Cm μ Hf E lam' gK Ψ κm A) {s t : ℕ → ℝ} (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡)
    (hKb : STKboundgL Cm.toFlowFM μ) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) (hLK : STLKgL Cm.toFlowFM μ s)
    (hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConclg Cm μ s v) (hLin : NQLinConclg Cm μ s t)
    {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p) {Ck Cv : ℝ} (hCk : 0 < Ck) (hCkCv : Ck ≤ Cv) (hAk0 : Ck < Cv ∨ A = 1)
    (hKer : ∀ᶠ n : ℕ in atTop, NQGoodGen_KerNAL Cm.toFlowFM gK n_ Ck n)
    {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (hXLp : ∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω) (fun n q _ => XL m n q.1.2))
    (hXLKp : ∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 m ω) (fun n q _ => XLK m n q.1.2))
    (q : ∀ n, TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d (sz.L n))) :
    StochDomAt μ sz.size
      (fun n (_ : Unit) ω => ‖Cm.L n ((q n).1 : ℝ) (q n).2.1.1 (q n).2.2 ω - Cm.K n ((q n).1 : ℝ) (q n).2.1.1 (q n).2.2‖ /
        (sz.Bctl n ((q n).1 : ℝ)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n ((q n).1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n ((q n).1 : ℝ) +
        STbootRHS 2 (fun m => XL m n ((q n).1 : ℝ)) (fun m => XLK m n ((q n).1 : ℝ)) (sz.Bctl n (s n)) n_ p) := by
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
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω)
        (fun n _ _ => XL m n (v n)) := fun m hm hl =>
    NQEndFlowGen_restrict_pair (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiLg Cm.toFlowFM n w m ω) (Z := fun n u => XL m n u) (hXLp m hm hl)
  have hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := fun n => TimeIcc s v n) (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω)
        (fun n _ _ => XLK m n (v n)) := fun m hm hm' =>
    NQEndFlowGen_restrict_pair (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiLKg Cm.toFlowFM n w m ω) (Z := fun n u => XLK m n u) (hXLKp m hm hm')
  have hcore := NQEndFlowGen_core Cm μ F hd h𝔠 hτR h𝔡 hKb hsize hband hWO hs0 (fun n => (hst n).le) ht1 hcase hrange
    hWt hsv hvt hLK (hGrid v hsv hvt) hLin hn hp hCk hCkCv hAk0 hKer (X := fun m n => XL m n (v n))
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

end SectionProof

/-! ## 4. The per-time statement `stOeqNQPTgL''_of`

The hypotheses of `stOeqNQPTgL''_of`: those of `gridGoodNgL_of` and `nqLinGoodgL_of`; `DecayGen_Spec` and the
inline `‖m‖ ≤ 1`; `S n = SB d (L n) (lam' n)` and the row sums; `GridRepTailGen_Ker`; the drift classes (eventual in `n`) and the link;
`NQGoodGen_KerNALFam` and the comparison hypothesis with the given `Aof κ`; the flow window `∃ τ > 0, RangeCond τ (T0 sz z)`.  The exponents `ε₁ τ' D' C_K` of the
endpoint are chosen after `(sz, z)` inside `nqGridEndLinNg`; the quantities `𝔠d`, `Ck` are chosen after `(k, κ, ε, 𝔡)` and before `(sz, z)`, and `Aof κ` is given. -/

section Public

/-- **`stOeqNQPTgL''_of`** (band `stOeqNQPT''_holds`): the per-time statement of Lemma 4.6 (`lem:STOeq_NQ`) over a carrier family
from the hypotheses above.  `𝔠_d = min (min 𝔠G 𝔠L) (1/(2d))` with `𝔠G`, `𝔠L` the constants of `gridGoodNgL_of` and `nqLinGoodgL_of` at the same
`(κ, ε, 𝔡, C_d)`: `d 𝔠_d ≤ 1/2 < 1` for `st_window`, and `STConStInd` passes to the larger exponents; the good event `gridGoodNgL_of` is re-instantiated on
every window `[s, v]` (`st_conStInd_sub`, the restriction of `STStep2ConclgL`); then `perTimeDomAt_iff_forall_section` and `NQEndFlowGen_section`.  The
kernel constant is `Ck` of `NQGoodGen_KerNALFam` at `k = n_`, the vocabulary constant `Cv = Ck + 1` (comparison hypothesis: `A = Aof κ`). -/
theorem stOeqNQPTgL''_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    -- the spectral data, the walk's variance law, the kernel class, the drift classes
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSeq : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), (mkM sz z).S n = SB d (sz.L n) (lam' sz z n))
    (hS : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1)
    (hRow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hKK : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (mkM sz z).KI n w (KLloopOf d (sz.L n) σ a) = (mkM sz z).K n w σ a)
    (hExp : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand (mkM sz z) s' t' K' n)
    (hKL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop (mkM sz z) n)
    (hKT : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep (mkM sz z).toFlowFM n)
    -- the kernel class of the non-alternating half (`∃ Ck` before `(sz, z)`) and the comparison hypothesis (`Aof κ`); the flow window
    (hKerFam : NQGoodGen_KerNALFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      1 ≤ Aof κ ∧ ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z)) :
    STOeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  have hGG := gridGoodNgL_of d law Flow mkM T0 Hf E lam' Ψ hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK
  have hNL := nqLinGoodgL_of d law Flow mkM T0 Hf E lam' Ψ hSE hFlow hL hW hLaw hC
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠G, hG0, hG1, HG⟩ := hGG hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠L, hL0, hL1, HL⟩ := hNL hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (0 : ℝ) < 1 / (2 * d) := by positivity
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min (min 𝔠G 𝔠L) (1 / (2 * d)) := ⟨_, rfl⟩
  have h𝔠d0 : 0 < 𝔠d := by rw [h𝔠d]; exact lt_min (lt_min hG0 hL0) hd2
  have h𝔠dG : 𝔠d ≤ 𝔠G := by rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_left _ _)
  have h𝔠dL : 𝔠d ≤ 𝔠L := by rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_right _ _)
  have h𝔠dd : 𝔠d ≤ 1 / (2 * d) := by rw [h𝔠d]; exact min_le_right _ _
  refine ⟨𝔠d, h𝔠d0, h𝔠dG.trans hG1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨τ0, hτ0, hrange0⟩ := hT0 sz κ ε 𝔠 𝔡 z hκ hε hflow
  have hrange : sz.RangeCond τ0 t := nqEnd_rangeCond_mono sz le_rfl ht hrange0
  have hconG : sz.STConStInd 𝔠G s t := nqFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dG ht1 hcon
  have hconL : sz.STConStInd 𝔠L s t := nqFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dL ht1 hcon
  have hdc : (d : ℝ) * 𝔠d < 1 := by
    calc (d : ℝ) * 𝔠d ≤ d * (1 / (2 * d)) := mul_le_mul_of_nonneg_left h𝔠dd hd0.le
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have hWt := st_window sz h𝔠d0 hdc hcon hA.2.2.2.2 (scaleFacts3_W_tendsto sz hA) hs ht1
  have hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConclg (mkM sz z) (law sz) s v :=
    fun v hsv hvt => HG 𝔠 sz z hflow s v hs hsv (fun n => (hvt n).trans (ht n)) trivial hK hKw hLK
      (st_conStInd_sub sz hG0 hconG (fun n => le_rfl) hsv hvt ht1) (NQEndFlowGen_step2_restrict hvt hStep2)
  have hLin : NQLinConclg (mkM sz z) (law sz) s t :=
    HL 𝔠 sz z hflow s t hs hst ht trivial hK hKw hLK hconL hStep2
  obtain ⟨κm, hspec⟩ := hSpec sz κ ε 𝔠 𝔡 z hκ hflow
  have hr1 := hR1 sz κ ε 𝔠 𝔡 z hκ hflow
  have F : NQEndFlowGen_Facts (mkM sz z) (law sz) (Hf sz z) (E sz z) (lam' sz z) (gK sz z) (Ψ sz z) κm (Aof κ) :=
    ⟨hL sz κ ε 𝔠 𝔡 z hκ hflow, hW sz κ ε 𝔠 𝔡 z hκ hflow, hspec, hm sz κ ε 𝔠 𝔡 z hκ hflow, hSeq sz z, hS sz z,
      hRow sz κ ε 𝔠 𝔡 z hκ hflow, hKK sz z, hExp sz κ ε 𝔠 𝔡 z hκ hflow, hKL sz κ ε 𝔠 𝔡 z hκ hflow,
      hKT sz κ ε 𝔠 𝔡 z hκ hflow, hU sz κ ε 𝔠 𝔡 z hκ hflow, hLaw sz z, hC sz z, hr1.2, hr1.1⟩
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  obtain ⟨Ck, hCk, hKerAll⟩ := hKerFam hd n_ hn κ ε 𝔡 hκ hε h𝔡
  have hKer := hKerAll sz 𝔠 z hflow
  refine (perTimeDomAt_iff_forall_section (law sz) sz.size
    (fun n => ⟨(⟨s n, le_rfl, (hst n).le⟩, ⟨fun _ => true, ⟨⟨0, by omega⟩, rfl⟩⟩, fun _ => 0)⟩) _ _).2 ?_
  intro q
  exact NQEndFlowGen_section (mkM sz z) (law sz) F hd hA.1 hτ0 hA.2.1 hK hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2 hs hst ht1 hR hrange
    hWt hLK hGrid hLin hn hp hCk (Ck := Ck) (Cv := Ck + 1) (by linarith) (Or.inl (by linarith)) hKer hXL hXLK hXLp hXLKp q

end Public

end RBM.BA

end
