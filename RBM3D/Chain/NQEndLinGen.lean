/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NQLinGen
import RBM3D.Chain.HierDriftGen
import RBM3D.Induction.NQEndLin

/-!
# The non-alternating grid endpoint with the linear right side over the carrier (U3s2c, file 1; ticket T2491)

Generic forms of `Induction/NQEndLin.lean` (not edited) over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: arXiv:2507.20274, `lem:STOeq_NQ` (`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148`, proof `3_5:1152-1190`).
`etaT E u` is `Cm.eta n u`, `|E n| ≤ 2 - κ` is `DecayGen_Spec` plus the inline `‖Cm.m n‖ ≤ 1` (D3), `STKbound` is the pin `STKboundgL`.

* **D5** (DECISIONS §294 (3) (9)): `GridDriftNgAt` (the body of `GridDriftNg` at one index), `gridDriftNg_envelope_ev` (the envelope with the
  drift premise eventual in `n`), `gridDriftNgAt_of_classes` (the per-index classes give it); the merged form is `Eventually.of_forall`.
* **Target 11** the regime facts (§2: the absorption lemmas `ha2`, `ha3`, `he2`, the range facts `hη`, `hΔη`, the shift hypothesis `hδ`), the
  assembly at the exit time `nqLinExitTauNg` (§3), the collapsed window and the `Y`-moment constant (§4).
* **Target 12** `nqGridEndLinNg` (§5), the per-carrier endpoint; `ε₁ τ' D' C_K` after the carrier; band re-derivation `nqGridEndLinN_of_gen`.

The model-free privates of `NQEndLin` §0-§2c are reused by `open private`; the lemmas that read `etaT (E n)`, `mE (E n)` are the band ones
at the energy `E'_n = 2 √(1 - (Im m_n)²)` (`GridEnvelopeGen_mE_im_Ep`), for which `etaT E' = Cm.eta`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private gridEnv_gridTime_le gridEnv_gridTime_nonneg from RBM3D.Induction.GridEnvelopeN

open private nqEnd_ev_rpow_le nqEnd_one_le_size nqEnd_ev_ha1 nqEnd_ev_ha2 nqEnd_ev_ha3 nqEnd_ev_he1 nqEnd_ev_he4 nqEnd_he2_bound
  nqEnd_he2_final nqEnd_ev_W_rpow_ge nqEnd_step_le nqEnd_K_mul_step nqEnd_ev_hη nqEnd_hΔη nqEnd_ev_hδ nqEnd_arith
  nqEnd_gridTime_nonneg nqEnd_gridTime_le nqEnd_rangeCond_mono nqEnd_ev_union nqEnd_stepErrN_nonneg from RBM3D.Induction.NQEndLin

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (kStepC uStepC nqGood1C nonAltClsN)

/-! ## 1. D5: the grid drift enters per index -/

section D5

variable {d : ℕ} {sz : Sizes d}

/-- **D5, `GridDriftNgAt`** (text fixed at the 1a-audit = probe `T2491_GridDriftNgAt`): the body of `GridDriftNg` (`HierDriftGen.lean:633-645`) at one
size index `n`, after `(hs0, hst, ht1, hK0)`.  At BA the drift classes hold only past the WO window, so no public statement of this row takes
`GridDriftNg` as an `∀ n` premise. -/
def GridDriftNgAt (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ (j : ℕ), j < K n → ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ Bk) →
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j)
              (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (Cm.eta n (gridTime s t K n (j + 1)))⁻¹) ^ (k + 4) * gridStep s t K n ^ ((3 : ℝ) / 2) +
          kStepC d (sz.L n) (sz.W n) k Bk * gridStep s t K n ^ 2 +
          uStepC k (gridStep s t K n) (gridTime s t K n (j + 1)) *
            ((Cm.eta n (gridTime s t K n j))⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk)

/-- The merged pin `GridDriftNg` is the form at every index (`Iff.rfl`). -/
theorem gridDriftNg_iff_at (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    GridDriftNg Cm s t K ↔ ((∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
      ∀ n, GridDriftNgAt Cm s t K n) := Iff.rfl

/-- **D5, the concluder of `GridDriftNgAt`**: the per-index classes `Expand`, `KLoop`, `KTwo`, `UStep`, the row sums and the link, with the
window at `n`, give the drift at `n` (`gridDriftNg_at`, `HierDriftGen.lean:818`). -/
theorem gridDriftNgAt_of_classes {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hExp : HierDriftGen_Expand Cm s t K n) (hKL : HierDriftGen_KLoop Cm n) (hKT : HierDriftGen_KTwo Cm n)
    (hU : HierDriftGen_UStep Cm.toFlowFM n) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hKK : HierDriftGen_KLink Cm n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) :
    GridDriftNgAt Cm s t K n :=
  fun j hj k hk σ Bk hBk hB => gridDriftNg_at hL hW s t K n j hExp hKL hKT hU hS hKK hs0 hst ht1 hK hj hk σ Bk hBk hB

/-- **D5, `gridDriftNg_envelope_ev`** (text fixed at the 1a-audit = probe `T2491_EnvelopeEv`; band `gridDriftN_envelope`, `GridEnvelopeN:111`):
`gridDriftNg_envelope` with the drift premise `∀ᶠ n, GridDriftNgAt Cm s t K n`; the conclusion is the same.  The merged form is recovered by
`Eventually.of_forall` (`gridDriftNg_envelope_of_merged`). -/
theorem gridDriftNg_envelope_ev (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 2 ≤ k) (τK : ℝ) (hτK : 0 < τK) {s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hη : ∀ (n : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hGD : ∀ᶠ n in atTop, GridDriftNgAt Cm s t K n) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        stepErrNg Cm.toFlowFM n k (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k) := by
  classical
  have hv1 : ∀ n j, j < K n → gridTime s t K n (j + 1) < 1 := fun n j hj =>
    (gridEnv_gridTime_le (hst n) (hK0 n) (show j + 1 ≤ K n by omega)).trans_lt (ht1 n)
  let P : ℕ → ℕ → Prop := fun n j => ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)),
    ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖Cm.KI n w J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k
  have hP : ∀ᶠ n in atTop, ∀ j, j < K n → P n j := by
    by_contra hcon
    have hfreq := Filter.not_eventually.1 hcon
    let bad : ℕ → Prop := fun n => ∃ j, j < K n ∧ ¬ P n j
    have hbad : ∀ n, ¬ (∀ j, j < K n → P n j) → bad n := by
      intro n hn
      by_contra hb
      exact hn fun j hj => by
        by_contra hc
        exact hb ⟨j, hj, hc⟩
    let v : ℕ → ℝ := fun n =>
      if h : bad n then gridTime s t K n (Classical.choose h + 1) else 0
    have hvmem : ∀ n, 0 ≤ v n ∧ v n < 1 := by
      intro n
      by_cases h : bad n
      · have e : v n = gridTime s t K n (Classical.choose h + 1) := by simp [v, h]
        rw [e]
        exact ⟨gridEnv_gridTime_nonneg (hs0 n) (hst n) _, hv1 n _ (Classical.choose_spec h).1⟩
      · have e : v n = 0 := by simp [v, h]
        rw [e]
        exact ⟨le_rfl, one_pos⟩
    have hwin := exists_norm_KI_le_wing Cm μ hsize hKb hKK hη v (fun n => (hvmem n).1)
      (fun n => (hvmem n).2) k τK hτK
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hwin).exists
    have hbn : bad n := hbad n hn1
    obtain ⟨hjlt, hnP⟩ := Classical.choose_spec hbn
    have e : v n = gridTime s t K n (Classical.choose hbn + 1) := by simp [v, hbn]
    apply hnP
    intro w hw J hJ h2 hJk
    have hb := hn2 w (by rw [e]; exact hw) J hJ h2 hJk
    rw [e] at hb
    exact hb
  filter_upwards [hP, hGD] with n hn hgd
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hη' : 0 < Cm.eta n (gridTime s t K n (j + 1)) :=
      (hη n _ (gridEnv_gridTime_nonneg (hs0 n) (hst n) _) (hv1 n j hj)).1
    have hBk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη'.le) _)
    have h := hgd j hj k hk σ _ hBk (hn j hj)
    exact h.mono fun ω hω _ => hω
  · exact Eventually.of_forall fun ω h => absurd h hj

/-- The merged envelope is the eventual one at the merged drift (`Eventually.of_forall`; band recovery of `gridDriftNg_envelope`). -/
theorem gridDriftNg_envelope_of_merged (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 2 ≤ k) (τK : ℝ) (hτK : 0 < τK) {s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hη : ∀ (n : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hGD : GridDriftNg Cm s t K) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        stepErrNg Cm.toFlowFM n k (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k) :=
  gridDriftNg_envelope_ev Cm μ k hk τK hτK hsize hKb hKK hη hs0 hst ht1 hK0
    (Eventually.of_forall fun n => hGD hs0 hst ht1 hK0 n) σ

end D5

/-! ## 2. Target 11 (a): the regime facts -/

section Regime

variable {d : ℕ} {sz : Sizes d}

/-- **The band energy with the same `Im m`** (`GridEnvelopeGen_mE_im_Ep`): under `DecayGen_Spec` and `Im m ≤ 1` there is an energy
`E'` with `|E'| < 2`, `Im mE(E'_n) = Im m_n` and `etaT E'_n = Cm.eta n`; the band regime lemmas at `E'` are the generic ones. -/
private theorem NQEndLinGen_Ep (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (him1 : ∀ n, (Cm.m n).im ≤ 1) :
    ∃ E' : ℕ → ℝ, (∀ n, |E' n| < 2) ∧ (∀ n, (mE (E' n)).im = (Cm.m n).im) ∧ (∀ n u, etaT (E' n) u = Cm.eta n u) := by
  have hκ0 : 0 < κm := hspec.1
  refine ⟨fun n => 2 * Real.sqrt (1 - ((Cm.m n).im) ^ 2), fun n => ?_, fun n =>
    GridEnvelopeGen_mE_im_Ep (hκ0.le.trans (hspec.2.1 n)) (him1 n), fun n u => ?_⟩
  · have h := GridEnvelopeGen_abs_Ep_le hκ0 (hspec.2.1 n) (him1 n)
    have : 0 < κm ^ 2 := by positivity
    linarith
  · rw [hspec.2.2 n u]
    unfold etaT
    rw [GridEnvelopeGen_mE_im_Ep (hκ0.le.trans (hspec.2.1 n)) (him1 n)]

/-- (ha2) over a carrier: `k W^{Cε} (N^{ε₁})² Ls ≤ N^{ε₀}/12`, `Ls = (Im m)⁻¹ log N` (band `nqEnd_ev_ha2` at `E'`). -/
private theorem NQEndLinGen_ev_ha2 (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (him1 : ∀ n, (Cm.m n).im ≤ 1) (hd : 1 ≤ d) (hsize : sz.SizeTendsto) (k : ℕ) {c ε₁ ε₀ : ℝ} (hc : 0 ≤ c)
    (hε : c + 2 * ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ c * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  obtain ⟨E', -, hmE, -⟩ := NQEndLinGen_Ep Cm hspec him1
  have h := nqEnd_ev_ha2 sz hd hsize k hspec.1 (E := E') (fun n => by rw [hmE n]; exact hspec.2.1 n) hc hε
  simpa only [hmE] using h

/-- (ha3) over a carrier: `N^{εq} W^{Cε} N^{ε₁} √(k (Ls + 1)) ≤ N^{ε₀}/12` (band `nqEnd_ev_ha3` at `E'`). -/
private theorem NQEndLinGen_ev_ha3 (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (him1 : ∀ n, (Cm.m n).im ≤ 1) (hd : 1 ≤ d) (hsize : sz.SizeTendsto) (k : ℕ) {c ε₁ εq ε₀ : ℝ} (hc : 0 ≤ c)
    (hε : εq + c + ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ c *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ *
          Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  obtain ⟨E', -, hmE, -⟩ := NQEndLinGen_Ep Cm hspec him1
  have h := nqEnd_ev_ha3 sz hd hsize k hspec.1 (E := E') (fun n => by rw [hmE n]; exact hspec.2.1 n) hc hε
  simpa only [hmE] using h

/-- (he2) over a carrier with an explicit kernel constant `C` (band `nqEnd_ev_he2`, `NQEndLin:397`, with `nqGood1C d k Λg κ'` read as `C`):
`N^{εq} (N^k √(k · qvFar · W^{-D''})) ≤ N^{ε₀}/12`, `qvFar = NQBudgetGen_qvFar`. -/
private theorem NQEndLinGen_ev_he2 (hsize : sz.SizeTendsto) {𝔠 : ℝ} (hband : sz.Bandwidth 𝔠) {k : ℕ}
    (hk : 1 ≤ k) {Λg C ε : ℝ} (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    {D'' εq ε₀ ξ : ℝ}
    (he1 : 2 * (C * ε) - D'' ≤ 0) (he2 : C * ε + C - D'' ≤ 0) (he3 : C + (k : ℝ) - D'' ≤ 0)
    (h1 : 2 * ((k : ℝ) - 1) + 𝔠 * (2 * (C * ε) - D'') ≤ ξ)
    (h2 : ((k : ℝ) - 1) + 𝔠 * (C * ε + C - D'') ≤ ξ)
    (h3 : 𝔠 * (C + (k : ℝ) - D'') ≤ ξ) (hξ : εq + (k : ℝ) + ξ / 2 < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * (NQBudgetGen_qvFar sz n k C ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  set P : ℝ := (1 + Λg ^ 2) ^ (k - 1) with hP
  have hP0 : 0 ≤ P := by positivity
  set M : ℝ := P ^ 2 + P + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  filter_upwards [hband, hlam, hsize.eventually (nqEnd_ev_rpow_le hξ (12 * Real.sqrt ((k : ℝ) * M))),
    hsize.eventually_ge_atTop 1] with n hW hg h hN1
  obtain ⟨hg0, hgΛ⟩ := hg
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hR0 : 0 ≤ ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) := by positivity
  have hR : ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ (k - 1) ≤
      P * ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) - 1) := by
    rw [mul_pow]
    have h1' : (1 + sz.lam n ^ 2) ^ (k - 1) ≤ P :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h2' : ((sz.size n : ℕ) : ℝ) ^ (k - 1) = ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) - 1) := by
      rw [← Real.rpow_natCast, Nat.cast_sub hk, Nat.cast_one]
    rw [h2']
    exact mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg hN0.le _)
  have hbound := nqEnd_he2_bound (x := ((sz.W n : ℕ) : ℝ)) (N := ((sz.size n : ℕ) : ℝ))
    (a := C * ε) (b := C) (D := D'') (𝔠 := 𝔠) (ξ := ξ) (r := (k : ℝ) - 1) (k := k) hN1 hW hR0 hR hP0 he1 he2 he3 h1 h2 h3
  have hY : NQBudgetGen_qvFar sz n k C ε * ((sz.W n : ℕ) : ℝ) ^ (-D'') ≤ M * ((sz.size n : ℕ) : ℝ) ^ ξ := by
    unfold NQBudgetGen_qvFar NQBudgetGen_kapFar
    exact hbound
  exact nqEnd_he2_final hN1 hM0 hY h

/-- (`hη`) over a carrier: `η_v⁻¹ ≤ N` eventually from `RangeCond τ_R v`, `κ_m ≤ Im m` (band `nqEnd_ev_hη` at `E'`). -/
private theorem NQEndLinGen_ev_hη (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (him1 : ∀ n, (Cm.m n).im ≤ 1) (hsize : sz.SizeTendsto) {τR : ℝ} (hτR : 0 < τR) {v : ℕ → ℝ}
    (hrange : sz.RangeCond τR v) :
    ∀ᶠ n : ℕ in atTop, (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  obtain ⟨E', -, hmE, hetaE⟩ := NQEndLinGen_Ep Cm hspec him1
  have h := nqEnd_ev_hη sz hsize hspec.1 (E := E') (v := v) (fun n => by rw [hmE n]; exact hspec.2.1 n) hτR hrange
  simpa only [hetaE] using h

/-- The shift error of the carrier is the band one at `E'`. -/
private theorem NQEndLinGen_eeShiftErrNg_eq (Cm : Step2Mat sz) {E' : ℕ → ℝ} (hetaE : ∀ n u, etaT (E' n) u = Cm.eta n u)
    (n k : ℕ) (u u' : ℝ) : eeShiftErrNg Cm n k u u' = RBM.Ind.eeShiftErrN d (sz.L n) (sz.W n) (E' n) k u u' := by
  unfold eeShiftErrNg RBM.Ind.eeShiftErrN
  rw [hetaE]

/-- (`hδ`, the shift hypothesis of `subGaussStop_linNg`) over a carrier: `W^{-(D''+1)} + eeShiftErrNg(u_j, u_{j+1}) ≤ W^{-D''}` for every
`j < K n`, eventually (band `nqEnd_ev_hδ` at `E'`). -/
private theorem NQEndLinGen_ev_hδ (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (him1 : ∀ n, (Cm.m n).im ≤ 1) (hd : 1 ≤ d) (hsize : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hband : sz.Bandwidth 𝔠) (k : ℕ) {D'' C_K : ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hη : ∀ᶠ n : ℕ in atTop, (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hD'' : 0 ≤ D'')
    (hCK : D'' + 2 * (k : ℝ) + 5 ≤ C_K) (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) +
      eeShiftErrNg Cm n k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
  obtain ⟨E', hE'2, hmE, hetaE⟩ := NQEndLinGen_Ep Cm hspec him1
  have hη' : ∀ᶠ n : ℕ in atTop, (etaT (E' n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := hη.mono fun n h => by rw [hetaE]; exact h
  have h := nqEnd_ev_hδ sz hd hsize h𝔠 hband k hE'2 hs0 hsv hv1 hK0 hη' hD'' hCK hKN
  refine h.mono fun n hn j hj => ?_
  have := hn j hj
  rwa [← NQEndLinGen_eeShiftErrNg_eq Cm hetaE] at this

/-- The step error is nonnegative on `[0, 1)` (band `nqEnd_stepErrN_nonneg` at `E'`). -/
private theorem NQEndLinGen_stepErrNg_nonneg (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (him1 : ∀ n, (Cm.m n).im ≤ 1) (n k : ℕ) {u v Δ Bk : ℝ} (hu1 : u < 1) (hv1 : v < 1) (hΔ : 0 ≤ Δ) (hBk : 0 ≤ Bk) :
    0 ≤ stepErrNg Cm.toFlowFM n k u v Δ Bk := by
  obtain ⟨E', hE'2, hmE, hetaE⟩ := NQEndLinGen_Ep Cm hspec him1
  have e : stepErrNg Cm.toFlowFM n k u v Δ Bk = RBM.Ind.stepErrN d (sz.L n) (sz.W n) (E' n) k u v Δ Bk := by
    rw [bandFM_stepErrN sz E' n k u v Δ Bk]
    exact GridEnvelopeGen_stepErrNg_eta n k u v Δ Bk (fun t => (hetaE n t).symm)
  rw [e]
  exact nqEnd_stepErrN_nonneg (hE'2 n) hu1 hv1 hΔ hBk

end Regime

/-! ## 3. Target 11 (b): the assembly at the exit time `nqLinExitTauNg`, for one sign vector

Band `nqEndLin_assembly` (`NQEndLin:769`).  The exit time is `nqLinExitTauNg` (exit from `GoodSetNg ∩ GoodLinNg`), the drift field is
`nqLin_hdriftNg` at the level `dDriftLinNg`, and the right side is `assembledRHSLinNg`.  The kernel class is the field `hKer` of
`GridAssemblyHypNg` (`GridRepTailGen_Ker`), the sub-Gaussian input is `subGaussStop_linNg` (D1, R1, D3), the envelope is D5. -/

section Assembly

variable {d : ℕ} {sz : Sizes d}

/-- `0 < η_u ≤ 1 - u` on `[0, 1)` (`LoopForm`, `‖m‖ ≤ 1`): the premise `hη` of the envelope. -/
private theorem NQEndLinGen_eta_win {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) :
    ∀ (n : ℕ) (w : ℝ), 0 ≤ w → w < 1 → 0 < Cm.eta n w ∧ Cm.eta n w ≤ 1 - w := fun n w _ hw1 =>
  ⟨NQGood1Gen_eta_pos hL n hw1, by
    rw [NQGood1Gen_eta_eq hL]
    nlinarith [(hL n).1, NQGood1Gen_im_le_one (hm n)]⟩

/-- **The assembly at the exit time, for one sign vector** (band `nqEndLin_assembly`, the merged `assembledNg` at `τ = nqLinExitTauNg`).
Eventually in `n`, for every non-alternating `σ` on a strict window `s_n < v_n` there is an event `G`, `P(Gᶜ) ≤ N^{-D₁}`, on which the
terminal bound `‖A_K(a)‖ ≤ assembledRHSLinNg` holds as soon as the grid walk stays in `GoodSetNg ∩ GoodLinNg`.  The per-`n` regime facts
of `subGaussStop_linNg` and the shift hypothesis `hδ` are eventual premises; the kernel class `hKer` (D1, constant `Ck`), the comparison
(R1: `hcmp`, `hA`, `hdW`, `hAk`, `Ck ≤ Cv`) enter only through `subGaussStop_linNg` and `nonAlt_hkerNg`; the drift is D5. -/
private theorem NQEndLinGen_assembly (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {κm : ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) (hd : 3 ≤ d) (hk : 2 ≤ k)
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n))
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hKb : STKboundgL Cm.toFlowFM μ) (hGD : ∀ᶠ n : ℕ in atTop, GridDriftNgAt Cm s v K n)
    (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (hΓ : ∀ n, 0 ≤ Γ n) (hΛ : ∀ n, 0 ≤ Λ n)
    (hΦ₁ : ∀ n, 0 ≤ Φ₁ n) (hΦ₂ : ∀ n, 0 ≤ Φ₂ n) (hΦ₃ : ∀ n, 0 ≤ Φ₃ n)
    {A Ck Cv ε τ' D' D'' D_Y τK εq D₁ C_P C_K : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A) (hCv : Ck ≤ Cv)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hD'' : (k : ℝ) + 1 < D'') (hD' : 1 < D') (hτK : 0 < τK) (hεq : 0 < εq)
    (hCK0 : 0 ≤ C_K) (hCK : D₁ + 4 * D_Y + (k : ℝ) + 2 * C_P + 8 ≤ C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsNg Cm σ (gridTime s v K n) τ (K n)
          (fun j ω => YvecNg Cm s v K n j σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n))
    (hKer : ∀ᶠ n : ℕ in atTop, NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n)
    (hW1 : ∀ᶠ n : ℕ in atTop, 1 < ((sz.W n : ℕ) : ℝ))
    (hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : ∀ᶠ n : ℕ in atTop, (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : ∀ᶠ n : ℕ in atTop, A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε))
    (hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrNg Cm n k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → s n < v n →
      ∃ G : Set (PathΩ sz), Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, Cm.Hpath s v K n j ω ∈
            {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} ∩
              GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          ∀ a : Fin k → Zd d (sz.L n),
            ‖AvecNg Cm s v K n (K n) σ ω a‖ ≤
              assembledRHSLinNg Cm s v K n k Cv ε Γ Λ Φ₁ Φ₂ Φ₃ D' D'' D_Y τK εq
                (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecNg Cm s v K n 0 σ ω b‖) a := by
  have : IsProbabilityMeasure Cm.Pp := by rw [hW'.2.1]; exact isProbabilityMeasure_pathP _
  have him1 : ∀ n, (Cm.m n).im ≤ 1 := fun n => NQGood1Gen_im_le_one (hm n)
  have hA' := assembledNg Cm hsize k εq hεq D_Y D₁ C_P C_K hCK0 hCK
  have hη := NQEndLinGen_eta_win hL hm
  have hEnv := fun σ : Fin k → Bool =>
    gridDriftNg_envelope_ev Cm μ k hk τK hτK hsize hKb hKK hη hs0 hsv hv1 hK0 hGD σ
  have hQV : QVPropagatedNg Cm lam' := qvPropagatedNg Cm E lam' hL hSeq
  have hSub : AzumaSubGNg Cm lam' s v K := azumaSubGNg Cm hW' s v K
  filter_upwards [hA', hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv, hWt, hKer, hW1, hWε, hdW,
    hAk, hδ] with n hAn hKNn hKUn hYn hEnvn hWtn hKern hW1n hWεn hdWn hAkn hδn
  intro σ hσ hsvn
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := nqEnd_step_le sz hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := nqEnd_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ => nqEnd_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (nqEnd_gridTime_le (hsv n) hKn hi).trans_lt (hv1 n)
  have hmono : ∀ i m, i ≤ m → m ≤ K n → gridTime s v K n i ≤ gridTime s v K n m :=
    fun i m him _ => ST_gridTime_mono s v K n (hsv n) him
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hW1' : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hW1n.le
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nqEnd_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hτmeas : ∀ j, MeasurableSet[filt sz j]
      {ω | j < nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω} :=
    nqLinExitMeasNg hL hW' s v K n k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D'
  have hmemG : ∀ (ω : PathΩ sz) (j : ℕ), j < nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω →
      GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v K n j ω) :=
    fun ω j hj => (mem_of_lt_nqLinExitTauNg hj).1
  have hmemL : ∀ (ω : PathΩ sz) (j : ℕ), j < nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω →
      Cm.Hpath s v K n j ω ∈ GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
    fun ω j hj => (mem_of_lt_nqLinExitTauNg hj).2
  -- the data of the assembly
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set τ : PathΩ sz → ℕ := nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n with hτdef
  set A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun ω => AvecNg Cm s v K n 0 σ ω with hA0
  set Dr : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    driftTensorNg Cm n (u j) (Cm.Hpath s v K n j ω) σ with hDr
  set Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω => ZvecNg Cm s v K n j σ ω with hZ
  set Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω => YvecNg Cm s v K n j σ ω with hY'
  set R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    predIncNg Cm s v K n j σ ω - ((Δ : ℝ) : ℂ) • Dr j ω with hR
  set Af : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun m ω =>
    Step2Gen_UN Cm.toFlowFM n σ (u 0) (u m) (A0 ω) +
      ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
        (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) with hAf
  set stepE : ℕ → ℝ := fun j => stepErrNg Cm.toFlowFM n k (u j) (u (j + 1)) Δ
    (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (u (j + 1)))⁻¹ ^ k) with hstepE
  have hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j) := fun j =>
    GridAssemblyGen_stronglyMeasurable_ZvecNg hL hW' s v K n j σ
  have hsubG : ∀ m ≤ K n, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
      SubGaussStopNg Cm σ u τ Z m a j (cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j) :=
    fun m hm' a j hj => subGaussStop_linNg (by omega) hk hSub hL hW' hQV hs0 hsv hv1 n (hm n) (hS n) hcmp hA hKern (hRow n)
      hCv (hwL n) hWtn hW1n hε0 hε1 hWεn hdWn hAkn hD'' hσ Γ Λ Φ Φ₁ Φ₂ Φ₃ (hΛ n) m hm' a j hj
      (hδn j (lt_of_lt_of_le hj hm'))
  have hu0K : u (K n) = v n := gridTime_last s v K n hKn
  have hu00 : u 0 = s n := ST_gridTime_zero s v K n
  have hbundle : GridAssemblyHypNg Cm σ u τ Δ (K n)
      (nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' D' u) A0 Af Dr Z Y R
      (kappaNonAltNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u) (epsNonAltNg Cv ((sz.W n : ℕ) : ℝ))
      (((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun j _ => dDriftLinNg Cm n (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
      (fun _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun m a j => cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j)
      (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE := {
    hKer := hRow n
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := fun m _ => Eventually.of_forall fun ω => rfl
    hκ0 := nonAlt_hκ0Ng k Cv (sz.lam n) _ ε hW0 (K n) u
    hε0 := nonAlt_hε0Ng Cv _ hW0 (K n)
    hker := nonAlt_hkerNg Cm.toFlowFM (by omega) hcmp hA hKern hCv hW1n hε0 hε1 hWεn hdWn hAkn hD' hu0 hmono
      (by rw [hu0K]; exact hwL n) (by rw [hu0K, hu00]; exact hWtn) hσ
    hδ0 := Real.rpow_nonneg hW0 _
    hA0cls := nonAlt_hA0clsNg (by omega) hW1' σ s v K Γ Λ Φ τ' D' D' le_rfl τ hmemG
    hdDrift0 := fun ω j hj => by
      have hη' := NQGood1Gen_eta_pos hL n (hu1 j hj.le)
      have hB := Sizes.STBctl_pos sz n (hu1 j hj.le)
      have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      unfold dDriftLinNg
      have h1 := hΓ n
      have h2 := hΦ₁ n
      have h3 := hΦ₂ n
      have h4 := hΦ₃ n
      positivity
    hδD0 := fun _ _ _ => Real.rpow_nonneg hW0 _
    hdrift := nqLin_hdriftNg hk σ s v K Γ Φ₁ Φ₂ Φ₃ τ hmemL
    hDcls := nonAlt_hDclsNg s v K (hsv n) (hv1 n) hW1' σ Γ Λ Φ τ' D' D' le_rfl τ hmemG
    hc_pos := cQVNonAltNg_sum_pos hL s v K n Cv ε (by omega) hsvn (hv1 n) hKn Γ Λ (hΛ n) D''
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := hYP τ hτmeas
    hstepErr0 := fun j hj => NQEndLinGen_stepErrNg_nonneg Cm hspec him1 n k (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
      (by
        have := NQGood1Gen_eta_pos hL n (hu1 (j + 1) hj)
        positivity)
    hR := (hEnvn σ).mono fun ω hω j hj _ b => by
      have h := hω j hj b
      simp only [hR, hDr, hstepE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, driftTensorNg]
      exact h }
  obtain ⟨G, hG, hGb⟩ := hAn (K n) σ u τ Δ
    (nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' D' u) A0 Af Dr Z Y R
    (kappaNonAltNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u)
    (epsNonAltNg Cv ((sz.W n : ℕ) : ℝ)) (((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun j _ => dDriftLinNg Cm n (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n))
    (fun _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun m a j => cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j)
    (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) stepE P hK1 hKUn hΔ hKΔ hP0 hPle
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) hτmeas hZmeas hsubG hbundle
  refine ⟨G, hG, fun ω hω hgood a => ?_⟩
  have hτeq : τ ω = K n := gridExitTauNg_eq_of_forall_mem hgood
  have hτpos : 0 < τ ω := by rw [hτeq]; omega
  have hb := hGb ω hω hτpos (K n) le_rfl a
  have hex := stoppedDuhamelNg_at Cm s v K n (hRow n).1 (hs0 n) (hsv n) (hv1 n) hKn σ τ (K n) ω (min_le_left _ _)
  have hAeq : Af (K n) ω = AvecNg Cm s v K n (K n) σ ω := by
    have hex' : AvecNg Cm s v K n (K n) σ ω =
        Step2Gen_UN Cm.toFlowFM n σ (u 0) (u (K n)) (AvecNg Cm s v K n 0 σ ω) +
          ∑ j ∈ Finset.range (K n), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u (K n))
            (predIncNg Cm s v K n j σ ω + martIncNg Cm s v K n j σ ω) := by
      rw [hτeq, min_self] at hex
      exact hex
    have hinner : ∀ j, ((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω =
        predIncNg Cm s v K n j σ ω + martIncNg Cm s v K n j σ ω := by
      intro j; funext b
      simp only [hR, hZ, hY', hDr, YvecNg, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hex']
    simp only [hAf, hτeq, min_self, hinner, hA0]
  rw [hAeq] at hb
  exact hb

end Assembly

/-! ## 4. Target 11 (c): the collapsed window, the union bound, the `Y`-moment constant -/

section Endpoint

variable {d : ℕ} {sz : Sizes d}

/-- If `v_n = s_n` the grid walk does not move: `Δ = 0` and every `H_j = H_0` (band `nqEnd_pathH_collapse`, `NQEndLin:967`; the walk of a
`WalkForm` carrier is a constant shift of the band walk). -/
private theorem NQEndLinGen_Hpath_collapse {Cm : Step2Mat sz} {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hW' : StepDecompGen_WalkForm Cm lam' Ψ)
    {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n = v n) (j : ℕ) (ω : PathΩ sz) :
    Cm.Hpath s v K n j ω = Cm.Hpath s v K n 0 ω := by
  have hΔ : gridStep s v K n = 0 := by unfold gridStep; rw [← hsv]; simp
  have hc : StepDecompGen_pathH sz lam' s v K n j ω = StepDecompGen_pathH sz lam' s v K n 0 ω := by
    unfold StepDecompGen_pathH pathH
    rw [hΔ]
    simp
    rfl
  rw [StepDecompGen_Hpath_eq hW', StepDecompGen_Hpath_eq hW', hc]

/-- **The collapsed window** (band `nqEnd_collapse`, `NQEndLin:978`; the case `v_n = s_n`, where `hc_pos` of the assembly fails): `H_K = H_0`
and `u_K = s`, so the initial bound `‖(𝓛-𝒦)_s‖ ≤ N^{ε₁} B_s^k` with `ε₁ ≤ ε₀`, `N ≥ 1`, `Λ ≥ 1`, `Φ_i ≥ 0` is the conclusion
`‖(𝓛-𝒦)_v‖ ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`. -/
private theorem NQEndLinGen_collapse {Cm : Step2Mat sz} {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hW' : StepDecompGen_WalkForm Cm lam' Ψ)
    {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hv1 : v n < 1)
    (hsv : s n = v n) {k : ℕ} {ε₁ ε₀ Λ Φ₁ Φ₂ Φ₃ : ℝ} (hε : ε₁ ≤ ε₀) (hΛ : 1 ≤ Λ) (hΦ₁ : 0 ≤ Φ₁)
    (hΦ₂ : 0 ≤ Φ₂) (hΦ₃ : 0 ≤ Φ₃) (ω : PathΩ sz) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (hinit : ‖STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) :
    ‖STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃) * (sz.Bctl n (v n)) ^ k := by
  rw [NQEndLinGen_Hpath_collapse hW' hsv (K n) ω, ← hsv]
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nqEnd_one_le_size sz n
  have hs1 : s n < 1 := by rw [hsv]; exact hv1
  have hB : 0 ≤ (sz.Bctl n (s n)) ^ k := pow_nonneg (Sizes.STBctl_pos sz n hs1).le _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ :=
    Real.rpow_le_rpow_of_exponent_le hN1 hε
  have h2 : 1 ≤ Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃ := by
    have := Real.one_le_rpow hΛ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have h3 : ((sz.size n : ℕ) : ℝ) ^ ε₀ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ *
      (Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃) :=
    le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) h2
  exact hinit.trans (mul_le_mul_of_nonneg_right (h1.trans h3) hB)

/-- **The uniform `Y` moments for all signs with one `C_P`** (before the grid `K`; band `nqEnd_yMomentsMax`, `NQEndLin:1028`): the maximum over the
`2^k` sign vectors of the constants of `yMomentsUnifNg` serves every sign. -/
private theorem NQEndLinGen_yMomentsMax (Cm : Step2Mat sz) {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n) {κm τR : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    {s v : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hsize : sz.SizeTendsto) (hrange : sz.RangeCond τR v) (k : ℕ) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → ∀ σ : Fin k → Bool,
      ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
        ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
          YMomentBoundsNg Cm σ (gridTime s v K n) τ (K n)
            (fun j ω => YvecNg Cm s v K n j σ ω)
            (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2) := by
  choose CP hCP0 hCPev using fun σ : Fin k → Bool =>
    yMomentsUnifNg hL hW' hRow κm τR s v hspec hs0 hsv hv1 hsize hrange k σ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty CP,
    (hCP0 (fun _ => true)).trans (Finset.le_sup' CP (Finset.mem_univ _)), fun K hK0 σ => ?_⟩
  filter_upwards [hCPev σ K hK0] with n hn
  obtain ⟨P, hP0, hPle, hτ⟩ := hn
  exact ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (nqEnd_one_le_size sz n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), hτ⟩

end Endpoint

/-! ## 5. Target 12: the grid endpoint `nqGridEndLinNg`

Band `nqGridEndLinN` (`NQEndLin:1067`).  Exponents (fixed order, after the carrier): `Λg = 𝔡⁻¹`, `C = Cv` (the vocabulary constant, `Ck ≤ Cv`),
`ε₀' = min ε₀ 1`, `ε₁ = εq = ε₀'/8`, `ε = min (ε₀'/(8Cv)) (1/2)`, `τ' = ε/2`, `D'' = Cv + k + 2 + (4k+2)/𝔠`, `D' = D'' + 1`, `τ_K = 1`,
`D_Y = D_t = k + 1`, `C_P^* = max_σ C_P(σ)` (`yMomentsUnifNg`), `C_K = D₁ + 2 C_P^* + 6k + 20 + D''`. -/

section Endpoint5

variable {d : ℕ} {sz : Sizes d}

/-- **`nqGridEndLinNg`: the non-alternating grid endpoint with the linear right side over a carrier** (band `nqGridEndLinN`, `lem:STOeq_NQ`,
`3_5:1136`, proof `3_5:1152-1180`).  For every length `k ≥ 2`, kernel constant `Ck` (D1: `NQGoodGen_KerNAL` at the kernel coupling `gK`,
eventually), vocabulary constant `Cv ≥ Ck` (`Cv > Ck` unless the comparison constant `A` of R1 is `1`), deterministic levels `Λ ≥ 0` (`≥ 1`
eventually), `Φ₁, Φ₂, Φ₃ ≥ 0`, end time `v ∈ [s,t]`, final loss `ε₀ > 0` and failure exponent `D₁ > 0` there are exponents
`ε₁, τ', D', C_K` such that, for every crude level `Φc` of `GoodSetNg` and every grid `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`, eventually there is an
event `G`, `P(Gᶜ) ≤ N^{-D₁}`, on which: if the carrier walk is in `GoodSetNg(N^{ε₁}, Λ, Φc, τ', D') ∩ GoodLinNg(N^{ε₁}, Φ₁, Φ₂, Φ₃)` at every
`j ≤ K_n` and the initial loops satisfy `|(𝓛-𝒦)_{s,σ,a}| ≤ N^{ε₁} B_s^k`, then `|(𝓛-𝒦)_{v,σ,a}(H_{K_n})| ≤ N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`
for every non-alternating `σ` and label `a`.  `|E n| ≤ 2 - κ` is `DecayGen_Spec` and `‖Cm.m n‖ ≤ 1` (D3); `STKbound` is the pin `STKboundgL`;
the drift enters per index (D5: the classes `Expand`, `KLoop`, `KTwo`, `UStep` eventually, the link and the row sums); R1 is `hcmp`, `hA`. -/
theorem nqGridEndLinNg (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {κm 𝔠 τ 𝔡 A : ℝ} (s t : ℕ → ℝ) (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτ : 0 < τ) (h𝔡 : 0 < 𝔡)
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n))
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hExp : ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand Cm s' t' K' n)
    (hKL : ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop Cm n) (hKT : ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo Cm n)
    (hU : ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep Cm.toFlowFM n)
    (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τ t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A) :
    ∀ k : ℕ, 2 ≤ k → ∀ Ck Cv : ℝ, 0 < Ck → Ck ≤ Cv → (Ck < Cv ∨ A = 1) →
      (∀ᶠ n : ℕ in atTop, NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n) →
    ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, Cm.Hpath s v K n j ω ∈
            {H | GoodSetNg Cm n (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φc n) τ' D' H} ∩
              GoodLinNg Cm n (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                (sz.Bctl n (v n)) ^ k := by
  intro k hk Ck Cv hCk hCkCv hAk0 hKer Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  classical
  have hd1 : 1 ≤ d := by omega
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have him1 : ∀ n, (Cm.m n).im ≤ 1 := fun n => NQGood1Gen_im_le_one (hm n)
  -- the coupling window `0 < lam n ≤ Λg = 𝔡⁻¹`
  obtain ⟨Λg, hΛgdef⟩ : ∃ Λg : ℝ, Λg = 𝔡⁻¹ := ⟨_, rfl⟩
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg := by
    rw [hΛgdef]
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  -- the range exponent of the end time, the `Y`-moment constant (one for all signs, before the grid)
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : sz.RangeCond (min τ 1) v := nqEnd_rangeCond_mono sz (min_le_left _ _) hvt hrange
  obtain ⟨Cmax, hCmax0, hYmax⟩ := NQEndLinGen_yMomentsMax Cm hL hW' hRow hspec hs0 hsv hv1 hsize hrangeV k
  -- the numerical constants, in the fixed order `Cv → ε₀' → ε₁ → ε → D'' → D' → C_P → C_K`
  obtain ⟨e0, he0def⟩ : ∃ e0 : ℝ, e0 = min ε₀ 1 := ⟨_, rfl⟩
  have he0 : 0 < e0 := by rw [he0def]; exact lt_min hε₀ one_pos
  have he01 : e0 ≤ 1 := by rw [he0def]; exact min_le_right _ _
  have he0le : e0 ≤ ε₀ := by rw [he0def]; exact min_le_left _ _
  have hC : 0 < Cv := lt_of_lt_of_le hCk hCkCv
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (e0 / (8 * Cv)) (1 / 2) := ⟨_, rfl⟩
  obtain ⟨D'', hD''def⟩ : ∃ D'' : ℝ, D'' = Cv + k + 2 + (4 * k + 2) / 𝔠 := ⟨_, rfl⟩
  obtain ⟨hε0, hε1, hCε0, hCε, hD''k, hD''0, E1, E2, E3, hCD', E4, F1, F2, F3, G1, G2, G3, H1,
    H2⟩ := nqEnd_arith k hk h𝔠 hC he0 he01 hεdef hD''def
  obtain ⟨C_K, hCKdef⟩ : ∃ C_K : ℝ, C_K = D₁ + 2 * Cmax + 6 * k + 20 + D'' := ⟨_, rfl⟩
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hCK0 : 0 ≤ C_K := by rw [hCKdef]; linarith
  refine ⟨e0 / 8, ε / 2, D'' + 1, C_K, by linarith, by linarith, by linarith, hCK0, ?_⟩
  intro Φc K hK0 hKN hKU
  -- the exponent constraints on `C_K`
  have hθ1 : 1 - min τ 1 ≤ 1 := by linarith
  have hθk1 : (4 * (k : ℝ) + 8) * (1 - min τ 1) ≤ 4 * k + 8 :=
    mul_le_of_le_one_right (by positivity) hθ1
  have hθk2 : 5 * (k : ℝ) * (1 - min τ 1) ≤ 5 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hθk3 : 2 * (k : ℝ) * (1 - min τ 1) ≤ 2 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hC1 : (D₁ + 1) + 4 * ((k : ℝ) + 1) + (k : ℝ) + 2 * Cmax + 8 ≤ C_K := by
    rw [hCKdef]; linarith
  have hC2 : 8 + (4 * (k : ℝ) + 8) * (1 - min τ 1) + 2 * ((k : ℝ) + 1) < C_K := by
    rw [hCKdef]; linarith
  have hC3 : 3 + 4 * (1 : ℝ) + 5 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 1) < C_K := by
    rw [hCKdef]; linarith
  have hC4 : 2 * (1 - min τ 1) + 1 + 2 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 1) < C_K := by
    rw [hCKdef]; linarith
  have hC5 : 1 - min τ 1 < C_K := by rw [hCKdef]; linarith
  have hC6 : D'' + 2 * (k : ℝ) + 5 ≤ C_K := by rw [hCKdef]; linarith
  have hC7 : 1 ≤ C_K := by rw [hCKdef]; linarith
  -- the eventual regime facts
  have hη := NQEndLinGen_ev_hη Cm hspec him1 hsize hτR hrangeV
  have hδ := NQEndLinGen_ev_hδ Cm hspec him1 hd1 hsize h𝔠 hband k hs0 hsv hv1 hK0 hη hD''0 hC6 hKN
  have hlogR := nqBudget_merged_inputsg Cm (κm := κm) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := (k : ℝ) + 1) (s := s) (v := v) (K := K) k hspec him1 hτR hτR1 one_pos
    (by linarith) hk hsize hs0 hsv hv1 hK0 hrangeV hC2 hC3 hC4 hC5 hKN
  have hWt' : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n) := by
    filter_upwards [hWt] with n hn
    refine hn.trans ?_
    have h1 : 0 < 1 - s n := by linarith [hst n, ht1 n]
    exact div_le_div_of_nonneg_right (by linarith [hvt n]) h1.le
  have hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := fun n => by
    have := hcase n
    linarith [hvt n]
  have hW1 : ∀ᶠ n : ℕ in atTop, 1 < ((sz.W n : ℕ) : ℝ) := by
    filter_upwards [nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband one_pos 2] with n hn
    rw [Real.rpow_one] at hn
    linarith
  have hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
    nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband hε0 4
  have hdW : ∀ᶠ n : ℕ in atTop,
      (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
    filter_upwards [nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband (show 0 < ε / 2 by linarith) ((d : ℝ) * Real.sqrt A)]
      with n hn
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ (ε / 2)
        ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0 _)
      _ = ((sz.W n : ℕ) : ℝ) ^ ε := by
          rw [← Real.rpow_add' hW0 (by linarith)]; congr 1; ring
  have hAk : ∀ᶠ n : ℕ in atTop, A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε) := by
    rcases hAk0 with hlt | hA1
    · have hpos : 0 < (Cv - Ck) * ε := mul_pos (sub_pos.2 hlt) hε0
      exact nqEnd_ev_W_rpow_ge sz hsize h𝔠 hband hpos (A ^ (k - 1))
    · filter_upwards [hW1] with n hn
      rw [hA1, one_pow]
      exact Real.one_le_rpow hn.le (mul_nonneg (sub_nonneg.2 hCkCv) hε0.le)
  -- the absorption lemmas of `budgetNonAltLinNg`
  have ha1 := nqEnd_ev_ha1 sz hd1 hsize hCε0 E1
  have ha2 := NQEndLinGen_ev_ha2 Cm hspec him1 hd1 hsize k hCε0 E2
  have ha3 := NQEndLinGen_ev_ha3 Cm hspec him1 hd1 hsize k hCε0 E3
  have he1 := nqEnd_ev_he1 sz hsize hband (k := k) hCD' E4
  have he2 := NQEndLinGen_ev_he2 hsize hband (by omega) hlam F1 F2 F3 G1 G2 G3 H1
  have he3 := nqEnd_ev_he4 sz hsize k (D := (k : ℝ) + 1) H2
  have he4 := nqEnd_ev_he4 sz hsize k (D := (k : ℝ) + 1) H2
  have hun := nqEnd_ev_union sz hsize k D₁
  -- the drift (D5): the per-index classes give `GridDriftNgAt` for this grid
  have hGD : ∀ᶠ n : ℕ in atTop, GridDriftNgAt Cm s v K n := by
    filter_upwards [hExp, hKL, hKT, hU] with n h1 h2 h3 h4
    exact gridDriftNgAt_of_classes hL hW' s v K n (h1 s v K) h2 h3 h4 (hS n)
      (fun w _ k σ a => hKK n w k σ a) (hs0 n) (hsv n) (hv1 n) (hK0 n)
  -- the assembly at the exit time `nqLinExitTauNg` (per sign vector, `D₁ + 1`)
  have hΓ0 : ∀ n, 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) := fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hAsm := NQEndLinGen_assembly Cm μ k hd hk hL hW' hspec hm hSeq hS hRow hKK hKb hGD hsize hs0 hsv hv1 hK0
    (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φc Φ₁ Φ₂ Φ₃ hΓ0 hΛ0 hΦ₁ hΦ₂ hΦ₃
    (A := A) (Ck := Ck) (Cv := Cv) (ε := ε) (τ' := ε / 2) (D' := D'' + 1) (D'' := D'') (D_Y := (k : ℝ) + 1) (τK := 1)
    (εq := e0 / 8) (D₁ := D₁ + 1) (C_P := Cmax) (C_K := C_K) hcmp hA hCkCv hε0 hε1 hD''k (by linarith) one_pos
    (by linarith) hCK0 hC1 hKN hKU (hYmax K hK0) hwL hWt' hKer hW1 hWε hdW hAk hδ
  filter_upwards [hAsm, hη, hlogR, ha1, ha2, ha3, he1, he2, he3, he4, hΛ1, hun, hKN] with n hAsmn
    hηn hlogRn ha1n ha2n ha3n he1n he2n he3n he4n hΛ1n hunn hKNn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nqEnd_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  by_cases hsvn : s n = v n
  · -- the collapsed window `v_n = s_n`: `G = univ`
    refine ⟨Set.univ, ?_, fun ω _ _ hinit' σ hσ a => ?_⟩
    · rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · exact NQEndLinGen_collapse hW' (hv1 n) hsvn (by linarith) hΛ1n (hΦ₁ n) (hΦ₂ n) (hΦ₃ n) ω σ a
        (hinit' σ hσ a)
  · have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
    have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 (hK0 n)
    have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
    have hη0 : 0 ≤ (Cm.eta n (v n))⁻¹ := inv_nonneg.2 (NQGood1Gen_eta_pos hL n (hv1 n)).le
    have hΔη := nqEnd_hΔη sz (C_K := C_K) (η := Cm.eta n (v n)) hC7 hKNn hvs hη0 hηn
    -- the events, one per non-alternating sign vector
    have hAsmσ := fun σ : {σ : Fin k → Bool // ∃ i, σ i = σ (finRotate k i)} =>
      hAsmn σ.1 σ.2 hlt
    choose Gs hGsP hGsb using hAsmσ
    refine ⟨⋂ σ, Gs σ, ?_, ?_⟩
    · -- the union bound over the `≤ 2^k` sign vectors
      have : IsProbabilityMeasure Cm.Pp := by rw [hW'.2.1]; exact isProbabilityMeasure_pathP _
      have hcompl : (⋂ σ, Gs σ)ᶜ = ⋃ σ, (Gs σ)ᶜ := by rw [Set.compl_iInter]
      rw [hcompl]
      calc Cm.Pp.real (⋃ σ, (Gs σ)ᶜ) ≤ ∑ σ, Cm.Pp.real (Gs σ)ᶜ :=
            measureReal_iUnion_fintype_le _
        _ ≤ ∑ _σ : {σ : Fin k → Bool // ∃ i, σ i = σ (finRotate k i)},
              ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := Finset.sum_le_sum fun σ _ => hGsP σ
        _ = (Fintype.card {σ : Fin k → Bool // ∃ i, σ i = σ (finRotate k i)} : ℝ) *
              ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp
        _ ≤ (2 : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN0.le _)
            have h1 := Fintype.card_subtype_le (fun σ : Fin k → Bool => ∃ i, σ i = σ (finRotate k i))
            have h2 : Fintype.card (Fin k → Bool) = 2 ^ k := by simp
            rw [h2] at h1
            exact_mod_cast h1
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := hunn
    · intro ω hω hgood hinit' σ hσ a
      have hωσ : ω ∈ Gs ⟨σ, hσ⟩ := Set.mem_iInter.1 hω ⟨σ, hσ⟩
      have hb := hGsb ⟨σ, hσ⟩ ω hωσ hgood a
      have hX0 : (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecNg Cm s v K n 0 σ ω b‖) ≤
          ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) * (sz.Bctl n (s n)) ^ k := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        have h := hinit' σ hσ b
        have e : ‖AvecNg Cm s v K n 0 σ ω b‖ = ‖STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b‖ := by
          simp only [AvecNg, ST_gridTime_zero]
        rw [e]
        exact h
      have hbud := budgetNonAltLinNg Cm hL s v K n k Cv ε
        (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φ₁ Φ₂ Φ₃ (D'' + 1) D'' ((k : ℝ) + 1)
        ((k : ℝ) + 1) 1 (e0 / 8) e0 (e0 / 8)
        (Finset.univ.sup' Finset.univ_nonempty fun b => ‖AvecNg Cm s v K n 0 σ ω b‖) a hk
        (by linarith) (hm n) (hs0 n) (hsv n) (hv1 n) (hK0 n) hηn hΔη rfl hΛ1n (hΦ₁ n) (hΦ₂ n)
        (hΦ₃ n) hlogRn.1 hX0 hlogRn.2 ha1n ha2n ha3n he1n he2n he3n he4n
      have hlk : ‖STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ a‖ =
          ‖AvecNg Cm s v K n (K n) σ ω a‖ := by
        simp only [AvecNg, gridTime_last s v K n (hK0 n)]
      rw [hlk]
      refine hb.trans (hbud.trans ?_)
      have hB : 0 ≤ (sz.Bctl n (v n)) ^ k := pow_nonneg (Sizes.STBctl_pos sz n (hv1 n)).le _
      have hS' : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have := hΦ₁ n
        have := hΦ₂ n
        have := hΦ₃ n
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hN1 he0le) hS') hB

end Endpoint5

/-! ## 6. The band re-derivation of `nqGridEndLinN` -/

section BandReDerivation

/-- **Band re-derivation of `nqGridEndLinN`** (`NQEndLin:1067`, the same statement): the merged band theorem from `nqGridEndLinNg` at the
carrier `bandStep2Mat sz E` with the law `seqP sz`: `A = 1`, `gK = sz.lam`, `Cv = Ck = nqGood1C d k 𝔡⁻¹ (min κ (4/5))`; `LoopForm`, `WalkForm`,
the spectral data `√κ/2`, `‖mE‖ = 1`, the row sums, the kernel class and the four drift classes are the band lemmas; `STKbound` is `stKbound_holds`;
D1 is `nqGoodGen_kerNAL_band_at`. -/
theorem nqGridEndLinN_of_gen :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
    ∀ k : ℕ, 2 ≤ k →
    ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                (sz.Bctl n (v n)) ^ k := by
  intro d sz κ 𝔠 τ 𝔡 E s t hd hκ h𝔠 hτ h𝔡 hsize hband hWO hE hs0 hst ht1 hcase hrange hWt k hk
    Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  obtain ⟨κ', hκ'def⟩ : ∃ κ' : ℝ, κ' = min κ (4 / 5) := ⟨_, rfl⟩
  obtain ⟨Λg, hΛgdef⟩ : ∃ Λg : ℝ, Λg = 𝔡⁻¹ := ⟨_, rfl⟩
  have hκ' : 0 < κ' := by rw [hκ'def]; exact lt_min hκ (by norm_num)
  have hκm : ∀ n, κ' ≤ (mE (E n)).im := fun n => by
    rw [hκ'def]; exact RBM.Ind.nqGood1_mE_im_ge hκ (hE n)
  have hΛg : 0 < Λg := by rw [hΛgdef]; exact inv_pos.2 h𝔡
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg := by
    rw [hΛgdef]
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  have hKb : sz.STKbound E := stKbound_holds sz hd hκ hΛg hsize (Eventually.of_forall hE) hlam
  have hKer : ∀ᶠ n : ℕ in atTop, NQGoodGen_KerNAL (bandStep2Mat sz E).toFlowFM sz.lam k (nqGood1C d k Λg κ') n := by
    filter_upwards [hlam] with n hn
    exact nqGoodGen_kerNAL_band_at sz E hd hk hΛg hκ' n hn.1 hn.2 (hE2 n).le (hκm n)
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := nqGridEndLinNg (bandStep2Mat sz E) (Sizes.seqP sz) (E := E)
    (lam' := sz.lam) (Ψ := fun _ => 0) (gK := sz.lam) (A := 1) (κm := Real.sqrt κ / 2) s t hd h𝔠 hτ h𝔡
    (stepDecompGen_loopForm_band sz E hE2) (stepDecompGen_walkForm_band sz E) (DecayGen_bandSpec sz hκ hE)
    (fun n => (norm_mE (hE2 n).le).le) (fun n => rfl) (fun n a => hierDriftGen_SB_row sz n a)
    (fun n => gridRepTailGen_ker_band sz E n (hE2 n).le) (fun n w k σ a => rfl) hKb
    (Eventually.of_forall fun n s' t' K' => hierDriftGen_expand_band sz E hE2 s' t' K' n)
    (Eventually.of_forall (hierDriftGen_kLoop_band sz E hE2)) (Eventually.of_forall (hierDriftGen_kTwo_band sz E hE2))
    (Eventually.of_forall (hierDriftGen_uStep_band sz E hE2)) hsize hband hWO hs0 hst ht1 hcase hrange hWt
    (fun n => ⟨mul_self_nonneg _, le_rfl, (one_mul _).ge⟩) le_rfl k hk (nqGood1C d k Λg κ') (nqGood1C d k Λg κ')
    (RBM.Ind.nqGood1C_pos hd hk hΛg hκ') le_rfl (Or.inr rfl) hKer Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, fun Φc K hK0 hKN hKU => ?_⟩
  filter_upwards [hend Φc K hK0 hKN hKU] with n ⟨G, hG, hGb⟩
  refine ⟨G, hG, fun ω hω hgood hinit σ hσ a => ?_⟩
  exact hGb ω hω (fun j hj => ⟨(bandStep2_GoodSetN sz E n _ k _ _ _ τ' D' _).1 (hgood j hj).1, (hgood j hj).2⟩) hinit σ hσ a

end BandReDerivation

/-! ## 7. Compiled nonempty instances (`d = 3`, band carrier `bandStep2Mat sz0 Einst`)

Data of the band instances `NQEndLinInst` (`Induction/NQEndLin.lean:1277-1592`, public facts by name): `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`,
`lam = 1/64`), `E = Einst ≡ 1/2`, `κ = 1` (`κ' = min κ (4/5)`), `s = sInst ≡ 0`, `t = tInst ≡ 1/16`, `v = vg ≡ 1/32` (`Δ > 0` on every grid
`KC C_K`), `τ = 1/2`, `k ≥ 2` arbitrary, levels `Λ = 3`, `Φ₁ = Φ₃ = 1`, `Φ₂ = 12`, `ε₀ = 1/10`, `D₁ = 1`.  The kernel constant is
`Ck = nqGood1C 3 k 10 κ'` (abstract, `> 0`); `A = 1`, `Cv = Ck`.  Every hypothesis is discharged (`STKboundgL` by `stKbound_holds`; the drift classes,
the kernel class, `LoopForm`, `WalkForm`, the spectral data by the band lemmas). -/

section Instances

namespace NQEndLinGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst
open RBM.Ind.NQEndLinInst (KC KC_ne_zero KC_low KC_up window_nondegenerate hE_i hlam_i WtInst rangeCond_tInst κi sInst_le_tInst
  vg_le_tInst)

private abbrev Cm1 : Step2Mat sz0 := bandStep2Mat sz0 Einst

/-- **`nqGridEndLinNg` at the data**: the conclusion is unfolded to the eventual event statement at the grid `KC C_K` (`N^{C_K} ≤ K_n ≤
⌈N^{C_K}⌉`) for the exponents the theorem produces, at one size index, on the non-collapsed window (`window_nondegenerate`). -/
private theorem nqEndLinNg_instance (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, sInst n < vg n ∧ 0 < gridStep sInst vg (KC C_K) n ∧
        ∃ G : Set (PathΩ sz0), Cm1.Pp.real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KC C_K n, Cm1.Hpath sInst vg (KC C_K) n j ω ∈
            {H | GoodSetNg Cm1 n (gridTime sInst vg (KC C_K) n j) k (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Λ3 n) (Φ1 n) τ' D' H} ∩
              GoodLinNg Cm1 n (gridTime sInst vg (KC C_K) n j) k (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Φ1 n) (12 : ℝ) (Φ1 n)) →
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd 3 (sz0.L n),
            ‖STLKMg Cm1 n (sInst n) (Cm1.Hpath sInst vg (KC C_K) n 0 ω) σ a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ ε₁ * (sz0.Bctl n (sInst n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd 3 (sz0.L n),
            ‖STLKMg Cm1 n (vg n) (Cm1.Hpath sInst vg (KC C_K) n (KC C_K n) ω) σ a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (Λ3 n ^ ((1 : ℝ) / 2) + Φ1 n + 12 + Φ1 n) *
                (sz0.Bctl n (vg n)) ^ k := by
  have hκ' : 0 < κi := lt_min one_pos (by norm_num)
  have hKb : sz0.STKbound Einst := stKbound_holds sz0 (by norm_num) one_pos (by norm_num : (0 : ℝ) < 10) sz0_tendsto
    (Eventually.of_forall hE_i) hlam_i
  have hKer : ∀ᶠ n : ℕ in atTop, NQGoodGen_KerNAL Cm1.toFlowFM sz0.lam k (nqGood1C 3 k 10 κi) n := by
    filter_upwards [hlam_i] with n hn
    exact nqGoodGen_kerNAL_band_at sz0 Einst le_rfl hk (by norm_num) hκ' n hn.1 hn.2 (Einst_abs_lt n).le
      (RBM.Ind.NQEndLinInst.hκm_i n)
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := nqGridEndLinNg Cm1 (Sizes.seqP sz0) (E := Einst)
    (lam' := sz0.lam) (Ψ := fun _ => 0) (gK := sz0.lam) (A := 1) (κm := Real.sqrt 1 / 2) sInst tInst (𝔠 := 1 / 6) (τ := 1 / 2)
    (𝔡 := 1 / 10) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (stepDecompGen_loopForm_band sz0 Einst Einst_abs_lt) (stepDecompGen_walkForm_band sz0 Einst)
    (DecayGen_bandSpec sz0 one_pos hE_i) (fun n => (norm_mE (Einst_abs_lt n).le).le) (fun n => rfl)
    (fun n a => hierDriftGen_SB_row sz0 n a) (fun n => gridRepTailGen_ker_band sz0 Einst n (Einst_abs_lt n).le)
    (fun n w k σ a => rfl) hKb
    (Eventually.of_forall fun n s' t' K' => hierDriftGen_expand_band sz0 Einst Einst_abs_lt s' t' K' n)
    (Eventually.of_forall (hierDriftGen_kLoop_band sz0 Einst Einst_abs_lt))
    (Eventually.of_forall (hierDriftGen_kTwo_band sz0 Einst Einst_abs_lt))
    (Eventually.of_forall (hierDriftGen_uStep_band sz0 Einst Einst_abs_lt)) sz0_tendsto sz0_bandwidth sz0_WO
    sInst_nonneg sInst_le_tInst tInst_lt_one sz0_caseI rangeCond_tInst WtInst
    (fun n => ⟨mul_self_nonneg _, le_rfl, (one_mul _).ge⟩) le_rfl k hk (nqGood1C 3 k 10 κi) (nqGood1C 3 k 10 κi)
    (RBM.Ind.nqGood1C_pos le_rfl hk (by norm_num) hκ') le_rfl (Or.inr rfl) hKer Λ3 Φ1 (fun _ => 12) Φ1
    (fun _ => by norm_num) (Eventually.of_forall fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) vg sInst_le_vg vg_le_tInst (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend Φ1 (KC C_K) (KC_ne_zero C_K)
    (Eventually.of_forall (KC_low C_K)) (Eventually.of_forall (KC_up C_K))).exists
  exact ⟨n, (window_nondegenerate C_K n).1, (window_nondegenerate C_K n).2, G, hG, hGb⟩


/-! ### D5 at the data -/

private theorem hKb1 : sz0.STKbound Einst := stKbound_holds sz0 (by norm_num) one_pos (by norm_num : (0 : ℝ) < 10) sz0_tendsto
  (Eventually.of_forall hE_i) hlam_i

private theorem hL1 : StepDecompGen_LoopForm Cm1 Einst := stepDecompGen_loopForm_band sz0 Einst Einst_abs_lt

private theorem hW1 : StepDecompGen_WalkForm Cm1 sz0.lam (fun _ => 0) := stepDecompGen_walkForm_band sz0 Einst

private theorem hm1 : ∀ n, ‖Cm1.m n‖ ≤ 1 := fun n => (norm_mE (Einst_abs_lt n).le).le

/-- **D5, `gridDriftNgAt_of_classes`** at the data (`k` arbitrary, window `s ≡ 0`, `t ≡ 1/16`, `K ≡ 4`, size index `n`): the per-index classes
(`Expand`, `KLoop`, `KTwo`, `UStep`, the row sums, the link) are the band lemmas; `GridDriftNgAt` holds at every `n`. -/
example (n : ℕ) : GridDriftNgAt Cm1 sInst tInst (fun _ => 4) n :=
  gridDriftNgAt_of_classes hL1 hW1 sInst tInst (fun _ => 4) n (hierDriftGen_expand_band sz0 Einst Einst_abs_lt _ _ _ n)
    (hierDriftGen_kLoop_band sz0 Einst Einst_abs_lt n) (hierDriftGen_kTwo_band sz0 Einst Einst_abs_lt n)
    (hierDriftGen_uStep_band sz0 Einst Einst_abs_lt n) (fun a => hierDriftGen_SB_row sz0 n a)
    (hierDriftGen_kLink_band sz0 Einst n) (sInst_nonneg n) (sInst_le_tInst n) (tInst_lt_one n) (by norm_num)

/-- **D5, `gridDriftNg_envelope_ev`** at the data (`k = 3`, `τ_K = 1/2`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 4`, every sign vector): the drift premise is
`∀ᶠ n, GridDriftNgAt` from the classes; `STKboundgL` is `stKbound_holds`; nothing is left open. -/
example (σ : Fin 3 → Bool) :=
  gridDriftNg_envelope_ev Cm1 (Sizes.seqP sz0) 3 (by norm_num) (1 / 2) (by norm_num) (s := sInst) (t := tInst) (K := fun _ => 4)
    sz0_tendsto hKb1 (fun n w k σ a => rfl) (NQEndLinGen_eta_win hL1 hm1) sInst_nonneg sInst_le_tInst tInst_lt_one
    (fun _ => by norm_num)
    (Eventually.of_forall fun n => gridDriftNgAt_of_classes hL1 hW1 sInst tInst (fun _ => 4) n
      (hierDriftGen_expand_band sz0 Einst Einst_abs_lt _ _ _ n) (hierDriftGen_kLoop_band sz0 Einst Einst_abs_lt n)
      (hierDriftGen_kTwo_band sz0 Einst Einst_abs_lt n) (hierDriftGen_uStep_band sz0 Einst Einst_abs_lt n)
      (fun a => hierDriftGen_SB_row sz0 n a) (hierDriftGen_kLink_band sz0 Einst n) (sInst_nonneg n) (sInst_le_tInst n)
      (tInst_lt_one n) (by norm_num)) σ

/-- **D5, the merged recovery** `gridDriftNg_envelope_of_merged` at the data: `GridDriftNg` is `gridDriftNg` with every class at the band. -/
example (σ : Fin 3 → Bool) :=
  gridDriftNg_envelope_of_merged Cm1 (Sizes.seqP sz0) 3 (by norm_num) (1 / 2) (by norm_num) (s := sInst) (t := tInst)
    (K := fun _ => 4) sz0_tendsto hKb1 (fun n w k σ a => rfl) (NQEndLinGen_eta_win hL1 hm1) sInst_nonneg sInst_le_tInst
    tInst_lt_one (fun _ => by norm_num)
    (gridDriftNg hL1 hW1 _ _ _ (fun n => hierDriftGen_expand_band sz0 Einst Einst_abs_lt _ _ _ n)
      (hierDriftGen_kLoop_band sz0 Einst Einst_abs_lt) (hierDriftGen_kTwo_band sz0 Einst Einst_abs_lt)
      (hierDriftGen_uStep_band sz0 Einst Einst_abs_lt) (fun n a => hierDriftGen_SB_row sz0 n a)
      (hierDriftGen_kLink_band sz0 Einst)) σ

/-- The merged pin is the form at every index (`gridDriftNg_iff_at` at the data). -/
example : GridDriftNg Cm1 sInst tInst (fun _ => 4) ↔ ((∀ n, 0 ≤ sInst n) → (∀ n, sInst n ≤ tInst n) → (∀ n, tInst n < 1) →
    (∀ n, (fun _ => 4 : ℕ → ℕ) n ≠ 0) → ∀ n, GridDriftNgAt Cm1 sInst tInst (fun _ => 4) n) :=
  gridDriftNg_iff_at Cm1 sInst tInst (fun _ => 4)

/-- The instance at `k = 2` (no `l ∈ [3,k]`; the sign vectors `σ` of length `2` with `σ_0 = σ_1`). -/
example := nqEndLinNg_instance 2 le_rfl

/-- The instance at `k = 3`. -/
example := nqEndLinNg_instance 3 (by norm_num)

/-- The instance at `k = 4`. -/
example := nqEndLinNg_instance 4 (by norm_num)

end NQEndLinGenCheck

end Instances

end RBM.BA

end
