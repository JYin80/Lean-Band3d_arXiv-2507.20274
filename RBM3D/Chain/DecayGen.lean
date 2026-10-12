/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.DecayLoopB
import RBM3D.Chain.Step2Gen

/-!
# `lem_decayLoop` over the flow carrier (BA-T row T7a, ticket T2454)

Design gate `docs/reports/T2454-prove.md` (a)-(a'''), probe `RBM3D/Probe/T2454Pins.lean` (branch
`t/T2454`).  The band files `Induction/DecayLoopA.lean`, `DecayLoopB.lean` are **not** edited: this
file states their generic forms over a carrier `C : FlowFM sz` and a law `μ`, and bridges the two.
There is no `BA/` import (the BA readings are in the leaf `Chain/DecayGenTw.lean`).

* **Pins.** `STDecayLoopUgL` (target 1; the body of conjunct 4 of `twSteps`,
  `BA/TwistPins.lean:139-142`), `STDecayLoopPTgL` (target 2), `STKcalDecaygL` (target 3; the far
  decay of `𝒦`, without the energy), `STDecayLoopAtgL` (target 4, the pin of `stDecayLoopAtgL_of`).
* **Carrier facts that replace band objects** (hypothesis predicates, not fields):
  `DecayGen_Spec C κm` (F3: `0 < κm ≤ Im m`, `η_t = (1 - t) Im m`) and `DecayGen_WardPair C` (F4:
  the Ward pair of `DecayLoopB_pair`, `3_5:1126` proof).  Band readings `DecayGen_bandSpec`
  (`κm = √κ/2`), `DecayGen_bandWardPair`; BA readings in `Chain/DecayGenTw.lean`.
* **Theorems.** `stDecayLoopAtgL_of` (target 4, band `stDecayLoopAt_holds`, `DecayLoopA.lean:938`),
  `stDecayLoopPTgL_of_step2` (target 5, band `stDecayLoopPT_of_step2`, `:970`) and
  `stDecayLoopUgL_of_step2` (target 6, band `stDecayLoopU_of_step2`, `DecayLoopB.lean:1637`).  The
  three proofs share one deterministic step `DecayGen_step` (the pointwise chain of
  `DecayLoopA_main`/`DecayLoopB_main_u`; paper `3_5:1126`).
* **Bridges.** `bandFM_STDecayLoopU` (a binder swap, not `Iff.rfl`), `bandFM_STDecayLoopPT`
  (`Iff.rfl`), `bandFM_STKcalDecay` (from `inst_stKcalDecay_admissible`).
* Target 7 (`stEtermDecay`) is U2's (no `Chain/Step34Gen` on `main`).

Opened private names of `Induction/DecayLoopB.lean` (`open private`, precedent
`Chain/NewKLKGen.lean:32-43`): `DecayLoopB_pair` (the Ward pair, F4), `_alg` (the exponent chain),
`_exp_small`, `_real_geom`, `_one_sub_u`, `_STWB_le`, `_STWB_nonneg`, `_two_mul_diam_le`,
`_diam_le_KLmaxDist`, `_zdistD_le_KLmaxDist_two`, `_diam_one`, `_mE_im_ge`.  Each is a statement
over `Zd`, `STWB`, reals only; copying them would cost the helper sections
`DecayLoopB.lean:802-1377`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private DecayLoopB_pair DecayLoopB_alg DecayLoopB_exp_small DecayLoopB_real_geom DecayLoopB_one_sub_u DecayLoopB_STWB_le
  DecayLoopB_STWB_nonneg DecayLoopB_two_mul_diam_le DecayLoopB_diam_le_KLmaxDist DecayLoopB_zdistD_le_KLmaxDist_two
  DecayLoopB_diam_one DecayLoopB_mE_im_ge from RBM3D.Induction.DecayLoopB

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The pins (targets 1-4) and the carrier facts F3, F4 -/

section Generic

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **Target 1.** `lem_decayLoop` uniformly in `u ∈ [s_n, t_n]`: conjunct 4 of `twSteps` (`BA/TwistPins.lean:139-142`)
verbatim, binder order `∀ τ' D' : ℝ, 0 < τ' → 0 < D' →` included.  Band: `STDecayLoopU` (`DecayLoopB.lean:792`),
`bandFM_STDecayLoopU`. -/
def STDecayLoopUgL (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ' D' : ℝ, 0 < τ' → 0 < D' → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- **Target 2.** The window form per time, in the binder order of the band `STDecayLoopPT` (`DecayLoopA.lean:106`). -/
def STDecayLoopPTgL (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- **Target 3.** The far decay of `𝒦` over a carrier, without the energy quantifier (`inst_stKcalDecay_admissible`,
`KDecay.lean:976`, for the band; `BAKcalDecay`, U2-BA, for BA): for `k ≥ 1`, `τ, D > 0`, eventually in `n`, every
`u ∈ [0,1)` and every far label vector (`ℓ_u W^τ ≤ KLmaxDist`, the `ℓ¹` diameter) has `|𝒦_{u,σ,a}| ≤ W^{-D}`. -/
def STKcalDecaygL : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D →
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ ≤ (RBM.Loop.KLmaxDist d (sz.L n) a : ℝ) →
        ‖C.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **F3, the spectral data of the carrier**: `0 < κm ≤ Im m` and `η_t = (1 - t) Im m` (`etaOf`, `Loop/GLoopFlow.lean:58`;
band `etaT`, `Loop/GLoop.lean:75`).  The band has `κm = √κ/2` (`DecayGen_bandSpec`), BA `κm = κ`. -/
def DecayGen_Spec (κm : ℝ) : Prop := 0 < κm ∧ (∀ n, κm ≤ (C.m n).im) ∧ ∀ (n : ℕ) (t : ℝ), C.eta n t = (1 - t) * (C.m n).im

/-- **F4, the Ward pair** (`DecayLoopB_pair`, `DecayLoopB.lean:1065`): for `k ≥ 2` a far pair `c` of `(σ, a)` (a function of
`(σ, a)` only) with `diam_∞ a ≤ (k-1) |c₁ - c₂|_∞` and `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛_{(+,-),c}|` for every time with
`η = C.eta > 0` and every sample. -/
def DecayGen_WardPair : Prop :=
  ∀ (n k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), ∃ c : Zd d (sz.L n) × Zd d (sz.L n),
    ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d (sz.L n) (c.1 - c.2) : ℝ) ∧
    ∀ (u : ℝ) (ω : sz.SeqΩ), 0 < C.eta n u →
      ‖C.L n u σ a ω‖ ^ 2 ≤ (C.eta n u)⁻¹ ^ (2 * (k - 1)) * ‖C.L n u ![true, false] ![c.1, c.2] ω‖

/-- **Target 4 (the pin, per time).** `STDecayLoopAt` (`DecayLoopA.lean:85`) over a carrier; `κm` is the lower bound of `Im m`
(in place of `0 < κ` and `|E n| ≤ 2 - κ`).  From the decay input of the `(+,-)` 2-loops `𝓛 - 𝒦` at the time sequence `u`
with a prefactor `P`, `1 ≤ P ≤ N^{C₀}` eventually, to the decay of every `k`-loop with labels spread beyond `ℓ_u W^{τ'}`. -/
def STDecayLoopAtgL (κm 𝔠 𝔡 C₀ : ℝ) (u P : ℕ → ℝ) : Prop :=
  DecayGen_Spec C κm → sz.Admissible 𝔠 𝔡 → (∀ n, 0 ≤ u n) → (∀ n, u n < 1) →
  (∀ᶠ n : ℕ in atTop, 1 ≤ P n ∧ P n ≤ ((sz.size n : ℕ) : ℝ) ^ C₀) →
  (∀ D : ℝ, 0 < D →
    PrecPTL sz μ (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (u n) p.2.1 p.2.2 ω - C.K n (u n) p.2.1 p.2.2‖)
      (fun n p _ => P n * STWB sz n (u n) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))) →
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    PrecPTL sz μ (U := fun n => Unit × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (u n) p.2.1 p.2.2 ω‖ + ‖C.L n (u n) p.2.1 p.2.2 ω - C.K n (u n) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

end Generic

/-! ## 2. The band readings (bridges and the facts F3, F4 at the band) -/

/-- **Target 1, band bridge**: not `Iff.rfl` (the band binder order is `∀ τ', 0 < τ' → ∀ D', 0 < D'`). -/
theorem bandFM_STDecayLoopU {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) :
    STDecayLoopU sz E s t ↔ STDecayLoopUgL (bandFM sz E) (Sizes.seqP sz) s t :=
  ⟨fun h k hk τ' D' hτ' hD' => h k hk τ' hτ' D' hD', fun h k hk τ' hτ' D' hD' => h k hk τ' D' hτ' hD'⟩

/-- **Target 2, band bridge** (`Iff.rfl`: the binder order is kept). -/
theorem bandFM_STDecayLoopPT {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) :
    STDecayLoopPT sz E s t ↔ STDecayLoopPTgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

/-- **Target 3, band reading**, from `inst_stKcalDecay_admissible` (`KDecay.lean:976`); the band hypotheses `|E n| ≤ 2 - κ`
and `Admissible` are allowed here only. -/
theorem bandFM_STKcalDecay {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {E : ℕ → ℝ} {κ 𝔠 𝔡 : ℝ} (hκ : 0 < κ)
    (hA : sz.Admissible 𝔠 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ) : STKcalDecaygL (bandFM sz E) := by
  intro k hk τ D hτ hD
  filter_upwards [RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ hk hτ hD] with n hn u hu0 hu1 σ a hfar
  exact hn (E n) (hE n) u hu0 hu1 σ a hfar

/-- **F3 at the band**: `κm = √κ / 2` (`Im m(E) ≥ √κ/2` for `|E| ≤ 2 - κ`); `η = etaT` is `(1 - t) Im m` by definition. -/
theorem DecayGen_bandSpec {d : ℕ} (sz : Sizes d) {E : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) :
    DecayGen_Spec (bandFM sz E) (Real.sqrt κ / 2) :=
  ⟨by have := Real.sqrt_pos.mpr hκ; positivity, fun n => DecayLoopB_mE_im_ge hκ (hE n), fun n t => rfl⟩

/-- **F4 for any Hermitian fine matrix** and `η ≤ |Im z|`: `DecayLoopB_pair` read through `loopM_eq_loopL` (`open private`). -/
theorem DecayGen_ward {d L W : ℕ} [NeZero L] [NeZero W] {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ∃ c : Zd d L × Zd d L, ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d L (c.1 - c.2) : ℝ) ∧
      ∀ (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (η : ℝ), H.IsHermitian → 0 < η → η ≤ |z.im| →
        ‖loopFine d L W H z σ a‖ ^ 2 ≤ η⁻¹ ^ (2 * (k - 1)) * ‖loopFine d L W H z ![true, false] ![c.1, c.2]‖ := by
  obtain ⟨c, hc1, hc2⟩ := DecayLoopB_pair (d := d) (L := L) (W := W) hk σ a
  refine ⟨c, hc1, fun H z η hH hη hz => ?_⟩
  have h2 : loopFine d L W H z ![true, false] ![c.1, c.2] = loopL d L W (blockMat d L W H) z ⟨[true, false], [c.1, c.2]⟩ :=
    (loopM_eq_loopL d L W _ _ ![true, false] ![c.1, c.2]).trans (by simp [loopOf, List.ofFn_succ])
  have h1 : loopFine d L W H z σ a = loopL d L W (blockMat d L W H) z (loopOf σ a) := loopM_eq_loopL d L W _ _ σ a
  rw [h1, h2]
  exact hc2 _ z η (hH.submatrix _) hη hz

/-- **F4 at the band**: `H = seqHflow`, `z = zt`, `η = etaT = Im zt`. -/
theorem DecayGen_bandWardPair {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : DecayGen_WardPair (bandFM sz E) := by
  intro n k hk σ a
  obtain ⟨c, hc1, hc2⟩ := DecayGen_ward (d := d) (L := sz.L n) (W := sz.W n) hk σ a
  exact ⟨c, hc1, fun u ω hη => hc2 _ (zt (E n) u) (etaT (E n) u) (Sizes.seqHflow_isHermitian sz n u ω) hη
    (by rw [← etaT_eq_zt_im]; exact le_abs_self _)⟩

/-! ## 3. The deterministic step, shared by targets 4-6 (the pointwise chain of `DecayLoopA_main`/`DecayLoopB_main_u`) -/

/-- The facts at one size index `n` that the step reads, all derived from `STKcalDecaygL`, `Admissible` and `N → ∞`:
`K`-decay at `(2, τ'/2, Q)` and `(k, τ', D' + 1)`, `exp(-√x) ≤ W^{-Q}` for `x ≥ (W^{τ'/2}/k)²`, the thresholds on `W`,
`N^𝔠 ≤ W`, and `(eq:WO)`. -/
private def DecayGen_Ev {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (κm 𝔠 𝔡 τ' D' Q : ℝ) (k n : ℕ) : Prop :=
  (∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ (τ' / 2) ≤ (RBM.Loop.KLmaxDist d (sz.L n) a : ℝ) →
        ‖C.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q)) ∧
  (∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (RBM.Loop.KLmaxDist d (sz.L n) a : ℝ) →
        ‖C.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1))) ∧
  (∀ x : ℝ, (((sz.W n : ℕ) : ℝ) ^ (τ' / 2) / (k : ℝ)) ^ 2 ≤ x → Real.exp (-Real.sqrt x) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q)) ∧
  (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ∧
  16 * κm⁻¹ ^ (2 * (k - 1)) * (2 + 2) ≤ ((sz.W n : ℕ) : ℝ) ∧
  (k : ℝ) - 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ' / 2) ∧
  ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ) ∧
  (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹) ∧
  (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ)

/-- `DecayGen_Ev` holds eventually: the eight facts of `DecayLoopA_main`/`DecayLoopB_main_u`, with `STKcalDecaygL` in
place of `inst_stKcalDecay_admissible`. -/
private theorem DecayGen_ev {d : ℕ} (sz : Sizes d) (C : FlowFM sz) {κm 𝔠 𝔡 τ' D' Q : ℝ} (hK : STKcalDecaygL C)
    (hA : sz.Admissible 𝔠 𝔡) {k : ℕ} (hk : 2 ≤ k) (hτ' : 0 < τ') (hD' : 0 < D') (hQpos : 0 < Q) :
    ∀ᶠ n in atTop, DecayGen_Ev sz C κm 𝔠 𝔡 τ' D' Q k n := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hB h1
  have hK2 := hK 2 (by norm_num) (τ' / 2) Q (by linarith) hQpos
  have hKk := hK k (by omega) τ' (D' + 1) hτ' (by linarith)
  have hexp := hWtend.eventually (DecayLoopB_exp_small (τ' := τ') hτ' (K := (k : ℝ)) (Q := Q) (by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith) hQpos.le)
  have hW2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hWtend.eventually_ge_atTop 2
  have hWΓ : ∀ᶠ n : ℕ in atTop, 16 * κm⁻¹ ^ (2 * (k - 1)) * (2 + 2) ≤ ((sz.W n : ℕ) : ℝ) :=
    hWtend.eventually_ge_atTop _
  have hWk : ∀ᶠ n : ℕ in atTop, (k : ℝ) - 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ' / 2)).comp hWtend).eventually_ge_atTop _
  have hN2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN.eventually_ge_atTop 2
  filter_upwards [hK2, hKk, hexp, hW2, hWΓ, hWk, hB, hWO, hN2] with n h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **The prefactor** `((1-s)/(1-v))^{Cd} Bctl_v^{1/5} ≤ N^{max Cd 0 + 1}` from `0 ≤ s ≤ v < 1`, `1 - v ≥ N⁻¹` and
`lam² W^d ≥ 1`, `N ≥ 2` (`Bctl_v ≤ 2`, `(1-s)/(1-v) ≤ N`). -/
private theorem DecayGen_prefactor {d : ℕ} (sz : Sizes d) (n : ℕ) {s v Cd : ℝ} (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (hN2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ)) (hNv : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - v) (hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) :
    ((1 - s) / (1 - v)) ^ Cd * (sz.Bctl n v) ^ (1 / 5 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hv : 0 < 1 - v := by linarith
  have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - v) := by
    have := mul_le_mul_of_nonneg_left hNv hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  have hB2 : sz.Bctl n v ≤ 2 := DecayLoopB_STWB_le sz n 0 hv1 hg1 hN1u
  have hB0 : 0 ≤ sz.Bctl n v := DecayLoopB_STWB_nonneg sz n _ 0
  have hB5 : (sz.Bctl n v) ^ (1 / 5 : ℝ) ≤ 2 :=
    calc (sz.Bctl n v) ^ (1 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hB0 hB2 (by norm_num)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hratio1 : 1 ≤ (1 - s) / (1 - v) := by
    rw [le_div_iff₀ hv]; linarith
  have hratioN : (1 - s) / (1 - v) ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [div_le_iff₀ hv]
    have := mul_le_mul_of_nonneg_left hNv hNpos.le
    rw [mul_inv_cancel₀ hNpos.ne'] at this
    nlinarith
  have hpow : ((1 - s) / (1 - v)) ^ Cd ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
    calc ((1 - s) / (1 - v)) ^ Cd ≤ ((1 - s) / (1 - v)) ^ (max Cd 0) :=
          Real.rpow_le_rpow_of_exponent_le hratio1 (le_max_left _ _)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) := Real.rpow_le_rpow (by linarith) hratioN (le_max_right _ _)
  have hNC : ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  calc ((1 - s) / (1 - v)) ^ Cd * (sz.Bctl n v) ^ (1 / 5 : ℝ)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * 2 := mul_le_mul hpow hB5 (Real.rpow_nonneg hB0 _) (by positivity)
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) := by gcongr
    _ = _ := hNC

/-- **The deterministic step** (the common part of `DecayLoopA_main` and `DecayLoopB_main_u`).  At a size index `n` with the
facts `DecayGen_Ev`, a time `u ∈ [0,1)`, labels `(σ, a)` with the Ward pair `c`, and the failure bound at the pair
(`hX`, the complement of the one bad event of the decay input): `(|𝓛| + |𝓛 - 𝒦|) 1(ℓ_u W^{τ'} ≤ diam_∞ a) ≤ W^{-D'}`.
The prefactor `Pn` need only satisfy `Pn ≤ N^{C₀}` once `N ≥ 2`, `1 - u ≥ N⁻¹` and `lam² W^d ≥ 1` (the last two derived here
from the far premise). -/
private theorem DecayGen_step {d : ℕ} (hd : 2 ≤ d) (sz : Sizes d) (C : FlowFM sz) {κm 𝔠 𝔡 C₀ τ' D' Q : ℝ} {k n : ℕ}
    (hk : 2 ≤ k) (hκm : 0 < κm) (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (hC₀ : 0 ≤ C₀) (hτ' : 0 < τ') (hD' : 0 < D')
    (hQ : Q = 2 * D' + 1 / 𝔠 * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1)
    (hEv : DecayGen_Ev sz C κm 𝔠 𝔡 τ' D' Q k n)
    (hmn : κm ≤ (C.m n).im) (hη : ∀ t, C.eta n t = (1 - t) * (C.m n).im)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (c : Zd d (sz.L n) × Zd d (sz.L n))
    (hcmax : ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d (sz.L n) (c.1 - c.2) : ℝ))
    (hcb : ∀ (u : ℝ) (ω : sz.SeqΩ), 0 < C.eta n u →
      ‖C.L n u σ a ω‖ ^ 2 ≤ (C.eta n u)⁻¹ ^ (2 * (k - 1)) * ‖C.L n u ![true, false] ![c.1, c.2] ω‖)
    {Pn : ℝ} (hPn : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) → ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - u →
      1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d → Pn ≤ ((sz.size n : ℕ) : ℝ) ^ C₀)
    (hX : ‖C.L n u ![true, false] ![c.1, c.2] ω - C.K n u ![true, false] ![c.1, c.2]‖ ≤
      ((sz.size n : ℕ) : ℝ) * (Pn * STWB sz n u (zdistInf d (sz.L n) (c.1 - c.2)) *
        Real.exp (-(((zdistInf d (sz.L n) (c.1 - c.2) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Q))) :
    (‖C.L n u σ a ω‖ + ‖C.L n u σ a ω - C.K n u σ a‖) *
        (if ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) then 1 else 0) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  obtain ⟨hK2n, hKkn, hexpn, hW2n, hWΓn, hWkn, hbwn, hwo, hN2n⟩ := hEv
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = κm⁻¹ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 / 𝔠 := ⟨_, rfl⟩
  rw [← hΓ] at hWΓn
  rw [← hAdef] at hQ
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  -- basic facts at the index n
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  -- not far: trivial
  by_cases hfar : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)
  swap
  · simp only [hfar, ↓reduceIte, mul_zero]
    exact (Real.rpow_pos_of_pos hWpos _).le
  simp only [hfar, ↓reduceIte, mul_one]
  -- the scales: `g`, `1 - u`, `η`
  have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) u := one_le_ellT hL1r
  have hℓpos : 0 < ellT (sz.L n) (sz.lam n) u := by linarith
  have hWτ : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW1r hτ'.le
  have hdiam : (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) / 2 := by
    have := DecayLoopB_two_mul_diam_le a
    have h2 : (2 : ℝ) * (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hℓL : ellT (sz.L n) (sz.lam n) u < ((sz.L n : ℕ) : ℝ) := by
    have h3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL3
    calc ellT (sz.L n) (sz.lam n) u
        ≤ ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' := le_mul_of_one_le_right hℓpos.le hWτ
      _ ≤ (STdiamInf a : ℝ) := hfar
      _ ≤ ((sz.L n : ℕ) : ℝ) / 2 := hdiam
      _ < _ := by linarith
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u := DecayLoopB_one_sub_u hd hL3 hW1 hlam0 hgW hu1 hℓL
  have hv : 0 < 1 - u := by linarith
  have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := by
    have := mul_le_mul_of_nonneg_left hNu hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  have hμ : 0 < (C.m n).im := lt_of_lt_of_le hκm hmn
  have hηpos : 0 < C.eta n u := by rw [hη]; exact mul_pos hv hμ
  have hηΓ : (C.eta n u)⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by
    have h1 : (1 - u) * κm ≤ C.eta n u := by
      rw [hη]; exact mul_le_mul_of_nonneg_left hmn hv.le
    have h2 : (C.eta n u)⁻¹ ≤ ((1 - u) * κm)⁻¹ := inv_anti₀ (by positivity) h1
    have h3 : ((1 - u) * κm)⁻¹ = Γ * (1 - u)⁻¹ := by
      rw [hΓ]; field_simp
    have h4 : (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    calc (C.eta n u)⁻¹ ≤ ((1 - u) * κm)⁻¹ := h2
      _ = Γ * (1 - u)⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by gcongr
  have hMi : STWB sz n u (zdistInf d (sz.L n) (c.1 - c.2)) ≤ 2 := DecayLoopB_STWB_le sz n _ hu1 hg1 hN1u
  obtain ⟨hfar2, hexarg⟩ := DecayLoopB_real_geom hWpos hℓpos (Nat.cast_nonneg _) hk2 hWkn (hfar.trans hcmax)
  -- the bounds on the far pair
  have hKp : ‖C.K n u ![true, false] ![c.1, c.2]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    refine hK2n u hu0 hu1 ![true, false] ![c.1, c.2] (hfar2.trans ?_)
    exact_mod_cast (zdistInf_le_zdistD d (sz.L n) _).trans (DecayLoopB_zdistD_le_KLmaxDist_two c.1 c.2)
  have hKc : ‖C.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) :=
    hKkn u hu0 hu1 σ a (hfar.trans (by exact_mod_cast DecayLoopB_diam_le_KLmaxDist a))
  have hex : Real.exp (-(((zdistInf d (sz.L n) (c.1 - c.2) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    have := hexpn _ hexarg
    rwa [Real.sqrt_eq_rpow] at this
  have hLp : ‖C.L n u ![true, false] ![c.1, c.2] ω‖ ≤
      ‖C.K n u ![true, false] ![c.1, c.2]‖ + ‖C.L n u ![true, false] ![c.1, c.2] ω - C.K n u ![true, false] ![c.1, c.2]‖ :=
    norm_le_norm_add_norm_sub' _ _
  have hNW : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ A := by
    calc ((sz.size n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (1 / 𝔠) := by
          rw [← Real.rpow_mul hNpos.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := Real.rpow_le_rpow (by positivity) hbwn (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ A := by rw [hAdef]
  have key := DecayLoopB_alg (W := ((sz.W n : ℕ) : ℝ)) (N := ((sz.size n : ℕ) : ℝ)) (Γ := Γ)
    (Θ := 2) (A := A) (k := k) (D' := D') (C₀ := C₀) (Q := Q)
    (Λ := ‖C.L n u σ a ω‖) hk hC₀ hΓ0 (by norm_num) hW2n hWΓn hN1 hNW hQ (inv_nonneg.mpr hηpos.le) hηΓ
    (norm_nonneg _) (norm_nonneg _) (hcb u ω hηpos) hLp hKp hX (hPn hN2n hNu hg1) hMi hex
    (DecayLoopB_STWB_nonneg sz n _ _) (Real.exp_pos _).le hKc
  have hlk : ‖C.L n u σ a ω - C.K n u σ a‖ ≤ ‖C.L n u σ a ω‖ + ‖C.K n u σ a‖ := norm_sub_le _ _
  linarith [norm_nonneg (C.L n u σ a ω)]

/-! ## 4. Targets 4, 5, 6 -/

/-- Deterministic domination implies `≺` at any law `μ` (`Sizes.prec_of_le`, `Defs/StochDomAt.lean:136`, for `μ = seqP sz`). -/
private theorem DecayGen_prec_of_le {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hle : ∀ n u ω, ξ n u ω ≤ ζ n u ω) : PrecL sz μ ξ ζ := by
  refine StochDomAt.of_eventually_empty fun τ hτ => Eventually.of_forall fun n => ?_
  ext ω
  have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro u
  nlinarith [hle n u ω, hζ n u ω]

/-- For `k = 1` the far set is empty (`diam_∞ a = 0 < ℓ_u W^{τ'}`): the indicator vanishes. -/
private theorem DecayGen_one_ind {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (τ' : ℝ) (a : Fin 1 → Zd d (sz.L n)) :
    ¬ (ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)) := by
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hpos : 0 < ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' :=
    mul_pos (ellT_pos hL) (Real.rpow_pos_of_pos hW _)
  have hmax : (STdiamInf a : ℝ) = 0 := by
    rw [DecayLoopB_diam_one]; simp
  rw [hmax]; exact not_le.mpr hpos

/-- **`k ≥ 2` of target 4**: the only random event is that of the decay input at the far pair `c = c(σ,a)`; on its
complement `DecayGen_step` gives `(|𝓛| + |𝓛-𝒦|)_{u,σ,a} ≤ W^{-D'}`.  Parameters: `τ₁ = 1` for the input, `D = Q` (its `W^{-D}`
term), `STKcalDecaygL` at `(2, τ'/2, Q)` and `(k, τ', D'+1)`. -/
private theorem DecayGen_main_at {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ)
    (hW : DecayGen_WardPair C) (hK : STKcalDecaygL C) {κm 𝔠 𝔡 C₀ : ℝ} {u P : ℕ → ℝ}
    (hspec : DecayGen_Spec C κm) (hA : sz.Admissible 𝔠 𝔡) (hC₀ : 0 ≤ C₀)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) (hP2 : ∀ᶠ n : ℕ in atTop, P n ≤ ((sz.size n : ℕ) : ℝ) ^ C₀)
    (hdec : ∀ D : ℝ, 0 < D →
      PrecPTL sz μ (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖C.L n (u n) p.2.1 p.2.2 ω - C.K n (u n) p.2.1 p.2.2‖)
        (fun n p _ => P n * STWB sz n (u n) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D)))
    {k : ℕ} (hk : 2 ≤ k) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    PrecPTL sz μ (U := fun n => Unit × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (u n) p.2.1 p.2.2 ω‖ + ‖C.L n (u n) p.2.1 p.2.2 ω - C.K n (u n) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨hκm, hmn, heta⟩ := hspec
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * D' + 1 / 𝔠 * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1 := ⟨_, rfl⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hQpos : 0 < Q := by
    have : 0 ≤ 1 / 𝔠 * (2 * ((k : ℝ) - 1) + 1 + C₀) := mul_nonneg (by positivity) (by nlinarith)
    rw [hQ]; linarith
  -- choice of the far pair
  choose cp hcp using fun (n : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) => hW n k hk σ a
  -- the pulled-back source
  have hpb : PrecPTL sz μ (U := fun n => Unit × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (u n) ![true, false] ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2] ω -
        C.K n (u n) ![true, false] ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]‖)
      (fun n p _ => P n * STWB sz n (u n) (zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2)) *
          Real.exp (-(((zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Q)) := by
    intro τ₁ hτ₁ D₁ hD₁
    filter_upwards [hdec Q hQpos τ₁ hτ₁ D₁ hD₁] with n hn p
    exact hn ((), ![true, false], ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2])
  refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_of_imp hpb ?_
  intro τ₀ hτ₀
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [DecayGen_ev sz C (κm := κm) hK hA hk hτ' hD' hQpos, hP2] with n hEv hP2n
  rintro ⟨⟨⟩, σ, a⟩ ω hlt
  by_contra hnot
  dsimp only at hlt hnot
  have hX := not_lt.mp hnot
  rw [Real.rpow_one] at hX
  have hs := DecayGen_step (by omega) sz C hk hκm h𝔠 h𝔡 hC₀ hτ' hD' hQ hEv (hmn n) (heta n) (hu0 n) (hu1 n) σ a ω
    (cp n σ a) (hcp n σ a).1 (hcp n σ a).2 (fun _ _ _ => hP2n) hX
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀.le
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _
  have hle : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
    le_mul_of_one_le_left hWD.le hNτ
  linarith

/-- **Target 4: `lem_decayLoop` at a single time over a carrier** (`3 ≤ d`; band `stDecayLoopAt_holds`, `DecayLoopA.lean:938`,
paper `3_5:1126`, `res_decayLK` `3_5:1128`).  From the decay input at the time sequence `u` (a section of
`STStep2DecayPTgL`, prefactor `P`, `1 ≤ P ≤ N^{C₀}` eventually), for every `k ≥ 1`, `τ', D' > 0`:
`(|𝓛| + |𝓛-𝒦|)_{u,σ,a} 1(ℓ_u W^{τ'} ≤ diam_∞ a) ≺ W^{-D'}` per time.  The carrier enters through the Ward pair
(`DecayGen_WardPair`, F4), the far decay of `𝒦` (`STKcalDecaygL`) and the spectral data (`DecayGen_Spec`, F3). -/
theorem stDecayLoopAtgL_of {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ)
    (hW : DecayGen_WardPair C) (hK : STKcalDecaygL C) (κm 𝔠 𝔡 C₀ : ℝ) (u P : ℕ → ℝ) :
    STDecayLoopAtgL C μ κm 𝔠 𝔡 C₀ u P := by
  intro hspec hA hu0 hu1 hP hdec k hk τ' hτ' D' hD'
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    refine RBM.Green.perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_) (fun n _ _ => ?_)
    · simp only [DecayGen_one_ind sz n (u n) τ' p.2.2, ↓reduceIte, mul_zero, le_refl]
    · exact (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _).le
  · refine DecayGen_main_at hd sz C μ hW hK hspec hA (C₀ := max C₀ 0) (le_max_right _ _) hu0 hu1 ?_ hdec hk2 hτ' hD'
    filter_upwards [hP] with n hn
    exact hn.2.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n) (le_max_left _ _))

/-- **Target 5: the window form per time from the Step 2 decay** (band `stDecayLoopPT_of_step2`, `DecayLoopA.lean:970`).
From `STStep2DecayPTgL C μ Cd s t` (prefactor `((1-s)/(1-u))^{Cd} Bctl^{1/5}`), every section `u ∈ [s,t]` satisfies the hypotheses of
`stDecayLoopAtgL_of` with `P_u' = max P_u 1` and `C₀ = max Cd 0 + 1`; `1 - u ≥ N⁻¹` is the hypothesis `hrange` (F6; the band
reads it off `STFlow` by `v3_premises_of_stFlow`).  The sections assemble by `perTime_timeIcc_of_forall_seq`. -/
theorem stDecayLoopPTgL_of_step2 {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (κm 𝔠 𝔡 : ℝ)
    (s t : ℕ → ℝ) (Cd : ℝ) (hspec : DecayGen_Spec C κm) (hA : sz.Admissible 𝔠 𝔡) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hrange : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) (hW : DecayGen_WardPair C)
    (hK : STKcalDecaygL C) (hD : STStep2DecayPTgL C μ Cd s t) : STDecayLoopPTgL C μ s t := by
  intro k hk τ' hτ' D' hD'
  refine RBM.Green.perTime_timeIcc_of_forall_seq μ sz.size hst
    (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n v q ω =>
      (‖C.L n v q.1 q.2 ω‖ + ‖C.L n v q.1 q.2 ω - C.K n v q.1 q.2‖) *
      (if ellT (sz.L n) (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf q.2 : ℝ) then 1 else 0))
    (fun n _ _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) ?_
  intro u hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs n).trans (hu n).1
  have hu1 : ∀ n, u n < 1 := fun n => (hu n).2.trans_lt (ht1 n)
  obtain ⟨-, h𝔡, hNtend, -, hWO⟩ := id hA
  -- the prefactor
  have hPev : ∀ᶠ n : ℕ in atTop, 1 ≤ max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1 ∧
      max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) := by
    filter_upwards [hrange, hNtend.eventually_ge_atTop 2, hWO] with n hr hN2 hwo
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u n := hr.trans (by linarith [(hu n).2])
    have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
      (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
    have h1N : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) :=
      Real.one_le_rpow hN1 (by have := le_max_right Cd 0; linarith)
    exact ⟨le_max_right _ _, max_le (DecayGen_prefactor sz n (hs n) (hu n).1 (hu1 n) hN2 hNu hg1) h1N⟩
  -- the decay input at the section `u` with the prefactor `P' = max P_u 1`
  have hdec_u : ∀ D : ℝ, 0 < D →
      PrecPTL sz μ (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖C.L n (u n) p.2.1 p.2.2 ω - C.K n (u n) p.2.1 p.2.2‖)
        (fun n p _ =>
          (fun n => max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1) n *
            STWB sz n (u n) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    intro D hD0
    have h1 := RBM.Green.perSeq_of_perTime_timeIcc μ sz.size (s := s) (t := t)
      (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
      (fun n v q ω => ‖C.L n v q.1 q.2 ω - C.K n v q.1 q.2‖)
      (fun n v q _ => ((1 - s n) / (1 - v)) ^ Cd * (sz.Bctl n v) ^ (1 / 5 : ℝ) *
          STWB sz n v (zdistInf d (sz.L n) (q.2 0 - q.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) v) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) (hD D hD0) u hu
    refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_of_imp h1 ?_
    intro τ₀ hτ₀
    refine ⟨τ₀, hτ₀, Filter.Eventually.of_forall ?_⟩
    rintro n ⟨⟨⟩, q⟩ ω hlt
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hlt
    have hP : ((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ) ≤
        max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1 := le_max_left _ _
    have hex0 : 0 ≤ Real.exp (-(((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) :=
      (Real.exp_pos _).le
    have hS0 := DecayLoopB_STWB_nonneg sz n (u n) (zdistInf d (sz.L n) (q.2 0 - q.2 1))
    gcongr
  exact stDecayLoopAtgL_of hd sz C μ hW hK κm 𝔠 𝔡 (max Cd 0 + 1) u
    (fun n => max (((1 - s n) / (1 - u n)) ^ Cd * (sz.Bctl n (u n)) ^ (1 / 5 : ℝ)) 1)
    hspec hA hu0 hu1 hPev hdec_u k hk τ' hτ' D' hD'

/-- **`k ≥ 2` of target 6**: the uniform far-loop decay (the pointwise chain at the time `v ∈ [s_n, t_n]` of the index).  The
input is `STGdecayWgL` at `D = Q` and the far pair `c(σ,a)`; the prefactor `((1-s)/(1-v))^{Cd} Bctl_v^{1/5} ≤ N^{max Cd 0 + 1}`
follows from the far premise alone.  The union over the index is the inclusion of failure events `badSetAt`
(`StochDomAt.of_subset`): it is pointwise in `(v, σ, a)`. -/
private theorem DecayGen_main_u {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ)
    (hW : DecayGen_WardPair C) (hK : STKcalDecaygL C) {κm 𝔠 𝔡 Cd : ℝ} {s t : ℕ → ℝ}
    (hspec : DecayGen_Spec C κm) (hA : sz.Admissible 𝔠 𝔡) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hdec : STGdecayWgL C μ s t Cd) {k : ℕ} (hk : 2 ≤ k) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨hκm, hmn, heta⟩ := hspec
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ, C₀ = max Cd 0 + 1 := ⟨_, rfl⟩
  have hC₀ : 0 ≤ C₀ := by rw [hC₀def]; have := le_max_right Cd 0; linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * D' + 1 / 𝔠 * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1 := ⟨_, rfl⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hQpos : 0 < Q := by
    have : 0 ≤ 1 / 𝔠 * (2 * ((k : ℝ) - 1) + 1 + C₀) := mul_nonneg (by positivity) (by nlinarith)
    rw [hQ]; linarith
  -- choice of the far pair
  choose cp hcp using fun (n : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) => hW n k hk σ a
  -- the pulled-back source (the uniform Step-2 decay at the far pair)
  have hpb0 := StochDomAt.precomp_param (V := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (hdec Q hQpos) (fun n p => (p.1, ![true, false], ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]))
  have hpb : PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) ![true, false] ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2] ω -
        C.K n (p.1 : ℝ) ![true, false] ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2)) *
          Real.exp (-(((zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Q)) := hpb0
  refine StochDomAt.of_subset hpb ?_
  intro τ₀ hτ₀
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [DecayGen_ev sz C (κm := κm) hK hA hk hτ' hD' hQpos] with n hEv
  rintro ω ⟨⟨v, σ, a⟩, hlt⟩
  refine ⟨⟨v, σ, a⟩, ?_⟩
  by_contra hnot
  dsimp only at hlt hnot
  have hu0 : 0 ≤ (v : ℝ) := (hs0 n).trans v.2.1
  have hu1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 n)
  have hX := not_lt.mp hnot
  rw [Real.rpow_one] at hX
  have hs := DecayGen_step (by omega) sz C hk hκm h𝔠 h𝔡 hC₀ hτ' hD' hQ hEv (hmn n) (heta n) hu0 hu1 σ a ω
    (cp n σ a) (hcp n σ a).1 (hcp n σ a).2
    (fun hN2 hNu hg1 => by rw [hC₀def]; exact DecayGen_prefactor sz n (hs0 n) v.2.1 hu1 hN2 hNu hg1) hX
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀.le
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _
  have hle : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
    le_mul_of_one_le_left hWD.le hNτ
  linarith

/-- **Target 6: `lem_decayLoop` over the window `[s,t]`, uniformly in `u`, from the uniform Step 2 decay** (band
`stDecayLoopU_of_step2`, `DecayLoopB.lean:1637`; the uniform form of target 5).  The setting is the carrier `C` with the facts
F3 (`DecayGen_Spec`), F4 (`DecayGen_WardPair`), the far decay of `𝒦` (`STKcalDecaygL`) and `Admissible`; the flow enters only
through `0 ≤ s`, `t < 1`.  The conclusion is `STDecayLoopUgL C μ s t`, conjunct 4 of `twSteps` (T7-BA's BA instance of this theorem
produces it at BA). -/
theorem stDecayLoopUgL_of_step2 {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (κm 𝔠 𝔡 : ℝ)
    (s t : ℕ → ℝ) (Cd : ℝ) (hspec : DecayGen_Spec C κm) (hA : sz.Admissible 𝔠 𝔡) (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hW : DecayGen_WardPair C) (hK : STKcalDecaygL C) (hD : STGdecayWgL C μ s t Cd) : STDecayLoopUgL C μ s t := by
  intro k hk τ' D' hτ' hD'
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    refine DecayGen_prec_of_le sz μ (fun n p ω => ?_) (fun n p ω => ?_)
    · exact (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _).le
    · simp only [DecayGen_one_ind sz n (p.1 : ℝ) τ' p.2.2, ↓reduceIte, mul_zero]
      exact (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _).le
  · exact DecayGen_main_u hd sz C μ hW hK hspec hA hs ht1 hD hk2 hτ' hD'

/-! ## 5. Compiled nonempty instances at the band (`d = 3`)

The size sequence is the merged preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`,
`Admissible (1/6) (1/10)`), the flow is the merged instance `z0` (`flow_z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), and the window is
`[s, t] = [0, 1/16]` (`1/16 ≤ lemT z0`), as in `DecayLoopB.lean:2236-2250`.  The Step 2 decay inputs (`STGdecayWgL`,
`STStep2DecayPTgL`, the decay input of target 4) are other gates' outputs and stay hypotheses of the examples; every deterministic
hypothesis (`DecayGen_Spec`, `Admissible`, the Ward pair, `STKcalDecaygL`, `0 ≤ s`, `t < 1`, `N⁻¹ ≤ 1 - t`) is discharged. -/

section Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

private theorem DecayGen_inst_hE (n : ℕ) : |STflowE z0 n| ≤ 2 - 1 / 10 := by
  have him : 0 < (z0 n).im :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz0.one_le_size n) _) (flow_z0.2 n).2.1
  exact (abs_lemE_le him).trans (flow_z0.2 n).1

private theorem DecayGen_inst_hN : ∀ᶠ n in atTop, (((sz0.size n : ℕ) : ℝ))⁻¹ ≤ 1 - tInst n := by
  filter_upwards [(tendsto_natCast_atTop_iff.2 (Sizes.tendsto_size sz0 sz0_tendsto)).eventually_ge_atTop (2 : ℝ)] with n hn
  have := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hn
  norm_num [tInst] at this ⊢; linarith

/-- **Target 6 at the band carrier**, re-deriving `STDecayLoopU` through `bandFM_STDecayLoopU`; open: the uniform Step 2 decay
`STGdecayWgL`. -/
example (Cd : ℝ) (hD : STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd) :
    STDecayLoopU sz0 (STflowE z0) sInst tInst :=
  (bandFM_STDecayLoopU sz0 _ _ _).2 <| stDecayLoopUgL_of_step2 (d := 3) (by norm_num) sz0 (bandFM sz0 (STflowE z0))
    (Sizes.seqP sz0) _ (1 / 6) (1 / 10) sInst tInst Cd (DecayGen_bandSpec sz0 (κ := 1 / 10) (by norm_num) DecayGen_inst_hE)
    sz0_admissible (fun _ => le_rfl) (fun n => by norm_num [tInst]) (DecayGen_bandWardPair sz0 _)
    (bandFM_STKcalDecay (by norm_num) sz0 (by norm_num) sz0_admissible DecayGen_inst_hE) hD

/-- **Target 5 at the band** (F6 discharged: `1 - 1/16 ≥ N⁻¹` eventually); open: the per-time Step 2 decay. -/
example (Cd : ℝ) (hD : STStep2DecayPTgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) Cd sInst tInst) :
    STDecayLoopPT sz0 (STflowE z0) sInst tInst :=
  (bandFM_STDecayLoopPT sz0 _ _ _).2 <| stDecayLoopPTgL_of_step2 (d := 3) (by norm_num) sz0 (bandFM sz0 (STflowE z0))
    (Sizes.seqP sz0) _ (1 / 6) (1 / 10) sInst tInst Cd
    (DecayGen_bandSpec sz0 (κ := 1 / 10) (by norm_num) DecayGen_inst_hE) sz0_admissible (fun _ => le_rfl)
    (fun n => by norm_num [sInst, tInst]) (fun n => by norm_num [tInst]) DecayGen_inst_hN (DecayGen_bandWardPair sz0 _)
    (bandFM_STKcalDecay (by norm_num) sz0 (by norm_num) sz0_admissible DecayGen_inst_hE) hD

/-- **Target 4 at the band** (`E ≡ 0`, `u ≡ 1/2`, `ℓ_u = 1`, `P ≡ 1`, `C₀ = 0`, loop length `k = 3`, `τ' = 1/10`, `D' = 1`): every
premise of the pin but the decay input of the `(+,-)` 2-loops is discharged. -/
example (hdec : ∀ D : ℝ, 0 < D →
      PrecPTL sz0 (Sizes.seqP sz0) (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n p ω => ‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω - STKloop sz0 n 0 (1 / 2) p.2.1 p.2.2‖)
        (fun n p _ => 1 * STWB sz0 n (1 / 2) (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz0.L n) (sz0.lam n) (1 / 2)) ^ (1 / 2 : ℝ)) +
          ((sz0.W n : ℕ) : ℝ) ^ (-D))) :
    PrecPTL sz0 (Sizes.seqP sz0) (U := fun n => Unit × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω => (‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω‖ + ‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω - STKloop sz0 n 0 (1 / 2) p.2.1 p.2.2‖) *
        (if ellT (sz0.L n) (sz0.lam n) (1 / 2) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  stDecayLoopAtgL_of (d := 3) (by norm_num) sz0 (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) (DecayGen_bandWardPair sz0 _)
    (bandFM_STKcalDecay (by norm_num) sz0 (κ := 1) (by norm_num) sz0_admissible (fun n => by norm_num)) _ (1 / 6) (1 / 10) 0
    (fun _ => 1 / 2) (fun _ => 1) (DecayGen_bandSpec sz0 (κ := 1) (by norm_num) (fun n => by norm_num)) sz0_admissible
    (fun _ => by norm_num) (fun _ => by norm_num) (Filter.Eventually.of_forall fun n => ⟨le_rfl, by simp⟩) hdec 3 (by norm_num)
    (1 / 10) (by norm_num) 1 (by norm_num)

end Inst

end RBM.BA

end
