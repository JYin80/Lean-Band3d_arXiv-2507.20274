/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.PinsK
import RBM3D.Universality.FreeConvRegular

/-!
# `RBM3D.Universality.PinsDens` (UN-01c): the primed density pins of bulk universality

Ticket T2201 (DECISIONS §65 finding T2190a, §66 (1)-(4), §57 (1)).  **No merged signature is
changed** (CLAUDE.md §5.3): the primed successors live here, in a new file.

*The finding.*  The merged density hypothesis `UNDens` (`Pins.lean:462`) observes `m_n` only on
`0 < η ≤ 10` through the three clauses (bounds, `x`-Lipschitz, limit `ρ_n`), and the tracial local
law `UNTrLocal` (`Pins.lean:447`) only on `N^{-1+ε} ≤ Im z ≤ 1`.  The shift
`m^h_n(z) = m_n(z) + (i/2) 1{Im z < h_n}`, `h_n = N^{-2}`, meets both (`unDens_shift`,
`unTrLocal_shift`) and moves `ρ_n` by `1/(2π)`.  Hence the Step 1 pins that conclude
`|ρ' - ρ_n| ≤ N^{-3τ_s/8}` from `UNDens` + `UNTrLocal` are refuted: `not_UNStep1Good`
(`UNStep1Good`, `Pins.lean:584`) and `not_UNStep1GoodC` (`UNStep1GoodC`, `PinsK.lean:275`),
generically for every datum meeting their hypotheses; `UNDensInst.not_UNStep1Good_band` makes it a
compiled fact for the band rows.

*Registry reclassification (DECISIONS §66 (2); the merged docstrings still say "owed" and are not
edited).*  `UNStep1Good`, `UNInfty1Row`, `UNStep1GoodC`, `UNCoreC` are **superseded, refuted**
(class `refutedProps` of `RBM3D/Test/Axioms.lean`): `UNStep1Good` and `UNStep1GoodC` by the compiled
theorems above, `UNInfty1Row` and `UNCoreC` by the argument of the supervisor verdict
`docs/supervisor/2026-10-05-1651.md` 1.3 (not compiled: it needs the GUE bulk one-point limit).
Their primed successors `UNStep1Good'`, `UNInfty1Row'`, `UNStep1GoodC'`, `UNCoreC'` (owed) differ
only by `UNDens ↦ UNDens'`, the structural hypothesis `UNDens'` = `UNDens` plus the box hypotheses
of `freeConv_stable_lip` (`FreeConvRegular.lean:1238-1240`) uniform in `n`; the shifted data are
never `UNDens'` (`not_unDens'_unDensShift`).  `UNCore'` and `UNDensBandRow'` are proved here
(`un_core_of_rows'`, `unDensBandRow'_of_row`) and are not registered.

Sections: 1 vocabulary and pins; 2 projection, bridges, the generic BA lemma; 3 composition; 4 the
compiled refutation; 5 the semicircle at `E = 0`, `δ = 1/2`; 6 compiled nonempty instances
(`UNDensInst`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ## 1. Vocabulary and pins -/

/-- **`UNDens'` (structural)**: the merged `UNDens` (`Pins.lean:462`) and the box hypotheses `hbox`, `hlip` of
`freeConv_stable_lip` (`FreeConvRegular.lean:1238-1240`) at `mref = m n`, `E₀ = E`, on the box `|Re z - E| ≤ δ`,
`0 < Im z ≤ 1`: `Im` bounded below, bounded, Lipschitz as a complex function, the constants `c K Lp` fixed before
`∀ᶠ n` (uniform in `n`).  Registry class: **structural**; it succeeds `UNDens` as the density hypothesis of the
primed pins (finding T2190a, DECISIONS §66 (1)). -/
def UNDens' (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) : Prop :=
  UNDens m E ρ δ ∧ ∃ c K Lp : ℝ, 0 < c ∧ 0 < K ∧ 0 < Lp ∧ ∀ᶠ n in atTop,
    (∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (m n z).im ∧ ‖m n z‖ ≤ K) ∧
    (∀ z z' : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 →
      |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖m n z - m n z'‖ ≤ Lp * ‖z - z'‖)

/-- **The shift of finding T2190a** (supervisor 1651, 1.1; target 6 of T2190 is the case `m = msc`, `E = 0`):
`m^h_n(z) = m_n(z) + (i/2) 1{Im z < h_n}`.  Not a `Prop`; a definition used by the refutation. -/
noncomputable def unDensShift (m : ℕ → ℂ → ℂ) (h : ℕ → ℝ) : ℕ → ℂ → ℂ :=
  fun n z => m n z + (if z.im < h n then Complex.I / 2 else 0)

/-- **`UNStep1Good'` (owed, UN-12)**: `UNStep1Good` (`Pins.lean:584`, refuted by `not_UNStep1Good`) with
`UNDens ↦ UNDens'`.  Registry class: **owed** (UN-12; consumer UN-13/UN-14, the Step 1 assembly of
`UNInfty1Row'`). -/
def UNStep1Good' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNInfty1Row'` (owed, UN-14)**: `UNInfty1Row` (`Pins.lean:733`, refuted by the argument of the supervisor
verdict 1.3) with `UNDens ↦ UNDens'`.  Registry class: **owed** (UN-14). -/
def UNInfty1Row' : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          ∀ E' : ℝ, |E'| < 2 →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1 sz M ρ E E' k O τU

/-- **`UNCore'`** (composed by `un_core_of_rows'`; not registered): `UNCore` (`Pins.lean:760`) with
`UNDens ↦ UNDens'`. -/
def UNCore' : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAll →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          UNClaimAll sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M ρ E E' k O

/-- **`UNDensBandRow'`** (proved from the merged owed row `UNDensBandRow` by `unDensBandRow'_of_row`; not
registered): `UNDensBandRow` (`Pins.lean:826`) with `UNDens ↦ UNDens'`. -/
def UNDensBandRow' : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∃ δ : ℝ, δ ≤ κ / 2 ∧ UNDens' (fun _ => msc) E (fun _ => rhoSC E) δ

/-- **`UNStep1GoodC'` (owed)**: `UNStep1GoodC` (`PinsK.lean:275`, refuted by `not_UNStep1GoodC`) with
`UNDens ↦ UNDens'`.  Registry class: **owed** (the C-form Step 1: UN-12 or a BA-N ticket). -/
def UNStep1GoodC' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNCoreC'` (owed)**: `UNCoreC` (`PinsK.lean:292`, refuted by the argument of the supervisor verdict 1.3) with
`UNDens ↦ UNDens'`.  Registry class: **owed** (BA-C1b `baBUniv_of_rows`). -/
def UNCoreC' : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAllC →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNTrLocalInit sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀) → UNClaimAllC sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M.toUNModel ρ E E' k O

/-! ## 2. Projection, bridges, the generic BA lemma -/

/-- `UNDens'.toUNDens` (implicit data, so that `h.toUNDens` works). -/
theorem UNDens'.toUNDens {m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ : ℝ} (h : UNDens' m E ρ δ) :
    UNDens m E ρ δ := h.1

/-- Distance between two points of the same vertical line (`FreeConvRegular.lean:353`, private there). -/
private lemma PinsDens_norm_vert (x η η' : ℝ) : ‖(⟨x, η⟩ : ℂ) - ⟨x, η'⟩‖ = |η - η'| := by
  have h1 : (⟨x, η⟩ : ℂ) - ⟨x, η'⟩ = ((η - η' : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The Lipschitz bound of `m_{u ⊞ sc_1}` from the lower bound of `Im` at the two points: the public targets 1
of T2190 re-derived (`FreeConvRegular.lean:363`, private there). -/
private lemma PinsDens_lip_one {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ) {c : ℝ}
    (hc : 0 < c) {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im)
    (h : c ≤ (freeConvST u 1 z).im) (h' : c ≤ (freeConvST u 1 z').im) :
    ‖freeConvST u 1 z - freeConvST u 1 z'‖ ≤ 1 / (2 * c ^ 2) * ‖z - z'‖ := by
  have h1 := freeConvST_sub_le u u 0 1 one_pos (fun i => by simp) z z' hz hz'
  rw [one_pow, one_mul, zero_add] at h1
  have h2 : 4 * c ^ 2 ≤ ((freeConvST u 1 z).im + (freeConvST u 1 z').im) ^ 2 := by nlinarith
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (freeConvST u 1 z - freeConvST u 1 z')]

/-- `|m_{u ⊞ sc_1}| ≤ 1` (`FreeConvRegular.lean:374`, private there). -/
private lemma PinsDens_norm_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ)
    {z : ℂ} (hz : 0 < z.im) : ‖freeConvST u 1 z‖ ≤ 1 := by
  have h := freeConvST_norm_sq_le u 1 zero_le_one z hz
  rw [one_mul] at h
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg (freeConvST u 1 z)]

/-- `unDens'_msc_of_unDens`: for `m = msc` the box hypotheses follow from `UNDens` (`c` from its first clause, the
window `η ≤ 10` contains the box; `K = 1`; `Lp = 1/(2c²)` from `freeConvST_sub_le` through `freeConvST_zero_eq_msc`). -/
theorem unDens'_msc_of_unDens (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : UNDens (fun _ => msc) E ρ δ) :
    UNDens' (fun _ => msc) E ρ δ := by
  refine ⟨h, ?_⟩
  obtain ⟨-, c, C, Lp, hc, -, -, hev⟩ := h
  obtain ⟨n₀, hb, -, -⟩ := hev.exists
  have hlow : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (msc z).im :=
    fun z hz hz1 hz2 => (hb z.re z.im hz hz1 (by linarith)).1
  refine ⟨c, 1, 1 / (2 * c ^ 2), hc, one_pos, by positivity, Eventually.of_forall fun n => ⟨?_, ?_⟩⟩
  · intro z hz hz1 hz2
    exact ⟨hlow z hz hz1 hz2, (norm_msc_lt_one hz1).le⟩
  · intro z z' hz hz1 hz2 hz' hz1' hz2'
    have h := PinsDens_lip_one (fun _ : Fin 1 => (0 : ℝ)) hc hz1 hz1'
      (by rw [FreeConvRegularInst.freeConvST_zero_eq_msc hz1]; exact hlow z hz hz1 hz2)
      (by rw [FreeConvRegularInst.freeConvST_zero_eq_msc hz1']; exact hlow z' hz' hz1' hz2')
    rwa [FreeConvRegularInst.freeConvST_zero_eq_msc hz1,
      FreeConvRegularInst.freeConvST_zero_eq_msc hz1'] at h

/-- `unDensBandRow'_of_row`: the band row in primed form from the merged owed row (no new owed pin). -/
theorem unDensBandRow'_of_row (h : UNDensBandRow) : UNDensBandRow' := by
  intro κ hκ E hE
  obtain ⟨δ, hδ, hD⟩ := h κ hκ E hE
  exact ⟨δ, hδ, unDens'_msc_of_unDens E _ δ hD⟩

/-- `unDens'_freeConvST`: `unDens_freeConvST` (`FreeConvRegular.lean:387`) with `UNDens ↦ UNDens'` (`K = 1` by
target 2, `Lp = 1/(2c²)` by target 1); BA-C1b/BA-C2 cite it for `UNDensBARow'`. -/
theorem unDens'_freeConvST :
    ∀ {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)] (u : ∀ n, ι n → ℝ) (E δ c : ℝ),
      0 < δ → 0 < c →
      (∀ᶠ n in atTop, ∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 → c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) →
      ∃ ρ : ℕ → ℝ, UNDens' (fun n => freeConvST (u n) 1) E ρ δ ∧
        ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 →
          |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n| ≤ η / c ^ 2 := by
  intro ι _ _ u E δ c hδ hc hev
  obtain ⟨ρ, hD, hmod⟩ := unDens_freeConvST u E δ c hδ hc hev
  refine ⟨ρ, ⟨hD, c, 1, 1 / (2 * c ^ 2), hc, one_pos, by positivity, ?_⟩, hmod⟩
  filter_upwards [hev] with n hn
  refine ⟨fun z hz hz1 hz2 => ⟨hn z.re z.im hz hz1 (by linarith), PinsDens_norm_le_one (u n) hz1⟩,
    fun z z' hz hz1 hz2 hz' hz1' hz2' => ?_⟩
  exact PinsDens_lip_one (u n) hc hz1 hz1' (hn z.re z.im hz hz1 (by linarith))
    (hn z'.re z'.im hz' hz1' (by linarith))

/-! ## 3. Composition -/

/-- `un_core_of_rows'` (`UNUnivMainRow` consumed through `UNDens'.toUNDens`): the proof of `un_core_of_rows`
(`Pins.lean:772`). -/
theorem un_core_of_rows' (h1 : UNInfty1Row') (h2 : UNUnivMainRow) : UNCore' := by
  intro h32 hGL hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hN hC E' hE' k _ O hO
  obtain ⟨τ₀, hτ₀, hU⟩ := h2 hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD.toUNDens hT hC k
  obtain ⟨τ₁, hτ₁, hI⟩ := h1 h32 hGL d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hN E' hE' k O hO
  have hpos : 0 < min τ₀ τ₁ := lt_min hτ₀ hτ₁
  have h3 := (hU _ hpos (min_le_left _ _) O hO).add (hI _ hpos (min_le_right _ _))
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

/-- `un_bUniv_of_rows'`: `un_bUniv_of_rows` (`Pins.lean:866`) with `UNInfty1Row ↦ UNInfty1Row'`; the band density
enters through `unDensBandRow'_of_row` (here the merged row `rD` is converted pointwise by
`unDens'_msc_of_unDens`). -/
theorem un_bUniv_of_rows' (rI : UNInfty1Row') (rU : UNUnivMainRow) (rC : UNClaimRow)
    (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow)
    (rT : UNTrLocalBandRow) (rN : UNNormBandRow) :
    UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNGreenCorrAll →
      UNBUniv := by
  intro h32 hML hLoc hQ hGL hGC d hd 𝔠 𝔡 sz hA k hk κ hκ E hE O hO
  have hE2 : |E| < 2 := by linarith
  obtain ⟨δ, hδκ, hDens⟩ := rD κ hκ E hE
  have hTr := rT hLoc d hd 𝔠 𝔡 sz hA κ hκ E hE δ hDens.1 hδκ
  have hCl := un_claimAll_of_rows rC rE rJ rO hML hLoc hQ d hd 𝔠 𝔡 sz hA κ hκ E hE
  have hO' : IsTestFun (fun β => O ((rhoSC E)⁻¹ • β)) :=
    isTestFun_comp_smul hO (inv_ne_zero (rhoSC_pos hE2).ne')
  have hcore := un_core_of_rows' rI rU h32 hGL hGC d hd 𝔠 𝔡 sz hA (UNModel.band sz)
    (fun _ => msc) E (fun _ => rhoSC E) δ (unDens'_msc_of_unDens E _ δ hDens) hTr
    (rN d hd 𝔠 𝔡 sz hA) hCl E hE2 k hk _ hO'
  refine hcore.congr fun n => ?_
  exact unBUniv_diff_eq (UNModel.band sz) hE2 k O n

/-! ## 4. The compiled refutation (supervisor 1.1-1.2) -/

/-- `unDensShift_of_le`: the shifted data agree with `m` on `Im z ≥ h n`. -/
theorem unDensShift_of_le (m : ℕ → ℂ → ℂ) (h : ℕ → ℝ) (n : ℕ) (z : ℂ) (hz : h n ≤ z.im) :
    unDensShift m h n z = m n z := by
  simp [unDensShift, not_lt.mpr hz]

/-- `unDens_shift` (supervisor 1.1, generic `m`, `E`, `δ`): constants `(c, C + 1/2, Lp)`; the indicator does not
depend on `x`, and for `η < h n` the quotient is the old one plus `1/(2π)`, so the limit along `𝓝[>] 0` moves by
`1/(2π)`.  Target 6 of T2190 (`FreeConvRegular.lean:470`) is the case `m = msc`, `E = 0`. -/
theorem unDens_shift (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (hD : UNDens m E ρ δ) :
    UNDens (unDensShift m h) E (fun n => ρ n + 1 / (2 * Real.pi)) δ := by
  obtain ⟨hδ, c, C, Lp, hc, hC, hLp, hev⟩ := hD
  refine ⟨hδ, c, C + 1 / 2, Lp, hc, by positivity, hLp, ?_⟩
  filter_upwards [hev] with n hn
  obtain ⟨hb, hl, ht⟩ := hn
  refine ⟨?_, ?_, ?_⟩
  · intro x η hx hη hη10
    obtain ⟨h1, h2⟩ := hb x η hx hη hη10
    by_cases hcase : η < h n
    · simp only [unDensShift, hcase, ite_true, Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
      constructor <;> linarith
    · simp only [unDensShift, hcase, ite_false, add_zero]
      constructor <;> linarith
  · intro x y η hx hy hη hη10
    have := hl x y η hx hy hη hη10
    by_cases hcase : η < h n
    · simp only [unDensShift, hcase, ite_true, Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
      convert this using 2
      ring
    · simp only [unDensShift, hcase, ite_false, add_zero]
      exact this
  · have h1 : Tendsto (fun η : ℝ => (m n ⟨E, η⟩).im / Real.pi + 1 / (2 * Real.pi)) (𝓝[>] 0)
        (𝓝 (ρ n + 1 / (2 * Real.pi))) := ht.add_const _
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (hh n)] with η hη
    have hcase : (⟨E, η⟩ : ℂ).im < h n := hη.2
    simp only [unDensShift, hcase, ite_true, Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
    field_simp

/-- `1 ≤ N` at every size index (`UNKInst.inWindow_nonempty`, `PinsK.lean:608`, for general `d`). -/
private theorem PinsDens_one_le_Nsz {d : ℕ} (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  have h1 : 1 ≤ sz.size n := by
    simp only [Sizes.size]
    have := sz.three_le_L n
    have := sz.W_pos n
    exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by omega))
  exact_mod_cast h1

private theorem PinsDens_Nsz_pos {d : ℕ} (sz : Sizes d) (n : ℕ) : (0 : ℝ) < Nsz sz n :=
  lt_of_lt_of_le one_pos (PinsDens_one_le_Nsz sz n)

/-- `N^{-2} ≤ N^{-1+ε}` for `ε > 0`: the window of `UNTrLocal` lies above the shift height. -/
private theorem PinsDens_rpow_two_le {d : ℕ} (sz : Sizes d) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nsz sz n ^ (-2 : ℝ) ≤ Nsz sz n ^ (-1 + ε) :=
  Real.rpow_le_rpow_of_exponent_le (PinsDens_one_le_Nsz sz n) (by linarith)

/-- `unTrLocal_shift`: at `h n = N^{-2} ≤ N^{-1+ε}` the event of `UNTrLocal` does not change. -/
theorem unTrLocal_shift {d : ℕ} (sz : Sizes d) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ)
    (hT : UNTrLocal sz M m E δ) :
    UNTrLocal sz M (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E δ := by
  intro ε τ D hε hτ hD
  filter_upwards [hT ε τ D hε hτ hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨z, h1, h2, h3, h4⟩
  refine ⟨z, h1, h2, h3, ?_⟩
  rwa [unDensShift_of_le m (fun n => Nsz sz n ^ (-2 : ℝ)) n z
    ((PinsDens_rpow_two_le sz n hε).trans h2)] at h4

/-- `unTrLocalInit_shift`: the same for `UNTrLocalInit`. -/
theorem unTrLocalInit_shift {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ)
    (hT : UNTrLocalInit sz M m E δ) :
    UNTrLocalInit sz M (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E δ := by
  intro τs hτs hτs1 ε τ D hε hτ hD
  filter_upwards [hT τs hτs hτs1 ε τ D hε hτ hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨z, h1, h2, h3, h4⟩
  refine ⟨z, h1, h2, h3, ?_⟩
  rwa [unDensShift_of_le m (fun n => Nsz sz n ^ (-2 : ℝ)) n z
    ((PinsDens_rpow_two_le sz n hε).trans h2)] at h4

/-- `not_unDens'_unDensShift` (the "two data, one model" test, compiled half): the shift of a `UNDens'` datum is
never `UNDens'` once `h n ≤ 1` (a jump `1/2` across `Im z = h n` against a uniform `Lp`). -/
theorem not_unDens'_unDensShift (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ ρ' : ℕ → ℝ) (δ : ℝ) (h : ℕ → ℝ)
    (hh : ∀ n, 0 < h n) (h1 : ∀ᶠ n in atTop, h n ≤ 1) (hD : UNDens' m E ρ δ) :
    ¬ UNDens' (unDensShift m h) E ρ' δ := by
  intro hD'
  obtain ⟨⟨hδ, -⟩, c, K, Lp, hc, hK, hLp, hev⟩ := hD
  obtain ⟨-, c', K', Lp', hc', hK', hLp', hev'⟩ := hD'
  obtain ⟨n, ⟨-, hl⟩, ⟨-, hl'⟩, hn1⟩ := (hev.and (hev'.and h1)).exists
  set a := h n with ha
  have ha0 : 0 < a := hh n
  set ε' := min (a / 2) (1 / (4 * (Lp + Lp'))) with hε'
  have hLL : 0 < Lp + Lp' := by linarith
  have hε0 : 0 < ε' := lt_min (by linarith) (by positivity)
  have hε1 : ε' ≤ a / 2 := min_le_left _ _
  have hε2 : ε' ≤ 1 / (4 * (Lp + Lp')) := min_le_right _ _
  -- the two points of the box
  have hz1 : |(⟨E, a⟩ : ℂ).re - E| ≤ δ := by simpa using hδ.le
  have hz2 : |(⟨E, a - ε'⟩ : ℂ).re - E| ≤ δ := by simpa using hδ.le
  have hzi : 0 < (⟨E, a⟩ : ℂ).im := ha0
  have hzi' : 0 < (⟨E, a - ε'⟩ : ℂ).im := by change 0 < a - ε'; linarith
  have hzj : (⟨E, a⟩ : ℂ).im ≤ 1 := hn1
  have hzj' : (⟨E, a - ε'⟩ : ℂ).im ≤ 1 := by change a - ε' ≤ 1; linarith
  have hnorm : ‖(⟨E, a⟩ : ℂ) - ⟨E, a - ε'⟩‖ = ε' := by
    rw [PinsDens_norm_vert, show a - (a - ε') = ε' by ring, abs_of_pos hε0]
  have hA := hl _ _ hz1 hzi hzj hz2 hzi' hzj'
  have hB := hl' _ _ hz1 hzi hzj hz2 hzi' hzj'
  rw [hnorm] at hA hB
  -- the shifted values
  have hv1 : unDensShift m h n ⟨E, a⟩ = m n ⟨E, a⟩ :=
    unDensShift_of_le m h n _ (le_refl a)
  have hv2 : unDensShift m h n ⟨E, a - ε'⟩ = m n ⟨E, a - ε'⟩ + Complex.I / 2 := by
    have : (⟨E, a - ε'⟩ : ℂ).im < h n := by change a - ε' < a; linarith
    simp only [unDensShift, this, ite_true]
  rw [hv1, hv2] at hB
  have hI : ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, Complex.norm_I]; simp
  have key : (Complex.I / 2 : ℂ) = (m n ⟨E, a⟩ - m n ⟨E, a - ε'⟩) -
      (m n ⟨E, a⟩ - (m n ⟨E, a - ε'⟩ + Complex.I / 2)) := by ring
  have h2 : 1 / 2 ≤ ‖m n ⟨E, a⟩ - m n ⟨E, a - ε'⟩‖ +
      ‖m n ⟨E, a⟩ - (m n ⟨E, a - ε'⟩ + Complex.I / 2)‖ := by
    rw [← hI]
    calc ‖(Complex.I / 2 : ℂ)‖ = ‖(m n ⟨E, a⟩ - m n ⟨E, a - ε'⟩) -
        (m n ⟨E, a⟩ - (m n ⟨E, a - ε'⟩ + Complex.I / 2))‖ := by rw [← key]
      _ ≤ _ := norm_sub_le _ _
  have h3 : 1 / 2 ≤ (Lp + Lp') * ε' := by nlinarith
  have h4 : (Lp + Lp') * ε' ≤ 1 / 4 := by
    calc (Lp + Lp') * ε' ≤ (Lp + Lp') * (1 / (4 * (Lp + Lp'))) :=
          mul_le_mul_of_nonneg_left hε2 hLL.le
      _ = 1 / 4 := by field_simp
  linarith

/-- Two events of probability `≤ x < 1/2` miss a common point (the "two small events miss a point" step of the
refutation). -/
private theorem PinsDens_exists_not_mem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B₁ B₂ : Set Ω) (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1 / 2)
    (h₁ : μ B₁ ≤ ENNReal.ofReal x) (h₂ : μ B₂ ≤ ENNReal.ofReal x) : ∃ ω, ω ∉ B₁ ∧ ω ∉ B₂ := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set Ω) ⊆ B₁ ∪ B₂ := fun ω _ => by
    by_cases h : ω ∈ B₁
    · exact Or.inl h
    · exact Or.inr (hcon ω h)
  have h1 : μ Set.univ ≤ μ (B₁ ∪ B₂) := measure_mono hsub
  rw [measure_univ] at h1
  have h2 : 1 ≤ ENNReal.ofReal x + ENNReal.ofReal x :=
    h1.trans ((measure_union_le _ _).trans (add_le_add h₁ h₂))
  rw [← ENNReal.ofReal_add hx0 hx0] at h2
  have h3 : ENNReal.ofReal (x + x) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  exact absurd h2 (not_le.mpr h3)

/-- Two solutions of the free-convolution equation `(2.5)` of `[32]` for the same `v`, `t` have the same limit
density at `0`: so two limits `ρ'` within `r` of `ρ₀` and of `ρ₀ + a` force `a ≤ 2 r` (the "same `ρ'`" step of
the refutation). -/
private theorem PinsDens_rho_eq {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (r ρ₀ a : ℝ)
    (P₁ : ∃ mfc : ℂ → ℂ, IsFreeConv32 v t mfc ∧ ∃ ρ' : ℝ,
      Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - ρ₀| ≤ r)
    (P₂ : ∃ mfc : ℂ → ℂ, IsFreeConv32 v t mfc ∧ ∃ ρ' : ℝ,
      Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - (ρ₀ + a)| ≤ r) :
    a ≤ 2 * r := by
  obtain ⟨f, hf, p, hp, hpr⟩ := P₁
  obtain ⟨g, hg, q, hq, hqr⟩ := P₂
  have hfg : ∀ η : ℝ, 0 < η → f ⟨0, η⟩ = g ⟨0, η⟩ := fun η hη =>
    isFreeConv32_unique v ht hf hg (z := ⟨0, η⟩) hη
  have hq' : Tendsto (fun η : ℝ => (f ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 q) := by
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [hfg η hη]
  have hpq : p = q := tendsto_nhds_unique hp hq'
  subst hpq
  rw [abs_le] at hpr hqr
  linarith [hpr.1, hpr.2, hqr.1, hqr.2]

/-- The generic refutation: if two Step 1 bad events (same random diagonal `v`, same OU time, densities `ρ` and
`ρ + 1/(2π)`) both have probability `≤ N^{-1}` eventually, and `N_n → ∞`, there is a contradiction.  Shared by
`not_UNStep1Good` and `not_UNStep1GoodC`; the regularity clauses `Reg₁`, `Reg₂` are arbitrary. -/
private theorem PinsDens_refute {d : ℕ} (sz : Sizes d) (hsz : Tendsto (fun n => Nsz sz n) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : ∀ n, Ω → Idx d (sz.L n) (sz.W n) → ℝ) (Reg₁ Reg₂ : ℕ → Ω → Prop) (ρ : ℕ → ℝ) (τs : ℝ)
    (hτs : 0 < τs)
    (h₁ : ∀ᶠ n in atTop, μ {ω | ¬ (Reg₁ n ω ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (v n ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-(1 : ℝ))))
    (h₂ : ∀ᶠ n in atTop, μ {ω | ¬ (Reg₂ n ω ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (v n ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - (ρ n + 1 / (2 * Real.pi))| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-(1 : ℝ)))) : False := by
  have hτ8 : 0 < 3 * τs / 8 := by positivity
  have t1 : Tendsto (fun n => Nsz sz n ^ (-(1 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop one_pos).comp hsz
  have t2 : Tendsto (fun n => Nsz sz n ^ (-(3 * τs / 8))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hτ8).comp hsz
  have hπ : 0 < 1 / (4 * Real.pi) := by positivity
  obtain ⟨n, hn1, hn2, hs1, hs2⟩ := (h₁.and (h₂.and
    ((t1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).and
      (t2.eventually (gt_mem_nhds hπ))))).exists
  have hN := PinsDens_Nsz_pos sz n
  have hx0 : 0 ≤ Nsz sz n ^ (-(1 : ℝ)) := Real.rpow_nonneg hN.le _
  obtain ⟨ω, hω1, hω2⟩ := PinsDens_exists_not_mem μ _ _ _ hx0 hs1 hn1 hn2
  have p1 := not_not.mp hω1
  have p2 := not_not.mp hω2
  have ht : 0 < 1 - Real.exp (-(ouTStar sz τs n)) := by
    have : 0 < ouTStar sz τs n := Real.rpow_pos_of_pos hN _
    have h2 : Real.exp (-(ouTStar sz τs n)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hfin := PinsDens_rho_eq (v n ω) ht (Nsz sz n ^ (-(3 * τs / 8))) (ρ n) (1 / (2 * Real.pi))
    p1.2 p2.2
  have h4 : 2 * (1 / (4 * Real.pi)) = 1 / (2 * Real.pi) := by field_simp; ring
  linarith

/-- `not_UNStep1Good` (supervisor 1.2): `UNStep1Good` refutes every datum that meets its hypotheses.  Proof:
`τ_s = min (𝔠𝔡) (1/2)`, `D = 1`, `h_n = N^{-2}`; `UNStep1Good` at `(m, ρ)` and at `(unDensShift m h, ρ + 1/(2π))`
(`unDens_shift`, `unTrLocal_shift`); both bad events have measure `≤ N^{-1}` eventually, so some `ω` is outside
both; on it both events use the same `vOU` and the same OU time, so by uniqueness of the free-convolution
solution the limit densities coincide, and `1/(2π) ≤ 2 N^{-3τ_s/8}`, false for large `N` (eventual only). -/
theorem not_UNStep1Good (hS : UNStep1Good) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
          UNNormBound sz M CV₀ → False := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV hN
  have hτs0 : 0 < min (𝔠 * 𝔡) (1 / 2) := lt_min (mul_pos hA.1 hA.2.1) (by norm_num)
  have hτs1 : min (𝔠 * 𝔡) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hτsle : min (𝔠 * 𝔡) (1 / 2) ≤ 𝔠 * 𝔡 := min_le_left _ _
  have hh : ∀ n, 0 < (fun n => Nsz sz n ^ (-2 : ℝ)) n := fun n =>
    Real.rpow_pos_of_pos (PinsDens_Nsz_pos sz n) _
  obtain ⟨c₁, C₁, hc₁, hev₁⟩ := hS d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV hN
    (min (𝔠 * 𝔡) (1 / 2)) 1 hτs0 hτs1 hτsle one_pos
  obtain ⟨c₂, C₂, hc₂, hev₂⟩ := hS d hd 𝔠 𝔡 sz hA M
    (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E (fun n => ρ n + 1 / (2 * Real.pi)) δ
    (unDens_shift m E ρ δ _ hh hD) (unTrLocal_shift sz M m E δ hT) CV₀ hCV hN
    (min (𝔠 * 𝔡) (1 / 2)) 1 hτs0 hτs1 hτsle one_pos
  exact PinsDens_refute sz hA.2.2.1 M.μ (fun n ω => vOU sz M n (min (𝔠 * 𝔡) (1 / 2)) E ω)
    (fun n ω => IsRegular32 (vOU sz M n (min (𝔠 * 𝔡) (1 / 2)) E ω)
      (Nsz sz n ^ (-1 + (min (𝔠 * 𝔡) (1 / 2)) / 4))
      (Nsz sz n ^ (-(min ((min (𝔠 * 𝔡) (1 / 2)) / 4) ((1 - (min (𝔠 * 𝔡) (1 / 2))) / 3)))) c₁ C₁
      (CV₀ + 1))
    (fun n ω => IsRegular32 (vOU sz M n (min (𝔠 * 𝔡) (1 / 2)) E ω)
      (Nsz sz n ^ (-1 + (min (𝔠 * 𝔡) (1 / 2)) / 4))
      (Nsz sz n ^ (-(min ((min (𝔠 * 𝔡) (1 / 2)) / 4) ((1 - (min (𝔠 * 𝔡) (1 / 2))) / 3)))) c₂ C₂
      (CV₀ + 1))
    ρ _ hτs0 hev₁ hev₂

/-- `not_UNStep1GoodC` (supervisor 1.2, last line): the same for the C form (`vOUC`, `UNTrLocalInit`). -/
theorem not_UNStep1GoodC (hS : UNStep1GoodC) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
          UNNormBound sz M.toUNModel CV₀ → False := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV hN
  have hτs0 : 0 < min (𝔠 * 𝔡) (1 / 2) := lt_min (mul_pos hA.1 hA.2.1) (by norm_num)
  have hτs1 : min (𝔠 * 𝔡) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hτsle : min (𝔠 * 𝔡) (1 / 2) ≤ 𝔠 * 𝔡 := min_le_left _ _
  have hh : ∀ n, 0 < (fun n => Nsz sz n ^ (-2 : ℝ)) n := fun n =>
    Real.rpow_pos_of_pos (PinsDens_Nsz_pos sz n) _
  obtain ⟨c₁, C₁, hc₁, hev₁⟩ := hS d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV hN
    (min (𝔠 * 𝔡) (1 / 2)) 1 hτs0 hτs1 hτsle one_pos
  obtain ⟨c₂, C₂, hc₂, hev₂⟩ := hS d hd 𝔠 𝔡 sz hA M
    (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E (fun n => ρ n + 1 / (2 * Real.pi)) δ
    (unDens_shift m E ρ δ _ hh hD) (unTrLocalInit_shift sz M m E δ hT) CV₀ hCV hN
    (min (𝔠 * 𝔡) (1 / 2)) 1 hτs0 hτs1 hτsle one_pos
  exact PinsDens_refute sz hA.2.2.1 M.μ (fun n ω => vOUC sz M n (min (𝔠 * 𝔡) (1 / 2)) E ω)
    (fun n ω => IsRegular32 (vOUC sz M n (min (𝔠 * 𝔡) (1 / 2)) E ω)
      (Nsz sz n ^ (-1 + (min (𝔠 * 𝔡) (1 / 2)) / 4))
      (Nsz sz n ^ (-(min ((min (𝔠 * 𝔡) (1 / 2)) / 4) ((1 - (min (𝔠 * 𝔡) (1 / 2))) / 3)))) c₁ C₁
      (CV₀ + 1))
    (fun n ω => IsRegular32 (vOUC sz M n (min (𝔠 * 𝔡) (1 / 2)) E ω)
      (Nsz sz n ^ (-1 + (min (𝔠 * 𝔡) (1 / 2)) / 4))
      (Nsz sz n ^ (-(min ((min (𝔠 * 𝔡) (1 / 2)) / 4) ((1 - (min (𝔠 * 𝔡) (1 / 2))) / 3)))) c₂ C₂
      (CV₀ + 1))
    ρ _ hτs0 hev₁ hev₂

/-! ## 5. The semicircle at `E = 0`, `δ = 1/2` -/

/-- `un_msc_box_zero`: `c = 9/100`, `K = 1`, `Lp = 62` on the box at `E = 0`, `δ = 1/2` (`c` from `un_msc_im_ge`,
`K` from `norm_msc_lt_one`, `Lp` from target 1 of T2190 through the bridge: `1/(2c²) = 61.73 ≤ 62`;
`un_msc_lip`'s `10000/81` is too large). -/
theorem un_msc_box_zero :
    ∀ z z' : ℂ, |z.re - 0| ≤ 1 / 2 → 0 < z.im → z.im ≤ 1 → |z'.re - 0| ≤ 1 / 2 → 0 < z'.im → z'.im ≤ 1 →
      9 / 100 ≤ (msc z).im ∧ ‖msc z‖ ≤ 1 ∧ ‖msc z - msc z'‖ ≤ 62 * ‖z - z'‖ := by
  intro z z' hz hz1 hz2 hz' hz1' hz2'
  have hlow : ∀ y : ℂ, |y.re - 0| ≤ 1 / 2 → 0 < y.im → y.im ≤ 1 → 9 / 100 ≤ (msc y).im :=
    fun y hy1 hy2 hy3 => un_msc_im_ge hy2 (by linarith) (by simpa using hy1)
  refine ⟨hlow z hz hz1 hz2, (norm_msc_lt_one hz1).le, ?_⟩
  have h := PinsDens_lip_one (fun _ : Fin 1 => (0 : ℝ)) (c := 9 / 100) (by norm_num) hz1 hz1'
    (by rw [FreeConvRegularInst.freeConvST_zero_eq_msc hz1]; exact hlow z hz hz1 hz2)
    (by rw [FreeConvRegularInst.freeConvST_zero_eq_msc hz1']; exact hlow z' hz' hz1' hz2')
  rw [FreeConvRegularInst.freeConvST_zero_eq_msc hz1,
    FreeConvRegularInst.freeConvST_zero_eq_msc hz1'] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)

/-- `un_dens'_msc_zero`: `UNDens'` at the semicircle, `E = 0`, `δ = 1/2` (`un_dens_msc_zero` and `un_msc_box_zero`):
the constants of `stable_lip_msc` (`FreeConvRegular.lean:1394`). -/
theorem un_dens'_msc_zero : UNDens' (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) :=
  ⟨un_dens_msc_zero, 9 / 100, 1, 62, by norm_num, by norm_num, by norm_num,
    Eventually.of_forall fun _ =>
      ⟨fun z hz hz1 hz2 => ⟨(un_msc_box_zero z z hz hz1 hz2 hz hz1 hz2).1,
          (un_msc_box_zero z z hz hz1 hz2 hz hz1 hz2).2.1⟩,
        fun z z' hz hz1 hz2 hz' hz1' hz2' => (un_msc_box_zero z z' hz hz1 hz2 hz' hz1' hz2').2.2⟩⟩

/-! ## 6. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

The data are those of `UNInst` (`Pins.lean`, section 7): `RBM.Gauss.SizesInst.sz0` (`n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10` (`κ = 1` in `not_UNStep1Good_band`), `k = 1`,
`E = 0`, `E' = 0`, `δ = 1/2`, `𝒪 = bump`.  Hypotheses that are pins of other gates (the rows, the consumed shapes,
`UNL32`, `UNGUELocal`, `UNGreenCorrAll(C)`, `UNTrLocal`, `UNTrLocalInit`, the norm bound) stay hypotheses; every
deterministic hypothesis (`Admissible`, `|0| < 2`, `IsTestFun bump`, `UNDens'`) is discharged. -/

namespace UNDensInst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `unDensShift` height `N^{-2} ≤ 1`. -/
private theorem PinsDens_rpow_two_le_one {d : ℕ} (sz : Sizes d) (n : ℕ) :
    Nsz sz n ^ (-2 : ℝ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (PinsDens_one_le_Nsz sz n) (by norm_num)

/-- `inst_core_band'`: `UNInst.inst_core_band` (`Pins.lean:1773`) with `UNCore ↦ UNCore'`. -/
theorem inst_core_band' (hcore : UNCore') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAll)
    (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.band sz0) 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
  hcore h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero hT hN hC 0 (by norm_num) 1 le_rfl bump bump_testFun

/-- `inst_core_of_rows'`: `UNInst.inst_core_of_rows` (`Pins.lean:1888`) with `UNInfty1Row ↦ UNInfty1Row'`. -/
theorem inst_core_of_rows' (rI : UNInfty1Row') (rU : UNUnivMainRow) (h32 : UNL32) (hGL : UNGUELocal)
    (hGC : UNGreenCorrAll) (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.band sz0) 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
  un_core_of_rows' rI rU h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0)
    (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero hT hN hC 0 (by norm_num) 1 le_rfl
    bump bump_testFun

/-- `inst_bUniv_band'`: `UNInst.inst_bUniv_band` (`Pins.lean:1757`) with `UNInfty1Row ↦ UNInfty1Row'`, through
`un_bUniv_of_rows'`. -/
theorem inst_bUniv_band' (rI : UNInfty1Row') (rU : UNUnivMainRow) (rC : UNClaimRow) (rE : UNEMCTE2Row)
    (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow) (rT : UNTrLocalBandRow)
    (rN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand)
    (hQ : UNQueBand) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
      atTop (𝓝 0) :=
  un_bUniv_of_rows' rI rU rC rE rJ rO rD rT rN h32 hML hLoc hQ hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0
    sz0_adm 1 le_rfl (1 / 10) (by norm_num) 0 (by norm_num) bump bump_testFun

/-- `inst_bUniv_band_k'`: `UNKInst.inst_bUniv_band_k` (`PinsK.lean:653`) with `UNInfty1Row ↦ UNInfty1Row'`; the
four band rows in generic form go through the merged row bridges (`PinsK.lean:666-667`). -/
theorem inst_bUniv_band_k' (rI : UNInfty1Row') (rU : UNUnivMainRow)
    (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d))
    (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand)
    (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (rD : UNDensBandRow) (rT : UNTrLocalBandRow) (rN : UNNormBandRow) (h32 : UNL32)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) (hGL : UNGUELocal)
    (hGC : UNGreenCorrAll) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
      atTop (𝓝 0) :=
  inst_bUniv_band' rI rU (UNClaimRowk_band.1 rC) (UNEMCTE2Rowk_band.1 rE) (UNJakUywRowk_band.1 rJ)
    (UNOURowk_band.1 rO) rD rT rN h32 hML hLoc hQ hGL hGC

/-- `inst_coreC_band'`: `UNKInst.inst_coreC_band` (`PinsK.lean:673`) with `UNCoreC ↦ UNCoreC'`. -/
theorem inst_coreC_band' (hcore : UNCoreC') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC)
    (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hTi : UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAllC sz0 (UNModel.band sz0).toC 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
  hcore h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0).toC (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero hT hTi hN hC 0 (by norm_num) 1 le_rfl bump bump_testFun

/-- `inst_dens'_uI`: `unDens'_freeConvST` at the constant BA-class sequence `u n = uI`, `E = 0`, `δ = 1/2`,
`c = 1/20` (`uI_lower`): all hypotheses discharged. -/
theorem inst_dens'_uI :
    ∃ ρ : ℕ → ℝ, UNDens' (fun _ : ℕ => freeConvST FreeConvRegularInst.uI 1) 0 ρ (1 / 2) ∧
      ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 →
        |(freeConvST FreeConvRegularInst.uI 1 ⟨0, η⟩).im / Real.pi - ρ n| ≤ η / (1 / 20 : ℝ) ^ 2 :=
  unDens'_freeConvST (ι := fun _ : ℕ => Fin 2) (fun _ => FreeConvRegularInst.uI) 0 (1 / 2) (1 / 20)
    (by norm_num) (by norm_num)
    (Eventually.of_forall fun _ x η hx hη hη10 => FreeConvRegularInst.uI_lower (z := ⟨x, η⟩)
      (by simpa using hx) hη hη10)

/-- `inst_T2190a_family`: the T2190a family at `sz0` (`h n = N_n^{-2}`) meets `UNDens` and the band local law
whenever `msc` does, and is not `UNDens'`. -/
theorem inst_T2190a_family :
    UNDens (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0
        (fun _ => rhoSC 0 + 1 / (2 * Real.pi)) (1 / 2) ∧
      (UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
        UNTrLocal sz0 (UNModel.band sz0) (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0
          (1 / 2)) ∧
      ¬ UNDens' (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0
        (fun _ => rhoSC 0 + 1 / (2 * Real.pi)) (1 / 2) := by
  have hh : ∀ n, 0 < (fun n => Nsz sz0 n ^ (-2 : ℝ)) n := fun n =>
    Real.rpow_pos_of_pos (PinsDens_Nsz_pos sz0 n) _
  exact ⟨unDens_shift (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) _ hh un_dens_msc_zero,
    unTrLocal_shift sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2),
    not_unDens'_unDensShift (fun _ => msc) 0 (fun _ => rhoSC 0) _ (1 / 2) _ hh
      (Eventually.of_forall fun n => PinsDens_rpow_two_le_one sz0 n) un_dens'_msc_zero⟩

/-- `not_UNStep1Good_band`: the band rows refute `UNStep1Good` (`sz0`, `E = 0`, `δ = 1/2`, `κ = 1`,
`un_dens_msc_zero`): the supervisor's sentence "the band model does" as a compiled fact. -/
theorem not_UNStep1Good_band (hS : UNStep1Good) (hLoc : UNLocAvgBand) (rT : UNTrLocalBandRow)
    (rN : UNNormBandRow) : False := by
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact not_UNStep1Good hS 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    CV₀ hCV hN

/-- Instance of `not_UNStep1GoodC` at `sz0`, `(UNModel.band sz0).toC`, `msc`, `E = 0`, `ρ = rhoSC 0`,
`δ = 1/2`, `un_dens_msc_zero`; the norm bound from the band row. -/
example (hS : UNStep1GoodC)
    (hTi : UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2)) (rN : UNNormBandRow) :
    False := by
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact not_UNStep1GoodC hS 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0).toC (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens_msc_zero hTi CV₀ hCV hN

/-- Instance of `unTrLocalInit_shift` at the same data (`h n = N_n^{-2}`). -/
example (hTi : UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2)) :
    UNTrLocalInit sz0 (UNModel.band sz0).toC
      (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0 (1 / 2) :=
  unTrLocalInit_shift sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2) hTi

/-- Instance of `unDensBandRow'_of_row` at `κ = 1/10`, `E = 0`. -/
example (rD : UNDensBandRow) :
    ∃ δ : ℝ, δ ≤ 1 / 10 / 2 ∧ UNDens' (fun _ => msc) 0 (fun _ => rhoSC 0) δ :=
  unDensBandRow'_of_row rD (1 / 10) (by norm_num) 0 (by norm_num)

end UNDensInst

end RBM.Univ

end
