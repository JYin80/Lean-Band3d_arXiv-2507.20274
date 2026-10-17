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

/-! ## 2. Projection, bridges, the generic BA lemma -/

/-- `UNDens'.toUNDens` (implicit data, so that `h.toUNDens` works). -/
theorem UNDens'.toUNDens {m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ : ℝ} (h : UNDens' m E ρ δ) :
    UNDens m E ρ δ := h.1

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

/-! ## 5. The semicircle at `E = 0`, `δ = 1/2` -/

/-! ## 6. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

The data are those of `UNInst` (`Pins.lean`, section 7): `RBM.Gauss.SizesInst.sz0` (`n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10` (`κ = 1` in `not_UNStep1Good_band`), `k = 1`,
`E = 0`, `E' = 0`, `δ = 1/2`, `𝒪 = bump`.  Hypotheses that are pins of other gates (the rows, the consumed shapes,
`UNL32`, `UNGUELocal`, `UNGreenCorrAll(C)`, `UNTrLocal`, `UNTrLocalInit`, the norm bound) stay hypotheses; every
deterministic hypothesis (`Admissible`, `|0| < 2`, `IsTestFun bump`, `UNDens'`) is discharged. -/

end RBM.Univ

end
