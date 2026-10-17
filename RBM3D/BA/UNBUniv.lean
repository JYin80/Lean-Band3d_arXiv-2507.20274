/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.BandTerminal
import RBM3D.BA.EMCTE2BA
import RBM3D.BA.MATrLocalBA
import RBM3D.BA.MADecolQUE
import RBM3D.BA.GUEKPrim
import RBM3D.BA.GUEHyp
import RBM3D.BA.MainIndTermBA
import RBM3D.Universality.NormBand
import RBM3D.Universality.PinsKD
import RBM3D.Universality.GUEPhase.RandomLayerBGD

/-!
# T2520 (BA leaf): the block Anderson filtered assembly and the end `BAThm27L 3`

MN-D3 D3-D6 and N2's own rows (`docs/reports/T2513-design.md` §3, §5, §6; DECISIONS §316, §336,
§340, §353).  New declarations only; no merged statement is edited (MNO-C1).

* §1 the BA readings of the filtered pins (`UNLocAvgBAD`, `UNQueBAD`, `UNOURowBAD`,
  `UNEMCTE2RowBAD`, `UNJakUywRowBAD`, `UNClaimRowBAD`) and the two one-line links to the per-`d`
  texts of M1 and M3 (`UNLocAvgBAAt`, `MAPins:170`; `UNQueBAAt`, `MADecolQUE:52`):
  `unLocAvgBAD_iff_at`, `unQueBAD_iff_at` (§340 (2));
* §2 the filtered BA assembly: `jakUywRowkD` (the filtered `jakUywRowk`, `EMCTE2BA:629`),
  `un_claimAll_of_rowsBAD`, `baBUniv_of_rowsD` (the filtered `baBUniv_of_rows`, `UNPins:367`, with
  the two TrLocal inputs at the per-`d` core types of M1 row b);
* §3 N2's rows: `unNormBARow_holds` (`(2.3)` of [32] at `H = λ Ψ + V`, twin of `unNormBandRow`,
  `NormBand:173`, at `sz.withLam 0`), `unEMCTE2RowBAD_holds`, `unG1RowkBAD_holds`,
  `unOURowBAD_holds` and, from the unfiltered producers of T2519, `unG1RowkBA_holds`,
  `unOURowBA_holds` (the merged `∀ d` implication `UNOURowBA`, `UNPins:123`);
* §4 the end in `RBM.BA`: `baEnd_BUnivL_of_ML`, `baThm27L_of_ML` (per `d`),
  `baEnd_BUnivL_three`, `baThm27L_three` (`UNL32 → BAEnd_BUnivL 3`, `UNL32 → BAThm27L 3`: the only
  external hypothesis is `UNL32`), `baThm27L_any` (general `d` under `STStep5IIIgL d`);
* §5 compiled nonempty instances at `d = 3`, `S0`.

C5 names read (T2519): `BAKFam`, `BAPB` (`BA/GUEProcBA:76, 93`), `ba_prodG`, `ba_LLG`, `ba_QueG`
(`BA/GUEHyp`).  Paper: `Thm: B_Univ` for block Anderson, `1_2:452-460`, `MR:decol_BA` `1_2:655`;
D723 (BA Theorem 2.7 at `d = 3`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private UNPins_normBound_mono UNPins_psiI_rowsum UNPins_hg_3_10 from RBM3D.BA.UNPins
open private NormBand_eig_le NormBand_Xentry_le NormBand_tail_eventually NormBand_subgaussian from RBM3D.Universality.NormBand

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints RBM.Univ.GUEPhase RBM.BA RBM.BA.UNPinsInst RBM.Univ.BAInst
open scoped NNReal ENNReal

/-! ## 1. The BA readings and the links to the per-`d` texts of M1 and M3 -/

/-- `UNLocAvgBAD`: `UNLocAvgkD` at the block Anderson kind (the filtered `UNLocAvgBA`, `UNPins:103`). -/
def UNLocAvgBAD (Dm : ℕ → Prop) : Prop := UNLocAvgkD Dm (fun d => UNKind.ba d)

/-- `UNQueBAD`: `UNQuekD` at the block Anderson kind (the filtered `UNQueBA`, `UNPins:99`). -/
def UNQueBAD (Dm : ℕ → Prop) : Prop := UNQuekD Dm (fun d => UNKind.ba d)

/-- `UNOURowBAD`: `UNOURowkD` at the block Anderson kind with `ML := ∀ d, Dm d → UNMLOutBA d` (the filtered `UNOURowBA`,
`UNPins:123`). -/
def UNOURowBAD (Dm : ℕ → Prop) : Prop :=
  UNOURowkD Dm (fun d => UNKind.ba d) (∀ d : ℕ, Dm d → UNMLOutBA d) (UNLocAvgBAD Dm) (UNQueBAD Dm)

/-- `UNEMCTE2RowBAD`: `UNEMCTE2RowkD` at the block Anderson kind (the filtered `UNEMCTE2RowBA`, `UNPins:128`). -/
def UNEMCTE2RowBAD (Dm : ℕ → Prop) : Prop := UNEMCTE2RowkD Dm (fun d => UNKind.ba d)

/-- `UNJakUywRowBAD`: `UNJakUywRowkD` at the block Anderson kind (the filtered `UNJakUywRowBA`, `UNPins:132`). -/
def UNJakUywRowBAD (Dm : ℕ → Prop) : Prop := UNJakUywRowkD Dm (fun d => UNKind.ba d) (UNLocAvgBAD Dm)

/-- `UNClaimRowBAD`: `UNClaimRowkD` at the block Anderson kind (the filtered `UNClaimRowBA`, `UNPins:136`). -/
def UNClaimRowBAD (Dm : ℕ → Prop) : Prop := UNClaimRowkD Dm (fun d => UNKind.ba d)

/-- `unLocAvgBAD_iff_at`: the filtered reading at `Dm = (· = d)` is M1's per-`d` text `UNLocAvgBAAt` (`MAPins:170`). -/
theorem unLocAvgBAD_iff_at (d : ℕ) : UNLocAvgBAD (· = d) ↔ (3 ≤ d → UNLocAvgBAAt d) :=
  ⟨fun h hd => h d rfl hd, fun h d' hdd hd => by subst hdd; exact h hd⟩

/-- `unQueBAD_iff_at`: the same for M3's per-`d` text `UNQueBAAt` (`MADecolQUE:52`). -/
theorem unQueBAD_iff_at (d : ℕ) : UNQueBAD (· = d) ↔ (3 ≤ d → UNQueBAAt d) :=
  ⟨fun h hd => h d rfl hd, fun h d' hdd hd => by subst hdd; exact h hd⟩

/-! ## 2. The filtered BA assembly -/

/-- `jakUywRowkD`: `UNJakUywRowkD` for every filter and kind that satisfies the three kind hypotheses (the filtered
`jakUywRowk`, `EMCTE2BA:629`; it imports `BA/EMCTE2BA`, so it lives here). -/
theorem jakUywRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (hbw : UNBulkWindowk K) (hbb : UNBadBoundk K)
    (hbb2 : UNBad2Boundk K) (Loc : Prop) : UNJakUywRowkD Dm K Loc := by
  intro _hloc hclaims d hD hd 𝔠 𝔡 sz hadm κ hκ E hE nf
  obtain ⟨τ₁, hτ₁, hτ⟩ := hclaims d hD hd 𝔠 𝔡 sz hadm
  refine ⟨3 * (nf : ℝ) + 16, min τ₁ (1 / 4), lt_min hτ₁ (by norm_num), ?_⟩
  intro τU hτU hτle
  obtain ⟨hQ, hDg⟩ := hτ τU hτU (le_min_iff.1 hτle).1
  exact ⟨unJak_of_ouClaimsk K hbw hbb d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτU (le_min_iff.1 hτle).2 hQ hDg,
    unUyw_of_ouClaimsk K hbw hbb2 d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτU (le_min_iff.1 hτle).2 hQ hDg⟩

/-- `un_claimAll_of_rowsBAD`: the Claim `(417)` of the block Anderson model from the filtered BA rows, at every `d` with
`Dm d` (the filtered `un_claimAll_of_rowsBA`, `UNPins:142`; `un_claimAll_of_rowskD` at `UNKind.ba`). -/
theorem un_claimAll_of_rowsBAD (Dm : ℕ → Prop) (rC : UNClaimRowBAD Dm) (rE : UNEMCTE2RowBAD Dm)
    (rJ : UNJakUywRowBAD Dm) (rO : UNOURowBAD Dm) (hML : ∀ d : ℕ, Dm d → UNMLOutBA d) (hLoc : UNLocAvgBAD Dm)
    (hQ : UNQueBAD Dm) :
    ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → UNClaimAllC sz (UNModelC.ba sz) E :=
  un_claimAll_of_rowskD Dm (fun d => UNKind.ba d) rC rE rJ rO hML hLoc hQ

/-- `baBUniv_of_rowsD`: `BAEnd_BUnivL d` at every `d` with `Dm d` from `UNCoreC''`, `UNL32`, `UNGUELocal`,
`UNGreenCorrAllC`, `UNDensBARow'`, the two TrLocal inputs at the per-`d` core types of M1 row b
(`unTrLocalBAAt_of_locAvg`, `MATrLocalBA:80`; `unTrLocalInitBAAt'_of_locAvg`, `:237`), `UNNormBARow`, the filtered BA rows and
the filtered consumed inputs (the filtered `baBUniv_of_rows`, `UNPins:367`). -/
theorem baBUniv_of_rowsD (Dm : ℕ → Prop) (hcore : UNCoreC'') (h32 : UNL32) (hGL : UNGUELocal)
    (hGC : UNGreenCorrAllC) (rD : UNDensBARow')
    (rT0 : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalBAAt d)
    (rT : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalInitBAAt' d) (rN : UNNormBARow)
    (rC : UNClaimRowBAD Dm) (rE : UNEMCTE2RowBAD Dm) (rJ : UNJakUywRowBAD Dm) (rO : UNOURowBAD Dm)
    (hML : ∀ d : ℕ, Dm d → UNMLOutBA d) (hLoc : UNLocAvgBAD Dm) (hQ : UNQueBAD Dm) (d : ℕ) (hD : Dm d) :
    BAEnd_BUnivL d := by
  intro hd 𝔠 𝔡 sz hA k hk κ hκ E hE E' hE' O hO
  have hLd : UNLocAvgBAAt d := (unLocAvgBAD_iff_at d).1 (fun d' hdd => hLoc d' (hdd ▸ hD)) hd
  obtain ⟨δ₀, hδ₀, hδ⟩ := rD d hd 𝔠 𝔡 sz hA κ hκ E hE
  obtain ⟨hDens, hbulk⟩ := hδ δ₀ hδ₀ le_rfl
  have hCl := un_claimAll_of_rowsBAD Dm rC rE rJ rO hML hLoc hQ d hD hd 𝔠 𝔡 sz hA κ hκ E hE
  obtain ⟨CV₀, hCV, hN⟩ := rN d hd 𝔠 𝔡 sz hA
  exact hcore h32 hGL hGC d hd 𝔠 𝔡 sz hA (UNModelC.ba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E
    (fun n => BArho d (sz.L n) (sz.lam n) E) δ₀ hDens
    (rT0 d hd hLd 𝔠 𝔡 sz hA κ hκ E hE δ₀ hδ₀ hbulk) (rT d hd hLd 𝔠 𝔡 sz hA κ hκ E hE δ₀ hδ₀ hbulk)
    ⟨CV₀ + 1, by linarith, UNPins_normBound_mono hN (by linarith), unMeanBound_ba sz hA _ (by linarith)⟩ hCl E' hE'
    k hk O hO

/-! ## 3. N2's rows -/

/-- **`unNormBARow_holds`**: the norm row `UNNormBARow` (`UNPins:190`, `(2.3)` of [32]) with `CV₀ = 3`.  `H = λ_n Ψ + V`,
`V` the Gaussian matrix of `sz.withLam 0`.  Every real coordinate of `V` is `N(0, v)` with `v ≤ 1`
(`NormBand_subgaussian`), so a union over the `2 N²` coordinates gives `P(∃ c, |ω_c| ≥ N) ≤ 4 N² e^{-N²/2} ≤ N^{-D}`
eventually (`NormBand_tail_eventually`, from `SizeTendsto` only); on the complement every entry of `V` is `≤ 2 N`
(`NormBand_Xentry_le`) and every entry of `λ_n Ψ` is `≤ 2d 𝔡⁻¹` (`λ_n ≤ 𝔡⁻¹` from `(eq:WO)`, row sum `2d` of `Ψ`,
`UNPins_psiI_rowsum`), so `|λ_i| ≤ N (2 N + 2d 𝔡⁻¹) ≤ N³` once `N ≥ 2 + 2d 𝔡⁻¹` (`NormBand_eig_le`).  Twin of
`unNormBandRow` (`NormBand:173`), which cannot be applied because `sz.withLam 0` is not admissible (`WO 𝔡` fails at `lam = 0`).
No new `∃` constant: `CV₀ = 3` is the row's own. -/
theorem unNormBARow_holds : UNNormBARow := by
  intro d hd 𝔠 𝔡 sz hA
  refine ⟨3, by norm_num, fun D hD => ?_⟩
  obtain ⟨h𝔠, h𝔡, hT, hB, hW⟩ := hA
  filter_upwards [NormBand_tail_eventually D (sz.withLam 0) hT, hT.eventually_ge_atTop (2 + 2 * (d : ℝ) * 𝔡⁻¹), hW] with n hn hN2 hlam
  obtain ⟨hl1, hl2⟩ := hlam
  set N : ℝ := Nsz sz n with hNdef
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) * 𝔡⁻¹ := by positivity
  have hN2' : 2 + 2 * (d : ℝ) * 𝔡⁻¹ ≤ N := hN2
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hl0 : 0 ≤ sz.lam n := le_trans (Real.rpow_nonneg hW0.le _) hl1
  have hcard : (Fintype.card (CoordF d (sz.L n) (sz.W n)) : ℝ) = 2 * N ^ 2 := by
    change (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) : ℝ) = _
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Sizes.card_Idx]; push_cast; ring
  have hsub : {ω : SeqΩ (sz.withLam 0) | ∃ i, N ^ (3 : ℝ) < |(Sizes.seqHBA_isHermitian sz n ω).eigenvalues i|} ⊆
      ⋃ c : CoordF d (sz.L n) (sz.W n), ({ω : SeqΩ (sz.withLam 0) | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ (sz.withLam 0) | N ≤ -ω ⟨n, c⟩}) := by
    rintro ω ⟨i, hi⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or, not_le] at hcon
    have hs : ∀ c, |slice (sz.withLam 0) n ω c| ≤ N := fun c =>
      abs_le.2 ⟨by have h := (hcon c).2; change -N ≤ ω ⟨n, c⟩; linarith, (hcon c).1.le⟩
    have hent : ∀ x y, ‖Sizes.seqHBA sz n ω x y‖ ≤ 2 * N + 𝔡⁻¹ * (2 * (d : ℝ)) := by
      intro x y
      have hΨ : ‖PsiI d (sz.L n) (sz.W n) x y‖ ≤ 2 * (d : ℝ) := by
        rw [← UNPins_psiI_rowsum d (sz.L n) (sz.W n) (sz.three_le_L n) x]
        exact Finset.single_le_sum (f := fun y => ‖PsiI d (sz.L n) (sz.W n) x y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)
      have h1 : ‖(sz.lam n : ℂ) * PsiI d (sz.L n) (sz.W n) x y‖ ≤ 𝔡⁻¹ * (2 * (d : ℝ)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
        exact mul_le_mul hl2 hΨ (norm_nonneg _) (inv_nonneg.2 h𝔡.le)
      have h2 : ‖Xentry d (sz.L n) (sz.W n) (slice (sz.withLam 0) n ω) x y‖ ≤ 2 * N :=
        NormBand_Xentry_le d (sz.L n) (sz.W n) (slice (sz.withLam 0) n ω) hs x y
      change ‖(sz.lam n : ℂ) * PsiI d (sz.L n) (sz.W n) x y + Xentry d (sz.L n) (sz.W n) (slice (sz.withLam 0) n ω) x y‖ ≤ _
      exact (norm_add_le _ _).trans (by linarith)
    have h1 := NormBand_eig_le (Sizes.seqHBA_isHermitian sz n ω) (B := 2 * N + 𝔡⁻¹ * (2 * (d : ℝ))) hent i
    rw [Sizes.card_Idx] at h1
    change |_| ≤ N * (2 * N + 𝔡⁻¹ * (2 * (d : ℝ))) at h1
    have h3 : N ^ (3 : ℝ) = N ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast N 3
    rw [h3] at hi
    have hc : 𝔡⁻¹ * (2 * (d : ℝ)) = 2 * (d : ℝ) * 𝔡⁻¹ := by ring
    rw [hc] at h1
    nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.2 hN2'), mul_nonneg hd0 (sub_nonneg.2 hN1), mul_nonneg hN0.le (mul_nonneg hd0 (sub_nonneg.2 hN1))]
  have hterm : ∀ c : CoordF d (sz.L n) (sz.W n),
      seqP (sz.withLam 0) ({ω : SeqΩ (sz.withLam 0) | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ (sz.withLam 0) | N ≤ -ω ⟨n, c⟩}) ≤
        ENNReal.ofReal (2 * Real.exp (-(N ^ 2 / 2))) := by
    intro c
    have hsg := NormBand_subgaussian (sz.withLam 0) ⟨n, c⟩
    have h1 : (seqP (sz.withLam 0)).real {ω | N ≤ ω ⟨n, c⟩} ≤ Real.exp (-N ^ 2 / (2 * (1 : ℝ≥0))) :=
      hsg.measure_ge_le hN0.le
    have h2 : (seqP (sz.withLam 0)).real {ω | N ≤ -ω ⟨n, c⟩} ≤ Real.exp (-N ^ 2 / (2 * (1 : ℝ≥0))) :=
      hsg.neg.measure_ge_le hN0.le
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 ?_
    have h3 : -N ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -(N ^ 2 / 2) := by simp [neg_div]
    rw [h3] at h1 h2
    exact (measureReal_union_le _ _).trans (by linarith)
  change seqP (sz.withLam 0) {ω : SeqΩ (sz.withLam 0) | ∃ i, N ^ (3 : ℝ) < |(Sizes.seqHBA_isHermitian sz n ω).eigenvalues i|} ≤ _
  calc _ ≤ seqP (sz.withLam 0) (⋃ c : CoordF d (sz.L n) (sz.W n),
        ({ω : SeqΩ (sz.withLam 0) | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ (sz.withLam 0) | N ≤ -ω ⟨n, c⟩})) := measure_mono hsub
    _ ≤ ∑ c : CoordF d (sz.L n) (sz.W n),
        seqP (sz.withLam 0) ({ω : SeqΩ (sz.withLam 0) | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ (sz.withLam 0) | N ≤ -ω ⟨n, c⟩}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c : CoordF d (sz.L n) (sz.W n), ENNReal.ofReal (2 * Real.exp (-(N ^ 2 / 2))) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = ENNReal.ofReal (4 * N ^ 2 * Real.exp (-(N ^ 2 / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
        congr 1; ring
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hn

/-- `unEMCTE2RowBAD_holds`: the filtered weighted `(EMCTE2)` row of the block Anderson kind, at every filter, from the
unfiltered `unEMCTE2RowBA_holds` (`EMCTE2BA:656`; each dimension is read at itself). -/
theorem unEMCTE2RowBAD_holds : ∀ Dm : ℕ → Prop, UNEMCTE2RowBAD Dm :=
  fun _ d _ hd => unEMCTE2RowBA_holds d hd

/-- `unG1RowkBAD_holds`: the two layer pins `UNOULLk`, `UNOUEq747k` of the block Anderson kind at every filter, from the
producers of T2519 (`ba_prodG`, `ba_LLG`, `ba_QueG` at `BAKFam`, `BAPB`, `BA/GUEHyp`) and the merged BA vocabulary of
`RandomLayerBGBA` (`ba_flowG`, `ba_domG`, `RandomLayerBGBA_comp`, `ba_mlout`) through `g1Rowk_of_inputsGD`. -/
theorem unG1RowkBAD_holds : ∀ Dm : ℕ → Prop,
    UNG1RowkD Dm (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, Dm d → UNMLOutBA d)
      (UNLocAvgBAD Dm) (UNQueBAD Dm) :=
  fun Dm => g1Rowk_of_inputsGD Dm _ _ _ _ _ BAEd BAfE BAfT (fun d sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAMO BAKFam BAPB
    (fun d _ _ => ba_flowG d) (fun d _ _ => ba_domG d) (fun d _ _ => RandomLayerBGBA_comp d (baProfComp d))
    (fun d _ hd => ba_prodG d hd) (fun d _ hd => ba_LLG d hd) (fun d _ hd => ba_QueG d hd)
    (fun hML' d hdd hd => ba_mlout d hd (hML' d hdd))

/-- `unOURowBAD_holds`: the filtered `𝐇_t` claims of the centred block Anderson flow, at every filter: `ouRowk_of_pinsD`
with the profile rows `baOUProfRowk_holds` (`BA/GUEKPrim:584`), `unG1RowkBAD_holds` and `g2bRowk` (`QUEFlow:898`). -/
theorem unOURowBAD_holds : ∀ Dm : ℕ → Prop, UNOURowBAD Dm :=
  fun Dm => ouRowk_of_pinsD Dm _ _ (fun d _ hd => baOUProfRowk_holds d hd) (unG1RowkBAD_holds Dm) (g2bRowk _ _)

end RBM.Univ

/-! ## 4. The end -/

namespace RBM.BA

open MeasureTheory Filter Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints RBM.Univ RBM.Univ.GUEPhase

/-- **`baEnd_BUnivL_of_ML`**: `BAEnd_BUnivL d` for every `d ≥ 3` from `UNL32` and `UNMLOutBA d` (the `d > 3` form stays in
hypothesis form).  `baBUniv_of_rowsD (· = d)`: every input is read at the dimension `d` only (`baEnd_locSCL d`,
`unLocAvgBAAt_of_locSCL`, `unQueBAAt_of_ML`, M1's and M3's cores) and the filtered rows are the proved ones. -/
theorem baEnd_BUnivL_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAEnd_BUnivL d :=
  baBUniv_of_rowsD (· = d) unCoreC''_holds h32 (un_gueLocal_of_tail gueSchurTail) greenCorrAllC unDensBARow'_holds
    unTrLocalBAAt_of_locAvg unTrLocalInitBAAt'_of_locAvg unNormBARow_holds (unClaimRowkD _ _)
    (unEMCTE2RowBAD_holds _) (jakUywRowkD _ _ UNBulkWindowk_ba UNBadBoundk_ba UNBad2Boundk_ba _)
    (unOURowBAD_holds _) (fun d' h => h ▸ hML)
    ((unLocAvgBAD_iff_at d).2 fun hd => unLocAvgBAAt_of_locSCL d hd (baEnd_locSCL d hML))
    ((unQueBAD_iff_at d).2 fun hd => unQueBAAt_of_ML d hd hML) d rfl

/-- **`baThm27L_of_ML`**: `BAThm27L d` for every `d ≥ 3` from `UNL32` and `UNMLOutBA d`: the five conjuncts. -/
theorem baThm27L_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAThm27L d :=
  ⟨baEnd_decolL d hML, baEnd_locSCL d hML, baEnd_QUEL d hML, baEnd_BUnivL_of_ML d hd h32 hML, baEnd_QDiffL d hML⟩

/-- **`baThm27L_three`** (D6, closing condition (vi)): the block Anderson Theorem 2.7 pins at `d = 3` (D723): the input of
MA-06b.  The only hypothesis is `UNL32`. -/
theorem baThm27L_three : UNL32 → BAThm27L 3 :=
  fun h32 => baThm27L_of_ML 3 le_rfl h32 unMLOutBA_three

/-- **`baThm27L_any`** (closing condition (iii), D723): `BAThm27L d` for every `d ≥ 3` under Step 5 (iii), `STStep5IIIgL d`,
through `baMainIndFamTL_any` (`MainIndTermBA:53`) and `unMLOutBA_of_famStep` (`MainIndOutBA:326`). -/
theorem baThm27L_any (d : ℕ) (hd : 3 ≤ d)
    (h5 : STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (h32 : UNL32) : BAThm27L d :=
  baThm27L_of_ML d hd h32 (unMLOutBA_of_famStep d (baMainIndFamTL_any d h5))

end RBM.BA

/-! ## 5. Compiled nonempty instances (`d = 3`, `S0`: `(L, g) = (4, 3/10)`, `(𝔠, 𝔡) = (1/6, 1/10)`)

Data of the merged instances `UNPins:1027-1066`: `S0` (`UNPins:884`), `κ_* = clsκ 4`, `E_* = (fp 4 _).E` in the ρ-bulk,
`k = 1` (`n_f = 1, 2` for the claim rows), `E' = 0`, `𝒪 = bump`.  Every deterministic hypothesis and every producer
is discharged by a merged or C5 name; the one hypothesis left is the borrowed `UNL32` (`inst_univ_baD`, the two end
theorems). -/
