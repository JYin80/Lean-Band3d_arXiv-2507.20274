/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.RandomLayerBG
import RBM3D.Universality.UnivMain
import RBM3D.Universality.PinsKD

/-!
# T2520 (G2): the dimension-filtered generic chain

MN-D3 D2 (`docs/reports/T2513-design.md` §3; DECISIONS §316, §340, §353).  The merged generic chain
from the layer inputs to the Claim `(417)`, with the dimension filter `Dm` of `Universality/PinsKD`
threaded through: every input is applied at its own dimension `d` with `Dm d` (MNO-C2).

* `un_claimAll_of_rowskD`: `un_claimAll_of_rowsk` (`PinsK:454`);
* `unClaimRowkD`: `unClaimRowk` (`UnivMain:471`);
* `ouRowk_of_pinsD`: `ouRowk_of_pins` (`OUInterfaceK:292`);
* `g1Rowk_of_inputsGD`: `g1Rowk_of_inputsG` (`RandomLayerBG:399`); its two private size lemmas
  `RandomLayerBG_oull_seq` (`:265`), `RandomLayerBG_eq747_seq` (`:313`) are read by `open private`.

Statements and proofs equal the merged ones after the filter map (script diff in the report).  No
block Anderson and no band vocabulary in the statements.  `jakUywRowkD` imports `BA/EMCTE2BA` and
lives in `BA/UNBUniv`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private RandomLayerBG_oull_seq RandomLayerBG_eq747_seq from RBM3D.Universality.GUEPhase.RandomLayerBG

noncomputable section

namespace RBM.Univ

open MeasureTheory Filter Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Loop RBM.Univ.GUEPhase

/-! ## 1. The chain -/

/-- `un_claimAll_of_rowskD`: the Claim `(417)` from the filtered rows, at every `d` with `Dm d`
(`un_claimAll_of_rowsk`, `PinsK:454`). -/
theorem un_claimAll_of_rowskD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) {ML Loc Que : Prop}
    (rC : UNClaimRowkD Dm K) (rE : UNEMCTE2RowkD Dm K) (rJ : UNJakUywRowkD Dm K Loc)
    (rO : UNOURowkD Dm K ML Loc Que) (hML : ML) (hLoc : Loc) (hQ : Que) :
    ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E := by
  have hOU := rO hML hLoc hQ
  apply rC
  intro d hD hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨Cn, τ₁, hτ₁, h1⟩ := rE d hD hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨C, τ₂, hτ₂, h2⟩ := rJ hLoc hOU d hD hd 𝔠 𝔡 sz hA κ hκ E hE nf
  refine ⟨Cn, C, min τ₁ τ₂, lt_min hτ₁ hτ₂, fun τU h0 hle => ?_⟩
  have hJU := h2 τU h0 (hle.trans (min_le_right _ _))
  exact ⟨h1 τU h0 (hle.trans (min_le_left _ _)), hJU.1, hJU.2⟩

/-- `unClaimRowkD`: `UNClaimRowkD` for every filter and kind (`unClaimRowk`, `UnivMain:471`). -/
theorem unClaimRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : UNClaimRowkD Dm K := by
  intro h d hD hd 𝔠 𝔡 sz hA κ hκ E hE
  refine ⟨𝔠 * 𝔡 / 30, by have := hA.1; have := hA.2.1; positivity, fun nf => ?_⟩
  obtain ⟨Cn, C, τ₀, hτ₀, hh⟩ := h d hD hd 𝔠 𝔡 sz hA κ hκ E hE nf
  refine ⟨Cn + C + 1, τ₀, hτ₀, fun τU hτU hτU0 => ?_⟩
  obtain ⟨hEM, hJ, hU⟩ := hh τU hτU hτU0
  exact unClaim417C_of_rows (K d) sz hA.2.2.1 E nf τU _ Cn C hτU hEM hJ hU

/-- `ouRowk_of_pinsD`: `UNOURowkD` from the filtered layer row `UNG1RowkD`, the row `UNG2bRowk` and the
profile rows at the filtered dimensions (`ouRowk_of_pins`, `OUInterfaceK:292`). -/
theorem ouRowk_of_pinsD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d))
    {ML Loc Que : Prop} (hprof : ∀ d : ℕ, Dm d → 3 ≤ d → UNOUProfRowk (K d) (P d)) :
    UNG1RowkD Dm K P ML Loc Que → UNG2bRowk K P → UNOURowkD Dm K ML Loc Que := by
  intro r1 r2b hML hLoc hQ d hD hd 𝔠 𝔡 sz hA
  refine ⟨ouTauMax 𝔠 𝔡, ouTauMax_pos hA.1 hA.2.1, fun τU hτ hle => ?_⟩
  have h1 := r1 hML hLoc hQ d hD hd 𝔠 𝔡 sz hA τU hτ hle
  exact ⟨r2b d hd (hprof d hD hd) 𝔠 𝔡 sz hA τU hτ h1.2, ouDiagk_of_ouLLk h1.1⟩

/-- `g1Rowk_of_inputsGD`: `UNG1RowkD` from the seven layer inputs, each read at its own dimension `d` with `Dm d`
(`g1Rowk_of_inputsG`, `RandomLayerBG:399`). -/
theorem g1Rowk_of_inputsGD (Dm : ℕ → Prop) :
    ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop)
      (Ed : ∀ d : ℕ, ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : ∀ d : ℕ, Sizes d → ℕ → ℂ → ℝ)
      (Fl : ∀ d : ℕ, Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
      (MO : ∀ d : ℕ, Sizes d → (ℕ → ℂ) → (ℕ → ℝ) → Prop)
      (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
        (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
      (∀ d, Dm d → 3 ≤ d → RBG_Flow (K d) (Ed d) (fT d)) →
      (∀ d, Dm d → 3 ≤ d → RBG_Dom (K d) (Fl d)) →
      (∀ d, Dm d → 3 ≤ d → RBG_Comp (K d) (P d)) →
      (∀ d, Dm d → 3 ≤ d → RBG_Prod (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
      (∀ d, Dm d → 3 ≤ d → RandomLayerB_LL (K d) (fE d) (fT d) (PB d)) →
      (∀ d, Dm d → 3 ≤ d → RBG_Que (K d) (P d) (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
      (ML → ∀ d, Dm d → 3 ≤ d → RandomLayerB_MLout (fT d) (Fl d) (MO d)) →
      UNG1RowkD Dm K P ML Loc Que := by
  intro K P ML Loc Que Ed fE fT Fl MO KF PB hT1 hT1' hC hT2 hT3 hT4 hT5 hML _ _ d hD hd 𝔠 𝔡 sz hA τU hτU hτUm
  refine ⟨fun κ hκ E t ht δ hδ p => ?_, fun κ hκ E t ht τ hτ => ?_⟩
  · refine RandomLayerBG_pad_subseq (fun n => (K d).bulk sz κ (E n) n)
      (fun n => RandomLayerB_LLAt (K d) sz τU n (E n) (t n) δ p) fun φ hφ hS => ?_
    exact (RandomLayerBG_oull_seq hd (hT1 d hD hd) (hT1' d hD hd) (hT2 d hD hd) (hT3 d hD hd) (hT5 hML d hD hd)
      (comp_admissible sz φ 𝔠 𝔡 hφ.tendsto_atTop hA) hτU hτUm hκ
      (fun j => (hC d hD hd sz φ hφ j).1 κ _ (hS j)) (fun j => ht (φ j)) δ hδ p).mono
      fun j hj => (hC d hD hd sz φ hφ j).2.1 τU _ _ δ p hj
  · refine RandomLayerBG_pad_subseq (fun n => (K d).bulk sz κ (E n) n)
      (fun n => RandomLayerB_QueAt (K d) (P d) sz 𝔡 n (E n) (t n) τ) fun φ hφ hS => ?_
    exact (RandomLayerBG_eq747_seq hd (hT1 d hD hd) (hT1' d hD hd) (hT2 d hD hd) (hT4 d hD hd) (hT5 hML d hD hd)
      (comp_admissible sz φ 𝔠 𝔡 hφ.tendsto_atTop hA) hτU hτUm hκ
      (fun j => (hC d hD hd sz φ hφ j).1 κ _ (hS j)) (fun j => ht (φ j)) τ hτ).mono
      fun j hj => (hC d hD hd sz φ hφ j).2.2 𝔡 _ _ τ hj

/-! ## 2. Compiled nonempty instances (band kind, `d = 3`, `sz0`; pins of other gates stay hypotheses)

The data of the merged instances (`UnivMainInst`, `RandomLayerBGInst`): `sz0` (`L = 4 (n + 1)`, `W = (2 (n + 1))^5`,
`lam = (2 (n + 1))^{-6}`, admissible at `(𝔠, 𝔡) = (1/6, 1/10)`), `κ = 1/2`, `E = 0`, `τ_U = ouTauMax (1/6) (1/10)`.
The filters are `fun _ => True` (the band rows are proved for every dimension) and `(· = 3)`. -/

namespace RandomLayerBGDInst

open RBM.Gauss.SizesInst

/-- `unClaimRowkD` at the band kind and the filter `(· = 3)`: the claim `(417)` at `sz0`, `κ = 1/2`, `E = 0` from the merged
band rows `unEMCTE2Rowk_band`, `jakUywRow` (only `UNLocAvgBand`, `UNOUClaims` stay hypotheses). -/
theorem inst_unClaimRowkD_band_zero :
    UNLocAvgBand → UNOUClaims → UNClaimAllC sz0 ((UNKind.band 3).M sz0) 0 := by
  intro hLoc hOU
  refine unClaimRowkD (· = 3) (fun d => UNKind.band d) ?_ 3 rfl le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm (1 / 2)
    (by norm_num) 0 (Filter.Eventually.of_forall fun n => by
      change |(0 : ℝ)| ≤ 2 - 1 / 2
      norm_num)
  intro d _ hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨Cn, τ₁, hτ₁, h1⟩ := unEMCTE2Rowk_band d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨C, τ₂, hτ₂, h2⟩ := (UNJakUywRowk_band.2 jakUywRow) hLoc (UNOUClaimsk_band.2 hOU) d hd 𝔠 𝔡 sz
    hA κ hκ E hE nf
  refine ⟨Cn, C, min τ₁ τ₂, lt_min hτ₁ hτ₂, fun τU h0 hle => ?_⟩
  have hJU := h2 τU h0 (hle.trans (min_le_right _ _))
  exact ⟨h1 τU h0 (hle.trans (min_le_left _ _)), hJU.1, hJU.2⟩

/-- `un_claimAll_of_rowskD` at the band kind and the filter `fun _ => True`, `d = 3`, `sz0`, `κ = 1/2`, `E = 0`: the claim
rows `UNClaimRowkD` (`unClaimRowkD`), `UNEMCTE2RowkD` (`unEMCTE2Rowk_band`), `UNJakUywRowkD` (`jakUywRow`) are discharged; the
row `UNOURowkD` and the consumed `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (pins of other gates) stay hypotheses. -/
theorem inst_un_claimAll_of_rowskD
    (rO : UNOURowkD (fun _ => True) (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNClaimAllC sz0 ((UNKind.band 3).M sz0) 0 :=
  un_claimAll_of_rowskD (fun _ => True) (fun d => UNKind.band d) (unClaimRowkD _ _)
    ((UNEMCTE2RowkD_true _).2 unEMCTE2Rowk_band) ((UNJakUywRowkD_true _ _).2 (UNJakUywRowk_band.2 jakUywRow))
    rO hML hLoc hQ 3 trivial le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 0
    (Filter.Eventually.of_forall fun n => by
      change |(0 : ℝ)| ≤ 2 - 1 / 2
      norm_num)

/-- `ouRowk_of_pinsD` at the band kind and the filter `(· = 3)`, applied at `sz0`: the profile rows are discharged
(`unOUProfRowk_band`); the layer row `UNG1RowkD` and `UNG2bRowk` (pins of other gates) stay hypotheses. -/
theorem inst_ouRowk_of_pinsD
    (r1 : UNG1RowkD (· = 3) (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d : ℕ, UNMLOut d)
      UNLocAvgBand UNQueBand)
    (r2 : UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d))
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNOUQUEk (UNKind.band 3) sz0 (1 / 10) τU ∧ UNOUDiagk (UNKind.band 3) sz0 τU :=
  ouRowk_of_pinsD (· = 3) (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
    (fun _ _ hd => unOUProfRowk_band hd) r1 r2 hML hLoc hQ 3 rfl le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm

/-- `g1Rowk_of_inputsGD` at the band kind and the filter `(· = 3)`, `d = 3`, `sz0`, `τ_U = ouTauMax (1/6) (1/10)`: every
deterministic premise is discharged by the merged `RandomLayerB_*_band` lemmas (twin of `inst_g1Rowk_of_inputsG`);
`UNMLOut`, `UNLocAvgBand`, `UNQueBand` stay hypotheses. -/
theorem inst_g1Rowk_of_inputsGD (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULLk (UNKind.band 3) sz0 (ouTauMax (1 / 6) (1 / 10)) ∧
      UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (ouTauMax (1 / 6) (1 / 10)) :=
  g1Rowk_of_inputsGD (· = 3) (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand
    UNQueBand (fun _ => RandomLayerBG_bandEd) (fun _ _ _ z => lemE z) (fun _ _ _ z => lemT z)
    (fun d => RandomLayerB_Flband (d := d)) (fun d => RandomLayerB_MOband (d := d))
    (fun d => RandomLayerB_KFam (d := d)) (fun d => RandomLayerB_PBband (d := d))
    (fun _ _ _ => RandomLayerBG_flowG_of_band_id RandomLayerB_flow_band) (fun _ _ _ => RandomLayerBG_dom_band)
    (fun _ _ _ => RandomLayerBG_comp_band) (fun _ _ hd => RandomLayerBG_prod_band hd)
    (fun _ _ _ => RandomLayerB_LL_band) (fun _ _ hd => RandomLayerBG_Que_band hd)
    (fun hML' _ _ hd => RandomLayerB_ML_band hML' hd) hML hLoc hQ 3 rfl le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible _
    (ouTauMax_pos (by norm_num) (by norm_num)) le_rfl

end RandomLayerBGDInst

end RBM.Univ

end
