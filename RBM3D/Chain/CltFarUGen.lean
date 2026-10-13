/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.IniTermIIGen
import RBM3D.Chain.Step34Gen
import RBM3D.Evolution.CltFarG
import RBM3D.Induction.IniTermI

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The `u`-uniform `lem;CLT` of Step 5, case (i), over the carrier (T2484, U4s2b)

Additive generic form of the section 13-15 layer of `Induction/IniTermI.lean` (not edited) over a carrier tuple
`(law, Flow, mk, T0)` of `Chain/Step5Gen.lean`, on the one propagator `STThg` (U-C4: no kernel and no propagator is defined here).
Paper: arXiv:2507.20274, `lem;CLT` is `3_5:2173-2176`; its use in `(iksjuwjx0)` is for every `u ∈ [s,t]` (paper-delta `T2329b`).

* **Target 5.**  The class `IniTermGen_CltFlow d law Flow mk T0` (D2): the `t`-free fields of X1's premise block `HCltOf` plus
  `STThPropsg`, `STExpInvgL`, and, per start time `s` under `STReg5I`, `STMfarg`, `STGijDecgL`, `STKfargL`, `STKpropsg`; its band
  result `iniTermGen_cltFlow_band` (the construction of `stCltFar_of_gL`, `Evolution/CltFarG.lean:926-950`).  With the flow facts
  and the Step-2 premises restricted to `[s, t']` it gives `HCltOf` at every `t' ∈ (s, t]`, hence X1's far pin `stCltFargL_holds`
  at `t'` (`CltFarUGen_cltFar_of`).
* **Target 6.**  The conclusion `STCltFarUConclgL`, its band bridge `bandFM_STCltFarUConcl`, and the restriction
  `stIngR5gL_hyps_restrict` of the hypotheses of a case-(i) pin from `[s, t]` to `[s, t']`.
* **Target 7.**  `stCltFarUgL_of`: the `u`-uniform `lem;CLT`, from `stCltFargL_holds` at the worst grid time, the Lipschitz bound of
  `f^{far}` in the propagator time (the resolvent identity of `Step2Gen_Theta` from the semigroup law, row sums of the kernel facts)
  and the union over the grid; band re-derivation `iniTermGen_cltFarU_band` of `stCltFar_uniform`.
* **Shared with `Chain/IniTermIGen`.**  The one-index algebra of `f^{far}` over an abstract propagator
  (`CltFarUGen_fSum`, the Lipschitz bound `CltFarUGen_fSum_lip`) and the bounds `CltFarUGen_Th_entry`, `CltFarUGen_Th_lip`.

Coupling (UBA-C1): the kernel facts are read at `gK`, every size-level quantity at `sz.lam`; the one comparison R1 enters in
`CltFarUGen_guard` only (the per-index guard `0 < lam → 0 < gK ≤ lam`).

Ported from `Induction/IniTermI.lean` of this project (last commit of the file `850a8a3b`): §13 `stIngR5_hyps_restrict` (`:1577`), §14
`iniTermI_fSum_lip` (`:1662`), `iniTermI_Theta_lip` (`:1628`), §15 `iniTermI_unif_det` (`:1939`), `stCltFar_uniform` (`:2005`) for
the carrier.  The d = 1 and d = 2 projects are not used.
-/

open private Step5KerGen_cmp_pos from RBM3D.Chain.Step5KerGen

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-! ## 1. Target 5: the class `IniTermGen_CltFlow` -/

/-- **Target 5, class `IniTermGen_CltFlow d law Flow mk T0`** (`T2484_CltFlow`; D2, the flow-tuple wrapper of X1's far pin): for
`3 ≤ d` and `κ, ε, 𝔡 > 0` there are `κ' ∈ (0, 1]` and `δ > 0` such that along every flow the carrier has the `t`-free fields of
`HCltOf` (`κ' ≤ Im m`, `N^{-1+δ} ≤ 1 - T0`, `CltRepg`, `Σ_y |M_xy|² ≤ 1`), `STThPropsg`, `STExpInvgL`, and, for every start time
`s` and end time `t ≤ T0` under `STReg5I`, `STMfarg`, `STGijDecgL`, `STKfargL`, `STKpropsg` (which depend on `s` only).  Band
`iniTermGen_cltFlow_band` with `κ' = cltCk (κ/2)`, `δ = ε/2`; BA: U4-BA (C9). -/
def IniTermGen_CltFlow (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ κ' δ : ℝ, 0 < κ' ∧ κ' ≤ 1 ∧ 0 < δ ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        (∀ n, κ' ≤ ((mk sz z).m n).im) ∧
        (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T0 sz z n) ∧
        CltRepg (mk sz z) (law sz) H₀ g' E ∧
        (∀ n x, ∑ y, ‖(mk sz z).M n x y‖ ^ 2 ≤ 1) ∧
        STThPropsg (mk sz z) ∧ STExpInvgL (mk sz z) (law sz) ∧
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) → STReg5I sz s t →
          STMfarg (mk sz z) s ∧ STGijDecgL (mk sz z) (law sz) s ∧ STKfargL (mk sz z) s ∧ STKpropsg (mk sz z) s

private theorem CltFarUGen_ck_pos {κ : ℝ} (h0 : 0 < κ) (h2 : κ ≤ 2) : 0 < cltCk κ := by
  unfold cltCk
  exact div_pos (Real.sqrt_pos.2 (mul_pos h0 (by linarith))) two_pos

/-- **Target 5 at the band** (`T2484_CltFlow` for `(seqP, STFlow, bandFM ∘ STflowE, lemT)`): the construction inside
`stCltFar_of_gL` (`Evolution/CltFarG.lean:926-950`) with `κ' = cltCk (κ/2)` (`min (κ/2) 2` to keep `cltCk` positive for every
`κ > 0`), `δ = ε/2`, `H₀ = 0`, `g' = sz.lam`, `E = STflowE z`. -/
theorem iniTermGen_cltFlow_band (d : ℕ) : IniTermGen_CltFlow d (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  have hκ' : 0 < min (κ / 2) 2 := lt_min (half_pos hκ) two_pos
  have hck : 0 < cltCk (min (κ / 2) 2) := CltFarUGen_ck_pos hκ' (min_le_right _ _)
  refine ⟨cltCk (min (κ / 2) 2), ε / 2, hck, ?_, half_pos hε, ?_⟩
  · unfold cltCk
    refine (div_le_one two_pos).2 (Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩)
    nlinarith [sq_nonneg (min (κ / 2) 2 - 2)]
  intro 𝔠 sz z hflow
  obtain ⟨hadm, hE, ht1, hRC⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow (t := fun n => lemT (z n)) (fun _ => le_rfl)
  have hEm : ∀ n, |STflowE z n| ≤ 2 - min (κ / 2) 2 := fun n => by linarith [min_le_left (κ / 2) 2, hE n]
  have hWt : Filter.Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono' _ hadm.2.2.2.1 ((tendsto_rpow_atTop hadm.1).comp hadm.2.2.1)
  refine ⟨fun _ => 0, sz.lam, STflowE z, fun n => (cltCk_facts hκ' (hEm n)).2.1, hRC, cltRepg_band sz _,
    fun n x => bandFM_M_le sz _ (fun n => (hE n).le.trans (by linarith)) n x,
    bandFM_STThPropsg sz (κ / 2) 𝔡 (STflowE z) hd (half_pos hκ) h𝔡 hadm.2.2.2.2 (fun n => (hE n).le),
    stExpInvgL_band sz _, ?_⟩
  intro s t hs0 hst htl hreg
  have hcl : ∀ n, s n ≤ lemT (z n) := fun n => (hst n).le.trans (htl n)
  obtain ⟨-, -, ht1', -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htl
  exact ⟨bandFM_STMfarg sz _ ((Real.tendsto_log_atTop.comp hWt).eventually_gt_atTop 0) _,
    bandFM_STGijDecgL_of_three_le hd hκ hε h𝔡 hflow hs0 hcl,
    bandFM_STKfargL hd hκ hε hflow hs0 hcl,
    bandFM_STKpropsg sz (κ / 2) 𝔡 (STflowE z) s t hd (half_pos hκ) h𝔡 hadm.2.2.2.2 (fun n => (hE n).le) hs0
      (fun n => (hst n).le) ht1' hreg⟩

/-- **D2: the class feeds X1's far pin at every grid time `t' ∈ (s, t]`** (closure under `t ↦ t'`): `HCltOf` at `t'` is assembled
from the `t`-free fields of the class (applied at `(s, t')`), the flow facts (admissibility, `T0 < 1`) and the Step-2 premises
restricted to `[s, t']`; `stCltFargL_holds` then gives the far pin at `t'`. -/
theorem CltFarUGen_cltFar_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hF : IniTermGen_CltFlow d law Flow mk T0) (hd : 3 ≤ d) (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ (Cd : ℝ) (s t' : ℕ → ℝ),
      (∀ n, 0 ≤ s n) → (∀ n, s n < t' n) → (∀ n, t' n ≤ T0 sz z n) → STReg5I sz s t' →
      STLocalEntryUgL (mk sz z) (law sz) s t' → STGdecayWgL (mk sz z) (law sz) s t' Cd →
      STCltFarConclgL (mk sz z) (law sz) s t' := by
  obtain ⟨κ', δ, hκ', hκ1, hδ, H⟩ := hF hd κ ε 𝔡 hκ hε h𝔡
  intro 𝔠 sz z hflow Cd s t' hs0 hst htT hreg hLE hGD
  obtain ⟨κm, -, hf⟩ := hFF κ hκ
  obtain ⟨hadm, hT1, -, -⟩ := hf sz ε 𝔠 𝔡 z hflow
  obtain ⟨H₀, g', E, hm, hev, hrep, hM, hTh, hX, hst'⟩ := H 𝔠 sz z hflow
  obtain ⟨hMf, hGij, hKf, hKp⟩ := hst' s t' hs0 hst htT hreg
  refine stCltFargL_holds d κ' δ 𝔠 𝔡 Cd sz (mk sz z) (law sz) g' E H₀ s t'
    ⟨hd, hκ', hκ1, hδ, hadm, hm, hs0, hst, fun n => (htT n).trans_lt (hT1 n),
      hev.mono fun n hn => hn.trans (by linarith [htT n]), hrep, hM, hMf, hLE, hGD, hGij, hKf⟩ hreg hTh hKp hX

/-! ## 2. Target 6: the conclusion, its band bridge and the restriction of the hypotheses -/

/-- **Target 6, `STCltFarUConclgL`** (`T2484_CltFarUConclgL`): `lem;CLT` uniformly in the propagator time `u ∈ [s,t]` over a carrier,
on the index set of `STCltFarConcl` with `ℓ_u` in place of `ℓ_t` (band `STCltFarUConcl`, `IniTermI:1786`; paper-delta `T2329b`). -/
def STCltFarUConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Σ u : TimeIcc s t n, sz.STCltFarIdx s n (u : ℝ))
    (fun n q ω => ‖STfFarg C n (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
    (fun n q _ => sz.STCltFarZeta n q.2.1.2)

/-- **Target 6, band bridge** (`T2484_BandCltFarU`): the band `STCltFarUConcl` is `STCltFarUConclgL` at `(bandFM sz E, seqP sz)`,
through `bandFM_STfFarg`. -/
theorem bandFM_STCltFarUConcl : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
    sz.STCltFarUConcl E s t ↔ STCltFarUConclgL (bandFM sz E) (Sizes.seqP sz) s t := by
  intro d sz E s t
  unfold STCltFarUConclgL STCltFarUConcl Prec PrecL
  simp only [bandFM_STfFarg]

private theorem CltFarUGen_prec_restrict {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U V : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {ξ' ζ' : ∀ n, V n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ) (φ : ∀ n, V n → U n) (hξ : ∀ n v ω, ξ' n v ω = ξ n (φ n v) ω)
    (hζ : ∀ n v ω, ζ' n v ω = ζ n (φ n v) ω) : PrecL sz μ ξ' ζ' := by
  have h' := StochDomAt.precomp_param h φ
  have e1 : ξ' = fun n v ω => ξ n (φ n v) ω := by funext n v ω; exact hξ n v ω
  have e2 : ζ' = fun n v ω => ζ n (φ n v) ω := by funext n v ω; exact hζ n v ω
  rw [e1, e2]; exact h'

/-- **Target 6, `stIngR5gL_hyps_restrict`** (band `stIngR5_hyps_restrict`, `IniTermI:1577`; the shape of `T2484-check.lean`): the
hypotheses of a case-(i) pin over a carrier restrict from `[s,t]` to `[s,t']`, `s < t' ≤ t`: the regime `STReg5I`, `(con_st_ind)`
(`Bctl(t')^{𝔠_d} ≤ Bctl(t)^{𝔠_d} ≤ (1-t)/(1-s) ≤ (1-t')/(1-s) < 1`, `STBctl_mono`), and the Step 1-4 premises over `u ∈ [s,t]`
(each has the index `u ∈ [s,t]` and the time `s`, never `t`: `StochDomAt.precomp_param` along `[s,t'] ⊂ [s,t]`).  Public for U4s3. -/
theorem stIngR5gL_hyps_restrict {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t t' : ℕ → ℝ) (𝔠d Cd : ℝ)
    (h𝔠d : 0 < 𝔠d) (hst' : ∀ n, s n < t' n) (ht' : ∀ n, t' n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hR : STReg5I sz s t) (hCon : sz.STConStInd 𝔠d s t) (hS1 : STStep1LoopgL C μ s t) (hS2 : STStep2ConclgL C μ s t Cd)
    (hLmax : STLmaxUgL C μ s t) (hLKU : STLKUgL C μ s t) :
    STReg5I sz s t' ∧ sz.STConStInd 𝔠d s t' ∧ STStep1LoopgL C μ s t' ∧ STStep2ConclgL C μ s t' Cd ∧
      STLmaxUgL C μ s t' ∧ STLKUgL C μ s t' := by
  refine ⟨fun n => ⟨(hR n).1.trans (by linarith [ht' n]), (hR n).2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hCon] with n hn
    obtain ⟨h1, h2⟩ := hn
    have hs0 : 0 < 1 - s n := by linarith [hst' n, ht1 n, ht' n]
    have hB : sz.Bctl n (t' n) ≤ sz.Bctl n (t n) := STBctl_mono sz n (ht' n) (ht1 n)
    have hB0 : 0 ≤ sz.Bctl n (t' n) := (st_Bctl_pos sz (lt_of_le_of_lt (ht' n) (ht1 n))).le
    refine ⟨((Real.rpow_le_rpow hB0 hB h𝔠d.le).trans h1).trans ?_, ?_⟩
    · exact div_le_div_of_nonneg_right (by linarith [ht' n]) hs0.le
    · rw [div_lt_one hs0]; linarith [hst' n]
  · intro k hk
    exact CltFarUGen_prec_restrict sz μ (hS1 k hk) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  · obtain ⟨h1, h2, h3⟩ := hS2
    exact ⟨CltFarUGen_prec_restrict sz μ h1 (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl),
      CltFarUGen_prec_restrict sz μ h2 (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl),
      fun D hD => CltFarUGen_prec_restrict sz μ (h3 D hD) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl)
        (fun _ _ _ => rfl)⟩
  · intro k hk
    exact CltFarUGen_prec_restrict sz μ (hLmax k hk) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro k hk
    exact CltFarUGen_prec_restrict sz μ (hLKU k hk) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-! ## 3. The propagator in the propagator time: entry bound, resolvent identity, Lipschitz bound -/

section ThBounds

variable {d : ℕ} {sz : Sizes d}

/-- **The resolvent identity** from the semigroup law at `(0, v, w)`: `Θ_w - Θ_v = (w - v) θ_w Θ_v`, `θ_w = X Θ_w`
(`uKer_{v,w} uKer_{0,v} = uKer_{0,w}`, `uKer_{0,t} = Θ_t`, and `Θ_w = 1 + w θ_w`). -/
theorem CltFarUGen_Theta_sub (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n) (p q : Bool) {v w : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    STThg C n p q w - STThg C n p q v =
      ((w - v : ℝ) : ℂ) • (Step2Gen_thetaKer C n p q w * STThg C n p q v) := by
  have h2 := (hU p q 0 v w hv0 hv1 hw0 hw1).2
  have hw := IniTermIIGen_Theta_eq C n hU p q hw0 hw1
  unfold Step2Gen_uKer at h2
  simp only [Complex.ofReal_zero, zero_smul, sub_zero, one_mul] at h2
  have e1 : (1 - (v : ℂ) • (Step2Kern_Mss C n p q * C.S n)) * Step2Gen_Theta (Step2Kern_Mss C n p q * C.S n) (w : ℂ) =
      1 + ((w - v : ℝ) : ℂ) • Step2Gen_thetaKer C n p q w := by
    have hw' : Step2Gen_Theta (Step2Kern_Mss C n p q * C.S n) (w : ℂ) = 1 + (w : ℂ) • Step2Gen_thetaKer C n p q w := hw
    have hth : Step2Gen_thetaKer C n p q w =
        (Step2Kern_Mss C n p q * C.S n) * Step2Gen_Theta (Step2Kern_Mss C n p q * C.S n) (w : ℂ) := rfl
    rw [sub_mul, one_mul, smul_mul_assoc, ← hth]
    nth_rewrite 1 [hw']
    push_cast
    module
  rw [e1] at h2
  have hΘv : STThg C n p q v = Step2Gen_Theta (Step2Kern_Mss C n p q * C.S n) (v : ℂ) := rfl
  have hΘw : STThg C n p q w = Step2Gen_Theta (Step2Kern_Mss C n p q * C.S n) (w : ℂ) := rfl
  rw [hΘv, hΘw]
  rw [add_mul, one_mul, smul_mul_assoc] at h2
  rw [← h2]
  abel

/-- Entrywise bound `|Θ_t(a,b)| ≤ (1 + C₆)/(1 - t)`: the row sums of `Θ = 1 + tθ` (`IniTermIIGen_row_le`). -/
theorem CltFarUGen_Th_entry (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n) (p q : Bool) {t C₆ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hrow : ∀ a, ∑ b, ‖Step2Gen_thetaKer C n p q t a b‖ ≤ C₆ / (1 - t))
    (a b : Zd d (sz.L n)) : ‖STThg C n p q t a b‖ ≤ (1 + C₆) * (1 - t)⁻¹ :=
  (Finset.single_le_sum (f := fun b => ‖STThg C n p q t a b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)).trans
    (IniTermIIGen_row_le C n hU p q ht0 ht1 a (hrow a))

/-- **Lipschitz bound in the propagator time** (band `iniTermI_Theta_lip`, `IniTermI:1628`, with the resolvent identity of
`CltFarUGen_Theta_sub` in place of `Theta_sub_Theta`): for `v, w ≤ t < 1`,
`|Θ_v(a,b) - Θ_w(a,b)| ≤ |v - w| C₆ (1 + C₆) (1 - t)⁻²` (row sums of `θ` by `hrow`, entries of `Θ` by `CltFarUGen_Th_entry`). -/
theorem CltFarUGen_Th_lip (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n) (p q : Bool) {v w t C₆ : ℝ}
    (hv0 : 0 ≤ v) (hvt : v ≤ t) (hw0 : 0 ≤ w) (hwt : w ≤ t) (ht1 : t < 1) (hC₆ : 0 ≤ C₆)
    (hrow : ∀ τ : ℝ, 0 ≤ τ → τ < 1 → ∀ a, ∑ b, ‖Step2Gen_thetaKer C n p q τ a b‖ ≤ C₆ / (1 - τ))
    (a b : Zd d (sz.L n)) :
    ‖STThg C n p q v a b - STThg C n p q w a b‖ ≤ |v - w| * (C₆ * (1 + C₆) * ((1 - t)⁻¹) ^ 2) := by
  have ht0 : 0 < 1 - t := by linarith
  have hv1 : v < 1 := by linarith
  have hw1 : w < 1 := by linarith
  have hid := CltFarUGen_Theta_sub C n hU p q hw0 hw1 hv0 hv1
  have hentry : STThg C n p q v a b - STThg C n p q w a b =
      ((v - w : ℝ) : ℂ) * (Step2Gen_thetaKer C n p q v * STThg C n p q w) a b := by
    have := congrFun (congrFun hid a) b
    simpa [Matrix.sub_apply, Matrix.smul_apply] using this
  rw [hentry, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [Matrix.mul_apply]
  have e1 : (1 - t)⁻¹ ≥ (1 - v)⁻¹ := inv_anti₀ ht0 (by linarith)
  have e2 : (1 - t)⁻¹ ≥ (1 - w)⁻¹ := inv_anti₀ ht0 (by linarith)
  have hTw : ∀ c : Zd d (sz.L n), ‖STThg C n p q w c b‖ ≤ (1 + C₆) * (1 - t)⁻¹ := fun c =>
    (CltFarUGen_Th_entry C n hU p q hw0 hw1 (hrow w hw0 hw1) c b).trans
      (mul_le_mul_of_nonneg_left e2 (by linarith))
  have hrv := hrow v hv0 hv1 a
  have hrv' : ∑ c, ‖Step2Gen_thetaKer C n p q v a c‖ ≤ C₆ * (1 - t)⁻¹ := by
    refine hrv.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left e1 hC₆
  calc ‖∑ c, Step2Gen_thetaKer C n p q v a c * STThg C n p q w c b‖
      ≤ ∑ c, ‖Step2Gen_thetaKer C n p q v a c * STThg C n p q w c b‖ := norm_sum_le _ _
    _ ≤ ∑ c, ‖Step2Gen_thetaKer C n p q v a c‖ * ((1 + C₆) * (1 - t)⁻¹) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hTw c) (norm_nonneg _)
    _ = (∑ c, ‖Step2Gen_thetaKer C n p q v a c‖) * ((1 + C₆) * (1 - t)⁻¹) := by rw [Finset.sum_mul]
    _ ≤ (C₆ * (1 - t)⁻¹) * ((1 + C₆) * (1 - t)⁻¹) :=
        mul_le_mul_of_nonneg_right hrv' (by have := inv_nonneg.2 ht0.le; positivity)
    _ = _ := by ring

end ThBounds

/-! ## 4. `f^{far}` over an abstract propagator and its Lipschitz bound in the propagator time -/

section FSum

/-- `f_a` of `3_5:2098` over the label set `P` for an abstract propagator `Th` (band `iniTermI_fSum`, `IniTermI:1291`;
`STfFarg` is the case `Th = Θ^{(σ₀σ₁)}_u`, `P = far`). -/
private def CltFarUGen_fSum {d L : ℕ} [NeZero L] (Th : Zd d L → Zd d L → ℂ) (s : ℝ) (X : (Fin 2 → Zd d L) → ℂ)
    (a : Fin 2 → Zd d L) (P : Zd d L → Prop) [DecidablePred P] : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter P, ∑ b₂ : Zd d L,
    Th (a 0) b₁ * X ![b₁, b₂] * (Th b₂ (a 1) - Th b₁ (a 1))

/-- **Lipschitz continuity of `f_a` in the propagator** (band `iniTermI_fSum_lip`, `IniTermI:1662`): if `Tv, Tv'` have entries
`≤ Tm` and differ by `≤ Δ` entrywise and `|X| ≤ X_m`, then `|f_{Tv} - f_{Tv'}| ≤ 4 N² T_m Δ X_m`, `N = L^d`. -/
private theorem CltFarUGen_fSum_lip {d L : ℕ} [NeZero L] {Tv Tv' : Zd d L → Zd d L → ℂ} {s Tm Δ Xm : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1) (hTm0 : 0 ≤ Tm) (hΔ0 : 0 ≤ Δ) (hT : ∀ x y, ‖Tv x y‖ ≤ Tm) (hT' : ∀ x y, ‖Tv' x y‖ ≤ Tm)
    (hD : ∀ x y, ‖Tv x y - Tv' x y‖ ≤ Δ) (X : (Fin 2 → Zd d L) → ℂ) (hX : ∀ b, ‖X b‖ ≤ Xm) (a : Fin 2 → Zd d L)
    (P : Zd d L → Prop) [DecidablePred P] :
    ‖CltFarUGen_fSum Tv s X a P - CltFarUGen_fSum Tv' s X a P‖ ≤ 4 * (Fintype.card (Zd d L) : ℝ) ^ 2 * Tm * Δ * Xm := by
  have hXm : 0 ≤ Xm := (norm_nonneg _).trans (hX (fun _ => 0))
  unfold CltFarUGen_fSum
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have h1s : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have hcard : ((Finset.univ.filter P).card : ℝ) ≤ (Fintype.card (Zd d L) : ℝ) := by
    exact_mod_cast Finset.card_le_univ _
  rw [← Finset.sum_sub_distrib]
  have hbd : ‖∑ b₁ ∈ Finset.univ.filter P, (∑ b₂ : Zd d L, Tv (a 0) b₁ * X ![b₁, b₂] *
        (Tv b₂ (a 1) - Tv b₁ (a 1)) -
      ∑ b₂ : Zd d L, Tv' (a 0) b₁ * X ![b₁, b₂] *
        (Tv' b₂ (a 1) - Tv' b₁ (a 1)))‖ ≤
      (Fintype.card (Zd d L) : ℝ) * ((Fintype.card (Zd d L) : ℝ) * (4 * Δ * Tm * Xm)) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ b₁ ∈ Finset.univ.filter P, ‖∑ b₂ : Zd d L, Tv (a 0) b₁ * X ![b₁, b₂] *
        (Tv b₂ (a 1) - Tv b₁ (a 1)) -
      ∑ b₂ : Zd d L, Tv' (a 0) b₁ * X ![b₁, b₂] *
        (Tv' b₂ (a 1) - Tv' b₁ (a 1))‖ ≤
        (Fintype.card (Zd d L) : ℝ) * (4 * Δ * Tm * Xm) := by
      intro b₁ _
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hpt2 : ∀ b₂ ∈ (Finset.univ : Finset (Zd d L)), ‖Tv (a 0) b₁ * X ![b₁, b₂] *
          (Tv b₂ (a 1) - Tv b₁ (a 1)) -
          Tv' (a 0) b₁ * X ![b₁, b₂] *
          (Tv' b₂ (a 1) - Tv' b₁ (a 1))‖ ≤ 4 * Δ * Tm * Xm := by
        intro b₂ _
        have e : Tv (a 0) b₁ * X ![b₁, b₂] *
            (Tv b₂ (a 1) - Tv b₁ (a 1)) -
            Tv' (a 0) b₁ * X ![b₁, b₂] *
            (Tv' b₂ (a 1) - Tv' b₁ (a 1)) =
            (Tv (a 0) b₁ - Tv' (a 0) b₁) * X ![b₁, b₂] *
              (Tv b₂ (a 1) - Tv b₁ (a 1)) +
            Tv' (a 0) b₁ * X ![b₁, b₂] *
              ((Tv b₂ (a 1) - Tv' b₂ (a 1)) -
                (Tv b₁ (a 1) - Tv' b₁ (a 1))) := by ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        have hr1 : ‖Tv b₂ (a 1) - Tv b₁ (a 1)‖ ≤ 2 * Tm :=
          (norm_sub_le _ _).trans (by have := hT b₂ (a 1); have := hT b₁ (a 1); linarith)
        have hr2 : ‖(Tv b₂ (a 1) - Tv' b₂ (a 1)) -
            (Tv b₁ (a 1) - Tv' b₁ (a 1))‖ ≤ 2 * Δ :=
          (norm_sub_le _ _).trans (by have := hD b₂ (a 1); have := hD b₁ (a 1); linarith)
        have hx := hX ![b₁, b₂]
        have n1 := norm_nonneg (X ![b₁, b₂])
        have a1 : ‖(Tv (a 0) b₁ - Tv' (a 0) b₁) * X ![b₁, b₂] *
            (Tv b₂ (a 1) - Tv b₁ (a 1))‖ ≤ Δ * Xm * (2 * Tm) := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul (hD _ _) hx n1 hΔ0) hr1 (norm_nonneg _) (by positivity)
        have a2 : ‖Tv' (a 0) b₁ * X ![b₁, b₂] *
            ((Tv b₂ (a 1) - Tv' b₂ (a 1)) -
              (Tv b₁ (a 1) - Tv' b₁ (a 1)))‖ ≤ Tm * Xm * (2 * Δ) := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul (hT' _ _) hx n1 hTm0) hr2 (norm_nonneg _) (by positivity)
        nlinarith [a1, a2]
      refine (Finset.sum_le_sum hpt2).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact le_rfl
    refine (Finset.sum_le_sum hpt).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  calc (1 - s) ^ 2 * ‖_‖ ≤ 1 * ((Fintype.card (Zd d L) : ℝ) * ((Fintype.card (Zd d L) : ℝ) * (4 * Δ * Tm * Xm))) :=
        mul_le_mul h1s hbd (norm_nonneg _) zero_le_one
    _ = _ := by ring

open Classical in
/-- `f^{far}` of the carrier is `CltFarUGen_fSum` of the carrier propagator `Θ^{(σ₀σ₁)}_u`, the far label set, and
`X = (𝓛-𝒦)^{(2)}_{s,σ}` (definitional). -/
private theorem CltFarUGen_STfFarg_eq {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (s u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STfFarg C n s u σ a ω = CltFarUGen_fSum (STThg C n (σ 0) (σ 1) u) s (fun b => C.L n s σ b ω - C.K n s σ b) a
      (fun b₁ : Zd d (sz.L n) =>
        Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
        Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)) := rfl

/-- **The Lipschitz bound of `f^{far}` in the propagator time** (band `iniTermI_STfFar_lip`, `IniTermI:1816`): from the semigroup law
and the row sums of `θ` (`hrow`, the second conjunct of `Step5KerGen_ThDecay` at the index), for `u, v ≤ t < 1` and
`|(𝓛-𝒦)^{(2)}_{s,σ}| ≤ X_m`: `|f_u - f_v| ≤ 4 c* N² (1-t)⁻³ |u-v| X_m`, `c* = C₆ (1+C₆)²`, `N = L^d`. -/
private theorem CltFarUGen_STfFarg_lip {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n)
    {C₆ s t u v Xm : ℝ} (hC₆ : 0 ≤ C₆) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hv0 : 0 ≤ v) (hvt : v ≤ t)
    (ht1 : t < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hrow : ∀ τ : ℝ, 0 ≤ τ → τ < 1 → ∀ p q : Bool, ∀ a, ∑ b, ‖Step2Gen_thetaKer C n p q τ a b‖ ≤ C₆ / (1 - τ))
    (hX : ∀ b, ‖C.L n s σ b ω - C.K n s σ b‖ ≤ Xm) :
    ‖STfFarg C n s u σ a ω - STfFarg C n s v σ a ω‖ ≤
      4 * (C₆ * (1 + C₆) ^ 2) * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |u - v| * Xm := by
  have ht0 : 0 < 1 - t := by linarith
  have hTm0 : 0 ≤ (1 + C₆) * (1 - t)⁻¹ := by have := inv_nonneg.2 ht0.le; positivity
  have hΔ0 : 0 ≤ |u - v| * (C₆ * (1 + C₆) * ((1 - t)⁻¹) ^ 2) := by have := inv_nonneg.2 ht0.le; positivity
  have hT : ∀ w, 0 ≤ w → w ≤ t → ∀ x y : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) w x y‖ ≤ (1 + C₆) * (1 - t)⁻¹ :=
    fun w hw0 hw x y => (CltFarUGen_Th_entry C n hU (σ 0) (σ 1) hw0 (by linarith) (hrow w hw0 (by linarith) _ _) x y).trans
      (mul_le_mul_of_nonneg_left (inv_anti₀ ht0 (by linarith)) (by linarith))
  rw [CltFarUGen_STfFarg_eq, CltFarUGen_STfFarg_eq]
  refine le_trans (CltFarUGen_fSum_lip (Tv := STThg C n (σ 0) (σ 1) u) (Tv' := STThg C n (σ 0) (σ 1) v) hs0 hs1 hTm0 hΔ0
    (hT u hu0 hut) (hT v hv0 hvt)
    (fun x y => CltFarUGen_Th_lip C n hU (σ 0) (σ 1) hu0 hut hv0 hvt ht1 hC₆ (fun τ h0 h1 a => hrow τ h0 h1 _ _ a) x y)
    (fun b => C.L n s σ b ω - C.K n s σ b) hX a _) (le_of_eq ?_)
  ring

/-- **The pointwise step of the grid argument** (band `iniTermI_unif_det`, `IniTermI:1939`): `|f_u - f_v| ≤ 16 c* N^{-5} ≤ N^{-3} ≤ ζ`
(`T_m ≤ N²`, `X_m ≤ 4N`, `|u-v| ≤ N^{-14}`, `16 c* ≤ N²`), so `|f_v| ≤ N^{τ/2} ζ` gives `|f_u| ≤ N^τ ζ`. -/
private theorem CltFarUGen_unif_det {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (hd : 3 ≤ d) (n : ℕ) {𝔡 cs s t u v τ : ℝ}
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹) (hA1 : 1 ≤ STAI sz n)
    (hb : 2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (4 / 5 : ℝ))
    (hN : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ)) (hNt : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (hcs : 0 ≤ cs)
    (hNcs : 16 * cs ≤ ((sz.size n : ℕ) : ℝ) ^ 2) (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (huv : |u - v| ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ 14) {σ : Fin 2 → Bool} (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hXω : ∀ b, ‖C.L n s σ b ω - C.K n s σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (sz.Bctl n s) ^ 2)
    (hlip : ‖STfFarg C n s u σ a ω - STfFarg C n s v σ a ω‖ ≤
      4 * cs * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |u - v| *
        (((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (sz.Bctl n s) ^ 2))
    (hfv : ‖STfFarg C n s v σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.STCltFarZeta n a) :
    ‖STfFarg C n s u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * sz.STCltFarZeta n a := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hs1 : s < 1 := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s :=
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ hL1 (by omega : 2 ≤ d))).trans
      (hreg.trans (by linarith))
  have hBs : sz.Bctl n s ≤ 2 := by
    have := iniTermI_Bctl_le sz n hg hs1 hlow
    have h2 : (STAI sz n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
    linarith
  have hBs0 : 0 ≤ sz.Bctl n s := (st_Bctl_pos sz hs1).le
  have hTm := iniTermI_oneSub_inv_le sz hd n hA1 hg hreg
  have hTm0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.2 (by linarith)
  have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ N := by
    rw [iniTermI_card_Zd, hNdef]
    have : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    unfold Sizes.size; exact_mod_cast this
  have hN14 : (0 : ℝ) < N ^ 14 := by positivity
  have hB2 : (sz.Bctl n s) ^ 2 ≤ 4 := by nlinarith
  have hXm4 : N ^ (1 : ℝ) * (sz.Bctl n s) ^ 2 ≤ 4 * N := by
    rw [Real.rpow_one]; nlinarith
  have hX0 : 0 ≤ N ^ (1 : ℝ) * (sz.Bctl n s) ^ 2 := by positivity
  have e3 : N ^ (-(3 : ℝ)) = (N ^ 3)⁻¹ := by
    rw [Real.rpow_neg hN0.le]; congr 1; exact_mod_cast Real.rpow_natCast N 3
  have e1 : (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have e2 : ((1 - t)⁻¹) ^ 3 ≤ (N ^ 2) ^ 3 := pow_le_pow_left₀ hTm0 hTm 3
  have herr : 4 * cs * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |u - v| * (N ^ (1 : ℝ) * (sz.Bctl n s) ^ 2)
      ≤ N ^ (-(3 : ℝ)) := by
    have h1 : 4 * cs * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 ≤ 4 * cs * N ^ 2 * (N ^ 2) ^ 3 := by
      have := mul_le_mul e1 e2 (by positivity) (by positivity)
      have h4 : 0 ≤ 4 * cs := by positivity
      calc 4 * cs * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3
          = (4 * cs) * ((Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3) := by ring
        _ ≤ (4 * cs) * (N ^ 2 * (N ^ 2) ^ 3) := mul_le_mul_of_nonneg_left this h4
        _ = _ := by ring
    have h2 : 4 * cs * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |u - v| ≤
        4 * cs * N ^ 2 * (N ^ 2) ^ 3 * (1 / N ^ 14) :=
      mul_le_mul h1 huv (abs_nonneg _) (by positivity)
    calc _ ≤ 4 * cs * N ^ 2 * (N ^ 2) ^ 3 * (1 / N ^ 14) * (4 * N) := mul_le_mul h2 hXm4 hX0 (by positivity)
      _ = 16 * cs / N ^ 5 := by field_simp; ring
      _ ≤ (N ^ 3)⁻¹ := by
          rw [div_le_iff₀ (by positivity)]
          calc 16 * cs ≤ N ^ 2 := hNcs
            _ = (N ^ 3)⁻¹ * N ^ 5 := by field_simp
      _ = _ := e3.symm
  have hz := iniTermI_zeta_ge sz hd n hg hgΛ hA1 hb a
  have hz0 : 0 ≤ sz.STCltFarZeta n a := (Real.rpow_nonneg hN0.le _).trans hz
  have hsub := norm_sub_norm_le (STfFarg C n s u σ a ω) (STfFarg C n s v σ a ω)
  have hNτ' : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by rw [← Real.rpow_add hN0]; congr 1; ring
  rw [hNτ']
  nlinarith [mul_nonneg hz0 (sub_nonneg.2 hNt), mul_nonneg hz0 (mul_nonneg (sub_nonneg.2 hNt) (sub_nonneg.2 hNt))]

end FSum

/-! ## 5. Target 7: the `u`-uniform `lem;CLT` over the carrier -/

section Uniform

open Classical in
/-- The failure event of `lem;CLT` at the propagator time `v` (band `iniTermI_cltBad`, `IniTermI:1793`), over the carrier. -/
private def CltFarUGen_bad {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (s : ℕ → ℝ) (τ : ℝ) (n : ℕ) (v : ℝ) : Set sz.SeqΩ :=
  {ω | ∃ p : sz.STCltFarIdx s n v, ((sz.size n : ℕ) : ℝ) ^ τ * sz.STCltFarZeta n p.1.2 <
    ‖STfFarg C n (s n) v p.1.1.1 p.1.2 ω‖}

/-- The guard (g) (UBA-C1): at an index with `0 < lam ≤ 𝔡⁻¹`, R1 gives `0 < gK ≤ 𝔡⁻¹`. -/
private theorem CltFarUGen_guard {g l A Λ : ℝ} (h : 0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) (hl : 0 < l) (hlΛ : l ≤ Λ) :
    0 < g ∧ g ≤ Λ :=
  have hg := IniTermIIGen_cmp_pos' h hl
  ⟨hg, (Step5KerGen_cmp_pos h hg).2.trans hlΛ⟩

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **Target 7, the pin `stCltFarUgL_of`** (`T2484_CltFarUOf`; band `stCltFar_uniform`, `IniTermI:2005`, re-derived below): the
`u`-uniform `lem;CLT` of case (i) over a carrier tuple.  (a) `f^{far}_u` depends on `u` only through `Θ_u`, which is Lipschitz with
the constant `c* N² (1-t)⁻³` (`CltFarUGen_STfFarg_lip`, row sums of the kernel facts), `(1-t)⁻¹ ≤ N²`, `X_m ≤ 4N` (`STLKgL` at
`s`, `k = 2`, w.h.p.); (b) the index set grows with `ℓ_u`, so `u ∈ [s_k - δ, s_k]` uses `s_k`; (c) per grid point
`s_k = s + k (t-s)/N^{14}` (`k ≤ N^{14}`), X1's far pin at the worst sequence `t'_n = s_{k*_n}` (`CltFarUGen_cltFar_of`, the class
`IniTermGen_CltFlow`) and the union over `N^{14}` grid points; (d) `stIngR5gL_hyps_restrict`. -/
theorem stCltFarUgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) →
    Step5CasesGen_FlowFacts d Flow mk T0 → IniTermGen_KerFacts d Flow mk gK → IniTermGen_CltFlow d law Flow mk T0 →
    STIngR5gL d STReg5I law Flow mk T0 (fun sz z s t => STCltFarUConclgL (mk sz z) (law sz) s t) := by
  classical
  intro hP hF hKF hFlow hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hreg hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  obtain ⟨κm, hκm, hFl⟩ := hF κ hκ
  obtain ⟨⟨h𝔠, h𝔡', hSz, hBw, hWO⟩, hT1, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT1 n)
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht1 n)
  obtain ⟨C₆, C₈, Cs, c₀, A, hC₆, hC₈, hCs, hc₀, hA, HK⟩ := hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨hUs, hdec, hR1, hE1, hG⟩ := HK sz ε 𝔠 z hflow
  set cs : ℝ := C₆ * (1 + C₆) ^ 2 with hcs
  have hcs0 : 0 ≤ cs := by positivity
  intro τ hτ D hD
  set Mn : ℕ → ℕ := fun n => (sz.size n) ^ 14 with hMn
  have hMn1 : ∀ n, 1 ≤ Mn n := fun n => Nat.one_le_pow _ _ (sz.one_le_size n)
  set ug : ℕ → ℕ → ℝ := fun n k => s n + (k : ℝ) * ((t n - s n) / (Mn n : ℝ)) with hug
  have hδ0 : ∀ n, 0 < (t n - s n) / (Mn n : ℝ) := fun n => div_pos (by linarith [hst n])
    (by exact_mod_cast hMn1 n)
  have hug_gt : ∀ n k, 1 ≤ k → s n < ug n k := fun n k hk => by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have := mul_pos this (hδ0 n); simp only [hug]; linarith
  have hug_le : ∀ n k, k ≤ Mn n → ug n k ≤ t n := fun n k hk => by
    have h1 : (k : ℝ) ≤ Mn n := by exact_mod_cast hk
    have hM0 : (0 : ℝ) < Mn n := by exact_mod_cast hMn1 n
    have : (k : ℝ) * ((t n - s n) / (Mn n : ℝ)) ≤ (Mn n : ℝ) * ((t n - s n) / (Mn n : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 (hδ0 n).le
    have h2 : (Mn n : ℝ) * ((t n - s n) / (Mn n : ℝ)) = t n - s n := by field_simp
    simp only [hug]; linarith
  let pb : ℕ → ℕ → ENNReal := fun n k => law sz (CltFarUGen_bad (mk sz z) s (τ / 2) n (ug n k))
  have hex : ∀ n, ∃ k ∈ Finset.Icc 1 (Mn n), ∀ k' ∈ Finset.Icc 1 (Mn n), pb n k' ≤ pb n k := fun n =>
    Finset.exists_max_image (Finset.Icc 1 (Mn n)) (fun k => pb n k) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hMn1 n⟩⟩
  choose kst hkmem hkmax using hex
  set t' : ℕ → ℝ := fun n => ug n (kst n) with ht'def
  have hst' : ∀ n, s n < t' n := fun n => hug_gt n _ (Finset.mem_Icc.1 (hkmem n)).1
  have ht'le : ∀ n, t' n ≤ t n := fun n => hug_le n _ (Finset.mem_Icc.1 (hkmem n)).2
  obtain ⟨hR', hCon', hS1', hS2', hLmax', hLKU'⟩ :=
    stIngR5gL_hyps_restrict sz (mk sz z) (law sz) s t t' (1 / 100) Cd (by norm_num) hst' ht'le ht1 hreg hCon hS1 hS2 hLmax hLKU
  have hH := CltFarUGen_cltFar_of d law Flow mk T0 hF hFlow hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow Cd s t' hs0 hst'
    (fun n => (ht'le n).trans (ht n)) hR' hS2'.1 hS2'.2.2
  have hev1 := hH (τ / 2) (half_pos hτ) (D + 14 + 1) (by linarith)
  have hev2 : ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc 1 (Mn n),
      pb n k ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 14 + 1))) := by
    filter_upwards [hev1] with n hn k hk
    exact (hkmax n k hk).trans hn
  have hXev := StochDomAt.highProb (hLK 2 (by norm_num)) (τ := 1) one_pos
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ ∧ 1 ≤ STAI sz n := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n h1 h2
    exact ⟨h2.1, h1.2, h2.2⟩
  have hN4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hSz.eventually_ge_atTop 4
  have hNcs : ∀ᶠ n in atTop, 16 * cs ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by
    filter_upwards [hSz.eventually_ge_atTop (max 1 (16 * cs))] with n hn
    have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hn
    nlinarith [le_max_right 1 (16 * cs)]
  have hNτ : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hSz).eventually_ge_atTop 2
  have hbig : ∀ᶠ n in atTop, 2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (4 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp hSz).eventually_ge_atTop _
  filter_upwards [hev2, hXev (D + 1) (by linarith), hlam, hN4, hNcs, hNτ, hbig] with n h2 hX hl hN hNc hNt hb
  obtain ⟨hg, hgΛ, hA1⟩ := hl
  obtain ⟨hgK, hgKΛ⟩ := CltFarUGen_guard (hR1 n) hg hgΛ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hcover : badSetAt sz.size (fun n (q : Σ u : TimeIcc s t n, sz.STCltFarIdx s n (u : ℝ)) ω =>
        ‖STfFarg (mk sz z) n (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
      (fun n q _ => sz.STCltFarZeta n q.2.1.2) τ n ⊆
      (⋃ k ∈ Finset.Icc 1 (Mn n), CltFarUGen_bad (mk sz z) s (τ / 2) n (ug n k)) ∪
        {ω | ∀ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
          ‖(mk sz z).L n (s n) p.1 p.2 ω - (mk sz z).K n (s n) p.1 p.2‖ ≤ N ^ (1 : ℝ) * (sz.Bctl n (s n)) ^ 2}ᶜ := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hXω : ∀ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
        ‖(mk sz z).L n (s n) p.1 p.2 ω - (mk sz z).K n (s n) p.1 p.2‖ ≤ N ^ (1 : ℝ) * (sz.Bctl n (s n)) ^ 2 := by
      simpa using hc2
    simp only [Set.mem_iUnion, not_exists] at hc1
    obtain ⟨q, hq⟩ := hω
    obtain ⟨⟨u, hu⟩, ⟨⟨σsub, a⟩, hcond⟩⟩ := q
    have hq' : N ^ τ * sz.STCltFarZeta n a < ‖STfFarg (mk sz z) n (s n) u σsub.1 a ω‖ := hq
    obtain ⟨k, hk1, hkM, huk, hkd⟩ := iniTermI_grid (hst n) hu.1 hu.2 (Mn n) (hMn1 n)
    have hv_le : ug n k ≤ t n := hug_le n k hkM
    have hu0 : 0 ≤ u := (hs0 n).trans hu.1
    have hv0 : 0 ≤ ug n k := hu0.trans huk
    have hℓ : ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) (ug n k) :=
      ellT_mono hg.le huk (hv_le.trans_lt (ht1 n))
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hlog0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
    have hcv : Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (ug n k) ∧
        ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (ug n k) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n) :=
      ⟨hcond.1.trans hℓ, hcond.2.trans (by
        have := mul_le_mul_of_nonneg_left hℓ (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
        linarith)⟩
    have hno := hc1 k (Finset.mem_Icc.2 ⟨hk1, hkM⟩)
    have hfv : ‖STfFarg (mk sz z) n (s n) (ug n k) σsub.1 a ω‖ ≤ N ^ (τ / 2) * sz.STCltFarZeta n a := by
      by_contra h
      exact hno ⟨⟨(σsub, a), hcv⟩, not_le.1 h⟩
    have hMnN : ((Mn n : ℕ) : ℝ) = N ^ 14 := by rw [hMn, hNdef]; push_cast; rfl
    have hN14 : (0 : ℝ) < N ^ 14 := by positivity
    have huv : |u - ug n k| ≤ 1 / N ^ 14 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have h1 : ug n k - u ≤ (t n - s n) / (Mn n : ℝ) := by simp only [hug]; linarith
      refine h1.trans ?_
      rw [hMnN]
      exact div_le_div_of_nonneg_right (by linarith [ht1 n, hs0 n]) hN14.le
    have hlip := CltFarUGen_STfFarg_lip (mk sz z) n (hUs n) hC₆.le (hs0 n) (hs1 n).le hu0 hu.2 hv0 hv_le (ht1 n) σsub.1 a ω
      (fun τ' h0 h1 p q a' => (hdec n hgK hgKΛ p q τ' h0 h1).2 a') (fun b => hXω (σsub.1, b))
    have := CltFarUGen_unif_det (mk sz z) hd n (cs := cs) hg hgΛ hA1 hb hN hNt hcs0 hNc (hs0 n) (hst n).le (ht1 n)
      (hreg n).1 huv a ω (fun b => hXω (σsub.1, b)) hlip hfv
    exact absurd hq' (not_lt.2 this)
  change law sz (badSetAt sz.size _ _ τ n) ≤ ENNReal.ofReal (N ^ (-D))
  have hcard' : (Finset.Icc 1 (Mn n)).card = Mn n := by simp
  calc law sz (badSetAt sz.size _ _ τ n) ≤ law sz ((⋃ k ∈ Finset.Icc 1 (Mn n),
        CltFarUGen_bad (mk sz z) s (τ / 2) n (ug n k)) ∪ _) := measure_mono hcover
    _ ≤ law sz (⋃ k ∈ Finset.Icc 1 (Mn n), CltFarUGen_bad (mk sz z) s (τ / 2) n (ug n k)) +
        law sz {ω | ∀ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
          ‖(mk sz z).L n (s n) p.1 p.2 ω - (mk sz z).K n (s n) p.1 p.2‖ ≤ N ^ (1 : ℝ) * (sz.Bctl n (s n)) ^ 2}ᶜ :=
        measure_union_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 (Mn n), ENNReal.ofReal (N ^ (-(D + 14 + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) :=
        add_le_add ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum h2)) hX
    _ = ENNReal.ofReal ((Mn n : ℝ) * N ^ (-(D + 14 + 1)) + N ^ (-(D + 1))) := by
        rw [Finset.sum_const, hcard', nsmul_eq_mul, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (N ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have hMnN : ((Mn n : ℕ) : ℝ) = N ^ 14 := by rw [hMn, hNdef]; push_cast; rfl
        rw [hMnN]
        exact iniTermI_union_numeric (by linarith) 14

end Uniform

/-! ## 6. Band re-derivation and compiled nonempty instances (target 10; `d = 3`, `szB`, `zB`) -/

/-- **Target 7 at the band** (re-derivation of `stCltFar_uniform`, `IniTermI:2005`): the generic pin at the band tuple
`(seqP, STFlow, bandFM ∘ STflowE, lemT)`, `gK = sz.lam`, through `Step5Gen_ingR5_iff_congr` and the bridge of target 6. -/
theorem iniTermGen_cltFarU_band (d : ℕ) : STIngR5 d STReg5I (fun sz E s t => sz.STCltFarUConcl E s t) :=
  (Step5Gen_ingR5_iff_congr d STReg5I (fun sz E s t => sz.STCltFarUConcl E s t)
    (fun sz z s t => STCltFarUConclgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t)
    (fun sz z s t => bandFM_STCltFarUConcl sz (STflowE z) s t)).2
    (stCltFarUgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz _ => sz.lam) (fun sz => inferInstance)
      (step5CasesGen_flowFacts_band d) (iniTermGen_kerFacts_band d) (iniTermGen_cltFlow_band d))

section Inst

open RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

/-- **Target 5 at `(szB, zB)`** (`L = 4`, `W_n = n + 4`, `lam = 1`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), case (i) window
`(s, t) = (7/8, 15/16)` (`szB_reg5I`; `15/16 ≤ 31/32 ≤ lemT`): every field of the class is discharged. -/
example : ∃ κ' δ : ℝ, 0 < κ' ∧ κ' ≤ 1 ∧ 0 < δ ∧
    ∃ (H₀ : ∀ n, Matrix (Idx 3 (szB.L n) (szB.W n)) (Idx 3 (szB.L n) (szB.W n)) ℂ) (g' E : ℕ → ℝ),
      (∀ n, κ' ≤ ((bandFM szB (STflowE zB)).m n).im) ∧
      (∀ᶠ n in atTop, ((szB.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - lemT (zB n)) ∧
      CltRepg (bandFM szB (STflowE zB)) (Sizes.seqP szB) H₀ g' E ∧
      STThPropsg (bandFM szB (STflowE zB)) ∧ STExpInvgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∧
      STMfarg (bandFM szB (STflowE zB)) (fun _ => 7 / 8) ∧
      STGijDecgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) ∧
      STKfargL (bandFM szB (STflowE zB)) (fun _ => 7 / 8) ∧ STKpropsg (bandFM szB (STflowE zB)) (fun _ => 7 / 8) := by
  obtain ⟨κ', δ, h1, h2, h3, H⟩ :=
    iniTermGen_cltFlow_band 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨H₀, g', E, hm, hev, hrep, hM, hTh, hX, hst⟩ := H (1 / 6) szB zB flow_zB
  exact ⟨κ', δ, h1, h2, h3, H₀, g', E, hm, hev, hrep, hTh, hX,
    hst (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
      (szB_flow_ht (by norm_num)) szB_reg5I⟩

/-- **The far pin from the class at `(szB, zB)`**, window `(7/8, 15/16)`: `CltFarUGen_cltFar_of` (the closure of `HCltOf` under
`t ↦ t'`) gives X1's far conclusion; the two restricted Step-2 premises stay hypotheses (another gate's pins). -/
example (hLE : STLocalEntryUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hGD : STGdecayWgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) 1) :
    STCltFarConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  CltFarUGen_cltFar_of 3 (fun sz => Sizes.seqP sz) _ _ _ (step5CasesGen_flowFacts_band 3) (iniTermGen_cltFlow_band 3) le_rfl
    (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) szB zB flow_zB 1 _ _ (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5I hLE hGD

/-- **Target 6, the bridge at `(szB, zB)`**: the band `STCltFarUConcl` is the generic one. -/
example : szB.STCltFarUConcl (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) ↔
    STCltFarUConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  bandFM_STCltFarUConcl szB _ _ _

/-- **Target 6, `stIngR5gL_hyps_restrict` at `(szB, zB, 7/8, 15/16)`**, `t' = 29/32`: the regime and `(con_st_ind)` are discharged,
the five stochastic premises of Steps 1-4 stay hypotheses (other gates' pins). -/
example (Cd : ℝ)
    (hS1 : STStep1LoopgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hS2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd)
    (hLmax : STLmaxUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hLKU : STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STReg5I szB (fun _ => 7 / 8) (fun _ => 29 / 32) ∧ szB.STConStInd (1 / 100) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧
      STStep1LoopgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧
      STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 29 / 32) Cd ∧
      STLmaxUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧
      STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 29 / 32) :=
  stIngR5gL_hyps_restrict szB (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => 29 / 32)
    (1 / 100) Cd (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5I
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hS1 hS2 hLmax hLKU

/-- **Target 7 at the band**: the generic pin `stCltFarUgL_of` at the band tuple, read through the band shape, gives the instance of
`Step5Pins` at `(szB, zB, 7/8, 15/16)` for every `Cd > 0` (as `inst_cltFarU_proved`, `IniTermI:3800`); the pin's hypotheses are
discharged by the band results, the stochastic premises of Steps 1-4 are the premises of the instance. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => sz.STCltFarUConcl E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_ing5_I STReg5I _ (iniTermGen_cltFarU_band 3) szB_reg5I Cd hCd

/-- **Target 7 applied at `(szB, zB, 7/8, 15/16)`**: the pin `stCltFarUgL_of` at the band tuple, its five hypotheses discharged
by the band results; the flow (`flow_zB`), the window (`szB_reg5I`, `15/16 ≤ 31/32 ≤ lemT`) and `(con_st_ind)` (`conStInd_const`)
are discharged; the stochastic premises of Steps 1-4 are hypotheses of the example (other gates' pins). -/
example (Cd : ℝ) (hCd : 0 < Cd)
    (hKb : STKboundgL (bandFM szB (STflowE zB)) (Sizes.seqP szB)) (hKw : STKwardgL (bandFM szB (STflowE zB)) (Sizes.seqP szB))
    (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hDecS : STDecayStronggL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8))
    (hS1 : STStep1LoopgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hS2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd)
    (hLmax : STLmaxUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hLKU : STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      STCltFarUConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := stCltFarUgL_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz _ => sz.lam) (fun sz => inferInstance)
    (step5CasesGen_flowFacts_band 3) (iniTermGen_kerFacts_band 3) (iniTermGen_cltFlow_band 3) le_rfl (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, H (1 / 6) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5I hKb hKw hLK hDec hDecS
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) hS1 hS2 hLmax hLKU⟩

end Inst

end RBM.BA

end
