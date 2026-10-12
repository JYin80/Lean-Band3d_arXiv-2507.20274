/-
Release check for T2453 (dispatcher V3, Mon Oct 12 12:24 UTC 2026; DECISIONS §264).  BA-T T4s1: the stopped grid Duhamel and Azuma layer of
`Induction/GridDuhamelN.lean` over the carrier, on T8b's kernel `Step2Gen_UN` (supervisor 1152 U-C4: one kernel), in the new
file `Chain/GridDuhamelGen.lean`; `GridDuhamelN` is not edited (outside the certificate lane).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2453_`; content binding; the measurability
premise of `T2453_StoppedAzumaNg` may be restated in the 1a, with the change reported), then shapes (not binding): the `Ugen`
bridge (U-C4), the BA readings, the band routes.  Part 3 (G1): the public band names of `GridDuhamelN`, unchanged; the auditor
adds `example : <statement> := <name>` for each.  Part 4: not this row (`AzumaProxyN`, `AzumaProxyN2` go to T4s2).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2453-check.lean
-/
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.Step2BA
import RBM3D.BA.TwistGrid2

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier and T8b's kernel (U-C4: the one kernel), its band and BA readings
#check @RBM.BA.FlowFM
#check @RBM.BA.bandFM
#check @RBM.BA.baFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.baStep2Mat
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Gen_Theta
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Kern_uKer_band
#check @RBM.BA.Step2Kern_UN_band
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.BAuKer
#check @RBM.BA.BAUN
#check @RBM.BA.BAReal
#check @RBM.BA.BAmF
-- target 3: the semigroup law, band and BA sources
#check @RBM.UN
#check @RBM.uKer
#check @RBM.cycProd
#check @RBM.mSigma
#check @RBM.norm_mul_mSigma_lt_one
#check @RBM.Path.ukerMat
#check @RBM.Path.ukerMat_self
#check @RBM.Path.ukerMat_mul
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.BAuKerSemigroup
#check @RBM.BA.BAuKerSemigroup_holds
-- target 4: the vocabulary the generic forms read
#check @RBM.BA.STLKMg
#check @RBM.BA.bandStep2_STLKM
#check @RBM.BA.STgAg
#check @RBM.BA.STgANg
#check @RBM.BA.STeeUMg
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STGridRepNAtgL
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.isProbabilityMeasure_pathP
#check @RBM.Path.filt
#check @RBM.Path.pathH
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
-- targets 1, 5, 6: the model-free tools of the band proofs
#check @RBM.Path.duhamel_telescope
#check @RBM.Path.sum_stopped
#check @RBM.Path.azuma_complex
#check @RBM.Path.pathH_measurable_filt
#check @RBM.Gauss.walk_measurable_loopFine
-- the twisted BA twin of pin G1 (stage TL; unaffected)
#check @RBM.BA.BATwistDuhamel
#check @RBM.BA.BATwistDuhamel_holds

/-! ## Part 2: the target statements (content binding) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 3** (content binding): the semigroup law of `(def_Ustz)` (`3_5:116`) for the carrier kernel `Step2Gen_uKer`
(`Chain/Step2Gen.lean:192`) at size index `n`, every charge pair.  It replaces the band window `|E| ≤ 2` of
`GridDuhamelN_Ugen_self`/`_comp` (`GridDuhamelN.lean:91, 108`); it has the content of the merged `BAuKerSemigroup`
(`BA/TwistGrid.lean:195`) read through `Step2Kern_uKer_BA`. -/
def T2453_USemigroup {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  ∀ (σ σ' : Bool) (u v w : ℝ), 0 ≤ v → v < 1 → 0 ≤ w → w < 1 →
    Step2Gen_uKer C n σ σ' v v = 1 ∧
      Step2Gen_uKer C n σ σ' v w * Step2Gen_uKer C n σ σ' u v = Step2Gen_uKer C n σ σ' u w

/-- **Target 1** (content binding): the Duhamel telescope of `GridDuhamelN_Ugen_duhamel_telescope` (`:161`) for
`Step2Gen_UN` (no new kernel, U-C4), under target 3 in place of `3 ≤ L`, `|E| ≤ 2`. -/
def T2453_UNTelescope : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2453_USemigroup C n →
    ∀ {k : ℕ} (σ : Fin k → Bool) (u : ℕ → ℝ) (m : ℕ), (∀ j ≤ m, 0 ≤ u j) → (∀ j ≤ m, u j < 1) →
      ∀ A : ℕ → ((Fin k → Zd d (sz.L n)) → ℂ),
        A m = Step2Gen_UN C n σ (u 0) (u m) (A 0) +
          ∑ j ∈ Finset.range m, Step2Gen_UN C n σ (u (j + 1)) (u m)
            (A (j + 1) - Step2Gen_UN C n σ (u j) (u (j + 1)) (A j))

/-- **Target 5** (content binding): pin G1 (`int_K-L_ST`, `3_5:134`) over `Step2Mat`, the band `StoppedDuhamelN`
(`GridDuhamelN.lean:293`) with `STLKMg`/`Cm.Hpath` for `STLKM`/`pathH`, `Cm.Pp` for `pathP`, `Step2Gen_UN` for `Ugen`, and target 3
for `|E n| < 2`.  The `let`s are target 4's `AvecNg` (`A`) and the conditional mean (`Y`); the summand is
`predIncNg + martIncNg`. -/
def T2453_StoppedDuhamelNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, T2453_USemigroup Cm.toFlowFM n) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    (∀ n, K n ≠ 0) →
    ∀ (n k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz), min j (τ ω) ≤ K n →
      let A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun i ω' a =>
        STLKMg Cm n (gridTime s t K n i) (Cm.Hpath s t K n i ω') σ a
      let Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun i ω' a =>
        MeasureTheory.condExp (filt sz i) Cm.Pp (fun ω'' => A (i + 1) ω'' a) ω'
      A (min j (τ ω)) ω =
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω))) (A 0 ω) +
          ∑ i ∈ Finset.range (min j (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
              (fun a : Fin k → Zd d (sz.L n) =>
                (Y i ω a - Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n i) (gridTime s t K n (i + 1)) (A i ω) a) +
                  (A (i + 1) ω a - Y i ω a))

/-- **Target 6** (content binding, measurability premise restatable): pin G3 over `Step2Mat`, the band `StoppedAzumaN`
(`GridDuhamelN.lean:531`) with `Step2Gen_UN` for `Ugen` and `Cm.Pp` for `pathP`; the band's five window premises are unused
(`:553`) and dropped; the premise is the `filt sz j`-measurability of target 4's `AvecNg … j`.  `ξ` is `martIncNg`. -/
def T2453_StoppedAzumaNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]
    (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n k : ℕ) (σ : Fin k → Bool),
    (∀ (j : ℕ) (b : Fin k → Zd d (sz.L n)),
      Measurable[filt sz j] (fun ω => STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ b)) →
    ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ m : ℕ, m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      let ξ : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun i ω' b =>
        STLKMg Cm n (gridTime s t K n (i + 1)) (Cm.Hpath s t K n (i + 1) ω') σ b -
          MeasureTheory.condExp (filt sz i) Cm.Pp
            (fun ω'' => STLKMg Cm n (gridTime s t K n (i + 1)) (Cm.Hpath s t K n (i + 1) ω'') σ b) ω'
      (∀ j < m,
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m) (ξ j ω') a) ω).re)
          (c j) Cm.Pp ∧
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m) (ξ j ω') a) ω).im)
          (c j) Cm.Pp) →
      ∀ x : ℝ, 0 ≤ x →
        (Cm.Pp).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n m) (ξ j ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ)))

/-- Targets 1, 3, 5 as Prop values. -/
example : Prop := T2453_UNTelescope
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2453_USemigroup C n
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ), T2453_StoppedDuhamelNg Cm s t K

/-- **Target 2 shape (U-C4; the two sides agree definitionally, checked on the branch):** the bridge `Ugen = Step2Gen_UN (bandFM …)` is the merged
`Step2Kern_UN_band` (`Chain/Step2Gen.lean:328`, read right to left) through the definition of `Ugen` (`GridDuhamelN.lean:65-67`):
no third kernel. -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (v w : ℝ)
    (A : (Fin k → Zd d (sz.L n)) → ℂ),
    (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v w A = Step2Gen_UN (bandFM sz E) n σ v w A) ↔
      (RBM.UN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) v w A = Step2Gen_UN (bandFM sz E) n σ v w A)

/-- E-C1 shape: the BA reading of the one kernel is stage E's `BAUN` (the merged `Step2Kern_UN_BA`, `Chain/Step2Kern.lean:124`,
under its `Im` premise). -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ),
    Step2Gen_UN (baFM sz lam0 E) n σ s t A = BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t A

/-- Target 3, band instance (this row: `step2Gen_USemigroup_band`) and BA instance (T4-BA, not this row: `BAuKer_self`,
`BAuKer_comp` through `Step2Kern_uKer_BA`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ), |E n| ≤ 2 → T2453_USemigroup (bandFM sz E) n
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ),
  BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 →
    T2453_USemigroup (baFM sz lam0 E) n

/-- Target 4, `AvecNg_two` (a definitional equation): at `k = 2` the observable is `STgAg` (`Chain/Step2Gen.lean:836`). -/
example : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : PathΩ sz),
    STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ a = STgAg Cm s t K n σ a j ω

/-- Target 7 (a), band routes (not binding): the generic pins at `bandStep2Mat` give the merged band pins. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ),
  T2453_StoppedDuhamelNg (bandStep2Mat sz E) s t K → RBM.Ind.StoppedDuhamelN sz E s t K
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ),
  @T2453_StoppedAzumaNg d sz (bandStep2Mat sz E) (isProbabilityMeasure_pathP sz) s t K →
    RBM.Ind.StoppedAzumaN sz E s t K

/-- BA reading of target 5, statement level (the BA proof of its premises is T4-BA's). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ),
  T2453_StoppedDuhamelNg (baStep2Mat sz lam0 E) s t K

end RBM.BA

end

/-! ## Part 3 (G1): the public band names of `GridDuhamelN` (file not edited; statements unchanged) -/
#check @RBM.Ind.Ugen
#check @RBM.Ind.GridDuhamelN_Ugen_add
#check @RBM.Ind.GridDuhamelN_Ugen_self
#check @RBM.Ind.GridDuhamelN_Ugen_comp
#check @RBM.Ind.GridDuhamelN_UgenHom
#check @RBM.Ind.GridDuhamelN_UgenHom_apply
#check @RBM.Ind.GridDuhamelN_Ugen_duhamel_telescope
#check @RBM.Ind.Ugen_two_eq_Uop
#check @RBM.Ind.AvecN
#check @RBM.Ind.martIncN
#check @RBM.Ind.predIncN
#check @RBM.Ind.StoppedDuhamelN
#check @RBM.Ind.stoppedDuhamelN_at
#check @RBM.Ind.stoppedDuhamelN
#check @RBM.Ind.AvecN_two
#check @RBM.Ind.martIncN_two
#check @RBM.Ind.predIncN_two
#check @RBM.Ind.stoppedDuhamel105_of_stoppedDuhamelN
#check @RBM.Ind.StoppedAzumaN
#check @RBM.Ind.stoppedAzumaN_at
#check @RBM.Ind.stoppedAzumaN

/-! ## Part 4: not this row (`AzumaProxyN`, `AzumaProxyN2` go to T4s2: they prove T4s2's pins and read T4s2/T5s2 vocabulary) -/
#check @RBM.Ind.AzumaSubGN
#check @RBM.Ind.azumaSubGN
#check @RBM.Ind.YMomentsN
#check @RBM.Ind.yMomentsN
#check @RBM.Ind.qvFormN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.azumaProxy_subG_ugen
#check @RBM.Ind.zero_mem_goodSetN_of_levels
#check @RBM.Gauss.Sizes.GoodSetN
