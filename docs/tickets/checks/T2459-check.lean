/-
Release check for T2459 (dispatcher V3, Mon Oct 12 14:18 UTC 2026; DECISIONS §267).  BA-U U5 design gate: BA case (iii) of Step 5
(`sec:Step5_larget` at BA, new mathematics; supervisor 1152 U-C5); report plus probe, no 1b.
Merged names only: the primed G pins (1155 C3; `BAGbEXPii` stands in for the diagonal, 2254 Q2), the MN0 spectral reading, the
range-uniform facts (1155 C1) and the C1-forbidden forms, the BA kernel `K = |M^{(B)}|²`, the one kernel and the BA flow
vocabulary, the inputs named by U-D (T2452), the band case-(iii) stack, and the BA instance data.  U6 (T2458) is not merged:
its `T2458_*` pins are not importable here; the probe copies them (prefix `T2459u6_`).  Every `example : Prop` is a shape
(not binding).
No proofs, no placeholders.
Run: lake env lean docs/tickets/checks/T2459-check.lean
-/
import RBM3D.Induction.PfStep5
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.GridDuhamelGen
import RBM3D.BA.Step2BA
import RBM3D.BA.GbEXPav
import RBM3D.BA.MReg
import RBM3D.BA.EKPins
import RBM3D.BA.EMn2BA
import RBM3D.BA.TwistPins
import RBM3D.BA.TwistStep

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the primed pins (1155 C3; 2254 Q2: `BAGbEXPii` in place of a primed diagonal pin, T2390d), all proved
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.baGbEXPii_holds
#check @RBM.BA.BAGbEXPij'
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.BAGbEXPav
#check @RBM.BA.baGbEXPav_holds
#check @RBM.BA.GreenCore_loopPrem
#check @RBM.BA.GreenCore_decayRHS
#check @RBM.BA.GreenCore_decayConcl
#check @RBM.BA.BAGiiGEX
#check @RBM.BA.BAGijGEX
#check @RBM.BA.FlowFM.indMax
-- superseded at G7 (not to be used by U5)
#check @RBM.BA.BAGbEXPij
-- MN0 spectral reading (`κ ≤ Im m`)
#check @RBM.BA.BAm_im_lower_window
#check @RBM.BA.BAbulk
-- range-uniform facts (1155 C1)
#check @RBM.BA.BAMres_fine_apply
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAMB_decay_large
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAp5s_A
#check @RBM.BA.BAp5s_S
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAReal
#check @RBM.BA.BASelf
#check @RBM.BA.BAdom
#check @RBM.BA.BAdom_real
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAm_self
#check @RBM.BA.BAoffDiag_scalar
#check @RBM.BA.BAProp5
#check @RBM.BA.BAProp5s
#check @RBM.BA.BAProp5to8
#check @RBM.BA.baProp5_holds
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.baProp5to8_holds
-- C1-forbidden forms (the `(Cλ)^{|a-b|}` form of `(Mbound_AO)`)
#check @RBM.BA.BAK_le_small
#check @RBM.BA.BAMB_upper_small
-- the BA kernel `K = |M^{(B)}|²` and the one-index factor (U5-1)
#check @RBM.BA.BAK
#check @RBM.BA.BAK_symm
#check @RBM.BA.BAK_diag
#check @RBM.BA.BAK_row_sum
#check @RBM.BA.BAK_offdiag_sum
#check @RBM.BA.BAK_off_le
#check @RBM.BA.BAK_le_decay
#check @RBM.BA.BAK_exp_moment_le
#check @RBM.BA.BAMss_norm_eq_BAK
#check @RBM.BA.BATheta_pm_eq
#check @RBM.BA.BATheta
#check @RBM.BA.BAMss
#check @RBM.BA.BAMB
#check @RBM.BA.BAm
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.BAuKer
#check @RBM.BA.BAUN
#check @RBM.BA.BAXi
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.BAuKer_convex
#check @RBM.BA.EKPins_norm_Theta_le
#check @RBM.BA.EKPins_norm_uKer_le
#check @RBM.BA.BAEKSumNdecay
-- the one kernel (U-C4) and the BA flow vocabulary
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAmF
#check @RBM.BA.Step2Mat
#check @RBM.BA.baStep2Mat
#check @RBM.BA.BAStep2
#check @RBM.BA.STStep2G
#check @RBM.BA.STMainIndG
#check @RBM.BA.twSteps
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_BAKsolve_form
#check @RBM.BA.BAKsolve
#check @RBM.BA.EMn2BA_K_two
#check @RBM.BA.baEMn2ExpHK
#check @RBM.Gauss.Sizes.emn2ExpHK
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.StoppedDuhamelNg
#check @RBM.BA.bandStep2_Ugen
-- inputs named by U-D (T2452): P1 (clause 4 of the grid pin at `m = 2`, a sub-stage T row), the TL grid martingale
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STGridRepNgL
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STeeUMg
#check @RBM.BA.baTwistGridMart_holds
-- the band case-(iii) stack (`3_5:2284-2383`; U5-0)
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.tailTD
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STDecayStrongU
#check @RBM.Gauss.Sizes.STStep5Concl
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STStep5R
#check @RBM.Gauss.Sizes.STStep5III
#check @RBM.Gauss.Sizes.STTailtoTail
#check @RBM.Gauss.Sizes.stTailtoTail_holds
#check @RBM.Gauss.Sizes.tailtoTailSq_kernelGen
#check @RBM.Gauss.Sizes.tailtoTailSq_kernel
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.stLemDecCalE_holds
#check @RBM.Gauss.Sizes.lemDecCalEPrec_kell
#check @RBM.Gauss.Sizes.STPfConcl
#check @RBM.Gauss.Sizes.STPfStep5
#check @RBM.Gauss.Sizes.PfStep5_walkConcl
#check @RBM.Gauss.Sizes.PfStep5_PTConcl
#check @RBM.Gauss.Sizes.PfStep5_PrecConcl
#check @RBM.Gauss.Sizes.stPfStep5_holds
#check @RBM.Gauss.Sizes.stStep5III_holds
#check @RBM.Gauss.Sizes.ST_step5_caseIII_of_pf
#check @RBM.Path.E2Hyp
#check @RBM.Path.E2HypDif
#check @RBM.Path.E2HypWG
#check @RBM.Path.lossE2
#check @RBM.Path.lossE2wG
#check @RBM.Green.GijGEXPTSwap
#check @RBM.Path.KellStarEv
#check @RBM.Path.kellStarEv
#check @RBM.Ind.stGridRepN_holds
#check @RBM.Gauss.Sizes.STGridRepNAt
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Ind.difRep_flow_bounds
#check @RBM.Ind.difRep2_norm_STeeM_le_N
-- the BA instance data (U5-7 (v); `sz0.lam n ≤ 1/64`, `t ≡ 1/2 < t₀`)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- U5-4: the conclusion of U5's BA target, i.e. U6's `T2458_STPfConclgL` (check `:254`) read at the BA carrier `baFMz` and the
law `seqP (sz.withLam 0)`; the target wraps it in `T2458_STIngR5gL` at the BA tuple (check `:459`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), STReg5III sz s t → ∀ D : ℝ, 0 < D →
  PrecL sz (Sizes.seqP (sz.withLam 0))
    (U := fun n => {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n})
    (fun n p ω => ‖(baFMz sz z).L n (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - (baFMz sz z).K n (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖)
    (fun n p _ => STtailTD sz n (p.1.1 : ℝ) D p.1.2.2)

/-- U5-1: the expected form of the BA kernel bound, at the flow carrier `baFMz` (coupling `BAflowLam0 = √t₀ · sz.lam`), in the
regime of `STReg5III`; the conclusion is that of U6's `T2458_STTailtoTailConclgL` (check `:281`). -/
example : Prop := ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧
  ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (D s t : ℝ), 0 ≤ s → s ≤ t → t ≤ BAflowT0 sz z n → sz.lam n ^ 2 ≤ 1 - t →
      ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ),
        (∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) s D (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) →
        ∀ a, ‖Step2Gen_UN (baFMz sz z) n σ s t A a‖ ≤
          Cc * tailTD d ((sz.W n : ℕ) : ℝ) t D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
            ((1 - s) / (1 - t)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- U5-1, drafting route: the weighted row sum of `K` (Ward `BAK_row_sum`, laziness `BAK_diag`, tails `BAK_off_le`), the BA
counterpart of `Σ_x S(x) e^{c|x|} ≤ 1 + g²/2` (`Induction/TailtoTail.lean:27`); the rate `μ` depends on `(d, Λ, κ)` only. -/
example : Prop := ∀ (d : ℕ) (Λ κ : ℝ), 2 ≤ d → 0 < Λ → 0 < κ → ∃ μ : ℝ, 0 < μ ∧
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
    ∀ a : Zd d L, ∑ b, BAK d L g E m a b * Real.exp (μ * (zdistD d L (a - b) : ℝ)) ≤ 1 + g ^ 2 / 2

/-- U5-1: the BA data of the flow (`BAflow_real`) and the coupling comparison `g₀ ≤ g` (`BAflowLam0 = √t₀ · sz.lam`). -/
example : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ,
  BAflowLam0 sz z n ≤ sz.lam n ∧
    BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)

/-- U5-6, dispatcher note (5): with `sz.lam ≥ 1` the regime (iii) is empty (`s ≥ 0`, `s < t`, `sz.lam² ≤ 1 - t`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ), (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, 1 ≤ sz.lam n) →
  ¬ STReg5III sz s t

/-- U5-3 input (U-D P1, a sub-stage T row): the grid pin at loop length 2 at the BA matrix carrier; U5 reads clause 4. -/
example : Prop := ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAtgL 3 2 C₀ (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

end RBM.BA

end
