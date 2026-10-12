/-
Release check for T2481 (dispatcher V3, Mon Oct 12 23:12 UTC 2026; DECISIONS §280).  U U5a = `BA/Step5IIIKer` (+ named second file
`BA/Step5IIIKer2`): the kernel part of BA case (iii) of Step 5 (design `docs/reports/T2459-design.md` (d) `:254`, U5-1
`:163-171`; probe `t/T2459:RBM3D/Probe/T2459Pins.lean` `:58-91`, `:240-276`, never merged).  Contents: the weighted row sum of
`K = |M^{(B)}|²`; `TailtoTail` `(neiwuj)` on the one kernel `Step2Gen_UN` at `baFM` (U6's `STTailtoTailConclgL`); its reading
at the flow; the Θ-level far field from the K-level `baEMn2ExpHK`; the `uKer`-level far field for all four charge pairs; the
BA `tailtoTailSq` with premises (H1)-(H3) and its `STeeUMg` reading (the weight of clause 4 of `STGridRepNAtgL d 2`).
Coupling (supervisor 1457 UBA-C1, DECISIONS §269 (2); R1 = supervisor 1752 TN-C1, DECISIONS §273 (1)): the regime reads
`sz.lam`, the kernel reads `lam0` (at the flow `g₀ = BAflowLam0`); the statements carry T2459's per-index guarded form
`0 < lam0 n`, `lam0 n ≤ sz.lam n`, which follows from R1
`∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (shape lines in Part 2); the `A` of
UBA-C1 does not enter.  No grid statement (TN-C4): no `STGridRepNgL` below.
Part 1: merged names.  Part 2: the target statements as `Prop` values (prefix `T2481_`): `T2481_Lam0LeLam`, `T2481_BAweighted`,
`T2481_BAKernel`, `T2481_ThetaFar` (the T2459 probe texts, verbatim up to the prefix and binder style; binding);
`T2481_KernelAtFlow` (the conclusion of the probe's `T2459_kernel_at_flow` with `ε 𝔠` after `∃ Cc`, every `d ≥ 3`; binding);
`T2481_UKerFar`, `T2481_BATailSq`, `T2481_BATailSqQV` (new here; binding, an equivalent restatement only if the 1a reports it);
then shapes (not binding): R1 at BA, the per-index consequence, instances, the U5d reading.  Part 3: the band twins and the
U6 / U4s1 names around them (unchanged; not edited).
Merged names only.  No proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2481-check.lean
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.GridRepTailGen
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.KKernel
import RBM3D.BA.KBase
import RBM3D.BA.EKPins
import RBM3D.BA.CombesThomas
import RBM3D.BA.Prop5Short
import RBM3D.BA.Prop6Path
import RBM3D.BA.GreenStab
import RBM3D.BA.GreenSchur
import RBM3D.BA.EMn2BA
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistGrid
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.GridMartBA
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.EMn2Exp1
import RBM3D.Induction.TailtoTail
import RBM3D.Induction.TailtoTailSq
import RBM3D.Path.DifREP2

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U6 (`Chain/Step5Gen`, T2458): the TailtoTail conclusion and pin shape, the targets of U5, the case-(iii) regime
#check @RBM.BA.STTailtoTailConclgL
#check @RBM.BA.STTailtoTailgL'
#check @RBM.BA.STPfStep5gL
#check @RBM.BA.STStep5IIIgL
#check @RBM.BA.STIngR5gL
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.tailTD
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.Gauss.zdistInf
#check @RBM.zdistD
#check @RBM.expC
#check @RBM.Gauss.Sizes.emn2ExpEllStar
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
-- the one kernel over a carrier (T8b) and its BA reading (stage E, E-C1)
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.STeeMg
#check @RBM.BA.STeeUMg
#check @RBM.BA.GridRepTailGen_STeeUMg_eq
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
-- the BA carrier and flow (`BA/FlowPins`), the real-axis data, the coupling `g₀ = √t₀ g`
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAmF
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAReal
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.TwistStep2_T0_ge
#check @RBM.BA.EMn2BA_T0_lt_one
-- the kernel `K = |M^{(B)}|²` (K1-K3 of the design) and its constants (`BA/KKernel`, `CombesThomas`, `Prop5Short`)
#check @RBM.BA.BAK
#check @RBM.BA.BAK_diag
#check @RBM.BA.BAK_row_sum
#check @RBM.BA.BAK_offdiag_sum
#check @RBM.BA.BAMss_norm_eq_BAK
#check @RBM.BA.BAMss_pm_eq
#check @RBM.BA.BATheta_pm_eq
#check @RBM.BA.BAK_off_le
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAp5s_A
#check @RBM.BA.BAp5s_S
#check @RBM.BA.BAsum_exp_decay_le
-- Θ, `uKer`, rows, decay (`BA/MFixedPoint`, `KBase`, `EKPins`, `EMn2BA`, `Prop6Path`, `GreenStab`)
#check @RBM.BA.BATheta
#check @RBM.BA.BAMss
#check @RBM.BA.BAMB
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.BAuKer
#check @RBM.BA.BAUN
#check @RBM.BA.BAuKer_convex
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.baEKSumNdecay_holds
#check @RBM.BA.baTheta_row_le
#check @RBM.BA.baTheta_col_le
#check @RBM.BA.BAProp5
#check @RBM.BA.baProp5_holds
#check @RBM.BA.baP8_BATheta_shift
#check @RBM.BA.baProp5s_of_real
#check @RBM.BA.baTheta_weighted_l1
-- the K-level far field and the identity behind the Θ-level one
#check @RBM.Gauss.Sizes.emn2ExpHK
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.EMn2BA_K_two
-- merged, not read in U5a (inputs of U5d): the semigroup, P1, P1b
#check @RBM.BA.BAuKerSemigroup_holds
#check @RBM.BA.baGridMart_holds
#check @RBM.BA.baGridRepNAt2_holds
-- instance data (`sz0`, `zSeq`, `flow_sz0`, `half_lt_t0`)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.BA.FlowPinsInst.sz0_lam_pos

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (content binding; the probe's `T2459_lam0_le_lam`, `:58`): the first conjunct of UBA-C1 at the flow, guarded:
where `g₀ = BAflowLam0 > 0`, `g₀ ≤ g = sz.lam` (from `TwistStep2_lam0_sq`, `BA/TwistStep2.lean:740`). -/
def T2481_Lam0LeLam (d : ℕ) : Prop :=
  ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ n : ℕ, 0 < BAflowLam0 sz z n → BAflowLam0 sz z n ≤ sz.lam n

/-- **Target 2** (content binding; the probe's `T2459_BAweighted`, `:69`, verbatim): the weighted row sum
`t Σ_b K_{ab} e^{μ|a-b|_1} ≤ (1+t)/2`, `μ = μ(d, 𝔡⁻¹, κ)`, for `g₀ ≤ g` and `g² ≤ 1 - t` (design U5-1 step 1, `:165`). -/
def T2481_BAweighted (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ μ : ℝ, 0 < μ ∧ ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ),
    BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
    0 ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t → ∀ a : Zd d (sz.L n),
      t * ∑ b, BAK d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) a b * Real.exp (μ * (zdistD d (sz.L n) (a - b) : ℝ)) ≤ (1 + t) / 2

/-- **Target 3** (content binding; the probe's `T2459_BAKernel`, `:78`, verbatim): `(neiwuj)` (`3_5:2344-2362`) on the one kernel
`Step2Gen_UN` at `baFM`, `Cc = Cc(d, 𝔡⁻¹, κ)`; `lam0 ≤ sz.lam` replaces `‖m‖ = 1`; conclusion U6's `STTailtoTailConclgL`
(`Chain/Step5Gen.lean:169`). -/
def T2481_BAKernel (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D s t : ℝ),
    BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
    0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t → STTailtoTailConclgL (baFM sz lam0 E) n Cc D s t

/-- **Target 3, at the flow** (content binding; the conclusion of the probe's `T2459_kernel_at_flow`, `:84`, for every `d ≥ 3`,
with `ε 𝔠` after `∃ Cc`): `g₀ = BAflowLam0`, eventually in `n`; regime `sz.lam² ≤ 1 - t` at `g = sz.lam`. -/
def T2481_KernelAtFlow (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, ∀ D s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
      sz.lam n ^ 2 ≤ 1 - t → STTailtoTailConclgL (baFMz sz z) n Cc D s t

/-- **Target 4 (a)** (content binding; the statement of the probe's `T2459_Theta_far`, `:242`): the Θ-level far field of the
mixed charges `(s, !s)` beyond `ℓ*_t`, from `BATheta_resolvent` (`BA/KBase.lean:330`), `EMn2BA_K_two` (`BA/EMn2BA.lean:624`) and
`baEMn2ExpHK` (`:637`) at `D + d`. -/
def T2481_ThetaFar (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ D : ℝ, 0 < D →
      ∀ᶠ n in atTop, ∀ (x x' : Zd d (sz.L n)) (s : Bool), x ≠ x' → emn2ExpEllStar sz n (t n) ≤ (zdistInf d (sz.L n) (x - x') : ℝ) →
        ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) s (!s) x x'‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **Target 4 (b)** (content binding, new): the `uKer`-level far field at the flow, all four charge pairs `(τ, τ')`, uniformly in
`0 ≤ v ≤ w ≤ t₀` with `sz.lam² ≤ 1 - w`, beyond `ℓ* = (log W)^{3/2}`; this is premise (H3) of targets 5 at the flow. -/
def T2481_UKerFar (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ D : ℝ, 0 < D →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ BAflowT0 sz z n → sz.lam n ^ 2 ≤ 1 - w →
        ∀ (τ τ' : Bool) (x y : Zd d (sz.L n)),
          Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
          ‖Step2Gen_uKer (baFMz sz z) n τ τ' v w x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **Target 5** (content binding, new; band twin `tailtoTailSq_kernelGen`, `Induction/TailtoTailSq.lean:906`): the squared-profile
`TailtoTail` for a 4-index tensor `X` on the BA kernel, near cut `2ℓ*` (T2459b), `ρ = (1-v)/(1-w)`, `Cq = Cq(d, 𝔡⁻¹, κ)`.
(H1) near bound `‖X(b,b')‖ ≤ p T_{v,D}(|b₀-b₁|)²` where `max_i |b_i - b'_i| ≤ 2ℓ*`; (H2) crude bound `‖X‖ ≤ Y`;
(H3) `‖uKer_{v,w}(x,y)‖ ≤ W^{-D₂}` beyond `ℓ*`, every charge pair (target 4 (b) at the flow). -/
def T2481_BATailSq (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cq : ℝ, 0 < Cq ∧
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D D₂ v w p Y : ℝ),
      BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
      0 ≤ v → v ≤ w → w < 1 → sz.lam n ^ 2 ≤ 1 - w → 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ p → 0 ≤ Y →
      ∀ (σ : Fin 2 → Bool) (X : (Fin 2 → Zd d (sz.L n)) → (Fin 2 → Zd d (sz.L n)) → ℂ),
        (∀ b b' : Fin 2 → Zd d (sz.L n),
          (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
          ‖X b b'‖ ≤ p * STtailTD sz n v D b ^ 2) →
        (∀ b b' : Fin 2 → Zd d (sz.L n), ‖X b b'‖ ≤ Y) →
        (∀ (τ τ' : Bool) (x y : Zd d (sz.L n)),
          Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
          ‖Step2Gen_uKer (baFM sz lam0 E) n τ τ' v w x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) →
        ∀ a : Fin 2 → Zd d (sz.L n),
          ‖∑ b : Fin 2 → Zd d (sz.L n), ∑ b' : Fin 2 → Zd d (sz.L n),
              (∏ i, Step2Gen_uKer (baFM sz lam0 E) n (σ i) (σ (finRotate 2 i)) v w (a i) (b i)) *
                (∏ i, Step2Gen_uKer (baFM sz lam0 E) n (!σ i) (!σ (finRotate 2 i)) v w (a i) (b' i)) * X b b'‖ ≤
            Cq * p * (STtailTD sz n w D a ^ 2 + ((1 - v) / (1 - w)) ^ 4 * (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
              4 * Y * ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂)

/-- **Target 5, the QV reading** (content binding, new; band twin `tailtoTailSq_kernel`, `:932`): target 5 at
`X = STeeMg (baStep2Mat sz lam0 E) n v H σ`, the left side being `STeeUMg` (`Chain/Step2Gen.lean:983`), the weight of clause 4. -/
def T2481_BATailSqQV (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cq : ℝ, 0 < Cq ∧
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D D₂ v w p Y : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool),
      BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
      0 ≤ v → v ≤ w → w < 1 → sz.lam n ^ 2 ≤ 1 - w → 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ p → 0 ≤ Y →
      (∀ b b' : Fin 2 → Zd d (sz.L n),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat sz lam0 E) n v H σ b b'‖ ≤ p * STtailTD sz n v D b ^ 2) →
      (∀ b b' : Fin 2 → Zd d (sz.L n), ‖STeeMg (baStep2Mat sz lam0 E) n v H σ b b'‖ ≤ Y) →
      (∀ (τ τ' : Bool) (x y : Zd d (sz.L n)),
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
        ‖Step2Gen_uKer (baFM sz lam0 E) n τ τ' v w x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        ‖STeeUMg (baStep2Mat sz lam0 E) n v w H σ a‖ ≤
          Cq * p * (STtailTD sz n w D a ^ 2 + ((1 - v) / (1 - w)) ^ 4 * (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
            4 * Y * ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂)

/-! ### Shapes (not binding): UBA-C1 -/

/-- R1 (the one comparison text, TN-C1, DECISIONS §273 (1)) at BA: `gK = BAflowLam0 sz z`, `A = (κ+1)/κ`, every `n`
(`0 ≤ √t₀ · lam²` and `TwistStep2_lam0_sq`). -/
example : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ), 0 < κ → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
    sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2

/-- The per-index consequence (the three-line step of §273 (1); a private copy per row): R1 at `n` and `0 < gK n` give the
guarded form that targets 1-3, 5 carry. -/
example : Prop := ∀ g l A : ℝ, (0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) → 0 < g → 0 < l ∧ g ≤ l

/-- The kernel part reads only `g₀² ≤ g² ≤ 1 - t` (the second conjunct of R1 with the regime), never `A`. -/
example : Prop := ∀ g₀ g t : ℝ, g₀ ^ 2 ≤ g ^ 2 → g ^ 2 ≤ 1 - t → g₀ ^ 2 ≤ 1 - t

/-! ### Shapes (not binding): instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`,
`s ≡ 1/10 < t ≡ 1/2 < t₀` (`half_lt_t0`; regime `sz0.lam² ≤ 1/2`) -/

/-- Target 2 at the instance (the probe's example `:346`). -/
example : Prop := T2481_BAweighted 3 →
  ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t < 1 → SizesInst.sz0.lam n ^ 2 ≤ 1 - t →
    ∀ a : Zd 3 (SizesInst.sz0.L n), t * ∑ b, BAK 3 (SizesInst.sz0.L n) (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq n)
      (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq n) (BAmF SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq)
        (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n) a b * Real.exp (μ * (zdistD 3 (SizesInst.sz0.L n) (a - b) : ℝ)) ≤ (1 + t) / 2

/-- Target 3 at the instance (the probe's example `:357`). -/
example : Prop := T2481_KernelAtFlow 3 →
  ∃ Cc : ℝ, 0 < Cc ∧ ∀ᶠ n in atTop, ∀ D : ℝ, STTailtoTailConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n Cc D (1 / 10) (1 / 2)

/-- Target 4 (a) at the instance, `t ≡ 1/2`, `D = 1` (the probe's example `:384`). -/
example : Prop := T2481_ThetaFar 3 →
  ∀ᶠ n in atTop, ∀ (x x' : Zd 3 (SizesInst.sz0.L n)) (s : Bool), x ≠ x' →
    emn2ExpEllStar SizesInst.sz0 n (1 / 2) ≤ (zdistInf 3 (SizesInst.sz0.L n) (x - x') : ℝ) →
    ‖BATheta 3 (SizesInst.sz0.L n) (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq n) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq n)
      (BAmF SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n)
      (1 / 2) s (!s) x x'‖ ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))

/-- Target 4 (b) at the instance, `v = 1/10`, `w = 1/2`, `D = 1`, every charge pair. -/
example : Prop := T2481_UKerFar 3 →
  ∀ᶠ n in atTop, ∀ (τ τ' : Bool) (x y : Zd 3 (SizesInst.sz0.L n)),
    Real.log ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf 3 (SizesInst.sz0.L n) (x - y) : ℝ) →
    ‖Step2Gen_uKer (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n τ τ' (1 / 10) (1 / 2) x y‖ ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))

/-- Targets 5 (QV) and 4 (b) composed at the instance (the U5d reading): (H3) discharged eventually, (H1)-(H2) stay premises
(their sources are U5b's `dif` bound through U5c's good event, and U5d's crude bound); `D₂ = D`. -/
example : Prop := T2481_BATailSqQV 3 → T2481_UKerFar 3 →
  ∃ Cq : ℝ, 0 < Cq ∧ ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
    ∀ (p Y : ℝ) (H : Matrix (Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) (Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) ℂ)
      (σ : Fin 2 → Bool), 0 ≤ p → 0 ≤ Y →
      (∀ b b' : Fin 2 → Zd 3 (SizesInst.sz0.L n),
        (∀ i : Fin 2, (zdistInf 3 (SizesInst.sz0.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq))
            n (1 / 10) H σ b b'‖ ≤ p * STtailTD SizesInst.sz0 n (1 / 10) D b ^ 2) →
      (∀ b b' : Fin 2 → Zd 3 (SizesInst.sz0.L n),
        ‖STeeMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq))
            n (1 / 10) H σ b b'‖ ≤ Y) →
      ∀ a : Fin 2 → Zd 3 (SizesInst.sz0.L n),
        ‖STeeUMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq))
            n (1 / 10) (1 / 2) H σ a‖ ≤
          Cq * p * (STtailTD SizesInst.sz0 n (1 / 2) D a ^ 2 +
              ((1 - 1 / 10) / (1 - 1 / 2) : ℝ) ^ 4 * (((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
            4 * Y * ((SizesInst.sz0.L n : ℕ) : ℝ) ^ 3 * ((1 - 1 / 10) / (1 - 1 / 2) : ℝ) ^ 3 * ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-D)

/-- Not a target (T2459d, design `:170`; `docs/tickets/checks/T2458-check.lean:462`): the free-`lam0` shape of U6 at BA,
expected false; U5a states the kernel at `lam0 ≤ sz.lam` only. -/
example : Prop := ∀ lam0 : ℕ → ℝ, STTailtoTailgL' 3 (fun sz E => baFM sz lam0 E)

end RBM.BA

/-! ## Part 3: band twins and the generic names around them (unchanged; not edited) -/

#check @RBM.Gauss.Sizes.STTailtoTail
#check @RBM.Gauss.Sizes.stTailtoTail_holds
#check @RBM.Gauss.Sizes.tailtoTailSq_kernelGen
#check @RBM.Gauss.Sizes.tailtoTailSq_kernel
#check @RBM.Ind.difRep2_norm_STeeM_le_N
#check @RBM.BA.stTailtoTailgL'_holds_band
#check @RBM.BA.Step5KerGen_uKer_eq
#check @RBM.BA.Step5KerGen_ThDecay
#check @RBM.BA.step5KerGen_profile_holds
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.ST_step5_caseIII_of_pfgL

end
