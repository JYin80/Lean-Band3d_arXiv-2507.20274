import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.TailtoTail
import RBM3D.Path.DifREP3

/-!
# T2209 (S5-10) check file: the pins of `Induction/PfStep5Alg` and the cited merged names

Section 1: the exact statements of targets 1-6 (`def … : Prop`); the theorem of target `i` must have
the body of the pin `PfStep5Alg_*_pin` (script diff, the binder line and the name stripped).
Section 2: `#check` of every merged name the ticket cites.
Section 3: Prop-valued examples (statement shapes at the merged instance data, no proofs).
No proofs, no `sorry`, no `by` (DECISIONS §17 check-file rules).
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Green

/-- **Target 1** (descent in `D`, `STPfConcl` docstring `Step5Pins.lean:195-201`): `T_{u,D'} ≤ T_{u,D}` for
`D ≤ D'` (`W ≥ 1`). -/
def PfStep5Alg_tailAnti_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (u D D' : ℝ) (a : Fin 2 → Zd d (sz.L n)), D ≤ D' →
    STtailTD sz n u D' a ≤ STtailTD sz n u D a

/-- **Target 2** (kernel sums, the `Ugen` form of `stTailtoTail_holds`; `EKsgn (mE E) σ` is
`fun i => mSigma E (σ i)`, `‖mE E‖ = 1` by `norm_mSigma`): for nonnegative weights `c j` and tensors
`ℰ j` dominated by `p j · T_{u_j,D}`, the weighted sum of `𝒰_{u_j,u_k,σ} ∘ ℰ_j` is dominated by
`Σ c_j p_j (C T_{u_k,D} + ((1-u_j)/(1-u_k))² W^{-D})`, `C` the constant of `STTailtoTail`. -/
def PfStep5Alg_ugenSum_pin (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E : ℝ), 0 < g → 0 < W → |E| ≤ 2 →
      ∀ (σ : Fin 2 → Bool) (k : ℕ) (u c p : ℕ → ℝ) (ℰ : ℕ → (Fin 2 → Zd d L) → ℂ),
        0 ≤ u 0 → (∀ j, u j ≤ u (j + 1)) → u k < 1 → g ^ 2 ≤ 1 - u k → (∀ j, 0 ≤ c j) →
        (∀ j, j < k → ∀ b, ‖ℰ j b‖ ≤ p j * tailTD d W (u j) D (zdistInf d L (b 0 - b 1) : ℝ)) →
        ∀ a, ‖∑ j ∈ Finset.range k, ((c j : ℝ) : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖ ≤
          ∑ j ∈ Finset.range k, c j * p j *
            (C * tailTD d W (u k) D (zdistInf d L (a 0 - a 1) : ℝ) +
              ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-D))

/-- **Target 3** (left Riemann sums of the increasing functions `(1-u)^{-2}`, `(1-u)^{-3/2}`, `(1-u)^{-1}`):
the time integrals `∫_s^{t'} (1-u)^{-2} du ≤ (1-t')^{-1}` etc. of Fable §4(3) on a grid. -/
def PfStep5Alg_riemann_pin : Prop :=
  ∀ (k : ℕ) (u : ℕ → ℝ), 0 ≤ u 0 → (∀ j, u j ≤ u (j + 1)) → u k < 1 →
    ∑ j ∈ Finset.range k, (u (j + 1) - u j) * (1 - u j)⁻¹ ^ 2 ≤ (1 - u k)⁻¹ ∧
    ∑ j ∈ Finset.range k, (u (j + 1) - u j) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ) ≤
      2 * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ) ∧
    ∑ j ∈ Finset.range k, (u (j + 1) - u j) * (1 - u j)⁻¹ ≤ Real.log ((1 - u 0) / (1 - u k))

/-- **Target 4** (the stopped control feeds S5-09's per-time good event): if the realized control is
`J♯(u) ≤ W^ε` (the stopping condition), the good event of `lemDecCalEPrec_good` at any control `J₀`
is inside the good event at the constant control `Jst ≡ W^ε` (conjunct 1 by `LemDecCalELip_Jsharp_basic`,
conjuncts 2-7 do not depend on `Jst`). -/
def PfStep5Alg_goodStop_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D ε τ' : ℝ) (J₀ : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 ≤ τ' →
    1 ≤ ((sz.size n : ℕ) : ℝ) →
    LemDecCalELip_Jsharp sz E D n u ω ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ω ∈ lemDecCalEPrec_good sz E D J₀ τ' n u →
    ω ∈ lemDecCalEPrec_good sz E D (fun m _ _ => ((sz.W m : ℕ) : ℝ) ^ ε) τ' n u

/-- **Target 5** (probability of the good event without the circular hypothesis): `lemDecCalEPrec_prob` at the
crude control `Jst n u D = W^D`, whose hypothesis `STLK2 ≺ W^D T` follows from `STLKU` at `k = 2`, `Bctl ≤ 1`
and `T ≥ W^{-D}` (`lemDecCalEPrec_tail_ge`). -/
def PfStep5Alg_goodProb_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E s t : ℕ → ℝ) (D : ℝ), sz.SizeTendsto →
    (∀ᶠ n in atTop, ∀ u : TimeIcc s t n, sz.Bctl n (u : ℝ) ≤ 1) →
    STLKU sz E s t → STLocalEntryU sz E s t → STAvgU sz E s t → STLmaxU sz E s t →
    GijGEXPTSwap sz E s t →
    ∀ τ' D₁ : ℝ, 0 < τ' → 0 < D₁ →
      ∀ᶠ n in atTop, ∀ u : TimeIcc s t n,
        sz.seqP (lemDecCalEPrec_good sz E D (fun m _ D' => ((sz.W m : ℕ) : ℝ) ^ D') τ' n (u : ℝ))ᶜ ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))

/-- **Target 6** (the closure, Fable §4(3) last line): for `0 < ε < 𝔡/4` and every `C ≥ 0` there is `τ > 0`
with `N^τ · C (1 + log W + W^{2ε} (ilambda² W^d)^{-1/4}) < W^ε` eventually (`(eq:WO)` gives
`(ilambda² W^d)^{-1/4} ≤ W^{-𝔡/2}`, `Bandwidth` gives `N^τ ≤ W^{τ/𝔠}`). -/
def PfStep5Alg_closure_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, sz.Admissible 𝔠 𝔡 → ∀ ε C : ℝ, 0 < ε → ε < 𝔡 / 4 → 0 ≤ C →
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ n in atTop,
      ((sz.size n : ℕ) : ℝ) ^ τ *
          (C * (1 + Real.log ((sz.W n : ℕ) : ℝ) +
            ((sz.W n : ℕ) : ℝ) ^ (2 * ε) * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ)))) <
        ((sz.W n : ℕ) : ℝ) ^ ε

end RBM.Gauss.Sizes

/-! ## 2. Merged names cited by the ticket -/

-- the pins of Step 5, case (iii) (`Induction/Step5Pins.lean`, d7da51e)
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STTailtoTail
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STPfConcl
#check @RBM.Gauss.Sizes.STPfStep5
#check @RBM.Gauss.Step5Inst.inst_lemDecCalE
#check @RBM.Gauss.Step5Inst.inst_pfStep5
#check @RBM.Gauss.Step5Inst.sz0_reg5III
-- S5-04 (`Induction/TailtoTail.lean`, 37f3a22)
#check @RBM.Gauss.Sizes.stTailtoTail_holds
-- S5-09 (`Induction/LemDecCalEPrec.lean`, d7da51e)
#check @RBM.Gauss.Sizes.stLemDecCalE_holds
#check @RBM.Gauss.Sizes.lemDecCalEPrec_good
#check @RBM.Gauss.Sizes.lemDecCalEPrec_prob
#check @RBM.Gauss.Sizes.lemDecCalEPrec_Bounds
#check @RBM.Gauss.Sizes.lemDecCalEPrec_goodDet
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R1
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R2₀
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R2
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R3₀
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R3
#check @RBM.Gauss.Sizes.lemDecCalEPrec_gij
#check @RBM.Gauss.Sizes.lemDecCalEPrec_kell
#check @RBM.Gauss.Sizes.lemDecCalEPrec_lossWG_eventually
#check @RBM.Gauss.Sizes.lemDecCalEPrec_QW
#check @RBM.Gauss.Sizes.lemDecCalEPrec_floor
#check @RBM.Gauss.Sizes.lemDecCalEPrec_tail_ge
#check @RBM.Gauss.Sizes.lemDecCalEPrec_Bctl_le
#check @RBM.Gauss.Sizes.lemDecCalEPrec_perTime_bounds
-- S5-09a (`Induction/LemDecCalELip.lean`, e4126a2)
#check @RBM.Gauss.Sizes.LemDecCalELip_Jsharp
#check @RBM.Gauss.Sizes.LemDecCalELip_Jsharp_basic
#check @RBM.Gauss.Sizes.LemDecCalELip_tail_pos
#check @RBM.Gauss.Sizes.LemDecCalELip_LK2
#check @RBM.Gauss.Sizes.LemDecCalELip_lift
-- S5-02 (`Induction/Step5Kit.lean`, 85e43db)
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_Bctl_le_one
#check @RBM.Gauss.Sizes.st5_t_lt_one
-- Steps 2-4 conclusions (`Induction/Step34Pins.lean`, fc76526; `Induction/Defs.lean`, 64bdfd3)
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STDecayStrong
-- kernels and grid (S5-11's material; `Induction/GridDuhamelN.lean` 2ebee73, `Induction/Step2Defs.lean` 86124dc,
-- `Path/Walk.lean` ddf5f74, `Path/DifREP3.lean` b3c37aa)
#check @RBM.Ind.Ugen
#check @RBM.Ind.StoppedAzumaN
#check @RBM.Ind.stGridRepN_holds
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.UN
#check @RBM.EKsgn
#check @RBM.norm_mSigma
#check @RBM.tailTD
#check @RBM.Green.GijGEXPTSwap

/-! ## 3. Statement shapes at the merged instance data (Prop-valued, no proofs) -/

example : Prop := RBM.Gauss.Sizes.PfStep5Alg_tailAnti_pin RBM.Gauss.SizesInst.sz0
example : Prop := RBM.Gauss.Sizes.PfStep5Alg_ugenSum_pin 3
example : Prop := RBM.Gauss.Sizes.PfStep5Alg_riemann_pin
example : Prop := RBM.Gauss.Sizes.PfStep5Alg_goodStop_pin RBM.Gauss.SizesInst.sz0
example : Prop := RBM.Gauss.Sizes.PfStep5Alg_goodProb_pin RBM.Gauss.SizesInst.sz0
example : Prop := RBM.Gauss.Sizes.PfStep5Alg_closure_pin RBM.Gauss.SizesInst.sz0
example : Prop := RBM.Gauss.Sizes.STPfStep5 3
