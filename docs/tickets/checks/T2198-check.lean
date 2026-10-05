import RBM3D.Induction.Step5Pins
import RBM3D.Path.NetLift2
import RBM3D.Propagator.Deriv
import RBM3D.Propagator.Props4

/-!
# T2198 (S5-09a) check file: the realized control `J♯`, the Hölder-1/2 bounds (L1), the relative
continuity (L2) and the generic lift (G) of DECISIONS §64 (supervisor 2026-10-05-1550, answer 2.1)

Section 1: the vocabulary def `LemDecCalELip_Jsharp_voc` (the new file defines `LemDecCalELip_Jsharp` with
this body; script diff, name stripped): `J♯(n,u,ω) = max(1, max_{σ,a} STLK2 / STtailTD)`, the `sup'` written as in
the merged `STJhatM` (`Induction/Step2Defs.lean:81-86`).
Section 2: the pins (`def … _pin : Prop`), one per public theorem of the new file; each theorem's type is the
pin body with `LemDecCalELip_Jsharp_voc` read as `LemDecCalELip_Jsharp`.
Section 3: `#check` of every merged name the ticket cites.
Section 4: Prop-valued examples (statement shapes only).  Nothing here is proved.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Vocabulary: the realized control `J♯` (supervisor 1.3) -/

/-- `J♯(n,u,ω) := max(1, max_{σ ∈ {±}², a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| / T_{u,D}(|a₁-a₂|))` at the single time `u`. -/
noncomputable def LemDecCalELip_Jsharp_voc {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ)
    (ω : sz.SeqΩ) : ℝ :=
  max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      STLK2 sz n (E n) u p.1 p.2 ω / STtailTD sz n u D p.2))

/-! ## 2. The pins -/

/-- Target 1: the three defining properties of `J♯` (deterministic, every `n, u, ω`). -/
def LemDecCalELip_Jsharp_basic_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ),
    1 ≤ LemDecCalELip_Jsharp_voc sz E D n u ω ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STLK2 sz n (E n) u σ a ω ≤ LemDecCalELip_Jsharp_voc sz E D n u ω * STtailTD sz n u D a) ∧
    ∀ X : ℝ, 1 ≤ X →
      (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), STLK2 sz n (E n) u σ a ω ≤ X * STtailTD sz n u D a) →
      LemDecCalELip_Jsharp_voc sz E D n u ω ≤ X

/-- Target 2a (L1): `STLK2` is Hölder-1/2 in `u ∈ [s_n, t_n]` on the good event `contGood` of
`step2LocalNetLift`, with constant `N^C`. -/
def LemDecCalELip_LK2_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ), 3 ≤ d → sz.SizeTendsto → 0 < κ →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        |STLK2 sz n (E n) (u : ℝ) σ a ω - STLK2 sz n (E n) (u' : ℝ) σ a ω| ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|

/-- Target 2b (L1): `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}` (`STELKLK`), same premises. -/
def LemDecCalELip_ELKLK_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ), 3 ≤ d → sz.SizeTendsto → 0 < κ →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLK sz n (E n) (u : ℝ) σ a ω - STELKLK sz n (E n) (u' : ℝ) σ a ω‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|

/-- Target 2c (L1): `ℰ^{G̃,(2)}` (`STEGt`), same premises. -/
def LemDecCalELip_EGt_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ), 3 ≤ d → sz.SizeTendsto → 0 < κ →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STEGt sz n (E n) (u : ℝ) σ a ω - STEGt sz n (E n) (u' : ℝ) σ a ω‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|

/-- Target 2d (L1): `(ℰ⊗ℰ)^{M,(2)}_{u,σ,a,a'}` (`STee` at `m = 2`), every `a'`, same premises. -/
def LemDecCalELip_ee_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ), 3 ≤ d → sz.SizeTendsto → 0 < κ →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
        ‖STee sz n (E n) (u : ℝ) ω σ a a' - STee sz n (E n) (u' : ℝ) ω σ a a'‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|

/-- Target 3 (L2): relative continuity of the deterministic factors of `STLemDecCalEConcl`
(`Step5Pins.lean:164-186`) for `u, u' ≤ t < 1`, with `ρ = 1 + (1-t)⁻¹ |u - u'|`. -/
def LemDecCalELip_relcont_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (t u u' D : ℝ) (a : Fin 2 → Zd d (sz.L n)), t < 1 → u ≤ t → u' ≤ t →
    (1 - u')⁻¹ ≤ (1 + (1 - t)⁻¹ * |u - u'|) * (1 - u)⁻¹ ∧
    (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ≤
      (1 + (1 - t)⁻¹ * |u - u'|) * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ∧
    (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ (1 / 2 : ℝ) ≤
      (1 + (1 - t)⁻¹ * |u - u'|) * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) ∧
    STtailTD sz n u' D a ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 2 * STtailTD sz n u D a ∧
    STtailTD sz n u' D a ^ 2 ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 4 * STtailTD sz n u D a ^ 2

/-- Target 4: relative continuity of `J♯` in `u` on `contGood` (supervisor 1.3; from (L1) for `STLK2`,
(L2) for `STtailTD` and the floors `J♯ ≥ 1`, `STtailTD ≥ W^{-D}`). -/
def LemDecCalELip_Jsharp_rel_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (κ D : ℝ), 3 ≤ d → sz.SizeTendsto → 0 < κ → 0 < D →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ u u' : TimeIcc s t n,
        LemDecCalELip_Jsharp_voc sz E D n (u' : ℝ) ω ≤
          (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) *
            LemDecCalELip_Jsharp_voc sz E D n (u : ℝ) ω

/-- Target 5 (G): `PrecPT(ξ ≺ R₀ + J^m R)` + Hölder-1/2 of `ξ` and relative continuity of `J` on `contGood`
+ relative continuity of the deterministic `R₀, R` + floors (`J ≥ 1`, `R₀ ≥ 0`, `R ≥ N^{-CR}`) ⇒
`Prec(ξ ≺ R₀ + J^m R)`, by the merged `cont_core`.  `J` is any random control (in S5-09: `J♯`). -/
def LemDecCalELip_lift_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (V : ℕ → Type) [∀ n, Fintype (V n)]
    (ξ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ) (J : ℕ → ℝ → sz.SeqΩ → ℝ)
    (R₀ R : ∀ n, TimeIcc s t n × V n → ℝ) (m Cv C CR : ℝ),
    sz.SizeTendsto → (∀ n, s n ≤ t n) → (∀ n, t n - s n ≤ 1) → 0 ≤ m →
    (∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv) →
    (∀ n u ω, 1 ≤ J n u ω) → (∀ n p, 0 ≤ R₀ n p) →
    (∀ᶠ n in atTop, ∀ p, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ R n p) →
    (∀ᶠ n in atTop, ∀ (u u' : TimeIcc s t n) (v : V n),
      R₀ n (u', v) ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * R₀ n (u, v) ∧
      R n (u', v) ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * R n (u, v)) →
    (∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n, ∀ u u' : TimeIcc s t n,
      (∀ v : V n, |ξ n (u, v) ω - ξ n (u', v) ω| ≤
        ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) ∧
      J n (u' : ℝ) ω ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * J n (u : ℝ) ω) →
    PrecPT sz (U := fun n => TimeIcc s t n × V n) ξ
      (fun n p ω => R₀ n p + J n (p.1 : ℝ) ω ^ m * R n p) →
    Prec sz (U := fun n => TimeIcc s t n × V n) ξ
      (fun n p ω => R₀ n p + J n (p.1 : ℝ) ω ^ m * R n p)

end RBM.Gauss.Sizes

/-! ## 3. Every merged name the ticket cites -/

-- the pin and the Step-5 vocabulary (`Induction/Step5Pins`, c8e4f17; `Defs/Tail`)
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STEtermsMidConcl
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Step5Inst.sz0_reg5III
#check @RBM.tailTD
#check @RBM.tailTD_nonneg
-- the functionals (`Induction/Step2Defs` 86124dc, `Induction/Step34Pins` fc76526, `Induction/Defs` 64bdfd3)
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STJhatM
#check @RBM.Gauss.Sizes.STavgM
#check @RBM.Gauss.Sizes.STmsig
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STEEk
#check @RBM.Gauss.Sizes.STLI
#check @RBM.Gauss.Sizes.STeeLoop
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STKloop
-- the flow and the loops (`Gauss/FineModel` 0a873f1, `Loop/GLoopFlow` 868b3b4)
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqHflow_eq_smul
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Hflow
#check @RBM.Gauss.Hflow_isHermitian
#check @RBM.Gauss.Hflow_sub
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopL
#check @RBM.Gauss.Sizes.W_pos
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.Gauss.norm_matrix_entry_le_opNorm
#check @RBM.Gauss.norm_matrix_trace_le_card_mul
#check @RBM.Gauss.norm_Gsig_le_inv_eta
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.mE_im_pos
-- `𝒦^{(2)}` and the propagator (`Loop/KLTree` b06ff9b, `Propagator/Deriv`, `Propagator/Props4`, `Defs/Block`)
#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_two
#check @RBM.Theta
#check @RBM.Theta_sub_Theta
#check @RBM.norm_Theta_apply_le
#check @RBM.sum_norm_Theta_row_le
#check @RBM.norm_Theta_le
#check @RBM.SB
#check @RBM.sum_norm_SB_row
#check @RBM.norm_SB
-- the net-lift machinery (`Induction/ContinuityNet` 5b6cbc1, `Path/NetLift2` efeda82)
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_norm_Xmat_le
#check @RBM.Ind.ContinuityNet.cont_norm_blockMat_Xmat_le
#check @RBM.Ind.ContinuityNet.cont_green_flow_diff
#check @RBM.Ind.ContinuityNet.cont_eta_le_abs_im
#check @RBM.Ind.ContinuityNet.cont_abs_sqrt_sub_sqrt_le
#check @RBM.Ind.ContinuityNet.cont_norm_spectralZ_sub
#check @RBM.Ind.ContinuityNet.cont_norm_Eblk_le_one
#check @RBM.Ind.ContinuityNet.cont_Gres_true_eq_green
#check @RBM.Ind.ContinuityNet.cont_Gres_false_eq_green
#check @RBM.Ind.ContinuityNet.cont_inv_add_one_sub_ratio
#check @RBM.Ind.ContinuityNet.cont_sqrt_abs_le
#check @RBM.Ind.ContinuityNet.cont_bulk
#check @RBM.Ind.ContinuityNet.cont_gap
#check @RBM.Ind.Step2LocalNetLift
#check @RBM.Ind.step2LocalNetLift
#check @RBM.Gauss.Sizes.stNetLift2_holds
-- the `≺` layer (`Defs/StochDomAt`, 9e2b00f)
#check @RBM.StochDomAt
#check @RBM.StochDomAt.precomp_param
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.precPT_of_le
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst

/-! ## 4. Statement shapes (Prop-valued, no proof obligations) -/

-- the lifted first conclusion in S5-09 (T2193 Amend 1, step (N)): `ξ = ‖ℰ^{LK×LK}‖`, `R₀ = 0`, `m = 2`,
-- `R = (1-u)⁻¹ (W^d|1-u|)⁻¹ T_{u,D}`, `J = J♯`
example {d : ℕ} (sz : RBM.Gauss.Sizes d) (E s t : ℕ → ℝ) (D : ℝ) : Prop :=
  RBM.Gauss.Sizes.Prec sz (U := RBM.Gauss.Sizes.STIdx2 sz s t)
    (fun n p ω => ‖RBM.Gauss.Sizes.STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
    (fun n p ω => 0 + RBM.Gauss.Sizes.LemDecCalELip_Jsharp_voc sz E D n (p.1 : ℝ) ω ^ (2 : ℝ) *
      ((1 - (p.1 : ℝ))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ *
        RBM.Gauss.Sizes.STtailTD sz n (p.1 : ℝ) D p.2.2))

-- the premise `(1 - t_n)⁻¹ ≤ N` at the instance data `sz0`, `tInst ≡ 1/16` (every `n`)
example : Prop :=
  ∀ n : ℕ, (1 - RBM.Gauss.InductionDefsInst.tInst n)⁻¹ ≤
    ((RBM.Gauss.Sizes.size RBM.Gauss.SizesInst.sz0 n : ℕ) : ℝ)

-- the (L1) conclusion for `STLK2` at the instance data (`E ≡ 1/2`, `sInst ≡ 0`, `tInst ≡ 1/16`)
example : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in Filter.atTop,
    ∀ ω ∈ RBM.Ind.ContinuityNet.contGood RBM.Gauss.SizesInst.sz0 n,
      ∀ (u u' : RBM.Path.TimeIcc RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst n)
        (σ : Fin 2 → Bool) (a : Fin 2 → RBM.Zd 3 (RBM.Gauss.Sizes.L RBM.Gauss.SizesInst.sz0 n)),
        |RBM.Gauss.Sizes.STLK2 RBM.Gauss.SizesInst.sz0 n (1 / 2) (u : ℝ) σ a ω -
            RBM.Gauss.Sizes.STLK2 RBM.Gauss.SizesInst.sz0 n (1 / 2) (u' : ℝ) σ a ω| ≤
          ((RBM.Gauss.Sizes.size RBM.Gauss.SizesInst.sz0 n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|
