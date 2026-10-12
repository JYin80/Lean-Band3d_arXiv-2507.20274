/-
Release check for T2479 (dispatcher V3, Mon Oct 12 22:25 UTC 2026; DECISIONS §279).  U X1b (ST side, route G): the CLT layer of Step 5 case (i),
part b: the proof of X1a's merged far pin `STCltFargL` (`Chain/CltGen.lean:166-170`) over the carrier, in the new files
`Evolution/CltMoments2G.lean`, `Evolution/MeanFarG.lean`, `Evolution/CltFarG.lean`; the band files `Evolution/CltMoments1`,
`CltMoments2`, `MeanFar`, `CltFar` are not edited (outside the certificate lane); supervisor 1152 X1-C1 … X1-C5, 1155 C9.
Part 1: merged names (X1a's pins and inputs, carrier, U4s1, band pins and instance data, propagator facts, BA producers).
Part 2: the target statements as Prop values (prefix `T2479_`).  Binding: `T2479_FarPin` (the merged pin, every `d`),
`T2479_BandFar` (band bridge), the conclusions of `T2479_ThPropsBand`, `T2479_KPropsBand` (their premise lists are
proposals; a change is reported).  Proposal (not binding): `T2479_MeanFarg`.  Then shapes (not binding): the BA reading
(U4-BA, C9) and the UBA-C1 literal (R1, DECISIONS §273 (1)).
Part 3 (G1): the 97 public declarations of the four band files, unchanged; the auditor adds `example : <statement> := <name>`.
Merged names only.  No proofs, no placeholders.
Run: lake env lean docs/tickets/checks/T2479-check.lean
-/
import RBM3D.Evolution.CltFar
import RBM3D.Induction.IniTermI
import RBM3D.Chain.CltGen
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Step2Kern
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Prop6Hold
import RBM3D.Propagator.Props4
import RBM3D.Loop.KLTree
import RBM3D.Green.Pins
import RBM3D.Gauss.BlockAnderson
import RBM3D.BA.FlowPins
import RBM3D.BA.Prop6Path
import RBM3D.BA.TwistStep2
import RBM3D.BA.GreenSchur
import RBM3D.BA.KSolve
import RBM3D.BA.EMn2BA
import RBM3D.BA.CombesThomas
import RBM3D.BA.GreenOff
import RBM3D.BA.KBase
import RBM3D.BA.MFixedPoint
import RBM3D.BA.Ward

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- X1a's vocabulary and pins (`Chain/CltGen.lean`; X1-C4: imported, never restated)
#check @RBM.BA.STThg
#check @RBM.BA.STfFarg
#check @RBM.BA.STCltFarConclgL
#check @RBM.BA.STcltBg
#check @RBM.BA.STcltXg
#check @RBM.BA.STCltIsoConclgL
#check @RBM.BA.STExpInvgL
#check @RBM.BA.CltRepg
#check @RBM.BA.STGijDecgL
#check @RBM.BA.STKfargL
#check @RBM.BA.STMfarg
#check @RBM.BA.STThPropsg
#check @RBM.BA.STKpropsg
#check @RBM.BA.CltInvg
#check @RBM.BA.HCltOf
#check @RBM.BA.STCltIsogL
#check @RBM.BA.STCltFargL
#check @RBM.BA.cltRepg_band
#check @RBM.BA.bandFM_M_le
#check @RBM.BA.bandFM_STMfarg
#check @RBM.BA.bandFM_STThg
#check @RBM.BA.bandFM_STfFarg
#check @RBM.BA.bandFM_STCltFarConcl
#check @RBM.BA.bandFM_STCltIsoConcl
#check @RBM.BA.bandFM_STExpInv
-- X1a's results that targets 6, 8, 9 read
#check @RBM.BA.stCltIsogL_holds
#check @RBM.BA.stExpInvgL_of_rep
#check @RBM.BA.stExpInvgL_band
#check @RBM.BA.stFarEntryAtLoggL
#check @RBM.BA.bandFM_STGijDecgL_of_three_le
#check @RBM.BA.bandFM_STKfargL
#check @RBM.Gauss.Step5Inst.cltGood_hCltOf_szCL
#check @RBM.Evol.cltCk_facts
#check @RBM.Evol.cltStepOf
#check @RBM.Gauss.Sizes.stCltIso_holds
#check @RBM.Gauss.Sizes.stExpInv_holds
-- the carrier, T8 / T8b (U-C4: one propagator), U6, U4s1
#check @RBM.BA.FlowFM
#check @RBM.BA.bandFM
#check @RBM.BA.PrecL
#check @RBM.BA.Step2Gen_Theta
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Kern_Mss_band
#check @RBM.BA.STLocalEntryUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.bandFM_STStep2Concl
#check @RBM.BA.STIngR5gL
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.step5CasesGen_flowFacts_band
-- U4s1b kernel facts: not read in X1b (kernel level at `gK`; X1b reads `STThPropsg`, T2462-prove F6)
#check @RBM.BA.Step5KerGen_ThDecay
#check @RBM.BA.step5KerGen_profile_holds
-- the band pins, the vocabulary they read, the size-level helpers, the instance data
#check @RBM.Gauss.Sizes.STCltFar
#check @RBM.Gauss.Sizes.STCltFarConcl
#check @RBM.Gauss.Sizes.STfFar
#check @RBM.Gauss.Sizes.STcltB
#check @RBM.Gauss.Sizes.STcltX
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STCltIso
#check @RBM.Gauss.Sizes.STExpInv
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.st5_eventually_A_ge_one
#check @RBM.Gauss.Sizes.st5_zdistInf_le
#check @RBM.Gauss.Sizes.stCltFar_uniform
#check @RBM.Gauss.Sizes.STCltFarUConcl
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.zCL
#check @RBM.Gauss.Step5Inst.sCL
#check @RBM.Gauss.Step5Inst.tCL
#check @RBM.Gauss.Step5Inst.inst_cltFar
#check @RBM.Gauss.Step5Inst.szCL_cltFar_index_nonempty
#check @RBM.Gauss.Step5Inst.szCL_reg5I
#check @RBM.Gauss.Step5Inst.szCL_admissible
-- spectral reading (X1-C1) and the propagator facts behind target 7 (X1-C2: band side only)
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.etaT_eq_etaOf
#check @RBM.Gauss.zdistInf
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.norm_mul_mSigma_lt_one
#check @RBM.Theta
#check @RBM.PropSpin
#check @RBM.Theta_apply_add_right_of_three_le
#check @RBM.Theta_transpose_of_three_le
#check @RBM.prop5Decay_holds
#check @RBM.prop6Diff1_holds
#check @RBM.prop7Diff2_holds
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.zdistD
#check @RBM.Loop.KLK_two
#check @RBM.Green.v3_premises_of_stFlow
-- BA readings and producers (U4-BA; statement level here)
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.Gauss.PsiI
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.TwistStep2_T0_ge
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAKsolve
#check @RBM.BA.Step2Kern_BAKsolve_form
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.baPropM_holds
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.BATheta
#check @RBM.BA.baP8_BATheta_shift
#check @RBM.BA.BATheta_isSymm
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.baOffDiag_holds

/-! ## Part 2: the target statements (binding where marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 6** (binding; X1-C4): the merged pin `STCltFargL` (`Chain/CltGen.lean:166-170`, premises `HCltOf`, `STReg5I`,
`STThPropsg`, `STKpropsg`, `STExpInvgL`), proved for every `d` (`stCltFargL_holds`). -/
def T2479_FarPin : Prop := ∀ d : ℕ, STCltFargL d

/-- **Target 7a** (conclusion binding; premise list a proposal): the band producer of `STThPropsg` (`bandFM_STThPropsg`):
shift, symmetry, `(prop:ThfadC)`, `(prop:BD1)`, `(prop:BD2)` of the band propagator at `sz.lam` (band coupling `gK = sz.lam`,
`A = 1`; no comparison text).  Route: `bandFM_STThg`, `Theta_apply_add_right_of_three_le`, `Theta_transpose_of_three_le`,
`prop5Decay_holds`, `prop6Diff1_holds`, `prop7Diff2_holds` at `Λ = 𝔡⁻¹`, `c = 1/2`, `κ' = min κ (1/2)`. -/
def T2479_ThPropsBand : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔡 : ℝ) (E : ℕ → ℝ), 3 ≤ d → 0 < κ → 0 < 𝔡 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → STThPropsg (bandFM sz E)

/-- **Target 7b** (conclusion binding; premise list a proposal): the band producer of `STKpropsg` (`bandFM_STKpropsg`):
invariance of `𝒦^{(2)}` (mixed charges, every `n`, `0 ≤ t < 1`) and `‖𝒦^{(2)}_{s}‖ ≤ c₁ / A` (regime from `STReg5I`).
Route: `KLK_two`, `Θ` invariance, the merged-private pattern `cltFar_K_le` (`CltFar:681-700`). -/
def T2479_KPropsBand : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔡 : ℝ) (E s t : ℕ → ℝ), 3 ≤ d → 0 < κ → 0 < 𝔡 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STReg5I sz s t →
    STKpropsg (bandFM sz E) s

/-- **Target 8** (binding): the band bridge `stCltFar_of_gL`: the generic pin gives the band pin (`HCltOf` at
`bandFM sz (STflowE z)` as in `stCltIso_holds`, targets 7a–7b, `stExpInvgL_band`, `bandFM_STCltFarConcl`). -/
def T2479_BandFar : Prop := ∀ d : ℕ, STCltFargL d → STCltFar d

/-- **Target 4** (proposal, not binding): the mean part over the carrier (`meanFar_eventuallyg`), mixed charges, from the
premises of the pin; band `meanFar_eventually` (`MeanFar:1980`, every `σ`, `|E| ≤ 2 - κ`). -/
def T2479_MeanFarg : Prop :=
  ∀ {d : ℕ} (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ),
    HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → STReg5I sz s t → STThPropsg C → STKpropsg C s → STExpInvgL C μ →
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n),
      ‖∫ ω, STfFarg C n (s n) (t n) σ a ω ∂μ‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1))

/-! ### Shapes (not binding) -/

/-- The band instance of target 6 composes with target 8 (target 9 reads the same data). -/
example : Prop := T2479_FarPin → T2479_BandFar → ∀ d : ℕ, STCltFar d

/-- The BA reading (C9: U4-BA owns it): the pin at `baFMz sz z`, law `seqP (sz.withLam 0)`, `H₀ = g₀ Ψ`, `g' = 0`,
`E = BAflowEs`; U4-BA (a) supplies `STThPropsg`, `STKpropsg` at `baFMz` (R1 conversion from `g₀`, 1457 (g)). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (κ δ 𝔠 𝔡 Cd : ℝ) (s t : ℕ → ℝ),
  HCltOf (baFMz sz z) (Sizes.seqP (sz.withLam 0))
      (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun _ => 0) (BAflowEs sz z)
      κ δ 𝔠 𝔡 Cd s t →
    STReg5I sz s t → STThPropsg (baFMz sz z) → STKpropsg (baFMz sz z) s →
    STExpInvgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) →
    STCltFarConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- UBA-C1 in the text of DECISIONS §273 (1): the R1 literal, the only admissible comparison text if a statement here ever
crosses size level and kernel level (not expected: X1b reads the Θ profile only through `STThPropsg`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

end

/-! ## Part 3 (G1): the public declarations of the four band files, unchanged (no band file is edited) -/

-- `Evolution/CltMoments1.lean` (59)
#check @RBM.Evol.cltMom1_zdistInf_sub_comm
#check @RBM.Evol.cltMom1_zdistInf_tri
#check @RBM.Evol.CltMom1.cs
#check @RBM.Evol.CltMom1.cs_pos
#check @RBM.Evol.CltMom1.Cluster
#check @RBM.Evol.CltMom1.Paired
#check @RBM.Evol.CltMom1.free
#check @RBM.Evol.CltMom1.assigned
#check @RBM.Evol.CltMom1.ball
#check @RBM.Evol.CltMom1.clusterSum
#check @RBM.Evol.cltMom1_exists_cluster
#check @RBM.Evol.cltMom1_sum_compat
#check @RBM.Evol.cltMom1_paired_sum_le
#check @RBM.Evol.cltMom1_assigned_pos
#check @RBM.Evol.cltMom1_sum_assigned
#check @RBM.Evol.cltMom1_two_mul_free_le
#check @RBM.Evol.cltMom1_card_cluster_le
#check @RBM.Evol.cltMom1_clusterSum_le_of_bound
#check @RBM.Evol.cltMom1_clusterSum_nonneg
#check @RBM.Evol.cltMom1_clusters
#check @RBM.Evol.cltMom1_not_paired_iff
#check @RBM.Evol.cltMom1_iso_hyp_iff
#check @RBM.Evol.cltMom1_weight_a1
#check @RBM.Evol.cltMom1_weight_a2
#check @RBM.Evol.cltMom1_comparable_real
#check @RBM.Evol.cltMom1_comparable
#check @RBM.Evol.cltMom1_comparable_weights
#check @RBM.Evol.cltMom1_scale_comparable
#check @RBM.Evol.cltMom1_scale_bd1
#check @RBM.Evol.cltMom1_scale_one_le
#check @RBM.Evol.cltMom1_scale_ell_le
#check @RBM.Evol.CltMom1.G
#check @RBM.Evol.CltMom1.G_nonneg
#check @RBM.Evol.CltMom1.Yw
#check @RBM.Evol.CltMom1.Yw_nonneg
#check @RBM.Evol.cltMom1_G_sum_le
#check @RBM.Evol.cltMom1_G_sum_sub_le
#check @RBM.Evol.cltMom1_cluster_sum
#check @RBM.Evol.CltMom1.Yw_le
#check @RBM.Evol.cltMom1_Yw_bound
#check @RBM.Evol.cltMom1_cluster_sum_C4
#check @RBM.Evol.cltMom1_term_le
#check @RBM.Evol.cltMom1_simplecalculus
#check @RBM.Evol.cltMom1_simplecalculus_ell
#check @RBM.Evol.cltMom1_exponent_identity
#check @RBM.Evol.cltMom1_exponent_nat
#check @RBM.Evol.cltMom1_exponent_count
#check @RBM.Evol.cltMom1_exponent_count_eq
#check @RBM.Evol.cltMom1_prod_exponent_exact
#check @RBM.Evol.cltMom1_prod_clusters
#check @RBM.Evol.CltMom1.Cd
#check @RBM.Evol.CltMom1.uw
#check @RBM.Evol.CltMom1.uw_nonneg
#check @RBM.Evol.cltMom1_uw_sum
#check @RBM.Evol.cltMom1_cluster_term_le
#check @RBM.Evol.cltMom1_clusterSum_le
#check @RBM.Evol.cltMom1_paired_moment_le
#check @RBM.Evol.cltMom1_cluster_inst
#check @RBM.Evol.cltMom1_b_paired
-- `Evolution/CltMoments2.lean` (23)
#check @RBM.Evol.CltMom2.Z
#check @RBM.Evol.CltMom2.fluc
#check @RBM.Evol.CltMom2.off
#check @RBM.Evol.CltMom2.BY
#check @RBM.Evol.CltMom2.DomHyp
#check @RBM.Evol.CltMom2.IsoHyp
#check @RBM.Evol.CltMom2.rhs
#check @RBM.Evol.CltMom2.BYStmt
#check @RBM.Evol.CltMom2.DecompStmt
#check @RBM.Evol.CltMom2.WeightStmt
#check @RBM.Evol.CltMom2.HzuStmt
#check @RBM.Evol.CltMom2.MomentStmt
#check @RBM.Evol.CltMom2.TailStmt
#check @RBM.Evol.CltMom2.X
#check @RBM.Evol.cltMom2_expand
#check @RBM.Evol.cltMom2_moment_le
#check @RBM.Evol.cltMom2_markov
#check @RBM.Evol.cltMom2_decomp
#check @RBM.Evol.cltMom2_norm_stcltB_le
#check @RBM.Evol.cltMom2_weight_le
#check @RBM.Evol.cltMom2_hzu
#check @RBM.Evol.cltMom2_moment_fixed
#check @RBM.Evol.cltMom2_tail_eventually
-- `Evolution/MeanFar.lean` (8)
#check @RBM.Gauss.Sizes.meanFar_Cd
#check @RBM.Gauss.Sizes.meanFar_core
#check @RBM.Gauss.Sizes.meanFar_T1
#check @RBM.Gauss.Sizes.meanFar_T2
#check @RBM.Gauss.Sizes.meanFar_eventually
#check @RBM.Gauss.Sizes.STMeanFarConcl
#check @RBM.Gauss.Sizes.STMeanFar
#check @RBM.Gauss.Sizes.stMeanFar
-- `Evolution/CltFar.lean` (7)
#check @RBM.Gauss.Sizes.CltFar.DomStmt
#check @RBM.Gauss.Sizes.CltFar.OffStmt
#check @RBM.Gauss.Sizes.CltFar.FlucStmt
#check @RBM.Gauss.Sizes.cltFar_dom
#check @RBM.Gauss.Sizes.cltFar_off
#check @RBM.Gauss.Sizes.cltFar_fluc
#check @RBM.Gauss.Sizes.stCltFar_holds
