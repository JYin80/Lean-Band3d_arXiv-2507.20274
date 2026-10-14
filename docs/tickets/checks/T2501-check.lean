/-
Release check for T2501 (dispatcher V4, 2026-10-14; DECISIONS §311).  U U4-BA = the block Anderson instance of U4
(supervisor 1457 Q4: rows (a) and (b); REQ-1418 `:56-67`).  Rows a1 (`Step5KerBA`) and a2 (`CltFlowBA`): the BA producers of the merged family classes of U4s1-U4s3
and X1 (`IniTermGen_KerFacts`, `IniTermGen_CltFlow`, A9 `EtermsMid_NewKLKL`, D2 `LemDecCalELipG_FlowMod`, D3 `NQEndFlowGen_KLip`
at k = 2).  Row b: the six ingredient pins and Step 5 cases (i), (ii), (iv) at the BA tuple
`(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)` (as T2499), from the merged generic results, plus the UN-C3 Ward bridge.
Coupling (UBA-C1; R1 = DECISIONS §273 (1)): the R1 conjunct of `IniTermGen_KerFacts` at `gK = BAflowLam0`, `A = (κ+1)/κ`
(`TwistStep2_lam0_sq`), and crossing (g) of the X1-C2 profile facts; nothing else crosses.  TN-C4: no `STGridRepNgL`.
Part 1: merged names (`main` 086d9091).  Part 2: pins (prefix `T2501_`; binding as marked), then shapes (not binding).
Part 3: the readers downstream (unchanged, not edited).  Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2501-check.lean
-/
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.IniTermIGen2
import RBM3D.Chain.CltFarUGen
import RBM3D.Chain.NewKLKLGen
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Induction.EtermsMid
import RBM3D.Induction.DuhamelII
import RBM3D.Induction.MainIndRegimes
import RBM3D.Evolution.ExpInv
import RBM3D.Evolution.CltFarG
import RBM3D.BA.SEforLnBA
import RBM3D.BA.Step2IterBA
import RBM3D.BA.Step2CloseBA
import RBM3D.BA.GridMartBA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.EMn2BA
import RBM3D.BA.Prop6Path
import RBM3D.BA.Prop5Short
import RBM3D.BA.CombesThomas
import RBM3D.BA.Ward
import RBM3D.BA.KInduct
import RBM3D.BA.KSolve
import RBM3D.BA.KTreeRep
import RBM3D.BA.KKernel
import RBM3D.BA.KBase
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistGrid
import RBM3D.BA.NewKLKBA
import RBM3D.BA.GreenSchur
import RBM3D.BA.Step5IIITargets
import RBM3D.Graph.BATermHoldsB
import RBM3D.Gauss.BlockAnderson

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U6 = T2458 (1debc230, `Chain/Step5Gen.lean`): the pin shape `:191`, Step 5 per regime `:214`, `:226-230`, the wrapped
-- ingredient pins `:234-251`, the conclusion `:62`, `lem:newKLK` at `ℓ = L` `:151`, `:164`
#check @RBM.BA.STIngR5gL
#check @RBM.BA.STStep5RgL
#check @RBM.BA.STStep5IgL
#check @RBM.BA.STStep5IIgL
#check @RBM.BA.STStep5IIIgL
#check @RBM.BA.STStep5IVgL
#check @RBM.BA.STStep5ConclgL
#check @RBM.BA.STEtermsMidgL
#check @RBM.BA.STDuhamelIgL
#check @RBM.BA.STDuhamelIIgL
#check @RBM.BA.STIniTermIgL
#check @RBM.BA.STIniTermIIgL
#check @RBM.BA.STWardIIgL
#check @RBM.BA.STNewKLKLAtgL'
#check @RBM.BA.STNewKLKLgL'
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STReg5Mid
-- U4s1 = T2462 (c9f69dba, 52f8f82a; `Chain/Step5CasesGen.lean`, `Chain/Step5KerGen.lean`, `Chain/NewKLKLGen.lean`): flow facts `:140`,
-- assembly `:169`, Ward identity `:187` (band `:198`), Ward term `:205`, case (iv) `:286`, case (i) `:340`, case (ii) `:548`;
-- kernel decay `Step5KerGen:188`; NewKLKL `NewKLKLGen:190`, `:301` under `NewKLKGenHyp` (`Chain/NewKLKGen.lean:383`)
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.ST_step5_assemblygL
#check @RBM.BA.Step5CasesGen_WardIdent
#check @RBM.BA.step5CasesGen_wardIdent_band
#check @RBM.BA.stWardIIgL_of
#check @RBM.BA.stStep5IVgL_holds
#check @RBM.BA.ST_step5_caseI_of_pinsgL
#check @RBM.BA.ST_step5_caseII_of_pinsgL
#check @RBM.BA.Step5KerGen_ThDecay
#check @RBM.BA.stNewKLKLAtgL'_of
#check @RBM.BA.stNewKLKLgL'_of
#check @RBM.BA.NewKLKGenHyp
-- U4s2 = T2484 (ba7e559e, e6c26ca4): `IniTermGen_KerFacts` (`IniTermIIGen:68`, band `:107`), `stIniTermIIgL_of` (`:991`);
-- `IniTermGen_CltFlow` (`CltFarUGen:62`, band `:83`); `stIniTermIgL_of` (`IniTermIGen2:707`)
#check @RBM.BA.IniTermGen_KerFacts
#check @RBM.BA.iniTermGen_kerFacts_band
#check @RBM.BA.stIniTermIIgL_of
#check @RBM.BA.IniTermGen_CltFlow
#check @RBM.BA.iniTermGen_cltFlow_band
#check @RBM.BA.stIniTermIgL_of
-- U4s3 = T2496 (e89f5609, 5e24c0bb; in place): `stEtermsMidgL_of` (`Induction/EtermsMid:356`), A9 (`EtermsMid2:46`, `:56`, band
-- `:62`), D2 (`LemDecCalELip:311`, band `:355`, the entry modulus `:337`), `stDuhamelIgL_of` (`DuhamelI2:1482`), `stDuhamelIIgL_of`
-- (`DuhamelII:823`); D3 is the inline `hKs`, the `k = 2` text of `NQEndFlowGen_KLip` (`Chain/NQEndFlowGen:209`, band `:222`)
#check @RBM.BA.stEtermsMidgL_of
#check @RBM.BA.EtermsMid_NewKLKLAtN
#check @RBM.BA.EtermsMid_NewKLKL
#check @RBM.BA.etermsMid_newKLKL_band
#check @RBM.Gauss.Sizes.LemDecCalELipG_FlowMod
#check @RBM.Gauss.Sizes.lemDecCalELipG_flowMod_band
#check @RBM.Gauss.Sizes.lemDecCalELipG_seqHflow_entry_sub
#check @RBM.BA.stDuhamelIgL_of
#check @RBM.BA.stDuhamelIIgL_of
#check @RBM.BA.NQEndFlowGen_KLip
#check @RBM.BA.nqEndFlowGen_kLip_band
-- the other merged family texts that the generic results read (`Step2IterGen:71`, `GridRepTailGen:54`, `Step2Gen:882`, `:651`,
-- `Step2EventsGen:80`, `:966`, `StepDecompGen:60`, `ZeroModeGen:289`, `GridDuhamelGen:51`, `EMn2Exp1:811`, `EMn2Exp2:934`)
#check @RBM.BA.Step2IterGen_K2
#check @RBM.BA.GridRepTailGen_Ker
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STLWTgL
#check @RBM.BA.Step2EventsGen_Grid
#check @RBM.BA.STBdatagL
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.ZeroModeGen_WardCls
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.Gauss.Sizes.emn2ExpFacts
#check @RBM.Gauss.Sizes.emn2ExpHK
-- X1a = T2455 (62eed82c), X1b = T2479 (82deb62b, 16861112): `Chain/CltGen.lean` `:31`, `:78-167`; far pin `CltFarG:807`;
-- `ExpInv:534`; the band producers (`CltFarG:911`, `:917`, `FarEntry:1731`, `CltGen:188`)
#check @RBM.BA.STThg
#check @RBM.BA.STThPropsg
#check @RBM.BA.STKpropsg
#check @RBM.BA.STKfargL
#check @RBM.BA.STMfarg
#check @RBM.BA.CltRepg
#check @RBM.BA.CltInvg
#check @RBM.BA.STExpInvgL
#check @RBM.BA.STGijDecgL
#check @RBM.BA.HCltOf
#check @RBM.BA.STCltFargL
#check @RBM.BA.STCltFarConclgL
#check @RBM.BA.stCltFargL_holds
#check @RBM.BA.stExpInvgL_of_rep
#check @RBM.BA.bandFM_STThPropsg
#check @RBM.BA.bandFM_STKpropsg
#check @RBM.BA.bandFM_STKfargL
#check @RBM.BA.bandFM_STMfarg
-- U2-BA = T2486 (7be99aae, 5fbefff2; 0349 O5, DECISIONS §296 (1)): flow facts, Ward class, loop form, compatibilities
-- (`BA/SEforLnBA.lean:152`, `:66`, `:135`, `:122`, `:129`)
#check @RBM.BA.baStep5CasesGen_flowFacts
#check @RBM.BA.baZeroModeGen_wardCls
#check @RBM.BA.baStep2Mat_loopForm
#check @RBM.BA.baStep34_LCompat
#check @RBM.BA.baStep34_KCompat
-- T1-BA = T2487 (268e07d4): `BA/Step2IterBA.lean:62`, `:74`, `:198`, `:226`, `:706`; `BA/Step2CloseBA.lean:66`; L5 = T2494
-- (8df84009): `Graph/BATermHoldsB.lean:865`; `Chain/Step2EventsGen.lean:1080`; `Chain/Step2EventsGenTw.lean:58`, `:73`
#check @RBM.BA.baStep2Mat_Hpath_herm
#check @RBM.BA.baStep2_oneLoop
#check @RBM.BA.baStep2_K2
#check @RBM.BA.baSTBdatagL_holds
#check @RBM.BA.baStep2_newKLK
#check @RBM.BA.baSTGijDecgL_holds
#check @RBM.BA.baLWtermExp_holds
#check @RBM.BA.stLWTgL_of_LWtermExpG
#check @RBM.BA.Step2EventsGenTw_baRot3
#check @RBM.BA.Step2EventsGenTw_baGrid
-- other merged BA sources (`GridMartBA:673`, `GridRepTailBA:60`, `EMn2BA:59`, `:64`, `:106`, `:125`, `:160`, `:386`, `:637`,
-- `NewKLKBA:446`, `:567`, `GreenSchur:59`, `:72`, `TwistStep2:731`, `:740`, `TwistGrid:199`, `KBase:381`, `KKernel:124`,
-- `Prop6Path:1009`, `:1049`, `Prop5Short:667`, `CombesThomas:562`, `Ward:53`, `:83`, `:136`, `:303`, `KInduct:88`, `KSolve:591`,
-- `KTreeRep:1674`, `Step2Kern:73`, `:90`, `:112`, `MFixedPoint:511-519`)
#check @RBM.BA.baGridMart_holds
#check @RBM.BA.gridRepTailGen_ker_BA
#check @RBM.BA.baEMn2Hf
#check @RBM.BA.baEMn2Zf
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.baEMn2ExpFacts
#check @RBM.BA.baComp_row_le
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.baNewKLKGenHyp
#check @RBM.BA.stK2decaygL'_ba
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.TwistStep2_T0_ge
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.BAuKerSemigroup_holds
#check @RBM.BA.BATheta_row_sum_pm
#check @RBM.BA.BAK_row_sum
#check @RBM.BA.baProp8_holds
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.baPropM_holds
#check @RBM.BA.BAMB_shift
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.baOffDiag_holds
#check @RBM.BA.baKsol_two
#check @RBM.BA.baK_translate
#check @RBM.BA.baKcac_isKLoopS
#check @RBM.BA.Step2Kern_Mss_BA
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.BAMss
#check @RBM.BA.BATheta
#check @RBM.BA.BATheta0
-- the BA tuple and data (`BA/FlowPins.lean:380-393`, `BA/Step2BA.lean:54`, `:75`, `:157`, `Gauss/BlockAnderson.lean:52`, `:65`, `:83`)
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baStep2Fam
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.PsiI_isHermitian
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.withLam
-- the carrier predicates among the binders of `STIngR5gL` (hypotheses of the instances of target 12)
#check @RBM.BA.STDecaygL
#check @RBM.BA.STDecayStronggL
-- instance data (`Defs/Sizes.lean:260`, `BA/FlowPins.lean:1181`, `:1214`, `:1254`)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: pins (binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### Row a: the BA producers -/

/-- **Target 1** (binding): the U4s2 kernel class at the BA family, `gK = g₀ = BAflowLam0` (the class carries its own
`3 ≤ d`; R1 is its third conjunct, `A = (κ+1)/κ`).  Band twin `iniTermGen_kerFacts_band` (`IniTermIIGen:107`). -/
def T2501_KerFactsBA : Prop :=
  ∀ d : ℕ, IniTermGen_KerFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowLam0

/-- **Target 1, the decay alone** (binding; `∃ C₆` after `κ`, the form of T2498's family row 9, `T2498.md:73`): the U4s1 kernel
decay at `gK = g₀` along every BA flow. -/
def T2501_ThDecayBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      Step5KerGen_ThDecay (baFMz sz z) (BAflowLam0 sz z) 𝔡⁻¹ C₆

/-- **Target 2** (binding): the X1 instance (C9), the U4s2 class `IniTermGen_CltFlow` at the BA tuple.  Band twin
`iniTermGen_cltFlow_band` (`CltFarUGen:83`). -/
def T2501_CltFlowBA : Prop :=
  ∀ d : ℕ, IniTermGen_CltFlow d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 3** (binding; A9, DECISIONS §301 (2)): `lem:newKLK` at `ℓ = L`, sharp form, along every BA flow at the Step2Mat family
`baStep2Mat sz g₀ E`; constants per `(κ, 𝔡)` before the sizes.  Band `etermsMid_newKLKL_band` (`EtermsMid2:62`). -/
def T2501_NewKLKLBA : Prop :=
  ∀ d : ℕ, EtermsMid_NewKLKL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))

/-- **Target 4** (binding; D2): the premise `hFM` of `stEtermsMidgL_of`, `stDuhamelIgL_of`, `stDuhamelIIgL_of` at the BA tuple,
`∃ c` before `(sz, z)` (`c = 1`: `Hm = sz.seqHflowBA g₀`, `G = contGood (sz.withLam 0)`). -/
def T2501_FlowModBA : Prop :=
  ∀ d : ℕ, ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      LemDecCalELipG_FlowMod (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) c

/-- **Target 5** (binding; D3): the time modulus of `𝒦^{(2)}` at the BA carrier, the `k = 2` text of `NQEndFlowGen_KLip`, which is
the inline premise `hKs` of `stDuhamelIgL_of` and `stDuhamelIIgL_of` read at `baStep2Mat sz g₀ E` (whose `toFlowFM` is `baFMz sz z`). -/
def T2501_KLipBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → NQEndFlowGen_KLip (baFMz sz z) t 2

/-- **Target 7** (binding): U6's `lem:newKLK` at `ℓ = L` at the BA family of T3-BA (`baStep2Fam`; REQ-1418 `:64`). -/
def T2501_NewKLKLgLBA : Prop := ∀ d : ℕ, STNewKLKLgL' d (fun sz E => baStep2Fam sz E)

/-! #### Shapes (not binding): the producers whose heads the registry tracks, and the inline facts -/

/-- `STThPropsg` along every BA flow (registry `Test/Axioms.lean:221`; crossing (g), R1 second conjunct only). -/
example : Prop := ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
  BAFlow sz κ ε 𝔠 𝔡 z → STThPropsg (baFMz sz z)

/-- `STKpropsg`, `STMfarg`, `STKfargL` under the start-time hypotheses of `IniTermGen_CltFlow` (registry `:222`, `:204`, `:203`). -/
example : Prop := ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
  BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
    STReg5I sz s t → STKpropsg (baFMz sz z) s ∧ STMfarg (baFMz sz z) s ∧ STKfargL (baFMz sz z) s

/-- `CltRepg` and `CltInvg` at `H₀ = g₀ Ψ`, `g' = 0`, `E = BAflowEs` (registry `:205`), the inputs of `stExpInvgL_of_rep`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ),
  CltRepg (baFMz sz z) (Sizes.seqP (sz.withLam 0))
      (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun _ => 0) (BAflowEs sz z) ∧
    CltInvg (sz := sz) (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))

/-- The inline premises `hmn`, `hSr` of the U4s3 results at the BA family (target 6; `S = 1`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  (∀ n, ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).m n‖ ≤ 1) ∧
    ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b, ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).S n a b‖ ≤ 1

/-- UBA-C1 at BA (DECISIONS §273 (1)): the one comparison text, `gK = BAflowLam0 sz z`, `A = (κ+1)/κ` (`TwistStep2_lam0_sq`). -/
example : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
    sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2

/-- The X1 far pin at BA (T2479 check `:229-235`): the merged `stCltFargL_holds` fed with target 2's fields. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (κ δ 𝔠 𝔡 Cd : ℝ) (s t : ℕ → ℝ),
  HCltOf (baFMz sz z) (Sizes.seqP (sz.withLam 0))
      (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun _ => 0) (BAflowEs sz z)
      κ δ 𝔠 𝔡 Cd s t →
    STReg5I sz s t → STThPropsg (baFMz sz z) → STKpropsg (baFMz sz z) s →
    STExpInvgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) →
    STCltFarConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-! ### Row b: the Ward identity, the six ingredient pins and the cases -/

/-- **Target 9** (binding): the `(zYU1)` identity along every BA flow, the premise shape of `stWardIIgL_of` (`Step5CasesGen:205`). -/
def T2501_WardIdentBA : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    Step5CasesGen_WardIdent (baFMz sz z)

/-- Target 9, the UN-C3 bridge (shape; 1852 `:77-80`): one Ward class plus the conjugation of the one-index `𝓛`, `𝒦`, written
inline (no named `Prop`), gives the identity, for every carrier. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (C : FlowFM sz), ZeroModeGen_WardCls sz C →
  (∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
    C.L n u (fun _ : Fin 1 => false) (fun _ => a) ω = (starRingEnd ℂ) (C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω) ∧
      C.K n u (fun _ : Fin 1 => false) (fun _ => a) = (starRingEnd ℂ) (C.K n u (fun _ : Fin 1 => true) (fun _ => a))) →
  Step5CasesGen_WardIdent C

/-- **Target 10** (binding): `(S5WG+M000)`, `(S5WG+M)` at the BA tuple. -/
def T2501_EtermsMidBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STEtermsMidgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 10** (binding): the integrated hierarchy of case (i) at the BA tuple. -/
def T2501_DuhamelIBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STDuhamelIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 10** (binding): the integrated hierarchy of case (ii) at the BA tuple. -/
def T2501_DuhamelIIBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STDuhamelIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 10** (binding): the initial term of case (i) at the BA tuple. -/
def T2501_IniTermIBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STIniTermIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 10** (binding): the initial terms of case (ii) at the BA tuple. -/
def T2501_IniTermIIBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STIniTermIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 10** (binding): the Ward term `(zYU1)` at the BA tuple. -/
def T2501_WardIIBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 11** (binding): Step 5 in case (i) (`STReg5I`) at the BA tuple. -/
def T2501_Step5IBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STStep5IgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 11** (binding): Step 5 in case (ii) (`STReg5II`) at the BA tuple. -/
def T2501_Step5IIBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → STStep5IIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-- **Target 11** (binding): Step 5 in case (iv) (`STReg5IV`) at the BA tuple, every `d` (`stStep5IVgL_holds` needs only the
flow facts). -/
def T2501_Step5IVBA : Prop :=
  ∀ d : ℕ, STStep5IVgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    baFMz BAflowT0

/-! #### Shapes (not binding): routes -/

/-- Target 11 (i) from target 10 (the merged `ST_step5_caseI_of_pinsgL` with `baStep5CasesGen_flowFacts d`). -/
example : Prop := T2501_EtermsMidBA → T2501_DuhamelIBA → T2501_IniTermIBA → T2501_Step5IBA

/-- Target 11 (ii) from target 10 (the merged `ST_step5_caseII_of_pinsgL`). -/
example : Prop := T2501_EtermsMidBA → T2501_DuhamelIIBA → T2501_IniTermIIBA → T2501_WardIIBA → T2501_Step5IIBA

/-- Row b's inputs from row a (the family table): the producers of targets 1-5 feed the six ingredient pins. -/
example : Prop := T2501_KerFactsBA → T2501_CltFlowBA → T2501_NewKLKLBA → T2501_FlowModBA → T2501_KLipBA →
  T2501_WardIdentBA → T2501_EtermsMidBA ∧ T2501_DuhamelIBA ∧ T2501_DuhamelIIBA ∧ T2501_IniTermIBA ∧
    T2501_IniTermIIBA ∧ T2501_WardIIBA

/-- The reader of the cases (V): the merged assembly at the BA carrier, `STDecaygL ∧ STDecayStronggL` at `t`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), (∀ n, s n ≤ t n) →
  STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
    STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STDecayStronggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

/-- The four regimes at the BA tuple, `d = 3`, for V (case (iii) is U5e's `baStep5III_holds`, `BA/Step5IIITargets.lean:57`). -/
example : Prop := T2501_Step5IBA → T2501_Step5IIBA → T2501_Step5IVBA →
  STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 →
    STStep5IgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 ∧
      STStep5IIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 ∧
      STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 ∧
      STStep5IVgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

end RBM.BA

end

/-! ## Part 3: the readers downstream (unchanged, not edited) -/

-- U5e = T2499 (086d9091): case (iii) at the BA tuple, `d = 3` (`BA/Step5IIITargets.lean:52`, `:57`)
#check @RBM.BA.baPfStep5_holds
#check @RBM.BA.baStep5III_holds
-- the band readers whose BA successors (V2a/V2b) take targets 11 (`Induction/MainIndRegimes.lean:222`, `:227`, `:232`)
#check @RBM.Gauss.Sizes.ST_mainIndR_I_of_steps
#check @RBM.Gauss.Sizes.ST_mainIndR_II_of_steps
#check @RBM.Gauss.Sizes.ST_mainIndR_IV_of_steps
