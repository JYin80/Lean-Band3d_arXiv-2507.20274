/-
Release check for T2211 (dispatcher V1, Mon Oct  5 20:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §40,
§45 O2, §67, §68).
S6-02 (stochastic layer ST-5, Step 6): the Step-6 kit of the T2191 probe (`git show 96c6b4c:RBM3D/Probe/T2191Pins.lean`,
branch `t/T2191`; design merged report-only at 4fecaa2, §67) moved verbatim into the new file
`RBM3D/Induction/Step6Kit.lean`: the `Prec` calculus and the bridges at a section (probe §2), the compiled glue (§5), the
initial term (§6), the four regime skeletons `ST_step6_case{I,II,III,IV}_of_pins` (§7), `st6_GdecayW_of_zero` and
`ST_step6R_mono` (§7b), and the §8 instances not moved by S6-01 (T2204, cda3bb2).  Not ported (DECISIONS §68 (7), (9)):
`ST_mainInd_of_steps` (§3; the regime assembly reuses its proof as `ST_mainIndR_of_steps R`), the intermediate-time gluing
(`st6_incl`, `st6_restrict_*`, `st6_cover_two`, `ST_step6_compose`, `ST_step6_four_of_regimes`, `STGenericPos`,
`st6_genericPos_regSeq`, `ST_step6_generic_of_regimes`) and its instances (`szFour` …, `inst_four`, `inst_generic`,
`inst_compose`, `inst_cover_two`, `inst_restrict`, `inst_assembly6`).
Section 1: the merged names the moved text uses (exact namespaces; file and last commit on `main` cda3bb2).
Section 2: the statements of the consumer-facing kit theorems as closed `Prop`s (probe binders verbatim, the section
variables `{d : ℕ} (sz : Sizes d)` written out as the leading binders exactly where Lean includes them), in the temporary
namespace `RBM.Gauss.Sizes.T2211Check` (T2211 proves each in `RBM.Gauss.Sizes`, verbatim, docstrings kept).  Not pinned
here (statement covered by the verbatim criterion): the `Type*`-polymorphic `Prec` lemmas (`st6_prec_det_iff`,
`st6_precU_of_forall_seq`, `st6_prec_pi_norm`, `st6_prec_of_forall_fin`, `st6_cover_exp2U`), the two `private` lemmas,
and the internal comparisons of §6/§7.
Section 3: the statements of the instances T2211 compiles (probe §8), as `Prop`-valued `example`s (no proof obligation;
probe binders and types verbatim).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Imports: the eleven merged modules the probe imports (probe lines 6-16; between the probe's base 0818c49 and `main`
cda3bb2 the only change to an existing file in their closure is `Induction/Step5Pins.lean:153-168`, `STLemDecCalEConcl`,
not used by the probe) and the merged `RBM3D.Induction.Step6Pins` (S6-01); not the probe, not `RBM3D`.
No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2211-check.lean`.
-/
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopNorm
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.DecayLoopB
import RBM3D.Loop.KLFinal
import RBM3D.Green.GbEXP
import RBM3D.Graph.LWPins
import RBM3D.Evolution.Prec
import RBM3D.Induction.Step6Pins

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204)
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpEGt
#check @RBM.Gauss.Sizes.STExpTarget
#check @RBM.Gauss.Sizes.STExp2U
#check @RBM.Gauss.Sizes.STExp2_of_STExp2U
#check @RBM.Gauss.Sizes.STStep2Core
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STStep6R
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STStep6II
#check @RBM.Gauss.Sizes.STStep6III
#check @RBM.Gauss.Sizes.STStep6IV
#check @RBM.Gauss.Sizes.STStep6
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Sizes.STExpAvgU
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Sizes.STExpDuhEq
#check @RBM.Gauss.Sizes.STExpDuhEqQ
#check @RBM.Gauss.Sizes.STDriftHi
#check @RBM.Gauss.Sizes.STExpLKLKHiConcl
#check @RBM.Gauss.Sizes.STExpLKLKHi
#check @RBM.Gauss.Sizes.STExpEGtHiConcl
#check @RBM.Gauss.Sizes.STExpDriftLo
#check @RBM.Gauss.Sizes.STExpDriftDecay
#check @RBM.Gauss.Sizes.STExpWardI
#check @RBM.Gauss.Sizes.STExpWardII
#check @RBM.Gauss.Sizes.STExpIntI
#check @RBM.Gauss.Sizes.STExpIntII
#check @RBM.Gauss.Sizes.STExpIntIII
#check @RBM.Gauss.Sizes.STExpIntIV
#check @RBM.Gauss.Sizes.STExpIniI
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_ing6_I
#check @RBM.Gauss.Step6Inst.inst_ing6_II
#check @RBM.Gauss.Step6Inst.inst_ing6_III
#check @RBM.Gauss.Step6Inst.inst_step6I
#check @RBM.Gauss.Step6Inst.inst_step6II
#check @RBM.Gauss.Step6Inst.inst_step6III
#check @RBM.Gauss.Step6Inst.inst_step6IV
-- `RBM3D/Induction/Step5Kit.lean` (85e43db)
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_prec_cover
#check @RBM.Gauss.Sizes.st5_zeroModeSet_empty
#check @RBM.Gauss.Sizes.st5_conStInd_mono
#check @RBM.Gauss.Sizes.st5_t_lt_one
-- `RBM3D/Induction/Step5Pins.lean` (d7da51e)
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STSigAll
#check @RBM.Gauss.Sizes.st5_reg5I_mid
#check @RBM.Gauss.Step5Inst.szG
#check @RBM.Gauss.Step5Inst.szB_reg5I
#check @RBM.Gauss.Step5Inst.szB_reg5II
#check @RBM.Gauss.Step5Inst.sz0_reg5III
-- `RBM3D/Induction/Step34Pins.lean` (fc76526)
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.szB_WO
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.flow_zB
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step34Inst.szB_flow_ht
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
-- `RBM3D/Induction/Step2Defs.lean` (86124dc)
#check @RBM.Gauss.Sizes.STmsig
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.STavgM
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.STEGt
-- `RBM3D/Induction/Step2Iterate.lean` (c5bbae7)
#check @RBM.Gauss.Sizes.ST_Kloop_one
-- `RBM3D/Induction/ScaleFacts.lean` (5d1e6b1)
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
-- `RBM3D/Evolution/Prec.lean` (fc76526): the proved kernel theorems used by the skeletons
#check @RBM.Gauss.Sizes.stek_sumNdecay_holds
#check @RBM.Gauss.Sizes.stek_nonzero_holds
-- `RBM3D/Evolution/Pins.lean` (d9de66f)
#check @RBM.EKsgn
-- `RBM3D/Graph/LWPins.lean` (975f4ff): `LWtermEXP` (LW-14, owed) is a premise of the skeletons I, II, III and of `st6_EGtHi_of_LW`
#check @RBM.Gauss.Sizes.LWcut
#check @RBM.Gauss.Sizes.LWE
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.LWtermEXP
-- `RBM3D/Induction/GridDuhamelN.lean` (2ebee73)
#check @RBM.Ind.Ugen
-- `RBM3D/Induction/QopAlgebra.lean` (6b2494e)
#check @RBM.Gauss.Sizes.stMollifierEx_holds
-- `RBM3D/Kernel/Evolution.lean` (ff8d36d)
#check @RBM.zeroModeSet
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.StochDomAt
#check @RBM.badSetAt
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.one_le_size
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_subset_union
#check @RBM.StochDomAt.of_eventually_empty
-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Idx
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.Gauss.SizesInst.sz0_admissible
-- `RBM3D/Defs/Params.lean` (c3f3d5d)
#check @RBM.ellT
#check @RBM.Bparam
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.mE
#check @RBM.mE_im
#check @RBM.norm_mE
#check @RBM.mSigma
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.abs_lemE_le
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.loopM
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.Sizes.Lloop
-- `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.Zd

/-! ## 2. Statements of the consumer-facing kit theorems (closed `Prop`s; probe binders verbatim) -/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2211Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### Probe §2 `167-333`: `0 < lam n`, the bridges at a section `u ∈ [s,t]`, the endpoint of `STLocalEntryU` -/

-- probe `:182`
def st6_lam_pos : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔡 : ℝ} (h : sz.WO 𝔡), ∀ᶠ n in atTop, 0 < sz.lam n

-- probe `:193`
def st6_target_lam_zero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {n : ℕ} (h : sz.lam n = 0) (u : ℝ),
    STExpTarget sz n u = (sz.Bctl n u) ^ 3

-- probe `:291`
def STLK_of_STLKU_at : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLKU sz E s t), STLK sz E u

-- probe `:297`
def STLmax_of_STLmaxU_at : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLmaxU sz E s t), STLmax sz E u

-- probe `:303`
def STLocalEntry_of_STLocalEntryU_at : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLocalEntryU sz E s t), STLocalEntry sz E u

-- probe `:310`
def LWAvgLaw_of_STAvgU_at : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STAvgU sz E s t), LWAvgLaw sz E u

-- probe `:320`
def STDecay_of_STGdecayW_at : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STGdecayW sz E s t 0), STDecay sz E u

-- probe `:329`
def STLocalEntry_of_STLocalEntryU : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLocalEntryU sz E s t),
    STLocalEntry sz E t

/-! ### Probe §5 `719-873`: windows, the rotation bridge `STEGt = LWE`, the Duhamel identity along `[s,t]` -/

-- probe `:796`
def st6_hi_of_reg5I : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (hd : 2 ≤ d) {s t : ℕ → ℝ} (h : STReg5I sz s t), STDriftHi sz s t

-- probe `:800`
def st6_hi_of_reg5II : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (h : STReg5II sz s t), STDriftHi sz s t

-- probe `:803`
def st6_hi_of_reg5III : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (h : STReg5III sz s t), STDriftHi sz s t

-- probe `:832`
def st6_EGt_eq_LWE : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ),
    STEGt sz n E t σ a ω = LWE sz n E t σ a ω

-- probe `:866`
def st6_duhEq_of_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (hDu : STExpDuhamelZ d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n)),
    STExpDuhEq sz (STflowE z) s t

/-! ### Probe §6 `875-1023`: the initial term in regimes (iii), (iv) -/

-- probe `:913`
def st6_xB_III : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) (hg : sz.lam n ^ 2 ≤ 1 - u),
    (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u)

-- probe `:933`
def st6_xB_IV : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1)
    (hg : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d),
    (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u)

-- probe `:980`
def st6_cmp_ini : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1)
    (h : (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u)),
    ((1 - s) / (1 - u)) ^ 2 * STExpTarget sz n s ≤ 4 * STExpTarget sz n u

/-! ### Probe §7 `1025-1535`: the uniform drift inputs and the four regime skeletons -/

-- probe `:1062`
def st6_expAvgU_of_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (hAvg : STImproveExpAver d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hS2 : STStep2Core sz (STflowE z) s t)
    (hLKU : STLKU sz (STflowE z) s t), STExpAvgU sz (STflowE z) s t

-- probe `:1076`
def st6_EGtHi_of_LW : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (hLW : LWtermEXP d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hHi : STDriftHi sz s t) (hS2 : STStep2Core sz (STflowE z) s t)
    (hLmax : STLmaxU sz (STflowE z) s t) (hLKU : STLKU sz (STflowE z) s t)
    (hS5 : STGdecayW sz (STflowE z) s t 0), STExpEGtHiConcl sz (STflowE z) s t

-- probe `:1233`
def st6_F1_window_vs_reg5II : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hI : STCaseI sz s t) (hII : STReg5II sz s t) (n : ℕ), t n ≤ s n

-- probe `:1242` (regime (iii); consumer: the regime assembly, `STStep6R_R` at `R = STReg5III`)
def ST_step6_caseIII_of_pins : Prop :=
  ∀ {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hDu : STExpDuhamelZ d) (hInt : STExpIntIII d),
    STStep6III d

-- probe `:1291` (regime (iv))
def ST_step6_caseIV_of_pins : Prop :=
  ∀ {d : ℕ} (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hLo : STExpDriftLo d) (hInt : STExpIntIV d),
    STStep6IV d

-- probe `:1370` (regime (ii))
def ST_step6_caseII_of_pins : Prop :=
  ∀ {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d)
    (hInt : STExpIntII d) (hWd : STExpWardII d), STStep6II d

-- probe `:1452` (regime (i))
def ST_step6_caseI_of_pins : Prop :=
  ∀ {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d)
    (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d) (hIni : STExpIniI d)
    (hInt : STExpIntI d), STStep6I d

/-! ### Probe §7b, the two lemmas kept (`1594-1625`, `1728-1733`) -/

-- probe `:1596`
def st6_GdecayW_of_zero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (h : STGdecayW sz E s t 0), STGdecayW sz E s t Cd

-- probe `:1729` (the section variable `sz` is not included: `hRR` binds its own `sz`)
def ST_step6R_mono : Prop :=
  ∀ {d : ℕ} {R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STStep6R d R), STStep6R d R'

end RBM.Gauss.Sizes.T2211Check

/-! ## 3. The statements of the instances T2211 compiles (probe §8; `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`) -/

namespace RBM.Gauss.Step6Inst.T2211Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

-- statement of `inst_hiI` (probe `:1845`)
example : Prop := STDriftHi szB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_hiII` (probe `:1846`)
example : Prop := STDriftHi szB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_hiIII` (probe `:1847`)
example : Prop := STDriftHi sz0 sInst tInst

-- statement of `inst_expLKLK_I` (probe `:1850`)
example : Prop :=
  ∀ (h : STExpLKLKHi 3),
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_expLKLK_II` (probe `:1853`)
example : Prop :=
  ∀ (h : STExpLKLKHi 3),
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_expLKLK_III` (probe `:1856`)
example : Prop :=
  ∀ (h : STExpLKLKHi 3),
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) sz0 z0 sInst tInst

-- statement of `inst_skeleton6I` (probe `:1910`)
example : Prop :=
  ∀ (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3)
    (hDuQ : STExpDuhamelQ 3) (hDec : STExpDriftDecay 3) (hWd : STExpWardI 3) (hIni : STExpIniI 3)
    (hInt : STExpIntI 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_skeleton6II` (probe `:1916`)
example : Prop :=
  ∀ (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3)
    (hInt : STExpIntII 3) (hWd : STExpWardII 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_skeleton6III` (probe `:1921`)
example : Prop :=
  ∀ (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3) (hInt : STExpIntIII 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst

-- statement of `inst_skeleton6IV` (probe `:1926`)
example : Prop :=
  ∀ (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3) (hLo : STExpDriftLo 3) (hInt : STExpIntIV 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_precU` (probe `:2131`)
example : Prop :=
  sz0.Prec (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n × Bool)
    (fun _ p _ => 1 - (p.1 : ℝ)) (fun _ p _ => 2 * (1 - (p.1 : ℝ)))

-- statement of `inst_GdecayW_of_zero` (probe `:2160`)
example : Prop :=
  ∀ (h : STGdecayW sz0 (STflowE z0) sInst tInst 0), STGdecayW sz0 (STflowE z0) sInst tInst 1

-- statement of `inst_F1` (probe `:2164`)
example : Prop := ¬ STCaseI szB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_step6R_mono` (probe `:2169`)
example : Prop :=
  ∀ (h : STStep6 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_bridges` (probe `:2174`)
example : Prop :=
  ∀ (hLE : STLocalEntryU sz0 (STflowE z0) sInst tInst) (hAvg : STAvgU sz0 (STflowE z0) sInst tInst)
    (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst) (hLK : STLKU sz0 (STflowE z0) sInst tInst)
    (hDec : STGdecayW sz0 (STflowE z0) sInst tInst 0),
    STLocalEntry sz0 (STflowE z0) (fun _ => 1 / 32) ∧ LWAvgLaw sz0 (STflowE z0) (fun _ => 1 / 32) ∧
      STLmax sz0 (STflowE z0) (fun _ => 1 / 32) ∧ STLK sz0 (STflowE z0) (fun _ => 1 / 32) ∧
      STDecay sz0 (STflowE z0) (fun _ => 1 / 32)

-- statement of `inst_endpoints` (probe `:2192`)
example : Prop :=
  ∀ (h : STExp2U sz0 (STflowE z0) sInst tInst) (hLE : STLocalEntryU sz0 (STflowE z0) sInst tInst),
    STExp2 sz0 (STflowE z0) tInst ∧ STLocalEntry sz0 (STflowE z0) tInst

-- statement of `inst_expAvgU` (probe `:2209`)
example : Prop :=
  ∀ (hAvg : STImproveExpAver 3) (hS2 : STStep2Core sz0 (STflowE z0) sInst tInst)
    (hLKU : STLKU sz0 (STflowE z0) sInst tInst), STExpAvgU sz0 (STflowE z0) sInst tInst

-- statement of `inst_EGtHi` (probe `:2216`)
example : Prop :=
  ∀ (hLW : LWtermEXP 3) (hS2 : STStep2Core sz0 (STflowE z0) sInst tInst)
    (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst) (hLK : STLKU sz0 (STflowE z0) sInst tInst)
    (hS5 : STGdecayW sz0 (STflowE z0) sInst tInst 0), STExpEGtHiConcl sz0 (STflowE z0) sInst tInst

-- statement of `inst_duhEq` (probe `:2223`)
example : Prop := ∀ (hDu : STExpDuhamelZ 3), STExpDuhEq sz0 (STflowE z0) sInst tInst

-- statement of `inst_G_pos_sz0` (probe `:2231`)
example : Prop := ∀ (n : ℕ), 0 < (sz0.lam n ^ 2 * ((sz0.W n : ℕ) : ℝ) ^ 3) ^ (-(1 / 5 : ℝ))

-- statement of `inst_G_pos_szB` (probe `:2236`)
example : Prop := ∀ (n : ℕ), 0 < (szB.lam n ^ 2 * ((szB.W n : ℕ) : ℝ) ^ 3) ^ (-(1 / 5 : ℝ))

-- statement of `inst_G_pos_szG` (probe `:2239`)
example : Prop := ∀ (n : ℕ), 0 < (szG.lam n ^ 2 * ((szG.W n : ℕ) : ℝ) ^ 3) ^ (-(1 / 5 : ℝ))

-- statement of `st6_target_pos` (probe `:2243`; declared in `RBM.Gauss.Step6Inst` with explicit `{d} (sz)`)
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {n : ℕ} (hl : sz.lam n ≠ 0) {u : ℝ} (hu : u < 1), 0 < STExpTarget sz n u

-- statement of `inst_target_pos_sz0` (probe `:2250`)
example : Prop := 0 < STExpTarget sz0 0 (1 / 16)

-- statement of `inst_target_pos_szB` (probe `:2253`)
example : Prop := ∀ (n : ℕ), 0 < STExpTarget szB n (15 / 16)

-- statement of `inst_target_pos_szG` (probe `:2256`)
example : Prop := ∀ (n : ℕ), 0 < STExpTarget szG n (3 / 4)

-- statement of `inst_lam_pos` (probe `:2292`)
example : Prop := ∀ᶠ n in atTop, 0 < sz0.lam n

-- statement of `inst_target_lam_zero` (probe `:2295`)
example : Prop :=
  ∀ (n : ℕ) (u : ℝ), STExpTarget (sz0.withLam fun _ => 0) n u = ((sz0.withLam fun _ => 0).Bctl n u) ^ 3

-- statement of `inst_cmp_III` (probe `:2301`)
example : Prop :=
  (1 - (0 : ℝ)) * sz0.Bctl 0 0 ≤ 2 * ((1 - 4095 / 4096 : ℝ) * sz0.Bctl 0 (4095 / 4096)) ∧
    ((1 - (0 : ℝ)) / (1 - 4095 / 4096)) ^ 2 * STExpTarget sz0 0 0 ≤ 4 * STExpTarget sz0 0 (4095 / 4096)

-- statement of `inst_cmp_IV` (probe `:2311`)
example : Prop :=
  (1 - (39 / 64 : ℝ)) * szG.Bctl 0 (39 / 64) ≤ 2 * ((1 - 3 / 4 : ℝ) * szG.Bctl 0 (3 / 4)) ∧
    ((1 - (39 / 64 : ℝ)) / (1 - 3 / 4)) ^ 2 * STExpTarget szG 0 (39 / 64) ≤ 4 * STExpTarget szG 0 (3 / 4)

-- statement of `inst_ini_sumNdecay` (probe `:2323`)
example : Prop :=
  ∀ (hExp : STExp2 sz0 (STflowE z0) sInst),
    sz0.Prec (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖RBM.Ind.Ugen 3 (sz0.L n) (sz0.lam n) (STflowE z0 n) p.2.1 (sInst n) (p.1 : ℝ)
        (fun b => sz0.STExpErr n (STflowE z0 n) (sInst n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - sInst n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz0 n (sInst n))

-- statement of `inst_ini_nonzero` (probe `:2332`)
example : Prop :=
  ∀ (hExp : STExp2 szB (STflowE zB) (fun _ => 15 / 16)),
    szB.Prec (U := STIdx2P szB STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32))
      (fun n p _ => ‖zeroModeSet 3 (szB.L n) (Finset.univ : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (15 / 16) (p.1 : ℝ)
          (fun b => szB.STExpErr n (STflowE zB n) (15 / 16) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget szB n (15 / 16))

-- statement of `inst_mollifier_family` (probe `:2343`)
example : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
    ∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)

end RBM.Gauss.Step6Inst.T2211Check
