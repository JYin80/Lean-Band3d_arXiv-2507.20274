/-
T2269 check file (BA-S2b2b, dispatcher V1, Tue Oct  6 07:38 UTC 2026).  Statements of the proof targets of
`RBM3D/BA/Step1.lean` (the block Anderson port of `Induction/Step1.lean` sections 1-4 and `baBootstrap'_holds`,
which closes the owed pin `BABootstrap'` of `RBM3D/BA/Step1Boot.lean`).  Defs, `#check`s and Prop-valued
`example`s only: no proofs.  Compiles on `main` (1462fdb) as is.
-/
import RBM3D.BA.Step1Setup
import RBM3D.Induction.Step1

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## 0. Merged names used (each `#check` with its full namespace) -/

-- BA-S2b1 (T2256, `BA/Step1Boot.lean`)
#check @RBM.BA.FlowFM.indMax
#check @RBM.BA.FlowFM.gexRHS
#check @RBM.BA.BAGiiGEX
#check @RBM.BA.BAGijGEX
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAGbEXPij
#check @RBM.BA.BAFlowMember
#check @RBM.BA.BABootstrap'
#check @RBM.BA.BAFamZ_mono
#check @RBM.BA.BAFamZ_horizon
#check @RBM.BA.PrecL_congr
#check @RBM.BA.baGii_member
#check @RBM.BA.baGij_member
#check @RBM.BA.baM_entry_le
#check @RBM.BA.baOmegaC_eq_one
#check @RBM.BA.baBoot_LI
#check @RBM.BA.Step1BootInst.inst_hcon
#check @RBM.BA.Step1BootInst.inst_BAFamZ_horizon
-- BA-S2b2a (T2262, `BA/Step1Setup.lean`)
#check @RBM.BA.flowFM_omegaC_mono
#check @RBM.BA.flowFM_wl_det
#check @RBM.BA.baS1Std
#check @RBM.BA.baG_continuousOn
#check @RBM.BA.baGopbound
#check @RBM.BA.baNetLift
#check @RBM.BA.Step1SetupInst.sI
#check @RBM.BA.Step1SetupInst.tI
#check @RBM.BA.Step1SetupInst.inst_im_m_ge
#check @RBM.BA.Step1SetupInst.inst_norm_m_le
#check @RBM.BA.Step1SetupInst.inst_baS1Std
#check @RBM.BA.Step1SetupInst.inst_rangeCond
#check @RBM.BA.Step1SetupInst.inst_GM_zero
-- BA-S1 (T2237 `ConArg.lean`), BA-S2a (T2238 `Step1Trivial.lean`), T2227 `CouplingWindow.lean`
#check @RBM.BA.FlowFM.omegaC
#check @RBM.BA.BAConArgLoop''
#check @RBM.BA.BAConArg''
#check @RBM.BA.baConArg''_holds
#check @RBM.BA.BAself_norm_le_one
#check @RBM.BA.BAFamZ
#check @RBM.BA.BAFamZ_main
#check @RBM.BA.BAFamZ_im_m_ge
#check @RBM.BA.BAflow_T0_bounds
#check @RBM.BA.baFM_loop_det
#check @RBM.BA.BAWinBulk
-- BA carrier and flow data (T2197 `FlowPins.lean`)
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.STmaxLoop2g
#check @RBM.BA.STKboundgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STLocalMaxgL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAGt
#check @RBM.BA.BAmF
#check @RBM.BA.BAMfine
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAFlow
#check @RBM.BA.BAConArgVec
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.sz0_lam_pos
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
-- band model: `S1Std` and its scale facts, generic per-time helpers (T2079 `Induction/Step1Setup.lean`)
#check @RBM.Ind.S1Std
#check @RBM.Ind.s1B
#check @RBM.Ind.s1_hsize
#check @RBM.Ind.s1_one_le_size
#check @RBM.Ind.s1_B_pos
#check @RBM.Ind.s1_Bu_pos
#check @RBM.Ind.s1_B_le_one
#check @RBM.Ind.s1_ratio_ev
#check @RBM.Ind.s1_F3
#check @RBM.Ind.s1_F4
#check @RBM.Ind.s1_F5
#check @RBM.Ind.s1_F6
#check @RBM.Ind.s1_F7
#check @RBM.Ind.s1_F8
#check @RBM.Ind.s1_highProb_of_pt
#check @RBM.Ind.s1_pt_of_highProb
#check @RBM.Ind.s1_stochDom_unit
#check @RBM.Ind.s1xM
#check @RBM.Ind.s1xM_le_add
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const
-- band model of the port (T2090 `Induction/Step1.lean`; sections 1-4 are private there)
#check @RBM.Ind.step1TargetV3_holds
-- `≺` calculus (T2045 `Induction/PerTimeCalc.lean`, T2012 `Defs/StochDomAt.lean`, `Gauss/DominationAt.lean`,
-- `Gauss/Domination.lean`, `Induction/ScaleFacts.lean`, `Defs/Sizes.lean`)
#check @RBM.Ind.PerTimeCalc.stepOneBootstrap
#check @RBM.Ind.PerTimeCalc.Unif.forbidden_region
#check @RBM.Ind.PerTimeCalc.PerTime.stochDom_of_indicator
#check @RBM.Ind.PerTimeCalc.PerTime.stochDom_of_highProb
#check @RBM.Ind.PerTimeCalc.PerTime.stochDom_of_le_left_eventually
#check @RBM.Ind.PerTimeCalc.PerTime.mono_right_eventually
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt
#check @RBM.StochDomAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.highProbAt_univ
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.perTimeOfStochDomAt
#check @RBM.Path.perTimeDomAt_iff_forall_section
#check @RBM.Path.stochDomAt_of_perTimeDomAt
#check @RBM.Gauss.netSize
#check @RBM.Gauss.netPt
#check @RBM.Gauss.rpow_le_netSize
#check @RBM.Gauss.exists_netPt_close
#check @RBM.Gauss.card_net_le
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto

namespace RBM.BA.T2269Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. Vocabulary (in the new file: `FlowFM.gmMax`, namespace `RBM.BA`, used with dot notation) -/

/-- `‖G_v - M‖_max` of a flow carrier at size index `n`, time `v`, sample `ω` (the band `s1xM`,
`Induction/Step1Setup.lean:913`, is the `bandFM` case with `llErrMat` entries; the band `s1x`,
`Induction/Step1.lean:91`, is private). -/
noncomputable def gmMax {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖C.GM n v ω q.1 q.2‖)

/-! ## 2. Statements of the proof targets (names in the new file without `_stmt`, namespace `RBM.BA`)

Common data of targets 1-5: a size sequence `sz`, a member `z'` with carrier `baFMz sz z'` under the law
`seqP (sz.withLam 0)`; the band standing hypotheses `S1Std` at any `κ'`, `τ` and energy `Ed` (BA-S2b2b supplies
them by `baS1Std` at `Ed ≡ 0`); `κm ≤ Im m` along the carrier (`BAFamZ_im_m_ge`); the output of `baBoot_LI` at the
event threshold `C₀ = 1 + κm⁻¹` (the BA `s1_LI`; band threshold `2`); `(GiiGEX)`, `(GijGEX)` of the member at every
`u ∈ [s,t]` (`baGii_member`, `baGij_member`). -/

/-- Target 1 (`baS1_wl_seq`): the weak-law step at one time sequence `u ∈ [s,t]` (band `s1_wl_seq`,
`Induction/Step1.lean:130`): `1(‖G_u - M‖_max ≤ 2 a_s^{1/4}) ‖G_u - M‖_max ≺ 2·3^d a_s^{7/15}` per time,
`a_s = W^{-d}B_{s,0}`.  Core: `flowFM_wl_det` at `C₀ = 1 + κm⁻¹` (on the event `‖G - M‖_max ≤ 2a ≤ W^{-c'} ≤ 1`,
`‖G_xy‖ ≤ ‖M_xy‖ + 1 ≤ κm⁻¹ + 1` by `baM_entry_le`). -/
def baS1_wl_seq_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun _ => Unit)
        (fun n _ ω => {ω | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}.indicator
          (fun ω => gmMax (baFMz sz z') n (u n) ω) ω)
        (fun n _ _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))

/-- Target 2 (`baS1_forb`): the forbidden region for all `u ∈ [s,t]` simultaneously (band `s1_forb`,
`Induction/Step1.lean:262`): w.h.p. `‖G_u - M‖_max ≠ a_s^{1/4}` for every `u ∈ [s,t]`.  Target 1 on a polynomial net
(`#net ≤ N^{C'+1}`), `forbidden_region` on the band `[a/2, 2a]`, `baGopbound` at `C = 1` to pass to all `u` (`M` is
time independent, so `|gmMax_u - gmMax_{u'}| ≤ max_xy ‖BAGt_u - BAGt_{u'}‖`). -/
def baS1_forb_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) ∨
        (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) < gmMax (baFMz sz z') n (u : ℝ) ω})

/-- Target 3 (`baS1_boot`): the continuity argument (band `s1_boot`, `Induction/Step1.lean:398`): w.h.p.
`‖G_u - M‖_max < a_s^{1/4}` for every `u ∈ [s,t]`.  Initial condition `STLocalMaxgL` at `s` with `s1_F3`; continuity
from `baG_continuousOn` (finite `sup'`); forbidden region target 2; `stepOneBootstrap`. -/
def baS1_boot_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)})

/-- Target 4 (`baS1_weakPT`): `(Gtmwc)` per time over `[s,t]` (band `s1_weakPT`, `Induction/Step1.lean:431`):
`‖(G_u - M)_xy‖ ≺ (W^{-d}B_{u,0})^{1/4}`; `a_s ≤ a_u` by `STBctl_mono`.  The left side and the bound are those of the
second hypothesis of `baNetLift`. -/
def baS1_weakPT_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(baFMz sz z').GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

/-- Target 5 (`baS1_loopPT`): `(lRB1)` per time over `[s,t]` (band `s1_loopPT`, `Induction/Step1.lean:474`): the
indicator `omegaC (1 + κm⁻¹)` of the `baBoot_LI` output is removed on the event of target 3 (`‖G_u‖_max ≤ ‖M‖_max +
‖G_u - M‖_max < κm⁻¹ + a_s^{1/4} ≤ κm⁻¹ + 1`, `s1_F7`, `baM_entry_le`); `PrecL` (uniform) gives the per-`u` per-time
form by `perTimeOfStochDomAt`, the sections over `TimeIcc` as the band's private `s1_perTime_timeIcc`
(`Induction/Step1.lean:455`).  The left side and the bound are those of the first hypothesis of `baNetLift`. -/
def baS1_loopPT_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    ∀ k : ℕ, 1 ≤ k →
      PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖(baFMz sz z').L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-- Target 6 (`baBootstrap'_holds`): the merged pin `BABootstrap'` (`BA/Step1Boot.lean:148`, unchanged) from the
owed `BAFlowMember`, `BAGbEXPii`, `BAGbEXPij` (band `step1TargetV3_holds`, `Induction/Step1.lean:525`).  Proof:
`baS1Std` (main flow `z`, `τ = ε/2`, `Ed ≡ 0`); `κm = κ` by `BAFamZ_mono` (to `Fam(0)`) and `BAFamZ_im_m_ge`;
`|m| ≤ 1` (copy of the private `BASetup_norm_BAmF_le_one`, `BA/Step1Setup.lean:1048`); `baBoot_LI` at
`C₀ = 1 + κ⁻¹` with the loop half of the ConArg premise; `baGii_member`, `baGij_member` at `u ∈ [s,t]`;
targets 4, 5 and `baNetLift` at `lam0 = BAflowLam0 sz z'`, `E = BAflowEs sz z'`. -/
def baBootstrap'_holds_stmt (d : ℕ) : Prop :=
  BAFlowMember d → BAGbEXPii d → BAGbEXPij d → BABootstrap' d

/-! ## 3. Prop-valued examples (no proof obligations) -/

example : Prop := baS1_wl_seq_stmt 3 ∧ baS1_forb_stmt 3 ∧ baS1_boot_stmt 3
example : Prop := baS1_weakPT_stmt 3 ∧ baS1_loopPT_stmt 3 ∧ baBootstrap'_holds_stmt 3
example (sz : Sizes 3) (z' : ℕ → ℂ) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) : Prop :=
  gmMax (baFMz sz z') n v ω ≤ 1
example : Prop := BAFlowMember 3 → BAGbEXPii 3 → BAGbEXPij 3 → BABootstrap' 3

end RBM.BA.T2269Check
