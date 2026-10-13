/-
Release check for T2494 (dispatcher V3, 2026-10-13 06:58 UTC; DECISIONS §296).  BA-L L5 (+ L6, the last terminal ticket): `lem:LWterm` and
`lem: EWGn2_N` at the block Anderson data from the closed moment pins (`baLWMoment_closed`, `baLWMomentExp_closed`), the BA
Step 2 pin closed through `baStep2_holds`, and L6: the closures of the L4a2 successor pins (T2490 target 5, deferred), which
read L4b2b's `baExp14bS2_holds` (on `t/T2489b`, not merged: it enters here only through the merged type `BAExp14bS2`).
New files `Graph/BATermHolds`, `Graph/BATermHoldsB`, `Graph/BALWOut`; twin of `Graph/LWTermHolds.lean` and `Graph/LWTermExpN.lean`.
Part 1: merged names (`main` 5fbefff2).  Part 2: the target statements (prefix `T2494_`; content binding up to the name),
then shapes (not binding).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2494-check.lean
-/
import RBM3D.Defs.Sizes
import RBM3D.Defs.StochDomAt
import RBM3D.Chain.Carrier
import RBM3D.Chain.LWGen
import RBM3D.Chain.Step2EventsGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.BA.FlowPins
import RBM3D.BA.LWPinsBA
import RBM3D.BA.GreenLDE
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenLocal
import RBM3D.BA.Step1Boot
import RBM3D.BA.GbEXPav
import RBM3D.BA.Step1Prime
import RBM3D.BA.TwistPins
import RBM3D.BA.TwistAvgB
import RBM3D.BA.Step2CloseBA
import RBM3D.Graph.LWPsi
import RBM3D.Graph.LWTermExpN
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.BAGGExp
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BAZetaExp
import RBM3D.Graph.BAMomentGen
import RBM3D.Graph.BAMomentGenB
import RBM3D.Graph.BAMomentExpGen
import RBM3D.Graph.BAMomentExpGenB
import RBM3D.Graph.BAAnpLift
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.BAExp14b
import RBM3D.Graph.BAExp14bB
import RBM3D.Graph.BAExp14a2

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier, the Step 1/2 pins and the generic light-weight pins (`Chain/Carrier`, `Chain/LWGen`)
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.STInitialGT2gL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.LWcutg
#check @RBM.BA.LWEg
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.LWLoop2gL
#check @RBM.BA.LWAssmgL
#check @RBM.BA.LWLoopExpgL
#check @RBM.BA.LWAssmExpgL
#check @RBM.BA.LWtermG
#check @RBM.BA.LWtermExpG
#check @RBM.BA.LWtermEXPG
#check @RBM.BA.PinFam
#check @RBM.BA.bandPin
#check @RBM.BA.LWterm_iff
#check @RBM.BA.LWtermExp_iff
-- the BA readings and the band instances (`BA/LWPinsBA`); the BA data (`BA/FlowPins`)
#check @RBM.BA.baPin
#check @RBM.BA.BALWterm
#check @RBM.BA.BALWtermExp
#check @RBM.BA.BALWtermEXP
#check @RBM.BA.BASTLWB
#check @RBM.BA.BASTLWT
#check @RBM.BA.band_LWtermG
#check @RBM.BA.band_LWtermExpG
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baFMz
#check @RBM.BA.BAStep2
-- band basis of the twin (`Graph/LWTermHolds`, `Graph/LWTermExpN`, `Graph/LWPsi`)
#check @RBM.Gauss.Sizes.lwInteg_holds
#check @RBM.Gauss.Sizes.LWTermHolds_prec_of_moments
#check @RBM.Gauss.Sizes.LWTermHolds_fB
#check @RBM.Gauss.Sizes.lwReduceB_holds
#check @RBM.Gauss.Sizes.lwterm_holds
#check @RBM.Gauss.Sizes.lwReduceT_holds
#check @RBM.Gauss.Sizes.lwtermExpS_holds
#check @RBM.Gauss.Sizes.lwtermExpN_holds
#check @RBM.Gauss.Sizes.lwtermExp_holds
#check @RBM.Gauss.Sizes.lwtermExpN_of_LWterm
#check @RBM.Gauss.Sizes.lwN_Bctl_le
#check @RBM.Gauss.Sizes.lwN_Wneg_le
#check @RBM.Gauss.Sizes.lwN_size_rpow_neg_le
#check @RBM.lwN_prec_mono
#check @RBM.lwN_tailW_le
#check @RBM.lwN_B_le_tail
#check @RBM.tailW_regime1_bounds
#check @RBM.StochDomAt.of_subset_union
-- the BA moment pins and their closures (L3d2a = T2470, L3d2b = T2483, L3d1 = T2488)
#check @RBM.BA.LWfg
#check @RBM.BA.LWfg_baFMz
#check @RBM.BA.LWMomentG
#check @RBM.BA.BALWMoment
#check @RBM.BA.BAMomentGen_whp_of_prec
#check @RBM.BA.BALWMomentOfAnp
#check @RBM.BA.baLWMoment_of_anp
#check @RBM.BA.BAMomentGen_avg_whp
#check @RBM.BA.BAMomentGen_f_le
#check @RBM.BA.LWfgD
#check @RBM.BA.LWfgD_univ
#check @RBM.BA.LWMomentExpG
#check @RBM.BA.BALWMomentExp
#check @RBM.BA.baLWMomentOfAnp_closed
#check @RBM.BA.BALWMomentExpOfAnp
#check @RBM.BA.baLWMomentExp_of_anp
#check @RBM.BA.BAMomentExp_integrable
#check @RBM.Graph.BAAnpAuxG
#check @RBM.Graph.baAnpAuxG_holds
#check @RBM.BA.baLWMoment_closed
#check @RBM.BA.baLWMomentExp_closed
-- stage G and the BA Green data (closed): `ζ` claims, `(GiiGEX)`, `(GijGEX)`, `(GavLGEX)`, `η > 0`, the coupling window
#check @RBM.Graph.baZetaClaim_holds
#check @RBM.Graph.baEntryPsi_holds
#check @RBM.Graph.baZetaVar
#check @RBM.Graph.BAAuxGraph2_zetaSq_le
#check @RBM.Graph.baZetaExpClaim_holds
#check @RBM.BA.BAGbEXPav
#check @RBM.BA.baGbEXPav_holds
#check @RBM.BA.baGbEXPii_holds
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.baSTGiiGEXgL_holds
#check @RBM.BA.baSTGavLGEXgL_holds
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
-- the `≺` toolbox at the BA law and the BA cut algebra (L4a = T2418, L4b1 = T2434)
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_eta_pos
#check @RBM.BA.BAExp14a_eta_inv_le
#check @RBM.BA.BAExp14b_cut_true
#check @RBM.BA.BAExp14bS2
-- the L4a2 successor pins and their conditional producers (T2490); TL1, TL2 (stage TL)
#check @RBM.BA.BALWCutExpTw
#check @RBM.BA.BALWtermEXPTw
#check @RBM.BA.BALWtermEXPTwOfCut
#check @RBM.BA.BALWCutExpTwOfS2
#check @RBM.BA.BALWtermEXPTwOfS2
#check @RBM.BA.baLWtermEXPTw_of_cut
#check @RBM.BA.baLWCutExpTw_of_S2
#check @RBM.BA.baLWtermEXPTw_of_S2
#check @RBM.BA.BATwistAvgLaw
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.BATwistAvgProd
#check @RBM.BA.baTwistAvgProd_holds
-- T1-BA (T2487) and the T2386-generic consumers of the two pins (T7b = T2467)
#check @RBM.BA.baStep2_holds
#check @RBM.BA.baSTOptL2gL_holds
#check @RBM.BA.baSTGijDecgL_holds
#check @RBM.BA.stLWBgL_of_LWtermG
#check @RBM.BA.stLWTgL_of_LWtermExpG
#check @RBM.BA.Step2EventsGen_Rot3
#check @RBM.BA.Step2EventsGenTw_baRot3
-- closing condition (iv), already merged (L2c2)
#check @RBM.Graph.BAGGGamma
#check @RBM.Graph.baGGGamma_holds
-- the instance data (`Defs/Sizes`, `BA/FlowPins` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

noncomputable section

namespace RBM.BA.T2494Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- **Target 2** (`baLWterm_holds`; content binding): `lem:LWterm` at the block Anderson data for every `d`, i.e. the merged pin
`BALWterm = baPin LWtermG` (`BA/LWPinsBA.lean:45`), unchanged (one text, X1-C4).  Registry line `:221` leaves. -/
def T2494_TermClosed : Prop := ∀ d : ℕ, BALWterm d

/-- **Target 5** (`baLWtermExp_holds`; content binding): `lem: EWGn2_N` at the block Anderson data for every `d`, the merged pin
`BALWtermExp = baPin LWtermExpG` (`BA/LWPinsBA.lean:47`), unchanged.  Registry line `:222` leaves. -/
def T2494_TermExpClosed : Prop := ∀ d : ℕ, BALWtermExp d

/-- **Target 6** (`baStep2_closed`; content binding): the BA reading of Step 2 for every `d` (`BA/FlowPins.lean:432`), from
`baStep2_holds` (`BA/Step2CloseBA.lean:181`) at targets 2 and 5; the shape check of the carrier forms against T2386. -/
def T2494_Step2Closed : Prop := ∀ d : ℕ, BAStep2 d

/-- **Target 7 (a)** (`baLWCutExpTw_holds`; content binding; = `T2490_CutClosed` up to the name): the R1 cut pin for every `d`. -/
def T2494_CutClosed : Prop := ∀ d : ℕ, BALWCutExpTw d

/-- **Target 7 (b)** (`baLWtermEXPTw_holds`; content binding; = `T2490_TermClosed` up to the name): the seven-premise successor
of `BALWtermEXP` for every `d` (supervisor 2246 L40-C1 (a)). -/
def T2494_EXPClosed : Prop := ∀ d : ℕ, BALWtermEXPTw d

/-- Shape (not binding): target 6 from targets 2 and 5 through `baStep2_holds`. -/
example : Prop := T2494_TermClosed → T2494_TermExpClosed → T2494_Step2Closed

/-- Shape (not binding): the route of target 2, the Markov step and the reductions of `7_8:15-91` from the closed moment pin. -/
example : Prop := (∀ d : ℕ, BALWMoment d) → T2494_TermClosed

/-- Shape (not binding): the route of target 5 (both regimes) from the closed moment pins. -/
example : Prop := (∀ d : ℕ, BALWMoment d) → (∀ d : ℕ, BALWMomentExp d) → T2494_TermExpClosed

/-- Shape (not binding): target 7 (a) from L4b2b's producer, read at the merged type of S2 only, and the merged assembly. -/
example : Prop := (∀ d : ℕ, BAExp14bS2 d) → (∀ d : ℕ, BALWCutExpTwOfS2 d) → T2494_CutClosed

/-- Shape (not binding): target 7 (b) likewise from the merged composition `baLWtermEXPTw_of_S2`. -/
example : Prop := (∀ d : ℕ, BAExp14bS2 d) → (∀ d : ℕ, BALWtermEXPTwOfS2 d) → T2494_EXPClosed

/-- Shape (not binding): the carrier forms are the merged `baPin` readings of the generic pins of `Chain/LWGen` (T2386 shape). -/
example : Prop := ∀ d : ℕ, (BALWterm d ↔ baPin LWtermG d) ∧ (BALWtermExp d ↔ baPin LWtermExpG d)

/-- Shape (not binding) of instance 8 (a): target 2 at `d = 3`, `sz0`, `zSeq`, `t ≡ 1/2`, with `LWAssmgL` as the hypothesis. -/
example : Prop :=
  T2494_TermClosed → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
    LWAssmgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))
      (fun _ => (1 / 2 : ℝ)) ε₀ Ψ Φ C₁ C₂ C₃ Cc →
    PrecL RBM.Gauss.SizesInst.sz0 (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))
      (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (RBM.Gauss.SizesInst.sz0.L n)))
      (fun n p ω => ‖LWEg (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) n (1 / 2 : ℝ) p.1 p.2 ω‖)
      (fun n p _ => ((baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq).eta n (1 / 2 : ℝ))⁻¹ * Φ n 0 *
        Φ n ((zdistInf 3 (RBM.Gauss.SizesInst.sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

/-- Shape (not binding) of instance 8 (c): target 7 (b) at `d = 3`, `sz0`, `zSeq`, `t ≡ 1/2`, TL1 produced from `LWAvgLawgL`,
`STLmaxgL` through `baTwistAvgProd_holds 3`; TL2 and the five Step 1/2 pins stay hypotheses. -/
example : Prop :=
  T2494_EXPClosed →
    STLocalEntrygL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    LWAvgLawgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    STLmaxgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    STLKgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    STDecaygL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    BATwistLoopLaw (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    PrecL RBM.Gauss.SizesInst.sz0 (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))
      (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (RBM.Gauss.SizesInst.sz0.L n)) //
        RBM.Gauss.SizesInst.sz0.lam n ^ 2 / ((RBM.Gauss.SizesInst.sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)})
      (fun n p _ => ‖∫ ω, LWEg (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) n (1 / 2 : ℝ) p.1.1 p.1.2 ω
        ∂(Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))‖)
      (fun n _ _ => (1 - (1 / 2 : ℝ))⁻¹ * (RBM.Gauss.SizesInst.sz0.Bctl n (1 / 2 : ℝ)) ^ (5 / 2 : ℝ))

end RBM.BA.T2494Check

end
