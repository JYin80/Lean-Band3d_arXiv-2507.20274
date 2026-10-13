/-
Release check for T2490 (dispatcher V3, 2026-10-13 04:47 UTC; DECISIONS §292).  BA-L L4a2 `BAExp14a2`: `lem:LWterm_EXP` at the block Anderson data,
i.e. the reduction `LWE → LWcut` over the BA carrier (twin of `lwTermEXP_of_cut`, `Graph/LWExpTerm.lean:286`) and the assembly of S1–S3
into the R1 cut pin `BALWCutExpTw` (twin of `lwCutExp_of_terms`, `Graph/LWExpTerm2.lean:1956`), in the new file `Graph/BAExp14a2`.
S2 (L4b2 = T2489) is not merged: it enters as the merged pin `BAExp14bS2` (`Graph/BAExp14b.lean:170`), antecedent of exact type (UBA-C3).
No design gate, no probe step: the cut pins are copied verbatim from the probe `t/T2398:RBM3D/Probe/T2398Pins.lean:413-440` (6429bb5).
Part 1: merged names (`main` 4270f377).  Part 2: the target statements (prefix `T2490_`; content binding up to the name), then shapes
(not binding; fixed at the 1a).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2490-check.lean
-/
import RBM3D.Chain.Carrier
import RBM3D.Chain.LWGen
import RBM3D.BA.FlowPins
import RBM3D.BA.LWPinsBA
import RBM3D.BA.TwistPins
import RBM3D.BA.TwistAvgB
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistChain
import RBM3D.Graph.LWExpTerm
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWExpTerm6
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.BAExp14b
import RBM3D.Graph.BAExp14bB
import RBM3D.Graph.BAExp14c
import RBM3D.Graph.BAExp14cB
import RBM3D.Graph.BAExp14e

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- band: the cut, the term, `≺ → 𝔼`, the reduction and the assembly (`Graph/LWPins`, `LWExpTerm`, `LWExpTerm2`, `LWExpTerm6`)
#check @RBM.Gauss.Sizes.LWcut
#check @RBM.Gauss.Sizes.LWE
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.Sizes.LWCutExp
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral
#check @RBM.Gauss.Sizes.lwTermEXP_of_cut
#check @RBM.Gauss.Sizes.lwCutExp_of_terms
#check @RBM.Gauss.Sizes.lwCutExp_holds
#check @RBM.Gauss.Sizes.lwTermEXP_holds
-- the carrier and the generic light-weight pins (`Chain/Carrier`, `Chain/LWGen`); the BA reading (`BA/LWPinsBA`)
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.PrecL_congr
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.LWcutg
#check @RBM.BA.LWEg
#check @RBM.BA.LWtermEXPG
#check @RBM.BA.LWtermEXP_iff
#check @RBM.BA.PinFam
#check @RBM.BA.bandPin
#check @RBM.BA.baPin
#check @RBM.BA.BALWtermEXP
#check @RBM.BA.band_LWtermEXPG
-- the BA data (`BA/FlowPins`)
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baFMz
-- S1 (L4a = T2418); the pins S2, S3, the identity and the conjugation (L4b1 = T2434); the S3 producer (L4c1 = T2464, L4g = T2465)
#check @RBM.BA.BAExp14aS1Fam
#check @RBM.BA.BAExp14aS1
#check @RBM.BA.baExp14a_S1_holds
#check @RBM.BA.BAExp14bS2Fam
#check @RBM.BA.BAExp14bS3Fam
#check @RBM.BA.BAExp14bS2
#check @RBM.BA.BAExp14bS3
#check @RBM.BA.BAExp14bExpand
#check @RBM.BA.BAExp14bCutConj
#check @RBM.BA.baExp14b_expand_holds
#check @RBM.BA.baExp14b_cut_conj
#check @RBM.BA.BAExp14b_cut_true
#check @RBM.BA.BAExp14bS3OfLeaf
#check @RBM.BA.baExp14bS3_of_leaf
#check @RBM.BA.baExp14bS3_holds
-- stage TL (TL0 = T2421 `BA/TwistPins`; closed): the TL1 producer at a fixed time; TL2 only through the chain of times
#check @RBM.BA.BATwistAvgLaw
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.BATwistAvgProd
#check @RBM.BA.baTwistAvgProd_holds
#check @RBM.BA.TwistStep2_tl1
#check @RBM.BA.BATwistLoopBase
#check @RBM.BA.baTwistLoopBase_holds
#check @RBM.BA.baTwistLoopStep_caseI
#check @RBM.BA.BAMainIndTL
#check @RBM.BA.BAMLOutTL
#check @RBM.BA.BAChainTL
#check @RBM.BA.baChainTL_holds
-- the `≺` toolbox and integrability at the BA law (L4a, `Graph/BAExp14a`, `BAExp14aB`)
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_prec_fin
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_μ
#check @RBM.BA.BAExp14a_integrable
#check @RBM.BA.BAExp14a_cont_G
#check @RBM.BA.BAExp14a_G_le
#check @RBM.BA.BAExp14a_eta_inv_le
#check @RBM.StochDomAt.precomp_param
-- the instance data (`Defs/Sizes`, `BA/FlowPins` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

noncomputable section

namespace RBM.BA.T2490Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- **Target 1 (a)** `LWCutExpG` (content binding; probe 413-424 verbatim up to the name): `LWCutExp` (`LWExpTerm.lean:52`) over a carrier
family, in the `(law, Flow, mk, T0)` shape of `LWtermEXPG` (`Chain/LWGen.lean:108`), five premises.  Merged docstrings already cite it
(`BAExp14b:179, 961`, `BAExp14e:346`). -/
def T2490_LWCutExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        STLocalEntrygL (mk sz z) (law sz) t → LWAvgLawgL (mk sz z) (law sz) t → STLmaxgL (mk sz z) (law sz) t →
        STLKgL (mk sz z) (law sz) t → STDecaygL (mk sz z) (law sz) t →
        PrecL sz (law sz) (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWcutg (mk sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂(law sz)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **Target 1 (b)** `BALWCutExpTw` (content binding; probe 434-440 verbatim up to the name; one text, X1-C4): the BA cut pin under R1, the
five premises of `LWCutExpG` at the BA data and TL1, TL2 as premises 6–7, the conclusion of `LWCutExpG`.  The consumer named in `BAExp14aB:18`,
`BAExp14b:15, 168` and `T2465.md:18`; the conclusion of the assembly (target 3). -/
def T2490_BALWCutExpTw (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, LWcutg (baFMz sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **Target 1 (c)** `BALWtermEXPTw` (content binding; new): the seven-premise successor of the merged `BALWtermEXP` (`BA/LWPinsBA.lean:49`,
`baPin LWtermEXPG`, five premises; supervisor 2246 L40-F2): `LWtermEXPG` written out at law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier
`baFMz`, horizon `BAflowT0`, with TL1, TL2 in the slots they have in `T2490_BALWCutExpTw`.  The merged `BALWtermEXP` is not changed. -/
def T2490_BALWtermEXPTw (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **Target 1 (d)**, statement def (content binding): the reduction `LWE → LWcut` at the BA data (pattern `BALWMomentOfAnp`,
`BAMomentGenB:362`: the antecedent sits inside the def, so no public result has a pin binder). -/
def T2490_BALWtermEXPTwOfCut (d : ℕ) : Prop := T2490_BALWCutExpTw d → T2490_BALWtermEXPTw d

/-- **Target 1 (d)**, statement def (content binding): the assembly with S2 as exact-type antecedent (UBA-C3; pattern `BAExp14bS3OfLeaf`,
`BAExp14c:915`). -/
def T2490_BALWCutExpTwOfS2 (d : ℕ) : Prop := BAExp14bS2 d → T2490_BALWCutExpTw d

/-- **Target 1 (d)**, statement def (content binding): the composition read at the terminal. -/
def T2490_BALWtermEXPTwOfS2 (d : ℕ) : Prop := BAExp14bS2 d → T2490_BALWtermEXPTw d

/-- **Target 1 (a), band check** (`band_LWCutExpG`; content binding): the generic cut pin at the band carrier, the merged band result
`lwCutExp_holds 3` transported through the bridge of the probe (probe 427), as `band_LWtermEXPG` (`BA/LWPinsBA.lean:59`). -/
def T2490_BandCut : Prop := bandPin T2490_LWCutExpG 3

/-- **Target 2** (`baLWtermEXPTw_of_cut`; content binding): the reduction for every `d`. -/
def T2490_Reduction : Prop := ∀ d : ℕ, T2490_BALWtermEXPTwOfCut d

/-- **Target 3** (`baLWCutExpTw_of_S2`; content binding): the assembly for every `d`, from S1, S3, the identity and the antecedent S2. -/
def T2490_Assembly : Prop := ∀ d : ℕ, T2490_BALWCutExpTwOfS2 d

/-- **Target 4** (`baLWtermEXPTw_of_S2`; content binding): the composition for every `d` (consumers: L6 in the last terminal ticket, V1-BA). -/
def T2490_TermOfS2 : Prop := ∀ d : ℕ, T2490_BALWtermEXPTwOfS2 d

/-- **Target 5** (`baLWCutExpTw_holds`; content binding; only under the start decision "T2489 merged"). -/
def T2490_CutClosed : Prop := ∀ d : ℕ, T2490_BALWCutExpTw d

/-- **Target 5** (`baLWtermEXPTw_holds`; content binding; only under the start decision "T2489 merged"). -/
def T2490_TermClosed : Prop := ∀ d : ℕ, T2490_BALWtermEXPTw d

/-- Shape (not binding): the band bridge of the probe (probe 427), stated here only. -/
example : Prop := ∀ d : ℕ, LWCutExp d ↔ bandPin T2490_LWCutExpG d

/-- Shape (not binding): target 4 from targets 2 and 3. -/
example : Prop := T2490_Reduction → T2490_Assembly → T2490_TermOfS2

/-- Shape (not binding): the closures of target 5 from L4b2's producer, read at the merged type of S2 only. -/
example : Prop := (∀ d : ℕ, BAExp14bS2 d) → T2490_Assembly → T2490_CutClosed

/-- Shape (not binding): as above for the successor pin. -/
example : Prop := (∀ d : ℕ, BAExp14bS2 d) → T2490_TermOfS2 → T2490_TermClosed

/-- Shape (not binding): the inputs of the assembly next to each other; all but S2 have a merged producer
(`baExp14a_S1_holds`, `baExp14bS3_holds`, `baExp14b_expand_holds`, `baExp14b_cut_conj`). -/
example : Prop :=
  (∀ d : ℕ, BAExp14aS1 d) ∧ (∀ d : ℕ, BAExp14bS3 d) ∧ (∀ d : ℕ, BAExp14bExpand d) ∧
    (∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ), BAExp14bCutConj sz z) ∧ (∀ d : ℕ, BAExp14bS2 d → T2490_BALWCutExpTw d)

/-- Shape (not binding): the five-premise cut pin at the BA data implies the R1 pin (the two extra premises are unused); `BALWCutExp`
(probe 431) itself is not added. -/
example : Prop := ∀ d : ℕ, baPin T2490_LWCutExpG d → T2490_BALWCutExpTw d

/-- Shape (not binding) of instance 6 (c): at `d = 3`, `sz0`, `zSeq`, `t ≡ 1/2`, the R1 cut pin with TL1 produced from `hA`, `hM` through
`baTwistAvgProd_holds 3` (TL1 discharged through its producer); only TL2 and the five Step 1/2 pins stay hypotheses. -/
example : Prop :=
  T2490_BALWCutExpTw 3 →
    STLocalEntrygL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    LWAvgLawgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    STLmaxgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    STLKgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    STDecaygL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    BATwistLoopLaw (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) (fun _ => (1 / 2 : ℝ)) →
    PrecL RBM.Gauss.SizesInst.sz0 (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))
      (U := fun n => {_p : (Bool × Bool) × (Zd 3 (RBM.Gauss.SizesInst.sz0.L n) × Zd 3 (RBM.Gauss.SizesInst.sz0.L n)) //
        RBM.Gauss.SizesInst.sz0.lam n ^ 2 / ((RBM.Gauss.SizesInst.sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)})
      (fun n p _ => ‖∫ ω, LWcutg (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) n (1 / 2 : ℝ) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω
        ∂(Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))‖)
      (fun n _ _ => (1 - (1 / 2 : ℝ))⁻¹ * (RBM.Gauss.SizesInst.sz0.Bctl n (1 / 2 : ℝ)) ^ (5 / 2 : ℝ))

end RBM.BA.T2490Check

end
