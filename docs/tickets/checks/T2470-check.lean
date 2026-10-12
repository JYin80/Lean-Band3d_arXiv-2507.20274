/-
Release check for T2470 (dispatcher V3, Mon Oct 12 18:07 UTC 2026; DECISIONS §274).  BA-L L3d2 `BAMomentGen`: `lem:LW_moment` at BA, twin of
`Graph/LWMoment.lean` `:1-1872` in new files (T2387 §6 row L3d2 `:143`; the `LWMomentExp` half is L3d2b, ticket Dispatcher notes (b)).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2470_`; the 1b names them `LWfg_bandFM`, `LWMomentG`,
`LWMoment_iff_bandPin`, `BALWMoment`, `ba_localregularX_holds`, `BALWMomentOfAnp`, `baLWMoment_of_anp`, or as the 1a fixes; content binding,
up to the name and the unfolding of the carrier `f_xy`), the path binder verbatim, and shapes (not binding).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2470-check.lean
-/
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWMomentExpA
import RBM3D.Graph.LWMomentExp
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.BAEngine
import RBM3D.Graph.BAShapeO2B
import RBM3D.Graph.BALocReg1B
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BAZetaExp
import RBM3D.Graph.BASizeClaim2
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BAExp14aB
import RBM3D.Chain.LWGen
import RBM3D.BA.LWPinsBA
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenLDE
import RBM3D.BA.GreenSchur
import RBM3D.BA.GbEXPav
import RBM3D.BA.Step1Boot
import RBM3D.Propagator.Props4

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band basis (`Graph/LWMoment`, `Graph/LWPins`): the pin, `f_xy`, the target and its parts
#check @RBM.Gauss.Sizes.LWMoment
#check @RBM.Gauss.Sizes.LWf
#check @RBM.Gauss.Sizes.LWS
#check @RBM.Gauss.Sizes.STGM
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.LWAssm
#check @RBM.Gauss.Sizes.LWMomentCtx
#check @RBM.Gauss.Sizes.lwMoment_holds
#check @RBM.Gauss.Sizes.lwMoment_expand
#check @RBM.Gauss.Sizes.lwMoment_prec_far
#check @RBM.Gauss.Sizes.lwMoment_prec_far_r
#check @RBM.Gauss.Sizes.lwMoment_prec_anp
#check @RBM.Gauss.Sizes.lwMoment_prec_scale
#check @RBM.Gauss.Sizes.lwMoment_prec_err
#check @RBM.Gauss.Sizes.lwMoment_prec_int
#check @RBM.Gauss.Sizes.lwMoment_prec_near
#check @RBM.Gauss.Sizes.lwMoment_prec_near_pre
#check @RBM.Gauss.Sizes.lwMoment_f_le
#check @RBM.Gauss.Sizes.lwMoment_avg_whp
#check @RBM.Gauss.Sizes.lwMoment_env
#check @RBM.Gauss.Sizes.lwMoment_floor
#check @RBM.Gauss.Sizes.lwMoment_decay
#check @RBM.Graph.lwMoment_val_smul
#check @RBM.Graph.lwMoment_fxy_bridge
-- band results imported as is (model-free, or generic in the matrix)
#check @RBM.Gauss.Sizes.lwMoment_phi_facts
#check @RBM.Gauss.Sizes.lwMoment_anp_arith
#check @RBM.Gauss.Sizes.lwMoment_near_arith
#check @RBM.Gauss.Sizes.lwMoment_rad
#check @RBM.Gauss.Sizes.lwMoment_ward_col
#check @RBM.Gauss.Sizes.lwMoment_CS
#check @RBM.Graph.lwXiRad_holds
#check @RBM.Graph.fxyVal
#check @RBM.Graph.fxyPowGraph
-- the band pipeline the basis calls (each has a BA twin on `main`, target 4's input table)
#check @RBM.Graph.LWLocRegConcl
#check @RBM.Graph.lw_localregularX
#check @RBM.Graph.lwGtoAG_holds
#check @RBM.Graph.lwAuxNested_holds
#check @RBM.Graph.lwAnp_holds
#check @RBM.Graph.lwXiClaim_holds
#check @RBM.Graph.lwGbyXi_holds
#check @RBM.Graph.lwEntryPsi_holds
#check @RBM.Graph.lwScalemole_holds
#check @RBM.Green.stGbEXP_holds
#check @RBM.Graph.fxyPowGraph_val_eq
#check @RBM.Graph.fxyPowGraph_nM
-- consumers: L5 (`lwterm_holds`), L3d2b (regime (A) and the `LWMomentExp` half; not here)
#check @RBM.Gauss.Sizes.lwterm_holds
#check @RBM.Graph.lwMomExpNoExp_holds
#check @RBM.Gauss.Sizes.LWMomentExp
#check @RBM.Gauss.Sizes.lwMomentExp_holds
#check @RBM.Graph.LWMomentExpOfParts
#check @RBM.Graph.LWfD
-- the carrier and L0 (`Chain/Carrier`, `Chain/LWGen`, `BA/LWPinsBA`, `BA/FlowPins`)
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.FlowFM.eta
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAmF
#check @RBM.BA.PinFam
#check @RBM.BA.bandPin
#check @RBM.BA.baPin
#check @RBM.BA.LWAssmgL
#check @RBM.BA.LWLoop2gL
#check @RBM.BA.STInitialGT2gL
#check @RBM.BA.band_LWAssm
#check @RBM.BA.LWtermG
#check @RBM.BA.LWterm_iff
#check @RBM.BA.BALWterm
#check @RBM.SB
#check @RBM.SBR
#check @RBM.SB_eq_map_SBR
#check @RBM.Gauss.svarF
-- L3d3 (T2448, `Graph/BAEngine`): the conclusion, the engine with its binder, the black waved edges
#check @RBM.Graph.BALocRegConcl
#check @RBM.Graph.ba_localregularX
#check @RBM.Graph.baEngine_assemble
#check @RBM.Graph.baStart_nWS
#check @RBM.Graph.ba_nWS_ge
-- L3b4″ (T2447, `Graph/BAShapeO2B`): the three shape results that discharge the engine's binder (O2R-C3)
#check @RBM.Graph.baShapeLL_e2_tn
#check @RBM.Graph.baShapeLL_macroA_tn
#check @RBM.Graph.baShapeLL_macroB_tn
#check @RBM.Graph.baLocReg6_holds
#check @RBM.Graph.BALocReg6
#check @RBM.Graph.BAShapeLL
#check @RBM.Graph.BAFrameStepTN
#check @RBM.Graph.BAShape.e2
#check @RBM.Graph.BAShape.macroA
#check @RBM.Graph.BAShape.macroB
-- L3b1 (T2456, `Graph/BALocReg1`, `BALocReg1B`): (1)-(5) along `BAReach` with the path binder, the start bound, the value identity
#check @RBM.Graph.BALocReg15
#check @RBM.Graph.baLocReg15_holds
#check @RBM.Graph.baStart_nM_le
#check @RBM.Graph.ba_fxyPow_integral_eq
#check @RBM.Graph.BAShapePath
#check @RBM.Graph.baShapePath_s1_tn
#check @RBM.Graph.baShapePath_e1_tn
#check @RBM.Graph.baShadow_locReg345
#check @RBM.Graph.BALocReg1_mol_of_atom
-- L3c1 (T2420, `Graph/BAAtom`, `BAAtom2`): G3, the tail, the nested aux graph, G4 (band-flow form)
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_holds
#check @RBM.Graph.baGtoAG_E
#check @RBM.Graph.BAAtom_decay_E
#check @RBM.Graph.BAAtom_term_tail
#check @RBM.Graph.BAAtom_tail_sum
#check @RBM.Graph.baAuxNested_holds
#check @RBM.Graph.BAAnpAux
#check @RBM.Graph.baAnpAux_holds
#check @RBM.Graph.BAShadowPG
#check @RBM.Graph.BAGraph.shadow
#check @RBM.Graph.BAGraph.auxVal
#check @RBM.Graph.BAGraph.auxOrd
-- L3c3a (T2435, `Graph/BAAuxGraph2`, `BAAuxGraph2B`): ζ, the claim, `(eq:Gbyxi2_BA)`, the entry bound, G4 on the BA carrier (L3d1's pin)
#check @RBM.Graph.baZetaVar
#check @RBM.Graph.LWXigL
#check @RBM.Graph.BAZetaClaim
#check @RBM.Graph.baZetaClaim_holds
#check @RBM.Graph.BAGbyZeta
#check @RBM.Graph.baGbyZeta_holds
#check @RBM.Graph.BAEntryPsi
#check @RBM.Graph.baEntryPsi_holds
#check @RBM.Graph.BAAnpAuxG
-- L3c3b (T2444, `Graph/BAZetaExp`): not read in this row (consumer L3d2b)
#check @RBM.Graph.BAZetaExpClaim
#check @RBM.Graph.baZetaExpClaim_holds
#check @RBM.Graph.LWXiEgL
-- L3c2 (T2412, `Graph/BASizeClaim`, `BASizeClaim2`): kernel bounds, the size claim, tails
#check @RBM.Graph.baKBound_E
#check @RBM.Graph.baClaimSize_E
#check @RBM.Graph.baMTail_E
#check @RBM.Graph.baSpTail_E
-- L4a (T2418, `Graph/BAExp14a`, `BAExp14aB`): the slice transport, `X_c = 𝓛^{(1)}_c - m`, the ≺ → 𝔼 kit
#check @RBM.BA.BAExp14a_slc
#check @RBM.BA.BAExp14a_int_slice
#check @RBM.BA.BAExp14a_sumS_GM
#check @RBM.BA.BAExp14a_X_eq
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_floor
#check @RBM.BA.BAExp14a_cont_lwG
-- stage G and the flow facts (G6b = T2422; `BA/GreenLDE`, `BA/GreenSchur`, `BA/Ward`)
#check @RBM.BA.baGbEXPav_holds
#check @RBM.BA.BAGavLGEX
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAGt_eq_green
#check @RBM.BA.BASelf
-- graphs and data
#check @RBM.Graph.BAlwData
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAReach
#check @RBM.Graph.atomSetoid
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.BAComb.val
#check @RBM.Gauss.PF
-- premise-scan producers (`Test/Axioms.lean:390-445`)
#check @RBM.Graph.BAEngine_pL_locStd
#check @RBM.Graph.localReg2_inst_Q_locReg345
-- the `d = 3` instance data (`BA/FlowPins.lean` §Inst, `BA/LWPinsBA.lean` §3)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: the target statements (Prop values; no proof) -/

noncomputable section

namespace RBM.BA.T2470Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- Target 1 (a) (`LWfg_bandFM`): at the band carrier the carrier `f_{xy}` is the merged `LWf` (`Graph/LWPins.lean:199`).  The 1b's
`LWfg C n t ω x y` is the sum on the left with `C` in place of `bandFM sz E`: block kernel `C.S` with the factor `W^{-d}`, `Ǧ = C.GM`, `G = C.G`
(at `bandFM`: `SB_eq_map_SBR`; `GM = STGM`). -/
def T2470_LWfgBand : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    (∑ α, if α = x ∨ α = y then (0 : ℂ) else
      ∑ β, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (bandFM sz E).S n (STblk sz n α) (STblk sz n β)) *
        (bandFM sz E).GM n t ω β β * (bandFM sz E).G n t ω x α * (bandFM sz E).G n t ω α y) =
      LWf sz n (E n) t ω x y

/-- Target 2 (`LWMomentG`): `lem:LW_moment` (`Graph/LWPins.lean:325`) over a carrier family, in the `PinFam` shape of `LWtermG`
(`Chain/LWGen.lean:79`): `STFlow` → `Flow`, `lemT` → `T0`, `LWAssm` → `LWAssmgL (mk sz z) (law sz)`, `Prec` → `PrecL sz (law sz)`,
`LWf` → the carrier `f_{xy}` of target 1, `etaT` → `(mk sz z).eta`; the rest verbatim (`c` before `𝔠`). -/
def T2470_LWMomentG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ),
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
            ∀ (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
              LWAssmgL (mk sz z) (law sz) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
              PrecL sz (law sz) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
                (fun n q _ => ∫ ω, ‖∑ α, (if α = q.1 ∨ α = q.2 then (0 : ℂ) else
                    ∑ β, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mk sz z).S n (STblk sz n α) (STblk sz n β)) *
                      (mk sz z).GM n (t n) ω β β * (mk sz z).G n (t n) ω q.1 α * (mk sz z).G n (t n) ω α q.2)‖ ^ p ∂(law sz))
                (fun n q _ => (((mk sz z).eta n (t n))⁻¹ * Φ n 0 *
                  Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))) ^ p)

/-- Target 2 (`LWMoment_iff_bandPin`): the band instance of the generic pin is the merged pin (a result through target 1 (a), not definitional). -/
def T2470_MomentBand : Prop :=
  ∀ d : ℕ, LWMoment d ↔ bandPin T2470_LWMomentG d

/-- Target 2 (`BALWMoment`): the BA reading (law `seqP (sz.withLam 0)`, `BAFlow`, `baFMz`, `BAflowT0`), beside `BALWterm` (`BA/LWPinsBA.lean:45`). -/
def T2470_BALWMoment (d : ℕ) : Prop := baPin T2470_LWMomentG d

/-- Target 3 (`ba_localregularX_holds`): the conclusion of `ba_localregularX` (`BAEngine:335`) without its binder (supervisor 0948 O2R-C3:
discharged from T2447's `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn`). -/
def T2470_LocRegXHolds : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)

/-- The path binder of `baLocReg15_holds` (`BALocReg1B.lean:264`), verbatim (DECISIONS §269 (7), O2R-C3 pattern): the first hypothesis of
target 4 while T2469 (L3b2) is not merged; never restated as a new `Prop`, no owed registry line. -/
def T2470_PathBinder : Prop :=
  ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN

/-- Target 4, the statement def (`BALWMomentOfAnp`): `lem:LW_moment` at BA from G4 on the BA carrier (`BAAnpAuxG`, `BAAuxGraph2B:865`, the
pin of L3d1).  `BAAnpAuxG` occurs only here, as the antecedent of a statement def (the premise scan is unchanged). -/
def T2470_MomentOfAnp (d : ℕ) : Prop := BAAnpAuxG d → T2470_BALWMoment d

/-- Target 4 (`baLWMoment_of_anp`) when T2469 is not merged at the 1b start: the path binder first. -/
def T2470_Moment : Prop := T2470_PathBinder → ∀ d : ℕ, T2470_MomentOfAnp d

/-- Target 4 when T2469 has merged at the 1b start (its shape results discharge the binder). -/
def T2470_MomentClosed : Prop := ∀ d : ℕ, T2470_MomentOfAnp d

/-- Statement level (not binding): the route of target 3 (`ba_localregularX` with the three shape inputs), of target 4 under each decision. -/
example : Prop := (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) → T2470_LocRegXHolds
example : Prop := T2470_LocRegXHolds → BALocReg15 → T2470_MomentClosed
example : Prop := T2470_LocRegXHolds → (T2470_PathBinder → BALocReg15) → T2470_Moment
example : Prop := T2470_LWfgBand → T2470_MomentBand

/-- Shape (not binding) of the private composition (supervisor 1152 `:189-192`): the conclusion of the engine (`(a)` and `(c)`) with the
contract (1)-(5) along `BAReach` gives, at every output, `LocStd`, `2p ≤ ord`, `n_M ≤ p` and (3)-(5) on the shadow: the premises of
`baAuxNested_holds` (`BAAtom2:647`) and `BAAnpAuxG` (`BAAuxGraph2B:865`). -/
example : Prop :=
  BALocReg15 → ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))), BALocRegConcl p c K0 d D outs errs →
    ∀ Q ∈ outs, Q.g.LocStd ∧ 2 * (p : ℤ) ≤ Q.scalingOrder ∧ Q.g.nM ≤ p ∧ (BAShadowPG Q).LocReg345 p

/-- Shape (not binding) of target 1 (b), the twin of `lwMoment_fxy_bridge` (`LWMoment:79`): at the BA carrier, `t` times the carrier `f_{xy}`
is `fxyVal` at the graph data `BAlwData` (`S = t·svarF(0)`, `S^{(B)}(0) = I`) of the slice of the sample. -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    (t : ℂ) * (∑ α, if α = x ∨ α = y then (0 : ℂ) else
      ∑ β, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) *
        (baFMz sz z).GM n t ω β β * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y) =
      fxyVal (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData x y

/-- Shape (not binding) of the near-pair step at BA, the twin of `lwMoment_f_le` (`LWMoment:1492`): the max bound `(eq:boundfxyGinf)`
with `X_c = 𝓛^{(1)}_c - m` (`BAExp14a_sumS_GM`, `BAExp14a_X_eq`) and Ward for the BA resolvent (`BAGt_eq_green`). -/
example : Prop :=
  ∀ {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (A μ : ℝ),
      (∀ b : Zd d (sz.L n), ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => b) ω - (baFMz sz z).m n‖ ≤ μ) →
      (∀ x : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).G n t ω x x‖ ≤ A) →
      ∀ x y : Idx d (sz.L n) (sz.W n),
        ‖∑ α, (if α = x ∨ α = y then (0 : ℂ) else
          ∑ β, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) *
            (baFMz sz z).GM n t ω β β * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)‖ ≤
          A / (baFMz sz z).eta n t * μ

/-- Target 2 beside its band original at `d = 3` (instance (ii) transports `lwMoment_holds 3`). -/
example : Prop := LWMoment 3 ∧ bandPin T2470_LWMomentG 3

/-- Shape (not binding) of instance (iii): target 4 at `d = 3`; at the data of `BA/LWPinsBA.lean` §3 the hypotheses left are `BAAnpAuxG 3`,
the path binder (decision (i)), and `STInitialGT2gL`, `LWLoop2gL` inside `LWAssmgL`. -/
example : Prop := T2470_PathBinder → BAAnpAuxG 3 → T2470_BALWMoment 3

/-- Shape (not binding) of instance (i): target 3 at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10` with nonempty lists. -/
example : Prop := ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧ outs ++ errs ≠ [] ∧
  ∀ Q ∈ outs ++ errs, 2 ≤ Q.g.waved.countP (fun e => !e.col)

end RBM.BA.T2470Check

end
