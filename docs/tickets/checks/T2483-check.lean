/-
Release check for T2483 (dispatcher V3, Tue Oct 13 00:45 UTC 2026; DECISIONS §283).  BA-L L3d2b `BAMomentExpGen`: the `LWMomentExp` half of `lem:LW_moment_exp` at BA
(successor of L3d2a = T2470), twin of `Graph/LWMomentExp.lean` (`:1-1509`), `Graph/LWMomentExpA.lean` (`:1-460`) and `Graph/AuxGraphRooted.lean`
(`:1-569`) in new files `Graph/BAMomentExpGen`, `Graph/BAMomentExpGenB`; basis: the interface table of `docs/reports/T2472-1a-audit.md` §7.
Part 1: merged names (the band basis, the merged BA inputs, the instance data).  Part 2: the target statements that merged names fix (prefix
`T2483_`; content binding up to the name and the unfolding of the carrier `LWfgD`, `BAGraph.valW` and the packing), then shapes (not binding; the
1a fixes them from the band texts).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2483-check.lean
-/
import RBM3D.Graph.LWMomentExp
import RBM3D.Graph.LWMomentExpA
import RBM3D.Graph.AuxGraphRooted
import RBM3D.Graph.LWProv
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.BAMomentGen
import RBM3D.Graph.BAMomentGenB
import RBM3D.Graph.BAProv
import RBM3D.Graph.BAProvB
import RBM3D.Graph.BALocReg2B
import RBM3D.Graph.BAZetaExp
import RBM3D.Graph.BAExp14d
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BASizeClaim2
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BAExp14aB
import RBM3D.Chain.LWGen
import RBM3D.BA.LWPinsBA
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenLDE
import RBM3D.BA.CombesThomas

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band target and its carrier vocabulary (`Graph/LWPins`, `Graph/LWProv`)
#check @RBM.Gauss.Sizes.LWMomentExp
#check @RBM.Gauss.Sizes.LWAssmExp
#check @RBM.Gauss.Sizes.LWf
#check @RBM.Gauss.Sizes.lwMomentExp_holds
#check @RBM.Graph.LWfD
#check @RBM.Graph.LWfD_union
#check @RBM.Graph.LWEngineProv
#check @RBM.Graph.lw_localregularXP
-- the band basis `Graph/LWMomentExp.lean` (public names; the private `_prec_err`, `_prec_scale`, `_rep`, `_prec_anp`, `_env`, `_comb` are twinned)
#check @RBM.Graph.domFar
#check @RBM.Graph.domNearA
#check @RBM.Graph.domNearB
#check @RBM.Graph.domFar_eq
#check @RBM.Graph.dom_union
#check @RBM.Graph.dom_disj
#check @RBM.Graph.LWf_split
#check @RBM.Graph.norm_add3_pow_le
#check @RBM.Graph.LWMomentExpOn
#check @RBM.Graph.LWMomExpFarPin
#check @RBM.Graph.LWMomExpNearPin
#check @RBM.Graph.LWMomentExpOfParts
#check @RBM.Graph.lwMomentExp_integrable
#check @RBM.Graph.lwMomentExp_of_parts
#check @RBM.Graph.lwMomentExp_valW_smul
#check @RBM.Graph.lwMomentExp_pvalW_smul
#check @RBM.Graph.lwMomentExp_valW_norm_le
#check @RBM.Graph.lwMomentExp_claimSize
#check @RBM.Graph.lwMomentExp_scalemole
#check @RBM.Graph.lwMomentExp_wt
#check @RBM.Graph.lwMomentExp_wt_abs
#check @RBM.Graph.lwMomentExp_expand
#check @RBM.Graph.lwMomentExp_phi_zero
#check @RBM.Graph.lwMomentExp_assm
#check @RBM.Graph.lwMomentExp_R
#check @RBM.Graph.lwMomentExp_pval_claim
#check @RBM.Graph.lwMomentExp_eta_le
#check @RBM.Graph.lwMomentExp_logW
#check @RBM.Graph.lwMomentExp_LWfD_zero
#check @RBM.Graph.lwMomentExp_pin_gen
#check @RBM.Graph.lwMomentExp_farPin_holds
#check @RBM.Graph.lwMomentExp_nearPin_holds
#check @RBM.Graph.lwMomentExp_inst_nonempty
-- model-free parts of the basis, imported as is (NGraph pins, floor, radius, arithmetic)
#check @RBM.Graph.lwMomentExp_zpow_cmp
#check @RBM.Graph.lwMomentExp_PsiT_le
#check @RBM.Graph.lwMomentExp_PinN
#check @RBM.Graph.lwMomentExp_pinN_far
#check @RBM.Graph.lwMomentExp_pinN_near
#check @RBM.Graph.lwMomentExp_valOn_floor
#check @RBM.Graph.lwMomentExp_valOn_smul
#check @RBM.Graph.lwMomentExp_rad
#check @RBM.Graph.lwMomentExp_arith
#check @RBM.Graph.AnpFarAndAt
#check @RBM.Graph.AnpFarAnd
#check @RBM.Graph.lwMomExpFar_and
#check @RBM.Graph.lwMomExpFar_ownExt
#check @RBM.Graph.lwMomExpFar_farDAnd
#check @RBM.Graph.AnpNearInfAt
#check @RBM.Graph.AnpNearInf
#check @RBM.Graph.lwMomExp_nearInf
#check @RBM.Graph.LWXiExpClaim
#check @RBM.Graph.lwXiExpClaim_holds
#check @RBM.Graph.lwTail32
#check @RBM.Graph.lwXE_phi
#check @RBM.Gauss.Sizes.LWMomentCtx
#check @RBM.Gauss.Sizes.lwMoment_prec_of_whp
#check @RBM.Gauss.Sizes.lwMoment_sum_det
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral
-- regime (A) `Graph/LWMomentExpA.lean` (the deterministic `lwMEA_*` are private)
#check @RBM.Graph.regA
#check @RBM.Graph.LWMomExpNoExpF
#check @RBM.Graph.lwMomExpNoExp_holds
-- the rooted `GtoAG` `Graph/AuxGraphRooted.lean`
#check @RBM.Graph.auxValOn
#check @RBM.Graph.lwAuxRoot_auxValOn_const
#check @RBM.Graph.lwAuxRoot_exists_forest
#check @RBM.Graph.lwAuxRoot_main_sum
#check @RBM.Graph.LWGtoAGRooted
#check @RBM.Graph.lwGtoAGRooted_holds
#check @RBM.Graph.lwAuxRoot_val_eq_on
#check @RBM.Graph.LWAuxNestedOwnOn
#check @RBM.Graph.lwAuxNestedOwnOn_holds
#check @RBM.Graph.lwAuxRoot_exists_rep
-- L3d2a = T2470 (`Graph/BAMomentGen`, `BAMomentGenB`): carrier, generic pin, BA reading, target 4, public tools reused here
#check @RBM.BA.LWfg
#check @RBM.BA.LWfg_bandFM
#check @RBM.BA.LWfg_baFMz
#check @RBM.BA.LWMomentG
#check @RBM.BA.LWMoment_iff_bandPin
#check @RBM.BA.BALWMoment
#check @RBM.BA.ba_localregularX_holds
#check @RBM.BA.BALWMomentOfAnp
#check @RBM.BA.baLWMoment_of_anp
#check @RBM.BA.BAMomentGen_consts
#check @RBM.BA.BAMomentGen_decay
#check @RBM.BA.BAMomentGen_D
#check @RBM.BA.BAMomentGen_R
#check @RBM.BA.BAMomentGen_tail
#check @RBM.BA.BAMomentGen_Wneg_le
#check @RBM.BA.BAMomentGen_scalemole
#check @RBM.BA.BAMomentGen_prec_scale
#check @RBM.BA.BAMomentGen_prec_err
#check @RBM.BA.BAMomentGen_prec_anp
#check @RBM.BA.BAMomentGen_pval_claim
#check @RBM.BA.BAMomentGen_env
#check @RBM.BA.BAMomentGen_prec_int
#check @RBM.BA.BAMomentGen_expand
#check @RBM.BA.BAMomentGen_entry_whp
#check @RBM.BA.BAMomentGen_Psi_facts
#check @RBM.BA.BAMomentGen_floor
#check @RBM.BA.BAMomentGen_prec_of_whp
#check @RBM.BA.BAMomentGen_whp_of_prec
#check @RBM.BA.BAMomentGen_LWfg_zero
#check @RBM.BA.BAMomentGen_cont_fxyVal
#check @RBM.BA.BAMomentGen_integral_list_sum
#check @RBM.BA.BAMomentGen_logW_ge
#check @RBM.BA.BAMomentGen_lists_nonempty
-- L3d4 = T2472 (`Graph/BAProv`, `BAProvB`): the interface table §7 of its 1a-audit
#check @RBM.Graph.BAGraph.valW
#check @RBM.Graph.BAPGraph.valW
#check @RBM.Graph.BAGraph.valW_one
#check @RBM.Graph.BAPGraph.valW_one
#check @RBM.Graph.BAPGraph.valW_of_factor
#check @RBM.Graph.BAPGraph.valW_of_not
#check @RBM.Graph.BAGraph.valW_partition
#check @RBM.Graph.BAProvOut
#check @RBM.Graph.BAProvOut.ExtOK
#check @RBM.Graph.BAProvOut.Molecular
#check @RBM.Graph.BACoverBy
#check @RBM.Graph.BACoverBy.comp
#check @RBM.Graph.BACoverBy.rep
#check @RBM.Graph.BAWExp
#check @RBM.Graph.BAWExp.comp
#check @RBM.Graph.BAWExp.prod
#check @RBM.Graph.BAWExp.val_identity
#check @RBM.Graph.fxyValD
#check @RBM.Graph.fxyValD_univ
#check @RBM.Graph.fxyValD_union
#check @RBM.Graph.baProv_bridge
#check @RBM.Graph.BAProvStepPos
#check @RBM.Graph.baProv_stepPos
#check @RBM.Graph.baProv_exists
#check @RBM.Graph.BAEngineProv
#check @RBM.Graph.ba_localregularXP
#check @RBM.Graph.ba_localregularXP_ne
#check @RBM.Graph.baEngineProv_imp_localregularX
#check @RBM.Graph.BAProv_LocRegXClosed
-- L3b2 = T2469 (`Graph/BALocReg2B`): the path binder concluded, (1)-(5) at the outputs
#check @RBM.Graph.baPathBinder_holds
#check @RBM.Graph.baLocReg15_closed
#check @RBM.Graph.baShapeLLBinder_holds
#check @RBM.Graph.baLocRegConcl_upto5
#check @RBM.Graph.ba_localregular_upto5
-- L3c3b = T2444 (`Graph/BAZetaExp`), L3c3a (`Graph/BAAuxGraph2`, `BAAuxGraph2B`): ζ for the exp class, `(eq:Gbyxi2_BA)`, entries, L3d1's pin
#check @RBM.Graph.BAZetaExpClaim
#check @RBM.Graph.baZetaExpClaim_holds
#check @RBM.Graph.LWXiEgL
#check @RBM.Graph.baZetaVar
#check @RBM.Graph.BAGbyZeta
#check @RBM.Graph.baGbyZeta_holds
#check @RBM.Graph.BAEntryPsi
#check @RBM.Graph.baEntryPsi_holds
#check @RBM.Graph.BAAnpAuxG
-- L4c2 = T2466 (`Graph/BAExp14d`): rescaled data, `t`-scaling, G3 at the rescaled kernels
#check @RBM.BA.BAExp14d_dataT
#check @RBM.BA.BAExp14d_dataT_eq
#check @RBM.BA.BAExp14d_val_scale
#check @RBM.BA.BAGtoAGT
#check @RBM.BA.baGtoAGT_holds
-- L3c1, L3c2 (`Graph/BAAtom`, `BAAtom2`, `BASizeClaim2`): shadow, root form, tails, G3, size claim
#check @RBM.Graph.BAGraph.shadow
#check @RBM.Graph.BAGraph.auxVal
#check @RBM.Graph.BAGraph.auxOrd
#check @RBM.Graph.BAShadowPG
#check @RBM.Graph.BAAtom_shadow_molOf_eq_iff
#check @RBM.Graph.BAAtom_solid_prod_conf
#check @RBM.Graph.BAAtom_term_tail
#check @RBM.Graph.BAAtom_tail_sum
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_holds
#check @RBM.Graph.baAuxNested_holds
#check @RBM.Graph.BAGraph.sizeConst
#check @RBM.Graph.baClaimSize_E
-- the engine (`Graph/BAEngine`) and the graph data
#check @RBM.Graph.BALocRegConcl
#check @RBM.Graph.baStart_nWS
#check @RBM.Graph.ba_nWS_ge
#check @RBM.Graph.BAlwData
#check @RBM.Gauss.PF
-- L40-C2: the flow window of the coupling, the uniform rate on `(0, Λ]`, the BA data facts
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAct_rate_pos
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAReal
#check @RBM.BA.BASelf
-- the carrier layer (`Chain/Carrier`, `Chain/LWGen`, `BA/LWPinsBA`, `BA/FlowPins`) and the ≺ → 𝔼 kit (`Graph/BAExp14a`, `BAExp14aB`)
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.baFMz
#check @RBM.BA.PinFam
#check @RBM.BA.bandPin
#check @RBM.BA.baPin
#check @RBM.BA.LWAssmExpgL
#check @RBM.BA.LWLoopExpgL
#check @RBM.BA.LWtermExpG
#check @RBM.BA.BALWtermExp
#check @RBM.BA.BAExp14a_slc
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_floor
-- the instance data (`BA/FlowPins` §Inst; T2472's flow point and labels)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.BA.CouplingWindowInst.m0P
#check @RBM.Graph.BASymm1Inst.ℓ0

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

noncomputable section

namespace RBM.BA.T2483Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- **Target 1 (a)** (`LWfgD_bandFM`; content binding up to the unfolding of `LWfgD`): the carrier `f_{xy}` with the `β`-sum restricted to the
blocks in `Dm` (the 1b's `LWfgD C n t ω Dm x y`: the sum on the left with `C` in place of `bandFM sz E`; twin of `LWfD`, `LWProv:190`, over a
carrier, as `LWfg`, `BAMomentGen:71`) is the merged `LWfD` at the band carrier. -/
def T2483_LWfgDBand : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n)))
    (x y : Idx d (sz.L n) (sz.W n)),
    (∑ α, if α = x ∨ α = y then (0 : ℂ) else
      ∑ β, if STblk sz n β ∈ Dm then
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (bandFM sz E).S n (STblk sz n α) (STblk sz n β)) *
          (bandFM sz E).GM n t ω β β * (bandFM sz E).G n t ω x α * (bandFM sz E).G n t ω α y
      else 0) = LWfD sz n (E n) t ω Dm x y

/-- **Target 1 (b)** (`LWfgD_univ`; content binding up to the unfolding of `LWfgD`): at `Dm = univ` the domain form is the merged carrier `LWfg`. -/
def T2483_LWfgDUniv : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    (∑ α, if α = x ∨ α = y then (0 : ℂ) else
      ∑ β, if STblk sz n β ∈ (Finset.univ : Finset (Zd d (sz.L n))) then
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (STblk sz n α) (STblk sz n β)) * C.GM n t ω β β * C.G n t ω x α * C.G n t ω α y
      else 0) = LWfg C n t ω x y

/-- **Target 1 (c)** (`LWfgD_union`; band `LWfD_union`, `LWProv:196`; content binding up to the unfolding of `LWfgD`). -/
def T2483_LWfgDUnion : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (D₁ D₂ : Finset (Zd d (sz.L n))), Disjoint D₁ D₂ →
    ∀ x y : Idx d (sz.L n) (sz.W n),
      (∑ α, if α = x ∨ α = y then (0 : ℂ) else
        ∑ β, if STblk sz n β ∈ D₁ ∪ D₂ then
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (STblk sz n α) (STblk sz n β)) * C.GM n t ω β β * C.G n t ω x α * C.G n t ω α y
        else 0) =
        (∑ α, if α = x ∨ α = y then (0 : ℂ) else
          ∑ β, if STblk sz n β ∈ D₁ then
            ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (STblk sz n α) (STblk sz n β)) * C.GM n t ω β β * C.G n t ω x α * C.G n t ω α y
          else 0) +
        (∑ α, if α = x ∨ α = y then (0 : ℂ) else
          ∑ β, if STblk sz n β ∈ D₂ then
            ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (STblk sz n α) (STblk sz n β)) * C.GM n t ω β β * C.G n t ω x α * C.G n t ω α y
          else 0)

/-- **Target 2** (`LWMomentExpG`; content binding): `lem:LW_moment_exp` (`Graph/LWPins.lean:341`) over a carrier family, in the `PinFam` shape of
`LWtermExpG` (`Chain/LWGen.lean:93`): `STFlow` → `Flow`, `lemT` → `T0`, `LWAssmExp` → `LWAssmExpgL (mk sz z) (law sz)`, `Prec` → `PrecL sz (law sz)`,
`LWf` → the merged carrier `LWfg (mk sz z)`, `etaT` → `(mk sz z).eta`; the rest verbatim. -/
def T2483_LWMomentExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
          ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (mk sz z) (law sz) t ε₀ Ψ ℓ →
            ∀ D : ℝ, 0 < D →
              PrecL sz (law sz) (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
                  sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
                (fun n q _ => ∫ ω, ‖LWfg (mk sz z) n (t n) ω q.1.1 q.1.2‖ ^ p ∂(law sz))
                (fun n q _ => (((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
                    (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p +
                  ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 2** (`LWMomentExp_iff_bandPin`; content binding): the band instance of the generic pin is the merged pin (through `LWfg_bandFM`,
not definitional; `LWAssmExp`, `Prec`, `etaT` are `LWAssmExpgL`, `PrecL`, `eta` at the band carrier, as in `LWtermExp_iff`, `Chain/LWGen.lean:143`). -/
def T2483_MomentExpBand : Prop :=
  ∀ d : ℕ, RBM.Gauss.Sizes.LWMomentExp d ↔ bandPin T2483_LWMomentExpG d

/-- **Target 2** (`BALWMomentExp`; content binding): the BA reading (law `seqP (sz.withLam 0)`, `BAFlow`, `baFMz`, `BAflowT0`), beside `BALWMoment`
(`BAMomentGen:146`) and `BALWtermExp` (`BA/LWPinsBA.lean:47`). -/
def T2483_BALWMomentExp (d : ℕ) : Prop := baPin T2483_LWMomentExpG d

/-- **Target 3** (`baLWMomentOfAnp_closed`; content binding; supervisor 2246 L40-F2): T2470's target 4 without the path binder, which T2469 now
concludes (`baPathBinder_holds`, `BALocReg2B:338`).  Equal to T2470's `T2470_MomentClosed`. -/
def T2483_MomentClosed : Prop := ∀ d : ℕ, BALWMomentOfAnp d

/-- **Target 4 (a)** (`BAMomentExp_valW_scale`; content binding up to the unfolding of `BAPGraph.valW`): the weighted form of `BAExp14d_val_scale`
(`BAExp14d:111`; band `lwMomentExp_pvalW_smul`, `LWMomentExp:266`): for every real weight, every waved factor of `BAlwData` is `t` times that of
`BAExp14d_dataT`, so the weighted packed value is `t^{n_W}` times its value at the rescaled data (`BAReal`, `0 ≤ t < 1`). -/
def T2483_ValWScale : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 κ E t : ℝ) (m : ℂ), BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
    ∀ (ω : RBM.Gauss.Ω d L W) (P : BAPGraph (Fin 2)) (Wt : (P.E' ⊕ P.I' → Idx d L W) → ℝ) (ℓ : Fin 2 → Idx d L W),
      P.valW (BAlwData d L W g0 E t m ω) Wt ℓ = (t : ℂ) ^ P.g.nW * P.valW (BAExp14d_dataT d L W g0 E t m ω) Wt ℓ

/-- **Target 5** (`BAGtoAGTRooted`; content binding up to the name, the order of the hypotheses and the unfolding of `BAGraph.valW`): the BA rooted G3
= `BAGtoAGT` (`BAExp14d:269`; constants from `(d, Λ, κ)` only, uniformly in `0 < g₀ ≤ Λ`, `0 ≤ t < 1`) with the changes of `LWGtoAGRooted`
(`AuxGraphRooted:225`): roots `rep` of the internal shadow molecules (from `BACoverBy.rep`, `BAProv:130`), a real weight `|Wt| ≤ 1` vanishing unless
every root block is in `Dm`, the weighted value `BAGraph.valW` on the left and `auxValOn` of the shadow (sum over the blocks in `Dm`) on the right. -/
def T2483_GtoAGRooted (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ →
    ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), Γ.Normal →
          ∀ rep : LGraph.AuxIMol Γ.shadow → I', (∀ c, Γ.shadow.molOf (Sum.inr (rep c)) = c.1) →
          ∀ D : BALData (Idx d L W), D.S = Matrix.of (fun x y => ((svarF d L W 0 x y : ℝ) : ℂ)) →
            D.Sp = lwLift d L W (BATheta d L g0 E m t true true) → D.M = BAlwM d L W g0 E m →
            D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ (Ψ A r R : ℝ) (ξ : Zd d L → Zd d L → ℝ) (Dm : Finset (Zd d L)),
            (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 →
            0 ≤ r → (Fintype.card (E' ⊕ I') : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
            (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((RBM.Gauss.split d L W x).1 - a) : ℝ) ≤ R →
              (zdistD d L ((RBM.Gauss.split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
            ∀ Wt : (E' ⊕ I' → Idx d L W) → ℝ, (∀ ℓ, |Wt ℓ| ≤ 1) →
              (∀ ℓ, Wt ℓ ≠ 0 → ∀ c, (RBM.Gauss.split d L W (ℓ (Sum.inr (rep c)))).1 ∈ Dm) →
              ∀ ℓe : E' → Idx d L W,
                ‖Γ.valW D Wt ℓe‖ ≤
                  Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
                      (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ.shadow ξ (fun a => (RBM.Gauss.split d L W (ℓe a)).1) Dm) +
                    Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
                      Γ.scalingSize Ψ W d L

/-- **Target 9, the statement def** (`BALWMomentExpOfAnp`; content binding): `lem:LW_moment_exp` at BA from G4 on the BA carrier (`BAAnpAuxG`,
`BAAuxGraph2B:865`, L3d1's pin), which enters only through regime (A) (`BALWMoment`, target 3).  `BAAnpAuxG` occurs only here. -/
def T2483_MomentExpOfAnp (d : ℕ) : Prop := BAAnpAuxG d → T2483_BALWMomentExp d

/-- **Target 9** (`baLWMomentExp_of_anp`; content binding; band `lwMomentExp_holds`, `LWMomentExp:1436`): no path binder. -/
def T2483_MomentExp : Prop := ∀ d : ℕ, T2483_MomentExpOfAnp d

/-- Target 9 when L3d1 has merged at the 1b start (L40-F2: the first consumer written after L3d1 merges discharges `BAAnpAuxG`). -/
def T2483_MomentExpClosed : Prop := ∀ d : ℕ, T2483_BALWMomentExp d

/-- Statement level (not binding): target 3 is T2470's target 4 at the path binder that T2469 concludes; instance (iii) of target 9. -/
example : Prop := (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) → T2483_MomentClosed
example : Prop := BAAnpAuxG 3 → T2483_BALWMomentExp 3
example : Prop := T2483_LWfgDBand ∧ T2483_LWfgDUniv ∧ T2483_LWfgDUnion

/-- Target 2 beside its band original at `d = 3` (instance (ii) transports `lwMomentExp_holds 3`). -/
example : Prop := RBM.Gauss.Sizes.LWMomentExp 3 ∧ bandPin T2483_LWMomentExpG 3

/-- Shape (not binding) of target 1 (d), the twin of `LWfg_baFMz` (`BAMomentGen:93`): at the BA carrier, `t` times the domain form is the data-level
`fxyValD` (`BAProv:678`, T2472 target 9 (a)) at `BAlwData` of the slice of the sample. -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)),
    (t : ℂ) * (∑ α, if α = x ∨ α = y then (0 : ℂ) else
      ∑ β, if STblk sz n β ∈ Dm then
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) *
          (baFMz sz z).GM n t ω β β * (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y
      else 0) =
      fxyValD (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData Dm x y

/-- Shape (not binding) of target 4 (c), the weighted BA scale-mole tail (twin of `lwMomentExp_scalemole`, `LWMomentExp:344`; route of
`BAMomentGen_scalemole`, `BAMomentGen:738`, with `|Wt| ≤ 1`): it covers every output with `𝓜_x = 𝓜_y`, every `x ~ y` among them (O4). -/
example : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I], 3 ≤ d →
    ∀ Γ : BAGraph E I, Γ.Normal → ∀ (D : BALData (Idx d L W)) (Ψ C c r : ℝ), (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
        ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, (RBM.Gauss.split d L W x).2 ≠ (RBM.Gauss.split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) → 0 ≤ r →
      ∀ Wt : (E ⊕ I → Idx d L W) → ℝ, (∀ ℓ, |Wt ℓ| ≤ 1) →
        ∀ (ℓe : E → Idx d L W) (a b : E), Sum.inl b ∈ Γ.mol (Sum.inl a) →
          (Fintype.card (E ⊕ I) : ℝ) * r < (lwBdist d L W (ℓe a) (ℓe b) : ℝ) →
          ‖Γ.valW D Wt ℓe‖ ≤ Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
            Γ.scalingSize Ψ W d L

/-- Shape (not binding) of target 5's nested form: no twin of `LWAuxNestedOwnOn`; the merged band result (`AuxGraphRooted:457`) at the shadow
`BAShadowPG Q` (`BAAtom:139`), its premise `(BAShadowPG Q).LocReg345 p` from `baLocRegConcl_upto5` (`BALocReg2B:367`). -/
example : Prop :=
  ∀ (p : ℕ) (Q : BAPGraph (Fin 2)), 0 < p → (BAShadowPG Q).LocReg345 p →
    (BAShadowPG Q).g.molOf (Sum.inl ((BAShadowPG Q).ext 0)) ≠ (BAShadowPG Q).g.molOf (Sum.inl ((BAShadowPG Q).ext 1)) →
    ∃ Γa : NGraph p (BAShadowPG Q).g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧
      Γa.ordN = LGraph.auxOrd (BAShadowPG Q).g

/-- Shape (not binding) of target 6, regime (A) at BA (twin of `LWMomExpNoExpF` / `lwMomExpNoExp_holds`, `LWMomentExpA:56, 334`): from `BALWMoment`
for the class `Φ_B`, for every `K > 0`, on the pairs with `λ²/L² < 1 - t` in `regA d K` (`regA` imported, model-free in `sz`). -/
example : Prop :=
  ∀ d : ℕ, BALWMoment d → ∀ K : ℝ, 0 < K → 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ regA d K sz n (t n) (ℓ n) q})
          (fun n q _ => ∫ ω, ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p ∂(Sizes.seqP (sz.withLam 0)))
          (fun n q _ => (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- Shape (not binding) of target 8's `BAMomentExpOn dom reg` (twin of `LWMomentExpOn`, `LWMomentExp:86`): the target at the BA data for the domain
form `LWfgD (baFMz sz z)` (unfolded) on the pairs in `reg`; the far pin is `dom = domFar`, the near pins `domNearA`, `domNearB`, with `reg = ¬ regA`. -/
example : Prop :=
  ∀ (d : ℕ) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
    (reg : ∀ (sz : Sizes d) (n : ℕ), ℝ → ℝ → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) → Prop),
    3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
      BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
              sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ reg sz n (t n) (ℓ n) q})
            (fun n q _ => ∫ ω, ‖∑ α, (if α = q.1.1 ∨ α = q.1.2 then (0 : ℂ) else
                ∑ β, if STblk sz n β ∈ dom (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n) then
                  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFMz sz z).S n (STblk sz n α) (STblk sz n β)) *
                    (baFMz sz z).GM n (t n) ω β β * (baFMz sz z).G n (t n) ω q.1.1 α * (baFMz sz z).G n (t n) ω α q.1.2
                else 0)‖ ^ p ∂(Sizes.seqP (sz.withLam 0)))
            (fun n q _ => (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
              sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
                (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- Shape (not binding) of the L40-C2 limit check over the range L5 reads (every `Λ = 𝔡⁻¹ > 0`, `κ > 0`): the rate of the `M`-decay
(`BAMfine_decay`, `GreenSchur:124`; uniform in `0 < g₀ ≤ Λ`) is positive, so `c (log W)^{3/2}` beats `D log W` eventually (`lwTail32`, `LWXiExp:81`). -/
example : Prop := ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → 0 < BAct_rate d Λ κ

end RBM.BA.T2483Check

end
