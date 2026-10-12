/-
Release check for T2472 (dispatcher V3, Mon Oct 12 19:32 UTC 2026; DECISIONS §275).  BA-L L3d4 `BAProv`: the BA twin of the band provenance engine
`Graph/LWProv.lean` (`:1-1820`; T2387 §6 row L3d4 `:145`), with the narrow design gate G5 (T2387 §3 row 12 `:89`: the provenance
half of `lem:LW_moment_exp` at BA) and a probe step.  New files `Graph/BAProv`, `Graph/BAProvB` only.
Part 1: merged names (the band basis, its consumers, the merged BA inputs).  Part 2: the target statements that merged names fix
(prefix `T2472_`; content binding up to the name and the unfolding of `fxyValD`, `BAGraph.valW` and the packing), the shape binder
verbatim (no statement of this row carries it), then shapes (not binding; fixed at the 1a-audit from the probe texts): the engine
with provenance, the start coverage, the weighted value at weight 1, the root map that L3d2b reads.
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2472-check.lean
-/
import RBM3D.Graph.LWProv
import RBM3D.Graph.AuxGraphRooted
import RBM3D.Graph.LWMomentExp
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.LWEngine
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LocalRegular
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.BAEngine
import RBM3D.Graph.BAShapeO2B
import RBM3D.Graph.BAStepS
import RBM3D.Graph.BAScost
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BALvl1B
import RBM3D.Graph.BALvl1B2
import RBM3D.Graph.BALvl1C
import RBM3D.Graph.BASim
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BALocReg1
import RBM3D.Graph.BALocReg1B
import RBM3D.Graph.BAZetaExp
import RBM3D.Graph.BAExp14d
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes
import RBM3D.BA.MFixedPoint
import RBM3D.BA.CouplingWindow
import RBM3D.BA.CombesThomas
import RBM3D.BA.GreenSchur

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band basis (`Graph/LWProv`): §1 weighted values, maps, the weighted expansion, coverage, tags (no BA content), the engine statement, `LWfD`
#check @RBM.Graph.valW
#check @RBM.Graph.pvalW
#check @RBM.Graph.valW_one
#check @RBM.Graph.pvalW_one
#check @RBM.Graph.ProvOut
#check @RBM.Graph.ProvOut.ExtOK
#check @RBM.Graph.ProvOut.Molecular
#check @RBM.Graph.ProvOut.comp
#check @RBM.Graph.ProvOut.Molecular.comp
#check @RBM.Graph.WExp
#check @RBM.Graph.WExp.refl
#check @RBM.Graph.WExp.comp
#check @RBM.Graph.WExp.prod
#check @RBM.Graph.CoverBy
#check @RBM.Graph.CoverBy.comp
#check @RBM.Graph.ProvOutX
#check @RBM.Graph.ProvOutX.ev
#check @RBM.Graph.ProvOutX.Cover
#check @RBM.Graph.mkProv
#check @RBM.Graph.stepOuts
#check @RBM.Graph.LWEngineProv
#check @RBM.Graph.lwEngineProv_imp_localregularX
#check @RBM.Graph.LWfD
#check @RBM.Graph.LWfD_union
-- §2 the bridge; §3 molecular maps, the partition with maps, the start coverage; §4 the weighted partition (scalar `M` on the diagonal)
#check @RBM.Graph.lwProv_pvalW_of_factor
#check @RBM.Graph.lwProv_pvalW_of_not
#check @RBM.Graph.lwProv_bridge
#check @RBM.Graph.lwProv_molecular
#check @RBM.Graph.lwProv_partX
#check @RBM.Graph.lwProv_blk_mol
#check @RBM.Graph.lwProv_weightOuts_mol
#check @RBM.Graph.lwProv_fxyCover
#check @RBM.Graph.lwProv_valW_partX
-- §5-§6 the weighted expansions of the three band steps; §7 positions, recursion, engine; §9 the pinned step
#check @RBM.Graph.lwProv_weight_EW
#check @RBM.Graph.lwProv_oe2x_EW
#check @RBM.Graph.lwProv_WExp_of_unpacked
#check @RBM.Graph.lwProv_weight_step
#check @RBM.Graph.lwProv_edge_step
#check @RBM.Graph.lwProv_gg_step
#check @RBM.Graph.lwProv_edgeOuts_mol
#check @RBM.Graph.lwProv_ggOuts_mol
#check @RBM.Graph.lwProv_stepPos
#check @RBM.Graph.lwProv_exists
#check @RBM.Graph.lw_localregularXP
#check @RBM.Graph.lwProv_LocStepXProvPos
#check @RBM.Graph.lwProv_locStepXProvPos_holds
-- the band consumers (L3d2b's basis; not here): the rooted G3 (reads `valW` only), the restricted nested aux graph, the assembly
#check @RBM.Graph.auxValOn
#check @RBM.Graph.LWGtoAGRooted
#check @RBM.Graph.lwGtoAGRooted_holds
#check @RBM.Graph.LWAuxNestedOwnOn
#check @RBM.Graph.lwAuxNestedOwnOn_holds
#check @RBM.Graph.domFar
#check @RBM.Graph.domNearA
#check @RBM.Graph.domNearB
#check @RBM.Graph.LWMomentExpOn
#check @RBM.Graph.LWMomExpFarPin
#check @RBM.Graph.LWMomExpNearPin
#check @RBM.Graph.LWMomentExpOfParts
#check @RBM.Graph.lwMomentExp_wt
#check @RBM.Graph.lwMomentExp_expand
#check @RBM.Graph.lwMomentExp_pin_gen
#check @RBM.Gauss.Sizes.LWMomentExp
#check @RBM.Gauss.Sizes.lwMomentExp_holds
-- L5's band original reads `lwMomentExp_holds` only (`LWTermHolds:1524`)
#check @RBM.Gauss.Sizes.lwtermExp_holds
-- the band engine and the generic tools the BA recursion reuses
#check @RBM.Graph.LWLocRegConcl
#check @RBM.Graph.lw_localregularX
#check @RBM.Graph.lwEngine_exists
#check @RBM.Graph.lvl1Cutoff
#check @RBM.Graph.lvl1_choose_list
#check @RBM.Graph.lvl1_sum_flatMap
#check @RBM.Graph.owx_integral_list_sum
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.localReg_fxyBeta
#check @RBM.Graph.fxyPowGraph_normal
#check @RBM.Graph.fxyPowGraph_val_eq
#check @RBM.Graph.fxyVal
#check @RBM.Graph.LData
#check @RBM.Graph.LGraph.Mol
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.IsExtMol
#check @RBM.Graph.LGraph.AuxIMol
-- L3d3 (T2448, `Graph/BAEngine`, merged 79f3c1c): the conclusion, the engine with its binder, the assembly, black waved edges, the `LocStd` producer
#check @RBM.Graph.BALocRegConcl
#check @RBM.Graph.ba_localregularX
#check @RBM.Graph.baEngine_assemble
#check @RBM.Graph.baStep_nWS
#check @RBM.Graph.ba_nWS_ge
#check @RBM.Graph.baStart_nWS
#check @RBM.Graph.BAEngine_pL_locStd
-- L3b4″ (T2447, `Graph/BAShapeO2B`, merged 00f4a10): the three shape results that discharge the binder
#check @RBM.Graph.baShapeLL_e2_tn
#check @RBM.Graph.baShapeLL_macroA_tn
#check @RBM.Graph.baShapeLL_macroB_tn
#check @RBM.Graph.baLocReg6_holds
#check @RBM.Graph.BAShapeLL
#check @RBM.Graph.BAFrameStepTN
#check @RBM.Graph.BAShape.e2
#check @RBM.Graph.BAShape.macroA
#check @RBM.Graph.BAShape.macroB
-- L3a3 (T2440, `Graph/BALvl1A`): the step, reachability, the identities of one step, packing, the macro identities, instances
#check @RBM.Graph.BALocStep
#check @RBM.Graph.BAReach
#check @RBM.Graph.BAReach.refl
#check @RBM.Graph.BAReach.step
#check @RBM.Graph.BAtwistComb
#check @RBM.Graph.baTwistComb_holds
#check @RBM.Graph.BAframeStepIdentity
#check @RBM.Graph.baFrameStepIdentity_holds
#check @RBM.Graph.baLvl1StepIdentity_holds
#check @RBM.Graph.BALvl1A_val_of_factor
#check @RBM.Graph.BALvl1A_val_of_not
#check @RBM.Graph.BALvl1A_pack
#check @RBM.Graph.BALvl1A_integrable_val
#check @RBM.Graph.BALvl1A_macroA
#check @RBM.Graph.BALvl1A_macroB
#check @RBM.Graph.BALvl1AInst.locStepB
#check @RBM.Graph.BALvl1AInst.normalB
-- L3a4/L3a5 (`Graph/BALvl1B`, `BALvl1B2`, `BALvl1C`): the measure, the good step, the data-free lists, the induction
#check @RBM.Graph.BALvl1Good
#check @RBM.Graph.baLvl1StepGood_holds
#check @RBM.Graph.BAlvl1Lemma
#check @RBM.Graph.BAlvl1LemmaSize
#check @RBM.Graph.baLvl1Lemma_holds
#check @RBM.Graph.baLvl1LemmaSize_holds
#check @RBM.Graph.baLvl1ExistsStep_holds
#check @RBM.Graph.ba_lvl1_induction
#check @RBM.Graph.BAReach.trans
#check @RBM.Graph.BALvl1Mu
#check @RBM.Graph.baLvl1Lt_wf
#check @RBM.Graph.ba_lvl1_mu_lt
-- R1 (T2423, `Graph/BASim`): the five frame kinds and their output lists, the twist of a packed graph
#check @RBM.Graph.BAFrameStep
#check @RBM.Graph.BAFrameStep.weight
#check @RBM.Graph.BAFrameStep.within
#check @RBM.Graph.BAFrameStep.edge
#check @RBM.Graph.BAFrameStep.gg
#check @RBM.Graph.BAFrameStep.ggSplit
#check @RBM.Graph.BAPGraph.outsOf
#check @RBM.Graph.BAPGraph.withinOuts
#check @RBM.Graph.BAPGraph.splitOuts
#check @RBM.Graph.BAPGraph.twist
#check @RBM.Graph.BAGraph.twist
-- the terms: `BAGraph.ext` keeps waved, `Ψ`- and `M`-dotted edges and appends new ones (the Molecular table of 1a (ii))
#check @RBM.Graph.BAGraph.ext
#check @RBM.Graph.bpW
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.BAGraph.lanlwT1
#check @RBM.Graph.BAGraph.lanlwD
#check @RBM.Graph.BAGraph.lanlwTerms
-- the per-labelling identities (census of 1a (iv)): `lanlw` on the sequence space, its graph form, the frame identities
#check @RBM.Graph.BAExpand_integral
#check @RBM.Graph.BAExpandW_lanlw_val_seq
#check @RBM.Graph.lanlw_val
#check @RBM.Graph.baExpFrame_lw
#check @RBM.Graph.baExpFrame_gg
#check @RBM.Graph.baExpFrameE_holds
#check @RBM.Graph.baLanlw_holds
#check @RBM.Graph.baLweight_holds
-- `BAVocab`: graphs, values, the start graph, the partition (pointwise, no data hypothesis), the data and law
#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BALData
#check @RBM.Graph.BAGraph.term
#check @RBM.Graph.BAGraph.val
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAComb.val
#check @RBM.Graph.BAGraph.ofLGraph
#check @RBM.Graph.BAGraph.val_ofLGraph
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.val_splitG
#check @RBM.Graph.BAGraph.merge
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.val_eq_partition
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BAGraph.adj
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.atomSetoid
#check @RBM.Graph.baPG
#check @RBM.Graph.BAlwData
#check @RBM.Gauss.PF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.Idx
#check @RBM.Gauss.split
#check @RBM.BA.BASelf
-- L3c1 (T2420, `Graph/BAAtom`, `BAAtom2`): molecules on the shadow, roots in the confined solid product, G3 (L3d2b's inputs)
#check @RBM.Graph.BAGraph.shadow
#check @RBM.Graph.BAShadowPG
#check @RBM.Graph.BAAtom_shadow_molOf_eq_iff
#check @RBM.Graph.BAAtom_solid_prod_conf
#check @RBM.Graph.BAGraph.auxVal
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_holds
#check @RBM.Graph.baGtoAG_E
#check @RBM.Graph.baAuxNested_holds
-- L3b1 (T2456, `Graph/BALocReg1`, `BALocReg1B`): atom inside molecule (1a (vii)), the (1)-(5) contract, the start bound, the unweighted value identity
#check @RBM.Graph.BALocReg1_mol_of_atom
#check @RBM.Graph.BALocReg15
#check @RBM.Graph.baLocReg15_holds
#check @RBM.Graph.baStart_nM_le
#check @RBM.Graph.ba_fxyPow_integral_eq
-- L4c2 (T2466, `Graph/BAExp14d`, merged 03109267) and L3c3b (T2444, `Graph/BAZetaExp`): L3d2b's inputs, not read here
#check @RBM.BA.BAExp14d_dataT
#check @RBM.BA.BAExp14d_val_scale
#check @RBM.BA.BAGtoAGT
#check @RBM.BA.baGtoAGT_holds
#check @RBM.Graph.BAZetaExpClaim
#check @RBM.Graph.baZetaExpClaim_holds
-- L4-C4 (b) numbers (1a (vii)): the fixed decay rate of `M`
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAMfine_decay
-- instance data (`BALvl1AInst`, `BAEngineInst`): the flow point, the external labelling
#check @RBM.BA.CouplingWindowInst.flowP_data
#check @RBM.BA.CouplingWindowInst.g0P
#check @RBM.BA.CouplingWindowInst.EP
#check @RBM.BA.CouplingWindowInst.t0P
#check @RBM.BA.CouplingWindowInst.m0P
#check @RBM.Graph.BASymm1Inst.ℓ0

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

noncomputable section

namespace RBM.Graph.T2472Check

open MeasureTheory
open RBM RBM.Gauss RBM.Graph RBM.BA

/-- The shape binder of `BALocReg6` (`BAStepS.lean:100`), verbatim (= `T2448_Binder`).  No public statement of this row carries it:
the engine with provenance discharges it from `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn` (`BAShapeO2B:221, 269, 303`). -/
def T2472_Binder : Prop :=
  ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN

/-- **Target 8 (b), conclusion** (`baEngineProv_imp_localregularX`; band `lwEngineProv_imp_localregularX`, `LWProv:177-188`; content binding):
the conclusion of `ba_localregularX` (`BAEngine:335`) without the binder. -/
def T2472_LocRegXClosed : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)

/-- **Target 9 (a)** (`fxyValD_univ`; content binding up to the unfolding of `fxyValD`): the data-level `f_xy` with the `β`-sum restricted to the
blocks in `Dm` (the 1b's `fxyValD D Dm x y`, twin of `LWfD`, `LWProv:190`; the sum on the left) is `fxyVal` (`LWVocab:217`) at `Dm = univ`. -/
def T2472_FxyDUniv : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (D : LData (RBM.Gauss.Idx d L W)) (x y : RBM.Gauss.Idx d L W),
    (∑ α, if α = x ∨ α = y then (0 : ℂ) else
      ∑ β, if (RBM.Gauss.split d L W β).1 ∈ (Finset.univ : Finset (Zd d L)) then
        D.S α β * (D.G β β - D.M β β) * D.G x α * D.G α y else 0) = fxyVal D x y

/-- **Target 9 (b)** (`fxyValD_union`; band `LWfD_union`, `LWProv:196`; content binding up to the unfolding of `fxyValD`). -/
def T2472_FxyDUnion : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (D : LData (RBM.Gauss.Idx d L W)) (D₁ D₂ : Finset (Zd d L)), Disjoint D₁ D₂ →
    ∀ x y : RBM.Gauss.Idx d L W,
      (∑ α, if α = x ∨ α = y then (0 : ℂ) else
        ∑ β, if (RBM.Gauss.split d L W β).1 ∈ D₁ ∪ D₂ then D.S α β * (D.G β β - D.M β β) * D.G x α * D.G α y else 0) =
        (∑ α, if α = x ∨ α = y then (0 : ℂ) else
          ∑ β, if (RBM.Gauss.split d L W β).1 ∈ D₁ then D.S α β * (D.G β β - D.M β β) * D.G x α * D.G α y else 0) +
        (∑ α, if α = x ∨ α = y then (0 : ℂ) else
          ∑ β, if (RBM.Gauss.split d L W β).1 ∈ D₂ then D.S α β * (D.G β β - D.M β β) * D.G x α * D.G α y else 0)

/-- **Target 9 (c)** (`baProv_bridge`; band `lwProv_bridge`, `LWProv:233`; content binding up to the unfolding of `fxyValD`, `BAGraph.valW` and the
packing `baPG`): at the BA data `BAlwData` (real `S`), pointwise in the sample, `p` even, the weighted value of the BA start graph with the weight
`Π_k 1_{Dm}([β^{(k)}])` (the sum on the left: `BAGraph.valW` unfolded) is `‖fxyValD‖^p` (the norm on the right: `fxyValD` unfolded); at
`Dm = univ` it is the pointwise identity under `ba_fxyPow_integral_eq` (`BALocReg1B:294`). -/
def T2472_Bridge : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) (ω : RBM.Gauss.Ω d L W) (p : ℕ), Even p →
    ∀ (Dm : Finset (Zd d L)) (ℓe : Fin 2 → RBM.Gauss.Idx d L W),
      (∑ ℓi : Fin (2 * p) → RBM.Gauss.Idx d L W,
          (((∏ k : Fin p, (if (RBM.Gauss.split d L W (ℓi (localReg_fxyBeta k))).1 ∈ Dm then (1 : ℝ) else 0)) : ℝ) : ℂ) *
            (BAGraph.ofLGraph (fxyPowGraph p)).term (BAlwData d L W g0 Em t m ω) (Sum.elim ℓe ℓi)) =
        ((‖∑ α, if α = ℓe 0 ∨ α = ℓe 1 then (0 : ℂ) else
            ∑ β, if (RBM.Gauss.split d L W β).1 ∈ Dm then
              (BAlwData d L W g0 Em t m ω).S α β *
                ((BAlwData d L W g0 Em t m ω).G β β - (BAlwData d L W g0 Em t m ω).M β β) *
                (BAlwData d L W g0 Em t m ω).G (ℓe 0) α * (BAlwData d L W g0 Em t m ω).G α (ℓe 1) else 0‖ ^ p : ℝ) : ℂ)

/-- Statement level (not binding): the route of target 8 (b) (the three shape results give the binder). -/
example : Prop := T2472_Binder → T2472_LocRegXClosed

/-- Shape (not binding; fixed at the 1a-audit) of target 8 (a) `BAEngineProv` (band `LWEngineProv`, `LWProv:168-175`, without tags and without
`∀ m`): output lists with provenance maps from the start graph `BAGraph.ofLGraph (fxyPowGraph p)` (vertices `Fin 2 ⊕ Fin (2p)`), the conclusion
`BALocRegConcl`, `n_{W,black} ≥ p`, external vertices to external vertices, every internal molecule of the shadow containing an image of some
`β^{(k)}`.  The weighted expansion `BAWExp` at `BAlwData` (`BASelf`, `0 ≤ t < 1`) and the packing of the maps (`BAProvOut`) are the probe's texts. -/
example : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
    ∃ outs errs : List (Σ Q : BAPGraph (Fin 2), (Fin 2 ⊕ Fin (2 * p) → Q.E' ⊕ Q.I')),
      BALocRegConcl p c K0 d D (outs.map Sigma.fst) (errs.map Sigma.fst) ∧
      (∀ o ∈ outs ++ errs, p ≤ o.1.g.waved.countP (fun e => !e.col)) ∧
      (∀ o ∈ outs ++ errs, ∀ i : Fin 2, o.2 (Sum.inl i) = Sum.inl (o.1.ext i)) ∧
      ∀ o ∈ outs ++ errs, ∀ mc : LGraph.AuxIMol o.1.g.shadow,
        ∃ k : Fin p, o.1.g.shadow.molOf (o.2 (Sum.inr (localReg_fxyBeta k))) = mc.1

/-- Shape (not binding) of the start of target 4 (twin of `lwProv_fxyCover`, `LWProv:537`): every partition term of the BA start graph has a map
from the start vertices, external to external, under which the `β^{(k)}` cover its internal shadow molecules. -/
example : Prop :=
  ∀ p : ℕ, ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition,
    ∃ pmap : Fin 2 ⊕ Fin (2 * p) → P0.E' ⊕ P0.I', (∀ i : Fin 2, pmap (Sum.inl i) = Sum.inl (P0.ext i)) ∧
      ∀ mc : LGraph.AuxIMol P0.g.shadow, ∃ k : Fin p, P0.g.shadow.molOf (pmap (Sum.inr (localReg_fxyBeta k))) = mc.1

/-- Shape (not binding) of target 1 at weight `1` (twin of `valW_one`, `LWProv:54`): the weighted value (unfolded) is `BAGraph.val`. -/
example : Prop :=
  ∀ {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι),
    (∑ ℓi : I → ι, ((1 : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)) = Γ.val D ℓe

/-- Shape (not binding) of what L3d2b reads from the coverage (twin of the private `lwMomentExp_rep`, `LWMomentExp:1000`): a root in every internal
shadow molecule, to be passed as `root` to the confined solid product (`BAAtom_solid_prod_conf`, `BAAtom:535-536`). -/
example : Prop :=
  ∀ (p : ℕ) (Q : BAPGraph (Fin 2)) (pmap : Fin 2 ⊕ Fin (2 * p) → Q.E' ⊕ Q.I'),
    (∀ mc : LGraph.AuxIMol Q.g.shadow, ∃ k : Fin p, Q.g.shadow.molOf (pmap (Sum.inr (localReg_fxyBeta k))) = mc.1) →
      ∃ rep : LGraph.AuxIMol Q.g.shadow → Q.I', ∀ mc, Q.g.shadow.molOf (Sum.inr (rep mc)) = mc.1

/-- Shape (not binding) of instance 10 (i): target 8 (b) at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10`, with nonempty lists. -/
example : Prop := T2472_LocRegXClosed → ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧ outs ++ errs ≠ []

/-- Target 9 beside its band original (`LWfD`, `LWfD_union`, `lwProv_bridge`): the three binding pins together. -/
example : Prop := T2472_FxyDUniv ∧ T2472_FxyDUnion ∧ T2472_Bridge

end RBM.Graph.T2472Check

end
