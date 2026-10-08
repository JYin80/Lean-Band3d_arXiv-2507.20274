/-
Release check for T2315 (dispatcher V1, Thu Oct  8 03:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §129 (1), §131,
§98 (2), §102, §57 (1), §29, §20, §17, §16).
BA-L2b2 (second cut of BA-L2b, §129 (1)): `RBM3D/Graph/BAExpandWOrd.lean` — target 3(c) of the T2303 draft
(`docs/tickets/drafts/T2303-draft.md`): the raw counters of the `lanlw` terms, their raw order and the claim
`lanlw_scalingOrderG`, plus instances (I3)-(I4) of T2295, on the vocabulary merged by T2303 (`Graph/BAExpandW`, 8f90d6d).
Section 1: the merged names (the section 1 of `T2303-check.lean`, compiled exit 0 at 66fd97e, plus the T2303 names).
Section 2: the target statements as `Prop`s (T2315 proves them with these exact texts) and the instance statements.
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2315-check.lean`.
-/
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAVocab
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWVocab
import RBM3D.BA.Ward
import RBM3D.BA.FlowPins
import RBM3D.BA.MFixedPoint
import RBM3D.Gauss.BlockAnderson
import RBM3D.Gauss.FineModel
import RBM3D.Loop.GLoopFlow
import RBM3D.Green.IBPPoly
import RBM3D.Green.LDEQuad
import RBM3D.Defs.Sizes
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import RBM3D.Graph.BAExpandW

/-! ## 1. Merged names -/

-- T2295 (BA-L2a1, ad9bb6d): `RBM3D/Graph/BAExpand.lean`, namespace `RBM.Graph` (`:48-902`)
#check @RBM.Graph.BAlwH                       -- :60
#check @RBM.Graph.BAlwM                       -- :64
#check @RBM.Graph.BAlwG                       -- :67
#check @RBM.Graph.BAlwGc                      -- :71
#check @RBM.Graph.BAlwS                       -- :75
#check @RBM.Graph.BAlwMp                      -- :78
#check @RBM.Graph.BAlwW                       -- :82
#check @RBM.Graph.BAlwf                       -- :86
#check @RBM.Graph.BAlwdf                      -- :90
#check @RBM.Graph.BAlanlwL                    -- :102
#check @RBM.Graph.BAlanlwR                    -- :106
#check @RBM.Graph.BAlanlw                     -- :117
#check @RBM.Graph.baGm                        -- :148
#check @RBM.Graph.baG                         -- :153
#check @RBM.Graph.dhSample_baG                -- :250
#check @RBM.Graph.dhSample_baG_star           -- :256
#check @RBM.Graph.baG_tame1                   -- :305
#check @RBM.Graph.baVar                       -- :319
#check @RBM.Graph.baPoly                      -- :325
#check @RBM.Graph.baPoly_tame1                -- :339
#check @RBM.Graph.stein_baPoly                -- :354
#check @RBM.Graph.baWx_baG                    -- :378
#check @RBM.Graph.baWx_baPoly                 -- :400
#check @RBM.Graph.baWx_dh                     -- :485
#check @RBM.Graph.BAExpand_defect             -- :512
#check @RBM.Graph.BAExpand_defect_identity    -- :517
#check @RBM.Graph.BAExpand_G_sub_M            -- :554
#check @RBM.Graph.BAExpand_integral_defect    -- :602
#check @RBM.Graph.BAExpand_integral           -- :647 (`lanlw` on `Sizes.seqP`, any `M` with `M_ββ = m`)
#check @RBM.Graph.BAExpand_M_diag             -- :722
#check @RBM.Graph.BAExpand_Gc_zero            -- :731
#check @RBM.Graph.baLanlw_holds               -- :744
#check @RBM.Graph.BAExpandInst.baS_row_sum    -- :793
#check @RBM.Graph.BAExpandInst.baLanlw_t0     -- :800
#check @RBM.Graph.BAExpandInst.baSelf_zero    -- :865

-- T2287 (BA-L1, c230ce5): `RBM3D/Graph/BAVocab.lean`, namespace `RBM.Graph` (`:34-1424`)
#check @RBM.Graph.BALData                     -- :39
#check @RBM.Graph.BAPsiEdge                   -- :43
#check @RBM.Graph.BAMEdge                     -- :48
#check @RBM.Graph.BAGraph                     -- :55
#check @RBM.Graph.BAPsiEdge.map               -- :59
#check @RBM.Graph.BAMEdge.map                 -- :61
#check @RBM.Graph.BAMEdge.val                 -- :68
#check @RBM.Graph.BAGraph.term                -- :72
#check @RBM.Graph.BAGraph.val                 -- :78
#check @RBM.Graph.BAGraph.addM                -- :87
#check @RBM.Graph.BAGraph.atomAdj             -- :92
#check @RBM.Graph.BAGraph.atom                -- :105
#check @RBM.Graph.BAGraph.nA                  -- :110
#check @RBM.Graph.BAGraph.adj                 -- :116
#check @RBM.Graph.BAGraph.mol                 -- :125
#check @RBM.Graph.BAGraph.nM                  -- :130
#check @RBM.Graph.BAGraph.nS                  -- :135
#check @RBM.Graph.BAGraph.nW                  -- :138
#check @RBM.Graph.BAGraph.counters            -- :141
#check @RBM.Graph.BAGraph.scalingOrder        -- :146
#check @RBM.Graph.BAGraph.Normal              -- :158
#check @RBM.Graph.baSplitSolid                -- :163
#check @RBM.Graph.BAGraph.splitG              -- :170
#check @RBM.Graph.BAGraph.packMerge           -- :220
#check @RBM.Graph.BAGraph.partition           -- :229
#check @RBM.Graph.BAGraph.scalingOrderG       -- :234
#check @RBM.Graph.BAGraph.term_addM           -- :254
#check @RBM.Graph.BAGraph.mem_atom_iff        -- :387
#check @RBM.Graph.BAGraph.mem_mol_iff         -- :394
#check @RBM.Graph.BAGraph.nA_le_card          -- :435
#check @RBM.Graph.BAGraph.val_splitG          -- :647
#check @RBM.Graph.BAGraph.splitG_circ         -- :688
#check @RBM.Graph.BAGraph.splitG_edges        -- :697
#check @RBM.Graph.BAGraph.val_eq_partition    -- :919
#check @RBM.Graph.BAGraph.partition_normal    -- :930
#check @RBM.Graph.BAGraph.partition_of_normal -- :1137
#check @RBM.Graph.BAGraph.le_scalingOrderG_iff -- :1154
#check @RBM.Graph.BAGraph.scalingOrderG_of_normal -- :1167
#check @RBM.Graph.BAVocabInst.baLWT1          -- :1201
#check @RBM.Graph.BAVocabInst.baGedge_ordG    -- :1308

-- LW-03 (37db678): `RBM3D/Graph/LWVocab.lean`, namespace `RBM.Graph` (`:67-2559`)
#check @RBM.Graph.LData                       -- :73
#check @RBM.Graph.SEdge                       -- :82
#check @RBM.Graph.WEdge                       -- :89
#check @RBM.Graph.LGraph                      -- :104
#check @RBM.Graph.LGraph.term                 -- :129
#check @RBM.Graph.LGraph.adj                  -- :157
#check @RBM.Graph.SEdge.map                   -- :412
#check @RBM.Graph.Counters                    -- ScalingOrder.lean:49 (3c07bc8)
#check @RBM.Graph.ord                         -- ScalingOrder.lean:65

-- LW-04 (89f29cf): `RBM3D/Graph/LWStein.lean`, namespace `RBM.Graph` (`:82-1894`)
#check @RBM.Graph.owxDefect                   -- :100
#check @RBM.Graph.owx_defect_identity         -- :107 (the band twin of the pathwise solve)
#check @RBM.Graph.dhSample                    -- :521
#check @RBM.Graph.Tame1                       -- :703
#check @RBM.Graph.lwSplit                     -- :891
#check @RBM.Graph.lwS                         -- :998
#check @RBM.Graph.stein_sample                -- :1013
#check @RBM.Graph.lwS_row_sum                 -- :1215
#check @RBM.Graph.owx_integral                -- :1239 (the band twin of target 1)
#check @RBM.Graph.lwSplus                     -- :1308
#check @RBM.Graph.lwS_isUnit                  -- :1313 (Gershgorin, the twin of target 1b)
#check @RBM.Graph.lwSplus_spec                -- :1346
#check @RBM.Graph.LGraph.dTerm                -- :1381 (coefficient `-Γ.coeff`; `lanlwD` has `+Γ.coeff`)
#check @RBM.Graph.lwSampleData                -- :1420 (`lwGm` only: the BA twin is new)
#check @RBM.Graph.lwStein_term_eq             -- :1506

-- LW-05 (975f4ff): `RBM3D/Graph/LWWeightExp.lean`, namespace `RBM.Graph` (`:51-1507`)
#check @RBM.Graph.lwWxSizes                   -- :60
#check @RBM.Graph.lwWx_lwS_apply              -- :281
#check @RBM.Graph.lwWx_integral               -- :330
#check @RBM.Graph.lwWeightExp_holds           -- :407
#check @RBM.Graph.owxEmb                      -- :454
#check @RBM.Graph.LGraph.owxExt               -- :458
#check @RBM.Graph.owxDE                       -- :468
#check @RBM.Graph.LGraph.term_owxExt          -- :474
#check @RBM.Graph.owxDE_val                   -- :487
#check @RBM.Graph.owx_nM_eq                   -- :514
#check @RBM.Graph.owxExt_nM                   -- :591
#check @RBM.Graph.owxT4                       -- :688 (the derivative-term pattern)
#check @RBM.Graph.owxT1_counters              -- :741
#check @RBM.Graph.lwSplit_perm                -- :928
#check @RBM.Graph.owx_integral_list_sum       -- :956
#check @RBM.Graph.owx_sum_fin2                -- :985
#check @RBM.Graph.owxEdgePoly                 -- :1001
#check @RBM.Graph.owx_term_integral           -- :1060
#check @RBM.Graph.owx_graph_E                 -- :1316

-- LW pins (975f4ff): `RBM3D/Graph/LWPins.lean`, namespace `RBM.Graph` (`:53-185`)
#check @RBM.Graph.LWPins_dH                   -- :62
#check @RBM.Graph.LWPins_resPoly              -- :73

-- Stein hypothesis, discharged; `Tame` (namespace `RBM.Green`)
#check @RBM.Green.Tame                        -- LDEQuad.lean:165 (cca94be)
#check @RBM.Green.GaussIBP                    -- LDEQuad.lean:302
#check @RBM.Green.Tame.integrable             -- LDEQuad.lean:312
#check @RBM.Green.gaussIBP                    -- IBPPoly.lean:305 (3b8c687)

-- the model (namespace `RBM.Gauss`)
#check @RBM.Gauss.Idx                         -- Defs/Sizes.lean:46 (0a873f1)
#check @RBM.Gauss.split                       -- Defs/Sizes.lean:64
#check @RBM.Gauss.splitEquiv                  -- Defs/Sizes.lean:87
#check @RBM.Gauss.svarF                       -- Gauss/FineModel.lean:47 (0a873f1)
#check @RBM.Gauss.Ω                           -- :84
#check @RBM.Gauss.PF                          -- :97
#check @RBM.Gauss.Sizes.seqP                  -- :169
#check @RBM.Gauss.Hflow                       -- :437
#check @RBM.Gauss.PsiI                        -- Gauss/BlockAnderson.lean:52 (868b3b4)
#check @RBM.Gauss.ztOf                        -- Loop/GLoopFlow.lean:55 (868b3b4)
#check @RBM.Gauss.Gres                        -- :74
#check @RBM.Gauss.Mres                        -- :81

-- BA deterministic layer (namespace `RBM.BA`)
#check @RBM.BA.BAMB                           -- BA/MFixedPoint.lean:190 (ae63e74)
#check @RBM.BA.BASelf                         -- :193
#check @RBM.BA.BAMB_symm                      -- BA/Ward.lean:83 (b4fb28b)
#check @RBM.BA.BAMB_diag_eq                   -- :89
#check @RBM.BA.BAMB_row_sq_real               -- :125
#check @RBM.BA.BAMres_fine_kron               -- BA/FlowPins.lean:70 (b750bf3)
#check @RBM.BA.BAMres_fine_apply              -- :100

-- Mathlib (root namespace): Gershgorin
#check @det_ne_zero_of_sum_row_lt_diag        -- Mathlib/LinearAlgebra/Matrix/Gershgorin.lean:63
#check @Matrix.isUnit_iff_isUnit_det

-- T2303 (BA-L2b1, 8f90d6d): `RBM3D/Graph/BAExpandW.lean`, namespace `RBM.Graph` (`:53-1064`)
#check @RBM.Graph.BAlwData                    -- :98
#check @RBM.Graph.BAGraph.lanlwExt            -- :114
#check @RBM.Graph.BAGraph.lanlwT1             -- :122
#check @RBM.Graph.BAGraph.lanlwD              -- :133
#check @RBM.Graph.BAGraph.lanlwTerms          -- :144
#check @RBM.Graph.lanlw_val                   -- :908
#check @RBM.Graph.baGcxy                      -- :971
#check @RBM.Graph.baGcxx                      -- :980
-- BAVocab (T2287, c230ce5), namespace `RBM.Graph`: the order layer this ticket uses
#check @RBM.Graph.BAGraph.counters            -- :141
#check @RBM.Graph.BAGraph.scalingOrder        -- :146
#check @RBM.Graph.BAGraph.Normal              -- :158
#check @RBM.Graph.BAGraph.scalingOrderG       -- :234
#check @RBM.Graph.BAGraph.nA                  -- :110
#check @RBM.Graph.BAGraph.nM                  -- :130

/-! ## 2. Target statements (T2315 proves them with these texts) and the instances -/

noncomputable section

open MeasureTheory Matrix RBM.Gauss

namespace RBM.Graph.T2315Check

/-- Target 3(c): raw counters of term 1. -/
def T2315_lanlwT1_counters : Prop :=
  ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      (BAGraph.lanlwT1 Γ p).counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩

/-- Target 3(c): raw counters of every derivative term. -/
def T2315_lanlwD_counters : Prop :=
  ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      ∀ q ∈ lwSplit p.2, (BAGraph.lanlwD Γ p q).counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩

/-- Target 3(c): the raw order goes up by one. -/
def T2315_lanlw_ord : Prop :=
  ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      ∀ Δ ∈ BAGraph.lanlwTerms Γ p, Δ.scalingOrder = Γ.scalingOrder + 1

/-- Target 3(c): **`lanlw_scalingOrderG`** (T2295-prove (a) row 9: tight, slack 0). -/
def T2315_lanlw_scalingOrderG : Prop :=
  ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      Γ.Normal → ∀ Δ ∈ BAGraph.lanlwTerms Γ p, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ Δ.scalingOrderG

/-- (I3) as stated (T2295-prove (a) Command D: counters `2 1 1 0`, raw 2, `ordG` 1). -/
def T2315_I3 : Prop :=
  (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).counters = ⟨2, 1, 1, 0, 0, 0⟩ ∧
    (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).scalingOrder = 2 ∧
    (BAGraph.lanlwT1 baGcxy (⟨true, true, .inl 0, .inl 1⟩, [])).scalingOrderG = (((1 : ℤ)) : WithTop ℤ)

/-- (I4) as stated (Command D: counters `2 1 2 1`, raw 0, `ordG` -1). -/
def T2315_I4 : Prop :=
  (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).counters = ⟨2, 1, 2, 1, 0, 0⟩ ∧
    (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).scalingOrder = 0 ∧
    (BAGraph.lanlwT1 baGcxx (⟨true, true, .inr 0, .inr 0⟩, [])).scalingOrderG = (((-1 : ℤ)) : WithTop ℤ)

example : Prop := T2315_lanlw_scalingOrderG

example : Prop := T2315_I3 ∧ T2315_I4

end RBM.Graph.T2315Check

end
