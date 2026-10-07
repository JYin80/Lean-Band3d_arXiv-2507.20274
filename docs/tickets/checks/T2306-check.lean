/-
Release check for T2306 (dispatcher V1, Tue Oct  6 14:35 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §95 (1), §105 (2)-(4),
§107, §17, §16).  LW-14e-1 "Cert": the computable model and the AND-tree kernel certificate (`k = false`, both `s`) of the
design T2288 (4686e08), portmap row LW-14e-1 (`docs/reports/T2288-portmap.md:15`); the code is copied from the compiled probe
`RBM3D/Probe/T2288Cert.lean` (branch `t/T2288`, 1228 lines: model 224-433, certificate 653-1212).
Section 1: `#check` of every merged name the copied code uses (`Graph/LWVocab` 37db678, `Graph/LWStein` 89f29cf,
`Graph/LWWeightExp` 975f4ff, `Graph/LWGGExp` 5c69cb4, `Graph/LWExpTerm3` 20de014; `Graph/ScalingOrder` 3c07bc8 through
`LGraph.scalingOrder`) and of the Mathlib / core names of its proofs; namespace of each from its enclosing
`namespace … end` block.
Section 2: none.  The only pin, `cert_all` (probe 1202), is stated with the model's own definitions (`rootInfo`, `goodB`),
which are not merged; its text is in the ticket ("Target") and is checked there by an `example` in a scratch file.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2306-check.lean`.
-/
import RBM3D.Graph.LWVocab
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LWExpTerm3

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`, T2050, 37db678; `namespace RBM.Graph` `:67-2559`): the edge and graph structures and their fields
#check @RBM.Graph.SEdge                -- :82
#check @RBM.Graph.SEdge.σ
#check @RBM.Graph.SEdge.circ
#check @RBM.Graph.SEdge.src
#check @RBM.Graph.SEdge.dst
#check @RBM.Graph.WEdge                -- :89
#check @RBM.Graph.WEdge.x
#check @RBM.Graph.WEdge.y
#check @RBM.Graph.DEdge                -- :96
#check @RBM.Graph.DEdge.eq
#check @RBM.Graph.DEdge.x
#check @RBM.Graph.DEdge.y
#check @RBM.Graph.LGraph               -- :104
#check @RBM.Graph.LGraph.solid
#check @RBM.Graph.LGraph.waved
#check @RBM.Graph.LGraph.dotted
#check @RBM.Graph.LGraph.coeff
-- maps, relabelling, the dotted partition (model of `cMerge`, `cPartition`, `belowOf`), weight split, scaling order
#check @RBM.Graph.SEdge.map            -- :412
#check @RBM.Graph.WEdge.map            -- :415
#check @RBM.Graph.DEdge.map            -- :418
#check @RBM.Graph.LGraph.relabel       -- :460
#check @RBM.Graph.LGraph.dotChoices    -- :1086
#check @RBM.Graph.LGraph.withDots      -- :1091
#check @RBM.Graph.LGraph.splitWeights  -- :1246
#check @RBM.Graph.LGraph.partition     -- :1303 (what `cPartition` models; used by LW-14e-3, not by this ticket's proofs)
#check @RBM.Graph.LGraph.scalingOrder  -- :1672 (`ord Γ.counters`)
-- `Graph/ScalingOrder` (3c07bc8; `namespace RBM.Graph` `:44-118`)
#check @RBM.Graph.ord                  -- :65

-- LW-04 (`Graph/LWStein`, T2060, 89f29cf; `namespace RBM.Graph` `:82-1894`)
#check @RBM.Graph.lwSplit              -- :891

-- LW-05 (`Graph/LWWeightExp`, T2107, 975f4ff; `namespace RBM.Graph` `:51-1507`)
#check @RBM.Graph.owxT1                -- :658

-- LW-07 (`Graph/LWGGExp`, T2120, 5c69cb4; `namespace RBM.Graph` `:56-1748`): the `(Oe2x)` families R2, R4-R8 (`fams`)
#check @RBM.Graph.oe2xR2               -- :485
#check @RBM.Graph.oe2xR4               -- :491
#check @RBM.Graph.oe2xR5               -- :500
#check @RBM.Graph.oe2xR6               -- :508
#check @RBM.Graph.oe2xR7               -- :518
#check @RBM.Graph.oe2xR8               -- :529

-- LW-14c (`Graph/LWExpTerm3`, T2255, 20de014; `namespace RBM.Gauss.Sizes` `:48-2224`): the root graph (`rootInfo`)
#check @RBM.Gauss.Sizes.LWG5Graph      -- :54

-- Mathlib / core (verified in the probe, `docs/reports/T2288-prove.md` (c))
#check @finSumFinEquiv
#check @List.getElem_of_mem
#check @List.getD_eq_getElem
#check @List.all_eq_true
#check @List.getElem?_eq_getElem
#check @Bool.or_eq_true
