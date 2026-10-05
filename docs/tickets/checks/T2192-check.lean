/-
Release check for T2192 (dispatcher V1, Mon Oct  5 07:47:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
MA-D1: main-theorem assembly design and the endpoint freeze (report only): the merged names the design builds on
(size data and model, the Green function of the endpoints, `≺`, the flow vocabulary and `zztE`, the stochastic
outputs `STMainInd` / `UNMLOut`, the K-loops `(Kn2sol)`, the propagator facts of the QUE deduction, the UN pins that
consume the freeze, the block Anderson matrix).  The BA and UN-01b names it references (`BAEnd_*`, `BAThm27`,
`UNQuek`, `UNLocAvgk`, `UNQueBA`, `UNLocAvgBA`, `UNMLOutBA`, `BAEnd_QUEL`) are on the branches `t/T2161`, `t/T2173`
(probes, not merged) and are not checked here.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2192-check.lean`.
-/
import RBM3D

-- size data, standing hypotheses, the domain and the control
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Bparam
#check @RBM.Gauss.Sizes.size_rpow_le_W_rpow
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible

-- the model, the Green function of the endpoints, blocks and distances
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.Gn
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.zdistInf
#check @RBM.zdistD
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.zdistD_le_mul_zdistInf

-- stochastic domination (union inside / per time)
#check @RBM.StochDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.stochDomAt_of_perTimeDomAt

-- the flow and `zztE`
#check @RBM.msc
#check @RBM.msc_eq_integral
#check @RBM.mE
#check @RBM.zt
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.abs_lemE_le
#check @RBM.zt_im_lemma28
#check @RBM.lemma28_quant
#check @RBM.Gauss.Sizes.seqHflow_eq_smul
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop

-- the stochastic layer: `lem:main_ind` and the outputs `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STMainInd
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Univ.UNMLOut

-- `(Kn2sol)` and the propagator facts of the QUE deduction
#check @RBM.Loop.KLK_one
#check @RBM.Loop.KLK_two
#check @RBM.Theta
#check @RBM.Prop6Diff1
#check @RBM.prop5to8_holds

-- the UN pins that consume the freeze, and the referenced Thm 2.4
#check @RBM.Univ.UNBUniv
#check @RBM.Univ.UNL32
#check @RBM.Univ.UNQueBand
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNOURow
#check @RBM.Univ.queBadMat
#check @RBM.Univ.queWindow
#check @RBM.Univ.queBound
#check @RBM.Univ.IsOrthoEigenbasis
#check @RBM.Univ.un_que_exponent

-- the block Anderson matrix and its law (DECISIONS §57 (3))
#check @RBM.Gauss.Sizes.seqHBA
#check @RBM.Gauss.Sizes.withLam
