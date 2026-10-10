/-
Release check for T2372 (dispatcher V2, Sat Oct 10 04:29 UTC 2026; DECISIONS §184).  UN-10a: `Universality/NormBand.lean`,
the band-model row `UNNormBandRow` (eigenvalue bound with high probability).
Part 1: the target statement (an existing pin, `Universality/Pins.lean:834`; no new pin).
Part 2: merged names the route uses.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2372-check.lean
-/
import RBM3D.Universality.Pins
import RBM3D.Gauss.FineModel
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Sizes
import RBM3D.Universality.GUEPhase.Markov

open RBM RBM.Gauss RBM.Univ

/-! ## Part 1: the target statement -/
#check @RBM.Univ.UNNormBandRow
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.UNModel.band
example : Prop := RBM.Univ.UNNormBandRow

/-! ## Part 2: merged names -/
#check @RBM.Gauss.Sizes.seqP_map_eval
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqXmat_isHermitian
#check @RBM.Gauss.Sizes.seqGvar
#check @RBM.Gauss.Xentry
#check @RBM.Gauss.measurable_Xentry
#check @RBM.Path.highProbAt_iInter
#check @RBM.Univ.GUEPhase.gue_highProb_incr_le
#check @RBM.Gauss.SizesInst.sz0
