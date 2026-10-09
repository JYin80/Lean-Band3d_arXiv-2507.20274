/-
Release check for T2361 (dispatcher V1, Fri Oct 9 02:52 UTC 2026; DECISIONS §163 (3)).  UN-50b PathBounds: port of RBM2D `GUEPhase` with a statement table.
Merged names (`main` 8d76de9).  Run: `lake env lean docs/tickets/checks/T2361-check.lean`.
-/
import RBM3D.Universality.GUEPhase.HypB
import RBM3D.Universality.GUEPhase.BoundsA
import RBM3D.Universality.GUEPhase.DuhamelC
import RBM3D.Universality.GUEPhase.EntryGrid
import RBM3D.Universality.GUEPhase.BootstrapAt
import RBM3D.Universality.GUEPhase.LLTransfer
import RBM3D.Universality.GUEPhase.ProcK

#check @RBM.Univ.GUEPhase.GUEPathBounds
#check @RBM.Univ.GUEPhase.Bounds_path
#check @RBM.Univ.GUEPhase.BoundsACheck.pathBounds_of_forall_highProbAt
#check @RBM.Univ.GUEPhase.eq727GEAt
#check @RBM.Univ.GUEPhase.eq728GAt
#check @RBM.Univ.GUEPhase.rhs745G
#check @RBM.Univ.GUEPhase.rhs746G
#check @RBM.Univ.GUEPhase.gueKproc_detDom
#check @RBM.Univ.GUEPhase.gueGrid_entry_bound
#check @RBM.Univ.GUEPhase.gueGrid_loop_duhamel
#check @RBM.Univ.GUEPhase.HypB_fixed
#check @RBM.Univ.GUEPhase.HypB_eG_745
#check @RBM.Univ.GUEPhase.HypB_eG_746
#check @RBM.Univ.GUEPhase.HypB_entry_le
#check @RBM.Univ.GUEPhase.Hyp_Kt_detDom
#check @RBM.Univ.GUEPhase.gueGridK
#check @RBM.Univ.GUEPhase.oull_of_pathBounds
#check @RBM.Green.flucAvg_card_Idx_eq_size
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Univ.UNMLOut
