/-
Release check for T2535 (dispatcher V5, 2026-10-17 01:35 UTC; DECISIONS §355 (2), §374): the names `docs/PAPER-VS-LEAN.md` is built on.
Statements only: `#check`; no proofs.
Run: lake env lean docs/tickets/checks/T2535-check.lean
-/
import RBM3D

#check @RBM.Endpoints.final_shape
#check @RBM.Endpoints.band_terminal
#check @RBM.Endpoints.Thm27_of_L32
#check @RBM.Endpoints.decol_holds
#check @RBM.Endpoints.locSC_holds
#check @RBM.Endpoints.QUE_holds
#check @RBM.Endpoints.QDiff_holds
#check @RBM.Endpoints.bUniv_holds
#check @RBM.Endpoints.decol
#check @RBM.Endpoints.locSC
#check @RBM.Endpoints.QUE
#check @RBM.Endpoints.QDiff
#check @RBM.Endpoints.BUniv
#check @RBM.BA.BAThm27L
#check @RBM.BA.baThm27L_any
#check @RBM.BA.baThm27L_three
#check @RBM.Univ.UNL32
