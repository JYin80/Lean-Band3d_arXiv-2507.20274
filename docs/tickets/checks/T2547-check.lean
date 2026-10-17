/-
Release check for T2547 (dispatcher V5, 2026-10-17 08:15 UTC; DECISIONS §371): a comment-only ticket must leave the
statements of the published roots unchanged (compile on `main` before and on `t/T2547` after).
Statements only: Prop-valued `example`s whose term is the name, and `#check`; no proofs.
Run: lake env lean docs/tickets/checks/T2547-check.lean
-/
import RBM3D

example : RBM.Univ.UNL32 →
    (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧
      RBM.Endpoints.Thm27 := RBM.Endpoints.final_shape
example : RBM.Univ.UNL32 → RBM.Endpoints.Thm27 := RBM.Endpoints.Thm27_of_L32
example : RBM.Univ.UNL32 →
    RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff :=
  RBM.Endpoints.band_terminal
example : RBM.Univ.UNL32 → RBM.BA.BAThm27L 3 := RBM.BA.baThm27L_three
#check @RBM.BA.baThm27L_any
#check @RBM.BA.baThm27L_of_ML
#check @RBM.BA.baEnd_BUnivL_of_ML
#check @RBM.Endpoints.bUniv_holds
#check @RBM.Univ.UNL32
