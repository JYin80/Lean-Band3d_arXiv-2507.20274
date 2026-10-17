/-
Release check for T2530 (dispatcher V5, 2026-10-17 01:10 UTC; DECISIONS §373): group Chain and Green deletes unreached declarations in its own files only.
The statements of the kept roots must be unchanged (compile on `main` before and on `t/T2530` after).
Statements only: `#check` and Prop-valued `example`s whose term is the name; no proofs.
Run: lake env lean docs/tickets/checks/T2530-check.lean
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
#check @RBM.BA.baThm27L_any          -- G3 (MNC-C1)
#check @RBM.BA.baThm27L_of_ML        -- G3
#check @RBM.BA.baEnd_BUnivL_of_ML    -- G3
#check @RBM.Endpoints.bUniv_holds    -- G4
