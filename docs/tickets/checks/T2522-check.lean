/-
Release check for T2522 (dispatcher V5, 2026-10-16 20:13 UTC; DECISIONS §367): the roots of the dead-code report exist on `main`.
Statements only (`#check`); no proofs.
Run: lake env lean docs/tickets/checks/T2522-check.lean
-/
import RBM3D

-- core roots
#check @RBM.Endpoints.final_shape        -- Main/FinalShape:43
#check @RBM.Endpoints.Thm27              -- Main/FinalShape:36
#check @RBM.Endpoints.Thm27_of_L32       -- Main/FinalShape:39
#check @RBM.Endpoints.band_terminal      -- Main/BandTerminal:104
-- group G3 (general-d BA forms)
#check @RBM.BA.baThm27L_any              -- BA/UNBUniv:286
#check @RBM.BA.baThm27L_of_ML            -- BA/UNBUniv:271
#check @RBM.BA.baEnd_BUnivL_of_ML        -- BA/UNBUniv:262
-- group G4
#check @RBM.Endpoints.bUniv_holds        -- Main/BUnivHolds:227
-- sanity names
#check @RBM.BA.baThm27L_three            -- BA/UNBUniv:281
#check @RBM.BA.unMLOutBA_three           -- BA/MainIndTermBA:47
