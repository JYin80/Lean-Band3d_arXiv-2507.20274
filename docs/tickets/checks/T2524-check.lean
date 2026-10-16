/-
Release check for T2524 (dispatcher V5, 2026-10-16 23:40 UTC; DECISIONS §371): the merged names the BA-D design gate reads.
Statements only: `#check` and Prop-valued `example`s whose term is the name; no proofs.
Run: lake env lean docs/tickets/checks/T2524-check.lean
-/
import RBM3D

example : RBM.Univ.UNL32 → RBM.BA.BAThm27L 3 := RBM.BA.baThm27L_three
#check @RBM.BA.baThm27L_any
#check @RBM.BA.baThm27L_of_ML
#check @RBM.BA.baStep5III_holds
#check @RBM.BA.baPfStep5_of_walk
#check @RBM.BA.BAStep5IIIWalk
#check @RBM.BA.BAStep5IIIFromWalk
#check @RBM.BA.BAStep5IIIWalkConcl
#check @RBM.BA.BAStep5IIIGood
#check @RBM.BA.BAStep5IIIGoodThm
#check @RBM.BA.baStep5IIIGoodThm_holds
#check @RBM.BA.baStep5IIIWalk_holds
#check @RBM.BA.baStep5IIIFromWalk_holds
#check @RBM.BA.STStep5IIIgL
#check @RBM.BA.STIngR5gL
#check @RBM.Endpoints.final_shape
