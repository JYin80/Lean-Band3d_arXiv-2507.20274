/-
Release check for T2348 (dispatcher V1, Thu Oct 8 22:52 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §158; supervisor 2026-10-08-2244 O1).
LW-13b-D (report only): the design of LW-13b after the T2344 stage-1a FAIL.  Merged names only (`main` f9f498d).
Run: `lake env lean docs/tickets/checks/T2348-check.lean`.
-/
import RBM3D.Graph.LWEngine
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWMomExp
import RBM3D.Graph.LWMomExpD
import RBM3D.Graph.LWMomExpFar

#check @RBM.Graph.lw_localregularX            -- Graph/LWEngine.lean:771 (the engine)
#check @RBM.Graph.lwEngine_exists_stepX       -- Graph/LWEngine.lean:455
#check @RBM.Graph.LocStepX.eval               -- Graph/LWEngine.lean:418 (the per-constructor identity)
#check @RBM.Graph.LocStepX.eval_one           -- Graph/LWEngine.lean:447
#check @RBM.Graph.lwGtoAG_holds               -- Graph/AuxGraph.lean:1018
#check @RBM.Graph.lwXiClaim_holds             -- Graph/AuxGraph2.lean:965 (G2: goes through `LWPsiAll`)
#check @RBM.Graph.LWGbyXi                     -- Graph/AuxGraph2.lean:1106 (`R` free, `2R+1 ≤ ρ`)
#check @RBM.Graph.AnpFarAndAt                 -- Graph/LWMomExpFar.lean:80
#check @RBM.Graph.lwMomExpFar_and             -- Graph/LWMomExpFar.lean:338
#check @RBM.Graph.lwMomExpFar_farDAnd         -- Graph/LWMomExpFar.lean:42
#check @RBM.Graph.AnpDetNearAt                -- Graph/LWMomExp.lean:900
#check @RBM.Graph.lwMomExp_near               -- Graph/LWMomExp.lean:1023
#check @RBM.Graph.lwMomExp_nearD              -- Graph/LWMomExp.lean:532 (intersection domain; G4)
#check @RBM.Graph.lwMomExp_valOnD_eq_valOn    -- Graph/LWMomExpD.lean:18 (T2312)
#check @RBM.Gauss.Sizes.lwMoment_holds        -- Graph/LWMoment.lean:1785 (T2297)
#check @RBM.Gauss.Sizes.LWMomentExp           -- Graph/LWPins.lean:341 (owed; the target of LW-13b)
