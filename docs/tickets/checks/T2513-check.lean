/-
Release check for T2513 (dispatcher V4, 2026-10-15; DECISIONS §336; supervisor 2026-10-15-0643 Q2 (A), MNO-C1–C4;
not compiled by the dispatcher).  M/N MN-D3 design gate: the merged statements of 0643 Q2's list, read by name.
Statements only; merged modules only; no pins (D1's filtered texts are written by the gate's probe).
Run: lake env lean docs/tickets/checks/T2513-check.lean
-/
import RBM3D.BA.UNPins
import RBM3D.BA.EMCTE2BA
import RBM3D.BA.RandomLayerBGBA
import RBM3D.Universality.GUEPhase.RandomLayerBG
import RBM3D.Universality.OUInterfaceK
import RBM3D.Universality.PinsK
import RBM3D.Universality.PinsC2
import RBM3D.Main.BandTerminal
import RBM3D.Main.BUnivHolds

-- K-row layer (Universality/PinsK, OUInterfaceK)
#check @RBM.Univ.UNLocAvgk          -- PinsK:406
#check @RBM.Univ.UNQuek             -- PinsK:398
#check @RBM.Univ.UNOUClaimsk        -- PinsK:421
#check @RBM.Univ.UNOURowk           -- PinsK:426
#check @RBM.Univ.UNEMCTE2Rowk       -- PinsK:429
#check @RBM.Univ.UNJakUywRowk       -- PinsK:435
#check @RBM.Univ.UNClaimRowk        -- PinsK:442
#check @RBM.Univ.UNG1Rowk           -- OUInterfaceK:101
#check @RBM.Univ.ouRowk_of_pins     -- OUInterfaceK:292
#check @RBM.Univ.GUEPhase.g1Rowk_of_inputsG  -- RandomLayerBG:399
#check @RBM.Univ.UNCoreC''          -- PinsC2:106 (per d)

-- BA readings and rows (BA/UNPins, BA/EMCTE2BA)
#check @RBM.Univ.UNQueBA            -- UNPins:99
#check @RBM.Univ.UNLocAvgBA         -- UNPins:103
#check @RBM.Univ.UNMLOutBA          -- UNPins:110
#check @RBM.Univ.un_claimAll_of_rowsBA  -- UNPins:142
#check @RBM.Univ.UNTrLocalBARow     -- UNPins:169
#check @RBM.Univ.UNTrLocalInitBARow'  -- UNPins:181
#check @RBM.BA.BAEnd_BUnivL         -- UNPins:343
#check @RBM.Univ.UNQueBA_of_BAEnd_QUEL  -- UNPins:357
#check @RBM.Univ.baBUniv_of_rows    -- UNPins:367
#check @RBM.Univ.BAInst.inst_UNOURowBA  -- UNPins:1024
#check @RBM.Univ.unJakUywRowBA_holds    -- EMCTE2BA:766

-- band terminal (axioms compared before / after, MNO-C1)
#check @RBM.Endpoints.band_terminal -- Main/BandTerminal:104
#check @RBM.Endpoints.bUniv_holds   -- Main/BUnivHolds:227
