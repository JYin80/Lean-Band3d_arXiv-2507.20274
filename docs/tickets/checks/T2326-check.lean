/-
Release check for T2326 (dispatcher V1, Thu Oct  8 09:55 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §142; supervisor 2026-10-08-0944 O2).
BA-DP3 (design probe, report only): the G-in-place pilot — the edited fraction `g` of restating a merged ST proof block over a
model-generic carrier (as `FlowFM`, `BA/FlowPins.lean:332`) so that the band model and BA both instantiate it, at two sites.
Section 1 only: the merged names the probe reads (exact namespaces; `main` f38bffa).  `#check` only; never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2326-check.lean`.
-/
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.QDriftA
import RBM3D.Induction.Step3
import RBM3D.BA.FlowPins

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.ST_selfImprove_section  -- Induction/Step2Iterate.lean:284 (site 1, Step 2)
#check @RBM.Ind.stStep3RegI_holds               -- Induction/Step3.lean (T2320; the cone of site 2)
#check @RBM.BA.FlowFM                           -- BA/FlowPins.lean:332 (the carrier precedent)
