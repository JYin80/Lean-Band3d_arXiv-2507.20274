/-
Release check for T2325 (dispatcher V1, Thu Oct  8 04:35 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §138, §135 (1); supervisor
2026-10-08-0344 Q1 and O1).
BA-DP2 (block Anderson design probe, report only): can the BA graph rows (BA-L3, BA-L4) instantiate the merged LW engine
(`LWLvl1`, the LW-14e expansion) and the BA chain rows (BA-T1…T8, U1…U6, V1…V3) the merged ST-2…ST-5 theorems through
model-generic statements, and the BA re-portmap with measured class ratios.
Section 1 only: the merged names the probe reads (exact namespaces; file:line on `main` 630de05).
`#check` only: no definition, no theorem, no proof.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2325-check.lean`.
-/
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.BAExpandW
import RBM3D.Induction.Step2Defs
import RBM3D.BA.Step1
import RBM3D.BA.Step1Fam
import RBM3D.Universality.PinsK

/-! ## 1. Merged names -/

-- the LW graph layer and engine (`RBM.Graph`, `RBM.Gauss.Sizes`)
#check @RBM.Graph.LGraph                       -- Graph/LWVocab.lean:104
#check @RBM.Graph.Lvl1Good                     -- Graph/LWLvl1.lean:989
#check @RBM.Graph.lvl1_exists_step             -- Graph/LWLvl1.lean:3655
#check @RBM.Gauss.Sizes.expandG                -- Graph/LWExpTerm5.lean:189
#check @RBM.Gauss.Sizes.ExpandGSum             -- :199
#check @RBM.Gauss.Sizes.lwExpandIdentity_holds -- :594
-- the BA graph layer (`RBM.Graph`)
#check @RBM.Graph.BAGraph                      -- Graph/BAVocab.lean:55
#check @RBM.Graph.BAlweight                    -- Graph/BAExpandW.lean:82
#check @RBM.Graph.BAGraph.lanlwTerms           -- :144
-- the ST chain pin and the BA chain (`RBM.Gauss.Sizes`, `RBM.BA`)
#check @RBM.Gauss.Sizes.STStep2                -- Induction/Step2Defs.lean:599
#check @RBM.BA.BAConArg''                      -- BA/ConArg.lean:70
#check @RBM.BA.BABootstrap'                    -- BA/Step1Boot.lean:148
#check @RBM.BA.baBootstrap'_holds              -- BA/Step1.lean:576
#check @RBM.BA.BAStep1                         -- BA/Step1Fam.lean:361
-- the model-generic precedent (UN-51g, T2282)
#check @RBM.Univ.UNOURowk                      -- Universality/PinsK.lean:426
