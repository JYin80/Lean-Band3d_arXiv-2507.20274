Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct 16 21:03:35 UTC 2026

(i) No exponents. T2523 is a deletion ticket (unreachable declarations, whole-dead modules, check clutter); it has no mathematical content, no exponent, threshold or constant.

(ii) Not applicable. No target theorem is added or restated; the kept roots' statements are unchanged and pinned by `docs/tickets/checks/T2523-check.lean` (hub compile on main e3540151: exit 0, no error lines, per CONTROL H335 (3)).

Verdict: T2523 PASS.

## (b) Script output: stage 1b, resumed from the WIP commit a9d1a6d4 (written Sat Oct 17 03:34:24 UTC 2026)

Branch `t/T2523`, last commit `8395d2d6`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2523`. Lines marked `$` are commands, the lines below them their verbatim output. `$SP` is the scratch directory of the hub session (`T2523/`).

Narrative (facts; the evidence is in the blocks B1-B16 below).

1. Start. Stage 1b resumed at 01:13:39 UTC from the hub's WIP commit a9d1a6d4 (B1). The final tree is the output of the deletion script (pasted at the end) on main's `RBM3D/`, plus 17 `git rm` (B11).
2. Build 8 of the WIP tree (01:13:59-01:48:55 UTC, B2) compiled every module; the last step, `#assert_rbm_axioms` at `RBM3D.lean:656`, failed: 45 premises that no theorem proves were in none of the five registry lists.
3. Cause. 3 of the 45 (`Graph.lvl1Split.below`, `Lvl1Reach.below`, `BAReach.below`) are registry entries (`Axioms.lean:290-292` on main) that the script had removed because T2522 (g) calls them unreached; the constants stay (generated for surviving inductives). The other 42 are `Prop`s that surviving theorems assume; on main each had 1 to 6 proving theorems (70 in all: instance and witness theorems such as `bandStep2_GridAssemblyHypN` for `GridAssemblyHypNg`), all unreached and so deleted; without them the scan finds the `Prop` unproved and unregistered.
4. Fix, under the ticket's rule (restore, list with the reason, rewrite no proof). (i) The 3 entries stay in the registry, and so does `STStep6`; section (g) of the tool now lists a registry name as gone only if its constant does not `survive` (a generated constant counts with its inductive). (ii) For each of the 42 `Prop`s one proving theorem is kept, the one whose closure adds the fewest constants, with the helpers it needs: 42 theorems and 68 helpers, 1094 lines (R2 in B14). They are roots of the tool (`scanProvers`). I chose them with a scratch emulation of the scan on main's library (`scan/DeadSim.lean`, the tool plus the scan): with the roots of the first run it reports the 42 (B3, iteration 0), with the 42 theorems none (iteration 1). I added no registry class for the 42 `Prop`s: the ticket names none (see (d) 1).
5. Result. Build 9 (02:08:56-03:20:59 UTC, B4) passes; it runs `#assert_rbm_axioms` and the premise scan. The four endpoints depend on the three standard axioms only (B5). `T2523-check.lean` compiles on the branch (B6); the nine kept statements are unchanged (B7).
6. Tool on the branch (B13, 03:21:10-03:21:50 UTC): 0 unreached non-meta declarations, 0 whole-dead modules, 0 unreached registry names; the four groups lie inside the closure. Declarations 22738 = 32770 - 10032. T2522 core + G1-G4 is 32770 - 10227 = 22543 (its (e) says 10243 unreached; the groups add 16); the difference 195 = 85 restored by the first run (R1) + 110 kept for the scan (R2). Reached constants: 35045 on the branch and on main with the same roots; T2522 gave 34795 (core) and 34812 (with G1-G4, scratch `dead1.txt`).
7. Registry (B12): the 49 names whose constants are gone are removed (11 owed, 19 structural, 4 refuted, 15 superseded; T2522 (g) gave 11/23/4/16, and 11/22/4/16 with G1-G4 as roots); `UNG1Rowk` is removed; `UNOULLk` moved to `structuralProps` with its owner text.
8. Size. 17 files deleted, 633 modified (B10). `git diff --shortstat main...t/T2523`: 489 insertions by git's default algorithm (291 in `RBM3D/`, 198 in the tool), 249 with `--minimal` (51 in `RBM3D/`). B15 lists the 51 added lines of the minimal diff (5 imports, `open` and simp-list edits, the registry). The tool's added lines are mostly its root lists ((d) 6). No declaration line is added under `RBM3D/` (B10).
9. Clutter. Only the `example`s of the four exempt files remain (B8); `RBM3D/Main/BandTerminal.lean` lost 4 lines (the unreached theorem `unClaimRowBA_holds`); `Test/InterfaceShape.lean` is deleted. The deletion leaves no namespace or section empty (B8: the same 5 blocks, all in `Induction/Step2Iterate.lean`, are empty or hold only `open`/`variable` lines on main and on the branch); unused `variable` lines are handled by the script (step 3), not checked separately.
10. Not done, found on the way: the tool's unit rule hides two unreached declarations (B16, (d) 2).

```text
--- B1. branch and starting point
$ git log --oneline -4 t/T2523 | cut -c1-110; git status --short | wc -l
8395d2d6 T2523: keep the 42 premise provers (scan) with their helpers; G1-G4 and restored lists as tool roots;
a9d1a6d4 T2523: deletions as applied at the stop, 01:02 UTC (WIP)
08e88ffb T2523: DeadDecls.lean: groups G1-G4 are roots of the closure
e3540151 H335: T2523 (release clean-up step 2) ticket and check, supervisor 2046 (M/N closed), REQ MNclose, DE
       0
$ git show --shortstat --format=%h a9d1a6d4 | tail -2

 650 files changed, 408 insertions(+), 150526 deletions(-)
--- B2. build 8: full build of the WIP tree (scratch log build8.log): every module compiled, the scan in RBM3D.lean failed
$ cat $SP/build8.start $SP/build8.end | tr '\n' ';'; echo; grep -n 'error: RBM3D.lean' $SP/build8.log | cut -c1-170; sed -n '96,140p' $SP/build8.log | grep -c 'RBM\.'
Sat Oct 17 01:13:59 UTC 2026;Sat Oct 17 01:48:55 UTC 2026;
95:error: RBM3D.lean:656:0: axiom audit: 45 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refuted
45
$ grep -c ' RBM.Graph.lvl1Split.below\| RBM.Graph.Lvl1Reach.below\| RBM.Graph.BAReach.below' $SP/build8.log; grep -n 'lvl1Split.below\|Lvl1Reach.below\|BAReach.below' $SP/pristine/RBM3D/Test/Axioms.lean | cut -c1-90
3
290:   `RBM.Graph.lvl1Split.below, -- auxiliary predicate that Lean generates for the recu
291:   `RBM.Graph.Lvl1Reach.below, -- auxiliary predicate that Lean generates for the recu
292:  `RBM.Graph.BAReach.below, -- auxiliary predicate that Lean generates for the recursi
--- B3. the scan simulated on main's library (scratch scan/DeadSim.lean = the tool + 70 lines; same roots as the tool of this branch)
$ grep -E '^SIM iter' $SP/scan/sim.out | cut -c1-60; grep -c '^  premise' $SP/scan/sim.out
SIM iter 0: extra roots 0, reached 34899, unregistered 42: [
SIM iter 1: extra roots 42, reached 35045, unregistered 0: [
42
--- B4. build 9: full build of the fixed tree (scratch log build9.log), then the same command at default log level
$ cat $SP/build9.start $SP/build9.end | tr '\n' ';'; echo; tail -2 $SP/build9.log
Sat Oct 17 02:08:56 UTC 2026;Sat Oct 17 03:20:59 UTC 2026;
Build completed successfully (4426 jobs).
exit 0
$ grep -n 'axiom audit:\|premises found by scanning\|^registry:\|Build completed' $SP/build_final.log | cut -c1-150
6545:info: RBM3D.lean:656:0: axiom audit: 10486 theorems, 3859 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
6651:premises found by scanning: 94 (borrowed 1, owed 36, structural 57, refuted 0, superseded 0).
6652:registry: 2 borrowed + 98 owed + 130 structural + 3 refuted + 4 superseded; 143 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
6796:Build completed successfully (4426 jobs).
--- B5. #print axioms of the kept roots (scratch file final/axioms_check.lean, not committed)
$ grep '#print' $SP/final/axioms_check.lean | tr '\n' ';'; echo; lake env lean $SP/final/axioms_check.lean
#print axioms RBM.Endpoints.final_shape;#print axioms RBM.Endpoints.band_terminal;#print axioms RBM.BA.baThm27L_any;#print axioms RBM.Endpoints.bUniv_holds;
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
--- B6. release check on the branch
$ lake env lean docs/tickets/checks/T2523-check.lean 2>&1 | grep -c 'error'; lake env lean docs/tickets/checks/T2523-check.lean >/dev/null 2>&1; echo "exit $?"
0
exit 0
--- B7. statements of the kept roots, extracted from main and from the branch by script (line numbers stripped for the diff)
$ python3 -I $SP/rep/stmt.py | cut -c1-230
RBM3D/Main/FinalShape.lean:43  theorem final_shape : RBM.Univ.UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
RBM3D/Main/FinalShape.lean:36  def Thm27 : Prop
RBM3D/Main/FinalShape.lean:39  theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27
RBM3D/Main/BandTerminal.lean:100  theorem band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff
RBM3D/Main/BUnivHolds.lean:227  theorem bUniv_holds : UNNormBandRow → UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail → UNBUniv
RBM3D/BA/UNBUniv.lean:262  theorem baThm27L_three : UNL32 → BAThm27L 3
RBM3D/BA/UNBUniv.lean:267  theorem baThm27L_any (d : ℕ) (hd : 3 ≤ d) (h5 : STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (h32 :
RBM3D/BA/UNBUniv.lean:257  theorem baThm27L_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAThm27L d
RBM3D/BA/UNBUniv.lean:248  theorem baEnd_BUnivL_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAEnd_BUnivL d
$ diff <(sed -E 's/:[0-9]+  / /' $SP/rep/stmt_main.txt) <(python3 -I $SP/rep/stmt.py | sed -E 's/:[0-9]+  / /') && echo 'statements identical (9 declarations)'
statements identical (9 declarations)
--- B8. nonempty instances: the example blocks of the four exempt files are kept (compiled in the build above); no other clutter; no empty scope created (second command: branch, then main)
$ for f in Main/FinalShape Main/BandTerminal BA/MAPins Main/BUnivHolds; do echo "$f: $(grep -c '^example' RBM3D/$f.lean) examples"; done
Main/FinalShape: 7 examples
Main/BandTerminal: 10 examples
BA/MAPins: 5 examples
Main/BUnivHolds: 2 examples
$ git diff --stat main...t/T2523 -- RBM3D/Main/FinalShape.lean RBM3D/Main/BandTerminal.lean RBM3D/BA/MAPins.lean RBM3D/Main/BUnivHolds.lean | cat
 RBM3D/Main/BandTerminal.lean | 4 ----
 1 file changed, 4 deletions(-)
$ python3 -I $SP/rep/emptyscopes.py | cut -c1-200; (cd $SP/pristine && python3 -I $SP/rep/emptyscopes.py | cut -c1-120)
3992 namespace/section/mutual blocks scanned; 5 empty or only open/variable/universe/set_option: [('RBM3D/Induction/Step2Iterate.lean', 'section', 'L2', 1), ('RBM3D/Induction/Step2Iterate.lean', 'name
4978 namespace/section/mutual blocks scanned; 5 empty or only open/variable/universe/set_option: [('RBM3D/Induction/Step
$ grep -rnE '^\s*(example|#print|#check|#eval|#guard_msgs|#reduce|#synth)\b' RBM3D | grep -vE '^RBM3D/(Main/FinalShape|Main/BandTerminal|BA/MAPins|Main/BUnivHolds)\.lean' | cut -c1-120
RBM3D/Chain/NQEndFlowGen.lean:716:example is a stochastic premise that is another gate's pin (`STKboundgL`, `STKwardgL`,
$ tail -2 RBM3D.lean; ls RBM3D/Test; grep -rnwE 'sorry|admit|native_decide' RBM3D | grep -vE ':[0-9]+:\s*(--|/-)|Test/Axioms.lean' | wc -l
/-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
#assert_rbm_axioms
AuditNegative.lean
Axioms.lean
       0
--- B9. name clash (new names are in the tool, namespace DeadDecls; none in RBM3D/)
$ grep -rnE '(def|theorem|lemma|abbrev) +(DeadDecls\.)?(restoredRoots|scanProvers|survives)\b' RBM3D | wc -l; grep -nE '^(partial )?def (restoredRoots|scanProvers|survives)' docs/claude-team/tools/DeadDecls.lean | cut -c1-60
       0
82:def restoredRoots : List Name :=
174:def scanProvers : List Name :=
339:partial def survives (env : Environment) (inScope : Name
--- B10. diff statistics (default diff, then git diff --minimal)
$ git diff --shortstat main...t/T2523; git diff --shortstat main...t/T2523 -- RBM3D RBM3D.lean; git diff --minimal --shortstat main...t/T2523; git diff --minimal --shortstat main...t/T2523 -- RBM3D RBM3D.lean
 650 files changed, 489 insertions(+), 149173 deletions(-)
 649 files changed, 291 insertions(+), 149162 deletions(-)
 650 files changed, 249 insertions(+), 148933 deletions(-)
 649 files changed, 51 insertions(+), 148922 deletions(-)
$ git diff --name-status main...t/T2523 | cut -f1 | sort | uniq -c | tr '\n' ' '; git diff --name-only main...t/T2523 | grep -vcE '^(RBM3D/|RBM3D.lean$|docs/claude-team/tools/DeadDecls.lean$)'
  17 D  633 M 0
$ git diff -U0 main...t/T2523 -- docs/claude-team/tools/DeadDecls.lean | grep '^@@' | cut -d@ -f3 | cut -c1-20 | tr '\n' ';'; echo
 -11,6 +11,6 ; -78,2 +78,142 ; -195,0 +336,16 ; -264,0 +421,10 ; -311 +477 ; -409 +575 ; -460 +626 ; -472,0 +639,21 ;
$ git diff --minimal main...t/T2523 -- RBM3D RBM3D.lean | grep '^+' | grep -v '^+++' | grep -cE '^\+\s*((private|protected|noncomputable) +)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b'
0
$ git diff main...t/T2523 -- RBM3D.lean | grep -E '^[-+]import' | cut -c1-1 | sort | uniq -c | tr '\n' ' '; git diff main...t/T2523 -- RBM3D.lean | grep -E '^\+import' | wc -l
  17 -        0
--- B11. the worktree equals the output of the script below on main's RBM3D/ (dry run in scratch), apart from the 17 deleted files
$ diff -rq $SP/verify2/RBM3D RBM3D | grep -v '^Only in' | wc -l; diff -rq $SP/verify2/RBM3D RBM3D | grep '^Only in' | wc -l; diff $SP/verify2/RBM3D.lean RBM3D.lean && echo 'RBM3D.lean identical'
       0
      17
RBM3D.lean identical

--- B12. registry lists of `RBM3D/Test/Axioms.lean`: entries on main and on the branch
$ python3 -I $SP/rep/registry_counts.py $SP/pristine/RBM3D/Test/Axioms.lean
borrowedProps      2 ->   2   removed  0   added []
owedProps        111 ->  98   removed 13   added []
structuralProps  148 -> 130   removed 19   added ['RBM.Univ.UNOULLk']
refutedProps       7 ->   3   removed  4   added []
supersededProps   19 ->   4   removed 15   added []
RBM.Univ.UNG1Rowk main: ['owedProps']  branch: []
RBM.Univ.UNOULLk main: ['owedProps']  branch: ['structuralProps']

--- B13. the tool of this branch on this branch (`lake env lean docs/claude-team/tools/DeadDecls.lean`, 03:21:10-03:21:50 UTC, exit 0), summary by script
DeadDecls report: modules 6766, in scope 656, constants in scope 42489, counted declarations 22807
- (35 constants in RBM.Audit and its sub-namespaces; 35045 in-scope constants reached in the core)
- every core root reached: true
- RBM.BA.baThm27L_three: reached in the core
- RBM.BA.unMLOutBA_three: reached in the core
- RBM.Endpoints.bUniv_holds: reached in the core
tool section (c) modules with no reached declaration (whole module dead), and the modules that import them
(none)
tool section (e) totals
- modules in scope: 656; with counted declarations: 653
- declarations (non-meta units): 22738; meta declarations: 69 (unreached meta: 60)
- unreached (non-meta): 0
- sum of unreached line spans (end-start+1 per declaration): 0
- unreached lines counted once (union of the intervals per module): 0
- modules with no reached declaration: 0
### G1: constants of the `example`s in Main/BandTerminal.lean §Instances
- roots: 20; already reached in the core: 20; not reached in the core: 0
### G2: constants of the `example`s in BA/MAPins.lean
- roots: 31; already reached in the core: 31; not reached in the core: 0
### G3: the general-`d` BA forms
- roots: 3; already reached in the core: 3; not reached in the core: 0
### G4: `bUniv_holds` and the constants of the `example`s in Main/BUnivHolds.lean
- roots: 16; already reached in the core: 16; not reached in the core: 0
### RBM.Audit.allowedAxioms  (lines 59-60): 3 names, 0 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.borrowedProps  (lines 84-93): 2 names, 2 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.owedProps  (lines 95-219): 98 names, 98 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.refutedProps  (lines 360-371): 3 names, 3 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.structuralProps  (lines 221-358): 130 names, 130 in scope, 0 unreached in the core, 0 not constants
### RBM.Audit.supersededProps  (lines 373-385): 4 names, 4 in scope, 0 unreached in the core, 0 not constants
- totals over 9 name lists: 240 names, 237 in scope, 0 unreached in the core
tool section (h) namespaces of `RBM` all of whose declarations are unreached (the namespace disappears with them)
(none)

--- B14. kept declarations (T2522 (b) names, as `Module.name`); R1 from the first run, R2 by the scan
$ python3 -I $SP/rep/lists.py
(R1) 85 declarations of T2522 (b) restored (tool list `restoredRoots`); reason recorded in the tool doc (`restoredRoots`): a reached proof uses them through simp/dsimp/unfold, with no trace in the proof term; kinds (regex on the text of main): {'rfl-proved theorem': 58, '@[simp] rfl-proved theorem': 21, 'def': 2, 'theorem': 3, 'abbrev': 1}
  BA: KCactus.BAMcharge_def, Ward.BAMss_pp_apply, KCactus.BAslotStart_leaf, GUETwistBA.GUETwistBA_Pi_apply, GreenMinor3.GreenMinor_a_zero, TwistAvgA2.TwistAvgA2_G_eq, TwistGridWTail.TwistGridWTail_cm_apply, TwistStep2.TwistStep2_eta_eq
  Chain: StepDecompGen.StepDecompGen_wd_nil
  Gauss: FineModel.fineModel_Hflow_apply, FineModel.fineModel_Xmat_apply, LoopFlowStein.wordDirectionMap_cons, LoopFlowStein.wordDirectionMap_nil
  Graph: BAExp14c.BAExp14c_D_G, BAExp14c.BAExp14c_D_S', BAExp14c.BAExp14c_blk, BAEngine.BAEngine_col_transpose, BAGGOp.BAGGOp_rho2_b, BAGGOp.BAGGOp_rho2_u, BALocReg1B.BALocReg1B_extMap, BALocReg1B.BALocReg1_molMap_mk, BALocReg2.BALocReg2_bpS_dst, BALocReg2.BALocReg2_bpS_src, BALocReg2.BALocReg2_bpS_σ, BAS3CloseC.BAS3Close_D_M, BAS3Close.BAS3Close_lift_bpv, BAShapeO2.BAShapeO2_rho2_zero, BASim2.BASim_owxEmb2_inr, LocalRegular2.localReg2_cends_mk, AnpKey5.anpKey5_inS_inl, LocalRegular2.localReg2_owxEmb_inr_eq, LocalRegular6d.localReg6d_map_mk, LocalRegular6d.localReg6d_phi_a, LocalRegular6d.localReg6d_phi_b, LWEngine.lwEngine_col_transpose, LWEngine.lwEngine_dotChoices_sc, LWSymm.lwSymm_slice_flip
  Green: MinorDiff.mE_zero, MinorDiff.sqrt_four, MinorDiff.toyHalf, MinorDiff.toyPow, FlucIter.applyOps_nil, MinorDiffCond.badTower_zero, MinorDiff.deltaFam_apply, FlucVanish.epsHom_inl, FlucVanish.epsHom_inr, MinorGoodLe.flucIterHigh_seqHflow_apply, MinorGoodLe.flucIterHigh_slice_apply, MinorDiff.gFam_apply, MinorDiff.gInvFam_apply, MinorDiff.iterDeltaFam_nil, MinorGoodLe.minorDiff_nil, EntryCore.minorGreen_apply, EntryCore.minorMat_apply, FlucIter.numQ_nil, RowIndep.slice_apply
  Hierarchy: ContractionBasic.contraction_coordinateMatrix_apply, ContractionBasic.contraction_gloopProd_cons, ContractionBasic.contraction_loopL_eq, ContractionSecondLoop.secondLoop_gloopProd_nil
  Induction: B45.B45_STKloop_eq, Step2Defs.STLM_seqHflow, NewKLK.nkl_STmsig_eq, LoopGenN.LoopGenN_gloopProd_cons, LoopGenN.LoopGenN_gloopProd_nil, LoopGenN.LoopGenN_loopL_eq, QVN.QVN_cm_apply, QVN.QVN_wd_nil, Split.gchain_single, Split.gloopProd_nil, ConArgDet.zSig_false, ConArgDet.zSig_true
  Loop: GLoopFlow.gloopProd_cons, GLoopFlow.gloopProd_nil, KLWard.KLWard_flipIdx_length
  Path: QVIdentity.QVIdentity_cm_apply
  Universality: GUEPhase.DuhamelA1.Duhamel_coordinateMatrix_apply, GUEPhase.Generator.Generator_gloopProd_cons, GUEPhase.Generator.Generator_gloopProd_nil, GUEPhase.Generator.Generator_loopL_eq, GUEInvariance.GUE_Tpp_eucl_apply, GUEInvariance.GUE_Xmat_apply, GUEInvariance.GUE_real_smul, PinsK.unPinsK_band_bulk, PinsK.unPinsK_toC_toUNModel
(R2) 110 declarations of T2522 (b) kept for the premise scan: 42 provers (premise <- prover [+constants reached]) and 68 helpers they use (1094 lines)
  BA: BA.BAConArgHyp <- inst_BAConArgHyp [+26]; BA.BAFlow <- flow_sz0 [+0]; BA.BAStep5IIIEMatrix <- baStep5III_EMatrix_level [+1]; BA.BAStep5IIIEScalar <- Step5IIIEdet_scalar_sz0_one [+1]
  Chain: BA.GridAssemblyHypNg <- bandStep2_GridAssemblyHypN [+1]; BA.NQGoodGen_KerNAL <- nqGoodGen_kerNAL_band_at [+1]; BA.QtBootGen_FlowModFam <- qtBootGen_flowModFam_band [+1]; BA.QtBootGen_Hyp <- qtBootGen_hyp_band [+3]; BA.QtNZGen_KerNZ <- qtNZGen_kerNZ_band_at [+5]; BA.STKwardgL <- KDecayGen_band_STKwardgL [+3]; BA.Step2IterGen_NewKLKAtN <- step2IterGen_newKLKAtN_band [+1]
  Evolution: Evol.CltMom1.Cluster <- cltMom1_cluster_inst [+1]; Evol.CltMom1.Paired <- cltMom1_b_paired [+6]
  Graph: Gauss.Sizes.Rel <- rel_self [+1]; Graph.AnpFarAndAt <- lwMomExpFar_inst_oneEdge [+9]; Graph.AnpNearInfAt <- inst_near [+10]; Graph.BAFrameStep <- hFW [+3]; Graph.BAFrameStepT <- hTW [+1]; Graph.BAGraph.LocStd <- BAEngine_pL_locStd [+3]; Graph.BALocStep <- locStepB [+6]; Graph.DEdge.sameU <- BASim_sameU_refl [+1]; Graph.LGraph.LocStd <- localReg2_inst_Q_locStd [+2]; Graph.LocStepX <- lwEngine_inst_stepX [+6]; Graph.PGraph.BAEquiv <- BASim_BAEquiv_refl [+1]; Graph.PGraph.LocStd <- localReg6a_instQ_locStd [+1]; Graph.WEdge.sameRev <- BASim_sameRev_refl [+1]; Graph.anpKey2_chain <- anpKey2_chain_new [+2]; Graph.untag <- baUntag_locStepT_intro [+1]
  Green: Green.AsGMcSeq <- asGMcSeq_time_zero [+9]; Green.GbEXPHypV3 <- inst_hyp [+1]; Green.LocalLawDetSeq <- localLawDetSeq_time_zero [+3]
  Induction: BA.Step5KerGen_ThDecay <- qDriftB_thDecay_band_concl [+1]; Gauss.Sizes.STNewKLKAt <- stNewKLKAt_holds [+1]; Gauss.Sizes.STRegIterI <- szB_regIterI [+5]; Ind.GridAssemblyHypN <- gridAsm_bundle [+2]
  Path: Path.E2Hyp <- LemDecCalE_e2Hyp_zero [+10]; Path.E2HypDif <- LemDecCalEdif_hyp_zero [+10]
  Universality: Univ.GUEPhase.Eq729B_FlowData <- Eq729B_flowData_formulas [+1]; Univ.GUEPhase.UnifDetDomAt <- eq736_detDomAt [+1]; Univ.GlSmall <- inst_glSmall_witness [+1]; Univ.UNOULL <- OUInterfaceK_UNOULL_of_k [+1]; Univ.jakGridGood <- gridGood_one [+2]
  helpers BA (20): FlowPins.BAConArg'_premise_diag, FlowPins.BAm_zSeq, FlowPins.FlowPins_BAmF_flow, FlowPins.FlowPins_BAmF_flow_im, FlowPins.FlowPins_mS_im_lower, FlowPins.FlowPins_mS_im_upper, FlowPins.FlowPins_wI_im, FlowPins.FlowPins_zS_add_mS_im, FlowPins.FlowPins_zim_pos, FlowPins.inst_premise_diag, FlowPins.mS_im_half, FlowPins.size_ge, FlowPins.size_rpow_le, FlowPins.sz0_lam_L, FlowPins.sz0_lam_pos, FlowPins.zSeq, FlowPins.zSeq_im_ge, FlowPins.zSeq_im_le, MFixedPoint.baMExists_holds, MFixedPoint.wI_norm
  helpers Chain (4): KDecayGen.KDecayGen_band_KI, QtBootGen.QtBootGen_flow_abs_le, QtNonzeroGen.qtNZGen_bandC, Step2EventsGen.Step2EventsGen_bandFlow
  helpers Evolution (2): CltMoments1.cltMom1_b, CltMoments1.cltMom1_b_dist
  helpers Graph (18): AnpKey.anpKey_oneEdge, AnpKey.anpKey_oneEdge_nested, BAEngine.BAEngine_pL, BALvl1A.hFB, BASim.Ed, BASim3.baPB, BASim3.baPW, BASim3.pB, BASim3.pW, LWLvl1.lvl1ExP2p, LWLvl1.lvl1ExStd, LWVocab.figAux, LWVocab.figAux_nested, LWVocab.instDecidableIsNestedFigAux, LWVocab.instDecidableNoGhostFigAux, LWVocab.instDecidableWalkOK, LWVocab.p2Graph, LocalRegular2.localReg2_inst_Q
  helpers Green (5): LocalLaw.localLaw_seqHflow_zero, Pins.gres_zero_true, Pins.llErrMat_time_zero, Pins.perTimeDomAt_of_nonpos, Pins.seqHflow_zero'
  helpers Induction (3): Defs.W_ge_32, GridAssemblyN.gridAsm_K, Step34Pins.szB
  helpers Path (15): LemDecCalE.lemDecCalE_STKloop_two, LemDecCalE.lemDecCalE_STKloop_zero_time, LemDecCalE.lemDecCalE_STLKM_zero_time, LemDecCalE.lemDecCalE_STLM_zero_time, LemDecCalE.lemDecCalE_blockMat_zero, LemDecCalE.lemDecCalE_gres_zero, LemDecCalE.lemDecCalE_gres_zero_true, LemDecCalE.lemDecCalE_sum_block_indicator, LemDecCalE.lemDecCalE_trace_Eblk_mul, LemDecCalEdif.lemDecCalEdif_STLM_zero_time, LemDecCalEdif.lemDecCalEdif_blockMat_zero, LemDecCalEdif.lemDecCalEdif_gres_zero, LemDecCalEdif.lemDecCalEdif_gres_zero_true, LemDecCalEdif.lemDecCalEdif_norm_trace_diag, LemDecCalEdif.lemDecCalEdif_prod_diag
  helpers Universality (1): JakKernel.im_Gres_le_inv

--- B15. every line change that is not a deletion, `file:line  old -> new` (from `git diff --minimal -U0 main...t/T2523 -- RBM3D RBM3D.lean`; each side cut at 90 characters)
$ python3 -I $SP/nondel.py main...t/T2523
RBM3D/BA/EMCTE2BA.lean:53  open private EMCTE2_hsum EMCTE2_hsum_nonneg EMCTE2_hsum_bdd EMCTE2_integrable_hsum EMCTE2_ -> open private EMCTE2_hsum EMCTE2_hsum_nonneg EMCTE2_integrable_hsum EMCTE2_integrable_L1t_t
RBM3D/BA/KCactusCut.lean:333  simp only [KCactusCut_φ, BAslotStart_out, ← hz] -> simp only [KCactusCut_φ, ← hz]
RBM3D/BA/KCactusCut.lean:340  simp only [KCactusCut_φ, BAslotStart_in, ← hz] -> simp only [KCactusCut_φ, ← hz]
RBM3D/BA/KCactusCut.lean:652  simp only [KCactusCut_ψ, BAslotStart_out, ← hz] -> simp only [KCactusCut_ψ, ← hz]
RBM3D/BA/KCactusCut.lean:662  simp only [KCactusCut_ψ, BAslotStart_in, ← hz] -> simp only [KCactusCut_ψ, ← hz]
RBM3D/BA/KTreeRep.lean:491  simp only [KTreeRep_φ, BAslotStart_out, ← hz] -> simp only [KTreeRep_φ, ← hz]
RBM3D/BA/KTreeRep.lean:498  simp only [KTreeRep_φ, BAslotStart_in, ← hz] -> simp only [KTreeRep_φ, ← hz]
RBM3D/BA/KTreeRep.lean:810  simp only [KTreeRep_ψ, BAslotStart_out, ← hz] -> simp only [KTreeRep_ψ, ← hz]
RBM3D/BA/KTreeRep.lean:820  simp only [KTreeRep_ψ, BAslotStart_in, ← hz] -> simp only [KTreeRep_ψ, ← hz]
RBM3D/BA/Step1Prime.lean:378  open private BAStep1_le_gmMax BAStep1_gmMax_le BAStep1_gmMax_nonneg BAStep1_gmMax_le_add B -> open private BAStep1_le_gmMax BAStep1_gmMax_le BAStep1_gmMax_le_add BAStep1_gmMax_continuo
RBM3D/BA/Step6BA.lean:37  open private Step6PinsBA_Aof Step6PinsBA_apply Step6PinsBA_applyD Step6PinsBA_prem Step6Pi -> open private Step6PinsBA_Aof from RBM3D.BA.Step6PinsBA
RBM3D/BA/TwistQV.lean:554  simpa [TwistQV_wd_singleton] using this -> simpa using this
RBM3D/Chain/ExpIntIQGen.lean:48  open private ExpIniIGen_envelope ExpIniIGen_Kb_band ExpIniIGen_bandData from RBM3D.Chain.E -> open private ExpIniIGen_envelope from RBM3D.Chain.ExpIniIGen
RBM3D/Chain/GridDuhamelGen.lean:32  open private GridDuhamelN_gridTime_nonneg GridDuhamelN_gridTime_lt_one GridDuhamelN_azuma_ -> open private GridDuhamelN_gridTime_nonneg GridDuhamelN_gridTime_lt_one
RBM3D/Chain/NQBudgetGen.lean:31  open private nqBudget_absorb nqBudget_gridTime_nonneg nqBudget_gridTime_le nqBudget_K_mul_ -> open private nqBudget_gridTime_nonneg nqBudget_gridTime_le
RBM3D/Chain/NewKLKGen.lean:45  nkl_SB_support nkl_theta_tail nkl_SBTheta_tail nkl_SBTheta_row nkl_conv_P nkl_ward_K nkl_m -> nkl_SB_support nkl_theta_tail nkl_SBTheta_tail nkl_SBTheta_row nkl_conv_P nkl_ward_K | fro
RBM3D/Chain/NewKLKLGen.lean:36  newKLKL_zdistInf_le_L newKLKL_mE_zero newKLKL_STGMM_zero from RBM3D.Induction.NewKLKL -> newKLKL_zdistInf_le_L from RBM3D.Induction.NewKLKL
RBM3D/Chain/QEndB1Gen.lean:58  open RBM.Ind (QProxyG_KerEK4 QProxyG_KerEK4Fam altYGridNg startLevelQNg qProxyG_kerEK4_ban -> open RBM.Ind (QProxyG_KerEK4 QProxyG_KerEK4Fam altYGridNg startLevelQNg qProxy4C qProxy4C_
RBM3D/Chain/QtXiRoundLiftGen.lean:51  open RBM.Ind (nqFlowSharp QProxyG_KerEK4Fam qProxyG_kerEK4_band) -> open RBM.Ind (nqFlowSharp QProxyG_KerEK4Fam)
RBM3D/Chain/ZeroModeGen.lean:37  open private qa_slot_zero qa_slot_succ qa_sum_filter_prod qa_sum_fiber0 from RBM3D.Inducti -> open private qa_slot_zero qa_slot_succ qa_sum_filter_prod from RBM3D.Induction.QopAlgebra
RBM3D/Evolution/CltFarG.lean:57  open private meanFarG_B meanFarG_B_bound meanFarG_chk_Th meanFarG_chk_K meanFarG_chk_m mea -> open private meanFarG_B meanFarG_B_bound
RBM3D/Graph/BAExp14bB.lean:658  BAExp14b_iT3CG, BAExp14b_outer_eq_fr, BAExp14b_outerDt_eq_fr, Fin.zero_eta, Fin.mk_one, Fi -> BAExp14b_iT3CG, BAExp14b_outer_eq_fr, Fin.zero_eta, Fin.mk_one, Fin.isValue,
RBM3D/Graph/BAExp14cB.lean:33  open private BAS3Close_pk BAS3Close_LeafC BAS3Close_CtxExD BAS3Close_LeafC_dec BAS3Close_C -> open private BAS3Close_pk BAS3Close_LeafC BAS3Close_CtxExD BAS3Close_Iso BAS3Close_iso_sym
RBM3D/Graph/BAExp14cB.lean:38  open private BAS3Close_D BAS3Close_data BAS3Close_hG BAS3Close_inst_leaf BAS3Close_rho BAS -> open private BAS3Close_D BAS3Close_data BAS3Close_hG BAS3Close_rho BAS3Close_kD from RBM3D
RBM3D/Graph/BALocReg2.lean:260  Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, i -> Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, i
RBM3D/Graph/BALocReg2B.lean:53  Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, i -> Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, i
RBM3D/Graph/BALvl1A.lean:560  open RBM.BA.CouplingWindowInst BASimInst BASymm1Inst -> open BASimInst
RBM3D/Graph/BAMomentExpGenB.lean:48  open private lwMEA_prec_mono lwMEA_phiB_sq_le lwMEA_loss lwMEA_phi_zero lwMEA_phi_sq lwMEA -> open private lwMEA_prec_mono lwMEA_phiB_sq_le lwMEA_loss lwMEA_phi_zero lwMEA_phi_sq lwMEA
RBM3D/Graph/BAS3CloseB.lean:40  open private BAS3Close_Iso BAS3Close_iso_refl BAS3Close_iso_symm BAS3Close_iso_trans BAS3C -> open private BAS3Close_Iso BAS3Close_iso_symm BAS3Close_iso_trans BAS3Close_iso_val BAS3Cl
RBM3D/Graph/BAS3CloseB.lean:43  BAS3Close_LeafC_dec BAS3Close_CtxExD_dec BAS3Close_InvC_dec BAS3Close_CandC_dec BAS3Close_ -> BAS3Close_CtxG BAS3Close_LeafT BAS3Close_MC
RBM3D/Graph/BAS3CloseC.lean:43  open private BAS3Close_LeafC BAS3Close_CtxExD BAS3Close_LeafC_dec BAS3Close_CtxExD_dec BAS -> open private BAS3Close_LeafC BAS3Close_CtxExD BAS3Close_Iso BAS3Close_iso_symm
RBM3D/Graph/BASim.lean:262  simp only [BAPGraph.splitOutsT, BAPGraph.splitOuts, List.map_append, BAPGraph.BASim_outsT_ -> simp only [BAPGraph.splitOutsT, BAPGraph.splitOuts, List.map_append, BAPGraph.BASim_outsT_
RBM3D/Graph/LocalRegular.lean:309  Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq, localReg_owx -> Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq]; try abel))
RBM3D/Green/IBP.lean:323  simp only [Function.comp_def, entryCLM_apply] at h2 -> simp only [Function.comp_def] at h2
RBM3D/Induction/EtermsMid2.lean:31  open private lemDecCalELipG_absorb lemDecCalELip_inst_tN from RBM3D.Induction.LemDecCalELi -> open private lemDecCalELipG_absorb from RBM3D.Induction.LemDecCalELip
RBM3D/Induction/GridAssemblyN.lean:1600  open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst |  | /-- The  -> open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
RBM3D/Induction/GridDuhamelN.lean:6  import RBM3D.Path.Expansion -> import RBM3D.Induction.Step2Defs
RBM3D/Induction/HierAlgebra.lean:7  import RBM3D.Path.DriftAlgebra -> import RBM3D.Induction.Step2Defs
RBM3D/Loop/KBound.lean:6  import RBM3D.Loop.TreeThree -> import RBM3D.Loop.Unique
RBM3D/Loop/KLUnique.lean:7  import RBM3D.Loop.TreeThree -> import RBM3D.Loop.Unique
RBM3D/Propagator/Pins.lean:6  import RBM3D.Propagator.Interface -> import RBM3D.Propagator.Basic
RBM3D/Test/Axioms.lean:352   -> `RBM.Univ.UNOULLk, -- (T2282, UN-51g: owed; owner band: UN-51 (`g1Rowk_band`); BA: C5g (`g
RBM3D/Test/Axioms.lean:371  `RBM.Univ.UNCoreC,       -- false: argued, supervisor 2026-10-05-1651 1.3 (not compiled);  -> `RBM.Univ.UNTrLocalInit] -- false for the band model at every admissible sequence: argued,
RBM3D/Test/Axioms.lean:382  [`RBM.Gauss.Sizes.STStep3,    -- Step 3, any regime: S3-27 cancelled (DECISIONS §68 (9));  -> [`RBM.Gauss.Sizes.STStep6,    -- Step 6, general `0 ≤ s < t ≤ t₀`: S6-13 cancelled (DECISI
RBM3D/Test/Axioms.lean:385  `RBM.Gauss.Sizes.STLWT, -- `lem: EWGn2_N` (`3_5:406-415`): superseded (T2377, supervisor 0 -> `RBM.Gauss.Sizes.STLWT] -- `lem: EWGn2_N` (`3_5:406-415`): superseded (T2377, supervisor 0
RBM3D/Universality/FreeConv.lean:108  field_simp [freeConv_card_ne_zero] -> field_simp
RBM3D/Universality/FreeConv.lean:135  field_simp [freeConv_card_ne_zero] -> field_simp
RBM3D/Universality/FreeConv.lean:196  rw [freeConv_stieltjesVec_im]; field_simp [freeConv_card_ne_zero] -> rw [freeConv_stieltjesVec_im]; field_simp
RBM3D/Universality/FreeConv.lean:209  rw [freeConv_stieltjesVec_im]; field_simp [freeConv_card_ne_zero] -> rw [freeConv_stieltjesVec_im]; field_simp
RBM3D/Universality/FreeConv.lean:395  field_simp [freeConv_card_ne_zero] -> field_simp
50 hunks with added lines; 51 added lines in total

--- B16. finding: the unit rule of the tool compares line ranges across modules; a module-aware variant (2 changed lines) on the branch (the unreached lines are printed as 1000000 x module index + line: lines 57-65 and 134-138)
$ diff docs/claude-team/tools/DeadDecls.lean $SP/scan/DeadModFix.lean
410c410
<   for (c, _) in modOf.toList do
---
>   for (c, mi) in modOf.toList do
412c412
<       ranges := ranges.insert c (r.range.pos.line, r.range.endPos.line)
---
>       ranges := ranges.insert c (mi * 1000000 + r.range.pos.line, mi * 1000000 + r.range.endPos.line)
$ lake env lean $SP/scan/DeadModFix.lean   # on the branch; sections (e) and "unreached declarations"
- declarations (non-meta units): 22765; meta declarations: 69 (unreached meta: 60)
- unreached (non-meta): 2
### unreached declarations
### RBM3D.BA.Step1Boot  (1 unreached of 33)
RBM.BA.FlowFM.gexRHS  6409000057-6409000065
### RBM3D.Induction.Step6Pins  (1 unreached of 43)
RBM.Gauss.Sizes.STStep6  6357000134-6357000138
```

## (c) Verified Mathlib names used

None. The branch adds no Lean code under `RBM3D/` (B10: no added declaration line in the minimal diff); the added library lines are imports, `open` and simp-list edits and registry entries (B15). The tool (`docs/claude-team/tools/DeadDecls.lean`) uses only Lean-core names that its earlier version already used (`Name`, `Environment`, `Std.HashSet`, `findDeclarationRanges?`).

## (d) Open issues and paper-delta candidates

1. **Decision for the dispatcher: the premise scan.** The 110 declarations of R2 (B14; 42 theorems, 68 helpers, 1094 lines) are kept only because `#assert_rbm_axioms` needs, for each of 42 `Prop`s that surviving theorems assume, a proving theorem or a registry entry. The alternative is to classify the 42 `Prop`s in `RBM3D/Test/Axioms.lean` (borrowed, owed, structural, refuted or superseded) and delete the 110 declarations. I did not classify: the ticket names no class, and the classes are the dispatcher's decision (DECISIONS). The list R2 gives each `Prop` with the theorem kept for it. A follow-up costs one full build (this branch: 02:08:56-03:20:59 UTC).
2. **Finding on the T2522 tool (not fixed here).** `inductUnit?` in `docs/claude-team/tools/DeadDecls.lean` compares the line range of a constant with that of its name prefix without comparing the modules. On this branch the tool counts 22738 declarations; a module-aware rule (B16, two changed lines) counts 22765 and reports 2 unreached: `RBM.BA.FlowFM.gexRHS` (`BA/Step1Boot.lean:57-65`) and `RBM.Gauss.Sizes.STStep6` (`Induction/Step6Pins.lean:134-138`, also in `supersededProps`). Both lie outside the T2522 (b) list, which is this ticket's deletion set, so they are not deleted and the ticket's acceptance line (0 unreached by the tool) is as stated in B13. Proposed: the two-line tool fix, deletion of the two declarations and of the `STStep6` registry entry, in a ticket with a full build.
3. 60 meta declarations stay listed as unreached meta (B13 (e)): `macroRules`, `unexpand`, notations and tactic macros (for example `tacticBf_elim`). The tool keeps meta code by design; a tactic macro leaves no trace in a proof term.
4. Not reworded, as the ticket says: comments and docstrings that mention deleted declarations. Four references to the deleted `RBM3D/Test/InterfaceShape.lean` remain: `Test/AuditNegative.lean:16`, `Test/Axioms.lean:398`, `Test/Axioms.lean:597` (inside the message text that `#assert_rbm_axioms` prints), `Propagator/Props4.lean:238` (`grep -rn InterfaceShape RBM3D RBM3D.lean`).
5. R1 (85 `rfl`-proved or `@[simp]` lemmas, defs and theorems) was taken over from the first stage-1b run (the hub's task text: lemmas the closure did not predict; its logs `build1.log`-`build6.log` in the scratch directory have 55, 48, 28, 13, 3 and 11 lines starting with `error`). I did not re-derive the need for each name; the build passes with them, and the tool lists them as roots (`restoredRoots`).
6. Insertion count: the ticket's limit of 300 holds for `RBM3D/` (291 by git's default algorithm, 51 with `--minimal`). With the tool file the default total is 489 (minimal 249); of the tool's 198 added lines (hunks in B10) 142 are the root lists `restoredRoots` (85 names) and `scanProvers` (42) with their doc comments, 16 the helper `survives`, 31 the root loops and the report code for the groups and the two lists, 9 header and one-line edits.
7. Paper-delta candidates: none. No statement of the library changed (B7), and no hypothesis, signature or target was touched.

## Deletion script (ticket: paste it in the report); not counted in the 120 lines

Call (from the worktree root, `$SP/dead2.txt` = output of the tool of commit 8395d2d6 on a copy of main's library, `$SP/pristine` = copy of main's `RBM3D/` and `RBM3D.lean`, `keep_none.txt` empty, `fix.json` = the five imports below):

```text
$ cat $SP/fix.json
{"RBM3D/Loop/KBound.lean": ["RBM3D.Loop.Unique"], "RBM3D/Propagator/Pins.lean": ["RBM3D.Propagator.Basic"], "RBM3D/Loop/KLUnique.lean": ["RBM3D.Loop.Unique"], "RBM3D/Induction/HierAlgebra.lean": ["RBM3D.Induction.Step2Defs"], "RBM3D/Induction/GridDuhamelN.lean": ["RBM3D.Induction.Step2Defs"]}
$ python3 -I $SP/delete_dead.py $SP/dead2.txt $SP/pristine $SP/keep_none.txt $SP/fix.json     # dry run in a scratch copy of main's RBM3D/
{'dead_units': 9372, 'clutter_units': 4669, 'lines_pass1': 133023, 'lines_pass2': 5675, 'files_written': 632}
$ sha256sum $SP/delete_dead.py
a5dbe962de4490f22673d9d4ea11833065c9551a68a0913c44afedcb0cbc2276  $SP/delete_dead.py
```

```python
#!/usr/bin/env python3
# T2523 deletion script.  From the worktree root:  python3 -I delete_dead.py REPORT PRISTINE KEEP FIX
#   REPORT   output of `lake env lean docs/claude-team/tools/DeadDecls.lean` (sections (b), (c), (g))
#   PRISTINE a clean copy of RBM3D/ and RBM3D.lean at main (git archive); every run rewrites the worktree from it
#   KEEP     names (as in REPORT) of unreached declarations that must stay (restored after a build failure), one per line
#   FIX      JSON {file: [modules]}: direct imports added where an import of a whole-dead module was removed
# (1) delete every unreached declaration of (b) (with doc comment, attributes, `set_option/omit/include/open ... in`
# prefix); (2) delete every example/#print/#check/#eval/#guard_msgs outside the four exempt files; (3) delete the
# namespaces/sections left empty and the `variable` lines left unused by (1)-(2); (4) drop the imports of the
# whole-dead modules of (c) (+ FIX) in every file and RBM3D.lean; (5) edit the registry lists of Test/Axioms.lean;
# (6) remove the deleted lemmas from the `simp`-like lists, the vanished namespaces / deleted private names from `open`.
import re, sys, glob, json, collections, os
EXEMPT = {'RBM3D/Main/FinalShape.lean', 'RBM3D/Main/BandTerminal.lean', 'RBM3D/BA/MAPins.lean', 'RBM3D/Main/BUnivHolds.lean'}
CLUTTER = {'example', '#print', '#check', '#eval', '#guard_msgs', '#reduce', '#synth'}
MODS = {'private', 'protected', 'noncomputable', 'unsafe', 'partial', 'nonrec'}
NOCODE = {'open', 'universe', 'set_option', 'variable', 'include', 'omit', 'end', 'namespace', 'section', 'mutual'}
SCOPE = ('namespace', 'section', 'mutual')
LOCALNOT = lambda x: x['head'] == 'local' and bool(re.match(r'local\s+(notation|macro|syntax|infix[lr]?|prefix|postfix)\b', x['code']))
W = r"(?<![\w'])%s(?![\w'])"
BIND = r'[({⦃\[]\s*([^:\]})⟩]+?)\s*:'

def lex(lines):
    """(state at line start: k code / c comment / s string, comment-blanked lines); block comments nest."""
    st, masked, depth, instr = [], [], 0, False
    for ln in lines:
        st.append('c' if depth else ('s' if instr else 'k')); out, i, n = [], 0, len(ln)
        while i < n:
            c, two = ln[i], ln[i:i + 2]
            if depth:
                depth += (two == '/-') - (two == '-/'); k = 2 if two in ('/-', '-/') else 1; out.append(' ' * k); i += k
            elif instr:
                k = 2 if c == '\\' else 1; instr = c != '"'; out.append(ln[i:i + k]); i += k
            elif two == '--': out.append(' ' * (n - i)); break
            elif two == '/-': depth = 1; out.append('  '); i += 2
            elif c == '"': instr = True; out.append(c); i += 1
            else:
                m = re.match(r"'(\\.|[^\\'])'", ln[i:]) if c == "'" and not (i and (ln[i - 1].isalnum() or ln[i - 1] in "_!?'")) else None
                k = len(m.group(0)) if m else 1; out.append(ln[i:i + k]); i += k
        masked.append(''.join(out))
    return st, masked

def units(lines):
    """Units = prefix items (doc-only, attribute-only, `... in`) + one core item; items start at a column-0 line."""
    st, masked = lex(lines)
    cont = ('|', ')', ']', '}', '⟩', ':=', '<;>', '·', '..')
    starts = [i for i, l in enumerate(lines) if st[i] == 'k' and l and l[0] not in ' \t' and not l.startswith(cont)
              and re.split(r'[\s(:\[{]', l, 1)[0] not in ('termination_by', 'decreasing_by', 'where')]
    res, pend = [], []
    for k, s in enumerate(starts):
        e = starts[k + 1] - 1 if k + 1 < len(starts) else len(lines) - 1
        code = ' '.join(masked[s:e + 1]).strip()
        if (lines[s].startswith('/--') and code == '') or re.fullmatch(r'(@\[[^\]]*\]\s*)+', code) or re.search(r'\bin$', code):
            pend.append((s, e)); continue
        w = [x for x in re.sub(r'@\[[^\]]*\]', ' ', code).split() if x not in MODS]
        res.append(dict(a=pend[0][0] if pend else s, s=s, e=e, st={p[0] for p in pend} | {s}, head=w[0] if w else '', code=code, pre=pend)); pend = []
    return res

def analyse(us):
    """Empty scopes (open, close) and unused variable units, as unit indices."""
    empty, stack, ends, st2, unused, live = [], [], {}, [], [], set()
    for k, u in enumerate(us):
        if u['head'] in SCOPE: stack.append(k); st2.append([])
        elif u['head'] == 'end' and stack:
            o = stack.pop()
            if all(x['head'] in NOCODE - {'end'} - set(SCOPE) or x['code'] == '' or LOCALNOT(x) for x in us[o + 1:k]): empty.append((o, k))
            for j in st2.pop(): ends[j] = k
        elif u['head'] == 'variable':
            if st2: st2[-1].append(k)
            else: ends[k] = len(us)
    for blk in st2:
        for j in blk: ends[j] = len(us)
    vn = {t for u in us if u['head'] == 'variable' for g in re.findall(BIND, u['code']) for t in g.split()}
    for j in sorted(ends, reverse=True):            # a variable is used if a later declaration (or live variable) mentions it
        x = us[j]; named = {t for g in re.findall(BIND, x['code']) for t in g.split()}
        mention = named or (set(re.findall(r"[\w']+", x['code'])) & vn)
        body = ' '.join(us[i]['code'] for i in range(j + 1, ends[j]) if us[i]['head'] not in NOCODE - {'include', 'omit'} or i in live)
        if any(re.search(W % re.escape(t), body) for t in mention) or (not mention and body.strip()): live.add(j)
        else: unused.append(j)
    return empty, unused

def edit(lines, rngs, clutter_ok):
    """Delete the unit ranges `rngs` (1-based report ranges) and the clutter units; return (lines, stat)."""
    n0 = len(lines); orig = list(range(n0)); us0 = units(lines); kill = []
    for (s, e) in rngs:
        ks = [u for u in us0 if u['a'] <= s - 1 <= u['e']]; ke = [u for u in us0 if u['a'] <= e - 1 <= u['e']]
        assert ks and ke and s - 1 in ks[0]['st'], (s, e)
        kill.append((ks[0]['a'], ke[0]['e']))
    nd = len(kill)
    kill += [(u['a'], u['e']) for u in us0 if u['head'] in CLUTTER and clutter_ok(u['head'])]
    merged = []
    for (x, y) in sorted(kill):
        if merged and x <= merged[-1][1] + 1: merged[-1][1] = max(merged[-1][1], y)
        else: merged.append([x, y])
    for x, y in reversed(merged): del lines[x:y + 1]; del orig[x:y + 1]
    n1 = len(lines); e0, u0 = analyse(us0); b_e = {us0[o]['s'] for o, k in e0}; b_u = {us0[j]['s'] for j in u0}
    while kill:                                     # scopes left empty, variables left unused (not already so before)
        us = units(lines); e1, u1 = analyse(us); kl = set()
        for o, k in e1:
            if orig[us[o]['s']] not in b_e:
                kl |= {(us[i]['a'], us[i]['e']) for i in [o, k] + [i for i in range(o + 1, k) if us[i]['head'] in NOCODE or LOCALNOT(us[i])]}
        kl |= {(us[j]['a'], us[j]['e']) for j in u1 if orig[us[j]['s']] not in b_u}
        if not kl: break
        for x, y in sorted(kl, reverse=True): del lines[x:y + 1]; del orig[x:y + 1]
    return lines, (nd, len(kill) - nd, n0 - n1, n1 - len(lines))

def contexts(lines, us):
    """Per unit: (active namespace prefixes, opened namespaces)."""
    ctx, ns, opens = [], [[]], [[]]
    for u in us:
        h = u['head']
        if h == 'namespace': ns.append(ns[-1] + u['code'].split()[1].split('.')); opens.append(list(opens[-1]))
        elif h in ('section', 'mutual'): ns.append(ns[-1]); opens.append(list(opens[-1]))
        elif h == 'end' and len(ns) > 1: ns.pop(); opens.pop()
        elif h == 'open': opens[-1] += [x for x in u['code'].split()[1:] if re.fullmatch(r"[\w.'«»]+", x) and x != 'scoped']
        ctx.append((ns[-1], opens[-1]))
    return ctx

def resolved(e, nsp, op, names):
    """The members of `names` that the identifier `e`, written in namespace `nsp` with namespaces `op` open, may denote."""
    pre = ['.'.join(nsp[:i]) for i in range(len(nsp) + 1)]
    return ({e} | {(p + '.' + e) if p else e for p in pre} | {o + '.' + e for o in op} | {p + '.' + o + '.' + e for o in op for p in pre if p}) & names

def resolves(e, nsp, op, names): return bool(resolved(e, nsp, op, names))

def unlist(text, names, hits=None):
    """Remove from every `simp`-like `[ ... ]` list of `text` the elements that resolve, in the namespaces and `open`s
    active there, to one of the full names `names` (deleted lemmas); elements such as local hypotheses stay."""
    if not names: return text
    lines = text.split('\n'); us = units(lines); m = '\n'.join(lex(lines)[1]); ctx = contexts(lines, us)
    loff = [0]
    for l in lines: loff.append(loff[-1] + len(l) + 1)
    import bisect
    ustart = [u['s'] for u in us]
    def hit(e, off):
        k = bisect.bisect_right(ustart, bisect.bisect_right(loff, off) - 1) - 1
        r = resolved(e, ctx[k][0], ctx[k][1], names) if e and k >= 0 and ('_' in e or '.' in e or len(e) >= 6) else set()  # short names are locals
        if hits is not None: hits.update(r)
        return bool(r)
    KW = re.compile(r"(simp only|simp_all only|simpa only|dsimp only|simp_all|simpa|simp|dsimp|simp_rw|norm_num|field_simp|push_cast)\b[^\[\]]*$")
    edits = []
    for lb in [i for i, c in enumerate(m) if c == '[']:
        if not KW.search(m[max(0, lb - 80):lb]): continue
        depth, start, els, j = 0, lb + 1, [], lb
        while j < len(m):
            c = m[j]
            if c in '[({⟨': depth += 1
            elif c in '])}⟩':
                depth -= 1
                if depth == 0: els.append((start, j)); break
            elif c == ',' and depth == 1: els.append((start, j)); start = j + 1
            j += 1
        else: continue
        cs = [(a + len(m[a:b]) - len(m[a:b].lstrip()), a + len(m[a:b].rstrip())) for a, b in els]     # content ranges
        drop = [hit(m[a:b].lstrip('←↓↑ '), a) for a, b in cs]
        if not any(drop): continue
        kept = [k for k in range(len(cs)) if not drop[k]]
        if not kept:
            k0 = lb
            while text[k0 - 1] == ' ': k0 -= 1
            edits.append((k0, j + 1, '')); continue
        new = text[lb + 1:cs[kept[0]][0]]
        for t, k in enumerate(kept):
            new += text[cs[k][0]:cs[k][1]]
            if t + 1 < len(kept): new += text[cs[k][1]:cs[k + 1][0]]
        new += text[cs[-1][1]:j]
        edits.append((lb + 1, j, new))
    for a, b, new in sorted(edits, reverse=True): text = text[:a] + new + text[b:]
    return text

def fix_opens(text, lost_ns, gone_private, gone_names=frozenset()):
    """Drop from `open N ...`, `open N ... in` the namespaces `N` that no longer exist, and from `open private x y from M [in]`
    the private declarations of `M` that were deleted (matched by their last components); an `open` left without argument
    is deleted.  `gone_private` maps a module name to the full names of its deleted private declarations."""
    lines = text.split('\n'); us = units(lines); ctx = contexts(lines, us); edits = []
    allpriv = set().union(*gone_private.values(), set())
    for k, u in enumerate(us):
        for (s, e) in u['pre'] + [(u['s'], u['e'])]:
            code = ' '.join(lex(lines[s:e + 1])[1]).strip()
            m2 = re.fullmatch(r'open\s+(\S+)\s*\(([^()]*)\)(\s+in)?', code)         # open N (a b c): drop the deleted a, b, c
            if m2:
                toks = m2.group(2).split(); gone = [t for t in toks if m2.group(1) + '.' + t in gone_names or resolves(m2.group(1) + '.' + t, ctx[k][0], ctx[k][1], gone_names)]
                if gone:
                    seg = '\n'.join(lines[s:e + 1])
                    for t in gone: seg = re.sub(r"(?<![\w.'])" + re.escape(t) + r"(?![\w.'])[ \t]*", '', seg, count=1)
                    seg = re.sub(r'\(\s*', '(', seg); seg = re.sub(r'\s+\)', ')', seg)
                    edits.append((s, e, [] if len(gone) == len(toks) else [x.rstrip() for x in seg.rstrip().split('\n')] + [''] * (len(seg) - len(seg.rstrip('\n')))))
                continue
            m = re.fullmatch(r'open(\s+private|\s+scoped)?\s+([^()]*?)(\s+in)?', code)
            if not m or 'hiding' in code or 'renaming' in code: continue
            priv = bool(m.group(1) and 'private' in m.group(1)); parts = m.group(2).split(' from '); toks = parts[0].split()
            if priv:
                pool = gone_private.get(parts[1].strip(), set()) if len(parts) > 1 else allpriv
                gone = [t for t in toks if any(d == t or d.endswith('.' + t) for d in pool)]
            else: gone = [t for t in toks if resolves(t, ctx[k][0], ctx[k][1], lost_ns)]
            if not gone: continue
            seg = '\n'.join(lines[s:e + 1])
            for t in gone: seg = re.sub(r"(?<![\w.'])" + re.escape(t) + r"(?![\w.'])[ \t]*", '', seg, count=1)
            edits.append((s, e, [] if len(gone) == len(toks) else [x.rstrip() for x in seg.rstrip().split('\n')] + [''] * (len(seg) - len(seg.rstrip('\n')))))
    for s, e, new in sorted(edits, reverse=True): lines[s:e + 1] = new
    return '\n'.join(lines)

def registry(L, gone):
    """Remove `gone` from the registry lists of Axioms.lean; move UNOULLk from owedProps to structuralProps."""
    ent = re.compile(r"^(\s*)(\[?)`([^\s,\]`]+)([,\]])(.*)$")
    out, i, moved = [], 0, None
    while i < len(L):
        m = re.match(r"^def (borrowedProps|owedProps|structuralProps|refutedProps|supersededProps) : List Name :=$", L[i])
        out.append(L[i]); i += 1
        if not m: continue
        j = i
        while not (ent.match(L[j]) and ent.match(L[j]).group(4) == ']'): j += 1
        kept = []
        for l in L[i:j + 1]:
            e = ent.match(l)
            if e and e.group(3) == 'RBM.Univ.UNOULLk' and m.group(1) == 'owedProps': moved = l
            elif not (e and e.group(3) in gone): kept.append(l)
        ix = lambda: [k for k, l in enumerate(kept) if ent.match(l)]
        if m.group(1) == 'structuralProps' and moved:
            kept.insert(next(k for k in ix() if ent.match(kept[k]).group(3) == 'RBM.Univ.UNOUProfRowk') + 1, '   ' + moved.lstrip())
        a, z = ix()[0], ix()[-1]                    # `[` on the first remaining entry, `]` on the last
        for k in ix():
            e = ent.match(kept[k]); kept[k] = e.group(1) + '`' + e.group(3) + (']' if k == z else ',') + e.group(5)
        kept[a] = '  [' + kept[a].lstrip()
        out += kept; i = j + 1
    return out

def main(rep, pr, keepf, fixf):
    txt = open(rep).read().split('\n'); keep = set(open(keepf).read().split('\n')) - {''}; fix = json.load(open(fixf))
    a = txt.index('### unreached declarations'); c = next(i for i, l in enumerate(txt) if l.startswith('## (c)'))
    d = next(i for i, l in enumerate(txt) if l.startswith('## (d)')); g = next(i for i, l in enumerate(txt) if l.startswith('## (g)'))
    ranges, mod, priv = collections.defaultdict(list), None, collections.defaultdict(set)
    for l in txt[a + 1:c]:
        m = re.match(r'### (\S+)\s+\(', l)
        if m: mod = m.group(1)
        elif l.strip() and re.sub(r'^private ', '', re.sub(r'  \d+-\d+$', '', l)) not in keep:
            r = re.search(r'  (\d+)-(\d+)$', l); ranges[mod].append((int(r.group(1)), int(r.group(2)), re.sub(r'^private ', '', l[:r.start()])))
            if l.startswith('private '): priv[mod].add(ranges[mod][-1][2])
    dead = {re.match(r'- (\S+)', l).group(1) for l in txt[c + 1:d] if l.startswith('- RBM3D.')}
    h = next(i for i, l in enumerate(txt) if l.startswith('## (h)'))
    prefixes = lambda n: {'.'.join(n.split('.')[:i]) for i in range(1, len(n.split('.')))}
    lost_ns = {l[2:] for l in txt[h + 1:] if l.startswith('- RBM')} - set().union(*[prefixes(n) for n in keep], set())
    gone = ({m.group(1) for l in txt[g:] if (m := re.match(r"  (RBM\S+)  line \d+$", l))} - keep) | {'RBM.Univ.UNG1Rowk'}
    alldel = {n for r in ranges.values() for _, _, n in r}

    stat = collections.Counter()
    for f in sorted(glob.glob(pr + '/RBM3D/**/*.lean', recursive=True)) + [pr + '/RBM3D.lean']:
        rel = os.path.relpath(f, pr); mname = rel[:-5].replace('/', '.')
        if mname in dead: continue
        lines = open(f).read().split('\n')
        if rel != 'RBM3D.lean':
            lines, s = edit(lines, [(a, b) for a, b, _ in ranges.get(mname, [])], lambda h, rel=rel: not (h == 'example' and rel in EXEMPT))
            for k, v in zip(('dead_units', 'clutter_units', 'lines_pass1', 'lines_pass2'), s): stat[k] += v
        if rel != 'RBM3D.lean': lines = fix_opens(unlist('\n'.join(lines), alldel), lost_ns, priv, alldel).split('\n')
        if lines[-1] != '': lines.append('')        # keep the final newline
        new = []
        for l in lines:                             # imports of whole-dead modules: dropped, or replaced by FIX
            m = re.fullmatch(r'import (\S+)', l)
            if m and m.group(1) in dead: new += ['import ' + x for x in fix.get(rel, []) if 'import ' + x not in lines and x not in dead]
            else: new.append(l)
        if rel.endswith('Test/Axioms.lean'): new = registry(new, gone)
        if not os.path.exists(rel) or open(rel).read() != '\n'.join(new):
            open(rel, 'w').write('\n'.join(new)); stat['files_written'] += 1
    print(dict(stat))

main(*sys.argv[1:5])
```


## Repair (audit round 1 D1) — Sat Oct 17 06:20:43 UTC 2026

Repairer model: claude-opus-5-5. Scope: Amend 1 "D1" items 1-3 only. `$S` = scratch `T2523/repair1/`, `$SP` = scratch `T2523/`. Repair commit `89856dac` on 8395d2d6, branch `t/T2523`.
The figures here replace those of (b) narrative 6, B13, B14 (R1) and (d) 5-6 (85 restored names, 22738 declarations, 35045 reached constants, 489/249 insertions).

1. Item 1. Deleted with their scopes: `Green/MinorDiff.lean:931-963` (namespace `MinorDiffInst`, its `noncomputable section`, the four declarations, the four heading comments inside) and `Graph/BALocReg1B.lean:317-341` (section `RelabelOps`, its `variable` line, `BALocReg1B_extMap`; the enclosing section `Inst` then held only `open RBM.Gauss` and a heading comment, so it went too, ticket item 5). The five names are removed from `restoredRoots` (80 remain). Deletions only (R-A).
2. Item 2. The three zero-reference `@[simp]` lemmas each break a proof of their own module when deleted (R-B); they stay. Each of the other 77 names has a use site in a surviving proof or in a tactic macro that surviving proofs call (R-C).
3. Item 3. Full build, tool rerun, check file, axioms: R-D. `Green/MinorDiff.lean:914` (a comment) still names `MinorDiffInst.szM`; comments are the next ticket.

```text
--- R-A. the repair commit (deletions only); the branch diff; non-deletion line changes (B15) and empty scopes (B8) rechecked
$ git diff --numstat 8395d2d6 t/T2523; git diff --shortstat main...t/T2523; git diff --shortstat main...t/T2523 -- RBM3D RBM3D.lean; git diff --minimal --shortstat main...t/T2523; git diff --minimal --shortstat main...t/T2523 -- RBM3D RBM3D.lean
0	25	RBM3D/Graph/BALocReg1B.lean
0	33	RBM3D/Green/MinorDiff.lean
0	5	docs/claude-team/tools/DeadDecls.lean
 650 files changed, 484 insertions(+), 149231 deletions(-)
 649 files changed, 291 insertions(+), 149220 deletions(-)
 650 files changed, 244 insertions(+), 148991 deletions(-)
 649 files changed, 51 insertions(+), 148980 deletions(-)
$ python3 -I $SP/nondel.py main...t/T2523 > $S/nondel.out; tail -1 $S/nondel.out; diff $S/nondel_prev.txt $S/nondel.out && echo "B15 list identical"   # nondel_prev.txt = the B15 lines of this report
50 hunks with added lines; 51 added lines in total
B15 list identical
$ python3 -I $SP/rep/emptyscopes.py | grep -o "'RBM3D/[^']*'" | sort | uniq -c        # 3992 blocks in B8, the same 5
3989 namespace/section/mutual blocks scanned; 5 
   5 'RBM3D/Induction/Step2Iterate.lean'
$ grep -rnwE "toyHalf|toyPow|BALocReg1B_extMap|sqrt_four|mE_zero|RelabelOps" RBM3D RBM3D.lean docs/claude-team/tools/DeadDecls.lean | wc -l
       0

--- R-B. the three zero-reference @[simp] lemmas: deleted in a scratch copy of their module, compiled against the branch build of 8395d2d6 (05:05:38-05:06:05 UTC)
$ awk 'NR!=190' RBM3D/BA/GreenMinor3.lean > $S/GreenMinor3_del.lean; lake env lean $S/GreenMinor3_del.lean      # exit 1, 1 error
$S/GreenMinor3_del.lean:442:8: error: Type mismatch: After simplification, term
  h
 has type
  @LE.le ℝ Real.instLE ‖GreenMinor_iFam Gs a T S‖ (2 / κ)
but is expected to have type
  @LE.le ℝ Real.instLE ‖GreenMinor_iFam Gs a T S‖ (GreenMinor_a κ 0)
  -> branch BA/GreenMinor3.lean:443 `simpa using h`, in GreenMinor_diffBd_atom (case zero): GreenMinor_a_zero is needed
$ awk 'NR<89||NR>92' RBM3D/Gauss/LoopFlowStein.lean > $S/LoopFlowStein_del.lean; lake env lean $S/LoopFlowStein_del.lean   # exit 1, 1 error; lines 1-2 and 8 of its output:
$S/LoopFlowStein_del.lean:194:8: error: unsolved goals
case nil
⊢ 0 = ((√u)⁻¹ * 2⁻¹) • (wordDirectionMap d L W u ω (zt E u) []) (blockMat d L W (Xmat d L W ω))
  -> branch Gauss/LoopFlowStein.lean:198 `simp [loopWordDeriv, spectralWordDeriv]`, in loopWordDeriv_split (case nil): wordDirectionMap_nil is needed
$ awk 'NR<141||NR>142' RBM3D/Green/MinorDiffCond.lean > $S/MinorDiffCond_del.lean; lake env lean $S/MinorDiffCond_del.lean  # exit 1, 1 error; lines 1-2 and 9 of its output:
$S/MinorDiffCond_del.lean:235:9: error: unsolved goals
case zero
⊢ sz.seqP (badTower sz n ε S 0) ≤ sz.seqP S
  -> branch Green/MinorDiffCond.lean:237 `simp`, in meas_badTower_le (case zero): badTower_zero is needed

--- R-C. per-name reason for the 80 restoredRoots names: declaration site, number of uses (identifier tokens, comments, strings and
    `open private` lines excluded; a private name only in its file), first use: enclosing declaration [tactic]; uses inside a local tactic
    macro give the macro and its first call; the first use shown lies outside the restoredRoots declarations (no name is used only inside them). `*` = private.
$ python3 -I $S/uses.py > $S/uses3.txt; python3 -I $S/table.py $S/uses3.txt | sed -E (append "-> R-B: <site>" to the three "uses 0" lines)   # sha256 uses.py 4140a7c4..., table.py f9548d5a...
BA.GUETwistBA_Pi_apply  BA/GUETwistBA.lean:66  uses 6: BA/GUETwistBA.lean:77 in GUETwistBA_Pi_conjTranspose [simp only]
BA.GreenMinor_a_zero  BA/GreenMinor3.lean:190  uses 0: -  -> R-B: GreenMinor3.lean:443
BA.BAMcharge_def  BA/KCactus.lean:352  uses 5: BA/KCactus.lean:479 in BAMcharge_empty [simp only]
BA.BAslotStart_leaf  BA/KCactus.lean:98  uses 5: BA/KCactus.lean:456 in BAnextSlot_empty [simp only]
BA.TwistAvgA2_G_eq  BA/TwistAvgA2.lean:162  uses 2: BA/TwistAvgA2.lean:283 in TwistAvgA2_L4a_norm [simp only]
BA.TwistGridWTail_cm_apply*  BA/TwistGridWTail.lean:865  uses 4: BA/TwistGridWTail.lean:875 in TwistGridWTail_cm_lt [simp only]
BA.TwistStep2_eta_eq  BA/TwistStep2.lean:631  uses 2: BA/TwistStep2.lean:675 in TwistStep2_pin [simp only]
BA.BAMss_pp_apply  BA/Ward.lean:260  uses 2: Graph/BAS3CloseC.lean:110 in BAS3Close_om_eq [simp only]
BA.StepDecompGen_wd_nil*  Chain/StepDecompGen.lean:177  uses 6: Chain/StepDecompGen.lean:189 in StepDecompGen_wd_append [simp]
Gauss.fineModel_Hflow_apply*  Gauss/FineModel.lean:434  uses 2: Gauss/FineModel.lean:464 in measurable_Hflow [simp only]
Gauss.fineModel_Xmat_apply*  Gauss/FineModel.lean:265  uses 2: Gauss/FineModel.lean:355 in Xmat_add [simp only]
Gauss.wordDirectionMap_cons  Gauss/LoopFlowStein.lean:95  uses 2: Gauss/LoopFlowStein.lean:123 in wordDirectionMap_coordinate [simp only]
Gauss.wordDirectionMap_nil  Gauss/LoopFlowStein.lean:90  uses 0: -  -> R-B: LoopFlowStein.lean:198
Graph.anpKey5_inS_inl  Graph/AnpKey5.lean:215  uses 8: Graph/AnpKey5.lean:223 in anpKey5_inS_mono [simp]
Graph.BAEngine_col_transpose*  Graph/BAEngine.lean:60  uses 1: Graph/BAEngine.lean:67 in BAEngine_twist_nWS [simp]
BA.BAExp14c_D_G*  Graph/BAExp14c.lean:178  uses 4: Graph/BAExp14c.lean:199 in BAExp14c_ptT0 [simp only]
BA.BAExp14c_D_S'*  Graph/BAExp14c.lean:181  uses 4: Graph/BAExp14c.lean:199 in BAExp14c_ptT0 [simp only]
BA.BAExp14c_blk*  Graph/BAExp14c.lean:184  uses 4: Graph/BAExp14c.lean:224 in BAExp14c_ptT0 [simp only]
Graph.BAGGOp_rho2_b*  Graph/BAGGOp.lean:1136  uses 6: Graph/BAGGOp.lean:1288 in BAGGOp_A2_atoms [simp only]
Graph.BAGGOp_rho2_u*  Graph/BAGGOp.lean:1134  uses 6: Graph/BAGGOp.lean:1288 in BAGGOp_A2_atoms [simp only]
Graph.BALocReg1_molMap_mk  Graph/BALocReg1B.lean:168  uses 1: Graph/BALocReg1B.lean:198 in BALocReg1_shadow_edge [simp]
Graph.BALocReg2_bpS_dst  Graph/BALocReg2.lean:189  uses 2: Graph/BALocReg2.lean:260 in BALocReg2_simp0 [simp only] (macro BALocReg2_simp0, invoked 39x; first call Graph/BALocReg2.lean:283 in BALocReg2_lw2Head)
Graph.BALocReg2_bpS_src  Graph/BALocReg2.lean:187  uses 2: Graph/BALocReg2.lean:260 in BALocReg2_simp0 [simp only] (macro BALocReg2_simp0, invoked 39x; first call Graph/BALocReg2.lean:283 in BALocReg2_lw2Head)
Graph.BALocReg2_bpS_σ  Graph/BALocReg2.lean:185  uses 2: Graph/BALocReg2.lean:260 in BALocReg2_simp0 [simp only] (macro BALocReg2_simp0, invoked 39x; first call Graph/BALocReg2.lean:283 in BALocReg2_lw2Head)
Graph.BAS3Close_lift_bpv*  Graph/BAS3Close.lean:436  uses 4: Graph/BAS3Close.lean:493 in BAS3Close_rel_gg2 [simp only]
Graph.BAS3Close_D_M*  Graph/BAS3CloseC.lean:99  uses 21: Graph/BAExp14c.lean:199 in BAExp14c_ptT0 [simp only]
Graph.BAShapeO2_rho2_zero  Graph/BAShapeO2.lean:274  uses 4: Graph/BAShapeO2.lean:556 in BAShapeO2_ggA2 [simp]
Graph.BASim_owxEmb2_inr  Graph/BASim2.lean:1430  uses 3: Graph/BASim2.lean:1459 in BASim_B_B1 [simp]
Graph.lwEngine_col_transpose  Graph/LWEngine.lean:469  uses 1: Graph/LWEngine.lean:478 in lwEngine_nws [simp] (macro lwEngine_nws, invoked 13x; first call Graph/LWEngine.lean:486 in lwEngine_T1_nWS)
Graph.lwEngine_dotChoices_sc  Graph/LWEngine.lean:135  uses 1: Graph/LWEngine.lean:145 in lwEngine_partitionTerms_sc [simp only]
Graph.lwSymm_slice_flip  Graph/LWSymm.lean:394  uses 1: Graph/LWSymm.lean:399 in lwSymm_seqHflow_flip [simp only]
Graph.SEdge.localReg2_cends_mk  Graph/LocalRegular2.lean:573  uses 7: Graph/BALocReg2.lean:258 in BALocReg2_simp0 [simp only] (macro BALocReg2_simp0, invoked 39x; first call Graph/BALocReg2.lean:283 in BALocReg2_lw2Head)
Graph.localReg2_owxEmb_inr_eq  Graph/LocalRegular2.lean:1188  uses 1: Graph/LocalRegular2.lean:1190 in localReg2_msnormx [simp only] (macro localReg2_msnormx, invoked 4x; first call Graph/LocalRegular2.lean:1505 in localReg2_pathFam_oe2xR7)
Graph.localReg6d_map_mk*  Graph/LocalRegular6d.lean:291  uses 1: Graph/LocalRegular6d.lean:453 in localReg6d_ll_R8 [simp only]
Graph.localReg6d_phi_a*  Graph/LocalRegular6d.lean:251  uses 5: Graph/LocalRegular6d.lean:302 in localReg6d_phi_owxDE_fst [simp]
Graph.localReg6d_phi_b*  Graph/LocalRegular6d.lean:254  uses 5: Graph/LocalRegular6d.lean:302 in localReg6d_phi_owxDE_fst [simp]
Green.minorGreen_apply  Green/EntryCore.lean:67  uses 4: BA/GreenMinor.lean:202 in GreenMinor_Gs_insert_apply [simp only]
Green.minorMat_apply  Green/EntryCore.lean:63  uses 3: BA/GreenMinor.lean:188 in GreenMinor_Gs_insert_apply [simp only]
Green.applyOps_nil  Green/FlucIter.lean:342  uses 2: BA/GreenCond2.lean:188 in GreenCond2_qRow_graded [simpa only]
Green.numQ_nil  Green/FlucIter.lean:356  uses 2: BA/GreenCond2.lean:188 in GreenCond2_qRow_graded [simpa only]
Green.epsHom_inl  Green/FlucVanish.lean:970  uses 4: BA/GreenCond2.lean:216 in GreenCond2_epsHom_budget [simp only]
Green.epsHom_inr  Green/FlucVanish.lean:972  uses 4: BA/GreenCond2.lean:218 in GreenCond2_epsHom_budget [simp only]
Green.deltaFam_apply  Green/MinorDiff.lean:113  uses 15: BA/GreenCond.lean:67 in GreenCond_iterDeltaFam_map [simp only]
Green.gFam_apply  Green/MinorDiff.lean:435  uses 6: Green/MinorDiff.lean:457 in deltaFam_gFam_apply [simp only]
Green.gInvFam_apply  Green/MinorDiff.lean:438  uses 4: Green/MinorDiff.lean:457 in deltaFam_gFam_apply [simp only]
Green.iterDeltaFam_nil  Green/MinorDiff.lean:119  uses 5: BA/GreenMinor3.lean:455 in GreenMinor_diffBd_atom [simp only]
Green.badTower_zero  Green/MinorDiffCond.lean:141  uses 0: -  -> R-B: MinorDiffCond.lean:237
Green.flucIterHigh_seqHflow_apply*  Green/MinorGoodLe.lean:101  uses 1: Green/MinorGoodLe.lean:156 in Hflow_submatrix_set_congr [simp only]
Green.flucIterHigh_slice_apply*  Green/MinorGoodLe.lean:97  uses 1: Green/MinorGoodLe.lean:140 in Xentry_congr_of_not_mem [simp only]
Green.minorDiff_nil  Green/MinorGoodLe.lean:360  uses 1: Green/MinorDiffCond.lean:376 in norm_minorDiff_qList_greenSetDiagCentered_le [simp only]
Green.slice_apply*  Green/RowIndep.lean:297  uses 2: Green/RowIndep.lean:318 in Xentry_congr_of_ne [simp only]
Gauss.contraction_coordinateMatrix_apply*  Hierarchy/ContractionBasic.lean:116  uses 8: Hierarchy/ContractionBasic.lean:145 in coordinateMatrix_real_eq [simp]
Gauss.contraction_gloopProd_cons*  Hierarchy/ContractionBasic.lean:745  uses 2: Hierarchy/ContractionBasic.lean:766 in contraction_gloopProd_append [simp only]
Gauss.contraction_loopL_eq*  Hierarchy/ContractionBasic.lean:742  uses 1: Hierarchy/ContractionBasic.lean:805 in sum_gloop_cutGlue_split [simp_rw]
Gauss.secondLoop_gloopProd_nil*  Hierarchy/ContractionSecondLoop.lean:348  uses 2: Hierarchy/ContractionSecondLoop.lean:389 in trace_sameEdge_cutLoop [simp only]
Gauss.Sizes.B45_STKloop_eq  Induction/B45.lean:195  uses 2: Induction/B45.lean:218 in B45_ward_fin [simp only]
Ind.zSig_false  Induction/ConArgDet.lean:365  uses 5: BA/ConArg.lean:300 in BAGres_smul [simp only]
Ind.zSig_true  Induction/ConArgDet.lean:363  uses 4: BA/ConArg.lean:298 in BAGres_smul [simpa only]
Ind.LoopGenN_gloopProd_cons*  Induction/LoopGenN.lean:396  uses 2: Induction/LoopGenN.lean:416 in LoopGenN_gloopProd_append [simp only]
Ind.LoopGenN_gloopProd_nil*  Induction/LoopGenN.lean:393  uses 1: Induction/LoopGenN.lean:432 in LoopGenN_gloop_same [simp only]
Ind.LoopGenN_loopL_eq*  Induction/LoopGenN.lean:389  uses 1: Induction/LoopGenN.lean:431 in LoopGenN_gloop_same [simp only]
Gauss.Sizes.nkl_STmsig_eq*  Induction/NewKLK.lean:987  uses 1: Induction/NewKLK.lean:1074 in nkl_at [simp only]
Ind.QVN_cm_apply*  Induction/QVN.lean:116  uses 4: Induction/QVN.lean:126 in QVN_cm_lt [simp only]
Ind.QVN_wd_nil*  Induction/QVN.lean:383  uses 6: Induction/QVN.lean:395 in QVN_wd_append [simp]
Ind.gchain_single  Induction/Split.lean:314  uses 3: Induction/ConArgDet.lean:477 in gchain_eq_add_sum_gchainMixed [simp only]
Ind.gloopProd_nil*  Induction/Split.lean:272  uses 1: Induction/Split.lean:370 in gchain_mul_Eblk [simp]
Gauss.Sizes.STLM_seqHflow  Induction/Step2Defs.lean:64  uses 4: Induction/Step2Events.lean:1302 in STB_EGt_eq_LWE [simp only]
Gauss.gloopProd_cons*  Loop/GLoopFlow.lean:370  uses 2: Loop/GLoopFlow.lean:392 in gloopProd_append [simp only]
Gauss.gloopProd_nil*  Loop/GLoopFlow.lean:367  uses 1: Loop/GLoopFlow.lean:859 in norm_gloop_le_sharp [simp only]
Loop.KLWard_flipIdx_length*  Loop/KLWard.lean:1038  uses 1: Loop/KLWard.lean:1063 in KLWard_treeEqRhsS_flip [simp only]
Path.QVIdentity_cm_apply*  Path/QVIdentity.lean:119  uses 4: Path/QVIdentity.lean:129 in QVIdentity_cm_lt [simp only]
Univ.GUE_Tpp_eucl_apply*  Universality/GUEInvariance.lean:780  uses 1: Universality/GUEInvariance.lean:789 in GUE_Tpp_eucl_norm_sq [simp_rw]
Univ.GUE_Xmat_apply*  Universality/GUEInvariance.lean:827  uses 3: Universality/GUEInvariance.lean:835 in Xmat_eq_GUERe_raw [simp]
Univ.GUE_real_smul*  Universality/GUEInvariance.lean:217  uses 3: Universality/GUEInvariance.lean:241 in GUERe_smul [simp only]
Univ.GUEPhase.Duhamel_coordinateMatrix_apply*  Universality/GUEPhase/DuhamelA1.lean:77  uses 4: Universality/GUEPhase/DuhamelA1.lean:106 in Duhamel_cm_lt [simp only]
Univ.GUEPhase.Generator_gloopProd_cons*  Universality/GUEPhase/Generator.lean:995  uses 2: Universality/GUEPhase/Generator.lean:1015 in Generator_gloopProd_append [simp only]
Univ.GUEPhase.Generator_gloopProd_nil*  Universality/GUEPhase/Generator.lean:992  uses 1: Universality/GUEPhase/Generator.lean:1031 in Generator_gloop_same [simp only]
Univ.GUEPhase.Generator_loopL_eq*  Universality/GUEPhase/Generator.lean:988  uses 1: Universality/GUEPhase/Generator.lean:1030 in Generator_gloop_same [simp only]
Univ.unPinsK_band_bulk  Universality/PinsK.lean:388  uses 1: Universality/PinsK.lean:419 in UNClaimRowk_band [simp only]
Univ.unPinsK_toC_toUNModel  Universality/PinsK.lean:110  uses 1: Universality/PinsK.lean:151 in UNClaim417C_toC [simp only]

--- R-D. full build of the repaired branch (05:06:31-06:17:47 UTC), tool rerun (06:18:00-06:18:45 UTC, exit 0), check file, axioms
$ lake build > $S/build.log; grep -c "^error" $S/build.log; grep -n "axiom audit:\|premises found by scanning\|^registry:\|Build completed\|^exit" $S/build.log | cut -c1-150
0
6667:info: RBM3D.lean:656:0: axiom audit: 10486 theorems, 3858 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
6773:premises found by scanning: 94 (borrowed 1, owed 36, structural 57, refuted 0, superseded 0).
6774:registry: 2 borrowed + 98 owed + 130 structural + 3 refuted + 4 superseded; 143 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
6918:Build completed successfully (4426 jobs).
6919:exit 0
$ lake env lean docs/claude-team/tools/DeadDecls.lean > $S/tool.out; grep -E (summary lines) $S/tool.out
DeadDecls report: modules 6766, in scope 656, constants in scope 42483, counted declarations 22802
- (35 constants in RBM.Audit and its sub-namespaces; 35038 in-scope constants reached in the core)
- every core root reached: true
- declarations (non-meta units): 22733; meta declarations: 69 (unreached meta: 60)
- unreached (non-meta): 0
- modules with no reached declaration: 0
- roots: 20; already reached in the core: 20; not reached in the core: 0
- roots: 31; already reached in the core: 31; not reached in the core: 0
- roots: 3; already reached in the core: 3; not reached in the core: 0
- roots: 16; already reached in the core: 16; not reached in the core: 0
- totals over 9 name lists: 240 names, 237 in scope, 0 unreached in the core
$ grep -c "core: restored by T2523" $S/tool.out; grep -c "core: kept by T2523" $S/tool.out; grep -A1 "^## (c)" $S/tool.out | tail -1
80
42
(none)
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2523-check.lean > $S/check.out 2>&1; echo "exit $?"; grep -c error $S/check.out
exit 0
0
$ cat $S/axioms.lean | grep -c "#print axioms"; lake env lean $S/axioms.lean      # scratch, not committed
7
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_BUnivL_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Counts after the repair (from R-A, R-D): `restoredRoots` 85 -> 80 (R1), `scanProvers` 42 and R2 110 unchanged. Tool: declarations 22738 -> 22733, unreached 0,
whole-dead modules 0, reached in-scope constants 35045 -> 35038. Against T2522 core + G1-G4 (22543, narrative 6): 22733 - 22543 = 190 = 80 (R1) + 110 (R2).
Axiom audit: 10486 theorems, 3859 -> 3858 definitions, 0 axioms; scan and registry lines unchanged. Insertions (default diff) 489 -> 484 in all, 291 under
`RBM3D/`+`RBM3D.lean` (Amend 1 D2 (b): the limit reads these only); `--minimal` 249 -> 244 in all, 51 under `RBM3D/`. B15 (51 added lines) unchanged.
