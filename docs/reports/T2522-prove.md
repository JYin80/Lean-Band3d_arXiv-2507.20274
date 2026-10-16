Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct 16 20:23:40 UTC 2026

**(i) Exponent table.** No exponents, thresholds or constants: T2522 is a report-and-tool ticket with no mathematics.

**(ii) Concrete instance.** Not applicable.

Root existence (the check `docs/tickets/checks/T2522-check.lean`; CONTROL.md line 701, `done:` Fri Oct 16 20:23:35 UTC 2026): on `main` 316653b9, `lake env lean docs/tickets/checks/T2522-check.lean` exit 0, no error lines. It `#check`s final_shape, Thm27, Thm27_of_L32, band_terminal, baThm27L_any, baThm27L_of_ML, baEnd_BUnivL_of_ML, bUniv_holds, baThm27L_three, unMLOutBA_three.

Declarations located by `grep` (command: `grep -nE "^(theorem|lemma|def|abbrev) <name>" <file>`), verbatim hits:
```
RBM3D/Main/FinalShape.lean:36:def Thm27 : Prop := RBM.BA.BAThm27L 3
RBM3D/Main/FinalShape.lean:39:theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27 := RBM.BA.baThm27L_three
RBM3D/Main/FinalShape.lean:43:theorem final_shape : RBM.Univ.UNL32 →
RBM3D/Main/BandTerminal.lean:104:theorem band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff := fun h32 =>
RBM3D/BA/UNBUniv.lean:262:theorem baEnd_BUnivL_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAEnd_BUnivL d :=
RBM3D/BA/UNBUniv.lean:271:theorem baThm27L_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAThm27L d :=
RBM3D/BA/UNBUniv.lean:281:theorem baThm27L_three : UNL32 → BAThm27L 3 :=
RBM3D/BA/UNBUniv.lean:286:theorem baThm27L_any (d : ℕ) (hd : 3 ≤ d)
RBM3D/BA/MainIndTermBA.lean:47:theorem unMLOutBA_three : Univ.UNMLOutBA 3 := unMLOutBA_of_famStep 3 baMainIndFamTL_three
RBM3D/Main/BUnivHolds.lean:227:theorem bUniv_holds :
```
Other roots' source files exist: `RBM3D/Main/FinalShape.lean`, `RBM3D/Main/BandTerminal.lean` (`example`s at lines 118 ff.), `RBM3D/Main/BUnivHolds.lean`, `RBM3D/BA/MAPins.lean` (5 lines starting `example`), `RBM3D/Test/Axioms.lean`, `RBM3D/Test/AuditNegative.lean`. `git ls-files RBM3D/Probe | wc -l` prints 0. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2522` is at 316653b9.

## Verdict
T2522 stage 1a: PASS (all listed roots exist; no hypotheses, exponents or instance to check).

## (b) Script output — worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2522`, branch `t/T2522`, tool commit 0aea2069

Tool run (main worktree `/Users/junyin/Lean_proof/RBM3D`, `main` 316653b9; Fri Oct 16 20:29:27 UTC 2026 to 20:30:06 UTC; exit 0; 12060 output lines, all in `docs/reports/T2522-dead.md`):
```
$ lake env lean /Users/junyin/Lean_proof/RBM3D-wt/T2522/docs/claude-team/tools/DeadDecls.lean > out.txt 2>&1; echo $?
0
--- first 20 lines of the output ---
DeadDecls report: modules 6783, in scope 673, constants in scope 56575, counted declarations 32992

## (a) roots actually used
- RBM.Endpoints.final_shape  (core: ticket root)
- RBM.Endpoints.Thm27  (core: ticket root)
- RBM.Endpoints.Thm27_of_L32  (core: ticket root)
- RBM.Endpoints.band_terminal  (core: ticket root)
- RBM.Univ.UNL32  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_decol  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_locSC  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_QUE  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_BUniv  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Endpoints.Inst.inst_QDiff  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- private RBM.Endpoints.FinalShape_hg  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.BAInst.S0  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.BAInst.S0_adm  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.BA.UNPinsInst.clsκ  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.BA.UNPinsInst.clsκ_pos  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.BA.UNPinsInst.fp  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
- RBM.Univ.BAInst.S0_bulk  (core: added by hand, constant of the `example`s in Main/FinalShape.lean)
--- last 20 lines of the output ---
  RBM.Univ.UNQuek  line 381
  RBM.Univ.UNLocAvgk  line 382
### RBM.Audit.supersededProps  (lines 408-435): 19 names, 19 in scope, 16 unreached in the core, 0 not constants
  RBM.Gauss.Sizes.STStep3  line 417
  RBM.BA.BAConArg'  line 418
  RBM.Gauss.Sizes.STStep3I  line 419
  RBM.Gauss.Sizes.STStep4  line 420
  RBM.Gauss.Sizes.STStep5  line 421
  RBM.Gauss.Sizes.STStep6  line 422
  RBM.BA.STStep6gL  line 423
  RBM.Gauss.Sizes.STExpIniI  line 424
  RBM.Gauss.Sizes.STExpIntI  line 425
  RBM.Gauss.Sizes.STOeqNQ'  line 426
  RBM.Gauss.Sizes.STOeqQt  line 427
  RBM.Gauss.Sizes.STOeqQtNZ  line 428
  RBM.Gauss.Sizes.STIterations  line 429
  RBM.Gauss.Sizes.STIterationsII  line 430
  RBM.Gauss.Sizes.LWG5Expand  line 431
  RBM.BA.BAGbEXPij  line 435
- totals over 9 name lists: 290 names, 287 in scope, 54 unreached in the core
```
Scope and sanity checks (each command run in `/Users/junyin/Lean_proof/RBM3D-wt/T2522` unless stated):
```
$ git diff main...t/T2522 -- RBM3D RBM3D.lean | wc -l
0
$ git diff --stat main...t/T2522
 docs/claude-team/tools/DeadDecls.lean | 274 ++++++++++++++++++++++++++--------
 1 file changed, 214 insertions(+), 60 deletions(-)
$ git ls-files RBM3D/Probe | wc -l
0
$ grep -rn "DeadDecls" RBM3D RBM3D.lean | wc -l     # name-clash grep (the tool declares only `DeadDecls.*`, not imported)
0
$ grep -n -A8 "^## sanity checks" docs/reports/T2522-dead.md     # in the main worktree
145:## sanity checks (core closure)
146-- every core root reached: true
147-- RBM.BA.baThm27L_three: reached in the core
148-  reached via (first discovered path, from the name up to a root): RBM.BA.baThm27L_three <- RBM.Endpoints.Thm27_of_L32
149-- RBM.BA.unMLOutBA_three: reached in the core
150-  reached via (first discovered path, from the name up to a root): RBM.BA.unMLOutBA_three <- RBM.BA.baThm27L_three <- RBM.Endpoints.Thm27_of_L32
151-- RBM.Endpoints.bUniv_holds: reached in the core
152-  reached via (first discovered path, from the name up to a root): RBM.Endpoints.bUniv_holds <- RBM.Endpoints.unBUniv_of_L32 <- RBM.Endpoints.BUniv_of_L32 <- RBM.Endpoints.band_terminal
153-
```
Sanity result: every core root is reached; `RBM.BA.baThm27L_three`, `RBM.BA.unMLOutBA_three` and `RBM.Endpoints.bUniv_holds` are all REACHED in the core (paths above). Hence G4 adds nothing over the core.
Deletion test (scratch copy, not committed): `cp -c -R /Users/junyin/Lean_proof/RBM3D-wt/T2522 <scratchpad>/T2522/wt-scratch`; module `RBM3D.Universality.GUEPhase.RandomLayerBGD` (8 declarations, 4 reached, 4 unreached: `inst_unClaimRowkD_band_zero 120-135`, `inst_un_claimAll_of_rowskD 137-149`, `inst_ouRowk_of_pinsD 151-161`, `inst_g1Rowk_of_inputsGD 163-177`); lines 120-177 deleted (the four theorems with their docstrings; the ranges start at the docstring); `lake build` in the scratch copy, Fri Oct 16 20:40:52 UTC 2026 to 20:42:22 UTC:
```
$ git diff --stat          # in the scratch copy
 RBM3D/Universality/GUEPhase/RandomLayerBGD.lean | 58 -------------------------
 1 file changed, 58 deletions(-)
$ lake build ... (lines of the log)
✔ [4439/4443] Built RBM3D.Universality.GUEPhase.RandomLayerBGD (11s)
✔ [4440/4443] Built RBM3D.BA.UNBUniv (7.6s)
Build completed successfully (4443 jobs).
exit 0
```
Ported file: `docs/claude-team/tools/DeadDecls.lean`, RBM2D `docs/claude-team/tools/DeadDecls.lean` (last commit touching it `c9a24cf`; RBM2D HEAD `9e0f275`); the copy already on `main` differed from it only in the project name (`diff` of the two files, before my edits: only the `RBM2D`/`RBM3D` lines 2, 4, 10, 11, 13, 36, 56, 70, 306). `git -C ../RBM2D --no-optional-locks diff --stat HEAD -- docs/claude-team/tools/DeadDecls.lean` prints nothing (unchanged). No RBM1D file used.
Axioms and targets: not applicable; the ticket has no Lean target and adds no declaration to the library (`RBM3D/` and `RBM3D.lean` untouched).
Tool changes (vs the copy on main): `fixedRoots`/`exampleRoots`/`sanity` replaced by the RBM3D roots; new `groups` (G1-G4, closure of core plus group); `closure` is a function of the roots; section (a) lists the group roots, the sanity section reports status and first discovered path; new sections (f) groups and (g) Audit registry lists (Name literals of every `Name`-valued constant in `RBM.Audit`, their unreached members with the line in `RBM3D/Test/Axioms.lean`, read from the current directory); `privName` builds the name of the private `FinalShape_hg`, `MAPins_hg`.

Narrative: G1 is not wholly inside the core (16 of 20 roots reached; the 4 others are `inst_bridge_loc`, `inst_bridge_que`, `unOUClaims_holds`, `unOUQUE_holds`: 4 declarations, 27 lines). G2 is not wholly inside either (22 of 31 roots reached; 10 extra declarations, 53 lines, mostly `BA/UNPins`, `BA/MAPins`). G3 adds 2 declarations (12 lines, in `BA/MainIndTermBA` and `BA/UNBUniv`). G4 is inside the core. The core closure leaves 10243 of 32770 declarations unreached, in 100272 line spans, 17 whole modules dead; (g): 54 of 287 in-scope registry names are unreached (11 owed, 4 refuted, 23 structural, 16 superseded) and must leave the registry in the deletion ticket.

## (c) Mathlib names
None used (the tool uses Lean core API only: `Lean.Environment`, `getStructureInfo?`, `findDeclarationRanges?`, `Std.HashMap/HashSet`); no Mathlib name checked or invented.

## (d) Open issues and paper-delta candidates
1. `example`s are not constants, so the closure does not see them: unreached helpers used only by `example`s are listed as unreached, and a deletion must remove or rewrite those `example`s. Evidence: `grep -n "j_data\|j_hscale\|j_hell" RBM3D/BA/GUEPathBoundsBA.lean` shows the unreached private `j_*` (655-733) used at 683, 706, 743-772 (inside the `example`s); `private GUELLBAInst.hg` (`BA/GUELLBA.lean:368`) is used at 374-384. The deletion test above used a module whose unreached theorems were not used elsewhere (`grep -rn` of the four names over `RBM3D` and `RBM3D.lean`, outside that file, prints nothing; the build passes).
2. `RBM.BA.GUETwistBA_Pi_apply` (`BA/GUETwistBA.lean:66-67`) is reported unreached while named in `simp only [...]` at lines 77, 87, 103, 110, 118, 119 (listed there; whether simp fires it was not checked); deleting it needs those simp lists changed. Not build-tested.
3. `RBM3D/Test/InterfaceShape.lean` (namespace `RBM.Test`, line 42) is not a root of the ticket (only `RBM.Audit`): it is reported whole-module dead in (c), imported by `RBM3D` only (per (c)). The dispatcher decides whether it is a root.
4. Declaration ranges (`findDeclarationRanges?`) start at the docstring (`RandomLayerBGD.lean:120` is `/--`), so unreached line spans include docstrings.
5. Paper-delta candidates: none (no Lean statement, no paper statement).

