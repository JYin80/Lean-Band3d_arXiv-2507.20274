Auditor model: claude-opus-5-5

# T2537 audit, round 2 (written Sat Oct 17 19:12:12 UTC 2026)

Ticket `docs/tickets/T2537.md` with Amend 1 (`docs/tickets/T2536-T2547-amend-1.md`); Amend 2's name/path check
was also run, since round 1 required it. Comments only, the 50 files of `docs/tickets/T2537-files.txt`. Branch
`t/T2537` at `b202392c` (repair of round-1 RETURN), merge-base `b51d55d7`, `main` at `0fc1e018`. Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2537-audit2` (detached at `b202392c`). The ticket has no theorem targets. Its
targets are rules 1-5 and the acceptance list, so the statement, vacuity and nonempty-instance items apply only through
the code-identity check (no declaration is added or changed).

## 1. Diff scope and code identity
```
$ git diff --name-only main...t/T2537 | sort | diff - <(sort docs/tickets/T2537-files.txt) && echo "changed files == list"
changed files == list
$ git diff --shortstat main...t/T2537
 50 files changed, 2108 insertions(+), 3152 deletions(-)
$ git diff --stat b51d55d7 main -- $(cat docs/tickets/T2537-files.txt) | wc -l     # files untouched on main since base
       0
$ python3 -I lexstrip.py     # auditor's own splitter: -- to EOL, nested /- -/ (/-- -/, /-! -/), "..." with escapes,
                             # 'c' char literals (not after an identifier char), «...»; compares rstripped non-blank
                             # code lines (indentation kept) of main:<f> and t/T2537:<f>
identical: 50 files
different: 0
$ self-test: nested "a /- x /- y -/ z -/ b -- q\n\"--s\" c" -> ['a  b','"--s" c']: True; one ':=' -> ': =' mutation in NQLin detected: True
```
No declaration, statement, proof, attribute, import, `open`/`set_option` line or string changed: no frozen signature
touched, no `sorry`/`admit`/`axiom`/`native_decide` added, no instance obligation arises.

## 2. Build and axioms (audit worktree, head b202392c)
```
$ lake build > build.log 2>&1; echo EXIT=$?      # started Sat Oct 17 17:27:05 UTC 2026
Build completed successfully (4426 jobs).
EXIT=0                                            # finished Sat Oct 17 19:11:09 UTC 2026
$ grep -ciE "^error|: error" build.log
0
info: RBM3D.lean:656:0: axiom audit: 10488 theorems, 3858 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; ...
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2537-check.lean; echo exit=$?
exit=0      (12 output lines, 0 containing "error")
```

## 3. Ticket acceptance greps (audit worktree)
```
$ bash -c 'grep -rnEi "<ticket regex verbatim>" $(cat docs/tickets/T2537-files.txt)' | cut -c1-100
LemDecCalEPrec.lean:286,287,294   have h729 / h729'            (code; \bH[0-9]{3}\b case-insensitive)
PfStep5.lean:2036,2050            have h128                     (code)
QEndGrid.lean:629,637             have h123                     (code)
QLevelsA.lean:421,427,429,482,484,488,491   QLevelsA_frozen(_ward) (private Lean names, code)
QProxy.lean:651,683               section D1 / end D1           (code)
QopAlgebra.lean:445, QopDecay.lean:332      have hub := ...     (code)
[18 lines]
$ python3 -I cgrep.py      # same patterns applied to comment text only (lexstrip split)
[ticket-acceptance] comment hit lines: 0
[CJK] comment hit lines: 0                       # [一-鿿]
[labels] comment hit lines: 0                    # U1s2, V2a, MN-D3, C5..., MA-06b, BA-.., ST-6, UN-01, KL-D1, PT-D1, EK-D1, LW-10c, X1, G1-G4
[hash] comment hit lines: 0                      # 7-40 hex chars with a digit and a letter
[extra-vocab] comment hit lines: 20              # route|wave|stage|landing line|stop line|borrowed|refuted|superseded|
                                                 # was replaced|earlier version|no longer|moved from|renamed|the old|Fable|TEAM|HANDOFF
   all 20 in MainIndRegimes.lean: "the stage of `s_n`", "stage pattern of `[s_n, t_n]`", "two-stage composition"
   (the index k of the regime interval [c_k, c_{k+1}], Lean names STStageS/STStageT): mathematical
[sister-fileline] comment hit lines: 3           # .lean:N or RBM[12]D/<path>
   QtNonzero.lean:23, QtNonzeroEnd.lean:20, QtXiRoundLift.lean:42: "No RBM1D/RBM2D source ..." (no path, no line)
$ grep -L '/-!' <files>                       -> (no output)
$ first item after copyright header/imports/options is "/-!" then "# ..."   -> files failing: 0
$ copyright header (text through first "-/") main vs branch                  -> header differs: 0
$ python3 docs/claude-team/tools/texref.py --scan <files> | wc -l
branch: 0 (exit 0)      main: 246
```

## 4. Final-paper references
```
$ python3 -I <cite check>   # "<Kind> n.m (`label`)" and "(n.m) `label`" in comments vs docs/claude-team/tools/paper-labels.tsv
number/label pairs checked: 368 matching: 368 mismatching: 0 (label not in tsv: 2 )
word/kind pairs: {('Lemma','lemma'): 93, ('Theorem','theorem'): 7, ('Claim','claim'): 6, ('Definition','definition'): 8, ('Example','example'): 6}
kind mismatches: 0
```

## 5. Amend 1 (d >= 3 scope sentences)
```
$ grep -nE 'D723|decision B|§316|only (for|at) .?d = 3|d = 3 only|out of scope' <files>   -> (no output)
$ grep -nE 'd *> *3|d *≥ *4|d *= *3|three-dimensional|dimension 3' <files>               -> (no output)
$ comment-only "enters only" hits: 8 (NQEndFlow:24,165, NQLin:21, QBudgetB:15, QGridB:38, QtNonzeroBoot:53,1045,
  QtXiRoundLift:38): each about an argument of a formula (`B` in `STbootRHS`, `n_`, `STKbound`, `GoodSetN`), not d-scope
```
These Induction files make no claim that a result holds only at `d = 3`; "`d ≥ 3`" headings match the hypotheses `3 ≤ d`.

## 6. Names and module paths in comments (round-1 item 4; Amend 2 items 1-2)
```
$ python3 -I names.py   # backticked identifiers in comments vs identifiers in the code of RBM3D/**/*.lean + RBM3D.lean,
                        # exact (primes kept); dotted names also accepted by last component; labels from \label{} of
                        # paper/final/tex, paper/tex and paper-labels.tsv; subscript X_y excused
backticked identifiers checked: 4797
absent from RBM3D code, not in a paragraph naming RBM1D/RBM2D/Mathlib: 52
   50 are helper prefixes or list abbreviations ("prefixed `nqBudget_`", `_Lloop_subg`, `qProxy`, `qdec`, ...):
      e.g. QopDecay:23 prefix `qdec` -> qdec_growth in code (4 hits); LoopC2N:35 `_contDiffAt_Gres` = suffix of LoopC2N_ helpers
   NQEndFlowLift:54 `when`: backtick-pairing artefact across a formula (not a name)
   path-like `RBM.Ind`, `RBM.Loop`, `RBM.BA`: namespaces present (56, 22, 239 files); `RBM.Gauss.Sizes.STNewPQ`:
      Step34Pins.lean:40 namespace RBM.Gauss.Sizes, :326 def STNewPQ; `Ind.Gres_mul_conjTranspose`: ConArgDet.lean:567
      inside namespace RBM.Ind; `H.IsHermitian`, `Cm.Pp`, `C.L`: field/dot notation
absent from RBM3D code, in a paragraph naming RBM1D/RBM2D/Mathlib (excused): 158  (117 distinct)
$ grep -rqF each distinct excused name in ../RBM2D/RBM2D, ../RBM1D/RBM1D, Mathlib (read only)
found: 113; not found: _contDiffAt_Gres _hasDerivAt_Gres nqEnd_ qtLift_   (list suffixes/prefixes of RBM3D private helpers)
$ RBM3D module paths `X/Y`, `X.lean` in comments checked against the tree      -> MISSING: none
$ grep RBM2D module paths (AltDriftQ.lean|AltGridQ.lean|AltProxyQ.lean|HierVocab.lean|SumZeroQ.lean) and "Route"  -> (no output)
```
Round-1 defects, rechecked on the branch:
```
$ grep -nE "Step34PinsP|\`STXiBoot\`|\`STOeqQt\`|\`STOeqQtNZ\`|\`STIterR\`|\`STNQConcl'\`|\`altGridEndQN\`" <files>  -> (no output)
NQLin.lean:15-16  "the statements with `B_s` are in `Induction/NQEndFlow.lean`"   (file exists)
NQEndFlow.lean:16-27 module docstring names STNQConcl'', STXiBoot', STOeqQt', STOeqQtNZ', STIterR' (defs at :71,:88,
   :118,:122,:128) and states the `B_s = sz.Bctl n (s n)` argument of `STbootRHS` directly, with the paper's `B_u` noted
QEndB1.lean:19-22 "the grid endpoint is `altGridEndQN'` (`QEndGrid.lean`)" -> QEndGrid.lean:1329 theorem altGridEndQN'
```
Remaining "with X in place of Y" sentences (QEndGrid:320, NQEndFlow:536, NQGood2:19-20, QVN:400, ...) name either RBM3D
declarations that exist (`nqGridEndLinN` NQEndLin.lean, `nzGridEndN` QtNonzeroEnd.lean) or RBM2D/RBM1D declarations in a
sentence attributed to them (`GridEndConcl`, `gridEnd_to_flow` in RBM2D Induction/StoppedEndDefs.lean;
`ugenPairCase1Explicit` in RBM2D Evolution/Bridge.lean), or symbols (`W^d` for `W²`, `Zd d L` for `ZMod L`).

## 7. Paper deltas
No code change, no Lean/paper statement difference; no candidate needed, none proposed. Covered.

## 8. Observations (no RETURN)
- O1 Amend 2 is addressed to comment tickets starting after 15:37 UTC; T2537 started earlier. Its items 1-2 hold anyway
  (section 6); items 3-5 were spot-checked on the repaired docstrings (no "Route", no invented label shorthands seen).
- O2 The repair section of the prove report records `pkill -f "lake build"` runs that hit other worktrees' builds; this
  is process information and does not change any statement, build or comment of T2537.
- O3 `main` advanced to `0fc1e018` after the base; the 50 files are unchanged on main since `b51d55d7` (section 1), so
  bringing them in is conflict-free. The hub's merge build reruns the full library.

## 9. Verdict
| Target | Verdict |
|---|---|
| Diff touches only the 50 listed files; comment-stripped code identical (50/50) | PASS |
| Acceptance grep (18 code-only hits), CJK, `/-!` module docstrings, headers, TeX line refs 246 -> 0 | PASS |
| Final-paper references (368 number/label pairs, 0 mismatches; kinds 0 mismatches) | PASS |
| Amend 1 scope sentences | PASS |
| Round-1 repair items 1-5; names and paths in comments exist | PASS |
| Full `lake build` EXIT=0, axioms within propext/Classical.choice/Quot.sound; check file exit 0 | PASS |

**PASS.** No dispatcher sign-off needed.
