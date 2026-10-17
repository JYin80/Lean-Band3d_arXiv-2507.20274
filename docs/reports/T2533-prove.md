Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 07:57:25 UTC 2026

(i) see `docs/reports/T2524-design.md` §1 and the T2524 prove report (a) (`docs/reports/T2524-prove.md`).

(ii) not applicable.

PASS

## (b) Script output (written Sat Oct 17 08:08:20 UTC 2026)
```
$ git log --oneline main..t/T2533; git diff --shortstat main...t/T2533; git diff --stat main...t/T2533   # base main 970b8b54
6db8094a T2533: BA case (iii) of Step 5 at every d >= 3, in place (baStep5III_holds_any)
 5 files changed, 284 insertions(+), 268 deletions(-)
 RBM3D/BA/Step5IIIGood.lean    |  94 ++++++------
 RBM3D/BA/Step5IIIGood2.lean   |  16 +-
 RBM3D/BA/Step5IIITargets.lean |  44 +++---
 RBM3D/BA/Step5IIIWalk.lean    |  66 ++++-----
 RBM3D/BA/Step5IIIWalk2.lean   | 332 +++++++++++++++++++++---------------------
 5 files changed, 284 insertions(+), 268 deletions(-)
$ lake build RBM3D.BA.Step5IIIGood (then Good2, Walk, Walk2, Targets): last "Built" line of each (tool log, before the Targets edit below)
✔ [3886/3886] Built RBM3D.BA.Step5IIIGood (20s)   ✔ [3892/3892] Built ...Good2 (3.8s)   ⚠ [4105/4105] Built ...Walk (10s)
✔ [4106/4106] Built RBM3D.BA.Step5IIIWalk2 (10s)   ⚠ [4115/4115] Built ...Targets (2.9s); each ended "Build completed successfully"
$ lake build   # whole library, final tree 6db8094a, 08:03:36 to 08:05:16 UTC (scratch full_build2.log)
info: RBM3D.lean:656:0: axiom audit: 10487 theorems, 3858 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 94 (borrowed 1, owed 36, structural 57, refuted 0, superseded 0).
Build completed successfully (4426 jobs).
error lines in the log: 0; the premise scan (Test/Axioms.lean:532-533) throws when 'unregistered' is non-empty: the build passed, so unregistered = []
$ lake env lean scratch/axioms.lean   # #print axioms, scratch, not committed
baStep5III_holds_any : [propext, Classical.choice, Quot.sound]
baStep5III_holds : [propext, Classical.choice, Quot.sound]
baPfStep5_holds : [propext, Classical.choice, Quot.sound]
baPfStep5_of_walk : [propext, Classical.choice, Quot.sound]
baStep5IIIGoodThm_holds : [propext, Classical.choice, Quot.sound]
baStep5IIIWalk_holds : [propext, Classical.choice, Quot.sound]
baStep5IIIFromWalk_holds : [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2533-check.lean ; the same with Part 2 activated (scratch copy, last comment line uncommented)
Part 1: exit=0, 'error' lines=0; Part 2 (example : T2533Check.Target := baStep5III_holds_any): exit=0, 'error' lines=0
$ grep -nE "Sizes 3|Zd 3|Idx 3" RBM3D/BA/Step5III{Good,Good2,Walk,Walk2,Targets}.lean
(no output; grep exit=1)
$ grep -nE "\b(sorry|admit|native_decide)\b|^axiom " <the five files>
(no output; grep exit=1)
$ zsh extract.sh   # statements extracted from the files (up to the first ":=" line; Props: first lines)
RBM3D/BA/Step5IIITargets.lean:58: theorem baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) :
RBM3D/BA/Step5IIITargets.lean:59:     STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
RBM3D/BA/Step5IIITargets.lean:63: theorem baStep5III_holds :
RBM3D/BA/Step5IIITargets.lean:64:     STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
RBM3D/BA/Step5IIIGood.lean:416: def BAStep5IIIGoodThm (d : ℕ) : Prop :=
RBM3D/BA/Step5IIIGood.lean:417:   3 ≤ d → ∀ (κ ε 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → BAFlow sz κ ε 𝔠 𝔡
RBM3D/BA/Step5IIIWalk2.lean:75: def BAStep5IIIWalk (d : ℕ) : Prop :=
RBM3D/BA/Step5IIIWalk2.lean:76:   STIngR5gL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
RBM3D/BA/Step5IIIWalk2.lean:77:     (fun sz z s t => BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t)
RBM3D/BA/Step5IIIWalk2.lean:81: def BAStep5IIIFromWalk (d : ℕ) : Prop :=
RBM3D/BA/Step5IIIWalk2.lean:82:   3 ≤ d → ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → BAFlow sz κ ε 𝔠 𝔡 z →
--- instance (extracted)
RBM3D/BA/Step5IIITargets.lean:73: example :
RBM3D/BA/Step5IIITargets.lean:74:     STStep5IIIgL 4 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
RBM3D/BA/Step5IIITargets.lean:75:   baStep5III_holds_any 4 (by norm_num)
$ python3 d2cmp.py   # the four Prop texts of the audited design probe (git show t/T2524:RBM3D/Probe/T2524Pins.lean) against the files
# normalization: whitespace collapsed, `T2524_` prefix and the `{d : ℕ}` binder removed
BAStep5IIIGood         identical: True (2353 chars)
BAStep5IIIGoodThm      identical: True (526 chars)
BAStep5IIIWalk         identical: True (232 chars)
BAStep5IIIFromWalk     identical: True (359 chars)
$ grep -rln baStep5III_holds_any RBM3D docs/tickets/checks   # name clash: the new public name is defined once (Targets:58)
RBM3D/BA/Step5IIITargets.lean
docs/tickets/checks/T2534-check.lean
docs/tickets/checks/T2533-check.lean
$ python3 numerals.py   # every numeral 3 left in the code of the five files (comments stripped), by syntactic role
file      guard   loop   frac    pow  const  total
Good          1      9      3      3      2     18
Good2         2      0      0      0      0      2
Walk          8      3     51      7     23     92
Walk2         7      0     16     10     10     43
Targets       1      0      0      0      2      3
all          19     12     70     20     37    158
  guard  = hypothesis/guard `3 ≤ d`, `3 ≤ L`, `3 ≤ N` (paper d ≥ 3; `three_le_L`)
  loop   = loop order: `Fin 3`, `finRotate 3`, `Icc 3 2`, `hLmax 3`, `{2,3,4,5}`, `p + 3`
  frac   = exponent fraction `3/2`, `3/4`, `3 ε₀/2`: `ℓ* = (log W)^{3/2}`, `J^{3/2}`
  pow    = power `^ 3`: `N³` (`Cv = 3`), `τ³`, `ρ³`, `J³` (loop length 4)
  const  = numeric coefficient or slack, listed by line below (`3 (w-v)`, `W^{3ε₀}`, `+ 3`, `3 N^{-(D'+1)}`, `Step5IIIGood_scale 3`)
```

Narrative (facts from the commands above and the tool log).
- Method: the edits are the design gate's scratch generalization (`scratchpad/T2524/full/T2524G/*.lean`: the 13 lexical rules and 77 hand edits of `T2524-design.md` section 1), carried onto main 970b8b54 by `git merge-file` (base = the five files at afab243f, ours = main's, theirs = the scratch files with `T2524G.*` imports mapped back to `RBM3D.BA.Step5III*`). Each file had one conflict, the instance-tail region that T2523 deleted (ours empty); I dropped that block. Loop output: `Good exit=1 conflicts=1 lines=709`, `Good2 ... 203`, `Walk ... 1781`, `Walk2 ... 1072`, `Targets ... 120` (with markers). The five merged files compiled in import order with no further edit.
- Own edits after the merge, all in `Step5IIITargets.lean`: the docstrings that said `d = 3` (module items 3-4, `baPfStep5_holds`, `baStep5III_holds_any`, `baStep5III_holds`), and section 2 (the instance stub T2523 emptied) replaced by the `d = 4` example. The other four files are exactly the merge result.
- Stop rules: landing is 284 insertions / 268 deletions (shortstat) against the 1,950 cap; no (b) item beyond its design entry and no (c) item arose; Walk and Walk2 did not stall, so the split R1a | R1b is not used.
- Instances: the ticket says the tails went with T2523 and R2 handles instances, so no `d = 3` instance is added (CLAUDE.md section 4 step 2 is met here only by the `d = 4` application, `Targets:73-75`, whose single hypothesis `3 ≤ 4` is discharged; Part 2 of the check applies the target at every `d`). No `Sizes 4` data instance is in these files (R2).
- `baStep5III_holds` keeps its type (Part 1 compiles unchanged); its readers `MainIndFamTL`, `MainIndRegBA`, `MainIndTermBA`, `UNBUniv` are rebuilt in the final full build (`full_build2.log:6457, 6491, 6510, 6541`). Registry unchanged: the three Props `BAStep5IIIGoodThm`, `BAStep5IIIWalk`, `BAStep5IIIFromWalk` have the audited D2 texts (d2cmp) and are concluded by theorem heads.
- Remaining numeral `3`s: classes guard, loop, frac, pow are in the legend above (`Fin 3` 3-loops, `ℓ* = (log W)^{3/2}`, `N^3` with `Cv = 3`, `3 ≤ d` guards). The 37 `const` lines, by reason:
  `W^{3ε₀}` (paper exponent of the closure bound): Walk:887, 912, 915, 918, 920, 1209, 1283, 1285, 1287, 1288, 1319; Walk2:139, 223, 294, 305, 388.
  coefficients `3 (w-v)`, `3 Δ` of the `Step5IIIWalk_Uc`/`_Tc` bounds: Walk:509, 535, 545, 567, 632, 637; `3 W^{2ε₀}(g²W^d)^{-1/4}`: Walk:1066, 1114, 1116, 1148.
  `+ 3` in `Step5IIIWalk_Ctot`: Walk:968; `J^3 ≤ W^{3ε₀}` (`(0:ℝ) ≤ 3`): Walk:1230; `Step5IIIGood_scale 3`, `hQ2 3` = case (v), `k = 4` (4-loop): Good:560.
  union count `3 N^{-(D'+1)}`: Walk2:541, 543, 567; exponent slack `D' + cK + 3`: Walk2:668, 715; Targets:64-65 = the dimension `3` of the kept `baStep5III_holds`.

## (c) Verified Mathlib names
No new Mathlib name: script over `git diff -U0 main...t/T2533` (identifiers containing `.` or `_` in added lines and in no removed line) printed `['baStep5III_holds_any', 'discharged.']`. No name verified absent.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2524a`, D712 (d) superseded by R1, was proposed by the design gate).
- Stale text I did not touch (comment ticket, `T2524-design.md` section 6): instance-section stubs that T2523 emptied still say "Compiled nonempty instances at `d = 3`": Good:41, :607; Good2:22, :25, :84, :87; Walk:1500; Walk2:29, :989.
- R2 remains: `baThm27L_all`, `Thm27`, `final_shape` and the `d = 4` data instance.
