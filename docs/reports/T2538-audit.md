Auditor model: claude-opus-5-5

# T2538 audit, round 1 (comments only, `RBM3D/Induction/` S-Z), written Sat Oct 17 13:43:41 UTC 2026

Inputs: ticket `docs/tickets/T2538.md`, Amend 1 `docs/tickets/T2536-T2547-amend-1.md`, files list
`docs/tickets/T2538-files.txt` (28 files), check `docs/tickets/checks/T2538-check.lean`, prove report
`docs/reports/T2538-prove.md`. Branch `t/T2538` = `ea3537e4` (one commit on merge-base `d0c20cc0`).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2538-audit1` (detached at `ea3537e4`). Scratch: scratchpad `T2538/`.

There are no target theorems: the ticket is a comment-only rewrite. The statement-centred items (1)-(3) reduce to
"no code token changed", so the published statements are the ones on `main` (checked by the stripper and the check file).

## 1. Scope: the diff touches exactly the listed files
```
$ git diff --name-only main...t/T2538 | sort > diffnames; sort docs/tickets/T2538-files.txt > list; diff diffnames list && echo ...
diff names == files list (      28 files)
$ git diff --name-only main...t/T2538 -- ':!RBM3D/Induction'      # (empty)
$ git diff --quiet d0c20cc0 main -- $(cat docs/tickets/T2538-files.txt) && echo ...
main vs d0c20cc0 on the 28 files: no change
$ git log --format='%h %an <%ae> %s' main..t/T2538
ea3537e4 Jun Yin <321276894+JYin80@users.noreply.github.com> T2538: comment clean-up of RBM3D/Induction (names S-Z), comments only
```

## 2. No code change (independent stripper, written by the auditor)
Own lexer: drops `--` to end of line and nested `/- -/` (including `/--`, `/-!`), keeps string and char literals
verbatim, then compares the remaining non-blank lines (right-stripped) of `git show <base>:<f>` and `git show t/T2538:<f>`.
```
$ python3 -I T2538/strip.py main
identical: 28 files
different: 0
$ python3 -I T2538/strip.py d0c20cc0
identical: 28 files
different: 0
$ git diff main...t/T2538 | grep -E '^\+' | grep -cwE 'sorry|admit|native_decide|axiom'
0
$ for f in <28 files>; do cmp <(git show main:$f | head -5) <(head -5 $f) || echo "header differs: $f"; done
(no output: all 28 copyright headers unchanged)
```

## 3. Ticket acceptance greps (branch tree, `/bin/bash`, BSD grep)
```
$ grep -rnEi '<the ticket pattern, verbatim>' $(cat docs/tickets/T2538-files.txt) > grep1; wc -l < grep1
      31
$ grep -vi control grep1
RBM3D/Induction/StepDecompN.lean:72:section PinnedDefs
RBM3D/Induction/StepDecompN.lean:147:end PinnedDefs
$ grep -i control grep1 | grep -oiE '.{0,25}control[a-z]*.{0,20}' | sort | uniq -c   (29 lines, excerpts)
   1 ... the deterministic control parameters `Ξ^{(𝓛)} ...
   1 ... **The random control `Ĵ^ℓ_{u,D}`** of (3 ...
   1 ... **The control parameter `Ψ(n,k;s, ...
   1 ... he three error terms are controlled by `STEtermsMidConc ...
   (all 29: the English word control/controls/controlled; the pattern is case-insensitive and contains CONTROL)
```
Remaining hits: 29 mathematical ("control" of the paper's control parameters / "controlled by"), 2 the code token
`section PinnedDefs` / `end PinnedDefs` (a Lean name, must not change). Accepted.
```
$ python3 -I -c '<count [一-鿿] in the 28 files>'
CJK chars in 28 files: 0
$ grep -L '/-!' $(cat docs/tickets/T2538-files.txt); echo "exit=$?"
exit=0                               # no file printed
$ python3 -I - <first command after copyright/imports/set_option is `/-!`>
module docstring first after imports/options: 28 / 28
(no empty comment shells `/-- -/`, `/-! -/`, bare `--` found by the same script)
$ grep -nE 'D723|decision B|§316|only (for|at) .?d = 3|d = 3 only|out of scope' $(cat docs/tickets/T2538-files.txt); echo "exit=$?"
exit=1                               # Amend 1 pattern: no hit
```

## 4. Further checks on the comment text (auditor's comment extractor, 3014 comment lines)
```
$ awk '<comment text> ~ /\.tex|paper\/tex|[0-9A-B_-]+:[0-9][0-9]|\.lean:[0-9]+|line [0-9][0-9]/ && !/arXiv:/'
(no output: no TeX line references, no file:line references)
$ awk '<comment text> ~ /AuditNegative|[Rr]egistry|Premise[A-Z]|[Bb]orrowed|[Ss]tructural|[Rr]efuted|[Ss]uperseded/'
(no output: nothing describes the removed premise registry)
$ grep -E 'd = 3|d > 3|scope|enters only|Thm27|Theorem 2\.7|block Anderson' <comments>
ScaleFacts.lean:302:All other hypotheses of `scaleFacts_R1` hold for the size data below (`d = 3`, `ilambda ≡ 0`,
Step34Pins.lean:26:* `st_Bctl_pos`, and the size sequence `szB` at `d = 3` in `RBM.Gauss.Step34Inst`.
Step34Pins.lean:558:/-! ## 7. The size sequence `szB` at `d = 3`
Step5Pins.lean:368:`Σ_b (|b|^{d-1}+1)^{-k} < ∞`, true iff `(d-1)k > d`, i.e. `k ≥ 2` at `d = 3` (fails at `d = 2, k = 2`); ...
SizesComp.lean:215:/-- The same for the block Anderson law `(sz.withLam g).seqP`, on the common space `SeqΩ sz`
(+ 3 "enters only through" sentences about parameters `a`, `A = STAII`, `B, ℓ`: no scope claim)
```
`szB` is `def szB : Sizes 3` (Step34Pins.lean:569): accurate. No sentence restricts Theorem 2.7 to `d = 3` (Amend 1 met).

Paper references against `docs/claude-team/tools/paper-labels.tsv` (final paper):
```
$ python3 -I T2538/refs2.py T2538/cmt.txt     # "Kind N.M (`label`)", "Kind N.M `label`", "(N.M) `label`"
number/label pairs: 124 mismatches: 0
$ python3 -I T2538/refs.py                    # colon labels `lem:…`, `eq:…`, `Eq:…`, `MR:…` cited
colon-labels cited: 95  not in final labels: 3
   eq:Exp(L-K           <- regex truncation of `eq:Exp(L-K)1`/`(L-K)2`: in tsv as 6.3 / 6.4
   lem:STOeq_*          <- wildcard for `lem:STOeq_NQ`/`_Qt`/`_Qt_nonzero` (tsv 4.6 / 4.10 / 4.14)
   lem:STOeq_Qt(_nonzero)  <- same family, written with an optional suffix
```

Process vocabulary outside the ticket grep (rule 1 word list), comment text only:
```
$ grep -niE '\b(stage|sub-?stage|wave|route|landing|stop line|no longer|renamed|primed|merged)\b|[0-9a-f]{7,40}' <comments>
Step6Pins.lean:157: ... kept as in the paper).  Route (as in RBM2D):
TailtoTail.lean:22:Route (the Neumann step is done by a weighted row-sum bound instead of the pointwise bound
TailtoTailSq.lean:31:Route: the helpers of `Induction/TailtoTail.lean` (copied with the prefix `tailtoTailSq_`)
(no stage/wave/landing/renamed/primed/merged, no commit hashes; "row" occurs only as "row sum(s)" of matrices)
```
RBM1D/RBM2D mentions name declarations only (`RBM2D's \`s1_gMax_le\``, `RBM1D \`stepZC\``), no file:line, no commit.

## 5. Build, check file, axioms (audit worktree)
```
$ lake build        # full library, started Sat Oct 17 11:47:45 UTC 2026
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
lake build  10756.48s user 1595.32s system 178% cpu 1:55:12.09 total
exit=0
$ grep -cE '^error' build.log
0
$ grep -E '^(warning|error): RBM3D/Induction/(<28 stems>)' build.log | sed 's/:[0-9]*:[0-9]*:/:/' | sort | uniq -c
   (13 warning kinds, all linter warnings on code: unused variables, `show`, deprecated `Set.mem_setOf_eq`,
    maxHeartbeats comment, unused hypothesis in `ST_PT_of_sections`, and Step34Pins "module doc-string should be the
    first command after the imports"; identical to the list in the prove report)
$ lake env lean docs/tickets/checks/T2538-check.lean; echo "check exit=$?"
check exit=0          (#check output of baThm27L_any, baThm27L_of_ML, baEnd_BUnivL_of_ML, bUniv_holds, UNL32; no errors)
$ lake env lean T2538/axioms.lean   # import RBM3D; #print axioms of the two roots
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Verdict per item

| Item | Result |
|---|---|
| (1) Statements | PASS: no code token changed (stripper 28/28 identical vs `main` and `d0c20cc0`); check file compiles |
| (2) Vacuity / hidden hypotheses / cycles | not applicable: no declaration added or changed |
| (3) Compiled nonempty instances | not applicable: no endpoint theorem in scope; the ticket forbids code changes |
| (4) Build and axioms | PASS: full `lake build` exit 0, axiom audit clean; only the 28 listed files touched |
| (5) Paper deltas | PASS: none expected, none needed (no statement changed) |
| Ticket acceptance greps | PASS: 31 hits, all justified (29 "control", 2 `PinnedDefs`); CJK 0; `grep -L` empty |
| Amend 1 scope sentences | PASS: pattern grep empty; no comment restricts block Anderson results to `d = 3` |
| Final-paper references | PASS: 124 number/label pairs match the final label table; no TeX line references |

**Verdict: PASS.** No dispatcher sign-off needed.

## 7. Observations (no effect on statements, build, axioms or paper-delta coverage)
1. The word "Route" survives in three proof-outline sentences (Step6Pins.lean:157, TailtoTail.lean:22,
   TailtoTailSq.lean:31). Rule 1 lists "route" among words to remove; here it means "outline of the proof", not a
   planning route, and the acceptance grep does not test it. A later comment pass may write "Proof outline".
2. ZeroModeCalc.lean:392 heading "The bridge to `SameSignOutside` ..." and :523 "`SameSignOutside` holds" name an
   identifier with no declaration in `RBM3D/` (pre-existing on `main`, where the docstring also named the absent
   `sameSignOutside_*` lemmas; the branch removed those names but kept this one). Read as the name of the property
   `A ⊇ I_diff(σ)` it is harmless.
3. Step34Pins.lean: `set_option linter.style.longLine false` precedes the module docstring (and appears twice); the
   linter warns. Code line, outside this ticket (also reported by the prover).
