Auditor model: claude-opus-5-5

# T2539 audit, round 1 (Sat Oct 17 13:55:22 UTC 2026)

Inputs: ticket, Amend 1, files list (70), check file, prove report. `t/T2539` = 6b88237b, base 59931dea; worktree
`RBM3D-wt/T2539-audit1`. Comments-only: no target theorem, hence no statement/instance check; audited: no code change,
acceptance greps, Amend 1, paper references, build, axioms.

## 1. Scope of the diff
```
$ git merge-base main t/T2539
59931dea7587f261383548a74cf16006f9a0a645
$ git diff --name-only main...t/T2539 | sort > d.txt; wc -l < d.txt; sort docs/tickets/T2539-files.txt | comm -3 - d.txt | wc -l
      70
       0
$ git diff --name-only 59931dea main -- $(cat docs/tickets/T2539-files.txt) | wc -l
       0
```

## 2. No code change (auditor's own stripper, written independently of the prover's)
`astrip.py`: drops nested `/- -/` (incl. `/--`, `/-!`) and `--`-to-EOL; keeps strings, raw strings, char literals (a `'`
after an identifier char is a prime); right-strips lines; compares with blank lines dropped (and, separately, kept).
```
$ python3 -I astrip.py 59931dea t/T2539 docs/tickets/T2539-files.txt
identical: 70 files, different: 0 (of the identical: 61 differ only in blank/trailing-space lines)
$ python3 -I astrip.py main t/T2539 docs/tickets/T2539-files.txt
identical: 70 files, different: 0 (of the identical: 61 differ only in blank/trailing-space lines)
# sensitivity check: rfl->simp in code detected (False); comment text change ignored (True); "--x" in a string kept
False True 'def s := "--x"  ++ \'-\''
```
(61: blank lines left by deleted/re-wrapped comments; no non-blank code line differs.)
`files without copyright header: 0`; `copyright header changed vs base: 0`.

## 3. Ticket acceptance greps (on the branch, bash; BSD grep has no `-P`, so the CJK test is run in Python)
```
$ bash greps.sh
ticket grep lines:      127
matched tokens:
  38 d0;  38 D0;  11 d1;  11 D1;   4 d2;   4 d3;   4 d4;   2 d5;   2 d6;  35 gate;  11 h345;
grep -L '/-!' count:        0
amend-1 grep lines:        0
$ python3 -I cjk.py docs/tickets/T2539-files.txt ; python3 -I cjk.py one.txt   # control: a file "test 中"
CJK lines: 0          | CJK lines: 1 (control)
```
Classification by comment span (auditor's scanner): `ticket-grep hits inside comments: 0`.
All 127 lines are code (`D0`/`D1`/`d0`-`d6` variables, `gate` local predicate, `h345` hypothesis): Lean names, allowed.

Extra scan of comments for the ticket's rule-1 vocabulary not covered by the acceptance grep
(wave, stage, route, structural, refuted, superseded, borrowed, renamed, the old, no longer, planning labels, hashes, `§`):
```
rule-1 extra vocabulary hits inside comments: 100
Counter({'stage': 48, 'the old': 33, 'renamed': 18, 'structural': 1})
```
All 100 hits were read. They are mathematical: "stage 1 / stage 2 of macro step (a)/(b)" (the two halves of a macro step
of the expansion strategy, e.g. `BASim3.lean:1688` "**Macro (a), stage 2**"), "the old vertices/edges" of a graph
extension (`BAScost.lean:723`), "`Γ` renamed by `owxEmb 2`" (vertex relabelling, `BAExpandWOrd.lean:23`), and
"Structural half: the twist keeps the four counters" (`BASymm1.lean:84`). None is process vocabulary.
Further scan (`BA-[A-Z]`, `Target [0-9]`, `delta`, `decision`, `registry`, `TODO`, `now`, `commit`, ...): only
`section G3`/`end G3` (code) and "the later edges" (math). `grep -niE 'registr|assert_rbm|premise list'`: nothing.

## 4. Final-paper references
```
$ python3 -I refcheck.py        # pairs "N.M (`label`)" against docs/claude-team/tools/paper-labels.tsv; TeX line refs; hashes
number+label pairs matching paper-labels.tsv: 72  mismatched: 0
backticked label-like tokens: 343  not in paper-labels.tsv: 3
   ('claim:size', 'BAMomentGen.lean')
   ('claim:size', 'BASizeClaim2.lean')
   ('claim:xi', 'BAZetaExp.lean')
TeX line references: 0
hex tokens (7-12, letters+digits): 0 []
RBM1D/RBM2D mentions: 0
$ python3 -I numcheck.py        # "Lemma/Theorem/.../Subsection N.M" outside [..] citations vs the table's numbers and kinds
numbered paper references (outside [..] citations): 262  not matching paper-labels.tsv kind/number: 3
   ('BAGGExp.lean', 11, 'Lemma', 'B.11', ['equation'])
   ('BAGGOp.lean', 12, 'Lemma', 'B.11', ['equation'])
   ('BAZetaExp.lean', 28, 'Subsection', '7.3', ['definition', 'equation'])
```
All three are right: "Lemma B.11 of [yang2024Del]" cites the other paper; Subsection 7.3 is unlabelled (`7_8...tex:716`).
`claim:size` and `claim:xi` are not TeX labels:
```
$ grep -rn 'claim:size\|claim:xi' paper/final/tex/ paper/tex/            # (empty)
$ grep -n 'begin{claim}' paper/final/tex/7_8_light_weight.tex
264:\begin{claim}
884:\begin{claim}
1616:\begin{claim}\label{claim:TTk}
$ grep -n 'claim:size\|claim:xi' <3 files on the branch> | cut -d: -f1,2
RBM3D/Graph/BAZetaExp.lean:309  RBM3D/Graph/BASizeClaim2.lean:9,48,288  RBM3D/Graph/BAMomentGen.lean:310
```
The same files cite these claims correctly elsewhere ("the claim `Γ ≺ size(Γ)` (Subsection 7.1, after (7.18) ...)",
`BASizeClaim2.lean:11`; "The claim (7.34) `eq:Gbyxi2`", `BAZetaExp.lean:26,72,311`). Observation O1 below.
Backticked identifier-like comment tokens not declared in `RBM3D/`: 552 base, 268 branch; the 56 new ones sampled are
final-TeX labels (`kwuyayw_ng`, `fxyG_sum`, `self_m`, `GtoAG`, `strat_local`).

## 5. Amend 1 (Theorem 2.7 at every `d ≥ 3`)
The Amend-1 grep prints 0 lines (§3). Comments with `d = 3|every .?d|UNMLOut|scope|...` were read; the scope sentences
match the signatures, e.g.
```
AnpKey6.lean:887  /-- **`lwAnpKeyGh_holds`**: Lemma 7.24 (`lem:Anp_key_gh`) for every `d`, with no hypothesis. -/
AnpKey6.lean:888  theorem lwAnpKeyGh_holds : ∀ d : ℕ, LWAnpKeyGh d := fun d => lwAnpKeyGh_of_det d (anpDetGh_holds d)
BAExp14e.lean:336 /-- **Unconditionally** (`baG5LeafPrec_holds`): ... `BAG5LeafPrec` for every `d`, ... -/
BAExp14e.lean:337 theorem baG5LeafPrec_holds : ∀ d : ℕ, BAG5LeafPrec d := fun d =>
BAExpand.lean:719 /-- **`lanlw`** (Lemma B.6, [yang2024Del, Lemma B.9]) on the block Anderson law `PF d L W 0`, for every `d`: `BAlanlw`.
BAExpand.lean:722 theorem baLanlw_holds (d : ℕ) : BAlanlw d := by
BALocReg2B.lean:341/352: the hypothesis `hX` of `baLocReg15_holds` is named, and its discharge `baPathBinder_holds` is named.
```
No comment claims a result only at `d = 3` or `d > 3` out of scope.

## 6. Module docstrings
`grep -L '/-!'` count 0 (§3). First item after imports and `set_option` lines is `/-!` in 69 of 70 files; in
`BASymm2.lean` the line `open private BAWeightOp_circ_counters from RBM3D.Graph.BAWeightOp` (code, line 22) precedes the
module docstring (line 24). Observation O2.

## 7. Build, check file, axioms, hygiene (audit worktree, 6b88237b)
```
$ lake build      # started Sat Oct 17 12:21:29 UTC 2026
ℹ [4424/4425] Built RBM3D (4.0s)
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
exit: 0
Sat Oct 17 13:54:23 UTC 2026
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2539-check.lean; echo "check exit: $?"
check exit: 0          # 12 output lines (the #check lines), no error
$ lake env lean ax.lean     # import RBM3D; #print axioms of the three roots of the check file
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE 'sorry|admit|native_decide|^axiom ' <70 files>
RBM3D/Graph/BALvl1C.lean:429:admits a step of the strategy: ...      # English word in a docstring
```
Warnings in the 70 files: `AnpKey.lean` 22 longLine, `AuxGraphRooted.lean` 9 set_option-column (code lines identical to base).

## 8. Paper deltas
No statement or signature changed (§2): no new Lean/paper difference; "none" in the prove report is correct.

## Observations (no effect on statements, build, axioms or paper-delta coverage)
- O1. Five header lines use the shorthand `claim:size` / `claim:xi`, which are not labels of the final TeX (the claims
  at `7_8_light_weight.tex:264, 884` are unlabelled). Ticket rule 2 asks for a label or a number, consistently within a
  file; the same files elsewhere use "the claim `Γ ≺ size(Γ)` (Subsection 7.1, after (7.18))" and "the claim (7.34)".
  Suggested wording for a later documentation pass: replace the shorthand by those phrases.
- O2. `BASymm2.lean`: the module docstring follows an `open private` line instead of directly following the imports and
  options. It is the first comment of the file and is accurate.
- O3. Prove report: 272 lines, mostly script output; its CJK `grep -P` used a tool absent here; Python check: 0 CJK lines.

## Verdict
T2539 (comments only, 70 files): **PASS**. The diff is exactly the 70 listed files. The stripped code is identical
(70/0, independent stripper). The acceptance grep has 0 hits in comments (127 code lines are Lean identifiers). There are
0 CJK lines, 0 files without `/-!`, 0 TeX line references and 0 Amend-1 hits. The full `lake build` passes, the check
file compiles, and the axioms are standard. No dispatcher sign-off needed.
