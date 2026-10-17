Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 09:03:55 UTC 2026

(i) no exponents; (ii) not applicable; PASS

## (b) Script output

Branch `t/T2538`, commit `ea3537e4` (parent `d0c20cc0`, the merge-base with `main`; `main` has not touched the 28 files since).
Report written: Sat Oct 17 11:44:36 UTC 2026

### Full build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2538, started Sat Oct 17 10:12:36 UTC 2026)
```
$ lake build   # tail of the log
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
lake build  10301.65s user 1229.65s system 235% cpu 1:21:45.44 total
$ grep -c "error" fullbuild.log   # lines containing the word error
0
$ grep -E "^(warning|error):" fullbuild.log | grep <the 28 files> | sed "s/:[0-9]*:[0-9]*:/:/" | sort | uniq -c | sort -rn
   5 warning: RBM3D/Induction/Step2Iterate.lean: Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in
   4 warning: RBM3D/Induction/Step2Events.lean: Variable name `κ` is not explicitly referenced.
   2 warning: RBM3D/Induction/Step2Iterate.lean: Variable name `hst` is not explicitly referenced.
   2 warning: RBM3D/Induction/Step2Iterate.lean: Variable name `hd` is not explicitly referenced.
   2 warning: RBM3D/Induction/Step2Iterate.lean: The `show` tactic should only be used to indicate intermediate goal states for readability.
   2 warning: RBM3D/Induction/Step2Events.lean: The `show` tactic should only be used to indicate intermediate goal states for readability.
   2 warning: RBM3D/Induction/Step2Events.lean: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
   1 warning: RBM3D/Induction/Step34Pins.lean: The module doc-string for a file should be the first command after the imports.
   1 warning: RBM3D/Induction/Step2Iterate.lean: Variable name `u` is not explicitly referenced.
   1 warning: RBM3D/Induction/Step2Iterate.lean: Variable name `n` is not explicitly referenced.
   1 warning: RBM3D/Induction/Step2Iterate.lean: Variable name `hsu` is not explicitly referenced.
   1 warning: RBM3D/Induction/Step2Iterate.lean: Variable name `hq0` is not explicitly referenced.
   1 warning: RBM3D/Induction/Step2Core.lean: `ST_PT_of_sections` does not use the following hypothesis in its type:
```
### Check file and axioms of the roots (no declaration is new, so there are no new axioms to print)
```
$ lake env lean docs/tickets/checks/T2538-check.lean   # exit 0
$ lake env lean axioms.lean   # import RBM3D; #print axioms of the two roots
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### Comment-stripping script (nested `/- -/`, `/-- -/`, `/-! -/`, `--`, string and char literals; `«»` names) and its summary
Stripped text = code segments only, with trailing blanks and empty lines removed; compared with `git show <base>:<file>`.
```python
# lex.py
import re
IDCH = re.compile(r"[A-Za-z0-9_'!?À-ɏͰ-Ͽᴀ-ᶿ₀-ₜ⁰-₟ᵢ-ᵪ]")
def segments(t):
    """Return list of (kind,start,end): kind in code,line,block."""
    segs = []
    n = len(t)
    i = 0
    cs = 0  # code start
    def flush(upto):
        nonlocal cs
        if upto > cs:
            segs.append(('code', cs, upto))
    while i < n:
        c = t[i]
        if c == '-' and t.startswith('--', i):
            flush(i)
            j = t.find('\n', i)
            if j < 0: j = n
            segs.append(('line', i, j))
            i = j; cs = i
            continue
        if c == '/' and t.startswith('/-', i):
            flush(i)
            depth = 1; j = i + 2
            while depth > 0:
                if j >= n:
                    raise ValueError('unterminated block comment at %d' % i)
                if t.startswith('/-', j):
                    depth += 1; j += 2
                elif t.startswith('-/', j):
                    depth -= 1; j += 2
                else:
                    j += 1
            segs.append(('block', i, j))
            i = j; cs = i
            continue
        if c == '"':
            j = i + 1
            while j < n and t[j] != '"':
                if t[j] == '\\': j += 2
                else: j += 1
            i = j + 1
            continue
        if c == '«':
            j = t.find('»', i)
            i = j + 1
            continue
        if c == "'":
            prev = t[i-1] if i > 0 else ' '
            if not IDCH.match(prev):
                # char literal?
                m = re.match(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'", t[i:i+12])
                if m:
                    i += m.end()
                    continue
        i += 1
    flush(n)
    return segs

def strip(t):
    out = []
    for k, a, b in segments(t):
        if k == 'code':
            out.append(t[a:b])
    s = ''.join(out)
    lines = [l.rstrip() for l in s.split('\n')]
    return '\n'.join(l for l in lines if l)
# strip.py
import sys, subprocess, hashlib
sys.path.insert(0, '.')
from lex import strip
files = [l.strip() for l in open('/Users/junyin/Lean_proof/RBM3D/docs/tickets/T2538-files.txt') if l.strip()]
wt = '/Users/junyin/Lean_proof/RBM3D-wt/T2538'
base = sys.argv[1] if len(sys.argv) > 1 else 'main'
same = diff = 0
for f in files:
    old = subprocess.run(['git', '-C', wt, 'show', base + ':' + f], capture_output=True, text=True, check=True).stdout
    new = open(wt + '/' + f, encoding='utf-8').read()
    if strip(old) == strip(new):
        same += 1
    else:
        diff += 1
        print('DIFFERENT:', f)
print('identical: %d files' % same)
print('different: %d' % diff)
```
```
$ python3 strip.py d0c20cc0   # base = merge-base (the same summary for base = main)
identical: 28 files
different: 0
```
### Acceptance greps (branch tree)
```
$ grep -rnEi 'T2[0-9]{3}|DECISIONS|paper-delta|\bD[0-9]{1,3}\b|\b(1_2|3_5|6|7_8|A|B):[0-9]+|ticket|prover|auditor|preflight|dispatcher|supervisor|\bhub\b|frozen|pinned|\bpin\b|\bamend|rework|\bprobe\b|\bgate\b|\bowed\b|\bREQ\b|\bH[0-9]{3}\b|CLAUDE\.md|HANDOVER|CONTROL|RBM[12]D/[^ ]*:[0-9]|sub-stage|successor|census' $(cat docs/tickets/T2538-files.txt) | wc -l
      31
$ (same grep) | grep -vi control
RBM3D/Induction/StepDecompN.lean:72:section PinnedDefs
RBM3D/Induction/StepDecompN.lean:147:end PinnedDefs
$ (same grep) | grep -i control | cut -d: -f1,2     # 29 hits; the pattern is case-insensitive, so it matches the word "control(s)(led)"
ScaleFacts3.lean:87 Split.lean:583 Step2Core.lean:920 Step2Events.lean:42 Step2Events.lean:378 Step2Events.lean:703 Step2Events.lean:1239 
Step2Defs.lean:76 Step2Defs.lean:309 Step2Defs.lean:443 Step3.lean:94 Step2Scale.lean:324 Step2Scale.lean:427 Step2Scale.lean:467 
Step2Iterate.lean:59 Step5Pins.lean:149 Step5Pins.lean:277 Step5Pins.lean:279 Step6Pins.lean:351 Step5Cases.lean:96 Step34Pins.lean:60 
Step34Pins.lean:69 Step34Pins.lean:346 Step34Pins.lean:380 Step34Pins.lean:384 Step34Pins.lean:465 Step34Pins.lean:478 Step5Kit.lean:205 
Step5Kit.lean:354 
$ grep -rnP '[\x{4e00}-\x{9fff}]' $(cat docs/tickets/T2538-files.txt); echo "exit=$?"
exit=1
$ grep -L '/-!' $(cat docs/tickets/T2538-files.txt); echo "exit=$?"
exit=1
$ grep -nE 'D723|decision B|§316|only (for|at) .?d = 3|d = 3 only|out of scope' $(cat docs/tickets/T2538-files.txt); echo "exit=$?"   # Amend 1 pattern
exit=1
$ git diff d0c20cc0 --name-only | sort | diff - <(sort docs/tickets/T2538-files.txt) && echo same
same
$ git diff d0c20cc0 --stat | tail -1
 28 files changed, 1150 insertions(+), 1595 deletions(-)
$ python3 before_after.py   # lexer-based counts: comments, comment lines, lines matching the ticket grep, TeX line references (1_2|3_5|6|7_8|A|B):N
files lines comments commentlines grephitlines texrefs
main    28 20544 1168 3459 665 378
branch  28 20099 1105 3014 29 0
$ grep -c "^example\|^  example" <the 28 files>   # sum over the files
0
```
### Narrative
- Scope: only comments and docstrings of the 28 files of `docs/tickets/T2538-files.txt` changed (+1150/-1595 lines); the comment-stripped files are identical to `d0c20cc0` and to `main`; every copyright header is unchanged (first 5 lines compared with `main` for all 28 files).
- Method: scratch scripts outside the repository (not committed): a lexer (above), a lister that printed every comment with its index, per-file replacement files (full text, substring substitutions, deletions, and a few regex rules for mechanical patterns such as a trailing `:123` or the word "merged"), and an applier that worked from the `main` text of each file by comment position and asserted that the stripped text was unchanged before writing. Comments: 1168 -> 1105, comment lines 3459 -> 3014, lines matching the ticket grep 665 -> 29, TeX line references 378 -> 0 (counts above).
- Paper references: every `1_2:`/`3_5:`/`6:` reference was translated with `texref.py --scan` (378 lines) and the TeX around the line; where the nearest label above was not the cited statement I read the TeX (for example `6:93-152` is the proof of Step 6, `3_5:1575-1595` the proof of `(Eq:LGxb)` in case (ii), `3_5:1366` the bootstrap bound `(am;asoi222)` in Lemma 4.10). Numbers are those of `docs/claude-team/tools/paper-labels.tsv` (looked up per label); labels are those of the final TeX. `5-6:NN` references are to the TeX of the `d = 2` paper and became `[YY_25, §5.1]` or were dropped.
- Removed: ticket, DECISIONS, paper-delta and planning labels; registry classes (owed, borrowed, structural); "pin" as a noun (now "statement" or "hypothesis"); probe and "merged"; RBM1D/RBM2D file:line and commit hashes. Kept: the mathematics, conventions, and the sentences saying that an argument follows the RBM2D/RBM1D formalization, naming at most the declaration. No Lean name changed (`Pins`, `PinnedDefs`, `ST_step2_of_pins`, ... stay).
- Comments about code that the files do not contain were removed, not rewritten. None of the 28 files has an `example` (count above), so the sections headed "Compiled nonempty instances", "Instances at `d = 3`" and their sub-headings were deleted (they described instances that are not in the files). Module docstrings and docstrings that named declarations absent from the whole of `RBM3D/` were corrected (a script looked up every backticked identifier of every comment among the identifiers of the code of `RBM3D/`): `st_EKWin`, `st_split_I/II` (ScaleFacts3); `stNetLift_holds` (Step1); `StochDomAt.of_subset_whp/_compl` (Step1Setup, section 0 deleted); `STStep2Parts`, `ST_step2_concl` (Step2Iterate); `st6_GdecayW_of_zero`, `ST_step6R_mono`, `ST_step6_caseI_of_pins` (Step6Kit); `step5Kernel_profile_holds`, `step5Kernel_calA*`, `step5Kernel_profile_not_unconditional` (Step5Kernel); `Ugen_stepZCN` (StepDecompN); `stSumTwoLoop_exists` (SEforLn2); `ST_model_of_whp_grid` (Step2Events); `STStep3I`, `ST_mainInd_of_pins` (Step3, Step4); `sameSignOutside_*`, `zeroModeOp_UN` (ZeroModeCalc); `STForbidden` (ScaleFacts, now `PerTimeCalc.Unif.forbidden_region`).
- Module docstrings: all 28 files have one (`grep -L` empty), placed after the imports; the process-heavy ones (Step1, Step1Setup, Step2Core, Step2Defs, Step2Events, Step2Iterate, Step34Pins, Step4, Step5Pins, Step6Kit, Step6Pins, StepDecompN, ZeroModeCalc, ...) were rewritten in mathematical terms (contents, differences from `d = 2`, conventions).
- Amend 1: no comment of the 28 files says or implies that block Anderson results hold only at `d = 3` or that `d > 3` is out of scope or depends on a decision (pattern grep above is empty, also on `main` for these files). Remaining `d = 3` in comments: the counterexample data of `scaleFacts_R1` (ScaleFacts section 7), a comparison with `d = 2` (Step5Pins), and the size sequence `szB` (Step34Pins).
- Remaining hits of the ticket grep: 29 are the English word "control"/"controlled" (the paper's control parameters `Ξ`, `Ψ`, `Ĵ`, or "bounded"; the pattern is case-insensitive and contains `CONTROL`), mathematical; 2 are the code token `PinnedDefs` (a `section` name, not changed).
- Build: a build of the 28 modules succeeded (3959 jobs); after further comment edits to Step2Events, SEforLn2, Step34Pins, Step5Pins, Step6Pins and StepDecompN, the final full `lake build` started at 10:12:36 UTC, after the last modification time of any of the 28 files (`TZ=UTC stat`: latest 2026-10-17 10:12:27), and completed with 0 errors and the axiom audit. The warnings in the 28 files concern tactics, unused variables, heartbeat options and the position of the module docstring after the `set_option` line in `Step34Pins.lean` (code, unchanged by this ticket). The check file `docs/tickets/checks/T2538-check.lean` compiles (exit 0); the two roots depend only on `propext`, `Classical.choice`, `Quot.sound`.

## (c) Verified Mathlib names
None used: no code token changed.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none.
- Observation: 90 files outside the 28 contain 266 citations `<file>.lean:<line>` of these 28 files (for example `RBM3D/Graph/LWTermExpN.lean:22` cites `Step2Iterate.lean:1049`, `RBM3D/Path/LemDecCalE.lean:928` cites `Step2Iterate.lean:1198`; command: `grep -rlE "\b(<the 28 stems>)\.lean:[0-9]" RBM3D | grep -v <the 28 files> | wc -l` printed 90). The 445 lines removed here (20,544 -> 20,099) shift these numbers further; those comments belong to the other clean-up tickets.
- Observation: none of the 28 files contains an `example` (count 0 above); CLAUDE.md section 4 step 2 asks for compiled instances of endpoint theorems, and the files no longer carry any. Nothing was added (comments only).
- Observation: `RBM3D/Induction/Step34Pins.lean` has `set_option linter.style.longLine false` before its module docstring (the build warns "The module doc-string for a file should be the first command after the imports"); fixing it needs a code-line move, outside this ticket.
- No mathematical problem noticed while reading.
