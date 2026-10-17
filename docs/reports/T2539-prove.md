Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 09:50:52 UTC 2026

(i) no exponents.

(ii) not applicable.

Verdict: PASS (comments-only ticket; no mathematics, no exponent, no hypothesis).

## (b) Script output
### b1. Branch and scope (base 59931dea is the main the branch was cut from)
```
$ git log --oneline 59931dea..t/T2539
6b88237b T2539: comments of Graph/ A-B, line lengths (documentation only)
3f8fe692 T2539: comments of Graph/ A-B, part 3 (documentation only)
4b07ef07 T2539: comments of Graph/ A-B, part 2 (documentation only)
bd34653f T2539: comments of Graph/ A-B, part 1 (documentation only)
$ git diff --shortstat 59931dea t/T2539
 70 files changed, 2251 insertions(+), 2742 deletions(-)
$ git diff --name-only 59931dea t/T2539 | sort | comm -23 - <(sort docs/tickets/T2539-files.txt) | wc -l
0
$ git diff --name-only 59931dea main -- $(cat docs/tickets/T2539-files.txt) | wc -l   # main has moved on; none of the 70 files
0
```
### b2. Comment-stripping script and comparison
```python
# strip.py
#!/usr/bin/env python3
"""Comment-stripping script for Lean 4 source (T2539 acceptance).

strip(src) removes, from Lean source text:
  - nested block comments  /- ... -/  (including doc comments /-- ... -/ and module docs /-! ... -/),
  - line comments  -- ... end of line,
while keeping string literals ("...", with escapes; raw strings r"..." / r#"..."#) and character
literals ('a', '\\n', '\\x41', '\\u{1F600}') intact.  A quote that follows an identifier character is
an identifier prime (x'), not a character literal.  After removal, trailing whitespace is stripped
from each line and lines that are empty are dropped, so that moving, deleting or re-wrapping a
comment gives identical output, while every code token and all whitespace inside code lines stay.

Usage:
  strip.py FILE            print stripped text of FILE
(compare.py imports strip() and compares two git revisions of every listed file.)
"""
import sys, re, os, subprocess

IDCH = re.compile(r"[A-Za-z0-9_'!?Ͱ-Ͽἀ-῿₀-₟ᴀ-ᶿ℀-⅏]")

def comment_spans(s):
    """Return list of (start, end) offsets of comments in s (end exclusive)."""
    n = len(s); i = 0; spans = []
    while i < n:
        c = s[i]
        if c == '"':
            # raw string handled below; ordinary string
            i += 1
            while i < n and s[i] != '"':
                if s[i] == '\\':
                    i += 2
                else:
                    i += 1
            i += 1
            continue
        if c == 'r' and i + 1 < n and s[i+1] in '"#' and (i == 0 or not IDCH.match(s[i-1])):
            j = i + 1; h = 0
            while j < n and s[j] == '#':
                h += 1; j += 1
            if j < n and s[j] == '"':
                close = '"' + '#' * h
                k = s.find(close, j + 1)
                if k < 0:
                    raise ValueError('unterminated raw string')
                i = k + len(close)
                continue
        if c == "'":
            if i > 0 and IDCH.match(s[i-1]):
                i += 1; continue
            m = re.match(r"'(\\x[0-9a-fA-F]{2}|\\u\{[0-9a-fA-F]+\}|\\.|[^\\'\n])'", s[i:i+14])
            if m:
                i += m.end(); continue
            i += 1; continue
        if c == '-' and i + 1 < n and s[i+1] == '-':
            j = s.find('\n', i)
            if j < 0: j = n
            spans.append((i, j))
            i = j
            continue
        if c == '/' and i + 1 < n and s[i+1] == '-':
            depth = 1; j = i + 2
            while j < n and depth > 0:
                if s.startswith('/-', j):
                    depth += 1; j += 2
                elif s.startswith('-/', j):
                    depth -= 1; j += 2
                else:
                    j += 1
            if depth != 0:
                raise ValueError('unterminated block comment at offset %d' % i)
            spans.append((i, j))
            i = j
            continue
        i += 1
    return spans

def strip(s):
    spans = comment_spans(s)
    out = []; last = 0
    for a, b in spans:
        out.append(s[last:a]); last = b
    out.append(s[last:])
    t = ''.join(out)
    lines = [ln.rstrip() for ln in t.split('\n')]
    return '\n'.join(ln for ln in lines if ln != '') + '\n'

if __name__ == '__main__':
    if len(sys.argv) == 2:
        sys.stdout.write(strip(open(sys.argv[1], encoding='utf-8').read()))
```
```python
# compare.py  (usage: compare.py <dir of strip.py> <rev A> <rev B> <file list>)
import sys, subprocess
sys.path.insert(0, sys.argv[1])
from strip import strip
A, B, listfile = sys.argv[2], sys.argv[3], sys.argv[4]
def show(rev, f):
    return subprocess.run(['git', 'show', rev + ':' + f], capture_output=True, text=True, encoding='utf-8', check=True).stdout
same = diff = 0
for f in open(listfile).read().split():
    if strip(show(A, f)) == strip(show(B, f)): same += 1
    else: diff += 1; print('DIFF', f)
print(f'identical: {same} files / different: {diff}')
```
```
$ python3 compare.py <dir> 59931dea t/T2539 docs/tickets/T2539-files.txt
identical: 70 files / different: 0
$ python3 compare.py <dir> main t/T2539 docs/tickets/T2539-files.txt
identical: 70 files / different: 0
```
### b3. Ticket grep and the classification of its hits
```
# tgrep.sh (the ticket's command)
grep -rnEi 'T2[0-9]{3}|DECISIONS|paper-delta|\bD[0-9]{1,3}\b|\b(1_2|3_5|6|7_8|A|B):[0-9]+|ticket|prover|auditor|preflight|dispatcher|supervisor|\bhub\b|frozen|pinned|\bpin\b|\bamend|rework|\bprobe\b|\bgate\b|\bowed\b|\bREQ\b|\bH[0-9]{3}\b|CLAUDE\.md|HANDOVER|CONTROL|RBM[12]D/[^ ]*:[0-9]|sub-stage|successor|census' $(cat docs/tickets/T2539-files.txt)
```
```
$ bash baseloop.sh   # the same pattern, counted line by line on `git show 59931dea:$f` over the 70 files
matching lines at base 59931dea: 971
$ bash tgrep.sh | wc -l   # on t/T2539
127
```
```python
# chits.py: the same pattern; each hit is placed inside or outside a comment span
import sys,re
sys.path.insert(0,'/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d6ebe5cd-b9c4-4c2a-9b3c-fa912982a931/scratchpad/T2539')
from strip import comment_spans
root='/Users/junyin/Lean_proof/RBM3D-wt/T2539'
pat=re.compile(r'T2[0-9]{3}|DECISIONS|paper-delta|\bD[0-9]{1,3}\b|\b(1_2|3_5|6|7_8|A|B):[0-9]+|ticket|prover|auditor|preflight|dispatcher|supervisor|\bhub\b|frozen|pinned|\bpin\b|\bamend|rework|\bprobe\b|\bgate\b|\bowed\b|\bREQ\b|\bH[0-9]{3}\b|CLAUDE\.md|HANDOVER|CONTROL|RBM[12]D/[^ ]*:[0-9]|sub-stage|successor|census', re.I)
files=[l.strip() for l in open(root+'/docs/tickets/T2539-files.txt') if l.strip()]
tot=0; code=0
for f in files:
    s=open(root+'/'+f,encoding='utf-8').read()
    spans=comment_spans(s)
    import bisect
    starts=[a for a,b in spans]
    pos=0
    for ln,line in enumerate(s.split('\n'),1):
        for m in pat.finditer(line):
            p=pos+m.start()
            i=bisect.bisect_right(starts,p)-1
            inc = i>=0 and spans[i][0]<=p<spans[i][1]
            if inc: tot+=1; print(f.split('/')[-1],ln,m.group(0),'|',line.strip()[:140])
            else: code+=1
        pos+=len(line)+1
print('comment hits',tot,'code hits',code,file=sys.stderr)
```
```
$ python3 chits.py | tail -1   # hits inside comments go to stdout; the totals go to stderr
comment hits 0 code hits 160
$ bash tgrep.sh | python3 tokens.py   # the matches (160) on the 127 lines, all in code, with the files
D0 38 ['BAMomentExpGenB.lean', 'BAMomentGen.lean', 'BAProv.lean']
D1 11 ['BAProv.lean']
d0 38 ['BASim.lean']
d1 11 ['BAExp14aB.lean', 'BAExp14b2B.lean', 'BAGGOp.lean', 'BASim.lean']
d2 4 ['BAExp14aB.lean', 'BAExp14b2B.lean']
d3 4 ['BAExp14aB.lean', 'BAExp14b2B.lean']
d4 4 ['BAExp14aB.lean', 'BAExp14b2B.lean']
d5 2 ['BAExp14b2B.lean']
d6 2 ['BAExp14b2B.lean']
gate 35 ['BAMomentExpGen.lean', 'BASizeClaim.lean']
h345 11 ['BALocReg1B.lean', 'BAMomentExpGenB.lean', 'BAMomentGen.lean', 'BAMomentGenB.lean']
```
### b4. Other greps and warnings
```
$ grep -rnP '[\x{4e00}-\x{9fff}]' $(cat docs/tickets/T2539-files.txt); echo "exit: $?"   # then the same grep on a control file with one CJK character
exit: 1
control file: 1:test 中
$ grep -L '/-!' $(cat docs/tickets/T2539-files.txt) | wc -l
0
$ grep -nE 'D723|decision B|§316|only (for|at) .?d = 3|d = 3 only|out of scope' $(cat docs/tickets/T2539-files.txt) | wc -l
0
$ line-length warnings of the build log, files of the list only (uniq -c)
  22 AnpKey
$ lines over 100 characters in AnpKey.lean, base and branch
59931dea: 26
t/T2539: 22
```
### b5. Build, check file, axioms
```
$ lake build   # in the worktree at 6b88237b, started 10:46:19 UTC; last lines of the log
ℹ [4424/4425] Built RBM3D (8.3s)
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
lake build  5508.17s user 617.63s system 115% cpu 1:28:08.11 total
exit: 0
Sat Oct 17 12:14:27 UTC 2026
$ lake env lean docs/tickets/checks/T2539-check.lean; echo "exit: $?"
RBM.BA.baThm27L_any : ∀ (d : ℕ),
  3 ≤ d →
    (RBM.BA.STStep5IIIgL d (fun sz => (sz.withLam 0).seqP) (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => RBM.BA.baFMz sz z) fun sz z => RBM.BA.BAflowT0 sz z) →
      RBM.Univ.UNL32 → RBM.BA.BAThm27L d
RBM.BA.baThm27L_of_ML : ∀ (d : ℕ), 3 ≤ d → RBM.Univ.UNL32 → RBM.Univ.UNMLOutBA d → RBM.BA.BAThm27L d
RBM.BA.baEnd_BUnivL_of_ML : ∀ (d : ℕ), 3 ≤ d → RBM.Univ.UNL32 → RBM.Univ.UNMLOutBA d → RBM.BA.BAEnd_BUnivL d
RBM.Endpoints.bUniv_holds : RBM.Univ.UNNormBandRow →
  RBM.Univ.UNL32 →
    (∀ (d : ℕ), RBM.Univ.UNMLOut d) →
      RBM.Univ.UNLocAvgBand → RBM.Univ.UNQueBand → RBM.Univ.UNGUESchurTail → RBM.Univ.UNBUniv
RBM.Univ.UNL32 : Prop
exit: 0
$ lake env lean ax.lean   # ax.lean: import RBM3D, then #print axioms of the three roots of the check file
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b6. Name clash
No declaration is added or renamed: the stripped sources are identical on all 70 files (b2), so the declared names and every code token are unchanged.  No Mathlib name is used.
## Narrative
Scope: the 70 files of `docs/tickets/T2539-files.txt` (`RBM3D/Graph/`, names A-B); only comments and docstrings changed.
No file outside the list changed relative to the branch base (b1), and no code token changed (b2: stripped output identical, 70 files / 0 different).

What was rewritten (line counts of the diff are in b1):
- Every module docstring and every declaration or section docstring: ticket numbers, DECISIONS, planning labels, role names, history
  narration and RBM1D/RBM2D file:line and hash citations removed; TeX line references replaced by label and number of the final
  paper (translation through `docs/claude-team/tools/paper-labels.tsv`).
- Every file starts with a `/-!` module docstring (b4: `grep -L` count 0).  `BAProvB.lean` had none at the base: its first `/-!` was the
  section header `## 1.` at line 31.
- Where a docstring listed declarations, sections or compiled instances that are no longer in the file, it was rewritten to match the
  declarations that are present.  A script listed the backticked names of comments that are not declared or structure fields in
  `RBM3D/**`; the remaining ones were reviewed and are paper labels, local variable names, name prefixes or suffixes, or Lean names.
- Scope sentences (Amend 1) say what each declaration states (for example `lwAnpKeyGh_holds : ∀ d, LWAnpKeyGh d`, whose statement
  carries `3 ≤ d →`); the grep for the retired scope wording (b4) finds 0 lines.  Citations of the cited work are those the paper
  itself makes (`[yang2024Del, Lemma B.9]` to `B.11` in `B_graphical_lemmas.tex`).

Ticket grep (b3): 971 matching lines at the base, 127 on the branch.  Comment hits: 0 (`chits.py`: 160 matches, all in code).  The 127 lines are code: the Lean identifiers
`D0`/`D1` (data variables of `BAMomentExpGenB`, `BAMomentGen`, `BAProv`), `d0`-`d6` (local names in `BASim`, `BAExp14aB`, `BAExp14b2B`,
`BAGGOp`), `gate` (local predicate in `BAMomentExpGen`, `BASizeClaim`) and `h345` (hypothesis names for `LocReg345`).  They cannot be
changed in a comments-only ticket.  In comments the terms `d1`-`d4` of `ggSplit` are written `d₁`-`d₄` and `D1`, `D2` of `BAExp14b` as
`D₁`, `D₂`; one use of the word `gate` in a docstring (`BAMomentExpGen_exists_forest`) was rephrased.

Build and warnings: the full `lake build` finishes with exit 0 (4425 jobs, the axiom audit line is in b5); the check file compiles with
exit 0.  The only line-length warnings in the 70 files are the 22 of `AnpKey.lean` (26 lines over 100 characters at the base, the
file has no `set_option linter.style.longLine false`); see b4.
## (c) Verified Mathlib names
None: comments only; no Mathlib name was used, added or checked.
## (d) Open issues and paper-delta candidates
1. Observation outside the ticket scope: `RBM3D/BA/TwistFold2B.lean` (not in the file list) mentions `twFold2PrecDet` and `twFold2PrecDet_holds` in comments, but no declaration of that name exists (grep below).  The comments of this ticket's files that cited them now cite `twFold2Prec` and `twFold2Prec_holds`, which exist.
```
$ grep -rn 'twFold2PrecDet' RBM3D --include='*.lean' | cut -c1-110
RBM3D/BA/TwistFold2B.lean:20:* `twFold2Prec`, `twFold2PrecDet` and their `_holds` theorems: for a deterministi
RBM3D/BA/TwistFold2B.lean:973:-- Target 7′ (`twFold2PrecDet`) at `d = 3`, `sz0`, `zSeq`, `t ≡ 1/2` for the roo
```
2. Paper-delta candidates: none (no statement, hypothesis or signature changed).
3. Mathematical observations: none noticed while reading.
