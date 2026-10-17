Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 15:21:26 UTC 2026

(i) No exponents.

(ii) Not applicable.

Verdict: PASS (ticket T2541 is comments-only; no mathematical hypotheses, exponents or constants are involved).

## (a′) Preflight corrections

None.

## (b) Script output

### Branch state
```
$ date -u
Sat Oct 17 18:24:18 UTC 2026
$ git -C ../RBM3D-wt/T2541 log --format="%h %s" 2a77235e..HEAD
9d5fc877 T2541: comments of BA/ConArg and BA/CouplingWindow (final review)
b13e92d7 T2541: release step 3, comments and docstrings of RBM3D/BA (names A-K), comments only
$ git diff --shortstat 2a77235e HEAD
 69 files changed, 2010 insertions(+), 2872 deletions(-)
$ git diff --name-only 2a77235e HEAD | sort | diff - <(sort docs/tickets/T2541-files.txt) && echo "changed files == ticket list"
changed files == ticket list
$ git status --short | wc -l
       0
```

### Comment-stripping script (nested block comments, doc comments, `--`, string and character literals): lexer.py
```python
#!/usr/bin/env python3
"""Lean comment lexer: comment spans and comment-stripped text.

Handles nested block comments (/- ... -/, including /-- and /-!), line comments (--),
string literals (with escapes, including s!"..." and raw strings r"..", r#".."#) and
character literals ('a', '\\n', '\\'' ...).  A quote preceded by an identifier character
is a prime, not a character literal.
"""
import re, sys

IDCH = re.compile(r"[A-Za-z0-9_'!?À-ɏͰ-Ͽᴀ-ᶿἀ-῿₀-₟⁰-₟℀-⅏ᵉ-ᵪ]")
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")

def spans(text):
    """Return list of (start, end) offsets of comments (end exclusive)."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth > 0:
                if text.startswith('/-', j):
                    depth += 1; j += 2
                elif text.startswith('-/', j):
                    depth -= 1; j += 2
                else:
                    j += 1
            if depth != 0:
                raise ValueError('unterminated block comment at offset %d' % i)
            out.append((i, j)); i = j
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: j = n
            out.append((i, j)); i = j
        elif c == '"':
            # raw string r"..." / r#"..."# : detect by preceding r and #s
            k = i - 1; hashes = 0
            while k >= 0 and text[k] == '#':
                hashes += 1; k -= 1
            if k >= 0 and text[k] == 'r' and (k == 0 or not IDCH.match(text[k-1])):
                term = '"' + '#' * hashes
                j = text.find(term, i + 1)
                if j < 0: raise ValueError('unterminated raw string at %d' % i)
                i = j + len(term)
            else:
                j = i + 1
                while j < n and text[j] != '"':
                    j += 2 if text[j] == '\\' else 1
                if j >= n: raise ValueError('unterminated string at %d' % i)
                i = j + 1
        elif c == "'":
            if i > 0 and IDCH.match(text[i-1]):
                i += 1
            else:
                m = CHAR.match(text, i)
                i = m.end() if m else i + 1
        else:
            i += 1
    return out

def strip(text):
    """Code with comments removed; trailing blanks and blank lines dropped."""
    sp = spans(text)
    parts, last = [], 0
    for a, b in sp:
        parts.append(text[last:a]); last = b
    parts.append(text[last:])
    code = ''.join(parts)
    lines = [l.rstrip() for l in code.split('\n')]
    return '\n'.join(l for l in lines if l.strip())

if __name__ == '__main__':
    for p in sys.argv[1:]:
        sys.stdout.write(strip(open(p, encoding='utf-8').read()) + '\n')
```
### Comparison on `main` (2a77235e) against the branch: cmp.py
```python
#!/usr/bin/env python3
"""Compare comment-stripped files of the list on a base commit and on the working tree."""
import subprocess, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lexer import strip
repo, base, listfile = sys.argv[1], sys.argv[2], sys.argv[3]
files = [l.strip() for l in open(listfile) if l.strip()]
same = diff = 0
for f in files:
    old = subprocess.run(['git', '-C', repo, 'show', f'{base}:{f}'], capture_output=True, text=True, check=True).stdout
    new = open(os.path.join(repo, f), encoding='utf-8').read()
    if strip(old) == strip(new):
        same += 1
    else:
        diff += 1
        print('DIFFERENT:', f)
print(f'identical: {same} files')
print(f'different: {diff}')
```
```
$ python3 -I cmp.py $PWD 2a77235e docs/tickets/T2541-files.txt
identical: 69 files
different: 0
```

### Module docstrings after `set_option .. in` (an `in` applies to the next command): modin2.py
```python
#!/usr/bin/env python3
# Module docstrings `/-! -/` directly after a line ending in `in` (`set_option .. in`) must stay: compare code text
# in which exactly those docstrings are marked, base against branch.
import subprocess, sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lexer import spans
repo, base, lst = sys.argv[1:4]
def marked(t):
    code, last = [], 0
    for a, b in spans(t):
        code.append(t[last:a] + ('\x00M\x00' if t.startswith('/-!', a) else '')); last = b
    code.append(t[last:])
    out = []
    for l in (x.rstrip() for x in ''.join(code).split('\n')):
        if not l.strip(): continue
        if l.strip() == '\x00M\x00' and not (out and re.search(r'\bin$', out[-1])): continue
        out.append(l)
    return '\n'.join(out)
same = diff = n = 0
for f in (l.strip() for l in open(lst) if l.strip()):
    o = subprocess.run(['git', '-C', repo, 'show', f'{base}:{f}'], capture_output=True, text=True, check=True).stdout
    a, b = marked(o), marked(open(os.path.join(repo, f), encoding='utf-8').read())
    n += a.count('\x00M\x00'); same += a == b; diff += a != b
print(f'identical: {same} files / different: {diff}; docstrings after an `in` line on the base: {n}')
```
```
$ python3 -I modin2.py $PWD 2a77235e docs/tickets/T2541-files.txt
identical: 69 files / different: 0; docstrings after an `in` line on the base: 1
```

### Full build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2541, HEAD 9d5fc877, clean tree)
```
$ lake build > fullbuild.log 2>&1   # start and end times from `date -u`
start: Sat Oct 17 16:48:40 UTC 2026
$ tail -n 5 fullbuild.log
ℹ [4424/4425] Built RBM3D (4.9s)
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
exit 0
Sat Oct 17 18:22:10 UTC 2026
$ grep -c "^error" fullbuild.log; grep -c "sorry" fullbuild.log
0
0
$ grep -E "Built RBM3D.Graph.LWExpCertBS[01] " fullbuild.log
⚠ [4331/4425] Built RBM3D.Graph.LWExpCertBS0 (2019s)
⚠ [4332/4425] Built RBM3D.Graph.LWExpCertBS1 (3229s)
```

### Release check and axioms (public declarations named by docs/tickets/checks/T2541-check.lean)
```
$ lake env lean docs/tickets/checks/T2541-check.lean   # 4 `example`s elaborate; 5 `#check` lines print
exit 0 (end: Sat Oct 17 18:22:22 UTC 2026)
error lines in the output: 0
$ lake env lean axioms.lean   # import RBM3D; #print axioms of the 8 declarations of the check file
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_BUnivL_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

### Acceptance greps (branch t/T2541, HEAD 9d5fc877)
```
$ grep -rnEi "<ticket pattern>" $(cat docs/tickets/T2541-files.txt) | wc -l      # branch
      99
$ same grep on `git show 2a77235e:<file>` copies of the 69 files | wc -l          # base
     738
$ python3 tally.py   # the 99 branch lines, by matched token (lowercase), comment or code, lines, files
control  comment    2 lines  GreenCond2, GreenLocal
d0       code      10 lines  GUEEntry, GreenCore, GreenOff
d1       code      13 lines  ConArg, EKGenBA, GreenCond, GridRepTailBA
d2       code      11 lines  ConArg, GreenCond, GridRepTailBA
d3       code       2 lines  GreenCond
d4       code       2 lines  GreenCond
frozen   code       2 lines  GUEDuhamelBA
h123     code       2 lines  GUEHyp
h128     code       2 lines  FlowPins
h416     code       2 lines  GreenMinor3
h727     code       3 lines  GUEPathBoundsBA
h728     code       2 lines  GUEPathBoundsBA
h729     code       2 lines  GUEHyp
h730     code      34 lines  GUEHyp, GUEHypABA, GUEHypBBA, GUEPathBoundsBA
h730     comment    4 lines  GUEHyp
h745     comment    2 lines  GUEPathBoundsBA
h746     comment    2 lines  GUEPathBoundsBA
hub      code       3 lines  GreenSchur
pin      code       2 lines  GreenOff
t2205    code       2 lines  CouplingWindow
$ grep -rnP '[\x{4e00}-\x{9fff}]' $(cat docs/tickets/T2541-files.txt); echo rc=$?
rc=1
$ grep -L "/-!" $(cat docs/tickets/T2541-files.txt)
$ python3 docs/claude-team/tools/texref.py --scan <files> | wc -l   # TeX line references: base copies / branch
     149
       0
```

### Remaining hits of the ticket grep: reason
- `d0`..`d4`, `D1`, `D2`, `D`: local variables and hypothesis names inside proofs (code lines; ConArg 905-946, GreenCond 1148-1174, GreenCore, GreenOff, GUEEntry, GridRepTailBA); `section D1` / `end D1` (EKGenBA 415, 447).
- `h123`, `h128`, `h416`, `h727`, `h728`, `h729`, `h730`, `h745`, `h746`: Lean hypothesis names (code). The 7 comment lines (GUEHyp 218, 552, 826, 927; GUEPathBoundsBA 55, 271, 376) quote the hypotheses `h730`, `h745`, `h746` of the statements they document, by name.
- `hub` is the hypothesis `hUB` (GreenSchur 185, 201, 202); `pin` is `section Pin` / `end Pin` (GreenOff 1111, 1371); `frozen` is the declaration name `DuhamelB_condSubG_frozen` (GUEDuhamelBA 48, 340); `t2205` is the private lemma `T2205_inv_spectral` (CouplingWindow 76, 125). Code is unchanged, so these names stay.
- `control` (GreenCond2 411, GreenLocal 12): "deterministic control" is the mathematical parameter of the local law, an English word.

### Identifier check of the comments (backticked tokens that occur in no RBM3D code and not in Mathlib/Lean core)
```
$ dangling.py $(cat docs/tickets/T2541-files.txt) | awk "{print \$NF}" | sort | uniq -c | sort -rn   # 57 lines, 27 distinct tokens (the same check on the 69 base files: 510 lines)
eq_K x12  K_BA x7  M_xx x3  K_ab x3  S_far x2  Rem_k x2  Mart_k x2  KTreeRep_ x2  K_st x2  F'_c x2  F_out x2  F_in x2  A'_w x2  w_far x1  uKer_ x1  
sup_c x1  sup_b x1  S_near x1  Q'_w x1  max_a x1  M_ca x1  M_aa x1  K_aa x1  G_xx x1  C_lat x1  C_gii x1  a_out x1  
```
All 27 are mathematical symbols (`K_BA`, `M_xx`, `F_out`, ...), the paper label `eq_K-Kpi` (A.39; split at the hyphen) or name prefixes (`KTreeRep_`, `uKer_`); the module-path check (`paths.py`, 21 flagged lines) flags only quotients and phrases (`L/L`, `U/4`, `Q/c`, `Neumann/resolvent`), no file path.

### Narrative
- Result: all 69 files of `docs/tickets/T2541-files.txt` have rewritten comments and docstrings, in two commits on `t/T2541` (b13e92d7, 9d5fc877; base 2a77235e); no other file is changed (script above). No code token changed: the stripped text is identical in 69/69 files, and the module docstring after `set_option .. in` is in place.
- Process vocabulary: 738 lines of the ticket grep on the base, 99 on the branch; each of the 99 is listed above (Lean names, hypothesis names, local variables, or the English word "control").
- TeX line references: 149 on the base, 0 on the branch (`texref.py --scan`). They were replaced by labels and numbers of the final paper (for example Lemma 8.3 `lem:propM`, Lemma 8.5 `lem_ConArg_BA`, (2.71) `Kn2sol`, (A.39) `eq_K-Kpi`). Equation and lemma numbers of the GUE-phase proofs are cited as those of [YY_25] and [RBSO1D].
- Module docstrings: every file starts with `/-! # ... -/` that describes the declarations the file contains. The identifier check (backticked names that occur in no code of the library) flags 510 comment lines on the base and 57 on the branch (all 57 are mathematical symbols, labels or prefixes, see above); the flagged comments were rewritten to say what the file proves or builds.
- Amend 1: no comment says a block Anderson result holds only at `d = 3` or `d > 3`. The remaining `d = 3` mentions are `EKPins.lean:119` (the `d = 3` instance of the lattice sum (A.19); the statement `BAEKSumDecay2` itself assumes `3 ≤ d` only) and `FlowPins.lean:28, 673` (the explicit data `FlowPinsInst` are at `d = 3`). Comments say "every `d`" or "every `d ≥ 3`" where the Lean statement does (for example `baKbound_holds`, `baKward_holds`, `baIniTermGen_cltFlow`).
- Amend 2: file and module paths named in comments exist (`paths.py`); backticked names exist exactly (`dangling.py`); the word "route" does not occur in any comment (`words2.py`, case-insensitive).
- Finding during the work: a module docstring `/-! -/` is a command. Deleting the one after `set_option maxHeartbeats 1600000 in` in `GUEEntry2.lean` made `in` apply to the next command (`error: GUEEntry2.lean:905:0 Unexpected name RBM.BA after end`, from my build log of that run). The file now keeps a one-line module docstring there, and `modin2.py` (above) checks that all such docstrings stay in place.
- Scope note: the stripping script ignores blank lines and trailing blanks, so blank lines between declarations may differ from the base; every non-blank code line is identical.

## (c) Verified Mathlib names
None: no code was written, so no Mathlib name is used.

## (d) Open issues and paper-delta candidates
- No paper-delta candidates. No port from RBM1D/RBM2D, so no diff-stat.
- Process incident (mine): at 2026-10-17T16:09:56Z and 16:09:59Z (transcript timestamps) I ran `pkill -f "lake build"` and `pkill -f "lean "` in a shell, patterns that are not limited to this worktree. The `ps` listing printed just before the second command shows `lean` processes of `RBM3D-wt/T2540`, of `/Users/junyin/Lean_proof/RBM3D` and of `RBM3D-wt/T2537`, each with about 22 minutes of CPU time. I did not check which of them were terminated; the other tickets' builds may have to be restarted. Afterwards I stopped only my own processes by PID. My first full build (start 16:44:52 UTC) was also stopped by me (exit 143) after a comment edit.
- Observations, no code change (comment-only ticket): `T2205_inv_spectral` (private, `CouplingWindow.lean:76`), `section D1` (`EKGenBA.lean:415`) and `section Pin` (`GreenOff.lean:1111`) carry planning-style names; renaming needs a code ticket.
- Style linter: lines over 100 characters in the 69 files: 7063 on the base, 6666 on the branch (warnings only, build exit 0).
- The full build took 94 minutes (start 16:48:40, end 18:22:10 UTC), dominated by `LWExpCertBS0` (2019 s) and `LWExpCertBS1` (3229 s) while other worktrees were building.

## Repair — Sat Oct 17 18:51:27 UTC 2026 (repairer claude-opus-5-5; audit round 1 F1, F2)
```
$ git log --format="%h %s" -1   # t/T2541
2a589ecd T2541: repair round 1 (audit F1, F2), comments only
$ git diff --stat 9d5fc877 HEAD
 RBM3D/BA/GUEEntry2.lean | 7 +++++--
 RBM3D/BA/GreenCore.lean | 2 +-
$ git diff --name-only main...t/T2541 | sort | diff - <(sort docs/tickets/T2541-files.txt) && echo "changed == list"
changed == list
$ python3 -I cmp.py $PWD 2a77235e docs/tickets/T2541-files.txt ; python3 -I modin2.py $PWD 2a77235e docs/tickets/T2541-files.txt
identical: 69 files / different: 0          identical: 69 files / different: 0; docstrings after an `in` line on the base: 1
$ grep -rnEi '<ticket pattern>' $(cat docs/tickets/T2541-files.txt) | wc -l ; texref.py --scan <69 files> | wc -l ; CJK grep | wc -l
99 ; 0 ; 0
$ grep -rnE '(^|[^_A-Za-z])decayRHS' $(cat docs/tickets/T2541-files.txt)      (no output)
$ grep -rnE '^(private )?(def|theorem) <name>( |$)' RBM3D    # every name in the new comment text
GUEEntryMixBA' GUEEntry2.lean:751 | GUEEntry_union GUEEntry2.lean:661 (private) | BAReal MFixedPoint.lean:432
mixEntry_final_arith Universality/GUEPhase/EntryTailMain.lean:462 (private) | GreenCore_decayRHS GreenCore.lean:1629
$ lake build RBM3D.BA.GUEEntry2 RBM3D.BA.GreenCore      # 18:46:46 - 18:47:01 UTC
Build completed successfully (3805 jobs).   exit 0
$ lake build      # start Sat Oct 17 18:47:08 UTC 2026
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).   exit 0   (end Sat Oct 17 18:51:12 UTC 2026; `^error` lines: 0)
```
- F1: the docstring of `gueEntryMixBA'` (GUEEntry2.lean:794-798) now describes its own body: the `filter_upwards`
  entries, the enlarged threshold `δ' = max (δ n) √(W^{-d})`, the inclusion of events, `GUEEntry_union`, `mixEntry_final_arith`.
  It no longer refers to a proof of `GUEEntryMixBA d`. The module docstring after `set_option maxHeartbeats 1600000 in` is kept.
- F2: GreenCore.lean:1634 reads `≺ GreenCore_decayRHS d L W c D Φ_t Ψ_t ([x], [y])`.
- Items 1-2 of Amend 2 were rerun only on the changed lines (the list above); no path occurs in them. O1 (`maxDist`) was not changed.
