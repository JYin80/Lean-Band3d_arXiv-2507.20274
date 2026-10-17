Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 08:46:30 UTC 2026

(i) no exponents; (ii) not applicable; PASS

(a′) Preflight corrections: none.

## (b) Script output (stage 1b, prover-hard; started Sat Oct 17 08:46:38 UTC 2026; commit 69d7369e on t/T2549 at Sat Oct 17 09:06:16 UTC 2026; report written Sat Oct 17 09:09:26 UTC 2026)

### b.1 Scope
```
$ git -C ../RBM3D-wt/T2549 diff --stat b51d55d7 HEAD
 RBM3D/BA/Step5IIIGood.lean    | 104 +++++++++++++---------------
 RBM3D/BA/Step5IIIGood2.lean   |  45 +++++-------
 RBM3D/BA/Step5IIITargets.lean |  48 ++++++-------
 RBM3D/BA/Step5IIIWalk.lean    | 154 ++++++++++++++++++++++--------------------
 RBM3D/BA/Step5IIIWalk2.lean   | 111 ++++++++++++++----------------
 RBM3D/BA/UNBUniv.lean         | 135 ++++++++++++++++++------------------
 RBM3D/Main/FinalShape.lean    |  55 ++++++++-------
 7 files changed, 310 insertions(+), 342 deletions(-)
$ python3 -I decls.py   (snippet in b.2)
declaration heads in comment-stripped code: b51d55d7 125, t/T2549 125, lists equal: True
```

### b.2 Comment-stripping script (strip_check.py, scratchpad copy) and its summary
```python
#!/usr/bin/env python3
# Comment-stripping check: strip_check.py BASE_COMMIT FILELIST  (run in the worktree of t/T2549)
# Removes nested /- -/ (including /-- and /-!), -- to end of line; keeps string and character literals;
# drops blank lines and trailing blanks; compares the stripped text on BASE_COMMIT and on the work tree.
import subprocess, sys
IDCH = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?.")

def strip(src):
    i, n, out = 0, len(src), []
    while i < n:
        c = src[i]
        if c == '"':                                   # string literal
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1]); i = j + 1
        elif c == "'" and (i == 0 or src[i - 1] not in IDCH):   # character literal
            if i + 2 < n and src[i + 1] != '\\' and src[i + 2] == "'":
                out.append(src[i:i + 3]); i += 3
            elif i + 1 < n and src[i + 1] == '\\':
                j = src.find("'", i + 2); out.append(src[i:j + 1]); i = j + 1
            else:
                out.append(c); i += 1
        elif src.startswith('--', i):                  # line comment
            j = src.find('\n', i); i = n if j < 0 else j
        elif src.startswith('/-', i):                  # nested block comment
            depth, j = 1, i + 2
            while j < n and depth > 0:
                if src.startswith('/-', j): depth += 1; j += 2
                elif src.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            out.append('\n' * src[i:j].count('\n')); i = j
        else:
            out.append(c); i += 1
    return [l.rstrip() for l in ''.join(out).split('\n') if l.strip()]

base, listing = sys.argv[1], sys.argv[2]
same = diff = 0
for f in open(listing).read().split():
    old = subprocess.run(['git', 'show', f'{base}:{f}'], capture_output=True, text=True, check=True).stdout
    new = open(f, encoding='utf-8').read()
    a, b = strip(old), strip(new)
    if a == b:
        same += 1
    else:
        diff += 1; print('DIFFERENT', f)
    print(f'{f}: {len(a)} code lines on {base}, {len(b)} on t/T2549')
print(f'identical: {same} files'); print(f'different: {diff}')
```
```
$ cd ../RBM3D-wt/T2549 && python3 -I strip_check.py b51d55d7 docs/tickets/T2549-files.txt
RBM3D/BA/Step5IIIGood.lean: 483 code lines on b51d55d7, 483 on t/T2549
RBM3D/BA/Step5IIIGood2.lean: 41 code lines on b51d55d7, 41 on t/T2549
RBM3D/BA/Step5IIITargets.lean: 30 code lines on b51d55d7, 30 on t/T2549
RBM3D/BA/Step5IIIWalk.lean: 1249 code lines on b51d55d7, 1249 on t/T2549
RBM3D/BA/Step5IIIWalk2.lean: 862 code lines on b51d55d7, 862 on t/T2549
RBM3D/BA/UNBUniv.lean: 166 code lines on b51d55d7, 166 on t/T2549
RBM3D/Main/FinalShape.lean: 147 code lines on b51d55d7, 147 on t/T2549
identical: 7 files
different: 0
```
Negative controls of the script (code token changed: not equal; comment word changed: equal; `"a -- b"` kept; nested comment removed):
```
control 1 (one code token changed): False
control 2 (one comment word changed): True
control 3 (string literal with -- kept): True
control 4 (nested comment): True
```
Snippet `decls.py` (uses `strip` of the script above; declaration heads of the comment-stripped code):
```python
import re, subprocess
exec(open('strip_check.py').read().split('base, listing')[0])
pat = re.compile(r'^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure|example|instance|axiom|opaque)\b')
tb = tn = 0; eq = True
for f in open('docs/tickets/T2549-files.txt').read().split():
    old = subprocess.run(['git', 'show', 'b51d55d7:' + f], capture_output=True, text=True).stdout
    a = [l for l in strip(old) if pat.match(l)]
    b = [l for l in strip(open(f, encoding='utf-8').read()) if pat.match(l)]
    tb += len(a); tn += len(b); eq = eq and a == b
print(f'declaration heads in comment-stripped code: b51d55d7 {tb}, t/T2549 {tn}, lists equal: {eq}')
```
`b51d55d7` is the head of `main` at the start (`git log -1 --format=%H main` printed `b51d55d7b87936f8fc3b0eadc29ed9199c1e6588`).

### b.3 Acceptance greps on the branch, and the TeX line references (texref.py)
```
$ grep -rnEi 'T2[0-9]{3}|DECISIONS|paper-delta|\bD[0-9]{1,3}\b|\b(1_2|3_5|6|7_8|A|B):[0-9]+|ticket|prover|auditor|preflight|dispatcher|supervisor|\bhub\b|frozen|pinned|\bpin\b|\bamend|rework|\bprobe\b|\bgate\b|\bowed\b|\bREQ\b|\bH[0-9]{3}\b|CLAUDE\.md|HANDOVER|CONTROL|RBM[12]D/[^ ]*:[0-9]|sub-stage|successor|census' $(cat docs/tickets/T2549-files.txt)
(exit 1; no output = no hit)
$ grep -rnP '[\x{4e00}-\x{9fff}]' $(cat docs/tickets/T2549-files.txt)
(exit 1; no output = no hit)
$ grep -L '/-!' $(cat docs/tickets/T2549-files.txt)
(exit 1; empty list = every file has a module docstring)
$ grep -rnE '\.lean:[0-9]|RBM[12]D|[0-9]_[0-9A-Z]*:[0-9]{2,}|§' $(cat docs/tickets/T2549-files.txt)   (file:line, sister-project and TeX line references)
(exit 1; no output = no hit)
```
```
$ python3 docs/claude-team/tools/texref.py --scan <the 7 files as on b51d55d7>      (18 TeX line references on main)
Step5IIIGood.lean:21: 3_5:2364-2383 -> proof of Lemma 5.3 `TailtoTail` p.51; section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; ne
Step5IIIGood.lean:22: 3_5:2369-2372 -> section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; nearest label above: (5.46) `neiwuj` p.5
Step5IIIGood.lean:22: 3_5:2310-2312 -> in (5.42) `eq:def_new_J*` p.51; section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; nearest 
Step5IIIGood.lean:23: 3_5:2314-2338 -> section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; nearest label above: (5.42) `eq:def_new_
Step5IIIGood.lean:23: 7_8:2101 -> section "Extension to the block Anderson model" Section 8 `sec:ext-to-BA` p.71; nearest label above: (8.26) `eq_resolventunderexp2` p.77
Step5IIIGood.lean:314: 3_5:2310 -> in (5.42) `eq:def_new_J*` p.51; section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; nearest labe
Step5IIIGood2.lean:12: 3_5:2314-2338 -> section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; nearest label above: (5.42) `eq:def_new
Step5IIIGood2.lean:13: 7_8:2101 -> section "Extension to the block Anderson model" Section 8 `sec:ext-to-BA` p.71; nearest label above: (8.26) `eq_resolventunderexp2` p.77
Step5IIITargets.lean:13: 3_5:2364-2383 -> proof of Lemma 5.3 `TailtoTail` p.51; section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50;
Step5IIITargets.lean:13: 3_5:2284 -> section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; nearest label above: Subsection 5.3 `sec:S
Step5IIITargets.lean:14: 7_8:2101 -> section "Extension to the block Anderson model" Section 8 `sec:ext-to-BA` p.71; nearest label above: (8.26) `eq_resolventunderexp2` p.77
Step5IIITargets.lean:52: 3_5:2364-2383 -> proof of Lemma 5.3 `TailtoTail` p.51; section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50;
Step5IIIWalk.lean:18: 3_5:2376-2383 -> in Lemma 5.4 `lem:pf_step5` p.51; section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; neares
Step5IIIWalk.lean:19: 7_8:2101 -> section "Extension to the block Anderson model" Section 8 `sec:ext-to-BA` p.71; nearest label above: (8.26) `eq_resolventunderexp2` p.77
Step5IIIWalk2.lean:14: 3_5:2376-2383 -> in Lemma 5.4 `lem:pf_step5` p.51; section "The case \texorpdfstring{$1-t \ge \ilambda^2$" Subsection 5.3 `sec:Step5_larget` p.50; neare
Step5IIIWalk2.lean:16: 7_8:2101 -> section "Extension to the block Anderson model" Section 8 `sec:ext-to-BA` p.71; nearest label above: (8.26) `eq_resolventunderexp2` p.77
UNBUniv.lean:41: 1_2:452-460 -> in Theorem 2.4 `Thm: B_Univ` p.9; section "Main results for the random band matrix model" Subsection 2.1 `subsec:main` p.7; nearest label above
UNBUniv.lean:41: 1_2:655 -> in Theorem 2.7 `MR:decol_BA` p.11; section "Main results for the block Anderson model"; nearest label above: Theorem 2.7 `MR:decol_BA` p.11
$ python3 docs/claude-team/tools/texref.py --scan <the 7 files on t/T2549> | wc -l
0
```

### b.4 Builds and the check file
```
$ lake build RBM3D.BA.Step5IIIGood RBM3D.BA.Step5IIIGood2 RBM3D.BA.Step5IIITargets RBM3D.BA.Step5IIIWalk RBM3D.BA.Step5IIIWalk2 RBM3D.BA.UNBUniv RBM3D.Main.FinalShape   (Sat Oct 17 09:06:44 UTC 2026; the first build of this closure ran 09:00:42 UTC, 3:06 minutes)
Build completed successfully (4420 jobs).
(exit 0)
$ lake build   (full library, Sat Oct 17 09:04:00 to 09:05:02 UTC; includes #assert_rbm_axioms)
non-vacuity certificates: 0 of 100 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4426 jobs).
lake build > $S/build_full.log 2>&1  43.48s user 6.20s system 80% cpu 1:01.98 total exit 0 
$ grep -c "^error" build_full.log;  grep "^warning: RBM3D/(BA/(Step5III|UNBUniv)|Main/FinalShape)" build_full.log
0
warning: RBM3D/Main/FinalShape.lean:10:0: The module doc-string for a file should be the first command after the imports.
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2549-check.lean   (first run Sat Oct 17 09:05:15 UTC 2026, in the worktree; the output below is from the rerun that records the exit code)
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
RBM.BA.baStep5III_holds_any : ∀ (d : ℕ),
  3 ≤ d →
    RBM.BA.STStep5IIIgL d (fun sz => (sz.withLam 0).seqP) (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) RBM.BA.baFMz
      RBM.BA.BAflowT0
RBM.BA.baStep5III_holds : RBM.BA.STStep5IIIgL 3 (fun sz => (sz.withLam 0).seqP)
  (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) RBM.BA.baFMz RBM.BA.BAflowT0
(exit code 0, no error line)
```

### b.5 Axioms of the published roots, statements (extracted by script), instances, name clashes, ports
```
$ lake env lean axioms.lean   (Sat Oct 17 09:08:39 UTC 2026, in the worktree; import RBM3D; #print axioms of the six roots)
'RBM.BA.baStep5III_holds_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
$ grep -n -A2 -E "^(theorem|def) (baStep5III_holds_any|baStep5III_holds|baThm27L_all|baThm27L_three|Thm27|Thm27_of_L32|final_shape)\b" RBM3D/BA/Step5IIITargets.lean RBM3D/BA/UNBUniv.lean RBM3D/Main/FinalShape.lean
RBM3D/BA/Step5IIITargets.lean:59:theorem baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) :
RBM3D/BA/Step5IIITargets.lean-60-    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
RBM3D/BA/Step5IIITargets.lean-61-  ST_step5_caseIII_of_pfgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baPfStep5_holds d)
RBM3D/BA/Step5IIITargets.lean:64:theorem baStep5III_holds :
RBM3D/BA/Step5IIITargets.lean-65-    STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
RBM3D/BA/Step5IIITargets.lean-66-  baStep5III_holds_any 3 le_rfl
RBM3D/Main/FinalShape.lean:39:def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
RBM3D/Main/FinalShape.lean-40-
RBM3D/Main/FinalShape.lean-41-/-- Theorem 2.7 at every `d ≥ 3` from the external input `UNL32` only: `baThm27L_all` (`BA/UNBUniv`). -/
RBM3D/Main/FinalShape.lean:42:theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27 := RBM.BA.baThm27L_all
RBM3D/Main/FinalShape.lean-43-
RBM3D/Main/FinalShape.lean-44-/-- **The final shape**: the paper's main results (band Theorems 2.1-2.5, block Anderson Theorem 2.7 at every `d ≥ 3`) with the single
RBM3D/Main/FinalShape.lean:46:theorem final_shape : RBM.Univ.UNL32 →
RBM3D/Main/FinalShape.lean-47-    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27 := fun h32 =>
RBM3D/Main/FinalShape.lean-48-  ⟨band_terminal h32, Thm27_of_L32 h32⟩
RBM3D/BA/UNBUniv.lean:271:theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d :=
RBM3D/BA/UNBUniv.lean-272-  fun d hd => baThm27L_any d hd (baStep5III_holds_any d hd) h32
RBM3D/BA/UNBUniv.lean-273-
RBM3D/BA/UNBUniv.lean:276:theorem baThm27L_three : UNL32 → BAThm27L 3 :=
RBM3D/BA/UNBUniv.lean-277-  fun h32 => baThm27L_all h32 3 le_rfl
RBM3D/BA/UNBUniv.lean-278-
$ grep -n "^example" RBM3D/BA/Step5IIITargets.lean RBM3D/Main/FinalShape.lean   (the nonempty instances; their code is unchanged, b.2)
RBM3D/BA/Step5IIITargets.lean:73:example :
RBM3D/Main/FinalShape.lean:63:example (h32 : UNL32) :=
RBM3D/Main/FinalShape.lean:67:example (h32 : UNL32) :=
RBM3D/Main/FinalShape.lean:71:example (h32 : UNL32) :=
RBM3D/Main/FinalShape.lean:75:example (h32 : UNL32) :=
RBM3D/Main/FinalShape.lean:79:example (h32 : UNL32) :=
RBM3D/Main/FinalShape.lean:88:example (h32 : UNL32) : True := by
RBM3D/Main/FinalShape.lean:102:example (h32 : UNL32) : True := by
RBM3D/Main/FinalShape.lean:217:example (h32 : UNL32) : ∃ g0 E κ : ℝ, 0 < κ ∧ (FinalShape_cls4 g0).Admissible (1 / 8) (1 / 10) ∧
```
Name clash: no declaration is added or renamed (declaration heads equal, b.1), so there is no new public name. Ports: none (comments only), so no RBM1D/RBM2D diff-stat.
No new declaration, so no new instance is owed: the existing instances above compile in the builds of b.4 with every deterministic hypothesis discharged (`UNL32` is the only hypothesis left in the `final_shape` examples).

### b.6 Narrative
1. Rewritten: the module docstrings, docstrings and comments of the 7 files (310 insertions, 342 deletions, b.1); the comment-stripped code is identical (7 of 7, 125 declaration heads equal, b.2). The 18 TeX line references of the submission (b.3) are gone; they are now labels and numbers of the final paper, read from `docs/claude-team/tools/paper-labels.tsv` and the TeX around the cited lines (`paper/tex/3_5` 2284-2390, `7_8` 2095-2101, `1_2` 640-660): Lemma 5.4 `lem:pf_step5`, Lemma 5.2 `lem_dec_calE`, Lemma 5.3 `TailtoTail`, (5.42) `eq:def_new_J*`, (5.47) `eq:def_TTT`, (3.13) `int_K-L_ST`, Subsection 5.3 `sec:Step5_larget`, Theorem 2.4 `Thm: B_Univ`, Theorem 2.7 `MR:decol_BA`, and Theorem 8.2 `lem:main_ind_BA` for the sentence of the paper that omits the details for the block Anderson model. The scan names the start line `3_5:2364` as inside the proof of Lemma 5.3; lines 2376-2383 are the proof of Lemma 5.4, which is the lemma cited.
2. Scope of Theorem 2.7 (ticket item 6): `Step5IIITargets`, `UNBUniv` and `FinalShape` now say that `baStep5III_holds_any`, `baThm27L_all` and `Thm27` are for every `d ≥ 3`, that `baStep5III_holds` and `baThm27L_three` are their `d = 3` cases, and that `baThm27L_any` takes Step 5 in case (iii) as a hypothesis which `baThm27L_all` discharges. The sentences about `d = 3` only, the decision, the withdrawn difference and the closing condition are removed. The section 5 header of `UNBUniv` (T2534 audit observation 2) now states that the instances are in `Main/FinalShape.lean`.
3. `FinalShape` instances, from the source: `d = 3` on `S0 = clsS 4 _` (`L = 4`, `W_n = (2(n+1))^5`, constant `lam = g₀` of the flow point), `(𝔠, 𝔡) = (1/6, 1/10)`, all five block Anderson conjuncts applied; `d = 4` on `FinalShape_cls4 g₀` (`L = 4`, `W_n = (2(n+1))^5`, constant `lam = g₀`, `g₀ ∈ (0, 3/10]`), `(𝔠, 𝔡) = (1/8, 1/10)`, bulk `BAbulk 4 4 g₀ κ E` proved nonempty (`FinalShape_bulk4`), the conjuncts decol, locSC, QUE, QDiff applied, the BUniv conjunct not applied.
4. Statements that the code contradicted were corrected by reading it: the `Step5IIIWalk` docstring listed `baStep5III_duhamel` (no declaration of that name; the declaration is `Step5IIIWalk_duhamel`); the `UNBUniv` docstring listed `unG1RowkBA_holds` and `unOURowBA_holds` (no such theorem at b51d55d7: `git show b51d55d7:RBM3D/BA/UNBUniv.lean | grep -c` printed 0) and said the `d > 3` form stays in hypothesis form (`baEnd_BUnivL_of_ML` takes `3 ≤ d`). The sections "Compiled nonempty instances" of `Step5IIIGood`, `Step5IIIGood2`, `Step5IIIWalk`, `Step5IIIWalk2` contained no `example` (`grep -c '^example'` printed 0 on b51d55d7 for each) and were deleted.
5. The labels K1-K3 (semigroup law, row sums, near identity: the first three clauses of `GridRepTailGen_Ker`) are explained in the module docstring of `Step5IIIWalk`; the label (H2) of another file is replaced by "the crude-bound hypothesis". The prose word "control" became "parameter" (the paper's `𝒥*` is its control parameter), because the ticket's case-insensitive grep matches `CONTROL`. The module docstrings are wrapped to 100 characters (the build linter counts them before the `set_option` lines); the build prints no warning for the six files other than `FinalShape`, whose one warning (b.4) is about its `set_option` line preceding the module docstring, code order that the ticket forbids changing.

## (c) Verified Mathlib names
None used: comments only.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none.
- Observation: files outside this ticket's list still cite ticket numbers: `grep -c "T2[0-9]\{3\}"` printed 9 for `BA/Step5IIIEdet.lean`, 9 for `BA/Step5IIIEdet2.lean`, 6 for `BA/Step5IIIKer.lean`, 3 for `BA/Step5IIIKer2.lean`, 4 for `Chain/GridRepTailGen.lean`; none of them is in `docs/tickets/T2549-files.txt` and none was touched. The docstrings written here refer to `GridRepTailGen_Ker` and `baStep5IIITailSqQV_holds` by name only.
- Observation: the source of the `d = 4` example does not state why the BUniv conjunct is not applied at `d = 4`; the docstring says only that it is not applied.

## Repair — Sat Oct 17 09:14:59 UTC 2026 (repairer, claude-opus-5-5; audit round 1 RETURN, Amend 1 BDC-C2)
Comments only, `RBM3D/Main/FinalShape.lean`, the three places the audit names (option (b): no reason given for not applying
BUniv at `d = 4`; the qualifier "that read `Sizes` and `Admissible`" is dropped). Commit 94109171 on t/T2549 (09:14:56 UTC).
```
$ git diff --stat 69d7369e HEAD
 RBM3D/Main/FinalShape.lean | 14 +++++++-------
 1 file changed, 7 insertions(+), 7 deletions(-)
$ git diff --stat main...t/T2549 | tail -1
 7 files changed, 312 insertions(+), 344 deletions(-)
$ python3 -I strip_check.py b51d55d7 docs/tickets/T2549-files.txt      (script of b.2)
RBM3D/BA/Step5IIIGood.lean: 483 code lines on b51d55d7, 483 on t/T2549
RBM3D/BA/Step5IIIGood2.lean: 41 code lines on b51d55d7, 41 on t/T2549
RBM3D/BA/Step5IIITargets.lean: 30 code lines on b51d55d7, 30 on t/T2549
RBM3D/BA/Step5IIIWalk.lean: 1249 code lines on b51d55d7, 1249 on t/T2549
RBM3D/BA/Step5IIIWalk2.lean: 862 code lines on b51d55d7, 862 on t/T2549
RBM3D/BA/UNBUniv.lean: 166 code lines on b51d55d7, 166 on t/T2549
RBM3D/Main/FinalShape.lean: 147 code lines on b51d55d7, 147 on t/T2549
identical: 7 files
different: 0
$ bash -c 'F=$(cat docs/tickets/T2549-files.txt); grep -rnEi "<ticket regex of b.3>" $F; echo "grep exit $?"'
grep exit 1
$ grep -L "/-!" $F; echo "grepL exit $?"
grepL exit 0                                (empty list)
$ python3 docs/claude-team/tools/texref.py --scan $F | wc -l
       0
$ grep -nEi "vanish|empty bulk|read \`Sizes\`|Sizes\` \+|reads? .*d = 3" $F      (BDC-C1, BDC-C2)
RBM3D/Main/FinalShape.lean:123:/-! ### The `d = 4` instance: `(𝔠, 𝔡) = (1/8, 1/10)`, nonempty bulk
RBM3D/Main/FinalShape.lean:192:/-- A nonempty bulk at `(d, L) = (4, 4)`: a coupling `g₀ ∈ (0, 3/10]`, an energy `E` and `κ > 0` with `κ ≤ ρ(E)`. -/
RBM3D/Main/FinalShape.lean:215:**nonempty bulk** `BAbulk 4 4 g₀ κ E` (every `n`) and nonempty end domains, and four of the five conjuncts of
$ lake build RBM3D.Main.FinalShape      (Sat Oct 17 09:14:39 -> 09:14:52 UTC 2026)
Build completed successfully (4420 jobs).
exit 0;  grep -c '^error' = 0
warning: RBM3D/Main/FinalShape.lean:10:0: The module doc-string for a file should be the first command after the imports.
```
The remaining hits are "nonempty bulk" only (BDC-C1 kept). New text at the three places: lines 27-29 "at `d = 4` four of the five
conjuncts (decol, locSC, QUE, QDiff) are applied on the class sequence …"; lines 128-129 "Four of the five conjuncts of `Thm27 4`
(decol, locSC, QUE, QDiff) are applied over it."; lines 215-216 "and four of the five conjuncts of `(final_shape h32).2 4` (decol,
locSC, QUE, QDiff) applied at it". No statement changed; no paper-delta candidate.
