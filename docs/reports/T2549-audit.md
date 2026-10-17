Auditor model: claude-opus-5-5

# T2549 audit, round 2 (comments only, 7 block Anderson files of Theorem 2.7 at every d >= 3; Amend 1)

Written Sat Oct 17 09:17:45 UTC 2026 (`date -u`). Branch `t/T2549` at 94109171 (repair after round-1 RETURN), base b51d55d7.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2549-audit2` (detached at 94109171). Inputs: ticket T2549, Amend 1.
Scratch scripts: scratchpad `T2549/strip.py`, `T2549/comments.py`, `T2549/ax.lean`.

**Verdict: PASS.** Amend 1 BDC-C1 and BDC-C2 are met. Every acceptance item of the ticket passes. No dispatcher sign-off is needed.

## 1. Scope of the diff
```
$ git diff --name-only b51d55d7 t/T2549
RBM3D/BA/Step5IIIGood.lean
RBM3D/BA/Step5IIIGood2.lean
RBM3D/BA/Step5IIITargets.lean
RBM3D/BA/Step5IIIWalk.lean
RBM3D/BA/Step5IIIWalk2.lean
RBM3D/BA/UNBUniv.lean
RBM3D/Main/FinalShape.lean
$ git diff --stat b51d55d7 main -- $(cat docs/tickets/T2549-files.txt)      (main = 0916ab51)
(empty: main has not touched the 7 files since the base)
$ git show 94109171 --stat   ->   RBM3D/Main/FinalShape.lean | 14 +++++++-------
```
This is exactly the list in `docs/tickets/T2549-files.txt`. `RBM3D.lean` and `RBM3D/Test/` are untouched.

## 2. Comments only (auditor's own lexer: nested `/- -/`, `/--`, `/-!`, `--` to EOL, string and char literals)
```
$ python3 -I T2549/strip.py b51d55d7 t/T2549 docs/tickets/T2549-files.txt
RBM3D/BA/Step5IIIGood.lean: code lines 483 / 483  identical
RBM3D/BA/Step5IIIGood2.lean: code lines 41 / 41  identical
RBM3D/BA/Step5IIITargets.lean: code lines 30 / 30  identical
RBM3D/BA/Step5IIIWalk.lean: code lines 1249 / 1249  identical
RBM3D/BA/Step5IIIWalk2.lean: code lines 862 / 862  identical
RBM3D/BA/UNBUniv.lean: code lines 166 / 166  identical
RBM3D/Main/FinalShape.lean: code lines 147 / 147  identical
identical: 7 files
different: 0
control nested/doc/string: True
control code change detected: True
```
No declaration, statement, proof, attribute or example changed. Statements, hypotheses and compiled instances are therefore the
ones already merged on main (T2534). There are no new endpoint theorems to instantiate. The existing instances still compile (section 5).

## 3. Acceptance greps (bash, in the audit worktree)
```
$ grep -rnEi '<the ticket regex, verbatim>' $(cat docs/tickets/T2549-files.txt)
grep1 exit 1                                   (no hit)
$ python3 CJK scan [一-鿿] over the 7 files
CJK hits: 0
$ grep -L '/-!' $(cat docs/tickets/T2549-files.txt)
(empty)
$ python3 docs/claude-team/tools/texref.py --scan $(cat docs/tickets/T2549-files.txt) | wc -l
       0                                       (control on main b51d55d7 files: 18)
```
Further comment-only scan (`comments.py`) for planning and history words (wave|stage|route|row|landing|structural|refuted|superseded|
borrowed|earlier|no longer|moved|renamed|the old|primed|now|decision|closing|withdrawn|replaced|version|U1s2|MN-D3|C5|MA-06b|BA-L|
BA-TL|BA-D|ST-6|UN-01|G1-4|Fable|RBM[12]D|hex hashes|was|previously). Hits:
```
Step5IIIWalk.lean:39/319/342: "row sums" of GridRepTailGen_Ker / a matrix / θ_t      (matrix row sums)
Step5IIIWalk.lean:53: "the good event moved to the grid walk"                         (transfer of an event)
Step5IIIWalk.lean:583: "with the energy bound and the unit modulus of m replaced by the kernel class"   (substitution)
Step5IIIWalk.lean:1366: "(Σ_{l=3}^{2} is empty)"                                       (empty sum)
UNBUniv.lean:20: "the block Anderson version of Theorem 2.4"                           (model variant)
UNBUniv.lean:62-79: "read only at the dimensions d with Dm d" (x6)                     (dimension filter Dm)
UNBUniv.lean:142: "row sum 2d of Ψ"                                                   (matrix row sum)
```
All are mathematical.
Paper citations match `docs/claude-team/tools/paper-labels.tsv` (final paper):
```
lem:pf_step5 5.4 | lem:main_ind_BA 8.2 | eq:def_new_J* 5.42 | eq:def_TTT 5.47 | int_K-L_ST 3.13 | TailtoTail 5.3
lem_dec_calE 5.2 | MR:decol_BA 2.7 | Thm: B_Univ 2.4 | sec:Step5_larget 5.3 | eq:WO 2.10
```
Each label is cited with these numbers in the comments.

## 4. Scope of Theorem 2.7 (ticket item 6), checked against the signatures
```
UNBUniv.lean:263  theorem baThm27L_any (d : ℕ) (hd : 3 ≤ d) (... STStep5IIIgL d ...) (h32 : UNL32) : BAThm27L d
UNBUniv.lean:271  theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d
UNBUniv.lean:276  theorem baThm27L_three : UNL32 → BAThm27L 3
Step5IIITargets   theorem baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) : STStep5IIIgL d ...;  baStep5III_holds := baStep5III_holds_any 3 le_rfl
FinalShape        def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
```
Comments on the branch:
- UNBUniv:38-41, 261-275 describe `baThm27L_any` as the form with Step 5 (iii) `STStep5IIIgL d` as a hypothesis. They say
  `baThm27L_all` discharges it and proves Theorem 2.7 at every `d ≥ 3` with `UNL32` its only hypothesis, and that `baThm27L_three`
  is its `d = 3` case.
- Step5IIITargets:24-25, 58, 63 say `baStep5III_holds_any` covers every `d ≥ 3` with no premise beyond `3 ≤ d`, and that
  `baStep5III_holds` is its `d = 3` case.
- UNBUniv:42 and 281-283 now say "the instances of `baThm27L_all` are in `Main/FinalShape.lean`". This fixes the section header
  (T2534 audit observation 2).
- FinalShape:13-29, 37 state Theorem 2.7 at every `d ≥ 3`.

No sentence restricts the scope to `d = 3` or calls the general case a hypothesis or a decision. The grep finds no "D723", "decision" or
"closing" hit. PASS.

## 5. Amend 1 (FinalShape.lean, branch text)
The repair diff (69d7369e..94109171) changes only the three named places: main :24-25 -> branch :27-29, :123-124 -> :128-129, and
:209-211 -> :214-216.
```
27-29:  ... and at `d = 4` four of the five conjuncts (decol, locSC, QUE,
        QDiff) are applied on the class sequence with `L = 4`, `W_n = (2(n+1))⁵`, `(𝔠, 𝔡) = (1/8, 1/10)`,
        over a bulk proved to be nonempty.
128-129: ... into `BAbulk 4 4 g₀ κ E` with `κ = Im m₀ / π > 0`, for every `n`.  Four of the five conjuncts of `Thm27 4`
        (decol, locSC, QUE, QDiff) are applied over it. -/
214-216: **The `d = 4` instance of `Thm27`**: ... and four of the five conjuncts of
        `(final_shape h32).2 4` (decol, locSC, QUE, QDiff) applied at it; `UNL32` is the only hypothesis.
```
- **BDC-C2: met** (option (b): no reason is given). The qualifier "that read `Sizes` and `Admissible`" and the sentence "the BUniv conjunct
  is not applied at `d = 4`" are gone. No comment in the 7 files says that BUniv reads `d = 3` data. The words are accurate: the
  `d = 4` example applies `h.1`, `h.2.1`, `h.2.2.1` and `h.2.2.2.2`, which are decol, locSC, QUE and QDiff in the order of `BAThm27L`.
- **BDC-C1: met.** A comment scan for `vanish|empty|→ 0|small` in FinalShape finds no hit except "nonempty bulk". The data are
  stated as they are in the source:
  - `FinalShape_cls4`: `L := fun _ => 4`, `W := fun n => (2 * (n + 1)) ^ 5`, `lam := fun _ => g0`.
  - `FinalShape_bulk4 : ∃ g0 E κ, 0 < g0 ∧ g0 ≤ 3/10 ∧ 0 < κ ∧ BAbulk 4 4 g0 κ E`, with the docstring "g₀ ∈ (0, 3/10]".
  - The comment does not claim that a vanishing coupling would give an empty bulk.

## 6. Build, check file, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.BA.Step5IIIGood RBM3D.BA.Step5IIIGood2 RBM3D.BA.Step5IIITargets RBM3D.BA.Step5IIIWalk \
    RBM3D.BA.Step5IIIWalk2 RBM3D.BA.UNBUniv RBM3D.Main.FinalShape        (Sat Oct 17 09:15:43 -> 09:17:13 UTC 2026)
Build completed successfully (4420 jobs).      exit 0;  grep -c '^error' = 0
warnings in the 7 files: RBM3D/Main/FinalShape.lean:10:0: The module doc-string for a file should be the first command after the imports.
$ lake env lean docs/tickets/checks/T2549-check.lean
check-file exit 0
$ lake env lean T2549/ax.lean      (import RBM3D.Main.FinalShape; #print axioms)
'RBM.BA.baStep5III_holds_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^\s*axiom" <7 files>
hygiene grep exit 1   (no hit)
```
The hub runs the full `lake build` at merge.

## 7. Paper deltas
No statement changed (section 2), so there is no Lean/paper statement difference to cover. None is proposed. PASS.

## 8. Observations (not RETURN reasons)
- O1. The linter warning at `FinalShape.lean:10` is about command order (`set_option` before the module docstring). That order is code,
  identical to main, and the ticket forbids changing it.
- O2. The module docstring of FinalShape breaks a sentence early at line 29 ("Only `UNL32` stays a" / "hypothesis."). This is cosmetic.

## Verdict per target
Comments only and scope: PASS. Greps and module docstrings: PASS. Theorem 2.7 scope: PASS. Amend 1 BDC-C1: PASS. BDC-C2: PASS.
Build, check file, axioms: PASS. Paper deltas: PASS. **Overall: PASS.** No dispatcher sign-off needed.
