Auditor model: claude-opus-5-5

# T2533 audit (round 1): BA-D row R1, `baStep5III_holds_any`, in place

Written Sat Oct 17 08:13:15 UTC 2026 (`date -u`). Branch `t/T2533` at 6db8094a, base `main` 970b8b54 (merge-base = main).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2533-audit1` (detached at 6db8094a). Scratch: scratchpad `T2533/`.

**Verdict: PASS** (one target, `baStep5III_holds_any`; `baStep5III_holds` unchanged in type). No stop rule fired.

## 1. Statement against the pin
```
$ python3 T2533/pin.py   # ticket ```lean block vs Step5IIITargets.lean; main vs branch for baStep5III_holds (whitespace-normalized)
pin == file (baStep5III_holds_any): True
main == branch (baStep5III_holds type): True
branch body: baStep5III_holds_any 3 le_rfl
$ lake env lean T2533/ax.lean   # #check, #print axioms, and an exact-type `example` of the pin
baStep5III_holds_any : ∀ (d : ℕ),
  3 ≤ d → STStep5IIIgL d (fun sz => (sz.withLam 0).seqP) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
baStep5III_holds : STStep5IIIgL 3 (fun sz => (sz.withLam 0).seqP) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz
  BAflowT0
'RBM.BA.baStep5III_holds_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0   (only output besides these: unused-variable linter on the scratch `example`'s binder `hd`)
```
The only premise is `3 ≤ d`; parameter order `(d) (hd)` as pinned; the tuple `(seqP (withLam 0), BAFlow, baFMz, BAflowT0)` is
the pinned one and is the `h5` argument type of the merged `baThm27L_any` (check Part 1 `#check`, below). The D2 Prop texts:
```
$ python3 T2533/d2.py   # probe t/T2524:RBM3D/Probe/T2524Pins.lean vs files (strip `T2524_`, `{d : ℕ} `; whitespace-normalized)
BAStep5IIIGood         probe==file: True  (2334 chars)
BAStep5IIIGoodThm      probe==file: True  (504 chars)
BAStep5IIIWalk         probe==file: True  (213 chars)
BAStep5IIIFromWalk     probe==file: True  (336 chars)
```
(`BAStep5IIIGood` takes `d` from `variable {d : ℕ}`, Good:67, = the probe's `{d : ℕ}` binder.)

## 2. Vacuity, hidden hypotheses, cycles
- `baStep5III_holds_any := ST_step5_caseIII_of_pfgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baPfStep5_holds d)`; `baPfStep5_holds d :=
  baPfStep5_of_walk d (baStep5IIIWalk_holds d) (baStep5IIIFromWalk_holds d)`: every input is a merged theorem or a theorem of the
  five files; the three Props are concluded by theorem heads (no Prop left as a premise). No structure-field hypothesis enters the
  target (`Step5IIIWalk2_Num` is a pre-existing `private structure` used inside the proof of `walk_at`, not a premise).
- No cycle: the five files import in the order Good → Good2 → Walk → Walk2 → Targets and import none of the readers of
  `baStep5III_holds`. Premise scan: see section 4 (passes, so `unregistered = []`).
- External readers of the changed public declarations:
```
$ grep -rlwE "BAStep5IIIGood|BAStep5IIIGoodThm|baStep5IIIGoodThm_holds|baStep5III_scalar_flow|...|baPfStep5_holds" RBM3D Test RBM3D.lean | grep -v BA/Step5III
RBM3D/Test/Axioms.lean        (line 181: a comment only)
```

## 3. Compiled nonempty instance
```
RBM3D/BA/Step5IIITargets.lean:73-75
example :
    STStep5IIIgL 4 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baStep5III_holds_any 4 (by norm_num)
```
The target's only hypothesis `3 ≤ d` is discharged at `d = 4` (nondegenerate; the first dimension `baStep5III_holds` does not
cover); it compiles in the full build (section 4). The ticket forbids new `d = 3` instances here and assigns the `Sizes 4` / flow
data instance to R2. Check Part 2 (target at every `d`) compiles too (section 4).

## 4. Build, axioms, hygiene, diff
```
$ lake build   # whole library, audit worktree, log T2533/full_build.log
⚠ [4414/4426] Built RBM3D.BA.Step5IIIWalk (10s)        ⚠ [4416/4426] Built RBM3D.BA.Step5IIITargets (3.1s)
info: RBM3D.lean:656:0: axiom audit: 10487 theorems, 3858 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 94 (borrowed 1, owed 36, structural 57, refuted 0, superseded 0).
Build completed successfully (4426 jobs).
exit=0
$ grep -c error full_build.log ; grep -E '^warning: RBM3D/BA/Step5III' full_build.log | grep -v 'exceeds the 100' | wc -l
0
0            (the ⚠ on Walk, Targets are longLine linter warnings only)
$ sed -n 532,536p RBM3D/Test/Axioms.lean   # the scan throws on a non-empty list, the build passed
  let unregistered := found.filter fun n => !classified.contains n
  unless unregistered.isEmpty do
    throwError m!"axiom audit: {unregistered.size} premise(s) that no theorem of this \
$ lake env lean docs/tickets/checks/T2533-check.lean   # Part 1, file identical to the main worktree's (cmp), unchanged on branch
Part1 exit=0 lines=7 error_lines=0
$ lake env lean T2533/chk2.lean   # Part 2 activated: `example : RBM.BA.T2533Check.Target := RBM.BA.baStep5III_holds_any`
Part2 exit=0 error_lines=0
$ grep -nE 'Sizes 3|Zd 3|Idx 3' RBM3D/BA/Step5III{Good,Good2,Walk,Walk2,Targets}.lean
exit=1   (no output)
$ grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' <five files>
exit=1   (no output)
$ grep -nE '(zdistInf|KLloopOf|tailTD|Step5IIIWalk_Ctot|baKbound_holds|pfStep5Grid_level|lossE2wG|baKsol_one|baStep5IIIJsharp_spec|
    baStep5III_matrix_level|Step5IIIGood_Wpow|baGridRepNAt2_holds|baFlow_premises|baStep5CasesGen_flowFacts) 3\b|\(d := 3\)|STIngR5gL 3|STPfStep5gL 3|STStep5IIIgL 3' <five files>
RBM3D/BA/Step5IIITargets.lean:64:    STStep5IIIgL 3 (...)      (the kept `baStep5III_holds`, required)
$ grep -nE '\^ 3\b|\b(6|2|12) \* 3\b|\(3 : ℕ\)' <five files>   # remaining dimension-shaped 3s
Good:362, :373, :407; Walk:201       ((W^d(1-u))⁻¹)^3  = 4-loop (`Fin 4`) power, loop order
Walk2:111, :144, :246, :318, :329, :333, :393; Walk:725, :763   N^3 = a-priori bound of `Step5IIIWalk_apriori` (already `{d}` on main)
Walk2:920, :941, :943                 N^3 with `Cv := ((3 : ℕ) : ℝ)` = the lift exponent (design b7: stays 3)
Walk:1415                             ((1-v)/(1-w))^3, ratio power, d-free
$ git diff --shortstat main...t/T2533 ; git diff --name-only main...t/T2533
 5 files changed, 284 insertions(+), 268 deletions(-)
RBM3D/BA/Step5IIIGood.lean  RBM3D/BA/Step5IIIGood2.lean  RBM3D/BA/Step5IIITargets.lean  RBM3D/BA/Step5IIIWalk.lean  RBM3D/BA/Step5IIIWalk2.lean
```
Only the five sole writable files (reports live in the main worktree). Landing 284+268 lines ≪ 1,950. `baStep5III_holds`
(the only declaration of the five files read in code outside them) keeps its type; its readers rebuild in the full build.

## 5. Class (b) changes against the design (T2524-design.md §1 table, §2, §4); read from `git diff main...t/T2533`
| item | design entry | branch | ok |
|---|---|---|---|
| b1 volume | `W^d`; `1 ≤ lam²W^d` via `lam_sq_mul_pow_ge` | Good:395-410, :568-572 (`sz.lam_sq_mul_pow_ge n hWO'.1`); Good2:58-61; Walk2 `hA`, `hRm` | yes |
| b2 level | `Dst - 2d` (`pfStep5Grid_level d`) | Walk:255-297 (`hlow`, `hWdl : W^{-d} ≤ 1-u`); Walk2 `PT` | yes |
| b3 floor | `(L^d W^{6d})² ≤ W^{Dst-2d}` via `pfStep5_fl` | Walk2:659-662 (`pfStep5_fl sz n hd1 h𝔠 hBWn hDstD₀`) | yes |
| b4 constants | `D₀ = 2/𝔠+12d`, `D* = max(D,D₀)+2d+1` | Walk2 `walk_at` (`hDstdef`, `hDstD₀`) | yes |
| b5 `d log W` | `√(2 Cq d)`, `Step5IIIWalk_Ctot d` | Walk2 `path` (`Real.sqrt (2 * Cq * (d : ℝ))`, `Step5IIIWalk_mart_real d`) | yes |
| b6 loss | `θ(d(Cd+1))`, `Step5IIIGood_Wpow d` | Good:409, :602; Walk `pertime` `hQ` | yes |
| b7 lift | `4L^{2d} ≤ N³`, `Cv = 3` | Walk2:918-943 (`hcardZ := by simp [Zd, ZMod.card]`, `hLN`) | yes |
| b8 side | `0 ≤ d`, `1 ≤ d` | Good:533 (`Nat.cast_nonneg d`); Walk2 `hd1 : 1 ≤ d := by omega` (walk_at, lift), `(by omega : 1 ≤ d)` (PT) | yes |
No (b) item exceeds its entry; no (c) item (no inequality replaced by a new argument). The probe helpers `T2524_*` were not needed
(none copied). Binders follow §2: Props `(d : ℕ)` with `3 ≤ d →` in GoodThm/FromWalk; `scalar_flow`, `walkLevel`, `walk_at`
take `(d) (hd)`; `bundle`, `good_of_flow`, `pertime`, private `Step5IIIWalk2_*` take `{d}` (+ `hd` where used); call sites pass
`d hd` (`baKbound_holds d hd`, `baEMn2ExpHK hd`, `baKsol_one d`, `pfStep5Grid_level d`, `lossE2wG d`, …).

## 6. Paper deltas
R1 removes a Lean/paper difference (Thm 2.7's BA case (iii) now at every `d ≥ 3`, as the paper). D723 is withdrawn as D754
(`docs/paper-deltas.md:1873`, present). The design gate's candidate `T2524a` (D712 (d) "targets 3, 4 only at `d = 3`", now
superseded) is proposed in `T2524-prove.md:221`; D712 (d) at `paper-deltas.md:1720` and the "只在 d = 3" remarks at :1776, :1789
still read as before until the dispatcher appends it. No new Lean/paper difference arises: coverage complete.

## 7. Observations (no statement, instance, build, axiom or delta effect)
- O1. The `d = 4` instance is an application at `d = 4` only; whether `BAFlow` at `Sizes 4` is inhabited is R2's data instance
  (ticket: "R2 handles instances"). Prove-report narrative states this.
- O2. Targets:70 docstring says the data instances belong to "ticket T2533, R2"; R2 is the next row, not T2533.
- O3. Stale "Compiled nonempty instances at `d = 3`" stub comments (Good:41, :607; Good2:22, :25, :84, :87; Walk:1500;
  Walk2:29, :989), listed in the prove report (d): for a comment ticket.
- O4. Prove report: 103 lines (≤ 120), line 1 `Prover model: claude-sonnet-5-5`; its build, axiom, grep and diff output agree
  with sections 1-4 above.

## Verdict
`baStep5III_holds_any`: **PASS**. `baStep5III_holds`: type unchanged (one line), **PASS**. No dispatcher sign-off needed.
