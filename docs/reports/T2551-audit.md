Auditor model: claude-opus-5-5

# T2551 audit (round 2): d = 4 example of FinalShape applies the BUniv conjunct

Date: Sat Oct 17 09:24:52 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2551-audit2`, detached at `t/T2551` = 3b9ebf4a (base main a92d38ad).
Scratch: `<scratchpad>/T2551/`.

## Verdict: PASS (single target: the `d = 4` example in `section D4Instance`; no statement changes)

## 1. Statement / diff scope

```
$ git diff --name-only main...t/T2551
RBM3D/Main/FinalShape.lean
$ git diff --stat main...t/T2551
 RBM3D/Main/FinalShape.lean | 12 +++++++-----
 1 file changed, 7 insertions(+), 5 deletions(-)
```
Only the sole writable file; 12 changed lines (≤ 30). Changed lines: 3 comment hunks (file header l.27, section
docstring l.128-129, example docstring l.215-216) and 2 added code lines inside the `d = 4` example:
```
+  have _ := h.2.2.2.1 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm 1 le_rfl κ hκ E (Eventually.of_forall fun _ => hb) 0
+    (by norm_num) UNInst.bump UNInst.bump_testFun
```
No declaration line (`theorem|def|example|lemma`) is added or removed by the diff:
```
$ git diff main...t/T2551 | grep -E "^[+-][^+-]" | grep -vE "<the two have-lines>" | grep -E "theorem|def |example|lemma"; echo $?
1
```
Statements of the published roots unchanged — the ticket check compiles against the branch build:
```
$ lake env lean docs/tickets/checks/T2551-check.lean ; echo exit $?
exit 0          (0 lines matching "error")
```
Binder order matches the pin `BAEnd_BUnivL d` (RBM3D/BA/UNPins.lean:304):
```
3 ≤ d → ∀ 𝔠 𝔡, ∀ sz, sz.Admissible 𝔠 𝔡 → ∀ k, 1 ≤ k → ∀ κ, 0 < κ →
  ∀ E, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ E', |E'| < 2 →
    ∀ O, IsTestFun O → UNUnivDilAt sz (UNModel.ba sz) (fun n => BArho d (sz.L n) (sz.lam n) E) E E' k O
```
and `BAThm27L d := decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff` (BA/MAPins.lean:126-127), so `h.2.2.2.1` is the BUniv
conjunct. Independent confirmation (scratch):
```
example (h32 : RBM.Univ.UNL32) : RBM.BA.BAEnd_BUnivL 4 := ((RBM.Endpoints.final_shape h32).2 4 (by norm_num)).2.2.2.1
-> compiles (exit 0)
```

## 2. Vacuity / hidden hypotheses / cycles

- Data of the new application: `d = 4`, `(𝔠,𝔡) = (1/8,1/10)`, `sz = FinalShape_cls4 g0` with `hadm` proved
  (`FinalShape_cls4_adm`), `k = 1` (`le_rfl : 1 ≤ 1`), `κ > 0` and `BAbulk 4 4 g0 κ E` from `FinalShape_bulk4`
  (constructed real-axis solution, not assumed), `E' = 0` (`|0| < 2` by `norm_num`),
  `O = UNInst.bump : ContDiffBump (0 : Fin 1 → ℝ)` with radii `1 < 2` (Universality/Pins.lean:1176), `IsTestFun`
  discharged by `bump_testFun` (smooth, compact support; nonzero bump).
- No `N = 0`, empty index, collapsed window or `False` premise; no structure-field hypothesis added.
- Only hypothesis of the example: `h32 : UNL32` (authorized external input, unchanged). No new dependency.

## 3. Compiled nonempty instance

The target is itself the instance: the `d = 4` example now applies all five conjuncts of
`(final_shape h32).2 4` (h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2) at the same nondegenerate data, and compiles
(build below).

## 4. Build and axioms (audit worktree)

```
$ lake build RBM3D.Main.FinalShape 2>&1 | grep -E "error|warning|Build completed|FinalShape" | tail
⚠ [4420/4420] Built RBM3D.Main.FinalShape (8.2s)
warning: RBM3D/Main/FinalShape.lean:10:0: The module doc-string for a file should be the first command after the imports.
Build completed successfully (4420 jobs).
$ lake build 2>&1 | grep -E "error|axiom audit|Build completed"
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).
$ lake env lean T2551/ax.lean   (import RBM3D)
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Main/FinalShape.lean; echo $?
1
```
The doc-string-position warning at l.10 predates the ticket (line not in the diff).

## 5. Comments (deliverable 2)

All three locations updated to "all five conjuncts (decol, locSC, QUE, BUniv, QDiff)" (file header l.27, section
docstring l.128-129, example docstring l.215-216). Rule check on added lines:
```
$ git diff main...t/T2551 | grep -E "^\+" | grep -inE "vanish|empt|lam ?= ?0|λ ?= ?0|ticket|repair|prover|audit"
5:+**nonempty bulk** `BAbulk 4 4 g₀ κ E` (every `n`) and nonempty end domains, and all five conjuncts of
```
The only match is "nonempty bulk" (pre-existing wording); no process words, no BDC-C1 claim that a vanishing coupling
empties the bulk. No remaining "four of the five" in the file (prove report grep, l.20-215; reconfirmed by the diff).

## 6. Paper deltas

No Lean statement changes; no new Lean/paper difference; no candidate needed.

## Observations (no RETURN)

- O1. Prove report is 70 lines (`wc -l`), above the ticket's ≤ 60-line limit.
- O2. Prove report section (b) diff stat (`10 | 6 ins, 4 del`) is the pre-repair state; the repair section shows the
  current `12 | 7 ins, 5 del`.

## Per-target verdict

| Target | Verdict |
|---|---|
| `d = 4` example (`section D4Instance`, RBM3D/Main/FinalShape.lean) applies BUniv; no statement change | PASS |
