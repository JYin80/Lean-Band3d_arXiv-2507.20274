Auditor model: claude-opus-5-5
# T2382 audit (round 1): BA-T row 0, carrier relocation to `RBM3D/Chain/Carrier.lean`
Date (date -u): Sat Oct 10 12:25:59 UTC 2026. Branch `t/T2382` at `b3ffbd9`, merge base `2192dea`.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2382-audit1` (detached at b3ffbd9); reference worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2382-audit1-main` (detached at 2192dea). Scripts in scratchpad `T2382/`.

## 1. Statement: moved text identical, every constant unchanged
```
$ python3 -I mv.py    # difflib of main:BA/FlowPins.lean vs branch FlowPins and Carrier
deleted main ranges (1-based incl): [(315, 346), (351, 441), (454, 464)] count 134
added branch lines: 3
  + 7 import RBM3D.Chain.Carrier
  + 316 /-! ## 4. Target 4 (moved, T2382): `PrecL`, `FlowFM`, `FlowFM.GM` and the generic predicat
  + 317 `STJhatg` and `STLWassmExpgL` stay here because they use `STprof` of `Induction/Step2Defs`
carrier body nonblank: 120 moved nonblank: 116
diff moved vs carrier body:
@@ -29,0 +30,2 @@
+section Generic
+variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)
@@ -116,0 +119,2 @@
+end Generic
+end RBM.BA
main 443-454 still in branch: True
```
(The 4 extra Carrier lines are the copied `section`/`variable`/`end` scaffolding; the originals stay in
FlowPins around the two stayers. FlowPins adds one import plus a 2-line "why" comment, as the ticket allows.)

Stayers need `STprof` (`Induction/Step2Defs`), so they cannot move (branch `FlowPins.lean:318-335`):
```
7:def STJhatg (n : ℕ) (D ℓ u : ℝ) (ω : sz.SeqΩ) : ℝ :=
10:      ‖C.L n u p.1 p.2 ω - C.K n u p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))
13:def STLWassmExpgL (t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) : Prop :=
16:    (fun n p _ => STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))
```

Kernel-level comparison (G1, stronger than per-theorem examples): `dump.lean` (imports `RBM3D.BA.FlowPins`)
writes name, `ConstantInfo.type` and, for definitions, the value, of every constant whose module is
`RBM3D.BA.FlowPins` or `RBM3D.Chain.Carrier`; run at 2192dea and on the branch.
```
$ DUMPOUT=before.txt lake env lean dump.lean (in 2192dea worktree); exit 0
$ DUMPOUT=after.txt  lake env lean dump.lean (in branch worktree);  exit 0
$ python3 -I cmp.py
constants before/after (all): 191 193  non-aux: 176 176
only before: []
only after: []
changed type/value: ['RBM.BA.STDecayStronggL', 'RBM.BA.STDecaygL', ... 13 names]
aux only before: []
aux only after: ['RBM.BA.STDecaygL._proof_3', 'RBM.BA.STJhatg._proof_2']
$ python3 -I cmp.py  (token diff of three of them)
RBM.BA.STLKgL [('replace', ['.RBM3D.BA.FlowPins.705148929._hygCtx._hyg.93'], ['.RBM3D.Chain.Carrier.705148929._hygCtx._hyg.93']), ...]
RBM.BA.STJhatg [('replace', ['RBM.BA.STDecaygL._proof_N'], ['RBM.BA.STJhatg._proof_N']), ...]
RBM.BA.STDecaygL [('replace', ['.RBM3D.BA.FlowPins.1171324010._hygCtx._hyg.94'], ['.RBM3D.Chain.Carrier.1171324010._hygCtx._hyg.94']), ('replace', ['RBM.BA.BAProp7._proof_N'], ['RBM.BA.STDecaygL._proof_N'])]
$ python3 -I cmp2.py  # normalise hygienic binder module tag and auxiliary _proof_ names
non-aux constants compared: 176 ; changed after normalising hygiene module tag and aux-proof names: []
```
All 176 non-auxiliary constants (all public/private theorems of FlowPins, incl. `bandFM_*`, `STMainInd_iff`,
and every moved definition) keep name, type and value; the only differences are hygienic binder tags carrying
the module name and compiler-generated `_proof_N` names.

Dispatcher check file:
```
$ grep -c "^#check" T2382-check.lean; grep -c "^example" T2382-check.lean
17
0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2382-check.lean  (branch worktree)
check-exit 0
```

## 2. No vacuity, no hidden hypothesis, no cycle
No new definition, structure field or theorem: text moved verbatim (§1). Import graph (import lines of
`RBM3D/**/*.lean` on the branch):
```
$ python3 -I imp.py .
Carrier direct imports: ['RBM3D.Induction.Defs']
Carrier forward cone size: 35 ; meets modules importing Induction.Defs: []
forward cone has Step2Defs/Step34Pins/BA.*: []
reverse cone of FlowPins: 36
RBM3D.BA.Boundary ... RBM3D.Induction.MainIndBase RBM3D.Induction.MainIndChain RBM3D.Induction.MainIndHolds
RBM3D.Induction.MainIndOut RBM3D.Main.BandTerminal
Cert modules in it: []
```
`Chain/Carrier` imports no chain file above `Induction/Defs`, and no `Step2Defs`/`Step34Pins`/`BA/*`.
No external hypothesis (none introduced).

## 3. Compiled nonempty instances
The ticket has no endpoint theorem (pure move). The existing instances of the moved predicates stay in
`BA/FlowPins.lean` (section `FlowPinsInst`) and compile on the branch:
```
$ grep -c "^example" RBM3D/BA/FlowPins.lean
21
```
(built as part of `lake build RBM3D.BA.FlowPins` below).

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Chain.Carrier | grep -E "error|Build" | tail
Build completed successfully (3313 jobs).
$ lake build RBM3D.BA.FlowPins | grep -E "error|Build" | tail
Build completed successfully (3735 jobs).
$ lake build <the 36 modules of the reverse cone of FlowPins>; echo exit $?
exit 0
Build completed successfully (4185 jobs).
$ lake build > full.log; echo exit $?; grep "axiom audit" full.log; tail -1 full.log
exit 0
info: RBM3D.lean:429:0: axiom audit: 11013 theorems, 3223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4198 jobs).
$ lake env lean ax.lean | sort | uniq -c   # import RBM3D; #print axioms of the 18 names; #assert_rbm_axioms
  17 depends on axioms: [propext, Classical.choice, Quot.sound]
   1 does not depend on any axioms
   1 All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
exit 0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Chain/Carrier.lean RBM3D/BA/FlowPins.lean; echo $?
1
$ git diff --numstat main...t/T2382
3	134	RBM3D/BA/FlowPins.lean
178	0	RBM3D/Chain/Carrier.lean
2	2	RBM3D/Test/Axioms.lean
$ wc -l < RBM3D/Chain/Carrier.lean
178
```
- Scope: only the three sole writable files. FlowPins: the moved block out, one import line plus the
  2-line "why" comment in (ticket target 1 asks for that line). Stop line: 178 + |3 - 134| = 309 <= 500.
- `Test/Axioms.lean`: two comment-only edits (owner-comment file reference: "moved to
  `RBM3D/Chain/Carrier.lean` by T2382"; stale line `BA/FlowPins.lean:565` -> `:434`, and branch
  `FlowPins.lean:434` is `def STMainIndG`). No registry name changed. Registry pre-check (`import RBM3D` +
  `#assert_rbm_axioms`) exits 0 (above).
- No frozen signature touched (§1: all 176 constants unchanged). No new public name except the module.

## 5. Paper deltas
No Lean/paper statement changes (pure relocation); no candidate needed. The report proposes none. Covered.

## Observations (no effect on verdict)
- O1. The dispatcher check file contains 17 `#check` lines and no `example : <stmt> := <name>` lines that
  ticket target 3 describes; the kernel-level comparison in §1 covers every theorem of FlowPins instead,
  and the prover's report shows 62 generated examples elaborating.
- O2. Prove report (a)(ii) finding confirmed by the reverse cone above: `Induction/MainIndBase`,
  `MainIndChain`, `MainIndHolds`, `MainIndOut` reach `BA/FlowPins` today, contrary to the ticket's phrase
  "no chain file imports `BA/FlowPins`". Not affected by this move; the T/U/V restated files should import
  `Chain/Carrier`, not these four (dispatcher note, not a defect of this branch).
- O3. The moved section docstring in Carrier still says "the bridges below are `Iff.rfl`"; the bridges
  stay in FlowPins (text moved verbatim, as required).
- O4. Branch is based on 2192dea; main has since gained T2380 (`BA/KPure`, imports `BA/KMolecule`).
  Since all FlowPins constants are unchanged, no interaction is expected; the hub's full build at merge decides.

## Verdict
- Target 1 `RBM3D/Chain/Carrier.lean`: PASS.
- Target 2 `RBM3D/BA/FlowPins.lean`: PASS.
- Target 3 G1 checks: PASS (check file exit 0; all 176 constants unchanged).
- Target 4 registry: PASS.
**Overall: PASS.** No dispatcher sign-off needed.
