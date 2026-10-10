Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 12:06:22 UTC 2026

Scope: pure refactor (T2382, BA-T row 0). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2382` at `2192dea`, clean. No mathematics changes; "exponents" are the import set, the cones and the stop line. Evidence is from scripts in the scratchpad (import-graph scripts read `import` lines of `RBM3D/**/*.lean`; no Lean was written or run).

### (i) Table: moved block, per-declaration dependencies, import list, stop line

Moved block `BA/FlowPins.lean:315-466` (152 lines). Output of the per-declaration scan (names of the defining modules, checked against `grep`):

| declaration (FlowPins line) | external symbols used -> defining module | moves? |
|---|---|---|
| PrecL (328) | StochDomAt -> Defs/StochDomAt:61; Sizes -> Defs/Sizes:138 | yes |
| FlowFM (332) | Idx -> Defs/Sizes:46; Zd -> Defs/Lattice:63; Sizes | yes |
| FlowFM.GM (353) | FlowFM | yes |
| STLKgL (357), STLmaxgL (364), STKboundgL (424) | PrecL; Bctl -> Defs/Sizes:214 | yes |
| STDecaygL (371) | Bctl; zdistInf -> Defs/Sizes:115; ellT -> Defs/Params:32; **STWB -> Induction/Defs:69** | yes |
| STDecayStronggL (382) | Bctl; zdistInf | yes |
| STLocalMaxgL (392) | GM; Bctl | yes |
| STLocalEntrygL (398) | GM; **STWB, STblk -> Induction/Defs:69,73**; zdistInf | yes |
| STExp2gL (404) | integral over mu (MeasureTheory); Bctl | yes |
| STmaxLoop2g (412), STInitialGT2gL (417) | C.L, GM; Finset.sup' | yes |
| STStep1LoopgL (431), STStep1WeakgL (438) | TimeIcc -> Defs/StochDomAt:100; Bctl; GM | yes |
| STEEg (458) | C.S, C.L only | yes |
| **STJhatg (444)** | **STprof -> Induction/Step2Defs:75** | **no, stays** |
| **STLWassmExpgL (450)** | **STprof -> Induction/Step2Defs:75** | **no, stays** |

Scan of the 20 names declared in `FlowPins.lean:1-314` against the moved text: none used (output `used by block 315-466: []`). So the moved block depends on no other part of `FlowPins`.

| item | value | constraint | slack |
|---|---|---|---|
| import list of `Chain/Carrier.lean` | `RBM3D.Induction.Defs` only (supplies Sizes, Idx, Zd, StochDomAt, TimeIcc, Bctl, zdistInf, ellT, STWB, STblk, `Sizes.SeqΩ`) | at most `Induction/Defs`; never `Step2Defs`, `Step34Pins`, `BA/*` | 0 further imports; `Loop/KLTree`, `BA/MFixedPoint` not needed |
| `open` lines of Carrier | `MeasureTheory` (Measure, integral), `RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes` (copied from `FlowPins:313`) | names resolve as in `FlowPins` | n/a |
| namespace | `RBM.BA` | every moved name keeps its full name | n/a |
| stay in FlowPins | STJhatg, STLWassmExpgL (lines 443-454, 12 lines with docstrings) | need `STprof` (`Step2Defs:75`); ticket: stay with one line why | both unused outside `FlowPins` (STJhatg: no other use; STLWassmExpgL: `:513`, `:1506` inside FlowPins) |
| stayers' `variable` | a short `section` with `variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)` in the same order | argument order of both defs unchanged (`C μ t D ℓ`; `C n D ℓ u ω`) | n/a |
| stop line (binding) | est. Carrier 165 lines + \|net change of FlowPins\| 134 = 299 | <= 500 (ticket estimate 150 / 250 / 400) | 201 |
| Carrier size | 6 header + 1 import + 8 doc + 6 open/namespace + 140 moved + 4 end ~ 165 | wc -l | n/a |
| FlowPins net | -(140 moved + header of §4 reworded) +1 import +~5 for the stayers' section and the one "why" line ~ -134 | "loses exactly the moved block, gains one import line" | the stayers' section lines (~5) and the why line are an unavoidable addition; the auditor should expect them |
| registry (`Test/Axioms.lean`) | lines 133-136, 144 (`STLmaxgL, STKboundgL, STLKgL, STLocalMaxgL, STLocalEntrygL`) carry no file reference; line 143 cites `BA/FlowPins.lean:565` for `STMainIndG` (stays; the line number shifts by about -134) | names unchanged | edit of Axioms.lean optional (stale line number only) |

### (ii) Import-graph checks (concrete instance: the repository at `2192dea`)

Command (scratchpad script, import lines only): `python3 -I final.py` (graph of 426 modules). Verbatim output:

```
Carrier imports: ['RBM3D.Induction.Defs']
(ii-a) Carrier imports inside reverse cone of Induction.Defs (chain files above Defs): []
(ii-b) Induction.Defs forward cone meets reverse cone of Induction.Defs: []
(ii-c) forward cone of Carrier (modules): 35 ; contains BA.*: [] ; Step2Defs/Step34Pins/FlowPins: []
(ii-d) direct importers of BA.FlowPins in Induction/: ['RBM3D.Induction.MainIndBase']
(ii-e) chain files (Induction/, in reverse cone of Defs) that reach FlowPins: ['RBM3D.Induction.MainIndBase', 'RBM3D.Induction.MainIndChain', 'RBM3D.Induction.MainIndHolds', 'RBM3D.Induction.MainIndOut']
(ii-f) Induction/ files in reverse cone of Defs not reaching FlowPins: 111
(iii) rebuild cone of an edit of FlowPins: modules 37 (+ new Carrier, 1) lines 32232 ; LWExpCert* in it: [] ; in forward cone of FlowPins: []
(iii) other direct imports of FlowPins that are not BA/Graph/Induction: []
FlowPins lines 1583 ; block 315-466: 152 ; stays (443-454): 12
estimate Carrier lines 165 ; FlowPins net change -134 ; stop-line metric (|net|) 299 <= 500 : True
```

Reading of the output:
- (ii-a)/(ii-b): `Carrier` imports one module, `Induction/Defs`, whose forward cone (35 modules together with `Carrier`) contains no module that imports `Induction/Defs` (reverse cone: 313 modules). So `Carrier` imports none of the chain files above `Induction/Defs`, no `Step2Defs`/`Step34Pins`/`BA/*`; no cycle can arise from `FlowPins -> Carrier` or from a later `Step2Defs -> Carrier`.
- Discrepancy with the ticket text (finding, no effect on the move): the ticket and T2379 L1 say "no chain file imports `BA/FlowPins` today". On `2192dea`, `Induction/MainIndBase` imports `BA.FlowPins` directly, and `MainIndChain`, `MainIndHolds`, `MainIndOut` reach it through it (4 `Induction/` files; the already-generic `STBaseG`, `STMLOutG`, `STHorizonG`). They use only unchanged full names (`RBM.BA.*`) and keep importing `FlowPins`, which now imports `Carrier`: no edit needed. The restated T/U/V files must not import these four.
- (iii) The rebuild cone of an edit of `BA/FlowPins.lean` (reverse cone of `RBM3D.BA.FlowPins` plus itself): 37 modules, 32,232 lines (T2379 B8 measured 33 modules, 27,955 lines before later merges: same order). **No certificate module** (`Graph/LWExpCert*`, 6 modules) is in it, neither as dependant nor as dependency. Expected result (T2379 B8): confirmed. `Test/Axioms.lean` imports only `Lean`, so an edit there rebuilds nothing. New file `Carrier` adds 1 module (cone below it: 35 modules, unchanged).
- The nonempty instances of the moved predicates stay in `FlowPins` (section `FlowPinsInst`, `FlowPins.lean:1465-1506`, 21 `example` lines at `d = 3`: `STLK/STLmax/STDecay/.../STKbound ↔ …gL (bandFM sz0 …) (seqP sz0)`; `grep -c "^example"` gives 21). They are not part of the moved block and need no edit; they are the G1 check that every moved name still elaborates with the same statement.
- External hypothesis: none (the ticket has no external input); the concrete limit computation of TEAM §8 lesson 14 does not apply.

### Verdict

- Target 1 (`RBM3D/Chain/Carrier.lean`): **PASS**. Plan: 15 of the 17 listed declarations move (all but `STJhatg`, `STLWassmExpgL`, which need `STprof` from `Step2Defs`); imports exactly `RBM3D.Induction.Defs`; `open MeasureTheory` plus the `FlowPins:313` open line; `variable` line as in `FlowPins:350`.
- Target 2 (`BA/FlowPins.lean`): **PASS**. Delete `:315-442` and `:455-466` (keep section opening for the two stayers with one line saying why), add `import RBM3D.Chain.Carrier`; the rest (`bandFM`, `baFM`, `bandFM_*`, `baFMz`, `BAFlow`, `STMainIndG`, `FlowPinsInst`) untouched.
- Target 3 (G1 checks): **PASS** (no obstruction: names and statements unchanged; instances present as above).
- Target 4 (registry): **PASS**; no owner comment names a moved file; only a stale line number (`Axioms.lean:143`), optional.
- Stop line: **PASS** (estimate 299 of 500).
- Overall: **PASS**.

## (b) Script output — Sat Oct 10 12:20:06 UTC 2026 (stage 1b, commit b3ffbd9 on t/T2382; scripts in scratchpad T2382/)
```
# move table: line of each def/structure in `git show 2192dea:RBM3D/BA/FlowPins.lean` vs the branch (Carrier = RBM3D/Chain/Carrier.lean)
PrecL FlowPins:328 -> Carrier:50             | FlowFM FlowPins:332 -> Carrier:54
FlowFM.GM FlowPins:353 -> Carrier:75         | STLKgL FlowPins:357 -> Carrier:79
STLmaxgL FlowPins:364 -> Carrier:86          | STDecaygL FlowPins:371 -> Carrier:93
STDecayStronggL FlowPins:382 -> Carrier:104  | STLocalMaxgL FlowPins:392 -> Carrier:114
STLocalEntrygL FlowPins:398 -> Carrier:120   | STExp2gL FlowPins:404 -> Carrier:126
STmaxLoop2g FlowPins:412 -> Carrier:134      | STInitialGT2gL FlowPins:417 -> Carrier:139
STKboundgL FlowPins:424 -> Carrier:146       | STStep1LoopgL FlowPins:431 -> Carrier:153
STStep1WeakgL FlowPins:438 -> Carrier:160    | STEEg FlowPins:458 -> Carrier:168
STJhatg FlowPins:444 -> FlowPins:324 STAYS(STprof) | STLWassmExpgL FlowPins:450 -> FlowPins:330 STAYS(STprof)
$ python3 -I movecheck.py   # deleted FlowPins lines vs Carrier text
FlowPins: deleted old lines 134 ranges: [(315, 346), (351, 441), (454, 464)]
FlowPins: added new lines 3
  + 7 import RBM3D.Chain.Carrier
  + 316 /-! ## 4. Target 4 (moved, T2382): `PrecL`, `FlowFM`, `FlowFM.GM` and the generic predicates are in `RBM3D/Chain
  + 317 `STJhatg` and `STLWassmExpgL` stay here because they use `STprof` of `Induction/Step2Defs`. -/
deleted non-blank lines missing from Carrier (in order): []
Carrier body equals old lines 315-442 + 455-466 (non-blank lines): True
$ git diff --numstat main...t/T2382; wc -l RBM3D/Chain/Carrier.lean   # scope; stop line 178 + |3-134| = 309 <= 500
3	134	RBM3D/BA/FlowPins.lean
178	0	RBM3D/Chain/Carrier.lean
2	2	RBM3D/Test/Axioms.lean
178 RBM3D/Chain/Carrier.lean
$ python3 -I imports.py   # import lines of RBM3D/**/*.lean
direct imports of Carrier: ['RBM3D.Induction.Defs']
forward cone of Carrier (modules): 35
forward cone meets chain files above Induction.Defs (reverse cone of Induction.Defs, 314 modules): []
forward cone contains Step2Defs/Step34Pins/BA.*/FlowPins: []
direct importers of Carrier: ['RBM3D.BA.FlowPins']
modules in reverse cone of FlowPins (rebuild cone minus itself): 36 ; LWExpCert* among them or in its forward cone: []
$ lake build RBM3D.Chain.Carrier | tail -1; lake build RBM3D.BA.FlowPins | tail -1
Build completed successfully (3313 jobs).
Build completed successfully (3735 jobs).
$ lake build > full4.log; echo exit $?; grep -n "axiom audit" full4.log | cut -c1-140; tail -1 full4.log
exit 0
4220:info: RBM3D.lean:429:0: axiom audit: 11013 theorems, 3223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4198 jobs).
$ lake env lean docs/tickets/checks/T2382-check.lean >/dev/null; echo exit $?   # 17 #check lines
exit 0
$ lake env lean G1.lean >/dev/null; echo exit $?   # 62 generated `example : ∀ binders, stmt := @name`
exit 0
$ python3 -I cmp.py   # before.txt: pp.all type and def value of every constant of the FlowPins+Carrier modules on main 2192dea; after.txt: on the branch
non-aux constants before/after: 173 173
only before: []
only after: []
changed (type or value, modulo aux-proof names): []
aux-only before: []
aux-only after: ['RBM.BA.STDecaygL._proof_3', 'RBM.BA.STJhatg._proof_2']
$ lake env lean axioms.lean | sed "s/^.RBM.BA.[A-Za-z0-9.]*. //" | sort | uniq -c   # #print axioms of the 18 table names
  17 depends on axioms: [propext, Classical.choice, Quot.sound]
   1 does not depend on any axioms
$ grep -rhoE "^(def|structure) (PrecL|FlowFM|...18 names)( |$)" RBM3D | sort | uniq -c | awk "\$1>1"   # duplicates
(none)  declarations found: 18
$ git diff -U0 main...t/T2382 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]" | cut -c1-100
-   -- T2197 (BA-C1a, DECISIONS §20): the block Anderson chain pins over a law (`RBM3D/BA/FlowPins.l
+   -- T2197 (BA-C1a, DECISIONS §20): the block Anderson chain pins over a law (`RBM3D/BA/FlowPins.l
-   `RBM.BA.STMainIndG, -- `lem:main_ind` over a carrier `(law, Flow, mk, T0)` (`BA/FlowPins.lean:56
+   `RBM.BA.STMainIndG, -- `lem:main_ind` over a carrier `(law, Flow, mk, T0)` (`BA/FlowPins.lean:43
$ grep -c "gL (bandFM sz0" RBM3D/BA/FlowPins.lean   # nonempty instances at d = 3 (section FlowPinsInst), unchanged
12
```
Narrative:
- Moved 16 declarations (`PrecL`, `FlowFM`, `FlowFM.GM` and 13 predicates `STLKgL` ... `STEEg`) into `RBM3D/Chain/Carrier.lean`, namespace `RBM.BA`; the only import is `RBM3D.Induction.Defs`. `STJhatg`, `STLWassmExpgL` stay (they use `STprof`, `Induction/Step2Defs:75`) with the old `section Generic` / `variable` / `end Generic` lines.
- `BA/FlowPins.lean` loses 134 lines (the moved text) and gains 3: `import RBM3D.Chain.Carrier` and a 2-line comment (lines 316-317) saying what moved and why the two stay.
- Statements unchanged: `cmp.py` compares the pp.all type and value of all 173 non-auxiliary constants of the two modules before/after (whitespace and `_proof_N` names normalised); the two new auxiliary constants (`STDecaygL._proof_3`, `STJhatg._proof_2`) are compiler-generated.
- G1: `gen_g1.py` turns every public `theorem N binders : stmt` of main's `BA/FlowPins.lean` into `example : ∀ binders, stmt := @N` (62, including `bandFM_*`, `STMainInd_iff`, `baSelf_none_of_gt`, `BAm_eq_zero_of_gt`, `inst_*`); all elaborate on the branch. Not generated: 17 private theorems and `not_BAConArg_of_data` (its statement mentions the private def `BAConArg`); `cmp.py` covers them.
- Registry (`Test/Axioms.lean`, imports only `Lean`): two comment edits (a note that the `…gL` names moved; the `STMainIndG` line number 565 to 434); no name changed.
- Actuals against (a): Carrier 178 lines (estimate 165), FlowPins net -131 (estimate -134). The root import in `RBM3D.lean` is the hub's at merge; the full build above already contains `Carrier` through `FlowPins`.
## (c) Mathlib names: none new; the moved text compiles unchanged.
## (d) Open issues, paper-delta candidates
- Paper-delta candidates: none (a move; no Lean/paper statement changed).
- Finding (evidence in (a), ii): `Induction/MainIndBase` imports `BA/FlowPins` directly (`MainIndChain`, `MainIndHolds`, `MainIndOut` through it), against the ticket text "no chain file imports `BA/FlowPins`". Names unchanged, so no edit; the restated T/U/V files must not import those four.
- Observation: the moved section docstring still says "the bridges below are `Iff.rfl`"; the bridges stay in `BA/FlowPins.lean` (text moved unchanged, as the ticket asks).
