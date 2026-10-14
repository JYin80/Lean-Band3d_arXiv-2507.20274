Auditor model: claude-opus-5-5
# T2508 row a audit (round 2): targets 1-8, branch `t/T2508` (5d7f96f7, merge base 22467000)
Written Wed Oct 14 14:43:20 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2508-audit2` (detached at 5d7f96f7).
Scratch (uncommitted): `<scratchpad>/T2508/AuditT2508.lean` = check lines 1-40 + `import` of the three new modules + check lines 41-247 (Part 1, Part 2 verbatim)
+ auditor pin examples + `#print axioms` of every public declaration of the three files (28 names, extracted by `grep -E '^(theorem|def) '`).

## 0. The repair (round-1 RETURN items 1-4)
```
$ git diff --stat b6b262b5 5d7f96f7
 RBM3D/Chain/ExpIntEasyGen.lean | 28 ++++++++++++++++------------
 RBM3D/Chain/ExpIntIGen.lean    | 12 ++++++------
```
The diff only removes `hduh` from the examples `ExpIntEasyGen:427, :438, :447` and `hduh`, `hDuQ` from `ExpIntIGen:749`, passing
`st6_duhEq_of_ping (STExpDuhamelZ_to_gL 3 _ (stExpDuhamelZ_holds 3)) _ flow_z0|flow_zG|flow_zB …` and
`fun Cq c ϑ hϑ => st6_duhEqQ_of_ping (STExpDuhamelQ_to_gL 3 _ (stExpDuhamelQ_holds 3)) _ flow_zB … Cq c ϑ hϑ`; docstrings updated. No statement, signature,
registry or import line changed. Items 1-3 done exactly; item 4 (prove report repair section) present (`T2508-prove.md:156-199`).

## 1. Build, axioms, diff scope
```
$ lake build RBM3D.Chain.ExpWardIIGen RBM3D.Chain.ExpIntEasyGen RBM3D.Chain.ExpIntIGen
Build completed successfully (3959 jobs).     exit 0; 'error' lines: 0; warnings: style linter (long lines) only
$ grep 'Built' build.log | awk '{print $4}'      -> RBM3D.Chain.ExpIntEasyGen, RBM3D.Chain.ExpIntIGen, RBM3D.Chain.ExpWardIIGen  (no band file rebuilt)
$ lake env lean <scratch>/AuditT2508.lean        exit 0; ': error' count 0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"  -> 28   (of 28 #print axioms; other axiom lines: none)
$ git diff --name-only main...t/T2508
RBM3D.lean
RBM3D/Chain/ExpIntEasyGen.lean
RBM3D/Chain/ExpIntIGen.lean
RBM3D/Chain/ExpWardIIGen.lean
RBM3D/Test/Axioms.lean
$ git diff --name-only main...t/T2508 -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Main | wc -l          -> 0
$ grep -nwE 'sorry|admit|axiom|native_decide' (three new files) | wc -l                                  -> 0
$ grep -hE '^import' (three new files) | grep -cE 'RBM3D.BA|Step2Kern'                                    -> 0
$ grep -nE '^(noncomputable )?(def|abbrev|structure) ' (three new files)
RBM3D/Chain/ExpIntIGen.lean:62:def STExpIntQConclgL' …      RBM3D/Chain/ExpIntIGen.lean:76:def STExpIntIgL' …     (exactly the two allowed, X1-C4)
$ wc -l ExpWardIIGen ExpIntEasyGen ExpIntIGen   -> 435 482 835 = 1752 (stop line 2,450; each file < 2,000)
```
`RBM3D.lean`: `+import RBM3D.Chain.ExpWardIIGen`, `+…ExpIntEasyGen`, `+…ExpIntIGen` (3 lines). `Test/Axioms.lean`: block header "V1s2'/V1s3'" -> "V1s2′ (T2506), V1s3′ (T2508)";
`STExpWardIIgL`, `STExpIntIIIgL`, `STExpIntIVgL` producer text; `owedProps += STExpIntIgL'` (owner T2508 row b); `structuralProps += STExpIntQConclgL'`. Matches the
ticket's "Registry" and decision (7). Only sole writable files touched; no frozen signature edited.

## 2. Statements against the pins (compiled script, `AuditT2508.lean`, exit 0)
```
example … : T2508_ExpIntQConclgL' C μ s t ↔ STExpIntQConclgL' C μ s t := Iff.rfl                                   -- target 5
example … : T2508_ExpIntIgL' d law Flow mk T0 ↔ STExpIntIgL' d law Flow mk T0 := Iff.rfl                          -- target 5
example … : T2508_CaseICoreg' C μ := fun hd h𝔡 hadm => st6_caseI_coreg' C μ hd h𝔡 hadm                            -- target 7
example … (hP : T2508_ConsumerPrem d law Flow mk T0) : T2508_Step6IAvgUgL d law Flow mk T0 :=
  ST_step6_caseI_of_pinsgL'' hP.1 hP.2.1 … hP.2.2.2.2.2.2.2.2.2.2.2                                                 -- target 8
example … : T2508_ConsumerOf d law Flow mk T0 := ⟨fun hP => ST_step6_caseI_of_pinsgL'' …, fun hP hC => ST_step6_caseI_of_pinsgL''_core … hC⟩
example … : T2508_RowAOf d law Flow mk T0 Ker gK := fun hB =>
  ⟨fun hRep hK1 hWI hB45 => stExpWardIIgL_of hB.1 hB.2.2.1 hRep hK1 hWI hB45,
   fun hS hK => ⟨stExpIntIIIgL_of gK hB.1 hB.2.2.1 hS hK, stExpIntIVgL_of gK hB.1 hB.2.2.1 hS hK⟩⟩                 -- targets 2, 4
```
The binding texts (`T2508_ExpIntQConclgL'`, `T2508_ExpIntIgL'`, `T2508_CaseICoreg'`, `T2508_Step6IAvgUgL`) are definitionally the Lean statements or obtained by
direct application in the pinned premise order; the non-binding `T2508_ConsumerOf`, `T2508_RowAOf` follow (`RowAOf` uses only rows 1, 3 of `FamBase`).
Targets 1, 3, 6 (unpinned helpers): read at their signatures (`ExpWardIIGen:132-195`, `ExpIntEasyGen:50, :200, :228`, `ExpIntIGen:202, :300, :369`): the band `|E|<2`/`etaT`
data are replaced by `κm ≤ Im m`, `η = (1-u) Im m`, the kernel class at `gK` with R1 only in `ExpIntIGen` (`hAof : 1 ≤ Aof κm`, the `gK²≤lam²≤Aof gK²` window) —
general carrier, no special case, no extra quantifier; `STIngR6gL` tuple order, no `∃` after `(sz, z)`, no `∀ n` hierarchy or drift premise.

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE 'STImproveExpAver|st6_expAvgU_of_pin|stImproveExpAver_holds|hAvg :' (three new files)   [V1L-C1]
ExpWardIIGen.lean:238: … (hAvg : STExpAvgUgL C …                    -- target 2 statement: per-flow average (allowed)
ExpWardIIGen.lean:338, :408; ExpIntEasyGen.lean:22; ExpIntIGen.lean:29, 30, 542, 615, 616   -- docstrings / instance example
ExpIntIGen.lean:625, :634: stImproveExpAvergL_of …, st6_expAvgU_of_ping …   -- inside proofs of the band re-derivations (V1L-C1 (ii))
```
- No new structure; the two new defs are Prop twins of band `STExpIntQConcl'`, `STExpIntI'` (`bandFM_STExpIntQConcl'` iff; `STExpIntI'_of_gL'` one way, D725).
- `STExpIntIgL'` is an unproved premise of target 8 and of the band re-derivations; registered in `owedProps` (owner T2508 row b). Imports are merged modules only: no cycle.
- Family premises of the endpoint producers are jointly satisfiable: `stExpWardIIgL_of`, `stExpIntIIIgL_of`, `stExpIntIVgL_of` are applied at the band tuple `d = 3`
  with no hypothesis left (examples `ExpWardIIGen:417`, `ExpIntEasyGen:458, :463`).

## 4. Compiled nonempty instances (hypotheses kept by each `example`, extracted by script)
Data: `szB/zB` `(7/8, 15/16)` regime (i) and `(15/16, 31/32)` regime (ii); `sz0/z0` `(0, 1/16)` regime (iii); `szG/zB` `(5/8, 3/4)` regime (iv); `d = 3`; all `s < t < 1`.
```
ExpWardIIGen:366/379/393: hyps = (none)          ExpWardIIGen:408: hyps = hAvg      ExpWardIIGen:417, :427: hyps = (none)
ExpIntEasyGen:391: hyps = h τ hτ                 ExpIntEasyGen:405, :416, :427, :438, :447: hyps = hDr      ExpIntEasyGen:458, :463, :470, :474: hyps = (none)
ExpIntIGen:666, :670: hyps = h                   ExpIntIGen:679: hyps = τ hτ        ExpIntIGen:723: hyps = hdr hdd     ExpIntIGen:736: hyps = hker
ExpIntIGen:749: hyps = hlk hegt hdec hAvgU hward hini hint                         ExpIntIGen:773: hyps = hLW hInt
ExpIntIGen:788: hyps = hLW hInt hLK0 hDec0 hExp hS2 hLmax hLKU hS5                 ExpIntIGen:818, :824: hyps = hLW hInt
```
| target | example | kept hypotheses (class) | status |
|---|---|---|---|
| 1 | ExpWardIIGen:366, 379, 393 | none | ok |
| 2 | :408 / :417 | `STExpAvgUgL` (row 21, V1-BA via 16c) / none | ok |
| 3 | ExpIntEasyGen:391, 405, 416 | expected-drift bound / `STExpDriftHi/LoConclgL` (T2506 pins, `LWtermEXPG`) | ok |
| 4 | :427, :438, :447 | `hDr` only; Duhamel now discharged by `stExpDuhamelZ_holds` (round-1 defect fixed) | ok |
| 4 | :458, :463 | none | ok |
| 5 | ExpIntIGen:666, :670 | band conclusion / `STExpIntIgL'` (row b) | ok |
| 6 | :679 / :723 / :736 | none / drift pins / kernel drift bound (T2506) | ok |
| 7 | :749 | pin conclusions at the tuple (`hlk`,`hegt`,`hdec`,`hward`,`hini`: need the stochastic `STIngR6gL` premises), `hAvgU` (row 21), `hint` (`STExpIntIgL'`, row b); `hduh`, `hDuQ` discharged (round-1 defect fixed) | ok |
| 8 | :773 / :788 | `LWtermEXPG`, `STExpIntIgL'`, stochastic `STIngR6gL` premises at `s` | ok |
Every remaining hypothesis is a stochastic induction premise or another gate's pin; every deterministic one is discharged. No `N = 0`, empty index, collapsed window or `False` premise.

## 5. Paper deltas
- Eventual Duhamel and one-way `STExpIntI'_of_gL'`: D725 (`docs/paper-deltas.md:1808`). Per-flow average on `[s,t]`: D727 (`:1813`) / V1L-C1.
- Proposed `T2508a` (band regime-(i) consumers re-derived with generic `hInt`), `T2508b` (constants `3 κm⁻¹` vs band `6/√(2κ)`, `4 Aof²` vs band 4) in
  `T2508-prove.md:152-153`: Lean-internal, adequate. The repair changes no statement, so no new delta.

## 6. Verdicts
| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 | ok | ok | ok | ok | ok | PASS |
| 2 | = `T2508_RowAOf` conj. 1 | ok | ok | ok | ok | PASS |
| 3 | ok | ok | ok | ok | ok | PASS |
| 4 | = `T2508_RowAOf` conj. 2 | ok | ok (repaired) | ok | ok | PASS |
| 5 | `Iff.rfl` with both pins | ok | ok | ok | D725 | PASS |
| 6 | ok | ok | ok | ok | ok | PASS |
| 7 | = `T2508_CaseICoreg'` | ok | ok (repaired) | ok | ok | PASS |
| 8 | = `T2508_Step6IAvgUgL`, `T2508_ConsumerOf` | `STExpIntIgL'` owed (row b) | ok | ok | D727 | PASS |

**Overall: PASS.** No dispatcher sign-off needed.

## 7. Observations (no verdict effect)
- O1: the band re-derivations `stExpWardII_gen_band`, `stExpIntIII_gen_band`, `stExpIntIV_gen_band`, `ST_step6_caseI_of_pins''_gen_band`, `ST_step6I_of_LW_Int_gen_band`
  are public and carry a `_gen_band` suffix, not the file stem prefix asked by the ticket ("re-derivations carry the file stem", T2506b O1; CLAUDE.md §3 (E)).
  Name-clash grep on `main` (all 28 public names, `git grep` for `theorem|def|lemma <name>`): 0 hits each. Naming only.
- O2: the sum-zero branch of `hpin` in `expIntI_kernel_unifg` has no instance in row a; row b's `expIntIQ_inig` is its first reader (as round 1 O1).
- O3: `main` is at b4147edc, past the merge base 22467000; the hub's full `lake build` at merge covers the union of `Test/Axioms.lean`/`RBM3D.lean` lines.
