Auditor model: claude-opus-5-5
# T2478 audit, round 1 (T1a = targets 1-6) — Tue Oct 13 00:37:57 UTC 2026

Branch `t/T2478` HEAD `1f0c2b4e`, merge-base `2dcfcda5`; audit worktree `RBM3D-wt/T2478-audit1` (detached at `1f0c2b4e`).
Scope: T1a only (`Chain/Step2IterGen.lean`, `Chain/Step2IterGen2.lean`, TLC-2 owner texts in `Test/Axioms.lean`); targets 7-11 are T1b
(stacked branch, pre-signed split, answer (1)). Scratch files: `<scratchpad>/T2478/lean/{audit,audit2,axioms,scan}.lean`.

**Verdict: PASS** (targets 1-6, answer (6) texts). No RETURN item. No dispatcher sign-off needed.

## 1. Statements against the pins (script diff by compilation)
`audit.lean` = check file lines 1-406 (Part 1 `#check`s + every binding `T2478_*` def, copied by `sed`) + `import RBM3D.Chain.Step2IterGen2` + these lines:
```
example … : T2478_NewKLKAtN Cm n C δ₀ ↔ Step2IterGen_NewKLKAtN Cm n C δ₀ := Iff.rfl
example … : T2478_NewKLK d Flow mk ↔ Step2IterGen_NewKLK d Flow mk := Iff.rfl
example … : T2478_K2 d Flow mk ↔ Step2IterGen_K2 d Flow mk := Iff.rfl
example … : T2478_OneLoop C ↔ Step2IterGen_OneLoop C := Iff.rfl
example … : T2478_SelfImpgL C μ Cd s t Kf ↔ STSelfImpgL C μ Cd s t Kf := Iff.rfl
example : T2478_GoodEngineg := @ST_good_engineg
example : T2478_Step2OfPinsg := @ST_step2_of_pinsg
example (h : T2478_GoodEngineg) : type_of% @ST_good_engineg := h          -- converse direction
example (h : T2478_Step2OfPinsg) : type_of% @ST_step2_of_pinsg := h
example … : STSelfImp sz Cd E s t Kf ↔ T2478_SelfImpgL (bandFM sz E) (Sizes.seqP sz) Cd s t Kf := Iff.rfl
$ lake env lean <scratch>/lean/audit.lean > audit.out; echo exit $?; grep -c ": error" audit.out
exit 0
0
```
The pins and the Lean statements agree in both directions (hypotheses, quantifier order, `C_d = 3C+1` constants, windows `0 ≤ u < 1`,
`s n ≤ u ≤ t n`, `STprof … (sz.L n)`; the skeleton's only grid premise is `STGridMartgL`; conclusion `STStep2G … (mk sz z).toFlowFM`).
Targets 3 (step lemmas), 4, 5 have shapes only in the ticket; checked against the band by re-derivation (§3).
Differences from the ticket text (not from a pin), all equivalent or more general:
- `ST_selfImprove_sectiong`/`ST_selfImproveg` take `STGridMartgL` (`∃ C₀`) instead of `STGridMartAtgL d C₀`: weaker premise, more general result.
- `ST_avgU_of_avgg`, `ST_concl_of_step2g` take the unfolded `STStep2AvggL`, `STLocalEntryUgL`, `STGdecayWgL`; definitional: the instances
  at `Step2IterGen2.lean:453, 457` pass `h : STStep2AvggL …`, `STStep2LocalgL …`, `STStep2DecaygL …` directly and compile.
- `ST_avgU_of_avgg` adds `0 ≤ s n`, `t n < 1`, forced by the pinned window of `Step2IterGen_OneLoop`; both hold inside `STStep2G`
  (the skeleton discharges them, `Step2IterGen2.lean:371`). Covered by candidate T2478b.

## 2. Hidden hypotheses, vacuity, cycles
- New `def`s are five `Prop` classes (`Step2IterGen_NewKLKAtN/NewKLK/K2/OneLoop`, `STSelfImpgL`), no structure, no new carrier field:
```
$ git grep -nE "^(noncomputable )?def" t/T2478 -- RBM3D/Chain/Step2IterGen.lean RBM3D/Chain/Step2IterGen2.lean
Step2IterGen.lean:50 Step2IterGen_NewKLKAtN   :63 Step2IterGen_NewKLK   :71 Step2IterGen_K2   :81 Step2IterGen_OneLoop   :447 STSelfImpgL
```
- Each class has a band discharge that is a closed theorem: `step2IterGen_newKLK_band` (from `stNewKLK_holds`), `step2IterGen_K2_band`
  (`ST_K2e_of_flow`), `step2IterGen_oneLoop_band` (`ST_Kloop_one`, `ST_Lloop_one_false`), instantiated in §4.
- Cycle: `ST_step2_of_pinsg` reads `STOptL2gL`, `STLocalAvgOfL2gL`, `STNetLift2gL`, `STScaleExistsgL`, `STBdatagL`, `STGridMartgL`,
  `STLWTgL`, `STEMn2ExpgL` (merged pins of `Chain/Step2Gen`, `Step2EventsGen`) and the target-1 classes; none of them has `STStep2G` as a
  premise (check file pins, `T2478_OptL2OfPinsg` takes no Step 2 conclusion). No external hypothesis is introduced.
- Registry: one new owed line `STOptL2gL` (needed: not on `main`, scan lists `RBM.BA.STOptL2gL: 2 [no certificate]`); concluded by T1b.

## 3. Band re-derivations (G1 content)
In the branch files (compiled with the module): `type_of% @ST_good_engine`, `@ST_selfImprove`, `@ST_next`, `@ST_decay_of_final`
(`Step2IterGen.lean:1224-1257`), `@ST_iterate`, `@ST_decay_pt`, `@ST_L2_decay_pt`, `@ST_base_inv` (`Step2IterGen2.lean:518-532`),
`step2IterGen_step2_of_pins_band` (`:394`). Auditor's addition:
```
$ cat audit2.lean   # import RBM3D.Chain.Step2IterGen2
example : type_of% @RBM.Gauss.Sizes.ST_step2_of_pins  := fun {d} _ hLWT hEMe hMart _ _ _ hOpt hClos => step2IterGen_step2_of_pins_band d hLWT hEMe hMart hOpt hClos
example : type_of% @RBM.Gauss.Sizes.ST_step2_of_pins' := fun {d} _ hLWT hEMe hMart hOpt hClos => step2IterGen_step2_of_pins_band d hLWT hEMe hMart hOpt hClos
$ lake env lean <scratch>/lean/audit2.lean | grep -c error ; echo exit
0   exit 0
```
Part 3 names keep their statements: the band files are not touched (§5 G1 diff empty).

## 4. Compiled nonempty instances (d = 3, `sz0`, `z0`, `flow_z0`, κ = ε = 𝔡 = 1/10, 𝔠 = 1/6, window `[0, 1/16]`)
| endpoint | instance (file:line) | discharged at the data | left as hypothesis |
|---|---|---|---|
| T1 `_newKLK_band`, `_K2_band`, `_oneLoop_band` | IterGen 1098, 1102, 1108 | everything (flow, `hs0`, `ht1`) | none |
| T2 `ST_good_engineg` | IterGen 1115 (n = 100, K ≡ 16, D = 1/2, Λ = C = 1, q = 1/10) | `hK`, window, F3 `DecayGen_bandSpec`, `lam_pos`, `hTmono`, `hb1`, `hsmall` (`core_small`), Hermitian walk | class at `(n=100, C=1)`, `STGoodAtg` |
| T3 `ST_nextg`, `ST_decay_of_finalg` | IterGen 1154, 1161 | `hK2_sz0`, `hq_sz0`, `Kseq0_adm`, `hqW`, `hq0` | `STSelfImpgL` |
| T3 `ST_selfImprove_sectiong`, `ST_selfImproveg` | IterGen 1182, 1202 (`tt ≡ 1/32`, 𝔠d = 1/240) | F1-F3, F9, Hermitian walk, `bdata_spec`, `conStInd_inst`, `Kseq0_adm` | pins `STLWTgL`, `STEMn2ExpgL`, `STGridMartgL`; class `∀ᶠ n, …NewKLKAtN … 1 (1/10)`; `STDecaygL`, `STStep1WeakgL`, `STScaleInvgL` |
| T4 `ST_iterateg`, `ST_decay_ptg`, `ST_L2_decay_ptg`, `ST_base_invg` | IterGen2 422, 431, 439, 444 | `sz0_tendsto`, `hst`, `CK0_pos`, `hK2_sz0`, `hq_sz0`, `Kseq0_adm`, `sz0_bandwidth` | `hSelf`/`hbase`/`hdec`/`hOpt` (stochastic) |
| T5 `ST_avgU_of_avgg`, `ST_concl_of_step2g` | IterGen2 453, 457 | `OneLoop` (band), `hs0`, `ht1` | the Step 2 conclusions |
| T6 `ST_step2_of_pinsg` | IterGen2 488 → `Step2IterGen2_inst_step2` (sz0, z0, s ≡ 0, t ≡ 1/16) | F1-F3, F9, Hermitian, OneLoop, `STBdatagL`, `NewKLK`, `K2`, `STNetLift2gL`, `STScaleExistsgL` | `STLWTgL`, `STEMn2ExpgL`, `STGridMartgL` (TN-C4 forbids `stGridRepN_holds`), `STOptL2gL` (T1b), `STLocalAvgOfL2gL` |
| band readings `stBdatagL_band`, `stScaleExistsgL_band`, `step2IterGen_step2_of_pins_band` | closed (`0 < d` only); IterGen2 509 at d = 3 | — | band pins |
No `N = 0`, empty index, collapsed window (`[0, 1/16]`, `K ≡ 16`) or `False` premise. Observation O1 on the C = 1 class below.

## 5. Build, axioms, hygiene, diff, layering
```
$ lake build RBM3D.Chain.Step2IterGen RBM3D.Chain.Step2IterGen2 2>&1 | grep -c "^error"; … | tail -1
0
Build completed successfully (3812 jobs).
$ grep -E "Step2IterGen" build.log | grep -vE "longLine|exceeds|^⚠"   (non-style warnings)
warning: RBM3D/Chain/Step2IterGen.lean:630:2: The `show` tactic should only be used to indicate intermediate goal states for readability.
warning: RBM3D/Chain/Step2IterGen.lean:1036:2: The `show` tactic should only be used to indicate intermediate goal states for readability.
$ lake env lean axioms.lean | sed "s/'RBM.BA.[^']*'//" | sort | uniq -c      # #print axioms of all 26 public theorem/def
  26  depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D | tail -1 ; lake env lean scan.lean   # import RBM3D + both modules + #assert_rbm_axioms
Build completed successfully (4316 jobs).
exit 0
axiom audit: 14110 theorems, 4457 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 62, structural 45, refuted 6, superseded 14).
$ git show t/T2478:<both files> | grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^private axiom" | wc -l
0
$ git diff --name-only main...t/T2478
RBM3D/Chain/Step2IterGen.lean
RBM3D/Chain/Step2IterGen2.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2478 --stat -- RBM3D/Induction RBM3D/Path RBM3D/Evolution RBM3D/BA RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/Carrier.lean 'RBM3D/Chain/DecayGen*.lean' 'RBM3D/Chain/Step2EventsGen*.lean' RBM3D/Chain/NewKLKGen.lean RBM3D/Chain/CltGen.lean | wc -l
0
$ lake env lean docs/tickets/checks/T2478-check.lean; echo exit $?; grep -c ": error"
exit 0
0
$ grep -c '^import RBM3D.BA' (both files); git grep -n "import RBM3D.Chain.Step2IterGen" t/T2478 -- RBM3D RBM3D.lean
0
t/T2478:RBM3D/Chain/Step2IterGen2.lean:6:import RBM3D.Chain.Step2IterGen
$ python3 cone (transitive imports of Step2IterGen2)
cone(Step2IterGen2): 111 modules; RBM3D.BA.*: 0
$ TN-C4: grep -nE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" (both files) | wc -l     -> 0
$ UBA-C1: grep -nE "gK|BAflowLam0|withLam|lam0" (both files) | wc -l                           -> 0
$ X1-C1 grep, hit lines:
Step2IterGen.lean: 80 92 94 95 105 114 116 121 125 128 130 131 133 457 1085-1257 (band discharges 92-133, bridge 457, instances)
Step2IterGen2.lean: 312 378 384 398-411 423-532 (312 = `Step2IterGen_NewKLK` false positive on `KLK d`; 378-411 band readings; instances)
$ grep -nE "\.lam\b": 95 105 (band discharge) 146 151 152 (target 2: `0 ≤ sz.lam n`, `tailT`) 482-958, IterGen2 140 159 (inside `tailT`/`ellT` in proofs)
```
`RBM3D.lean` is not edited (hub adds the two imports at merge). Frozen signatures: none touched (diff limited to three files).
`Test/Axioms.lean` TLC-2 texts (answer (6)), scripted:
```
BATwistAvgLaw endswith answer(6) text: True
BATwistLoopLaw endswith answer(6) text: True
```

## 6. Paper deltas
Candidates in the prove report (d): T2478a (Step 2 iteration over the carrier, `lem:newKLK` and the `𝒦^{(2)}` decay as carrier classes),
T2478b (`Step2IterGen_OneLoop` window `0 ≤ u < 1`, and the window premises of `ST_avgU_of_avgg`), T2478c (`STGridMartgL` with `C₀` inside;
unfolded premises of target 5). Every Lean/statement difference found in §1 is covered. No uncovered delta.

## Observations (no RETURN)
- O1. The T2/T3 instances keep the class `Step2IterGen_NewKLKAtN` at `C = 1` (T2 at `n = 100`; T3 `∀ᶠ n`, δ₀ = 1/10) as a hypothesis,
  as the merged band instances do (`Step2Core.lean:1726` `STNewKLKAt 3 (1/10) (1/10) 1 δ₀`; `Step2Iterate.lean:1938`). For T2 a fixed
  `C` is needed for the numeric `hsmall` at fixed `n`; for T3 the class could be discharged by `step2IterGen_newKLK_band` with
  `𝔠d := 1/(60(3C+1))`. The T6 instance does discharge `Step2IterGen_NewKLK` and runs `ST_selfImproveg`/`ST_selfImprove_sectiong` inside.
- O2. `ST_avgU_of_avgg`/`ST_concl_of_step2g` state `STStep2AvggL` unfolded "so that no premise outside the registry enters the signature"
  (docstring, `Step2IterGen2.lean:264`); the band form `STStep2Avg` is registered (`Test/Axioms.lean:167`). The statement is unchanged
  (definitional), but the scan no longer sees this premise by name; for the dispatcher's registry bookkeeping.
- O3. `Test/Axioms.lean` conflicts textually with `main` (`git merge-tree`: T2479's block and the `STOptL2gL` line at the same
  insertion point before `STExp2U]`); resolution is the union of lines (ticket "Sibling scan").
- O4. The prove report has 254 lines (ticket asks ≤ 200; CLAUDE.md §6 cap 300). Two non-style linter warnings (`show`, lines 630, 1036).
- O5. `Step2IterGen` imports `Induction/NewKLK` beyond the ticket layout (for `stNewKLK_holds`); not a `BA/*` module, cone has 0 BA modules.
