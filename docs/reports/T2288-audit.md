Auditor model: claude-opus-5-5

# T2288 audit (round 1): LW-14e-D, design/probe for the leaf half of LW-14e (report-only)

Written Tue Oct  6 14:28:27 UTC 2026 (date -u). Branch `t/T2288` at 5f3d37f, audit worktree `RBM3D-wt/T2288-audit1` (detached).
Inputs: the ticket, its check file, `docs/reports/T2288-prove.md`, `docs/reports/T2288-portmap.md`. Scratch: `scratchpad/T2288/audit1/`.

## 1. Scope and hygiene
```
$ git diff --stat main...t/T2288
 RBM3D/Probe/T2288Cert.lean | 1228 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1228 insertions(+)
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Probe/T2288Cert.lean      -> (no lines)
$ grep -n "^namespace\|^end RBM" ; first declaration
45:namespace RBM.Probe.T2288
1228:end RBM.Probe.T2288
55:def LWJoined (P : PGraph (Fin 2)) : Prop :=
$ grep -c "decide +kernel"  -> 185
$ imports: LWExpTerm3 LWExpTerm2 LWGGExp LWWeightExp LWStein LWVocab LWSymm LWLvl1 ScalingOrder AnpKey5 Defs.Semicircle (all permitted)
```
Only the sole writable probe file is touched (reports live in the main worktree); no merged file and no frozen signature are changed.
`decide +kernel` is the use that DECISIONS §95 allows for target 1 (B); there is no `native_decide`.

## 2. Build and axioms (whole probe, audit worktree)
```
$ lake build <the 10 imported RBM3D.Graph modules> RBM3D.Defs.Semicircle   -> Build completed successfully (3885 jobs).
$ /usr/bin/time -l lake env lean RBM3D/Probe/T2288Cert.lean    # Tue Oct  6 14:08:55 -> 14:26:29 UTC 2026
'RBM.Probe.T2288.cert_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.inner_node_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.root_FF_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.root_FT_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.cands_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.Rel.cand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.Rel.leaf_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.Rel.scalingOrder_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.lwSplitLoopsX_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.goodB_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.lwG5ExpandSplit_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.lwG5ExpandOfHalves' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2288.lwG5LeafProps_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
     1053.46 real      1036.30 user        25.17 sys
          7521058816  maximum resident set size
exit 0
```
No error or warning lines. `cert_all` covers transitively all 22 `root_F*_i` theorems and every chunk theorem, and it has no `Lean.ofReduceBool` and no `sorryAx`.
Thresholds (5 min per declaration, 30 min per file, 8 GB): the file takes 17.6 min and 7.52 GB, so it is within all three.

## 3. Re-timed kernel theorems (standalone: probe lines 1-652/658 plus one theorem)
```
$ /usr/bin/time -l lake env lean AudInner.lean   # probe 1-658 (= inner_node_one) + #print axioms   (14:26:44 UTC)
'RBM.Probe.T2288.inner_node_one' depends on axioms: [propext, Classical.choice, Quot.sound]
        4.53 real         3.41 user         2.17 sys
          3647930368  maximum resident set size
$ /usr/bin/time -l lake env lean AudHeavy.lean   # probe 1-652 + line 819 `ch_FF_10_0_8` (heaviest chunk)   (14:26:49 UTC)
'RBM.Probe.T2288.ch_FF_10_0_8' depends on axioms: [propext, Classical.choice, Quot.sound]
       20.13 real        18.27 user         2.68 sys
          7084326912  maximum resident set size
```
These agree with the prove report (heaviest chunk: 22.21 s and 7.10 GB).

## 4. Non-degeneracy of the certified nodes (auditor's own kernel and `#eval` lines appended to probe 1-643)
```
theorem aud_root0_nonleaf : leaf (rootAt false false 0) = false ∧ (rootAt false false 0).g.scalingOrder = 3 ∧
    tgt (rootAt false false 0) = 4 ∧ (rootAt false false 0).b = 2 ∧ (cands (rootAt false false 0).g).length = 2 := by decide +kernel
theorem aud_roots_below : (rootInfo false false).2.all (fun N => !leaf N) = true ∧ (rootInfo false true).2.all (fun N => !leaf N) = true := by decide +kernel
'RBM.Probe.T2288.aud_root0_nonleaf' depends on axioms: [propext, Classical.choice, Quot.sound]
#eval (a, b, ord, tg, #cands) of the 11 below-target root terms, (k,s)=(F,F) and (T,F):
[(0, 2, 3, 4, 2), (1, 2, 4, 5, 2), (0, 2, 3, 4, 2), (1, 2, 4, 5, 2), (0, 2, 3, 4, 2), (1, 2, 4, 5, 2), (0, 2, 3, 4, 2),
  (1, 2, 4, 5, 2), (0, 3, 3, 4, 3), (0, 3, 2, 4, 3), (1, 3, 3, 5, 3)]          (identical list for k = true)
#eval (rootInfo true false).1 && (rootInfo true true).1  -> true
#eval all model children per candidate (Σ over fams of cPartition length), root terms 0..10 (F,F):
[[264, 264], [533, 533], [264, 264], [533, 533], [264, 264], [533, 533], [264, 264], [533, 533], [707, 653, 698],
  [533, 533, 533], [1125, 1125, 1125]]
#eval below-target children per candidate: [[0, 0], ..., [0, 0, 0], [12, 12, 12], [14, 14, 14]]
```
`inner_node_one` is a genuine inner node: ord 3 < tg 4, 2 internal vertices, 2 candidates and 528 children, all of them leaves.
The child counts equal the python route-(C) table (§6; the candidate order of term 8 differs).
The certificate is therefore not vacuous: no node is `default`, there is no empty candidate list, and no root term is a leaf.

## 5. Statement check: section-2 pins against the check file (script, `Iff.rfl`)
The script copies probe lines 1-106 and the check file's `namespace RBM.Gauss.Sizes … T2288Check` block verbatim.
It also copies T2265-check lines 190-191 (`LWJoinedPin`) and 197-207 (`LWG5Expand'Pin`) into `T2265C`, then adds:
```
example (P) : RBM.Probe.T2288.LWJoined P ↔ LWJoinedPin P := Iff.rfl          example (P) : … LWJoined P ↔ T2265C.LWJoinedPin P := Iff.rfl
example (P) : … LWG5Cand P ↔ LWG5CandPin P := Iff.rfl                          example (P) : … LWG5Progress P ↔ LWG5ProgressPin P := Iff.rfl
example Ls : … LWG5LeafProps Ls ↔ LWG5LeafPropsPin Ls := Iff.rfl              example d Ls : … LWG5Identity d Ls ↔ LWG5IdentityPin d Ls := Iff.rfl
example d : … LWG5ExpandSplit d ↔ LWG5ExpandSplitPin d := Iff.rfl             example d : … LWG5Expand' d ↔ T2265C.LWG5Expand'Pin d := Iff.rfl
example d : LWG5ExpandSplitPin d ↔ T2265C.LWG5Expand'Pin d := Iff.rfl
$ /usr/bin/time lake env lean PinAudit.lean  ->  3.71 real; exit 0
```
All six section-2 pins and `LWJoinedPin` agree up to names. The split is `Iff.rfl` to T2265's `LWG5Expand'Pin`, so the re-pin answer "the pin stays" holds.
The procedure statements compile (probe 183-213):
- `Sel` returns an `RCand` that carries the `LWG5Cand` fields, so the spec is built into the type.
- `LWExpandIdentity sel fuel` is generic in `sel` and `fuel`.
- `oe2x_graph_E` (`LWGGExp.lean:1550`) needs only the `RCand` fields (`hp`, `hp1`, `hq`, `hq1`, `hy`) and the data hypotheses. The identity half is therefore consistent with a generic `sel`.

## 6. Target 0 re-run (python, copies of the prover's scripts in `audit1/py`, Tue Oct  6 14:10:47 UTC 2026)
```
$ python3 summary.py      (10.2 s)
False False   30609   21219   21070 |   13263   13242    4104 |  13697    4104       0      0 |     3    11
False True    31159   19693   19552 |   13349   13303    4507 |      0    4507       0      0 |     3    11
True  False   30609   21217   21068 |   13263   13242    4104 |  13697    4104       0      0 |     3    11
True  True    31159   19691   19550 |   13349   13303    4507 |      0    4507       0      0 |     3    11
      min nW 2, max nM 1, min(ord-target): merged 0 distinct 0 joined 0 (all four rows)
$ python3 rules.py orig 8
R-orig k=False s=False: leaves 30609, inner by depth {0: 11, 1: 26, 2: 1} (total 38), stuck(no candidate) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 38}, hx2 {True: 38}
R-orig k=False s=True: leaves 31159, inner by depth {0: 11, 1: 26, 2: 2} (total 39), stuck(no candidate) 0, max leaf depth 3, largest partition 438, degree {2: 39}, hx2 {True: 39}
R-orig k=True s=*: identical to k=False
$ python3 rules.py any 6  -> same numbers as R-orig, "expanded vertex contains a created vertex: 0", all four rows
$ python3 rall.py         (13.6 s)
R-all k=False s=False: below-target root terms 11, distinct (up to iso) below-target nodes 125, stuck 0, cycles 0, max height of AND-tree 3, candidates examined 332, at created vertices 91, hx2 false 0, not-ok nodes 0
R-all k=False s=True: below-target root terms 11, distinct (up to iso) below-target nodes 129, stuck 0, cycles 0, max height of AND-tree 3, candidates examined 359, at created vertices 105, hx2 false 0, not-ok nodes 0
R-all k=True s=*: identical to k=False
$ python3 routeC.py; python3 routeC2.py   (11.4 s)
  9  2   4    2       3     [533, 533, 533] | ... | [12, 12, 12]
 10  3   5    2       3     [1125, 1125, 1125] | ... | [14, 14, 14]
s=False: increments by depth of the parent: {0: {1: 344, 2: 714, 3: 12350}, 1: {0: 36, 1: 3664, ...}, 2: {...}}
s=True:  increments by depth of the parent: {0: {1: 344, 2: 714, 3: 12350}, 1: {0: 40, 1: 3920, ...}, 2: {...}}
```
R-orig reproduces F-d: 30,609 / 31,159 leaves, 38 / 39 inner nodes, and 0 stuck nodes. R-any and R-all have 0 stuck nodes, and the AND-tree height is 3.
These scripts are the prover's own engine (`eng.py`). The independent evidence is the Lean kernel certificate (§2), and its model counts agree with the scripts (§4).

## 7. Per-target verdicts
| target | content checked | verdict |
|---|---|---|
| 0 scripts | §6 re-run: every R-orig, R-any and R-all number of the report is reproduced | PASS |
| 1 route (B) | Kernel certificate `cert_all` (k = false, both s) compiles with standard axioms (§2). One inner node with all its children is `inner_node_one`, which is nondegenerate (§4). Timings are within the thresholds (§2, §3). Bridge: statements compile, part of it is proved (`Rel.*`, `cands_spec`, `lwSplitLoopsX_spec`). (A) and (C) are rejected with script evidence. | PASS |
| 2 procedure | Signature, spec and identity statement compile. `LWG5ExpandSplit ↔ LWG5Expand'` holds by `Iff.rfl` (§5). The procedure lives on `PGraph (Fin 2)`, with the reason given. Fuel 4 is used against a height of 3. | PASS |
| 3 split | Portmap: 4 rows, each ≤ 1500 lines at the high estimate. Pins point to compiled probe line ranges. Registry classes are given. LW projection 47-48 (O11 range 45-48) | PASS |
| 4 re-pin | The pin stays, verified by `Iff.rfl` (§5) | PASS |
| 5 paper deltas | T2265d stands. T2288a-e are proposed. No Lean/paper statement difference is left uncovered (observation 3 refines T2288a). | PASS |
This is a design ticket, so it delivers no endpoint theorem of LW-14e. The compiled nonempty instances it does have are the kernel certificate theorems, at concrete nondegenerate data (§4).

## 8. Observations (no statement, instance, build, axiom or delta-coverage defect)
1. **k = true is not kernel-checked.** It rests on `SoundRoot` (stated, not proved), which uses `Rel` ignoring waved colours.
   - `LWG5Graph k s` differs from `LWG5Graph false s` only in the waved `col` (`LWExpTerm3.lean:54-60`).
   - Molecules (`LGraph.adj`, `LWVocab.lean:157`) do not read `col`.
   - §4: the model roots and the root flags agree for k = true.
   - If tickets 3/4 cannot prove the colour-blindness, a second pair of certificate modules is needed. The portmap §9 states this risk.
2. **`CertImpliesLeaf` needs more than `SoundStep`.** The `expand`/`selClassical` nodes are `pcomp` graphs with quotient vertex types, and `SoundStep` is stated only at `N.toP h` with `Cand.toR` candidates. The induction also needs:
   - (i) the converse of `Rel.cand`: every `RCand P` of a `P` with `Rel N P` is the transport of some `c ∈ cands N.g`;
   - (ii) the transport of `RCand.kids` along `Rel`. Portmap L4/L5 (partition and families under `relabel`) supply most of (ii). (i) has no row of its own. Recommendation to the dispatcher: pin (i) and (ii) explicitly in ticket 3 or 4 (Sim/Sound).
3. **T2288a should be more precise.** The paper's `(eq:GGraisesord)` (`B:99`) is stated for a "non-standard neutral vertex". The increment-0 children (36 / 40) come from `R2` at a blue 2-cycle, whose new `G_xx` is split off as `m` by the weight split (routeC2 example). The delta should say whether those depth-1 vertices are non-standard neutral in the paper's sense, and that the drop is the `m`-term of the re-partition.
4. **Memory margin is thin.** The whole file peaks at 7.52 GB against the 8 GB threshold, and the heaviest chunk alone uses 7.08 GB. Ticket 1 (Cert) should split per candidate, or the hub should build the certificate modules alone (portmap §4, §9).
5. **Open dispatcher decisions (not a sign-off on this audit):** keeping T2265 instance (3) (needs the converse simulation, portmap §4); the 2800 / 3400 / 4700-line split against the single-ticket 1150-1450.

## Verdict
**PASS**, for all targets 0-5. No repair is required.
