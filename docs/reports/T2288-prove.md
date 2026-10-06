Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 11:36:43 UTC 2026

Notation as in `docs/reports/T2265-prove.md` (a): `ord = nS+2(nW-nV)`, `tg = 4` if `ext 0 = ext 1` else `5`, leaf = node with `ord ≥ tg`; R1..R8 the `(Oe2x)` families; (j,j') exponents of `m`, `m̄`. Scripts (python only, no Lean; scratch `T2288/`): `eng.py`, `tree.py`, `root.py`, `canon.py`, `summary.py` are copies of the T2265 scripts (same session scratchpad `T2265/`); `rules.py` (R-orig, R-any) and `rall.py` (R-all, with `rall_nomemo.py` = same with the isomorphism memo disabled) are new. R1 is dropped as in T2265 (a). Candidate = internal `v` with blue uncircled non-loop out-edge `p` and in-edge `q` (`candidates` in `eng.py`).

### (i) Exponent table
| row | value | constraint | slack |
|---|---|---|---|
| root graph | `nS=5 nW=2 nV=3 nM=1`, `ord=3`; 163 partition terms, 11 below `tg` (every (k,s)) | root terms below `tg` are the only inner roots | 11 below-`tg` roots |
| order target | `tg` = 4 (`x=y`), 5 (`x≠y`) | leaf: `tg ≤ ord` | `min(ord-tg)` = 0 over merged, distinct, joined leaves, all four (k,s) (output 1) |
| (Oe2x) counters `(ΔnS,ΔnW,ΔnV,ΔnM)` | R2 `(-1,+1,0,≤0)`, R3 `(+1,+1,+1,0)`, R4/R6/R8 `(+1,+2,+2,0)`, R5/R7 `(+1,+1,+1,0)`, R1 `(-1,0,-1,≤0)`; `Δord=+1` each | `oe2xR*_counters`, `oe2xR*_ord` | `Δord=+1` exactly (output 5) |
| leaves, R-orig | 30,609 (s=F), 31,159 (s=T); inner nodes 38 / 39 (depth 0/1/2: 11/26/1 and 11/26/2); largest partition 438 terms; max leaf depth 3 | reproduces T2265 (a) | identical, 0 stuck (outputs 1, 2) |
| progress (stuck nodes) | R-orig 0; R-any 0; R-all 0 | every node with `ord<tg` has a candidate | 0 stuck, 0 cycles (outputs 2, 3) |
| R-all (every candidate, every node) | below-`tg` nodes 125 (s=F), 129 (s=T); candidates examined 332 / 359 (max 4 per node); 91 / 105 of them at created `(Oe2x)` vertices; AND-tree height 3 | height = max number of expansions on any path = fuel needed for any selection rule | height 3: fuel 3 suffices (fuel 4 has slack 1) |
| expanded vertex | degree 2 at all 332 / 359 candidates of R-all and at all 38 / 39 inner nodes of R-orig; `hx2` (no other solid edge at `v` outside `p,q`) true at all of them, 0 false | `hx2` of `lvl1_good_R7` (`LWLvl1.lean:2848`) | 0 violations |
| weights | 9 of 38 / 39 R-orig inner nodes have a solid self-loop | `LocStep.gg` needs no solid loop (`hwf`) | so `gg` unusable, per-family lemmas needed |
| `Lvl1Good` steps | 123,038 of 123,038 (R2 1,204; R3 154; R4/R5/R6 3,844 each; R7 15,996; R8 94,152) | `ord` not lower, `nM`,`nV-nW` not higher | all good (output 5) |
| `m`-power | max `j` = 12 (s=F), 13 (s=T); max `j'` = 3 (s=F), 0 (s=T) | `‖m^j m̄^{j'}‖ = |m|^{j+j'} = 1` | equality |
| leaf invariants | `min nW`=2, `max nM`=1, `min(nW-nV)` over joined leaves = 1, 0 violations of `Normal`, `nM≤1`, `2≤nW`, `LWAttached`, ext-status at all leaves | leaf conjuncts of `LWG5LeafPropsPin` | slack 0, 0 |
| size of what a kernel check would range over | leaves 30,609 / 31,159 (R-orig); 38 / 39 inner nodes; 384 / 393 partitions (T2265 (a)); R-all 125 / 129 inner nodes | the ticket's thresholds (5 min per declaration, 30 min total, 8 GB) | not measured here (Lean is stage 1b) |
| hypotheses at the Lean identity instance | `E = lemE(z0 0) = 0.49999999999488`, `|E|<2` slack 1.5; `t=1/16`, `0<t<1` slack 15/16 | pins `LWG5IdentityPin`: `|E|<2`, `0<t<1` | output 4 |

### (ii) One concrete nondegenerate instance
Identity half (`LWG5IdentityPin d`): `d=3`, `sz0` (`Defs/Sizes.lean:260-262`: `L n = 4(n+1)`, `W n = (2(n+1))^5`), `n=0`: `L=4`, `W=32`, `N=2097152`; `E = lemE(z0 0)`, `t = 1/16`, all `(k,s,x,y)`; the only hypotheses are `|E|<2`, `0<t<1` (output 4); no external hypothesis occurs (the inputs are merged theorems), so no limit computation is owed. Leaf half (`LWG5LeafPropsPin`, `LWG5ProgressPin`): the root graph of `LWG5Graph k s` (`nS=5 nW=2 nV=3 nM=1`, `ord=3`, `tg=4/5`) and its 11 below-`tg` partition terms, expanded to the 30,609 / 31,159 leaves of output 1 (nonempty, nondegenerate: 3 internal vertices, `ord` 3 < `tg`).

```
$ cd scratchpad/T2288; python3 summary.py   # (output 1; 11.9 s) R-orig tree of T2265 (a): per (k,s) leaves, status, violations, stuck
k     s      leaves distinct   netnz |  merged distinct  joined |   j'>0 jnt nM=0    viol  stuck | depth root<tg
False False   30609   21219   21070 |   13263   13242    4104 |  13697    4104       0      0 |     3    11
      min nW 2, max nM 1, min(ord-target): merged 0 distinct 0 joined 0; min(nW-nV) over joined 1; max j 12, max j' 3; root partition terms 163
False True    31159   19693   19552 |   13349   13303    4507 |      0    4507       0      0 |     3    11
      min nW 2, max nM 1, min(ord-target): merged 0 distinct 0 joined 0; min(nW-nV) over joined 1; max j 13, max j' 0; root partition terms 163
True  False   30609   21217   21068 |   13263   13242    4104 |  13697    4104       0      0 |     3    11
      min nW 2, max nM 1, min(ord-target): merged 0 distinct 0 joined 0; min(nW-nV) over joined 1; max j 12, max j' 3; root partition terms 163
True  True    31159   19691   19550 |   13349   13303    4507 |      0    4507       0      0 |     3    11
      min nW 2, max nM 1, min(ord-target): merged 0 distinct 0 joined 0; min(nW-nV) over joined 1; max j 13, max j' 0; root partition terms 163
$ python3 rules.py orig 8; python3 rules.py any 6   # (output 2; 1.5 s each) rows (k,s)=(F,F),(F,T); (T,F),(T,T) have identical numbers
R-orig k=False s=False: leaves 30609, inner by depth {0: 11, 1: 26, 2: 1} (total 38), nodes 30647, stuck(no candidate) 0, stuck(depth>8) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 38}, hx2 {True: 38}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
R-orig k=False s=True: leaves 31159, inner by depth {0: 11, 1: 26, 2: 2} (total 39), nodes 31198, stuck(no candidate) 0, stuck(depth>8) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 39}, hx2 {True: 39}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
R-any k=False s=False: leaves 30609, inner by depth {0: 11, 1: 26, 2: 1} (total 38), nodes 30647, stuck(no candidate) 0, stuck(depth>6) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 38}, hx2 {True: 38}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
R-any k=False s=True: leaves 31159, inner by depth {0: 11, 1: 26, 2: 2} (total 39), nodes 31198, stuck(no candidate) 0, stuck(depth>6) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 39}, hx2 {True: 39}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
$ python3 rall.py   # (output 3; 14 s) AND-tree over every candidate (v,p,q) at every below-target node; rows (F,F),(F,T); (T,*) identical
R-all k=False s=False: below-target root terms 11, distinct (up to iso) below-target nodes 125, with no candidate (stuck) 0, cycles 0, max height of AND-tree 3, candidates examined 332 (max per node 4), candidates at created vertices 91, degree of expanded vertex {2: 332}, hx2 false 0, largest partition 438, not-ok nodes 0  [3s]
R-all k=False s=True: below-target root terms 11, distinct (up to iso) below-target nodes 129, with no candidate (stuck) 0, cycles 0, max height of AND-tree 3, candidates examined 359 (max per node 4), candidates at created vertices 105, degree of expanded vertex {2: 359}, hx2 false 0, largest partition 438, not-ok nodes 0  [4s]
$ python3 rall_nomemo.py   # same script with `key = object()` (no isomorphism memo): all four rows equal output 3 (125/129 nodes, 0 stuck, 0 cycles, height 3)
$ python3 inst.py   # (output 4)
L=4 W=32 N=2097152  z0 0 = (0.5 + 8.76387294767e-6j)
E = lemE(z0 0) = 0.49999999999488
|E| < 2 : True (slack 1.5)
0 < t < 1 : t = 1/16, slack to 1: 15/16
Im zt = (1-t) Im m = 0.9077304718  (> 0: True)
hzm residual |zt + t m + 1/m| = 1.1833e-41
|m| = 1.0 ; ||m||^2 t = 0.0625 < 1 (hSp), slack 0.9375
|m^j conj(m)^j'| = |m|^(j+j') = 1.0 at (j,j')=(12,3)
m^-1 = conj m ? |1/m - conj(m)| = 1.1833e-41
$ python3 counters_chk.py; python3 lvl1good.py   # (output 5)
(family,(dnS,dnW,dnV,dnM),dord):count over every (vertex,p,q) of every below-target root term:
{('R1', (-1, 0, -1, -1), 1): 28, ('R1', (-1, 0, -1, 0), 1): 72, ('R2', (-1, 1, 0, -1), 1): 28, ('R2', (-1, 1, 0, 0), 1): 72, ('R3', (1, 1, 1, 0), 1): 100, ('R4', (1, 2, 2, 0), 1): 100, ('R5', (1, 1, 1, 0), 1): 100, ('R6', (1, 2, 2, 0), 1): 100, ('R7', (1, 1, 1, 0), 1): 192, ('R8', (1, 2, 2, 0), 1): 192}
Lvl1Good steps (4 (k,s) x all tree edges): 123038, good 123038; by family: {'R2': 1204, 'R3': 154, 'R4': 3844, 'R5': 3844, 'R6': 3844, 'R7': 15996, 'R8': 94152}
```

### Verdicts
- Target 0 (scripts, preflight): PASS. R-orig reproduces 30,609 / 31,159 leaves, 38 / 39 inner nodes, largest partition 438, 0 stuck, `min(ord-tg)=0` (outputs 1, 2). R-any (first internal vertex in sorted name order, created vertices allowed) gives the same numbers: 0 of its expansions are at a created vertex, so on this tree R-any = R-orig (which is not evidence about other orders). R-all: 125 / 129 below-`tg` nodes, 332 / 359 candidates (91 / 105 at created vertices), 0 stuck, 0 cycles, AND-tree height 3. Recommended rule: no fixed rule is needed for progress on this tree, since R-all has 0 stuck nodes and height 3, so the leaf half holds for every selection rule that satisfies the candidate spec, with fuel 3 (a measure is not needed here); for the identity half any `sel` with that spec works. If a concrete rule is wanted, R-orig is the one with the preflight's counts (38 / 39 inner nodes, 31k leaves), but R-all shows the choice is free. Caveat: these are statements about the python model (`eng.py`, a re-implementation of `LWVocab.lean:1000-1303`, `LWGGExp.lean:465-570`, `LWWeightExp.lean:658`), with R1 dropped (zero term, T2265 (a)); the Lean bridge is stage 1b's.
- Target 1 ((B) kernel route): mathematics PASS. The model facts needed (progress, `ord ≥ tg`, `hx2`, degree 2) hold at every node and every candidate; the kernel time and memory are not decided by mathematics and are not claimed here; R-all (125 / 129 nodes, all candidates) is a smaller check than the 31k leaves if only progress is wanted. Routes (A) and (C) are not examined in this section.
- Target 2 (procedure): PASS on the mathematics: the (j,j') exponents are those of output 1 (max `j` 12 / 13, max `j'` 3 / 0; `|m|^{j+j'}=1`); fuel 3 is enough on this tree.
- Target 3 (split), target 4 (re-pin), target 5 (paper deltas): no mathematical obstruction found; the content is design. `T2265d` stands: output 3 shows progress holds on this tree for every rule, the paper gives no argument for it.
- §29: (1) `0<t<1`, `|E|<2` only in the identity half (output 4); (2)-(4) no index set, no `L^d ≤ W^K`, every `n`; (5) one list for all `sz, n, E, t, x, y`; (6), (7) no `ĝ`, no scale.

## (b) Script output and design evidence (stage 1b) — written Tue Oct  6 14:07:55 UTC 2026

Scope: report-only design ticket. Lean written: `RBM3D/Probe/T2288Cert.lean` (branch `t/T2288`, commit 5f3d37f, 1228 lines; not merged); `Test/Axioms.lean` not touched; ports from RBM1D/RBM2D: none (no light-weight layer there). Machine: `sysctl -n hw.ncpu hw.memsize` = 10, 34359738368; toolchain `leanprover/lean4:v4.34.0`; branch base 9664e13. All kernel runs use `decide +kernel`; the file has no `sorry`, `admit`, declared axiom or `native_decide` (grep below). Scripts and scratch Lean files (python: eng, tree, rules, rall, summary, rawcount, routeC, routeC2, r1check, invsearch2, indtest, indtestJ, pincheck, extract, timing; Lean: V4, TG2-TG5, Single_*) are in the session scratchpad `T2288/`.

```
$ cd RBM3D-wt/T2288; /usr/bin/time -l lake env lean RBM3D/Probe/T2288Cert.lean      # started Tue Oct  6 13:10:33 UTC 2026, finished Tue Oct  6 13:29:42 UTC 2026; output has 0 lines matching "error"
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
1148.62 real      1124.40 user        29.32 sys
7429488640  maximum resident set size
138191696  peak memory footprint
$ grep -c "ofReduceBool\|sorryAx" <that output>   ->  0
$ python3 timing.py <profiler run of the same file, `set_option profiler true`, threshold 0.5 s>      # started Tue Oct  6 13:10:32 UTC 2026
declarations above the profiler threshold (0.5 s): 166  last completion time 985.0 s  sum of differences 985.0 s
largest 5 differences (s): ['17.0', '17.0', '16.0', '16.0', '16.0']  median 5.0  mean 5.93
real 1145.63
maximum resident set size 7408304128
peak memory footprint 138453864
standalone single theorems (file = probe without chunks + one theorem; /usr/bin/time -l): base wall 5.67 s, RSS 3.66 GB; median chunk `ch_FF_9_0_4` wall 10.77 s, RSS 4.68 GB; heaviest chunk `ch_FF_10_0_8` wall 22.21 s, RSS 7.10 GB
B-lite (progress and ord only; scratch variant with the leaf-property flag `true`) vs B-full, the 36 chunks + assembly of root term 9, (F,F), run one after the other, no other job of this session running (`13:30:18 UTC 2026` to `13:35:20 UTC 2026`): wall 121.2 s, RSS 4.92 GB vs wall 180.9 s, RSS 5.77 GB (+49%)
second run of the delivered file (`python3 lrun.py .../T2288Cert.lean`, wrapper prints the exit code), Tue Oct  6 13:39:27 UTC 2026 to Tue Oct  6 13:58:52 UTC 2026: wall 1164.9 s, exit 0, RSS 7.41 GB, 13 axiom lines, 0 `ofReduceBool`/`sorryAx` lines
naive B-full with the REAL definitions (`LGraph.Normal`, `LGraph.nM`, `LWAttached` unfolded, `mol`; kernel, scratch `TReal2.lean`, Tue Oct  6 14:07:01 UTC 2026): building and checking the first 5 children of root 0 cand 0: 1.67 s; the first 20 children (a separate theorem, rebuilt): 2.55 s (0.13 s per child); `Normal` alone on 20 children 0.44 s; at 0.13 s per child the 275,620 / 301,079 children would take about 10 h (extrapolation), so the label flags of `belowOf` (one evaluation per raw dotted choice) are part of the design. A first attempt over all children of three (node, candidate) pairs did not finish in 902 s (`TReal.lean`, `[TIMEOUT after 902s]`).
lite vs straightforward model (kernel, scratch `TEq.lean`, Tue Oct  6 13:40:41 UTC 2026): the below-target children of `childrenB` equal those of `(fams ..).flatMap cPartition |>.filter (!leaf)` at the level of node keys (sizes, edge lists, waved pairs, dotted, ext) for root 9 cand 0, root 10 cand 0, root 8 cand 1, a depth-1 node cands 0 and 1 (5 theorems, all axioms standard): wall 28.2 s, exit 0
```

Target 0 (scripts re-run in this session, python only, scratch `T2288/`; 11:44:10-11:44:38 UTC; the python model is `eng.py`, a re-implementation of `LWVocab.lean:1000-1303`, `LWGGExp.lean:465-570`, `LWWeightExp.lean:658`):
```
$ python3 summary.py      # R-orig, the T2265 tree (rows (F,F),(F,T); (T,*) identical)
k     s      leaves distinct   netnz |  merged distinct  joined |   j'>0 jnt nM=0    viol  stuck | depth root<tg
False False   30609   21219   21070 |   13263   13242    4104 |  13697    4104       0      0 |     3    11
      min nW 2, max nM 1, min(ord-target): merged 0 distinct 0 joined 0; min(nW-nV) over joined 1; max j 12, max j' 3; root partition terms 163
False True    31159   19693   19552 |   13349   13303    4507 |      0    4507       0      0 |     3    11
      min nW 2, max nM 1, min(ord-target): merged 0 distinct 0 joined 0; min(nW-nV) over joined 1; max j 13, max j' 0; root partition terms 163
$ python3 rules.py orig 8; python3 rules.py any 6      # R-orig, R-any (created vertices allowed), rows (F,F),(F,T)
R-orig k=False s=False: leaves 30609, inner by depth {0: 11, 1: 26, 2: 1} (total 38), nodes 30647, stuck(no candidate) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 38}, hx2 {True: 38}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
R-orig k=False s=True: leaves 31159, inner by depth {0: 11, 1: 26, 2: 2} (total 39), nodes 31198, stuck(no candidate) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 39}, hx2 {True: 39}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
R-any k=False s=False: leaves 30609, inner by depth {0: 11, 1: 26, 2: 1} (total 38), nodes 30647, stuck(no candidate) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 38}, hx2 {True: 38}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
R-any k=False s=True: leaves 31159, inner by depth {0: 11, 1: 26, 2: 2} (total 39), nodes 31198, stuck(no candidate) 0, max leaf depth 3, largest partition 438, degree of expanded vertex {2: 39}, hx2 {True: 39}, inner nodes with a solid self-loop 9, expanded vertex contains a created vertex: 0  [0s]
$ python3 rall.py      # R-all: AND-tree over every candidate (v,p,q) at every below-target node, rows (F,F),(F,T)
R-all k=False s=False: below-target root terms 11, distinct (up to iso) below-target nodes 125, with no candidate (stuck) 0, cycles 0, max height of AND-tree 3, candidates examined 332 (max per node 4), candidates at created vertices 91, degree of expanded vertex {2: 332}, hx2 false 0, largest partition 438, not-ok nodes 0  [3s]
R-all k=False s=True: below-target root terms 11, distinct (up to iso) below-target nodes 129, with no candidate (stuck) 0, cycles 0, max height of AND-tree 3, candidates examined 359 (max per node 4), candidates at created vertices 105, degree of expanded vertex {2: 359}, hx2 false 0, largest partition 438, not-ok nodes 0  [4s]
$ python3 rawcount.py      # raw dotted choices and children over the R-all tree (Tue Oct  6 13:38:27 UTC 2026)
k=False s=False {'below_children': 114, 'cand': 332, 'children': 275620, 'inner': 125, 'raw': 89018} [3s]
k=False s=True {'below_children': 118, 'cand': 359, 'children': 301079, 'inner': 129, 'raw': 97413} [7s]
$ Lean model (probe functions `rootInfo`, `childrenB`, `cands`; interpreter `#eval`, not a proof): (root leaf flag, inner nodes, candidates, below-target children, all leaf flags) for (F,F),(F,T),(T,F),(T,T)
(true, 125, 332, 114, true)
(true, 129, 359, 118, true)
(true, 125, 332, 114, true)
(true, 129, 359, 118, true)
$ Lean `childrenB` at every candidate of each below-target root term: below-target children per candidate (the lists for (F,F),(F,T),(T,F),(T,T) are identical): [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0, 0], [12, 12, 12], [14, 14, 14]]
$ Lean interpreter `stats 3` on the two case-(4) root terms (F,F) (inner nodes, candidates, children incl. fuel-exhausted nodes): [(57, 158, 94135), (59, 155, 172937)]
```
Recommended rule: **none fixed** (R-all). R-orig, R-any and R-all all have 0 stuck nodes; R-all examines every candidate (91 / 105 at created `(Oe2x)` vertices), so the leaf half holds for every selection rule that satisfies the candidate spec, with fuel 3 (AND-tree height 3). The Lean model and the python engine agree on 125 / 129 inner nodes and 332 / 359 candidates; the below-target children per candidate of the case-(4) root terms agree with the route-(C) table (12 and 14).

Statements extracted from the probe by script (`extract.py`: first line(s) of the declaration up to `:=`; line numbers of the file):
```
73: def LWG5LeafProps (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
80: def LWG5Identity (d : ℕ) (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : Prop :=
89: def LWG5ExpandSplit (d : ℕ) : Prop :=
106: theorem lwG5ExpandSplit_iff (d : ℕ) : LWG5ExpandSplit d ↔ LWG5Expand' d
183: abbrev Sel := (P : PGraph (Fin 2)) → Option (RCand P)
186: def expand (sel : Sel) : ℕ → PGraph (Fin 2) → List ((ℕ × ℕ) × PGraph (Fin 2))
195: def expandRoot (sel : Sel) (fuel : ℕ) (k s : Bool) : List ((ℕ × ℕ) × PGraph (Fin 2)) :=
201: def LWExpandIdentity (sel : Sel) (fuel : ℕ) : Prop :=
205: def selClassical : Sel
213: theorem lwG5ExpandOfHalves : LWG5ExpandOfHalves
375: def goodB : ℕ → MNode → Bool
335: def belowOf (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)) : Bool × List MNode :=
1202: theorem cert_all : ∀ s, (rootInfo false s).1 = true ∧ (rootInfo false s).2.all (goodB 3) = true
473: theorem Rel.scalingOrder_eq {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) : P.g.scalingOrder = N.g.scalingOrder
489: theorem Rel.leaf_iff {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) : leaf N = true ↔ (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder
530: theorem Rel.cand {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) (c : Cand N.a N.b) (hc : c ∈ cands N.g) : LWG5Cand P
495: theorem cands_spec {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin b)) (c : Cand a b) (hc : c ∈ cands g) : c.p ∈ lwSplit g.solid ∧ c.q ∈ lwSplit c.p.2 ∧ c.y ≠ Sum.inr c.x ∧ c.y' ≠ Sum.inr c.x ∧ c.p.1 = ⟨true, false, Sum.inr c.x, c.y⟩ ∧ c.q
444: theorem lwSplitLoopsX_spec {V : Type*} [DecidableEq V] (m : ℂ) (es : List (SEdge V)) : lwSplitLoops m es = (lwSplitLoopsX es).map fun r => (m ^ r.1.1 * star m ^ r.1.2, r.2)
598: def PartitionSim : Prop :=
606: def ChildrenSim : Prop :=
563: def RelInvariance : Prop :=
622: def SoundStep : Prop :=
629: def SoundRoot : Prop :=
637: def CertImpliesLeaf : Prop :=
```

Pin check (`pincheck.py` copies section 2 of `T2288-check.lean` and of `T2265-check.lean` into scratch namespaces, extracts the probe's section 1 by script, and compiles 9 `Iff.rfl` examples: the six pins of the check file, `LWJoinedPin`, T2265's `LWG5Expand'Pin`, and `LWG5ExpandSplitPin d ↔ LWG5Expand'Pin d`): `lake env lean PinCheck.lean` Tue Oct  6 13:14:57 UTC 2026 -> [wall 4.0s] [exit 0]

```
$ name-clash and hygiene greps of the probe (Tue Oct  6 13:15:01 UTC 2026)
sorry|admit|native_decide|axiom lines in the probe: 0; declarations outside `namespace RBM.Probe.T2288`: 0
MNode:       0 rootInfo:       0 goodB:       0 belowOf:       0 cPartition:       0 LWG5Cand:       0 LWG5Progress:       0 LWG5LeafProps:       0 LWG5Identity:       0 LWG5ExpandSplit:       0 LWJoined:       0 RCand:       0 expandRoot:       0 selClassical:       0 partitionX:       0 lwSplitLoopsX:       0 cert_all:       0
$ grep -rnw <T2288 names> docs/tickets (outside the T2288 files): T2288:       0 LWG5CandPin:       0 LWG5ProgressPin:       0 LWG5LeafPropsPin:       0 LWG5IdentityPin:       0 LWG5ExpandSplitPin:       0
$ python3 r1check.py   # the partition of the R1 graph (Tue Oct  6 13:14:42 UTC 2026)
R1 graph: Ga+x+y>c Gc>a+x+y | S(c,a+x+y) S*(a+x+y,a+x+y) | x(a+x+y,c) x(c,a+x+y) x(a+x+y,a+x+y)
partition size 2 signs [-1, 1] net coefficients after summing equal graphs [0]
R1 graphs of all (below-target root term, candidate) pairs, F,F: 25, partition nonempty and net zero in every case
```

Route (A), time-boxed (20 min) invariant search (`invsearch2.py`, `indtest.py`, `indtestJ.py`; Tue Oct  6 13:08:51 UTC 2026 to Tue Oct  6 13:10:47 UTC 2026; 71 decidable features: blue/red in/out degrees at internal vertices and at `x`, `y`, charge, boundary, blue paths, thresholds on `n_S`, `n_V`, ...):
```
positives (distinct below-target R-all nodes, k=F, s in F,T): 193  [6s]
features true at every positive: ['#int(bi&bo)>=1', '#int(bi&bo)>=2', '#int(bi)>=1', '#int(bi)>=2', '#int(bo)>=1', '#int(bo)>=2', 'ext_neutral', 'nS<=6', 'nS<=7', 'nS<=8', 'nint>=1', 'nint>=2', 'nint_ge1', 'no_direct_blue_xy', 'ri_x=0', 'ro_y=0', 'some_int_bi_bo']
stuck graphs NI=2 nS<=5: 442  [0s, total 6s]
stuck graphs NI=3 nS<=4: 2309  [0s, total 6s]
separating conjunctions (minimal, <=3 features, true at all positives, false at all 2751 stuck graphs): 5
   ['#int(bi&bo)>=1']  ['#int(bi&bo)>=2']  ['#int(bi)>=2']  ['#int(bo)>=2']  ['some_int_bi_bo']
$ indtest.py (Amend-1 invariants + neutrality + boundary + a candidate + ord < tg; every candidate expanded, families R2-R8, re-partition; children with x != y)
NI=2 nS<=5: family size 386 graphs, children examined 205034, violations among below-target children with x != y: {'stuck child (progress fails)': 348, 'invariant boundary fails': 366, 'invariant ext fails': 8}  [3s]
NI=3 nS<=4: family size 2337 graphs, children examined 1392954, violations among below-target children with x != y: {'stuck child (progress fails)': 27312, 'invariant boundary fails': 23241, 'invariant ext fails': 6318}  [21s]
$ indtestJ.py 3 4 (each separating J: parent satisfies J; children below target)
  J = int_bi>=2                                                              family  1224 graphs, children   963786, violations among below-target children (x != y): {'J fails': 21498, 'stuck child': 9918}
  J = int_bo>=2                                                              family  1224 graphs, children   963786, violations among below-target children (x != y): {'J fails': 21948, 'stuck child': 9828}
  J = int_bi>=2 & int_bo>=2                                                  family   810 graphs, children   768516, violations among below-target children (x != y): {'J fails': 17634, 'stuck child': 4380}
  J = int_bibo>=2                                                            family   810 graphs, children   768516, violations among below-target children (x != y): {'J fails': 18138, 'stuck child': 4380}
  J = ri_x=0 & ro_y=0                                                        family  2337 graphs, children  1392954, violations among below-target children (x != y): {'stuck child': 27312, 'J fails': 1521}
```
Route (A) result: **none in the time box** (the search used 1 min 56 s). The separating conjunctions are the progress predicate itself (`#int(bi&bo) ≥ 1`, `some_int_bi_bo`, `#int(bi&bo) ≥ 2`) or `#int(bi) ≥ 2`, `#int(bo) ≥ 2`; none is inductive on the bounded family: the family of all graphs satisfying the Amend-1 invariants with a candidate is not closed (stuck children 348 and 27,312), and each separating `J` has children that violate `J` or are stuck. The bound rests on the structure of the specific tree.

Route (C), per root term below `tg` (`routeC.py`, `routeC2.py`; Tue Oct  6 13:08:51 UTC 2026 to Tue Oct  6 13:09:02 UTC 2026):
```
k=False s=False: 163 root terms, 11 below target
  i  ord tg  deficit  #cands | children per cand | ord(child)-ord(parent): count | below-tg children per cand
  0  3   4    1       2     [264, 264] | {1: 22, 2: 32, 3: 78, 4: 88, 5: 110, 6: 88, 7: 70, 8: 32, 9: 8} | [0, 0]
  8  3   4    1       3     [707, 698, 653] | {1: 45, 2: 98, 3: 234, 4: 332, 5: 458, 6: 395, 7: 310, 8: 140, 9: 46} | [0, 0, 0]
  9  2   4    2       3     [533, 533, 533] | {1: 36, 2: 75, 3: 183, 4: 258, 5: 360, 6: 303, 7: 240, 8: 108, 9: 36} | [12, 12, 12]
 10  3   5    2       3     [1125, 1125, 1125] | {1: 51, 2: 125, 3: 306, 4: 444, 5: 621, 6: 606, 7: 546, 8: 356, 9: 216, 10: 80, 11: 24} | [14, 14, 14]
s=False: increments ord(child)-ord(parent) (3 = ">=3") by depth of the parent: {0: {1: 344, 2: 714, 3: 12350}, 1: {0: 36, 1: 3664, 2: 8230, 3: 221610}, 2: {1: 980, 2: 1856, 3: 25836}}
s=True: increments ord(child)-ord(parent) (3 = ">=3") by depth of the parent: {0: {1: 344, 2: 714, 3: 12350}, 1: {0: 40, 1: 3920, 2: 8841, 3: 239802}, 2: {1: 1124, 2: 2156, 3: 31788}}
```
Route (C) result: **rejected**. For the 9 root terms with deficit 1 (cases (2), (3)) one step gives leaves only (0 below-target children for every candidate); the 2 case-(4) terms (deficit 2) have 12 / 14 below-target children per candidate and 57 / 59 inner nodes in R-all. A per-parent lemma `ord(child) ≥ ord(parent) + 1` holds at the roots (increment at least 1 for all 13,408 children) but is false at depth 1 (36 / 40 children with increment 0, e.g. `R2` at a vertex whose out- and in-edges are the two edges of a blue 2-cycle: the new edge becomes a weight and the re-partition splits it), so each depth needs the exact enumeration, i.e. (B).

Narrative (every number is in the output above or in the probe):
1. **Route (B) is accepted, with the R-all certificate and B-full leaf properties.** The kernel (`decide +kernel`, axioms propext, Classical.choice, Quot.sound) certifies for `k = false` and both `s`: the 163 root terms meet the leaf properties where they are leaves, and each of the 11 below-target root terms has a height-3 AND-tree over every candidate and every family (125 / 129 inner nodes, 332 / 359 candidates, 114 / 118 below-target children, no stuck node, all leaf properties at every leaf). The interpreter counts of the Lean model for the four `(k, s)` equal the python R-all numbers.
2. **Cost.** The whole probe takes 1149 s (19.1 min; the second run 1164.9 s, exit 0) and 7.43 GB resident in one process; the heaviest declaration alone takes 22.21 s and 7.10 GB (baseline 3.66 GB); thresholds of the ticket (5 min per declaration, 30 min total, 8 GB) are met, with 0.57 GB margin on memory in the whole-file run (portmap §4 gives the per-candidate split that lowers it). B-full costs +49% over B-lite on root term 9.
3. **What made it feasible.** One declaration per root term did not finish in 552 s (scratch `TV2b`, `[TIMEOUT after 552s]`), and 12 depth-1 nodes in one declaration took 50 s and 10.7 GB (`TV2g`). The probe classifies every raw dotted choice by class labels (`labsOf`), the loop count `L` and the formula `n_S - t + 2 (n_W - B)` and builds full graphs only for below-target children (12 / 14 per candidate); one theorem per depth-1 node (78 per `s`) keeps each declaration at most about 20 s. Raw dotted choices: 89,018 / 97,413; children 275,620 / 301,079 (python, `rawcount.py`).
4. **Why R-all.** With R-all the leaf half holds for every selection rule, so the identity half is generic over `sel` (probe 183-213) and no iso-invariant rule is needed on the real carrier, whose vertex types are quotient subtypes. Created `(Oe2x)` vertices are expanded (91 / 105 candidates), so nothing is tracked through `merge`/`vmap`/`relabel`. If a concrete rule is wanted for an instance, the preflight's R-orig (first of `α, β, γ` with a candidate) has the counts of target 0.
5. **Carrier.** Real `PGraph (Fin 2)` with exponent-tracking `partitionX` and `RCand.kids` (probe 115-181); the model only simulates the real children (one direction), so no exact list bridge is needed. Proved in the probe: `Rel.scalingOrder_eq`, `Rel.tgt_eq`, `Rel.leaf_iff`, `cands_spec`, `Rel.cand`, `lwSplit_map`, `lwSplitLoopsX_spec`; stated and compiled: `PartitionSim`, `ChildrenSim`, `RelInvariance`, `SoundStep`, `SoundRoot`, `CertImpliesLeaf`. (vi) the model families are the merged `oe2xR*`, `owxT1` on `Fin` types; the only renumbering is `finSumFinEquiv`.
6. **R1 is dropped by value.** Its partition is not empty (25 of 25 R1 graphs: two terms of opposite sign, net 0), so `∫ R1.val = 0` (by `oe2xR1_val`, `LWGGExp.lean:592`, and `Normal` (iii): `1_{x=y}` and `1_{x≠y}` both occur) is a T2265a lemma, not a consequence of the partition.
7. **Fuel and measure.** Fuel 3 suffices (height 3), 4 has slack; `Lvl1Good` is not needed; zero terms: only R1. Coefficients `(j, j')`: `lwSplitLoopsX` and the family shifts 3 / 1 (python: max j 12 / 13, max j' 3 / 0).
8. **Routes (A) and (C) fail** (outputs above): no inductive invariant in a 71-feature library; no per-parent lemma (increment 0 at depth 1); neither has a line estimate because neither closes the leaf half, while (B) closes it in four tickets of 2800 / 3400 / 4700 lines (portmap).
9. **Split** (portmap): four tickets, 2800 / 3400 / 4700 lines; LW plan +3 (47-48, O11 range 45-48, HOLD at 50). **Re-pin: none**; `LWG5ExpandSplitPin d ↔ LWG5Expand'Pin d` is `Iff.rfl`.
10. **Risks.** Memory of parallel builds; the soundness statements are stated, not proved (evidence: model = python engine on all counts); `k = true` rests on `Rel` ignoring waved colours (interpreter counts agree for all four `(k, s)`). Observed: independent theorems of one file are kernel-checked one after another (4 theorems: wall 25.5 s, user 23.4 s), so parallelism needs separate modules.

§29: (1) `0 < t < 1`, `|E| < 2` only in the identity half; (2)-(4) no index set, no `L^d ≤ W^K`, every `n`; (5) one list for all `sz, n, E, t, x, y`; (6), (7) no `ĝ`, no scale. Endpoint instances: the kernel theorems are concrete (3 internal vertices, `ord` 2 or 3 below `tg` 4 or 5, 125 / 129 inner nodes); no endpoint theorem of LW-14e is delivered by this ticket.

## (c) Verified Mathlib / Lean names (each compiled in the probe)
`List.getElem_of_mem`, `List.getD_eq_getElem`, `List.all_eq_true`, `List.getElem?_eq_getElem`, `Bool.or_eq_true`, `List.mem_flatMap`, `List.mem_filterMap`, `List.flatMap_map`, `List.map_flatMap`, `List.flatMap_congr`, `List.mem_map`, `Bool.and_eq_true`, `decide_eq_true_eq`, `Bool.not_eq_true'`, `Fintype.card_congr`, `EmbeddingLike.apply_eq_iff_eq`, `Nat.mod_lt`, `finSumFinEquiv`, `Equiv.sumCongr`, `Function.Surjective.comp`. Absent: `RBM.Graph.PGraph.comp` (field notation `P.comp` failed; the probe defines `pcomp`). Not used: `if_pos`, `if_neg` (deprecated warning).

## (d) Open issues and paper-delta candidates
- Stated, not proved: `PartitionSim`, `ChildrenSim`, `RelInvariance`, `SoundStep`, `SoundRoot` (portmap §4: about 1700 lines, central, in two tickets). T2265 stays HELD; ticket 2 of the portmap is T2265a.
- T2265's instance (3) (explicit members with `j' ≥ 1` and with `LWJoined`) needs the converse direction of the simulation; `PartitionSim`, `ChildrenSim` are `List.Forall₂` and give it (portmap §4, ticket 4); not delivered here.
- Kernel memory of the heaviest chunk (7.10 GB standalone) and the hub building several modules at once; `k = true` is not kernel-checked (by `Rel`, to be proved).
- Paper-delta candidates (T2265d stands):
  - `T2288a`: `(eq:GGraisesord)` (`B:98-100`) fails after the dotted re-partition at depth >= 1: 36 / 40 children of depth-1 parents have `ord` equal to the parent's (route (C) output); at the roots every child gains at least 1.
  - `T2288b`: case (4) (`B:107-108`, "the two expansions raise the scaling order by at least 2 in total"): the case-(4) root terms have trees of depth 3 (57 / 59 inner nodes in R-all; R-orig has 1 / 2 inner nodes at depth 2); every leaf still meets `(eq:sizeGammamu_E)` with slack 0.
  - `T2288c`: progress holds for every choice of the expansion vertex (R-all: 0 stuck nodes, 91 / 105 candidates at created vertices); the choice of `α, γ, β` in the paper is not needed. Outside the tree it fails (route (A): stuck children 348 / 27,312).
  - `T2288d`: the molecule facts that `GtoAG` needs at the leaves (`n_M ≤ 1`, attached to at least 2 solid edges, distinct external molecules or joined) hold at every leaf of the R-all tree by enumeration; `B:84-90` asserts them (`q ∈ {0,1}`, "attached to at least two solid edges") without an argument.
  - `T2288e`: the leaf bound is a finite certificate in Lean (kernel, 125 / 129 nodes); the paper says "verified by inspecting" (`B:98`).
