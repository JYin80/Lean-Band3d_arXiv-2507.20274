Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 15:16:07 UTC 2026

Targets: `cert_all : ∀ s, (rootInfo false s).1 = true ∧ (rootInfo false s).2.all (goodB 3) = true` (plus `cert_FF`, `cert_FT`, `goodB_succ_of`, `inner_node_one`, `root_F?_shape`, instances (2)-(3)), a finite kernel certificate about the one tree `LWG5Graph false s`, `s ∈ {false, true}`.  Mathematics only; all numbers below are from the python scripts of T2288 (copied to the scratchpad `T2306/`, `tree.py eng.py root.py canon.py rall.py rawcount.py routeC.py`) and the T2288 reports; the root in `root.py` has the edges of `LWG5Graph` (`LWExpTerm3.lean:51-56`: solid `x→a, a→c, c→b, b→y`, then `y→x` if `s` else non-directed `x–y`; waved `(k) c→a`, `a→b`).

### (i) Exponent table (no analytic exponent: the certificate is combinatorial; rows are the counts, thresholds and resource limits the targets depend on)

| Item | Value | Constraint | Slack |
|---|---|---|---|
| `ord(Γ) = n_S + 2(n_W − n_V)` (`ScalingOrder.lean:65`, `LGraph.scalingOrder` = `ord Γ.counters`, `LWVocab:1672`) | root `LWG5Graph false s`: `5 + 2(2 − 3) = 3` | definition | — |
| `tg` (`tgt`, probe `:325`) | `4` if `ext 0 = ext 1`, else `5` | leaf `⇔ tg ≤ ord` | root term 0: `ord 3 < 4` (deficit 1); term 9: `2 < 4` (2); term 10: `3 < 5` (2) |
| partition terms of the root | 163 (both `s`) | — | 152 leaves, 11 below `tg` |
| below-target root terms | 11 / 11 | `root_FF_shape`, `root_FT_shape`: `.2.length = 11` | exact |
| distinct below-target nodes (R-all, `s = false / true`) | 125 / 129 | every one has a candidate | stuck nodes 0, cycles 0, not-ok 0 |
| of these: depth 0 / 1 / 2 | 11 / 78 / 36 and 11 / 78 / 40 | `125 = 11 + 78 + 36`, `129 = 11 + 78 + 40` | exact |
| AND-tree height | 3 (roots, depth 1, depth 2; compiled probe: `goodB 3` at roots, `goodB 2` at depth 1, per the ticket) | `cert_all` states `goodB 3` | exact (max height 3) |
| candidates `(v,p,q)` examined | 332 / 359 (max 4 per node) | `cands` non-empty at every below-target node | min 2 per root term |
| depth-1 chunks | 78 = 3·12 + 3·14 per `s` (terms 9, 10: `j < 3`, `l < 12` resp. `< 14`) | one theorem per depth-1 node | 78 `ch_FF_`, 78 `ch_FT_` in the probe (grep below) |
| `chs_`, `root_F?_i` | 6 + 6, 11 + 11 | — | by grep |
| below-target children, root terms 0-8 | 0 per candidate | depth-1 node has no below-target child, so one shot `decide +kernel` | — |
| below-target children, term 9 / term 10 | 12 / 14 per candidate (3 candidates) | chunks | — |
| raw dotted choices / children (no memo) | 89,018 / 275,620 (`s=false`); 97,413 / 301,079 (`s=true`) | the lite model builds full graphs only for below-target children (114 / 118) | `114 = 78+36`, `118 = 78+40` |
| lite order of a child | `n_S − t + 2(n_W − B)`, `t` = weight splits, `B` = merged internal classes | used by T2288/ticket 4 (L7), not by this ticket's Lean | not re-derived here |
| kernel option | `maxRecDepth 1000000` (probe `:38`) | `decide +kernel` runs | as in the probe |
| copy size | 210 + 10 + 548 = 768 probe lines (`:224-433`, `:653-662`, `:664-1211`) | ticket: > 1500 lines stops | 1500 − 768 = 732 before instances/header |
| wall per module (probe whole file, both `s`) | 1148.6 s real, 1124.4 s user | `LWExpCertS0`, `LWExpCertS1` ≤ 1.5 × 575 = 862.5 s each; any module ≤ 1800 s | half-probe 574.3 s: slack 288 s (S0/S1), 1226 s (1800 − 574.3) |
| peak memory (probe whole file) | 7.43 GB (heaviest chunk 7.10 GB, baseline 3.66 GB) | ≤ 8 GB per module | 0.57 GB (0.90 GB for the heaviest chunk) |
| per declaration | heaviest `ch_FF_10_0_8` 22.21 s | ≤ 300 s | 277.8 s |

Probe figures taken from `docs/reports/T2288-prove.md:89,211`.

### (ii) One concrete nondegenerate instance (`(k, s) = (false, false)`)

Terms: root term 0 (`n_S=3, n_W=2, n_V=2, ord=3 < 4=tg`, ext vertices coincide, 2 candidates, 528 children, all leaves) and term 9 (`n_S=4, n_W=2, n_V=3, ord=2 < 4`, 3 candidates, 12 below-target children each).  No hypothesis is external; instance (2) of the ticket (`rootAt false false 0` is not a leaf, `scalingOrder = 3`, `tgt = 4`, `b = 2`, 2 candidates) is exactly the term-0 row.

```
$ date -u; python3 inst2.py            # scratchpad T2306/inst2.py (uses tree.py partition/candidates/oe2x_families)
Tue Oct  6 15:16:39 UTC 2026
root LWG5Graph false false: nS=5 nW=2 nV=3 ord=3 ; partition terms 163
below target: 11 of 163; leaves: 152
root term 0: nS=3 nW=2 nV=2 ord=3 tg=4 (ext equal: True) ord<tg: True ; candidates 2 ; children 528 ; below-target children per candidate [0, 0]
root term 9: nS=4 nW=2 nV=3 ord=2 tg=4 (ext equal: True) ord<tg: True ; candidates 3 ; children 1599 ; below-target children per candidate [12, 12, 12]

$ python3 rall.py | sed -E '...'      # R-all AND-tree over every candidate at every below-target node (T2288 script)
R-all k=False s=False: below-target root terms 11, distinct (up to iso) below-target nodes 125, with no candidate (stuck) 0, cycles 0, max height of AND-tree 3, candidates examined 332 (max per node 4) ... largest partition 438, not-ok 0  [3s]
R-all k=False s=True: below-target root terms 11, distinct (up to iso) below-target nodes 129, with no candidate (stuck) 0, cycles 0, max height of AND-tree 3, candidates examined 359 (max per node 4) ... largest partition 438, not-ok 0  [4s]
(rows k=True identical)

$ python3 rawcount.py | sed -E "s/'raw_by_k[^}]*//"
k=False s=False {'below_children': 114, 'cand': 332, 'children': 275620, 'inner': 125, 'raw': 89018, } [3s]
k=False s=True {'below_children': 118, 'cand': 359, 'children': 301079, 'inner': 129, 'raw': 97413, } [7s]

$ python3 routeC.py | grep -E "^k=|^ +(0|9|10) " | cut -c1-110     # i ord tg deficit #cands | children per cand
k=False s=False: 163 root terms, 11 below target
  0  3   4    1       2     [264, 264] | ...      (528 = 2 x 264 children)
  9  2   4    2       3     [533, 533, 533] | ...  (1599 = 3 x 533)
 10  3   5    2       3     [1125, 1125, 1125] | ...
(k=False s=True: same rows)

$ probe counts (git show t/T2288:RBM3D/Probe/T2288Cert.lean, 1228 lines), grep -c:
theorem ch_FF_: 78   theorem ch_FT_: 78   theorem chs_FF_: 6   theorem chs_FT_: 6   theorem root_FF_[0-9]: 11   theorem root_FT_[0-9]: 11
```

Non-vacuity: all 11 root terms are below target (instance (3) `!leaf` at all 11), every node has at least 2 candidates (no `default`, no empty candidate list), `k = false` only; the `k = true` rows of `rall.py` are identical (not a target here).

Note (inconsistency check only): the model graphs of the ticket's `root_FF_shape` ("163 partition terms, 11 below the target", probe `:660`) agree with the python `163` / `11` above; python and Lean roots were compared by edge list only (not by Lean evaluation, which is stage 1b).

### Verdict

- `cert_all` (with `cert_FF`, `cert_FT`, `root_F?_shape`, `inner_node_one`, `goodB_succ_of`, instances (2)-(3)): PASS.  The counts close exactly (125 = 11+78+36, 129 = 11+78+40, 78 = 36+42), 0 stuck nodes, height 3 = the `goodB 3` of the target, every hypothesis is a Lean-evaluable fact about one fixed finite tree.  The time and memory figures leave 288 s per half-module against the ticket's 862.5 s, and 0.57 GB against 8 GB, but the re-measurement is stage 1b's and the stop rule applies if a limit is exceeded.

## (b) Script output (stage 1b; written Wed Oct  7 06:04:51 UTC 2026)

```
$ git log --oneline -1 t/T2306; git diff --name-only main...t/T2306
533adf0 T2306: LW-14e-1 computable model and R-all AND-tree kernel certificate (Graph/LWExpCert, S0, S1)
RBM3D/Graph/LWExpCert.lean
RBM3D/Graph/LWExpCertS0.lean
RBM3D/Graph/LWExpCertS1.lean
$ wc -l RBM3D/Graph/LWExpCert*.lean
     291 RBM3D/Graph/LWExpCert.lean
     298 RBM3D/Graph/LWExpCertS0.lean
     311 RBM3D/Graph/LWExpCertS1.lean
     900 total
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWExpCert*.lean; echo grep-exit $?
grep-exit 1
$ grep -c "ofReduceBool\|trustCompiler\|sorryAx" b0.log b1.log b2.log full.log (build outputs)
b0.log:0
b1.log:0
b2.log:0
full.log:0
```

### Builds, one module per invocation, nothing else of mine running (CONTROL H101 (1)); /usr/bin/time -l
```
upstream: lake build RBM3D.Graph.LWExpTerm3 RBM3D.Graph.LWGGExp RBM3D.Graph.LWWeightExp RBM3D.Graph.LWStein RBM3D.Graph.LWVocab  -> Build completed successfully (3881 jobs), 05:32:05-05:32:08 UTC
--- lake build RBM3D.Graph.LWExpCert  (start/end UTC from date -u: 05:32:13 / 05:32:22)
⚠ [3882/3882] Built RBM3D.Graph.LWExpCert (6.1s)
Build completed successfully (3882 jobs).
8.97 real         5.15 user         4.97 sys
3723722752  maximum resident set size
RBM3D/Graph/LWExpCert.lean:284:0: 'RBM.Graph.LWCert.goodB_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Graph/LWExpCert.lean:285:0: 'RBM.Graph.LWCert.inner_node_one' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Graph/LWExpCert.lean:286:0: 'RBM.Graph.LWCert.root_FF_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Graph/LWExpCert.lean:287:0: 'RBM.Graph.LWCert.root_FT_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Graph/LWExpCert.lean:288:0: 'RBM.Graph.LWCert.lwCert_root0_nonleaf' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Graph/LWExpCert.lean:289:0: 'RBM.Graph.LWCert.lwCert_roots_below' depends on axioms: [propext, Classical.choice, Quot.sound]
--- lake build RBM3D.Graph.LWExpCertS0  (start/end UTC from date -u: 05:32:32 / 05:41:54)
⚠ [3883/3883] Built RBM3D.Graph.LWExpCertS0 (558s)
Build completed successfully (3883 jobs).
561.32 real       540.74 user        19.66 sys
7091732480  maximum resident set size
RBM3D/Graph/LWExpCertS0.lean:296:0: 'RBM.Graph.LWCert.cert_FF' depends on axioms: [propext, Classical.choice, Quot.sound]
--- lake build RBM3D.Graph.LWExpCertS1  (start/end UTC from date -u: 05:42:03 / 05:52:19)
⚠ [3884/3884] Built RBM3D.Graph.LWExpCertS1 (612s)
Build completed successfully (3884 jobs).
615.58 real       595.52 user        19.92 sys
6872367104  maximum resident set size
RBM3D/Graph/LWExpCertS1.lean:308:0: 'RBM.Graph.LWCert.cert_FT' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Graph/LWExpCertS1.lean:309:0: 'RBM.Graph.LWCert.cert_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```
probe figures (T2288 prove (b), per ticket): whole probe 1148.6 s / 7.43 GB; heaviest chunk ch_FF_10_0_8 22.2 s / 7.10 GB standalone, baseline 3.66 GB; median chunk 10.8 s / 4.68 GB
limits: each module <= 30 min and <= 8 GB; S0, S1 <= 862.5 s.  Peak bytes above: 3723722752 / 7091732480 / 6872367104 (7.09 GB = 6.60 GiB).
```

### Per-declaration profile of LWExpCertS0 (scratch copy with set_option profiler true, profiler.threshold 500; lake env lean)
```
start Wed Oct 7 05:52:35 UTC 2026
exit=0
Wed Oct  7 06:01:57 UTC 2026
$ grep -c "^type checking took" prof.log
90
$ largest five successive increments of the monotone "type checking took" values (the printed values are cumulative, positions not printed)
18 s (entry 84)
18 s (entry 68)
16 s (entry 72)
16 s (entry 66)
16 s (entry 55)
562.73 real       542.02 user        16.92 sys
6750683136  maximum resident set size
```

### Registry pre-check, scratch copy, and full build
```
$ lake build RBM3D.Test.Axioms  -> Build completed successfully (2 jobs)
$ lake env lean reg.lean   # import RBM3D; import RBM3D.Graph.LWExpCertS1; #assert_rbm_axioms
exit=0; first lines: axiom audit: 8858 theorems, 2873 definitions, 0 axioms in `RBM`; All within [propext, Classical.choice, Quot.sound]; no new premise line mentions LWCert (the module adds no Prop definition)
$ cat ex.lean; lake env lean ex.lean
import RBM3D.Graph.LWExpCertS1
open RBM.Graph.LWCert
example : ∀ s, (rootInfo false s).1 = true ∧ (rootInfo false s).2.all (goodB 3) = true := cert_all
exit=0 (no output)
$ lake build   (worktree, after the three modules; the root RBM3D.lean here is main-at-branch, the hub adds the imports at merge)
2.99 real         1.48 user         3.02 sys
exit=0 (3082 lines of output, no error)
```

### Copy check against the probe at 5f3d37f (probe :224-433, :653-662, :664-1211 vs the three files; blank lines, #print, end and ### headers removed)
```
$ diff probe.txt ours.txt
51c51
< /-- A candidate of a model node (the data of `LWG5Cand` / `oe2x_graph_E`). -/
---
> /-- A candidate of a model node (the data of `oe2x_graph_E`). -/
177a178
> /-! ## The certificate: one inner node, the shapes, and non-vacuity instances -/
186a188,199
> /-- Instance (2): the root term `0` of `(k, s) = (false, false)` is not a leaf, has `scalingOrder 3`, target `4`,
> `2` internal vertices and `2` candidates. -/
> theorem lwCert_root0_nonleaf :
>     leaf (rootAt false false 0) = false ∧ (rootAt false false 0).g.scalingOrder = 3 ∧
>       tgt (rootAt false false 0) = 4 ∧ (rootAt false false 0).b = 2 ∧
>       (cands (rootAt false false 0).g).length = 2 := by
>   decide +kernel
> /-- Instance (3): all `11` below-target root terms of both `s` are not leaves. -/
> theorem lwCert_roots_below :
>     (rootInfo false false).2.all (fun N => !leaf N) = true ∧
>       (rootInfo false true).2.all (fun N => !leaf N) = true := by
>   decide +kernel
diff exit=1
```

### Counts by grep
```
theorem ch_FF_: 78
theorem ch_FT_: 78
theorem chs_FF_: 6
theorem chs_FT_: 6
theorem root_FF_[0-9]: 11
theorem root_FT_[0-9]: 11
```

### Name clash (36 names: the 34 ticket names, lwCert_root0_nonleaf, lwCert_roots_below, LWCert, LWExpCert), main 1d19466
```
main at 1d19466
HIT kids:        1
total hits over 36 names (main, Probe excluded): 1
(the one hit of 'kids' is RCand.kids in LWExpTerm5, namespace RBM.Gauss.Sizes, a qualified name; no clash in RBM.Graph.LWCert)
```

### Statements (extracted by script)
```
theorem cert_all : ∀ s, (rootInfo false s).1 = true ∧ (rootInfo false s).2.all (goodB 3) = true := by
theorem goodB_succ_of (n : ℕ) (N : MNode) (nc : ℕ) (hc : (cands N.g).length = nc) (hnc : 0 < nc)
    (hk : ∀ j < nc, kidsOk N j = true)
    (hch : ∀ j < nc, ∀ l < (kids N j).length, goodB n (kid N j l) = true) :
    goodB (n + 1) N = true := by
theorem inner_node_one : goodB 3 (rootAt false false 0) = true := by
theorem root_FF_shape : (rootInfo false false).1 = true ∧ (rootInfo false false).2.length = 11 := by decide +kernel
theorem root_FT_shape : (rootInfo false true).1 = true ∧ (rootInfo false true).2.length = 11 := by decide +kernel
theorem lwCert_root0_nonleaf :
    leaf (rootAt false false 0) = false ∧ (rootAt false false 0).g.scalingOrder = 3 ∧
      tgt (rootAt false false 0) = 4 ∧ (rootAt false false 0).b = 2 ∧
      (cands (rootAt false false 0).g).length = 2 := by
theorem lwCert_roots_below :
    (rootInfo false false).2.all (fun N => !leaf N) = true ∧
      (rootInfo false true).2.all (fun N => !leaf N) = true := by
theorem cert_FF : (rootInfo false false).1 = true ∧ (rootInfo false false).2.length = 11 ∧ ∀ i < 11, goodB 3 (rootAt false false i) = true := by
theorem cert_FT : (rootInfo false true).1 = true ∧ (rootInfo false true).2.length = 11 ∧ ∀ i < 11, goodB 3 (rootAt false true i) = true := by
```

### Narrative (stage 1b; resumed run, written from the tool log)
- Resumed under CLAUDE.md §3 (H) on the previous run's three uncommitted files (291 / 298 / 311 lines).  The copy check above (script diff against the probe at 5f3d37f) shows they are the probe's lines `:224-433`, `:653-662`, `:664-1211` with only the allowed differences: the `Cand` docstring without `LWG5Cand`, the section header, instances (2) and (3), and the file headers.  The files were kept, not redone.
- One edit this run: the docstring of `LWExpCert.lean` said "never `native_decide`"; reworded so that the grep for `native_decide` is empty (grep above, exit 1).
- CONTROL H101: before the first build `pgrep -fl "bin/lake|bin/lean"` showed a `lake build` of another ticket in the main worktree (`LWExpTerm5`); I waited until it ended (`pgrep` empty at 05:31:55 UTC), then ran the five upstream modules, then the three certificate modules one per invocation, each with an empty `pgrep` immediately before (outputs in the tool log).  `vm_stat` at about 05:31 UTC gave 7123 free + 594900 inactive pages of 16 KiB (about 10 GB, below 12 GB); `memory_pressure` gave "System-wide memory free percentage" 60-64% of 32 GB (`hw.memsize` 34359738368) at each start; I took the latter as the free-memory reading.  No build was killed, no swapping (`0 swaps` in the `time -l` outputs of the three module builds and the profile run), so rule (5) did not apply.
- The profiler run (scratch copy of `LWExpCertS0` with the profiler options, `lake env lean`) started at 05:52:35 UTC while a `lake env lean .../T2308/precheck` of another ticket was running (pgrep output of that moment, tool log); it is a profile, not one of the three timed builds.  Its printed values are cumulative, so the per-declaration figure is the largest successive increment, 18 s, below the 300 s limit.
- Result against the Role-line limits: `LWExpCert` 8.97 s / 3.72 GB; `LWExpCertS0` 561.32 s / 7.09 GB; `LWExpCertS1` 615.58 s / 6.87 GB (limits 30 min, 8 GB, 862.5 s for S0/S1).  Every limit holds; the stop rule did not fire.  The whole certificate (S0 + S1) took 1176.9 s of wall against the probe's 1148.6 s.
- The worktree's `lake build` ran with the root `RBM3D.lean` as on the branch (no import of the new modules; the hub adds it at merge).  The registry pre-check and `#assert_rbm_axioms` import `RBM3D.Graph.LWExpCertS1` explicitly (reg.lean, exit 0).
- Not touched: `RBM3D/Test/Axioms.lean`, `RBM3D.lean`, section (a).  No port from RBM1D/RBM2D (none exists).

## (c) Verified Mathlib / core names used
The code is the probe's; `finSumFinEquiv`, `List.getElem_of_mem`, `List.getD_eq_getElem`, `List.all_eq_true`, `List.getElem?_eq_getElem`, `Bool.or_eq_true` are used as in the probe and elaborate in the three builds above (names not re-grepped separately).  No new Mathlib name was introduced.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new (T2288a-e cover it; T2288e: the leaf bound is a finite kernel certificate, 125 / 129 nodes, where the paper says "verified by inspecting", `B:98`).
- Hub notes (DECISIONS §105 (4)): after the merge, build the three modules in the main worktree alone before cloning the next worktree (S0 561 s and S1 616 s here), so that `cp -c -R .lake/build` carries their `.olean`s.
- Style linters report `longLine` warnings in the module docstrings (lines 16-18 of `LWExpCert.lean`, 11 of S0, 12 of S1); warnings only, as in the upstream LW files.
