Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 02:58:18 UTC 2026

Python only, no Lean. Scripts are copies (originals untouched) of the T2318/T2288 engine (`eng.py`, `tree.py`, `root.py`, `canon.py`, `rall.py`, `lost2.py`, `lost2T.py`) plus new `belowp.py` (mirror of `belowOf` / `belowOf'`, `LWExpCert.lean:157-190`, per family graph and choice), `inst.py`, `cexp.py`, in `scratchpad/ec1cbe39-…/T2319/` (run as `PYTHONPATH=. python3 <script>`). Lean facts are read from files (file:line), not evaluated.

### (i) Exponent table
| row | value | constraint | slack |
|---|---|---|---|
| skip test of `belowOf'` | `X0' = (Δ.dotBase.filter !eq)`, `LGraph.dotBase` `LWVocab.lean:1073` (`dotted.filter !isB`); `(Δ.withDots c).dotted = Δ.dotBase ++ c.2` (`:1094`) | skip iff some `×`-edge of `X0' ++ X1` is inside a class of `E0 ++ E1`; must equal `¬ Consistent (Δ.withDots c)` (`LWVocab.lean:1267`: `∀ e ∈ dotted, e.eq = false → ¬ cls x = cls y`) and `cMerge (Δ.withDots c) = none` (`LWExpCert.lean:88-89`) | equality; `E0` is unchanged because `isB e = true → e.eq = false` (`:1066`) |
| order of a variant | `ord = n_S − t + 2(n_W − B)`, `0 ≤ t ≤ L`, `2^L` variants (`lwSplitLoops`, `LWVocab.lean:1209-1214`, one binary choice per uncircled loop) | `ord(Γ) = n_S + 2(n_W − n_V)`; leaf iff `tg ≤ ord` | `t = 0` is the maximum, so `ok0` is evaluated iff `n_S + 2(n_W − B) ≥ tg` |
| target | `tg = 4` if the images of `x`,`y` coincide, else `5` (`tgt` `:147`) | leaf iff `tg ≤ ord` | min `ord − tg = 0` over leaves |
| leaf thresholds | `n_M ≤ 1`, `n_W ≥ 2`, ≥ 2 solid edges between distinct molecules at each internal molecule, (`x`,`y` merged or distinct molecules or `n_M = 0`) | `ok0` (`:176-183`) | mirror finds 0 failures at all evaluated choices (below); the mirror is sensitive: replacing `n_M ≤ 1` by `n_M ≤ 0`, or `≥ 2` by `≥ 3`, gives 2984 resp. 2548 failing family graphs (`s = F`) |
| AND-tree height | `goodB 3` (`cert_all'`), fuel of `lwG5Expand'` is 4 | `goodB n → goodB (n+1)` | slack 1; max height 3 (below) |
| root | `LWG5Graph k s`: `(a,b) = (1,3)`, `dotted := []` (`LWExpTerm3.lean:59`) | no `×`-edge at the root, so `X0 = X0' = ∅` | `belowOf' = belowOf` at the root; `lostOf = 0` |
| root kid shape | 11 below-target root terms per `s`; per root term and candidate (Lean order: `p` index, then `q` index) `[[0,0]×8, [0,0,0], [12,12,12], [14,14,14]]`, 78 = 3·12 + 3·14 depth-1 nodes, 36 / 40 depth-2 nodes for `s = F / T` (114 − 78, 118 − 78) | equals T2288 audit §4, so the chunk lists are unchanged | exact equality (below) |
| §29 | combinatorial; no time variable, no `1 − iλ²/L²` boundary, no `L^d ≤ W^K`, no `∀ᶠ n`, no `(a,b,sz,n,E,t)` parameter, no scale, no grid lift; no external hypothesis, no authorized input | — | — |

### (ii) Concrete instance (mirror of `belowOf'` over the whole unmemoised R-all tree, `k = false`)
Command `PYTHONPATH=. python3 belowp.py` (per `s`; full output of both blocks equal in the lines shown; `s = True` figures in the second column):
```
s=False root: belowOf' flag True, below-target 11 ; belowOf flag True, below-target 11 ; real partition below-target 11
  kid counts per root term (Lean candidate order = sorted by (p,q)): [[0, 0]x8, [0, 0, 0], [12, 12, 12], [14, 14, 14]]   (both s, verbatim lists)
  max AND-tree height (goodB n minimal n): 3                               s=True: 3
   candidates 332                                                         s=True: 359
   family graphs 3394                                                     s=True: 3685
   choices real-consistent 70253                                          s=True: 76853
   choices consistent under old test 17454                                s=True: 19048
   ok0 evaluated new 70193 / old 17394                                    s=True: 76793 / 18988
   flag NEW false 0   flag old false 0                                    s=True: 0 / 0
   kid count new != real partition below-target 0                         s=True: 0
   below-target kid nodes (unmemoised) 114                                s=True: 118
```
(Rows `x != real partition` count family graphs whose `belowOf'` kid count differs from the below-target terms of `eng.partition`, a separate mirror of `LGraph.partition`: 0, so the lists of below-target children are exactly the real ones; the kid-node total `114 + 11 = 125`, `118 + 11 = 129`.) Memoised tree, `python3 rall.py`: `k=False s=False: below-target root terms 11, distinct (up to iso) below-target nodes 125, stuck 0, cycles 0, max height of AND-tree 3, candidates examined 332`; `s=True: … 129 … stuck 0, cycles 0, max height 3, candidates 359`.
Lost terms (`python3 lost2.py` / `lost2T.py`, real terms of choices that `belowOf` skips, tagged in `eng.partition`):
```
(F,F)  choices real-consistent but model-inconsistent 52799 ; family graphs with a lost choice 3061 / 3394 ; lost terms 212194 ; lost non-leaf (ord < tg) 0 ; lost leaf, some property fails 0
(F,T)  lost terms 231842 ; lost non-leaf (ord < tg) 0 ; lost leaf, some property fails 0 ; (76853 − 19048 = 57805 lost choices)
```
Leaf properties are checked in `belowp.py` in the exact Lean form of `ok0` on every real-consistent choice with `n_S + 2(n_W − B) ≥ tg` (flag NEW false 0, both `s`), and in `lost2.py` in the paper's form (`normal`, `n_M`, `n_W`, `attached`, external condition): 0 failures. **Counts agree with the ticket and T2318 (a): 52799, 212194, 231842, 3061/3394, 125/129, kid lists; no lost non-leaf, no kid count differs: the chunk shape is unchanged.** One ticket figure differs: Route 4 says the corrected flag evaluates the leaf properties on "about 1.75×" as many choices; the mirror gives ok0 evaluated on 70193 vs 17394 choices (`s=F`; 76793 vs 18988 for `s=T`), ratio 4.04, and 70253 vs 17454 consistent choices (ratio 4.02) (not a mathematical issue; for stage 1b's measurement).

**Root term 9, `(k,s) = (F,F)`, candidate 0** (command `PYTHONPATH=. python3 inst.py`; ext `x+y`, ints `a b c`, solid `x+y→a, a→c, c→b, b→x+y`, waved `(c,a),(a,b)`, `n_S,n_W,n_V,n_M = 4,2,3,1`):
```
Lean candidate order by (p index, q index, x): [(1, 0, 'a'), (2, 1, 'c'), (3, 2, 'b')]   (python's order is by vertex: 'a','b','c' = (1,0),(3,2),(2,1); candidate 0 is the same in both)
candidate 0: x=a p=solid[1] q=solid[0] y=c y'=x+y
fams idx fam  #b-edges #aPairs #raw-choices #real-consistent #belowOf-consistent #lost(=lostOf) #kids(non-leaf)
 0 R2 2 1 8 7 2 5 1
 1 R3 0 0 1 1 1 0 1
 2 R4 2 2 16 14 4 10 1
 3 R5 2 2 16 14 4 10 1
 4 R6 2 2 16 14 4 10 1
 5 R7 2 2 16 14 4 10 2
 6 R8 3 3 64 42 6 36 2
 7 R7 2 2 16 12 3 9 1
 8 R8 3 3 64 42 6 36 2
```
(`fams` index = `0:R2, 1:R3 (owxT1), 2:R4, 3:R5, 4:R6`, then `(R7, R8)` per `q' ∈ lwSplit c.q.2`: index 5/6 for the first `q'`, 7/8 for the second; the same order as `fams`, `LWExpCert.lean:138-143`; kids sum `1+1+1+1+1+2+2+1+2 = 12`.) So at fams index 0 (R2): 8 raw choices, 1 aPair, 2 b-edges, 7 real terms, 2 evaluated by `belowOf`, **`lostOf` = 5**; at fams index 6 (first `q'`, R8): 42 real, 6 evaluated, **`lostOf` = 36**, both `> 0`. (`lostOf f.2 = real-consistent − belowOf-consistent` because the `X0'`-test is the weaker one: `X0' ⊆ X0`.)
One lost term (R2, fams index 0), edges of `Δ`: `Gc>b Gb>x+y Gx+y>c | S(c,a) S*(a,b) S+(a,c) | x(x+y,a) x(a,c) x(c,b) x(b,x+y)`; choice `=(x+y,c), =(a,c)` (the b-edges `×(x+y,a)`, `×(a,c)` of `Δ` are dropped by `withDots` and now lie inside one class):
```
classes (E0++E1): [['x+y', 'a', 'c'], ['b']]  B=1 L=1 nS=3 nW=3 tg=4
ord(t) = nS - t + 2(nW - B): {0: 7, 1: 6}
nM=0 nW>=2: True attached: True ext cond: True  leaf (t=0 ord>=tg): True  all variants leaf: True
```
That is `a ~ c ~ x+y`, `B = 1`, `L = 1`, `n_S = 3`, `n_W = 3`, `tg = 4`, `ord = 7 − t`, `n_M = 0`: a leaf with all properties (`ok0` true), no children.
**Counterexample `lwCertB_cex`** (`a = 1`, `b = 0`, `×(0,1)` only; `PYTHONPATH=. python3 cexp.py`):
```
belowOf : flag True, #below-target children 1, #choices evaluated 1
belowOf': flag True, #below-target children 2, #choices evaluated 2
lostOf = 1
real term: ext ['e0', 'e1'] ints [] ord 0 tg 5
real term: ext ['e0+e1'] ints [] ord 0 tg 4
```
Both real terms have `ord 0 < tg` (non-leaves), `tg 5` resp. `4`; `belowOf'` lists both, `belowOf` lists only the first. Root: `(rootInfo' false s).2.length = 11 = (rootInfo false s).2.length` (first line of the block above), `lostOf (LWG5Graph k s) = 0` (`dotted := []`).
Order caveat: python's list order of root terms is the product order of `dotChoices` with `foldr` prepending (same as `lwCombineAtoms` `LWVocab.lean:1081`, `dotChoices` `:1086`); the kid counts (12, 14) and the per-fam counts above are order-independent up to candidate order, and candidate 0 is the same in both orders; the numbers 5 and 36 are the ones for `fams` index 0 and 6 in Lean's order.

### Verdict per target
| target | verdict | reason |
|---|---|---|
| `cert_all'` (`belowOf'`, `goodB'`, `rootInfo'`, chunk lists, height 3) | PASS | skip test equals `¬ Consistent`; 0 lost non-leaf and 0 failing leaf property in both `s`; kid lists, node counts (125/129), height 3 unchanged; flag true at all 3394 / 3685 family graphs |
| `goodB'_succ_of`, `inner_node_one'`, `root_F?_shape'`, `lwCert_root0_nonleaf'`, `lwCert_roots_below'` | PASS | unchanged statements on unchanged lists (root has no b-edge) |
| diagnostic `lostOf`/`lostAt`; instances (5)-(7) | PASS | values 5, 36, `lwCertB_cex` 1/2 terms and `lostOf = 1`, root equality: all nonzero/nondegenerate as asserted by the ticket (lines above) |
Overall: **PASS**.

## (a′) Preflight corrections

None: section (a) was not edited; no mistake found that changes a statement or a verdict.

## (b) Script output — stage 1b, written Thu Oct  8 04:37:29 UTC 2026

```
$ git log --oneline -1; git diff --name-only main...t/T2319
0ed1177 T2319: corrected lite flag belowOf' and the R-all kernel certificate cert_all' (LWExpCertB, BS0, BS1)
RBM3D/Graph/LWExpCertB.lean
RBM3D/Graph/LWExpCertBS0.lean
RBM3D/Graph/LWExpCertBS1.lean

$ wc -l (three files)
     243 RBM3D/Graph/LWExpCertB.lean;     566 RBM3D/Graph/LWExpCertBS0.lean;     597 RBM3D/Graph/LWExpCertBS1.lean;    1406 total;

$ builds, one module per `lake build`, alone (checked: no lake/lean process in `ps` before BS0 and BS1; `memory_pressure` free 68% before BS0; hw.memsize 34359738368)
/usr/bin/time -l lake build RBM3D.Graph.LWExpCertB   (final run, after the helper lemmas were added)
8.52 real         6.65 user         5.45 sys
3868065792  maximum resident set size
Build completed successfully (3883 jobs).

/usr/bin/time -l lake build RBM3D.Graph.LWExpCertBS0
start Thu Oct  8 03:08:31 UTC 2026
exit 0
end Thu Oct  8 03:33:00 UTC 2026
1469.39 real      1437.20 user        53.18 sys
6256082944  maximum resident set size
Build completed successfully (3884 jobs).

/usr/bin/time -l lake build RBM3D.Graph.LWExpCertBS1
start Thu Oct  8 03:33:17 UTC 2026
exit 0
end Thu Oct  8 04:02:47 UTC 2026
1769.72 real      1709.49 user        66.36 sys
6376062976  maximum resident set size
Build completed successfully (3885 jobs).

$ grep -c "ofReduceBool\|trustCompiler\|sorryAx" of the three build outputs
B: 0
BS0: 0
BS1: 0

$ #print axioms lines of the three module builds (grep LWExpCertB in build output)
LWExpCertB.lean:229 goodB_succ_of' : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:230 inner_node_one' : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:231 root_FF_shape' : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:232 root_FT_shape' : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:233 lwCert_root0_nonleaf' : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:234 lwCert_roots_below' : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:235 lwcertB_nokids : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:236 lwcertB_onekid : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:237 lwcertB_two : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:238 lwCertB_lost_R2 : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:239 lwCertB_lost_R8 : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:240 lwCertB_cex_bites : [propext, Classical.choice, Quot.sound]
LWExpCertB.lean:241 lwCertB_root_eq : [propext, Classical.choice, Quot.sound]
LWExpCertBS0.lean:564 cert_FF' : [propext, Classical.choice, Quot.sound]
LWExpCertBS1.lean:594 cert_FT' : [propext, Classical.choice, Quot.sound]
LWExpCertBS1.lean:595 cert_all' : [propext, Classical.choice, Quot.sound]

$ grep -nE "sorry|admit|^axiom|native_decide" (three files)
RBM3D/Graph/LWExpCertB.lean:0
RBM3D/Graph/LWExpCertBS0.lean:0
RBM3D/Graph/LWExpCertBS1.lean:0
```
```
$ pin check: ticket lines 26-63 against the file (diff, verbatim)
belowOf' : IDENTICAL to the ticket pin

$ diff <(tr -d "'" < LWExpCertB.lean) <(sed -n '152,215p;226,282p' LWExpCert.lean | tr -d "'")  -- hunks (line ranges) and the one changed code line
1,34d0 45c11 99,100d64 158,243d121 
<   let X0 : List (ℕ × ℕ) := (Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)   -- T2319: was `Δ.dotted` (T2306); `withDots` keeps `dotBase` only
>   let X0 : List (ℕ × ℕ) := (Δ.dotted.filter fun e => !e.eq).map (pairOf a b)
<   let X0 : List (ℕ × ℕ) := (Δ.dotted.filter fun e => !e.eq).map (pairOf a b)
<   let X0 : List (ℕ × ℕ) := (Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)

$ chunk copy checks (tr -d "'" both sides): lines of the diff by kind
S0: added-in-B lines not chc_/chd_ lines: 3; removed (old ch_ lines): 78; other removed: 2
S1: added-in-B lines not chc_/chd_ lines: 4; removed (old ch_ lines): 78; other removed: 4

$ declaration counts (grep)
ch_FF_ 78, ch_FT_ 78, chs_FF_ 6, chs_FT_ 6, root_FF_i' 11, root_FT_i' 11, chc_ 477, chd_ 76

$ per-node shape data (Lean #eval dump: s i j l nc [kid counts per candidate]); totals per s: nodes, candidates, depth-2 nodes
{'false': [78, 231, 36], 'true': [78, 246, 40]}

$ target statements extracted (sed by line range)
def belowOf' (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)) : Bool × List MNode :=
  let n := a + 1 + b
theorem goodB_succ_of' (n : ℕ) (N : MNode) (nc : ℕ) (hc : (cands N.g).length = nc) (hnc : 0 < nc)
    (hk : ∀ j < nc, kidsOk' N j = true)
    (hch : ∀ j < nc, ∀ l < (kids' N j).length, goodB' n (kid' N j l) = true) :
    goodB' (n + 1) N = true := by
583:theorem cert_all' : ∀ s, (rootInfo' false s).1 = true ∧ (rootInfo' false s).2.all (goodB' 3) = true := by
584-  intro s
RBM3D/Graph/LWExpCertBS0.lean:545:theorem cert_FF' : (rootInfo' false false).1 = true ∧ (rootInfo' false false).2.length = 11 ∧ ∀ i < 11, goodB' 3 (rootAt' false false i) = true
RBM3D/Graph/LWExpCertBS1.lean:563:theorem cert_FT' : (rootInfo' false true).1 = true ∧ (rootInfo' false true).2.length = 11 ∧ ∀ i < 11, goodB' 3 (rootAt' false true i) = true
theorem lwCertB_lost_R2 : lostAt (rootAt' false false 9) 0 0 = 5 := by decide +kernel
theorem lwCertB_lost_R8 : lostAt (rootAt' false false 9) 0 6 = 36 := by decide +kernel
/-- Instance (6): the counterexample is covered: `belowOf` lists `1` term, `belowOf'` lists `2`, `lostOf = 1`. -/
theorem lwCertB_cex_bites :
    (belowOf (a := 1) (b := 0) lwCertB_cex ![0, 1]).2.length = 1 ∧
    (belowOf' (a := 1) (b := 0) lwCertB_cex ![0, 1]).2.length = 2 ∧
    lostOf (a := 1) (b := 0) lwCertB_cex = 1 := by
  decide +kernel
theorem lwCertB_root_eq :
    (rootInfo' false false).2.length = (rootInfo false false).2.length ∧
    lostOf (a := 1) (b := 3) (LWG5Graph false false) = 0 ∧
    lostOf (a := 1) (b := 3) (LWG5Graph false true) = 0 := by
  decide +kernel
theorem inner_node_one' : goodB' 3 (rootAt' false false 0) = true
theorem root_FF_shape' : (rootInfo' false false).1 = true ∧ (rootInfo' false false).2.length = 11
theorem root_FT_shape' : (rootInfo' false true).1 = true ∧ (rootInfo' false true).2.length = 11
theorem lwCert_root0_nonleaf' :
    leaf (rootAt' false false 0) = false ∧ (rootAt' false false 0).g.scalingOrder = 3 ∧
      tgt (rootAt' false false 0) = 4 ∧ (rootAt' false false 0).b = 2 ∧
      (cands (rootAt' false false 0).g).length = 2 := by
  decide +kernel
theorem lwCert_roots_below' :
    (rootInfo' false false).2.all (fun N => !leaf N) = true ∧
      (rootInfo' false true).2.all (fun N => !leaf N) = true := by
  decide +kernel

$ compiled application of the target (scratch file, lake env lean)
import RBM3D.Graph.LWExpCertBS1
open RBM.Graph.LWCert
example : ∀ s, (rootInfo' false s).1 = true ∧ (rootInfo' false s).2.all (goodB' 3) = true := cert_all'
exit 0
```
```
$ public declarations of LWExpCertB.lean (grep -noE)
40:belowOf' 75:childrenB' 80:goodB' 87:rootInfo' 89:rootAt' 92:kids' 95:kidsOk' 98:kid' 101:goodB_succ_of' 134:inner_node_one' 142:root_FF_shape' 143:root_FT_shape' 147:lwCert_root0_nonleaf' 154:lwCert_roots_below' 166:lwcertB_candGood 169:lwcertB_nokids 175:lwcertB_onekid 183:lwcertB_two 189:lostOf 202:lostAt 208:lwCertB_cex 212:lwCertB_lost_R2 213:lwCertB_lost_R8 216:lwCertB_cex_bites 223:lwCertB_root_eq 

$ name-clash grep over RBM3D/ (excluding Probe and the three new files); positive control = same pattern inside the new files
occurrences in RBM3D/ + RBM3D.lean outside the new files:        0
  (of which Probe/:        0 not counted)
positive control, occurrences inside the new files: RBM3D/Graph/LWExpCertB.lean:72 RBM3D/Graph/LWExpCertBS0.lean:472 RBM3D/Graph/LWExpCertBS1.lean:498 
T2318 ticket files (mentions as consumers / declaration lines):
  T2318.md: 0 / 0
  T2318-amend-1.md: 5 / 0
  T2318-check.lean: 38 / 0

$ heaviest chunk of T2306, ch_FF_10_0_8', primed, standalone (lake env lean on scratch file importing LWExpCertB, before the split)
51.16 real        45.33 user         4.86 sys
11887296512  maximum resident set size
$ the seven split declarations of the same node (4 chc, 2 chd, cands count), standalone scratch file
50.66 real        47.27 user         2.81 sys
5173723136  maximum resident set size

$ set_option profiler true, threshold 500 ms, lake env lean on a scratch copy of LWExpCertBS0.lean (the profiler prints cumulative wall times; per-declaration = consecutive differences)
1635.51 real      1572.59 user        57.11 sys
5975605248  maximum resident set size
start Thu Oct  8 04:03:07 UTC 2026
exit 0
end Thu Oct  8 04:30:23 UTC 2026
357 declarations above 0.5 s; largest five (s): [11.0, 12.0, 12.0, 20.0, 20.0] ; last cumulative time: 1630.0 (3 significant digits)

$ registry pre-check: import RBM3D + import RBM3D.Graph.LWExpCertBS1 + #assert_rbm_axioms (lake env lean), first lines and exit code
exit 0
axiom audit: 9811 theorems, 2945 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
lines naming the new modules or declarations: 0

$ full lake build (worktree; root RBM3D.lean does not import the new modules, the hub adds the imports at merge)
Build completed successfully (4126 jobs).
2.01 real         1.45 user         3.13 sys
769802240  maximum resident set size
ofReduceBool/trustCompiler/sorryAx lines: 0
```

### Narrative (stage 1b)
- Branch `t/T2319`, commit `0ed1177` (identity Jun Yin from `.git/config`); the diff against `main` is the three sole writable files; no other file touched. No port from RBM1D/RBM2D (the three files copy RBM3D's merged `LWExpCert*.lean`; no diff-stat applies).
- `belowOf'` is the ticket pin verbatim (diff above: IDENTICAL); against `LWExpCert.lean:152-215, 226-282` the one changed code line is `X0` (hunk `45c11`); the other hunks are the header/imports (`1,34d0`), the docstring and blank line before `goodB_succ_of'` (`99,100d64`), and the new tail (`158,243d121`: the helper lemmas below, the diagnostic, the instances, the `#print axioms` lines). `all_of_getD` is imported, not copied.
- Route 4 outcome: the heaviest chunk `ch_FF_10_0_8'` standalone took 51.16 s / 11.89 GB max RSS, above the 8 GB limit, so the per-candidate split was applied to every `ch_F?_i_j_l'` (78 per `s`): 477 `chc_` (one per candidate: `kidsOk' K c = true ∧ (kids' K c).length = m_c`), 76 `chd_` (one per below-target depth-2 node, 36 + 40), and `ch_F?_i_j_l' : goodB' 2 K = true` with the original name and statement. The numbers `nc`, `m_c` come from a Lean `#eval` dump (`dump.lean` output, 156 lines, totals above: 231/246 candidates, 36/40 depth-2 nodes = the ticket's counts); every one is then proved by `decide +kernel`.
- The assembly of `ch_F?_i_j_l'` uses four helper declarations added to `LWExpCertB.lean` (`lwcertB_candGood`, `lwcertB_nokids`, `lwcertB_onekid`, `lwcertB_two`; stem-prefixed, E) and one line per node (`interval_cases c; exacts [...]`) instead of a `match` block per node; the whole delivery is 1406 lines (ticket stop threshold 1500; estimate hi 1000 + 2·250).
- All kernel facts hold as stated: every `chc_`, `chd_`, `ch_`, `chs_`, `root_F?_i'`, `cert_FF'`, `cert_FT'`, `cert_all'` compiled with `decide +kernel`; the kid counts 12 / 14 (`root_F?_9'`, `root_F?_10'`) and the 11 root terms are the kernel's own facts (no lost non-leaf appeared).
- Limits (ticket acceptance): `LWExpCertBS0` 1469.39 s (24.5 min) and 6.26 GB, `LWExpCertBS1` 1769.72 s (29.5 min) and 6.38 GB: both under 30 min and 8 GB; `LWExpCertBS1` is 30.3 s under the 30 min limit. T2306 figures (ticket): 563.9 s / 6.99 GB and 621.2 s / 7.01 GB, i.e. 2.61x and 2.85x the time. Heaviest chunk: 51.16 s / 11.89 GB against T2306's 22.2 s / 7.10 GB (2.30x, 1.67x; the ticket's expectation was 1.3-1.8x time, up to 1.3x memory; the preflight had already noted the 1.75x vs 4.04x choice count). The profiler run on a scratch copy of `LWExpCertBS0`: 357 declarations above 0.5 s, largest five about 11, 12, 12, 20, 20 s (differences of cumulative 3-significant-digit times, so resolution 5-10 s), all far below 5 min.
- H101 conditions: no `lake`/`lean` process was in `ps` before `LWExpCertBS0` and before `LWExpCertBS1`; no build ran in parallel with either (the scratch measurements ran before / after, one at a time). Memory before each build from `vm_stat` (page 16384 B): BS0 `Pages free` 93573 (1.43 GiB), free + inactive 10.54 GiB; BS1 `Pages free` 228039 (3.48 GiB), free + inactive 12.53 GiB; `memory_pressure` said 68% free (32 GiB machine) before BS0 and 69% after it; I did not read `memory_pressure` right before BS1. Neither build was killed and none was retried (both exit 0). Peak memory is `maximum resident set size` of `/usr/bin/time -l` as above.
- The registry pre-check printed no line naming the new modules or declarations (exit 0). The worktree's `lake build` finished in 2.0 s because `RBM3D.lean` does not import the three modules; the hub adds the imports at merge and runs the full build (the three modules are built, `.olean` in the worktree `.lake/build`).
- Instances (CLAUDE.md §4 step 2): `cert_all'` applied in a scratch file (`example` above, exit 0); (1) `inner_node_one'`, (2) `lwCert_root0_nonleaf'`, (3) `lwCert_roots_below'`, (4) `root_F?_shape'`, (5) `lwCertB_lost_R2 = 5`, `lwCertB_lost_R8 = 36`, (6) `lwCertB_cex_bites` (1 / 2 / 1), (7) `lwCertB_root_eq`: all compiled by `decide +kernel`, axioms listed above. The R2/R8 values equal the preflight (a) mirror values (5, 36), and the cex values equal (a).

## (c) Mathlib/core names used (compiled in `goodB_succ_of'` and the helpers)
`List.getElem_of_mem`, `List.getD_eq_getElem`, `List.getElem?_eq_getElem`, `List.all_eq_true`, `Bool.or_eq_true` (as in T2306); tactics `interval_cases`, `omega`, `decide +kernel`. No name was checked for absence.

## (d) Open issues and paper-delta candidates
- Time margin: `LWExpCertBS1` is 30.3 s below the 30 min module limit (1769.72 s); a slower machine or a concurrent job would exceed it. Dispatcher question for the hub's merge-time builds and for the auditor's alone-build.
- The unprimed T2306 modules (`LWExpCert`, `LWExpCertS0`, `LWExpCertS1`) are unchanged and, after T2318, have no consumer (ticket remark; not decided here).
- `LWExpCertB.lean` module docstring (7 style warnings) and `LWExpCertBS0.lean`/`BS1.lean` docstrings (2 each) exceed 100 characters (linter warnings only; `set_option linter.style.longLine false` comes after the docstring, as in the source files).
- Paper-delta candidates: none new (`T2288e` covers the kernel certificate; the corrected flag follows `dot-def`, `7_8:217-218`).

## Repair — Thu Oct  8 08:23:50 UTC 2026 (repairer claude-opus-5-5; audit round 1 RETURN, items 1-3)
```
$ sed -i '' "s/goodB_succ_of'/goodB'_succ_of/g" (3 files); per file: git show 0ed1177:$f | sed (same) | diff - $f
LWExpCertB.lean: only rename   LWExpCertBS0.lean: only rename   LWExpCertBS1.lean: only rename
$ git log --oneline -1; git diff --stat HEAD~1 HEAD | tail -1; git diff --name-only main...t/T2319 | wc -l
6cbecb2 T2319 repair: rename goodB_succ_of' to the pinned goodB'_succ_of (audit round 1) | 27 ins, 27 del | 3 files
$ grep -c "goodB_succ_of'" / "goodB'_succ_of" (B, BS0, BS1): 0 0 0 / 5 12 11; clash grep, main RBM3D/ + RBM3D.lean: 0
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertB      07:26:36-07:26:45  exit 0  9.26 real  3837378560 max RSS
LWExpCertB.lean:229:0: 'RBM.Graph.LWCert.goodB'_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound]
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertBS0    07:26:52-07:53:20  exit 0  1587.79 real  6286311424 max RSS
  before: other lean/lake procs 0; vm_stat free+inactive+speculative 716062 pages = 11.73 GB; Swapouts +88 pages
RBM3D/Graph/LWExpCertBS0.lean:564:0: 'RBM.Graph.LWCert.cert_FF'' depends on axioms: [propext, Classical.choice, Quot.sound]
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertBS1    07:53:32-08:22:14  exit 0  1722.61 real  6336053248 max RSS
  before: other lean/lake procs 0; vm_stat free+inactive+speculative 797324 pages = 13.06 GB; Swapouts +0 pages
RBM3D/Graph/LWExpCertBS1.lean:594:0: 'RBM.Graph.LWCert.cert_FT'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Graph/LWExpCertBS1.lean:595:0: 'RBM.Graph.LWCert.cert_all'' depends on axioms: [propext, Classical.choice, Quot.sound]
$ 30 s ps monitor of other lake/lean processes during BS0 / BS1: 0 / 0 lines; ofReduceBool|trustCompiler|sorryAx|error: 0 / 0
$ lake env lean chk.lean  (import LWExpCertBS1, LWExpSim; all 34 `#check @RBM.Graph.LWCert.*` of T2318-check.lean; #print axioms)
exit 0   (error lines: 0; the #check output below is abridged, line breaks joined)
RBM.Graph.LWCert.goodB'_succ_of : ∀ (n : ℕ) (N : RBM.Graph.LWCert.MNode) (nc : ℕ),
  (RBM.Graph.LWCert.cands N.g).length = nc → 0 < nc → (∀ j < nc, RBM.Graph.LWCert.kidsOk' N j = true) → …
'RBM.Graph.LWCert.goodB'_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- Only the name changed; no statement, proof or other file changed. Lines of (b)-(c) above that say `goodB_succ_of'` describe commit `0ed1177`; at `6cbecb2` the declaration is `goodB'_succ_of` (`LWExpCertB.lean:101`). `LWExpSim` is imported in `chk.lean` only for T2318-check's `MNode.toP`/`Cand.toR` (T2311); without it those 2 lines are unknown, the other 32 compile.
- H101/H118: the two certificate builds ran one at a time, neither was killed or retried. Free memory before BS0 was 11.73 GB, below 12 GB, but no other build was running, so there was nothing to wait for. BS1 took 1722.61 s, 77.4 s under the 30 min limit.
