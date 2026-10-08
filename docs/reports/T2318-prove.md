Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 10:25:30 UTC 2026

Python only, no Lean anywhere. Scripts (scratchpad `T2318/`, run as `PYTHONPATH=. python3 <script>` there): `eng.py`, `tree.py`, `canon.py` (mirror of `LGraph.partition`, `oe2x*`, `candidates`, from the T2265/T2288 engine), `belowp_lib.py` (copy of T2319's mirror of `belowOf` / `belowOf'`), new `pre2318b.py`, `child2318.py`, `keys2318.py`, `cexp2318.py`. Lean facts are read from the files (file:line), not evaluated. Tree totals (`lost non-leaf`, `lost leaf failing`, node counts, height) are T2319's preflight numbers, cited from `docs/reports/T2319-prove.md` (a) (written Thu Oct  8 02:58:18 UTC 2026), not recomputed.

### (i) Exponent table
| row | value | constraint | slack |
|---|---|---|---|
| skip test of `belowOf'` | `X0' = Δ.dotBase.filter (!eq)` (`LWExpCertB.lean:45`); `dotBase = dotted.filter (!isB)` (`LWVocab.lean:1073`); `(Δ.withDots c).dotted = Δ.dotBase ++ c.2` (`:1091-1094`); `isB e = true → e.eq = false` (`:1066`) | skip iff some `×`-edge of `X0' ++ X1` has its ends in one class of the `=`-edges `E0 ++ E1`; this is `¬ Consistent (Δ.withDots c)` and `cMerge (Δ.withDots c) ext = none` (`LWExpCert.lean:88-89`), exact for every `Δ` (no b-edge-free hypothesis); `E0` is unchanged because `isB` edges are `×` | equality; mirror: evaluated-choice count of `belowOf'` = real-consistent count at all 9 family graphs of root term 9 (table in (ii)); old test is stronger, `X0' ⊆ X0` |
| order of a variant | `ord = n_S − t + 2(n_W − B)`, `0 ≤ t ≤ L`, `2^L` variants (`lwSplitLoopsX`, `LWExpTerm5.lean:91`: per uncircled loop `[kept circled, dropped]`); `ord(Γ) = n_S + 2(n_W − n_V)` (`(eq:ordG)`, `7_8:272`) | leaf iff `tg ≤ ord` (`leaf` `LWExpCert.lean:150`) | `t = 0` has the maximal order, so `ok0` is evaluated iff `n_S + 2(n_W − B) ≥ tg`; the list is built iff `n_S − L + 2(n_W − B) < tg` |
| target | `tg = 4` if `ext 0 = ext 1` else `5` (`tgt` `LWExpCert.lean:147`) | leaf iff `tg ≤ ord` | min `ord − tg = 0` over leaves (T2319 mirror: 0 failing leaf properties) |
| leaf thresholds | `n_M ≤ 1`, `n_W ≥ 2`, `≥ 2` solid edges between distinct molecules at each internal molecule, (ends of `x`,`y` merged, or distinct molecules, or `n_M = 0`) | `ok0` flag (`LWExpCert.lean:176-183`) | unchanged by `belowOf'`; T2319 mirror: `flag NEW false 0` for both `s` over all 3394 / 3685 family graphs |
| `(j,j')` shifts | R2, R4, R6, R8: `(3,0)`; R3, R5, R7: `(1,0)` (`famsX`, `LWExpSim.lean`) plus loop split `(j,j')` | `Δord = +1` per family | exactly `+1`; `Rel` ignores coefficients |
| fuel vs height | AND-tree height `3` (`goodB' 3`, `cert_all'`), fuel `4` (`expandRoot selClassical 4`) | `goodB' n → goodB' (n+1)` | slack `1` (T2319: max AND-tree height 3, both `s`) |
| root | `LWG5Graph k s`: `(a,b) = (1,3)`, no dotted edge (`LWExpTerm3.lean:54-60`); `k` is the `col` of one waved edge (`:58`) | no `×`-edge at the root, so `X0 = X0'` | `rootInfo' = rootInfo` as lists (11 terms, 11 below target); `Rel` compares waved endpoints only (`LWExpSim.lean:120`) |
| `k = true` keys | colour-erased lists of `cPartitionX (LWG5Graph true s) ![0,1]` and of `(false, s)` | equal (`soundRoot`, L8 (d)) | 163 terms each, equal for both `s` (below) |
| §29 | combinatorial; no time variable, no `1 − iλ²/L²` boundary, no `L^d ≤ W^K`, no `∀ᶠ n`, no scale; no external hypothesis, no authorized input | — | — |

### (ii) Concrete instance (python mirror, all hypotheses at once; `N = rootAt' false false 9`)
Command `python3 pre2318b.py` (first block):
```
root term 9 (k,s)=(F,F): ext ['x+y'] ints ['a', 'b', 'c'] (nS,nW,nV,nM)= (4, 2, 3, 1) ord 2 tg 4  (a,b)=(0,3)
candidate 0 (Lean order by (p,q)): x=a p=solid[1] q=solid[0] y=c y'=x+y
corrected flag at every family graph of the candidate: (fams idx, family, #b-edges, #raw, #real-consistent (= cMerge some), #belowOf-evaluated, #belowOf'-evaluated, flag belowOf', #below-target kids (belowOf'))
  0 R2 2 8 7 2 7 True 1
  1 R3 0 1 1 1 1 True 1
  2 R4 2 16 14 4 14 True 1
  3 R5 2 16 14 4 14 True 1
  4 R6 2 16 14 4 14 True 1
  5 R7 2 16 14 4 14 True 2
  6 R8 3 64 42 6 42 True 2
  7 R7 2 16 12 3 12 True 1
  8 R8 3 64 42 6 42 True 2
```
Evaluated = real at every family graph (columns 5 vs 7); old `belowOf` evaluates 2/1/4/4/4/4/6/3/6. `lostAt` = real − old: `5` at fams 0 (R2) and `36` at fams 6 (R8) (T2319 instances, `LWExpCertB.lean:212-213`). `fams` order `0:R2, 1:R3, 2:R4, 3:R5, 4:R6`, then `(R7, R8)` per `q' ∈ lwSplit c.q.2` (`LWExpSim.lean` `famsX`). Below-target kids sum `1+1+1+1+1+2+2+1+2 = 12`.

**`relKids`, `relInvariance` at the same node** (`python3 child2318.py`):
```
children (all partition terms of the 8 family graphs R2..R8): 533 ; below target: 12
first below-target child: family R2 (j,j') = (3, 0) a = 0 b = 3 ord 3 tg 4 leaf False
   edges: Gc>b Gb>x+y Gx+y>c | S(c,a) S*(a,b) S+(a,c) | x(c,b) x(b,x+y) x(x+y,c)
   Rel witnesses (rank by first vertex): eE {'x+y': 0} eI {'a': 0, 'b': 1, 'c': 2}
```
(`Rel` ignores the waved colours `S+`/`S*` and the coefficient; `eE : Fin 1 ≃ {x+y}`, `eI : Fin 3 ≃ {a,b,c}`; `rel_self` gives `Rel N (N.toP _)`, `a = 0` so `ext` is surjective onto `Fin 1`.)

**Instance (5), a term the old certificate did not cover** (`python3 pre2318b.py`, second block): `f := ((fams N.g c)[0]).2` (R2), `ext := N.ext`, `ext` surjective (`N.a = 0`, `Fin 1`):
```
R2 family graph edges: Gc>b Gb>x+y Gx+y>c | S(c,a) S*(a,b) S+(a,c) | x(x+y,a) x(a,c) x(c,b) x(b,x+y) | aPairs [('x+y', 'c')] | b-edges [('x+y', 'a'), ('a', 'c')] | ext ['x+y'] ints ['a','b','c'] | em {'x': 'x+y', 'y': 'x+y'}
  choice 0 [=(x+y,c)] first 0 nvar 2 classes [[x+y,c],[a],[b]] B 2 L 1 tg 4 ords [5, 4]
  choice 1 [=(x+y,c), =(a,c)] first 2 nvar 2 classes [[x+y,a,c],[b]] B 1 L 1 nS 3 nW 3 tg 4 ords [7, 6]
  choice 2 [=(x+y,c), =(x+y,a)] first 4 nvar 2 classes [[x+y,a,c],[b]] B 1 L 1 ords [7, 6]
  choice 3 [=(x+y,c), =(x+y,a), =(a,c)] first 6 nvar 2 classes [[x+y,a,c],[b]] B 1 L 1 ords [7, 6]
  choice 4 [x(x+y,c)] first 8 nvar 1 B 3 L 0 ords [3]
  choice 5 [x(x+y,c), =(a,c)] first 9 nvar 1 B 2 L 0 ords [5]
  choice 6 [x(x+y,c), =(x+y,a)] first 10 nvar 1 B 2 L 0 ords [5]
  choice 7 inconsistent (cMerge = none)
(cPartitionX f N.ext).length for R2 = 11
merged-b-edge term: choice 1 i = 2 (variant t=0, loop kept circled) ... ord(t) [7, 6] leaf(ord>=tg) at t=0: True
eng.partition term at i=2: ext ['a+c+x+y'] ints ['b'] ord 7 tg 4 nM 0 leaf True
```
So `i = 2` (choices in the order of `dotChoices`: aPair `=`/`×` first, then the two b-edges `[ , =]`; `lwSplitLoopsX` lists the kept-circled variant first): `(cPartitionX f N.ext).length = 11`, the term has classes `a ~ c ~ x+y`, `B = 1`, `L = 1`, `n_S = 3`, `n_W = 3`, `tg = 4`, `ord = 7 − t`, `n_M = 0`, `leaf = true` at `t = 0` and `t = 1` (indices 2 and 3, `ord` 7 and 6 `≥ 4`). The merged b-edge is `=(a,c)` (dropped by `withDots`, so the old test, which keeps `×(a,c)` in `X0`, skipped this choice). All properties: `n_M = 0 ≤ 1` (printed above), `n_W = 3 ≥ 2`, `n_M = 0` so the attachment and the external condition are vacuous. In the mirror all 7 consistent choices pass `ok0` (flag `True` above).

**Counterexample graph now listed by `belowOf'`** (`python3 cexp2318.py`; `a = 1`, `b = 0`, `Δ.dotted = [×(0,1)]`, `ext = ![0,1]` onto):
```
belowOf : flag True, #below-target children 1, #choices evaluated 1
belowOf': flag True, #below-target children 2, #choices evaluated 2
lostOf = 1
real term: ext ['e0', 'e1'] ints [] ord 0 tg 5
real term: ext ['e0+e1'] ints [] ord 0 tg 4
```
Both real terms are non-leaves (`ord 0 < tg`); `belowOf'` lists both (the old `belowOf` only the first, which made the 02:11 `BelowOfSound` false).

**`k = true`** (`python3 keys2318.py`):
```
s=False: partition sizes k=F/k=T 163/163 ; colour-erased key lists equal: True ; below-target roots F/T 11/11
s=True: partition sizes k=F/k=T 163/163 ; colour-erased key lists equal: True ; below-target roots F/T 11/11
```
Both lists equal, so no second certificate pair (DECISIONS §119 O2); the Lean kernel equality is then a `decide +kernel` fact of 163 terms per `s`.

### Verdict per target
| target | verdict | reason |
|---|---|---|
| 1 `relInvariance` | PASS | no exponent; instance above; leaf properties read endpoints only (colour-blind) |
| 2 `relKids` (+ `Rel.ext_surj`, `goodB'_mono`) | PASS | converse of `Rel.cand`; the 7 families only map waved edges; instance node above (3 candidates, 12 below-target kids at candidate 0) |
| 3 `belowOfSound` (`belowOf'`) | PASS | skip test = `cMerge (Δ.withDots c) = none` for every `Δ`; evaluated = real at all 9 family graphs; instance (5) and the counterexample graph are covered; hypotheses (`ext` onto) hold |
| 4 `soundStep` (`childrenB'`) | PASS | `belowOfSound` at each `fams` member (flags true at the 9 family graphs above) composed with `childrenSim`; no hypothesis beyond `(childrenB' N c).1 = true` |
| 5 `soundRoot` (`rootInfo'`) | PASS | root has no dotted edge (`belowOf' = belowOf`), `k = true` keys equal (above) |
| 6 `lwG5LeafProps_holds` | PASS | needs 3-5 and `cert_all'` (height 3 ≤ fuel 4, `goodB'_mono`); T2319: flag true at 3394 / 3685 family graphs, 0 lost non-leaf, 0 failing leaf property |
| 7 `lwG5ExpandSplit_iff`, `lwG5LeafProps_iff`, `lwG5ExpandOfHalves` | PASS | `Iff.rfl` / definitional (no mathematical content) |
| 8 `lwG5Expand'_holds` | PASS | identity half `lwExpandIdentity_holds selClassical 4` (T2307) with 6 |
Overall: **PASS**.

## (b) Script output

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2318`, branch `t/T2318`, commit `4eda3d252c86838c3ec62c859a2aa7091fcc5041` (parent `7b9fefe`). First tool call of this stage `Thu Oct  8 10:25:30 UTC 2026`; commit amended `Thu Oct  8 11:43:39 UTC 2026`. Raw outputs: scratchpad `T2318/rep/` (not committed).

### Build (`date -u` before `Thu Oct  8 11:43:06 UTC 2026`, after `Thu Oct  8 11:43:23 UTC 2026`; exit 0)
```
$ lake build RBM3D.Graph.LWExpSound
⚠ [3883/3888] Replayed RBM3D.Graph.LWExpCert
⚠ [3885/3888] Replayed RBM3D.Graph.LWExpCertB
⚠ [3886/3888] Replayed RBM3D.Graph.LWExpCertBS0
⚠ [3887/3888] Replayed RBM3D.Graph.LWExpCertBS1
ℹ [3888/3888] Built RBM3D.Graph.LWExpSound (15s)
info: RBM3D/Graph/LWExpSound.lean:1318:0: '_private.RBM3D.Graph.LWExpSound.0.RBM.Gauss.Sizes.lwExpSound_key_FF' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Graph/LWExpSound.lean:1319:0: '_private.RBM3D.Graph.LWExpSound.0.RBM.Gauss.Sizes.lwExpSound_key_FT' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3888 jobs).
lake build RBM3D.Graph.LWExpSound  20.20s user 5.19s system 149% cpu 16.927 total
```
### Size, hygiene, imports, unprimed names (the tool shell `grep` is ugrep, which supports `-P`)
```
$ wc -l RBM3D/Graph/LWExpSound.lean
    1490 RBM3D/Graph/LWExpSound.lean
$ grep -cE '\b(sorry|admit|native_decide)\b|^axiom' RBM3D/Graph/LWExpSound.lean
0
$ grep -nP "\b(cert_all|cert_FF|cert_FT|belowOf|childrenB|goodB|goodB_succ_of|rootInfo|rootAt|kidsOk)\b(?!')" RBM3D/Graph/LWExpSound.lean
1453:`5` choices that `belowOf` skipped and `belowOf'` evaluates (`lwCertB_lost_R2`); the leaf term `2` (classes `a ~ c    <- a doc comment; no code hit
$ grep -nP "\bkids?\b" RBM3D/Graph/LWExpSound.lean | grep -v '\.kids'   # every other hit is `.kids` of `RCand.kids` (T2307): 7 hits in all
1468:/-- Instance of `soundStep` at the first kid of the first candidate (`childrenB'` flag by the kernel). -/
$ grep -n '^import' RBM3D/Graph/LWExpSound.lean
6:import RBM3D.Graph.LWExpSim
7:import RBM3D.Graph.LWExpCertBS0
8:import RBM3D.Graph.LWExpCertBS1
$ git diff --stat main...t/T2318
 RBM3D/Graph/LWExpSim.lean   |   58 +-
 RBM3D/Graph/LWExpSound.lean | 1490 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    5 +-
 3 files changed, 1522 insertions(+), 31 deletions(-)
```
### Axioms of every new public declaration (scratch file importing `RBM3D.Graph.LWExpSound`, `#print axioms`; the two private kernel facts are printed in the build output above)
```
[propext, Classical.choice, Quot.sound]: 16 declarations
  Rel.ext_surj relInvariance relKids belowOfSound soundStep soundRoot goodB'_mono lwG5LeafProps_holds lwG5ExpandSplit_iff lwG5LeafProps_iff lwG5ExpandOfHalves lwG5Expand'_holds lwExpSound_inst_relKids lwExpSound_inst_belowOfSound_R2 lwExpSound_inst_leafOK_R2 lwExpSound_inst_leafProps
```
### Target statements (extracted by script: line, signature) and the two new pinned statements
```
118: theorem Rel.ext_surj {N : MNode} {P : PGraph (Fin 2)} (h : Rel N P) : Function.Surjective N.ext
226: theorem relInvariance : RelInvariance
554: theorem relKids : RelKids
1161: theorem belowOfSound : BelowOfSound
1254: theorem soundStep : SoundStep
1349: theorem soundRoot : SoundRoot
1200: theorem goodB'_mono (n : ℕ) (N : MNode) : goodB' n N = true → goodB' (n + 1) N = true
1393: theorem lwG5LeafProps_holds : LWG5LeafProps (expandRoot selClassical 4)
1402: theorem lwG5ExpandSplit_iff (d : ℕ) : LWG5ExpandSplit d ↔ LWG5Expand' d
1403: theorem lwG5LeafProps_iff (Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2))) : LWG5LeafProps Ls ↔ ∀ k s, ∀ q ∈ Ls k s, LeafOK q.2
1405: theorem lwG5ExpandOfHalves : LWG5ExpandOfHalves
1408: theorem lwG5Expand'_holds : ∀ d, LWG5Expand' d
-- public `def`s (the pinned Props; statements = check file, `Iff.rfl` check below): LWG5LeafProps:43, LWG5ExpandSplit:50, LWG5Expand':55, LWG5ExpandOfHalves:68, RelInvariance:72, LeafOK:81, SoundStep:88, SoundRoot:95, RelKids:102, BelowOfSound:110
-- RelKids, BelowOfSound (lines 102-107, 110-115 of the file):
def RelKids : Prop :=
  ∀ (N : MNode) (P : PGraph (Fin 2)), Rel N P → ∀ c' : RCand P,
    ∃ c : Cand N.a N.b, c ∈ cands N.g ∧
      List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
        (childrenX N c) c'.kids

def BelowOfSound : Prop :=
  ∀ (a b : ℕ) (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)), Function.Surjective ext →
    (belowOf' Δ ext).1 = true → ∀ r ∈ cPartitionX Δ ext,
      (leaf r.2 = true → ∀ Q : PGraph (Fin 2), Rel r.2 Q → LeafOK Q) ∧
      (leaf r.2 = false → ∃ M ∈ (belowOf' Δ ext).2, ∀ Q : PGraph (Fin 2), Rel r.2 Q → Rel M Q)

```
### Pins against the revised check file (scratch `lean/pincheck.lean`: sections 2-3 of `docs/tickets/checks/T2318-check.lean` and T2265's `LWG5Expand'Pin` copied into `T2318Check`/`T2265Check`; 11 `Iff.rfl` theorems `chk_*`, 11 `example`s applying the targets at the pinned statements)
```
$ lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false lean/pincheck.lean   -> exit 0, output empty (0 bytes)
$ (same file with the pin `q.2.g.nM ≤ 1` changed to `≤ 2` in the check copy)               -> 7 `error` lines (negative control)
```
### Compiled instances (all in the file, section 10, `decide +kernel` for every kernel fact; line, first line of the statement)
```
1423: example : lwExpSound_N.a = 0 ∧ lwExpSound_N.b = 3 ∧ lwExpSound_N.g.scalingOrder = 2 ∧ tgt lwExpSound_N = 4 ∧ (cands lwExpSound_N.g).length = 3 ∧ (chil
1429: example : LWG5Expand' 3 := lwG5Expand'_holds 3
1430: example := And.intro (lwG5ExpandSplit_iff 3) (And.intro (lwG5LeafProps_iff (expandRoot selClassical 4)) lwG5ExpandOfHalves)
1433: example := relInvariance lwExpSound_N lwExpSound_N_surj _ (rel_self lwExpSound_N lwExpSound_N_surj)
1436: theorem lwExpSound_inst_relKids : ∃ c ∈ cands lwExpSound_N.g, List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ 
1446: example : ∀ Q, Rel ((cPartitionX (a := 1) (b := 3) (LWG5Graph false false) ![0, 1])[0]'(by decide +kernel)).2 Q → LeafOK Q :=
1448: example : ∃ M ∈ (rootInfo' false false).2, ∀ Q, Rel ((cPartitionX (a := 1) (b := 3) (LWG5Graph false false) ![0, 1])[95]'
1455: theorem lwExpSound_inst_belowOfSound_R2 : ∀ Q, Rel ((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[2]'(by decide +kernel)).2 Q → LeafOK Q :=
1460: theorem lwExpSound_inst_leafOK_R2 : LeafOK (((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[2]'(by decide +kernel)).2.toP (by decide +kernel)) :=
1463: example : ∃ M ∈ (belowOf' lwExpSound_f.2 lwExpSound_N.ext).2, ∀ Q, Rel ((cPartitionX lwExpSound_f.2 lwExpSound_N.ext)[8]' (by decide +kernel)).2 Q → R
1469: example := soundStep lwExpSound_N lwExpSound_N_surj lwExpSound_c (List.getElem_mem _) (by decide +kernel)
1475: example (k : Bool) := soundRoot k false cert_FF'.1 ((partitionX (LWG5Graph k false))[0]'
1479: theorem lwExpSound_inst_leafProps : ∃ q ∈ expandRoot selClassical 4 false false, LeafOK q.2 := by
```
Evidence for the new mandatory instance (Amend 1; scratch `lean/t3.lean`, `#eval` on the family graph `R2` of candidate 0 of `rootAt' false false 9`; 16 lines = `f.2.dotted`, `solid`, `waved` (vertex indices), `bEdges`, `aPairs`, `dotChoices`, terms per choice, `(oldSkip, newSkip)` per choice, then term `[2]`: solid, waved, dotted, exponents, and `lostOf f.2`; vertices `0` = `x+y`, `1,2,3` = `a,c,b`; exit 0, `date -u` Thu Oct  8 11:38:36 UTC 2026):
```
[(false, 0, 1), (false, 1, 2), (false, 2, 3), (false, 3, 0)]
[(true, false, 2, 3), (true, false, 3, 0), (true, false, 0, 2)]
[(2, 1), (1, 3), (1, 2)]
[(false, 0, 1), (false, 1, 2)]
[(0, 2)]
[(1, [(true, 0, 2)]), (-1, [(true, 0, 2), (true, 1, 2)]), (-1, [(true, 0, 2), (true, 0, 1)]),
  (1, [(true, 0, 2), (true, 0, 1), (true, 1, 2)]), (1, [(false, 0, 2)]), (-1, [(false, 0, 2), (true, 1, 2)]),
  (-1, [(false, 0, 2), (true, 0, 1)]), (1, [(false, 0, 2), (true, 0, 1), (true, 1, 2)])]
[2, 2, 2, 2, 1, 1, 1, 0]
[(false, false), (true, false), (true, false), (true, false), (false, false), (true, false), (true, false),
  (true, true)]
[(true, false, 0, 1), (true, false, 1, 0), (true, true, 0, 0)]
[(0, 0), (0, 1), (0, 0)]
[(false, 0, 1), (false, 1, 0)]
(0, 0)
5
```
Choice 1 of the list is `=(0,2), =(1,2)` (the b-edge `×(1,2)` merged), contributes the terms 2, 3; skipped by the old test (`true`), evaluated by the new (`false`); 5 of 8 choices are of this kind = `lostOf` = `lwCertB_lost_R2`.
### Registry (`RBM3D/Test/Axioms.lean`) and the `LWExpSim.lean` diff
```
$ lake env lean lean/precheck.lean   (file: `import RBM3D`, `import RBM3D.Graph.LWExpSound`, `#assert_rbm_axioms`)
main's registry (`git show 9cd356f:RBM3D/Test/Axioms.lean` copied into the worktree, `lake build RBM3D.Test.Axioms`; `date -u` Thu Oct  8 11:39:00 UTC 2026), exit 1:
/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2318/lean/precheck.lean:3:0: error: axiom audit: 1 premise(s) that no theorem of this developmen
  [RBM.Graph.LGraph.IsExtCls]
Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, refuted (shown false and superseded), or superseded (not needed).
with the committed registry (Thu Oct  8 11:43:39 UTC 2026 and later), exit 0, first line:
axiom audit: 9940 theorems, 2990 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ git diff -U0 HEAD~1 HEAD -- RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.LWG5Expand, -- `(eq:sizeGammamu_E)`, `B:91-108`: the fixed list of packed graphs with `𝔼 𝒢_xy = Σ m^j 𝔼 Γ_μ` (`n_M ≤ 1`, `n_W ≥ 2`, attached, `ord ≥ 4·1_{
+   `RBM.Graph.LGraph.IsExtCls, -- a class of `=`-dotted vertices contains an external vertex (`dot-def`, `7_8:222`; T2050): a defining predicate of the merged graph, hypothes
-   `RBM.Gauss.Sizes.STIterationsII]  -- superseded by `STIterationsII'` (R2*, DECISIONS §80 (1)); definition kept (CLAUDE.md §5.3)
+   `RBM.Gauss.Sizes.STIterationsII,  -- superseded by `STIterationsII'` (R2*, DECISIONS §80 (1)); definition kept (CLAUDE.md §5.3)
+   `RBM.Gauss.Sizes.LWG5Expand]  -- superseded by `LWG5Expand'` (proved, T2318): the `m^j` coefficient model misses `m̄` (red weights) and outputs with both external vertices
```
```
git diff -U0 HEAD~1 HEAD -- RBM3D/Graph/LWExpSim.lean: 29 lines removed, 29 added; every removed line = the added line with the token `private ` in front: True
lwExpSim_vi_lt lwExpSim_vi_inj lwExpSim_vi_inr lwExpSim_R lwExpSim_LabsGood lwExpSim_good_unite lwExpSim_labsOf_good lwExpSim_labs lwExpSim_labs_good
lwExpSim_test_iff lwExpSim_cMerge_none lwExpSim_cMerge_some lwExpSim_equivs lwExpSim_cls_relabel lwExpSim_consistent_relabel lwExpSim_splitLoopsX_map
lwExpSim_vmap_inl lwExpSim_real lwExpSim_model lwExpSim_R0 lwExpSim_sBetween_relabel lwExpSim_xBetween_relabel lwExpSim_dotBase_relabel
lwExpSim_dotChoices_relabel lwExpSim_terms_relabel lwExpSim_forall₂_flatMap lwExpSim_partition_sim lwExpSim_relabel_refl lwExpSim_forall₂_flatMap_same
```
Name clash: 26 new public names (10 pinned `def`s, `Rel.ext_surj`, `relInvariance`..`soundRoot` (5), `goodB'_mono`, 5 `lwG5*` theorems, 4 `lwExpSound_inst_*`): `grep -rnE '(theorem|def|abbrev|structure|lemma)[[:space:]]+<name>' RBM3D --include='*.lean'` outside `LWExpSound.lean` and `RBM3D/Probe/`: 0 hits in total; `lwExpSound_` occurs only in `LWExpSound.lean`.
Ports from RBM1D/RBM2D: none (no file of either project was read or copied).

### Narrative (every statement is backed by the output above or by the file)
1. All eight targets are proved in `RBM3D/Graph/LWExpSound.lean` (1490 lines; the preset cut was not needed): `relInvariance` (L6, :226), `relKids` (L5', :554), `belowOfSound` (L7,
   :1161), `soundStep` (:1254), `soundRoot` (:1349), `lwG5LeafProps_holds` (:1393), `lwG5ExpandSplit_iff`, `lwG5LeafProps_iff`, `lwG5ExpandOfHalves` (:1402-1405) and `lwG5Expand'_holds`
   (:1408), plus the optional helpers `Rel.ext_surj` (:118) and `goodB'_mono` (:1200). The pins are the texts of the revised check file (`Iff.rfl` check above); the certificate side
   uses T2319's primed names only (grep above).
2. L6: from `Rel` the map `Equiv.sumCongr eE eI` preserves `adj` (`lwExpSound_adj_map`, with a copy of the private `adj_iff`), hence `mol`, `n_M`, `Normal`, `LWAttached`, the molecule
   statement and `LWJoined` are transported (`lwExpSound_mol_map`, `lwExpSound_nM_map`, `lwExpSound_normal_map`).
3. L5': from `Rel N P` and `c' : RCand P` the model candidate is rebuilt (`lwExpSound_cand_of_rel`, converse of `Rel.cand`); the seven families at `P` are the model families renamed by
   `rho` up to the waved colours (`lwExpSound_Rl`, `lwExpSound_Rl_owxExt`, `lwExpSound_fam2`, `lwExpSound_fam78`); their partitions are compared with `cPartitionX` of the renumbered
   model by a generalisation of `lwExpSim_term_some` / `lwExpSim_partition_sim` to an arbitrary external type (`lwExpSound_term_some`, `lwExpSound_partition_sim`, reusing
   `lwExpSim_equivs`).
4. L7 (Amend 1): `belowOf'` equals a `foldr` of a step function by `rfl` (`lwExpSound_below_eq`, `lwExpSound_tpl`); its skip test is `not (Δ.withDots c).Consistent`
   (`lwExpSound_skipC_iff`) and its labels are `lwExpSim_labs (Δ.withDots c)` (`lwExpSound_labsC_eq`), so no b-edge-free hypothesis occurs. At one term: the molecules of the merge are
   the images of those of the term (`lwExpSound_molOf`), the labels `mol` are the least vertices of the molecules (`lwExpSound_mol_good`, via `lwExpSim_good_unite`), `n_M` is at most
   the number of internal representatives (`lwExpSound_nM_le`), the attachment counts (`lwExpSound_attached`), distinct external molecules or joined (`lwExpSound_molDisj`), the order
   bookkeeping (`lwExpSound_ord`, `lwExpSound_split_len`, `lwExpSound_split_filter`); `Normal` comes from the real partition (`lwExpSound_normal`: `partitionSim`,
   `LGraph.partition_normal`, `relInvariance`).
5. L8: `lwExpSound_expand` is the induction along `expand selClassical n` (`relKids` and `lwExpSound_childSound`, which is `belowOfSound` per family); fuel 4 against height 3 uses
   `goodB'_mono`; `soundRoot` covers every `k` through the colour-erased key `lwExpSound_Key` and the two kernel facts `lwExpSound_key_FF`, `lwExpSound_key_FT` (`decide +kernel`,
   `#print axioms` in the build output).
6. No hypothesis was added to any pinned statement; `BelowOfSound` keeps `Function.Surjective ext` and the flag exactly as pinned. The instance at `R2`
   (`lwExpSound_inst_belowOfSound_R2`, `lwExpSound_inst_leafOK_R2`) is a term of a choice that the old flag skipped (evidence block above).
7. `LWExpSim.lean`: 29 declarations lost the token `private` (list above, checked by script), nothing else changed. The certificate modules were replayed, not rebuilt (build output).
8. Registry: `LWG5Expand` moved to `supersededProps` with the ticket's comment. The pre-check on main's registry lists one more premise, `RBM.Graph.LGraph.IsExtCls` (the hypothesis `h3`
   of `lwExpSim_equivs`, which is public after the `private` deletion); one line in `structuralProps` next to `IsExtMol` clears it (output above). See (d) 1.
9. The branch was rebased onto main `7b9fefe` (T2328 merged after this worktree was cloned and changed one comment line of `Axioms.lean`); `git diff --stat main...t/T2318` lists the
   three writable files only.
10. Machine: the final `lake build` took 16.9 s wall. An earlier revision of the file compiled under `/usr/bin/time -l` in 17.67 s real, maximum resident set size 4025122816 B; `ps`
   shortly before showed another ticket's `lean RBM3D/Induction/IniTermIc.lean` (3.3 GB) and no second build of this ticket.

## (c) Names (`#check @name` for each: 0 errors; scratch `lean/chknames.lean`, `lean/chknames2.lean`)
Namespaced names occurring in the file (104): Bool.and_eq_true Bool.and_eq_true_iff.1 Bool.and_self Bool.eq_iff_iff Bool.false_eq_true Bool.false_or Bool.not_eq_true Bool.not_eq_true'
Bool.not_false Bool.or_eq_true Bool.true_and Classical.choice Equiv.coe_toEmbedding Equiv.forall_congr Equiv.refl Equiv.sumCongr Equiv.symm_apply_apply Finset.card_image_of_injective
Finset.card_le_card_of_surjOn Finset.map Finset.map_inj Finset.map_injective Finset.mem_coe Finset.mem_coe.2 Finset.mem_filter Finset.mem_image Finset.mem_map.1 Finset.mem_map_equiv
Finset.mem_map_of_mem Finset.mem_univ Finset.univ.filter Function.comp_apply List.Forall₂ List.all_eq_true List.all_eq_true.1 List.any_append List.any_eq_true List.any_map
List.append_assoc List.append_nil List.exists_mem_of_ne_nil List.filter_append List.filter_congr List.filter_cons List.filter_filter List.filter_map List.flatMap_append
List.flatMap_assoc List.flatMap_cons List.flatMap_map List.flatMap_nil List.foldl_cons List.foldr_cons List.forall₂_map_left_iff List.forall₂_map_right_iff List.forall₂_same
List.getElem_mem List.isEmpty_eq_false_iff.1 List.length List.length_cons List.length_map List.map List.map_append List.map_congr_left List.map_cons List.map_injective_iff.2
List.map_map List.mem_append_left List.mem_append_right List.mem_cons List.mem_cons.1 List.mem_cons_of_mem List.mem_cons_self List.mem_filter List.mem_filterMap List.mem_flatMap
List.mem_flatMap.1 List.mem_flatMap.2 List.mem_map List.mem_map.1 List.mem_map.2 List.mem_nil_iff List.mem_range List.mem_singleton List.mem_toFinset.2 List.range List.rel_append
List.toFinset_card_le Nat.le_zero.1 Prod.ext Prod.mk.injEq Quotient.eq Quotient.exact Quotient.sound Relation.EqvGen Relation.EqvGen.mono Relation.EqvGen.refl Relation.EqvGen.rel
Relation.EqvGen.symm Relation.EqvGen.trans SimpleGraph.Adj.reachable SimpleGraph.ConnectedComponent.eq SimpleGraph.Reachable.refl SimpleGraph.fromRel_adj
Dot-notation lemmas checked separately: `Equiv.eq_symm_apply`, `Equiv.symm_apply_eq`, `Equiv.ofBijective`, `SimpleGraph.Iso.reachable_iff`, `List.Forall₂.length_eq`, `List.Forall₂.imp`,
   `Function.Surjective.comp`, `Function.Injective.eq_iff`, `decide_eq_decide`, `decide_not`. Verified absent: a `List.Forall₂` membership lemma `∀ x ∈ l₁, ∃ y ∈ l₂, R x y` (`grep -cE
   '∃ [a-z]+ ∈' Mathlib/Data/List/Forall2.lean` = 0), proved here as `lwExpSound_forall₂_mem_left/right`.

## (d) Open issues and paper-delta candidates
1. **Registry line needing the dispatcher**: `RBM.Graph.LGraph.IsExtCls` is in `structuralProps` (diff above). The ticket expected nothing (or `LeafOK`/`LWG5ExpandSplit`) and says to
   report and ask for anything else; it is a data predicate of the merged graph (like `IsExtMol`, `Consistent`), not an owed line. Without it the full-library `#assert_rbm_axioms` of
   the hub's merge fails (pre-check exit 1 above). The alternative, a private copy of `lwExpSim_equivs` (about 70 lines) in `LWExpSound.lean`, would exceed the 1500-line cap.
2. Shared files: `Axioms.lean` and `LWExpSim.lean` are edited by several tickets and main moved during this ticket; the branch is rebased, so bringing in the three files as they are on
   the branch is correct at `7b9fefe`; the hub's step (A.4) adds `import RBM3D.Graph.LWExpSound` to `RBM3D.lean`.
3. T2306's `cert_all`, `LWExpCertS0/S1` and the unprimed certificate names are not used (grep above); deleting them is LW-14f's question (Amend 1).
4. The `soundRoot` instance is one `example (k : Bool)` (covers `k = false` and `k = true`; the kernel facts are specialised by `cases k`).
5. Paper-delta candidates: none (`T2318a`...: none). The leaf bookkeeping found no leaf property that `(eq:sizeGammamu_E)` does not state; the model-flag repair is T2319's.
