Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 02:11:05 UTC 2026

Python only (no Lean anywhere). Scripts are copies of the T2265/T2288 engine (`eng.py`, `tree.py`, `root.py`, `canon.py`, `rall.py`, from `scratchpad/85663390-…/T2288/audit1/py/`, a mirror of `LGraph.partition`, `oe2x*`, `candidates`) plus new `pre2318.py`, `lost.py`, `lost2.py`, `cex.py` in `scratchpad/ec1cbe39-…/T2318/`. Run as `PYTHONPATH=. python3 <script>` there. Lean facts below are read from the files (file:line) and are not evaluated.

### (i) Exponent table
| row | value | constraint | slack |
|---|---|---|---|
| order of a variant | `ord = nS − t + 2(nW − B)`, `t` = number of dropped uncircled loops, `0 ≤ t ≤ L`; `ord(Γ) = nS + 2(nW − nV)` (`ScalingOrder.lean:65`), `lwSplitLoopsX` `LWExpTerm5.lean:91` | `belowOf` `LWExpCert.lean:157-190`: leaf properties evaluated iff `nS + 2(nW−B) ≥ tg` (some variant a leaf ⇒ `t=0` variant is); list built iff `nS − L + 2(nW−B) < tg` | `t` ranges over `L+1` values; the two tests cover all variants |
| target | `tg = 4` if the images of `x`,`y` coincide, else `5` (`tgt` `:147`) | leaf iff `tg ≤ ord` | min `ord − tg = 0` over all leaves (T2288 report) |
| leaf thresholds | `nM ≤ 1`, `nW ≥ 2`, `≥ 2` solid non-inside edges at each internal molecule, distinct external molecules or `LWJoined` (`LeafOK`, check file §2) | independent of `t` (loops lie inside a molecule) | python: 0 failures on all real leaves incl. the unseen ones below |
| family shifts `(j,j')` | R2,R4,R6,R8: `(3,0)`; R3,R5,R7: `(1,0)` (`famsX`, `LWExpSim.lean`) + loop split `(j,j')` | `Δord = +1` per family (T2288) | exactly `+1` |
| fuel vs height | AND-tree height `3` (`goodB 3`, `cert_all`), fuel `4` (`expandRoot selClassical 4`) | `goodB n → goodB (n+1)` | slack `1` |
| root | `(a,b)=(1,3)`, 163 partition terms, 11 below `tg`, for every `(k,s)` | `k` only enters as `col` of one waved edge (`LWExpTerm3.lean:58`) | `Rel` compares waved endpoints only (`LWExpSim.lean:120`) |
| `belowOf` consistency test | `X0` = ALL `×`-dotted edges of `Δ` (`LWExpCert.lean:162,171`); the real partition uses `dotBase` which DROPS `isB` edges (`×` without solid edge, `LWVocab.lean:1066,1073,1094`) | must equal `¬ Consistent (Δ.withDots c)` (ticket L7: "`cMerge = none`") | **violated** whenever `Δ` has a b-edge (below) |

### (ii) Concrete instance (python mirror)
Command and output (`pre2318.py`, filtered of the import-time prints of `lost.py`):
```
s=False: partition sizes F/T 163/163 ; colour-erased key lists equal: True ; below-target roots F/T 11/11
s=True: partition sizes F/T 163/163 ; colour-erased key lists equal: True ; below-target roots F/T 11/11
root term 9: ext ['x+y'] ints ['a', 'b', 'c'] (nS,nW,nV,nM)= (4, 2, 3, 1) ord 2 tg 4 #cands 3
candidate 0: x=a p=solid[1] (->c) q=solid[0] (x+y->)
children (all partition terms of 7 families): 533
below-target children 12 [('R2', 3, 0, 0, 3, 3, 4), ('R3', 1, 0, 0, 4, 3, 4), ('R4', 3, 0, 0, 5, 3, 4), ('R5', 1, 0, 0, 4, 3, 4), ('R6', 3, 0, 0, 5, 3, 4), ('R7', 3, 0, 0, 3, 3, 4), ('R7', 1, 0, 0, 4, 3, 4), ('R8', 5, 0, 0, 4, 3, 4), ('R8', 3, 0, 0, 5, 3, 4), ('R7', 1, 0, 0, 4, 3, 4), ('R8', 5, 0, 0, 4, 3, 4), ('R8', 3, 0, 0, 5, 3, 4)]
one real child: family R2 (fam,(j,j'),a,b,ord,tg) = ('R2', (3, 0), 0, 3, 3, 4)
   edges: Gc>b Gb>x+y Gx+y>c | S(c,a) S*(a,b) S+(a,c) | x(c,b) x(b,x+y) x(x+y,c)
   Rel witnesses eE: {'x+y': 0}  eI: {'a': 0, 'b': 1, 'c': 2}  leaf: False
```
Tuples are `(family, j, j', a, b, ord, tg)` with `(j,j')` relative to the parent. 533 children and 12 below target agree with T2288 audit §4 (`[533,533,533]`, `[12,12,12]`; Lean `#eval` there). The `Rel` witnesses are the rank-by-first-vertex bijections `eE : Fin 1 ≃ {x+y}`, `eI : Fin 3 ≃ {a,b,c}` (the model partner is the same graph with its class vertices renumbered; `Rel` ignores the colours `S+`/`S*` and the coefficient). For `k = true` the colour-erased lists equal those for `k = false` for both `s` (first two lines; Lean side: T2288 audit §4 `#eval (rootInfo true false).1 && (rootInfo true true).1 → true` and "identical list for k = true"). The kernel equality and the key lemma of ticket L8 (d) are thus consistent with the mirror.

**Hypotheses of `belowOfSound` (target 3) at the same node.** Command `python3 pre2318.py` (last block), columns (family, #b-edges of `Δ`, #choices of `Δ.dotChoices` consistent in the real partition, # consistent in `belowOf`'s test):
```
   R2 2 7 2
   R3 0 1 1
   R4 2 14 4
   R5 2 14 4
   R6 2 14 4
   R7 2 14 4
   R8 3 42 6
   R7 2 12 3
   R8 3 42 6
```
Over the whole unmemoised R-all tree for `(k,s)=(F,F)` (`python3 lost2.py`):
```
choices real-consistent 70253
choices real-consistent but model-inconsistent 52799
family graphs with a lost choice 3061
family graphs 3394
lost terms 212194
lost non-leaf (ord < tg) 0
lost leaf, some property fails 0
```
and for `(F,T)` (`lost2T.py`): `lost terms 231842`, `lost non-leaf 0`, `lost leaf, some property fails 0`. The root `Δ = LWG5Graph k s` has no dotted edge, so `belowOf` is exact there. Tree check (`python3 rall.py`): `R-all k=False s=False: … distinct … nodes 125, stuck 0, cycles 0, max height of AND-tree 3`; `s=True: … 129 … stuck 0, cycles 0, max height 3`.

**Counterexample to `BelowOfSound` (python mirror `cex.py`, Lean semantics by reading `belowOf` and `withDots`).** `a = 1, b = 0`, `ext = ![0,1]` (onto), `Δ.solid = Δ.waved = []`, `Δ.dotted = [×(0,1)]` (one b-edge: `isB` holds, no solid edge).
```
b-edges 1 choices (idx, real_inconsistent, belowOf_inconsistent): [(0, False, False), (1, False, True)]
real term: ext ['e0', 'e1'] ints [] ord 0 tg 5 ext map {'e0': 'e0', 'e1': 'e1'}
real term: ext ['e0+e1'] ints [] ord 0 tg 4 ext map {'e0': 'e0+e1', 'e1': 'e0+e1'}
```
By `LWExpCert.lean:171`, choice `c = (−1,[=(0,1)])` has `labs 0 = labs 1` and `X0 ∋ (0,1)`, so it is skipped; choice `(1,[])` gives `ord 0 < 5`, no leaf, so `ok0 = true` and `(belowOf Δ ext).1 = true`, `(belowOf Δ ext).2 = [M₁]` with `M₁.a = 1`. The real term of the skipped choice is `r ∈ cPartitionX Δ ext` with `r.a = 0`, `leaf r.2 = false` (`ord 0 < tg 4`). `BelowOfSound` demands `M ∈ [M₁]` with `∀ Q, Rel r.2 Q → Rel M₁ Q`; `Q = r.2.toP _` (`rel_self`, ext onto) has `E' = Fin 1`, but `Rel M₁ Q` needs `Fin 2 ≃ Fin 1`. So the pinned `BelowOfSound` is **false**.

### Consequences and verdicts
- Cause: `belowOf` tests `X0 ++ X1` with every `×`-edge of `Δ`; the family graphs of `(Oe2x)` keep `Δ.dotted` (`owxExt` `LWWeightExp.lean:462`) while deleting the solid edges `p`,`q`, so `×`-edges lose their solid support (python: 3061 of 3394 family graphs). The real choice "b-edge ↦ `=`" (merge) and choices where another `=` merges the ends are skipped by the kernel certificate: its flag and list say nothing about them (212194 / 231842 terms; mathematically all are leaves with all properties, by the mirror).
- Hence `cert_all` does not prove the leaf properties of those terms, and `SoundStep` (same defect at every `N` with such a family) cannot be derived from `(childrenB N c).1 = true`. A repair needs a corrected flag (`X0` restricted to edges with `SBetween`) and a new certificate (T2306's modules, not writable here; 17.6 min, 7.5 GB per T2288 audit §2), or a separate kernel check of the skipped terms: a dispatcher decision (new ticket), not a stage-1b matter.
- Targets 1 (`relInvariance`), 2 (`relKids`, `Rel.ext_surj`, `goodB_mono`): hypotheses consistent (instance above, `rel_self` at term 9, `c'` = candidate 0); the statements are true by the argument of the ticket (L5′, L6; the completeness of `cands` and naturality under a bijection of vertices, waved colours not read).

| target | verdict | reason |
|---|---|---|
| 1 `relInvariance` | PASS | no exponent involved; instance above; colour-blind (O2 check of the ticket confirmed by the readers listed in the ticket) |
| 2 `relKids` (+ helpers) | PASS | converse of `Rel.cand` holds; families only map waved edges; same order since `Rel` is a bijection on vertices |
| 3 `belowOfSound` | **FAIL** | pinned statement false (counterexample above); needs the b-edge-free hypothesis, which fails on 3061 of 3394 family graphs of the tree |
| 4 `soundStep` | **FAIL** | its proof goes through target 3 at the `fams` members, which carry b-edges; not derivable from `(childrenB N c).1 = true` |
| 5 `soundRoot` | PASS | root `Δ` has no dotted edge, `belowOf` is exact there (so target 3 holds at the root); `k = true` keys equal (first lines of (ii)) |
| 6 `lwG5LeafProps_holds` | **FAIL** | needs 3 and 4 at every inner node (fuel `3 ≤ 4` is fine, but the leaves reached through b-edge merges are not certified) |
| 7 `lwG5ExpandSplit_iff`, `lwG5LeafProps_iff`, `lwG5ExpandOfHalves` | PASS | `Iff.rfl`/definitional |
| 8 `lwG5Expand'_holds` | **FAIL** | needs 6 |

Overall verdict: **FAIL** (a pinned statement is false and the certificate does not cover the real partition). Hint for the dispatcher: the mirror shows that a certificate with `X0` restricted to edges with a solid edge between their ends would flag no failure (0 lost non-leaf, 0 lost leaf with a failing property, both `s`); the repaired `belowOf'` flag is the exact `¬ Consistent` test.
