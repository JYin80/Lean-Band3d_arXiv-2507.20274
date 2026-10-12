Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 15:00:47 UTC 2026
Setting: C1, combinatorial; no analytic exponent, no external hypothesis (no limit computation). Python only, no Lean; `$SP` = scratchpad `T2456/`. Model `ba56.py`: vertex-level BA graph (solid, waved, M-dots; externals 0, 1), builders of BAExpandW:122-148, BAWeightOp:68-73, BAGGOp:73-90, BASim:115-136, constructors BASim:138-161 with their hypotheses, `tagStd`/`tagT1`, `splitG`, twist LWSymm:167; `PathInv2` of the atomic image solved exactly (molecules = waved components of the atoms; p coloured trails x→y using each off-diagonal coloured edge once; Hall; colour-visit; LR2:147, 1577); `BAReach` is not cut at K (superset). Fidelity: the model reproduces the kernel counts of BASim3:1909-1913 (`wit` below).
### (i) Exponent table (no exponent: the constants, thresholds and counts the targets use; the ticket asks "no constants" and the R1 witness rows)
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | p, k = number of walks | instance p = 2; numerics p = 1, 2, 3; start terms p = 1..4 | `PathInv2 k` with k = p; paper p even (p = 1, 3 tested too) | — |
| 2 | `P0.g.nM`, 2^(2p) start terms | p = 2: {0: 9, 1: 6, 2: 1}; max = p for p = 1..4 (`t68` below) | ≤ p (T2456_StartNM, §260 (1)) | 0 at the all-circled term, p − n_M elsewhere |
| 3 | `Q.g.nM` along `BAReach` | instance Q: 1; 0 violations at all outputs | ≤ p | 1 at the instance |
| 4 | n_V ≤ n_W + 1 per image molecule | instance: 1 ≤ 1, 1 ≤ 1, 3 ≤ 5 | every molecule (LocReg2) | 0, 0, 2 |
| 5 | Hall, (4) at the internal molecule | 2 distinct walks through it | ≥ \|A\| = 1; (4) needs ≥ 2 | 1; 0 |
| 6 | K | 5 | ord(source) < K, source not LocStd: ord P0 = 2, ord Q1 = 4 | K − ord = 3, 1 |
| 7 | k at the R1 witnesses (target 10 i-iv) | P_A 2 (gg), P_B 1 (within), P_C 2 (ggSplit), P_E none (edge) | `P.img.PathInv2 k` must hold to discharge target 3 | P_E fails k = 0..4 (blue degrees at x, y are 2, 1: parity); replacement below, k = 1 |
| 8 | target 9 data | p = 2 (Even), d = 3, L = 4, W = 2, g0 = Em = t = 1, m = 1 | Even p, NeZero L, NeZero W | no further hypothesis |
| 9 | central vs Σ threshold 1,575; stop line 2,000/file | (c) below | central ≤ 1,575 else Σ | 1,550 without 3(c)-(e) (slack 25); 2,424 with |
Table (a) by output group (O2R-C4; route (S) for `band`, (U)-style term lemmas for the BA-only shapes; one shared pair of new lemmas: a BA term lemma and an M-split quotient lemma = `map` along the atom merge + `of_add_diag` LR2:257/616):
- `band` (all five constructors): target 2 `baMatch_holds` (BASim3:218) at `P.twist c t`, `pathInv2_locStep` (LR2:1582), target 1 (`BAEquivC` via LR2:616, twist via LR2:289, 976); new: `baSimP'_holds`, `baEquivPath_holds`, `baPathTwist_holds`.
- `s1`: vacuous (no constructor tags `s1`), as BAStepS:353. `e1` (`tagT1` outputs of `lanlwT1`): owxT1/oe1xOwx-type leaf with a blue loop (LR2:1027, 1143), then the M-split quotient lemma; new: 1 term glue.
- `e2` (14 builder terms): lanlwD ↔ oe1xD :1165; lw2 head ↔ owxT1 :1027; lw4 head/tail ↔ owxT2/T4 :1052/:1088; within head ↔ oe1xOwx :1143; gg2 A2/A3 ↔ oe2xR2 :1330, A4 ↔ R3 :1352, A5 ↔ R5 :1410, AD ↔ R7 :1481; gg4 B1/B2/BD ↔ R4/R6/R8 :1374/:1444/:1510; ggSplit d1 ↔ R5 at x := a. Note (script): A2 merges x ~ y', A3 merges x ~ y, while R2 merges x ~ y, so the band lemma serves A2 only with p, q exchanged (the swapped selector of BASim:196-198, T2423):
A2: molecules of x=2, y=0, y'=1 in the unsplit term: x~y False, x~y' True
A3: molecules of x=2, y=0, y'=1 in the unsplit term: x~y True, x~y' False
- `macroA` (within stage 2): P.img → tr (the edge inside an atom becomes the blue loop at β; `map` + `add_diag`), then lw2/lw4 at tr = the lw2/lw4 rows above; `macroB` (ggSplit): d2, d3 ↔ R2 :1330, d4 = two R2 merges (needs no band term lemma: a `map` along the merge + `of_add_diag`), stage 2 = gg2/gg4 rows at tr (leaf β, molecular edges unchanged). Every group has a route; no new row.
(c) Fit (ticket 1a item (c); command `python3 fit56.py`). 1a estimates in lines (A header+pins+docs 150, B target 1 150, C target 2 40, D s1 10, E shared BA term lemma + M-split quotient lemma 200, F e1 60, G target 4 40, H target 5 100, I target 6 120, J target 7 200, K target 8 200, L target 9 80, M instances 200); 3(c)-(e) specific = 0.7 × the measured cost-twin proof lines:
```
wc -l: BAStepS 523  BAShapeO2 1094  BAShapeO2B 447  LocalRegular2 2068
band path term lemmas (LR2 s.3): 17 lemmas, 488 proof lines; cost twin proofs for e2/macroA/macroB (BAShapeO2 all decls + BAShapeO2B without baLocReg6_holds): 1248 lines
cost twin of targets 1,2,3a,3b,4 (BAStepS decls): tools 41 , simC'+step+s1+e1+reach 43 lines (file 523 incl. pins, docs, instances)
central L3b1 without 3c-3e (A..M): 1550 ; 3c-3e specific = 0.7 x 1248 = 874 ; with 3c-3e: 2424
rule (ticket l.6): central > 1,575 => Sigma.  with 3c-3e: 2424 > 1575 = True ;  under Sigma: 1550 <= 1,575, slack 25 ; per-file stop line 2,000 x 2 = 4,000
```
### (ii) One concrete nondegenerate instance, and the PathInv2 check (b)
Targets 2-8 at p = 2 (command `python3 inst56.py`): P0 the all-circled start term, two `BALocStep`s, Q locally standard with an internal molecule visited by a blue and a red walk. Target 9 at the data of row 8. No external hypothesis.
```
p = 2; P0 = start term (index 0 of 16), n_M = 2: nv=6 solid=[('B', 3, 3), ('B', 0, 2), ('B', 2, 1), ('R', 5, 5), ('R', 0, 4), ('R', 4, 1)] waved=[(2, 3), (4, 5)] mdot=[]
  ord(P0) = 2, normal True, LocStd False, PathInv2 at P0: True
step 1 (P0 -> Q1): weight, twist (False,False), tag band: Q1 = nv=8 solid=[('B', 0, 2), ('B', 2, 1), ('R', 0, 4), ('R', 4, 1)] waved=[(2, 3), (4, 5), (6, 7)] mdot=[(5, 6), (7, 5), (7, 3), (3, 6)]
  ord(Q1) = 4, nM 1, LocStd False, PathInv2 True
step 2 (Q1 -> Q): gg, twist (False,False), tag band; K = 5 (both sources have ord < K and are not LocStd), so BAReach K P0 Q holds
Q = nv=10 solid=[('R', 4, 1), ('R', 0, 8), ('B', 9, 1), ('B', 0, 2)] waved=[(2, 3), (4, 5), (6, 7), (8, 9)] mdot=[(9, 4), (2, 8), (5, 6), (7, 5), (7, 3), (3, 6)]
  Q: ord 6, nM 1 <= p: True, LocStd True, PathInv2 True (blue walks 1, visit sets [[0, 1, 2]], red visit sets [[0, 1, 2]])
  LocReg2 True; LocReg1 (image LocStd) True; LocReg345 on the image True; on the shadow True
  molecule of vertex v (x=0,y=1): [0, 1, 2, 2, 2, 2, 2, 2, 2, 2]; internal molecules [2]; solid edges between different molecules 4
  molecule 0: n_V (atoms) = 1, n_W = 0, n_V <= n_W + 1: True (slack 0); internal: False
  molecule 1: n_V (atoms) = 1, n_W = 0, n_V <= n_W + 1: True (slack 0); internal: False
  molecule 2: n_V (atoms) = 3, n_W = 4, n_V <= n_W + 1: True (slack 2); internal: True
  Hall at A = {2}: walks meeting A = 2 >= |A| = 1; distinct walks through it (LocReg4 needs >= 2): 2
```
R1 witnesses (command `python3 wit56.py`; counts equal BASim3:1909-1913: gg at P_A 23 band + 8 e2, ggSplit at P_C 8/1/5/34) and the replacement `edge` witness (blue 2→0, 2→1; vertices 0, 1 external, 2 internal):
```
baPA (gg)        normal True  nM 1  hwf True  hnb True  k with PathInv2 on the image: [2]
baPB (within)    normal True  nM 1  hwf False  hnb False  k with PathInv2 on the image: [1]
baPC (ggSplit)   normal True  nM 1  hwf True  hnb True  k with PathInv2 on the image: [2]
baPE (edge)      normal True  nM 1  hwf True  hnb False  k with PathInv2 on the image: []
--- all untwisted frame steps at the witnesses (k = the PathInv2 value above): outputs by tag, PathInv2 violations at the outputs
  baPA (gg)        gg       {'e2': 8, 'band': 23}  violations 0
  baPB (within)    within   {'band': 14, 'e2': 3, 'macroA': 34}  violations 0
  baPC (ggSplit)   ggSplit  {'band': 8, 'e1': 1, 'e2': 5, 'macroB': 34}  violations 0
replacement edge witness: nv 3, blue 2->0, blue 2->1:  normal True  k with PathInv2: [1]  hwf True  hnb False
  edge     {'band': 4, 'e1': 1, 'e2': 5}  violations 0
  edge     {'band': 4, 'e1': 1, 'e2': 5}  violations 0
```
(b) Check. Commands (`$SP`): `python3 bfs56p.py 1 3 2000 1 3000; python3 bfs56p.py 2 3 1500 1 6000; python3 bfs56p.py 3 3 1500 1 3000 3000 30000` (all 5-constructor steps with twist and M-splits from the 2^(2p) start terms, depth ≤ 2 exhaustive for p = 1, 2; p = 3: depth 1 exhaustive (13,272 states), depth 2 a random 3,000 of them; depth 3: p = 1 all 1,526 states admitting edge/gg/ggSplit + 2,000 others, p = 2 a random 6,000 of the 67,009 admitting + 1,500 others, p = 3 all 2,557 admitting among a random 30,000 scanned + 1,500 others); `python3 rand56.py 12000 2` (random normal parents with PathInv2, 5,876 constructed + 6,124 mutated by extra M-dots/waved edges, degeneracy classes: ext atom merged 10,135, x~y one atom 4,613, x~y one molecule 3,515, edge in atom 9,123, loop 7,969, internal atoms merged 7,846, twist-invariance failures of the parent 0); `GEN=1 python3 rand56.py 2000 3` (constructor hypotheses hwf, hint, hnb, hbad, sameAtom dropped, only the shape of p, q kept); `python3 agg56.py`:
```
outputs/violations of PathInv2 at the image, per (constructor, tag)
ctor tag                  BFS p=1 d3          BFS p=2 d3          BFS p=3 d3         rand strict            rand GEN
edge band                          -                   -                   -             55841/0            262980/0
edge e1                            -                   -                   -              3005/0              7320/0
edge e2                            -                   -                   -             30348/0             85148/0
gg band                     158468/0            726472/0            815746/0             70037/0            253592/0
gg e2                        10616/0            108384/0             99104/0             12699/0             63060/0
ggSplit band                 64612/0            187168/0            184201/0              3303/0            413236/0
ggSplit e1                    4052/0              9514/0              4704/0               162/0             12029/0
ggSplit e2                    3776/0             48418/0             18663/0               179/0            131639/0
ggSplit macroB              169192/0            547284/0            443360/0              8260/0           1220008/0
weight band                  50364/0            347556/0           1094844/0            860296/0            161504/0
weight e2                     5888/0             35548/0             99084/0            120540/0             22600/0
within band                  41898/0             92684/0            167898/0            175466/0            182128/0
within e2                     5084/0              7598/0             19240/0             34600/0             69000/0
within macroA                93964/0            200564/0            374276/0            420132/0            502256/0
TOTAL                       607914/0           2311190/0           3321120/0           1794868/0           3386500/0
BFS p=1 d3 {'locreg2 fail (all outputs)': 0, 'locstd outputs': 30808, 'locreg2 fail': 0, 'locreg345 image fail': 0, 'locreg345 shadow fail': 0}
BFS p=2 d3 {'locreg2 fail (all outputs)': 0, 'locstd outputs': 194418, 'locreg2 fail': 0, 'locreg345 image fail': 0, 'locreg345 shadow fail': 0}
BFS p=3 d3 {'locreg2 fail (all outputs)': 0, 'locstd outputs': 71568, 'locreg2 fail': 0, 'locreg345 image fail': 0, 'locreg345 shadow fail': 0}
```
```
$ python3 t68.py        # target 6 at p = 1..4; target 8 at every state within 2 steps of the p = 2 start terms
== target 6: n_M at the 2^{2p} start terms of fxyPowGraph p
  p=1: 4 start terms (= 2^(2p) = 4), n_M histogram {0: 3, 1: 1}, max 1 <= p: True, PathInv2 at p: True
  p=2: 16 start terms (= 2^(2p) = 16), n_M histogram {0: 9, 1: 6, 2: 1}, max 2 <= p: True, PathInv2 at p: True
  p=3: 64 start terms (= 2^(2p) = 64), n_M histogram {0: 27, 1: 27, 2: 9, 3: 1}, max 3 <= p: True, PathInv2 at p: True
  p=4: 256 start terms (= 2^(2p) = 256), n_M histogram {0: 81, 1: 108, 2: 54, 3: 12, 4: 1}, max 4 <= p: True, PathInv2 at p: True
== target 8: 141740 distinct states (depth <= 2 from the p = 2 start terms), 19170 locally standard
   BA LocStd (atom level) == band LocStd of the image, all states: True
   image/shadow molecule bijection + coloured edge multisets + externals, all states: True
   LocReg345 on image and on shadow (p = 2) at the locally standard states: 19170 / 19170 of 19170
$ python3 xlevel56.py 1   # the unsplit builder terms X (stage 1 of the route), parents = start terms + depth 1
states 2353
unsplit builder terms X: PathInv2 at image(X): terms / violations per constructor
  gg          9,424 / 0
  ggSplit     1,824 / 0
  weight     31,816 / 0
  within     13,080 / 0
$ python3 control56.py    # control: dropping an edge / flipping a colour / dropping the wave is detected
controls on 1500 outputs of depth-1 steps: {'genuine fail': 0, '(a) edge dropped fail': 452, '(b) colour flipped fail': 452, '(c) wave dropped fail': 437}
```
```
states within 2 steps of the p = 2 start terms: 141740; not locally standard: 122570; states admitting each constructor: {'gg': 51077, 'ggSplit': 43280, 'weight': 39546, 'within': 39878}
```
(d) No hidden input: the `GEN=1` run (3,386,500 outputs, 0 violations) shows that `PathInv2` passes from a parent with `PathInv2` using only the shape of p, q; hwf, hint, hnb, hbad, sameAtom are not used, and nothing from (6).
### Verdict
- Numerics (b): 0 violations of `PathInv2` at the image in 11,421,592 outputs (all five shapes `band`, `e1`, `e2`, `macroA`, `macroB`), n_M ≤ p, LocReg2 at all outputs, LocReg345 on image and shadow at the 296,794 locally standard BFS outputs and at all 19,170 distinct locally standard states of `t68`; target 8 correspondence holds (molecule bijection, coloured edge multisets, externals; LocStd atomic = LocStd of the image). Per target: 1, 2, 3(a), 3(b), 4, 5, 6, 8, 9, 10: PASS; 3(c), 3(d), 3(e): mathematics holds, BLOCKED on pricing (next line); 7: PASS in the Σ form (binder), BLOCKED without Σ.
- Stop rule O2R-C4: (b) has no violation, (c) needs no new row, target 8 holds; but the pricing gives central 2,424 with 3(c)-(e) in L3b1 against 1,575, so split Σ is called (3(c)-(e) to L3b2; L3b1 proves target 7 as `T2456_PathBinder → T2456_LocReg15`, central 1,550). Σ needs the dispatcher's sign-off before 1b (H183 (3)): **BLOCKED**.
- Findings for the dispatcher: (1) R1's `P_E` has no `PathInv2` for any k (row 7): the target 3 (iv) instance needs the replacement `edge` witness above, not `hTE`; (2) no state within 2 steps of the p = 2 start terms admits an `edge` step (`python3 admit56.py` below; so the BFS has no `edge` row); `edge` is covered by the random parents (3,005 e1 and 30,348 e2 outputs, 0 violations); (3) A2 is mirrored (note above).
## (b) Script output — Mon Oct 12 16:28:01 UTC 2026; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2456`, branch `t/T2456` at `e6edc23`
```
$ wc -l RBM3D/Graph/BALocReg1.lean RBM3D/Graph/BALocReg1B.lean     # stop line 2,000 per file (ticket)
     778 RBM3D/Graph/BALocReg1.lean
     440 RBM3D/Graph/BALocReg1B.lean
    1218 total
$ git log --oneline -5 ; git diff --stat main...t/T2456 | tail -4   # branch point 6bdc5a3 = main when claimed; main was not merged in
e6edc23 T2456: module doc of BALocReg1B names the limit of the LocStd instance
0bd0366 T2456: instances after one weight step (target 7), stem-prefixed helpers
15d1000 T2456: L3b1 Graph/BALocReg1, BALocReg1B: coloured path invariant at the atomic image, BASimP', BAShape
af56a5b T2456: WIP BALocReg1, BALocReg1B (targets 1, 2, 3(a)(b), 4-9 proved; instances and docs pending)
6bdc5a3 T2452: merge BA-U U-D census report (report-only; probe stays on t/T2452)
 RBM3D/Graph/BALocReg1.lean  | 778 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BALocReg1B.lean | 440 +++++++++++++++++++++++++
 2 files changed, 1218 insertions(+)
$ grep -n 'sorry\|admit\|native_decide\|^axiom' RBM3D/Graph/BALocReg1.lean RBM3D/Graph/BALocReg1B.lean | wc -l
       0
$ lake build RBM3D.Graph.BALocReg1 RBM3D.Graph.BALocReg1B | tail -2
Build completed successfully (3843 jobs).
```
Whole-library check without editing `RBM3D.lean` or `Test/Axioms.lean` (the hub adds the two imports): scratch file `import RBM3D` + both modules + `#assert_rbm_axioms`:
```
axiom audit: 13338 theorems, 4181 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
errors in the output: 0; lines naming a new declaration or module: 0
```
Axioms (`#print axioms` of all public declarations of both files, script `axioms.lean`; each target below):
```
public declarations: 61; standard three exactly: 54; none: 1; proper subsets: 6; with sorryAx: 0
'BALocReg1_flip_false_ms' depends on axioms: [propext, Quot.sound]
'BALocReg1_flip_false_list' depends on axioms: [propext, Quot.sound]
'BALocReg1_split_perm' depends on axioms: [propext, Quot.sound]
'BALocReg1_forall₂_mem' depends on axioms: [propext]
'BALocReg1_ends' depends on axioms: [propext]
'BALocReg1Inst.pEr' depends on axioms: [propext]
targets with exactly [propext, Classical.choice, Quot.sound] (13 of 13): baEquivPath_holds baPathTwist_holds baShapePath_s1_tn baShapePath_e1_tn baShapePath_twist baSimP'_holds baPathStep_of_simP' baPathStep_holds baPathInit_holds baStart_nM_le baShadow_locReg345 baLocReg15_holds ba_fxyPow_integral_eq
```
Target statements, extracted from the files by `stmt.py` (file:line; statement up to `:=`; `def` with body):
```
BALocReg1.lean:430: theorem baEquivPath_holds (R S : PGraph (Fin 2)) (hRS : R.BAEquivC S) (k : ℕ) (h : R.PathInv2 k) : S.PathInv2 k
BALocReg1.lean:465: theorem baPathTwist_holds (c t : Bool) (P : BAPGraph (Fin 2)) (k : ℕ) : (P.twist c t).img.PathInv2 k ↔ P.img.PathInv2 k
BALocReg1.lean:565: def BAShapePath (sh : BAShape) (T : BTStep) : Prop := ∀ P LT, T P LT → ∀ Q, (sh, Q) ∈ LT → ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k
BALocReg1.lean:569: theorem baShapePath_s1_tn : BAShapePath BAShape.s1 BAFrameStepTN
BALocReg1.lean:575: theorem baShapePath_e1_tn : BAShapePath BAShape.e1 BAFrameStepTN
BALocReg1.lean:581: theorem baShapePath_twist : ∀ sh : BAShape, BAShapePath sh BAFrameStepTN → BAShapePath sh BALocStepT
BALocReg1.lean:596: def BASimP' (m : ℂ) (T : BTStep) : Prop := ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), (∀ k : ℕ, P.img.PathInv2 k → P'.PathInv2 k) ∧ ∀ Q : BAPGraph (Fin 2), (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧ ∃ R ∈ L', ∀ k : ℕ, R.PathInv2 k → Q.img.PathInv2 k
BALocReg1.lean:602: theorem baSimP'_holds (m : ℂ) : BASimP' m BALocStepT
BALocReg1.lean:613: def BAPathStep (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop := ∀ P L, BStep P L → ∀ k : ℕ, P.img.PathInv2 k → ∀ Q ∈ L, Q.img.PathInv2 k
BALocReg1.lean:617: theorem baPathStep_of_simP' (m : ℂ) (T : BTStep) (hS : BASimP' m T) (hX : ∀ sh, sh ≠ BAShape.band → BAShapePath sh T) : BAPathStep (untag T)
BALocReg1.lean:630: theorem baPathStep_holds (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) : BAPathStep (untag BALocStepT)
BALocReg1B.lean:57: def BAPathInit (p : ℕ) : Prop := ∀ P ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P.img.PathInv2 p
BALocReg1B.lean:62: theorem baPathInit_holds (p : ℕ) : BAPathInit p
BALocReg1B.lean:79: theorem baStart_nM_le (p : ℕ) : ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P0.g.nM ≤ p
BALocReg1B.lean:215: theorem baShadow_locReg345 (Q : BAPGraph (Fin 2)) (p : ℕ) (h : PGraph.LocReg345 Q.img p) : (BAShadowPG Q).LocReg345 p
BALocReg1B.lean:253: def BALocReg15 : Prop := ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition → ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p ∧ (Q.g.LocStd → PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p)
BALocReg1B.lean:263: theorem baLocReg15_holds (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) : BALocReg15
BALocReg1B.lean:293: theorem ba_fxyPow_integral_eq (d L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) (p : ℕ) (hp : Even p) (ℓe : Fin 2 → Idx d L W) : ∫ ω, (BAGraph.ofLGraph (fxyPowGraph p)).val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1) ^ (p / 2) * star (fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1)) ^ (p / 2) ∂(PF d L W 0)
```
Pin diff (script `pindiff.py`) and the pins applied (scratch copy of `docs/tickets/checks/T2456-check.lean` + `import RBM3D.Graph.BALocReg1`, `BALocReg1B`; not merged):
```
T2456_LocReg15 body == BALocReg15 body : True
T2456_PathInit body == "∀ p : ℕ," + BAPathInit body : True
T2456_SimP body (instantiated T := BALocStepT) == BASimP' body : True
310:example : T2456_S1Path := baShapePath_s1_tn
311:example : T2456_E1Path := baShapePath_e1_tn
312:example : T2456_SimP := fun m => baSimP'_holds m
313:example : T2456_PathBinder → T2456_PathStep := baPathStep_holds
314:example : T2456_PathInit := baPathInit_holds
315:example : T2456_StartNM := baStart_nM_le
316:example : T2456_PathBinder → T2456_LocReg15 := baLocReg15_holds
317:example : T2456_ValueId := fun d L W _ _ g0 Em t m p hp ℓe => ba_fxyPow_integral_eq d L W g0 Em t m p hp ℓe
errors compiling the scratch copy: 0
the check file itself, compiled on the branch: exit 0
```
Compiled instances (target 10); `grep -n '^example'` and the helper theorems they use:
```
RBM3D/Graph/BALocReg1.lean:745:example : ((baPG baPEr).twist true true).img.PathInv2 1 ∧ (baPG baPEr).img.PathInv2 1 :=
RBM3D/Graph/BALocReg1.lean:750:example : (∃ Q, (BAShape.e1, Q) ∈ outsEr ∧ Q.img.PathInv2 1) ∧ BAShape.s1 ∉ outsEr.map Prod.fst := by
RBM3D/Graph/BALocReg1.lean:763:example (m : ℂ) (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN)
RBM3D/Graph/BALocReg1B.lean:329:example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, P0.img.PathInv2 2 ∧ P0.g.nM ≤ 2 := by
RBM3D/Graph/BALocReg1B.lean:334:example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
RBM3D/Graph/BALocReg1B.lean:403:example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
RBM3D/Graph/BALocReg1B.lean:419:example : (liftC localReg2_inst_Q.pack).g.LocStd ∧ (liftC localReg2_inst_Q.pack).img.PathInv2 2 ∧ (liftC localReg2_ins
RBM3D/Graph/BALocReg1B.lean:432:example : ∫ ω, (BAGraph.ofLGraph (fxyPowGraph 2)).val (BAlwData 3 4 2 1 1 1 1 ω) ![0, 1] ∂(PF 3 4 2 0) =
```
The two examples that carry the step (targets 2, 4 at the `edge` witness) and the reach (target 7 after one step), verbatim:
```lean
/-- targets 2 and 4 at the twisted step at the witness: `BASimP'` gives a band step whose output carries the invariant of a `band` output (every deterministic hypothesis discharged);
the step lemma `baPathStep_holds` (with the shape binder of split Σ as a hypothesis) carries it to every output -/
example (m : ℂ) (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
    (∃ Q, (BAShape.band, Q) ∈ outsErT ∧ Q.img.PathInv2 1) ∧ ∀ Q ∈ outsErT.map Prod.snd, Q.img.PathInv2 1 := by
  refine ⟨?_, baPathStep_holds hX _ _ ⟨outsErT, stepErT, rfl⟩ 1 pathInv2_ErT⟩
  obtain ⟨P', hP', hQ⟩ := baSimP'_holds m _ _ stepErT
  obtain ⟨Q, hQb⟩ := BASimInst.tag_exists outsErT .band (by
    unfold outsErT; simp only [List.map_map, Function.comp_def]; exact tags_Er.1)
  obtain ⟨L', hst, R, hR, hRQ⟩ := hQ Q hQb
  exact ⟨Q, hQb, hRQ 1 (pathInv2_locStep hst (hP' 1 pathInv2_ErT) R hR)⟩

/-- target 7 (and, through it, the step lemma of target 4 and the start of targets 5, 6) from a start term **after one step**: the weight step at the blue circled loop has an output `R`,
`BAReach` reaches it (the start term is not locally standard: its loop lies inside an atom), and the contract holds at `R` (the shape binder of split Σ stays a hypothesis) -/
example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
    ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (K : ℤ) (R : BAPGraph (Fin 2)), BAReach K P0 R ∧
      R.img.PathInv2 2 ∧ R.g.nM ≤ 2 ∧ PGraph.LocReg2 R.img 2 := by
  obtain ⟨P0, hP0, L, hL, hne, hnl⟩ := BALocReg1B_start_step
  obtain ⟨R, hR⟩ := List.exists_mem_of_ne_nil _ hne
  have hreach : BAReach (P0.g.scalingOrder + 1) P0 R := BAReach.step P0 P0 R L (BAReach.refl P0) (by omega) hnl hL hR
  obtain ⟨h1, h2, h3, -⟩ := baLocReg15_holds hX 2 P0 hP0 _ R hreach
  exact ⟨P0, hP0, _, R, hreach, h1, h2, h3⟩
```
Name-clash grep of the new public names (`clash.sh`: `git grep -wFf` of the 61 names over `main` (a1412ad at this run), `t/T2449`-`t/T2455`, `t/T2457`-`t/T2459`, and `HEAD` outside the two files; `t/T2460`, `t/T2461` do not exist):
```
git grep -wFf <the new public names> over: main t/T2449 t/T2450 t/T2451 t/T2452 t/T2453 t/T2454 t/T2455 t/T2457 t/T2458 t/T2459
hits above (empty = none)
hits in HEAD outside the two files above (empty = none)
probe branch t/T2397 (reference only, never merged):
t/T2397 (probe, reference only, never merged; source of the pins): 5 lines, e.g. t/T2397:RBM3D/Probe/T2397Pins.lean:377:theorem inst_baPathSt
```
Mathlib names (script `mathlib.lean`: `#check @name`): 35 names, 0 errors (names listed in (c)). Ports: none from `../RBM1D`, `../RBM2D` (no `git diff --stat` there); one copy inside this project, `BAStepS.lean:269-350` (private helpers) as `BALocReg1_tagStd_ne` ... `BALocReg1_frameT_tags` (BAStepS commit `e9528ea`).

Narrative (script output above is the evidence; every number is from it):
- **Split Σ** (CONTROL H250 (2)): targets 3 (c)-(e) (`BAShapePath` for `e2`, `macroA`, `macroB`) are not here. `baPathStep_holds` and `baLocReg15_holds` take the text of
  `T2456_PathBinder` as their hypothesis `hX` (no new `Prop`; `example : T2456_PathBinder → T2456_PathStep` and `→ T2456_LocReg15` compile, line above). L3b2 concludes the binder.
- **Delivered**: targets 1, 2, 3 (a) (b), 4, 5, 6, 7 (with `hX`), 8, 9 and the instances of 10, in 778 + 440 lines (central of (a) with Σ: 1,550; stop line 2,000 per file). No
  `inductive` (the word occurs only in docstrings), no registry entry, no edit of `Test/Axioms.lean` or `RBM3D.lean` (the hub adds the two imports); the scratch `#assert_rbm_axioms` names no new premise. No (a′): nothing of (a) used here was contradicted (the replacement witness has `PathInv2 1`, as (a) row 7 says).
- **Route.** One generic lemma, `BALocReg1_pathAt_map` (BALocReg1.lean:77): `LGraph.localReg2_pathFam_map` (LR2:616) at the atomic image for a vertex map that respects the atoms, is onto up
  to molecules and sends waved edges into molecules; the budget moves up to the colour flip `c`, removed loops (`of_add_diag`, LR2:257) and loops added at a colour already present
  (`add_diag`, LR2:264). Uses: `M`-split + merge, hence `BALocReg1_pathAt_partition` for **any** term and the packed outputs `BAScost_pack` (reused by L3b2 for `e2`, `macroA`, `macroB`); the
  twist (colours flip); `BALocReg1_pathAt_ext` for `BAGraph.ext` terms; `BALocReg1_pathAt_lanlwT1` (target 3 (b)); target 5 through `BAAtomic_pathFam_iff`.
- **Target 8** (`baShadow_locReg345`): the walks of (3)-(5) are carried along a bijection of the molecules of image and shadow (`BALocReg1_molMap`, from `BAGraph.img_molOf_eq_iff` and
  `BAAtom_shadow_molOf_eq_iff`); the molecular edge multisets agree. It needs no `Q.g.Normal` (the check's non-binding shape has it).
- **Target 1**: `baPathTwist_holds` is `↔` (the twist is an involution); `baEquivPath_holds` is one direction (R to S), the one `baSimP'_holds` reads; the check's non-binding shape has `↔`.
- **Tags**: `BALocReg1_frameT_tags` and its four helpers are a copy of the private `BAStepS_frameT_tags` (BAStepS.lean:269-350) under the stem (dispatcher note (1)), not `open private`.
- **Instances** (map: target 1 at BALocReg1:745; 3 (a)(b) at :750; 2, 4 at :763; 5, 6 at BALocReg1B:329; 7 at :334 from a start term and at :403 after one weight step; 8 and the
  `LocStd` chain at :419; 9 at :432). The `edge` witness is the replacement of (a) (R1's `baPE` has no `PathInv2`, (a) row 7 and finding (1)): `E = Fin 2`, `I = Fin 1`, blue `i -> x`,
  `i -> y`; `PathInv2 1` at its image is a hand-built family (BALocReg1:657, one blue walk `x -> i -> y`) transferred by `BAAtomic_pathFam_iff`; `tags_Er` (`decide +kernel`) shows the
  tags `band`, `e1`, `e2` present and `s1` absent among its `edge` outputs. The hypothesis `hX` stays a hypothesis of the examples (L3b2's pin).
- **Repair (audit round 1, items 1-2; script output in (b′))**: target 3 (b) is now also applied at R1's `ggSplit` step `hTC` at `P_C` (BALocReg1:874), with `PathInv2 2`
  at its image (`pathInv2_C`: a hand-built family of two blue walks on a band twin, moved by `BALocReg1_pathAt_map`). The `LocStd` branch of target 7 is applied at a graph
  `Q` reached from a `p = 2` start term by two weight steps (BALocReg1B:892, via `BALocReg1B_reach_locStd`), with `Q.g.LocStd` and `Q.g.nM = 1` proved: renaming lemmas carry
  `LocStd`, `n_M` between the packed outputs (quotient types) and concrete twins that `decide` evaluates (`BALocReg1B_data`); `hX` stays the only open hypothesis.

### (b′) Repair of the round-1 RETURN (repairer: claude-opus-5-5) — Mon Oct 12 17:03:02 UTC 2026; branch `t/T2456` at `6926e67` (audit items 1-3; no target statement changed)
```
$ wc -l RBM3D/Graph/BALocReg1.lean RBM3D/Graph/BALocReg1B.lean ; git log --oneline e6edc23..HEAD ; git diff e6edc23 HEAD | grep -cE '^-[^-]'   # stop line 2,000; removed: docstrings only
     884 RBM3D/Graph/BALocReg1.lean
     926 RBM3D/Graph/BALocReg1B.lean
6926e67 T2456 repair: docstring of BALocReg1B_reach_locStd names the path
d6ecede T2456 repair: LocStd branch of target 7 at a graph reached by two weight steps from a p = 2 start term (renaming lemmas for LocStd, n_M)
1e2e75f T2456 repair: target 3 (b) instance at R1's ggSplit step hTC at P_C (PathInv2 2)
10
$ lake build RBM3D.Graph.BALocReg1 RBM3D.Graph.BALocReg1B > build.log; tail -1 build.log; grep -c 'Graph/BALocReg1' build.log
Build completed successfully (3843 jobs).
0
$ lake env lean axioms_r1.lean > axioms_r1.out 2>&1 ; lake env lean AssertT2456.lean > assert_r1.out 2>&1 ; head -1 assert_r1.out ; bash summ.sh   # #print axioms of the 13 targets, then of the 49 new public declarations
axiom audit: 13373 theorems, 4195 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
axioms: lines 62; targets std3 13; new std3 37; new none 6; new other 6; sorryAx 0
check file: exit 0, error lines 0
clash: names 45, main 62eed82, hits on refs 0, hits in HEAD outside the two files 0
$ grep -n '^example' (new) ; statements extracted by script (up to `:=`)
BALocReg1.lean:874: example : ∃ Q, (BAShape.e1, Q) ∈ (baPG baPC).splitOutsT pC qC 0 ∧ Q.img.PathInv2 2
BALocReg1B.lean:892: example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q ∧ Q.g.LocStd ∧ Q.g.nM = 1 ∧ PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2
BALocReg1B.lean:856: theorem BALocReg1B_reach_locStd : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (Q1 Q : BAPGraph (Fin 2)) (L1 L2 : List (BAPGraph (Fin 2))) (K : ℤ), BALocStep P0 L1 ∧ Q1 ∈ L1 ∧ BALocStep Q1 L2 ∧ Q ∈ L2 ∧ ¬ P0.g.LocStd ∧ ¬ Q1.g.LocStd ∧ BAReach K P0 Q ∧ Q.g.LocStd ∧ Q.g.nM = 1 ∧ ∃ φ : Fin 2 ⊕ ((Fin (2 * 2) ⊕ Fin 2) ⊕ Fin 2) → Q.E' ⊕ Q.I', BALocReg1B_Good φ ∧ Q.g = BALocReg1B_mapG φ BALocReg1B_G2
$ python3 ww56.py | head -4 | cut -c1-200   # first 2 of 4 lines; scratch, on the 1a model ba56.py: two weight steps, P0 -> LocStd Q with n_M >= 1 and PathInv2 2; (start, (c, p, family, term, split) x 2)
32
0 (False, 0, 'lw2', 4, 2) (True, 2, 'lw2', 1, 2)
```
(`summ.sh`: std3 = `[propext, Classical.choice, Quot.sound]`; clash refs = `main`, `t/T2449`-`t/T2455`, `t/T2457`-`t/T2462`.) Mathlib names newly used (compiled): `Relation.ReflTransGen.lift`, `List.filter_map`, `List.forall_mem_map`, `List.flatMap_map`, `List.map_flatMap`, `List.filter_eq_self`, `List.getElem_mem`, `List.mem_flatMap`, `List.Perm.swap`, `Finset.image_injective`, `Finset.image_image`, `Sum.map_injective`, `Sum.inl_injective`, `Bool.or_eq_true_iff`, `of_decide_eq_true`.
### (c) Verified Mathlib names (all `#check`ed, script above; used in the proofs)
- `Multiset.coe_eq_coe` (`↑l₁ = ↑l₂ ↔ l₁.Perm l₂`), `Multiset.map_coe`, `Multiset.coe_add`, `Multiset.map_id`, `Multiset.coe_mapAddMonoidHom`, `Multiset.map_le_map`, `map_sum`
- `Finset.card_image_of_injective`, `Finset.card_le_card`, `Finset.mem_image`
- `Function.surjInv`, `Function.surjInv_eq`; `Equiv.ofBijective`, `Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`
- `SimpleGraph.ConnectedComponent.lift` (needs a walk-indexed hypothesis), `.ind`, `.eq`; `Sym2.ind`, `Sym2.mk_isDiag_iff`, `Sym2.mem_iff`
- `List.filter_map`, `List.map_map`, `List.map_id''`, `List.map_congr_left`, `List.filter_congr`, `List.flatMap_cons`, `List.append_eq_nil_iff`, `List.map_eq_nil_iff`, `List.exists_mem_of_ne_nil`
- `List.Perm.of_eq`, `List.perm_append_singleton` (`l ++ [a] ~ a :: l`), `List.Perm.append_right`; `Bool.cond_false` (`cond_false` is deprecated); `decide_eq_decide`
- Verified absent: `Sym2.map_comp_apply` (`Unknown constant`); `import Mathlib` has no olean in this tree (checked through `import RBM3D.Graph.BALocReg1B`).

### (d) Open issues and paper-delta candidates
- Open: (1) none left from the round-1 RETURN (both instances are in (b′)). (2) L3b2
  proves `BAShapePath` for `e2`, `macroA`, `macroB`; the tools are `BALocReg1_pathAt_ext`/`_partition`/`_twist`, the budget pattern `Bm`, `Drem`, `Dadd` of `BALocReg1_pathAt_map`, and the witness `BALocReg1Inst.baPEr`
  (`hStepEr`, `pathInv2_Er`, `tags_Er` has `e2`). (3) Hub: add `import RBM3D.Graph.BALocReg1`, `import RBM3D.Graph.BALocReg1B` after the last `import` of `RBM3D.lean`.
- `T2456a`: (3)-(5) at BA are read on the atomic image `Q.img` and on the shadow `BAShadowPG Q`, not on the BA molecular graph; the molecules coincide (`BAGraph.img_molOf_eq_iff`, BAAtomic:388; `BAGraph.shadow_mol`, BAAtom:86).
- `T2456b`: `(eq:MolVW)` at BA counts atoms (`n_V ≤ n_W + 1` of the image); same as the candidate `T2397c` named in the ticket.
- `T2456c`: the invariant is the coloured walk family `PathInv2` (walks, not paths; existing `T2151d`, `T2142a`), carried through the image.
- `T2456d`: split Σ (H250 (2)): the shapes `e2`, `macroA`, `macroB` enter target 4 and target 7 as the binder `hX`; target 3 (c)-(e) belong to L3b2.
- `T2456e`: tool shapes of the check differ: `baEquivPath_holds` is `→` (check: `↔`); `baShadow_locReg345` has no `Q.g.Normal` (check: with).
