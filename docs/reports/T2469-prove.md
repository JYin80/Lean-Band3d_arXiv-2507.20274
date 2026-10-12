Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 20:26:20 UTC 2026
Setting: C1, combinatorial; no analytic exponent, and no new external hypothesis (the data `BASelf`, `0 ≤ t < 1` enter only through the merged `ba_localregularX`; the flow point `flowP_data` is merged, `#check` clean in the hub's compile of `T2469-check.lean`: 0 error lines). Python only, no Lean; scratch = `scratchpad/T2469/`.
Model: `ba56.py` (copied from T2456's scratchpad: BA graph = (nv, solid, waved, M-dots), builders BAExpandW:122-148, BAWeightOp:68-73, BAGGOp:73-90, BASim:115-136, constructors BASim:138-161; `path_inv2` = exact `localReg2_Fam` of the atomic image incl. Hall and colour-visit, LR2:147) + `term69.py` (term level: every UNSPLIT builder term X, as `BALocReg1_PathAt X k a b` reads it). Check = `PathInv2 k` of the parent ⇒ `PathInv2 k` of X.
### (i) Exponent table (no exponent; thresholds, counts, budgets)
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | walks k | numerics k ∈ {0,1,2,3} (parents with PathInv2 at k: 5,132 / 49,568 / 121,844 / 104,163); instance p = 2 | term lemmas hold for every k (`BAShapePath` is `∀ k`) | — |
| 2 | K of `BALocReg15` vs `lvl1Cutoff` (BAEngine:228, `(… : ℤ)`) | K = ⌈(10 + 2·2 + 3·2)/(1/4)⌉ = 80 at p=2, c=1/4, K0=2, d=3, D=10 (`inst69.py`) | ord(source) < K: ord P0 = 2, ord Q1 = 4 | 78, 76 |
| 3 | conj (a) of `BALocRegConcl` at the instance Q | 2p = 4 ≤ ord Q = 6; ext atoms distinct ⇒ 3p = 6 ≤ 6 | `2p ≤ ord`, `3p ≤ ord` | 2; 0 |
| 4 | conj (c): `Q.nM ≤ P0.nM`, `nA−nW`, `ord P0 ≤ ord Q` | 1 ≤ 2; −1 ≤ 2; 2 ≤ 6 | as stated | 1; 3; 4 |
| 5 | `Q.nM ≤ p` (3 (b)) | 1 ≤ 2 | `n_M ≤ p` | 1 |
| 6 | budget (\|Drem\|,\|Dadd\|) of `BALocReg1_pathAt_ext` per term | see table (a); intermediates trA, trB (0,0) | `hDrem`, `hDadd` diagonal; `hcov(Bm)` | `ext` valid at every term of the 26 non-detour labels in strict mode (`route69.py`, 20,000 parents) |
| 7 | PathInv2 violations, term level | 0 in 44,116,876 checks (strict 1,719,223; gen 33,672,397; shape 8,021,781; BFS 703,436; witnesses 39) | 0 | baseline T2456 frame level: 0 in 11,421,592 |
| 8 | central of the row | 2,130 lines (file 1 1,240; file 2 890; `fit69.py` in (c)) | split rule §227: central ≤ 1,575 | −555 (exceeds) |
| 9 | per-file stop line / reserve rule | file 1 1,240, file 2 890 | ≤ 2,000 per file; `BALocReg2C` only if file 1 > 1,800 | 760; 1,110; reserve not needed (slack 560) |
| 10 | upper references | T2456 final/central 1.17 → 2,487; TLC-4 2.6× → 5,538 | two files 4,000, with the reserve 6,000 | 1,513 / −1,538 (2.6× exceeds two files) |
Table (a) as proved (command `python3 summ69.py`; verbatim). Columns: the 17 builder terms of T2447-prove.md:9-28 plus `A1` of `gg2`, the two intermediates I1 = `Γ.BAScost_trA p`, I2 = `Γ.BAScost_trB p q`; band twin for reference (LR2 lines); route = `ext` (`BALocReg1_pathAt_ext`, merged :309, with the budget sizes (|Drem|,|Dadd|)) or `thr` (one `localReg2_Fam.thr` step, LR2:381, then `of_add_diag`/`add_diag`); `L` = estimated proof lines; term checks / violations at random parents under the strict constructor hypotheses, with them dropped (gen), at BFS parents, and at the stage-2 copies (S2 = terms of `tr.lw2/lw4/gg2/gg4` at the transfer graph `tr`; SHAPE = only the hypotheses of the check's intermediate shapes).
```
# | term | ctor; tag | band pairing | route (|Drem|,|Dadd|) | hyps used | strict | gen | BFS | stage-2 copy at tr (S2 / SHAPE)
1 | lanlwD | lw2/within/edge/ggSplit tail; e2 | oe1xD:1165 | thr 65L | p blue circled | 430k/0 | 6.57M/0 | 145k/0 | S2 1.51M/0 | SHAPE 1.80M/0
2 | lw2 head | weight; e2 | owxT1:1027 | ext (0,1) 45L | p loop | 92k/0 | 92k/0 | 21k/0 | S2 412k/0 | SHAPE 504k/0
3 | lw4 head | weight; e2 | owxT2:1052 | ext (0,1) 45L | p loop | 92k/0 | 92k/0 | 21k/0 | S2 412k/0 | SHAPE 504k/0
4 | lw4 tail | weight; e2 | owxT4:1088 | thr 65L | p loop | 283k/0 | 283k/0 | 85k/0 | S2 1.51M/0 | SHAPE 1.80M/0
5 | within head | within; e2 | oe1xOwx:1143 | ext (0,1) =lanlwT1.splitG[0] 10L | p blue circled, x!=y | 23k/0 | 412k/0 | 14k/0 | 
6 | gg2 A1 | gg; e2 | none (stage 2 only) | ext (2,0) 45L | p,q blue circled, q.dst=p.src | 40k/0 | 266k/0 | 11k/0 | S2 922k/0 | SHAPE 207k/0
7 | gg2 A2 | gg; e2 | R2:1330 (mirrored) | ext (1,0) 45L | same | 40k/0 | 266k/0 | 11k/0 | S2 922k/0 | SHAPE 207k/0
8 | gg2 A3 | gg; e2 | R2:1330 | ext (1,0) 45L | same | 40k/0 | 266k/0 | 11k/0 | S2 922k/0 | SHAPE 207k/0
9 | gg2 A4 | gg; e2 | R3:1352 | ext (0,1) 45L | same | 40k/0 | 266k/0 | 11k/0 | S2 922k/0 | SHAPE 207k/0
10 | gg2 A5 | gg; e2 | R5:1410 | ext (0,1) 45L | same | 40k/0 | 266k/0 | 11k/0 | S2 922k/0 | SHAPE 207k/0
11 | gg2 AD | gg; e2 | R7:1481 | thr 65L | same | 95k/0 | 833k/0 | 26k/0 | S2 2.97M/0 | SHAPE 631k/0
12 | gg4 B1 | gg; e2 | R4:1374 | ext (0,1) 45L | same | 40k/0 | 266k/0 | 11k/0 | S2 922k/0 | SHAPE 207k/0
13 | gg4 B2 | gg; e2 | R6:1444 | ext (0,1) 45L | same | 40k/0 | 266k/0 | 11k/0 | S2 922k/0 | SHAPE 207k/0
14 | gg4 BD | gg; e2 | R8:1510 | thr 65L | same | 95k/0 | 833k/0 | 26k/0 | S2 2.97M/0 | SHAPE 631k/0
15 | ggSplit d1 | ggSplit; e2 | R5 at a | ext (0,1) 45L (hsame) | p,q blue circled | 6754/0 | 922k/0 | 9976/0 | 
16 | ggSplit d2 | ggSplit; macroB | R2 | ext (1,0) 45L | same | 6754/0 | 922k/0 | 9976/0 | 
17 | ggSplit d3 | ggSplit; macroB | R2 | ext (1,0) 45L | same | 6754/0 | 922k/0 | 9976/0 | 
18 | ggSplit d4 | ggSplit; macroB | 2 x R2 (map+of_add_diag) | ext (2,0) 45L | same | 6754/0 | 922k/0 | 9976/0 | 
I1 | trA (macro a) | within; stage 2 hop 1 | map + add_diag | ext (0,0) 70L | p blue circled | 23k/0 | 412k/0 | 14k/0 | SHAPE 504k/0
I2 | trB (macro b) | ggSplit; stage 2 hop 1 | 2 x R2 | ext (0,0) 70L | p,q blue circled | 6754/0 | 922k/0 | 9976/0 | SHAPE 207k/0
TOTAL checks/violations: strict [1719223, 0] gen [33672397, 0] shape [8021781, 0] BFS [703436, 0]
lanlwT1 (e1, merged L3b1): strict 28k/0 gen 1.43M/0 BFS 9976/0
```
### (b) PathInv2 at term level — commands and verbatim totals (stop rule O2R-C4: a violation ends the 1a BLOCKED; none occurred)
```
$ python3 run69.py 80000 11; python3 run69.py 80000 12   # random normal parents: rand56 generator + targeted `gen69.py` (hwf, hnb by construction; flipped edges for `edge`) + mutated reached states; every constructor instance, every term, intermediates, stage 2
parents 160,000; k-values tested {0: 5132, 1: 49568, 2: 121844, 3: 104163}; parent classes (a parent can lie in several): ext atom merged 77,126; x~y molecule 54,809; x~y atom 21,598; edge in atom 88,299; loop 80,268; int atoms merged 81,152; plain 13,159
TOTAL checks/violations: strict 1,719,223 / 0; gen (hwf, hint, hnb, hbad, sameAtom dropped, shapes of p, q kept) 33,672,397 / 0; shape (intermediates trA, trB and their S2 terms at the hypotheses of the check's shapes only) 8,021,781 / 0
class coverage per label: gen 31 of 34 labels hit all 7 classes (lw2.head, lw4.head, lw4.tail miss `plain`: a weight step needs a loop); shape 15 of 15; strict gg labels miss `edge in atom`, `loop` (hwf excludes them), strict ggSplit and S2 labels also `plain`
$ python3 bfs69.py 1 3 1500 1; python3 bfs69.py 2 2 4000 2; python3 bfs69.py 3 1 3000 3   # reached states from the 2^(2p) start terms, 4 twists, strict
p = 1: states per level [4, 92, 5314, 1500 (sampled)], with PathInv2: 6910, checks/violations 270,104 / 0;  p = 2: [16, 2337, 4000 (sampled)], 6353, 239,326 / 0;  p = 3: [40, 3000 (sampled)], 3040, 194,006 / 0   (p = 3 depth 2 was started and stopped after 14 minutes: not run)
$ python3 ctor69.py   # strict instances per constructor (`edge` is not reached from the start terms, T2456 finding 2)
parents 6000 strict instances per constructor: {'edge': 808, 'ggSplit': 173, 'weight': 1847, 'within': 176, 'gg': 992}
edge terms: {('edge', 'lanlwT1'): (1186, 0), ('edge', 'lanlwD'): (4097, 0)}  total violations 0
$ python3 control69.py   # mutants of the 94,807 terms X (parents of any k): the checker detects a wrong term; genuine failures 0
{'terms': 94807, '(a) edge dropped fail': 45081, '(b) colour flipped fail': 38854, '(c) wave dropped fail': 39117}
$ python3 route69.py 20000 3; python3 thr69.py 6000 5; python3 rsum69.py   # proof route per term (molecule multisets A of Γ's edges and B of X's edges in X's molecules)
[strict] ext route (hnew, offdiag(A)=offdiag(B), hcov(Bm)) valid at ALL terms of 26 of 26 non-detour labels
[strict] detour lanlwD   : ext route 28,309/34,995; thr route (one localReg2_Fam.thr step + of_add_diag/add_diag) 10,226/10,226; S2 copy thr 1,365/1,365
[strict] detour lw4.tail : ext route 19,120/22,791; thr route (one localReg2_Fam.thr step + of_add_diag/add_diag) 6,677/6,677; S2 copy thr 1,365/1,365
[strict] detour gg2.AD   : ext route 4,730/8,664; thr route (one localReg2_Fam.thr step + of_add_diag/add_diag) 2,740/2,740; S2 copy thr 458/458
[strict] detour gg4.BD   : ext route 4,730/8,664; thr route (one localReg2_Fam.thr step + of_add_diag/add_diag) 2,740/2,740; S2 copy thr 458/458
[gen] ext route (hnew, offdiag(A)=offdiag(B), hcov(Bm)) valid at ALL terms of 25 of 26 non-detour labels; not at all terms: ggSplit.d1 50990/76025
$ python3 wit69.py   # the witnesses of target 4 (Lean literals BASim3:1878-1893, BASim:1964-1966, BALocReg1:657, 715-728), term level and frame outputs
P_A  (gg, k=2): normal True, PathInv2 2 True, blue walks 2, visit sets [[0, 1], [0, 1, 2]], molecules [0, 1, 2, 2, 2]; terms 9/0; frame outputs: gg {'e2': 8, 'band': 23} viol 0
P_B  (within, k=1): normal True, PathInv2 1 True, blue walks 1, visit sets [[0, 1, 2]], molecules [0, 1, 2, 2, 2]; terms 10/0; frame outputs: within {'band': 14, 'e2': 3, 'macroA': 34} viol 0
P_C  (ggSplit, k=2): normal True, PathInv2 2 True, blue walks 2, visit sets [[0, 1], [0, 1, 2]], molecules [0, 1, 2, 2, 2]; terms 16/0; frame outputs: ggSplit {'band': 8, 'e1': 1, 'e2': 5, 'macroB': 34} viol 0
baPEr (edge, k=1): normal True, PathInv2 1 True, blue walks 1, visit sets [[0, 1, 2]], molecules [0, 1, 2]; terms 4/0; frame outputs: edge {'band': 4, 'e1': 1, 'e2': 5} viol 0
```
### (ii) One concrete nondegenerate instance (p = 2, c = 1/4, K0 = 2, d = 3, D = 10; targets 1–4; no `N = 0`, no empty index, no collapsed window)
```
$ python3 inst69.py   # P0 = start term, two steps to a locally standard Q with n_M = 1; conj (a), (c) of BALocRegConcl and the conclusions of 3 (b) at Q
p=2 c=1/4 K0=2 d=3 D=10; P0: counters {'nS': 6, 'nW': 2, 'nA': 4, 'nM': 2}, ord 2; cutoff K = ceil((10 + 2*2 + 3*2)/1/4) = 80
BAReach 80 P0 Q: steps ('weight', 'band'), ('gg', 'band'); sources ord(P0) = 2 < K, ord(Q1) = 4 < K, neither LocStd: True True
(a) Q: LocStd True, 2p = 4 <= ord Q = 6; ext atoms distinct True so 3p = 6 <= ord Q: True (slack 0)
(c) Q: normal True, ord P0 = 2 <= ord Q: True; nM Q = 1 <= nM P0 = 2; nA-nW: Q -1 <= P0 2
3 (b) at Q: PathInv2 2: True; nM <= p: True; LocReg2: True; LocReg1: True; LocReg345 image: True; shadow: True
$ python3 weight_e2.py | head -2; python3 wecheck.py | sort | uniq -c   # target 4 (v): a weight step with an e2 output at a start term of p = 2
start terms 16 all with PathInv2 2;  (ctor, tag) outputs over all 16 start terms, 4 twists: {('weight', 'band'): 2976, ('weight', 'e2'): 224, ('within', 'band'): 136, ('within', 'macroA'): 272}
weight e2 outputs: 224
   4 weight at (True, True, 3, 3) term lanlwD e2-split outputs 1 of 8 PathInv2 2 at X: True
   4 weight at (True, True, 3, 3) term lw4.tail e2-split outputs 1 of 8 PathInv2 2 at X: True
```
Target 4 data: (i) `within` at P_B, k = 1: e2 3, macroA 34 outputs, 0 violations, hand-built family = one blue walk 0 → molecule {2,3,4} → 1; (ii) `ggSplit` at P_C, k = 2: e2 5, macroB 34, `BALocReg1Inst.pathInv2_C`; (iii) `gg` at P_A, k = 2: e2 8, blue walks visit sets {0,1}, {0,1,2} (hand-built); (iv) `edge` at `baPEr` (= nv 3, blue 2→0, 2→1), k = 1: e2 5; (v) `weight` at the all-circled start term (index 0), untwisted: 8 e2 outputs (terms lanlwD ×4 and lw4 tail ×4), all PathInv2 2, so no stated witness is needed; (vi), (vii) the lines above (K = 80); (viii) the term-level counts of the witness lines. External hypothesis: none new (limit computation: not applicable).
### (c) Fit (items (c), (d), (e))
```
$ python3 fit69.py
wc -l: BALocReg1 884 + BALocReg1B 926 = 1810 (T2456 1a central without 3c-e: 1550 incl. instances); BAShapeO2 1094 BAShapeO2B 447 LocalRegular2 2068
BA path term lemma BALocReg1_pathAt_lanlwT1 (ext route, 2 new edges + 1 loop): 46 lines; band analogue localReg2_pathFam_oe1xOwx: 22 lines; ratio 2.09
17 band lemmas paired with the 17 builder terms (+1 for d4's second R2) = 460 lines; x 2.1 = 962; cost-twin term proofs 588 + A1 ~25
per-term estimates (ext 45 as measured, thr 65, within head 10 via splitG[0], A1 45): 855 lines
file 1 BALocReg2: header, imports, docs 90; 17+1 term lemmas 855; list forms lw2 lw4 within gg2 gg4 (cost twins 7+7+9+16+13) 60; ext-term helpers (molecule equalities, hnew) 110; thr variant of pathAt_map 100; perm_pq, perm_pqr, perm_rot copies 25 => 1240
file 2 BALocReg2B: header, imports, docs 80; trA, trB 140; stage-2 composites macroA, macroB (cost 13+34) 50; baShapePath e2/macroA/macroB _tn (cost 48+34+47) 125; private copies (group, group_ne, tag_ne x2, mem_pq, lwSplit_last, ext_normal, frameT_tags + 4 helpers) 145; 1(d), 2, 3(a), 3(b), 3(c) 100; instances (ticket estimate) 250 => 890
central 2130; split rule 1,575: True; reserve rule (file 1 > 1,800): False; stop line 2,000/file: file 1 slack 760, file 2 slack 1110
T2456 precedent final/central = 1.17 -> 2487; TLC-4 2.6x = 5538 (2 files = 4,000, 3 files = 6,000); dispatcher 900/1300/2400 (2.6 x 1300 = 3380)
if split at BALocReg2 | BALocReg2B: L3b2a = 1240 (<= 1,575: True), L3b2b = 890 (<= 1,575: True)
```
Verdict on the split rule: central 2,130 > 1,575, so §227 applies (boundary `BALocReg2 | BALocReg2B`: L3b2a = target 1 (a), 1,240; L3b2b = the rest, 890; each ≤ 1,575). Reserve `BALocReg2C`: not needed (file 1 slack 560 below 1,800). A single row stays within the per-file stop line, but only the split keeps each row inside the §227 range.
(d) No hidden input: the model reads only the constructor shapes (gen/shape totals above, 0 violations with hwf, hint, hnb, hbad, sameAtom dropped); it uses nothing of (6), `BAShapeLL` or (1)–(5). The one hypothesis a route needs beyond the shapes is `hsame` for the `ext` route of d1 (gen: 50,990 of 76,025 terms; it is a `ggSplit` constructor hypothesis, and PathInv2 holds without it). trA needs only `p` blue circled (shape: 504k checks), trB only the shapes of `p`, `q`.
(e) Composition (statement check): `lvl1Cutoff c K0 d D P0.g.counters : ℕ` cast to ℤ (BAEngine:228) is the `K : ℤ` of `BALocReg15` (BALocReg1B:254); conj (c) gives `P0 ∈ partition` and `BAReach`; conj (a) gives `Q.g.LocStd` for `Q ∈ outs` only, so `LocReg1`, `LocReg345` are stated for `outs` (as the check's `T2469_ConclUpto5`); the inst69 lines show all conclusions at one Q.
Findings: (1) 4 of 18 terms (lanlwD, lw4 tail, gg2 AD, gg4 BD) are detours: `ext` holds at only 81% / 84% / 55% / 55% of the strict terms; they need the `thr` step (BA twin of LR2:381) as a new generic lemma (≈ 100 lines, in the estimate) — it is not in the merged `BALocReg1`; the other 14 terms and I1, I2 are `ext` at every term. (2) The A2 mirror (T2456 1a) does not arise on the `ext` route. (3) trA, trB need no `diag-swap` lemma (hcov(Bm) holds at every term: the new loop and the consumed edge have the same molecule pair). (4) Conj (a) `3p ≤ ord` has slack 0 at the instance.
### Verdict per target
1 (a) PASS; 1 (b) PASS; 1 (c) PASS; 1 (d) PASS; 2 PASS; 3 (a) PASS; 3 (b) PASS; 3 (c) PASS; 4 PASS (mathematics: 0 violations, routes close, witnesses exist). Row-level fit: **BLOCKED** on the §227 split rule (central 2,130 > 1,575): the dispatcher's sign-off before 1b (H183 (3)) is the missing input; proposed split at `BALocReg2 | BALocReg2B` as above (no other split, no new row).

## (a′) Preflight corrections — Mon Oct 12 21:42:14 UTC 2026
One route statement of (a) is corrected; no verdict changes. Table (a), column "route", and finding (1) (4 of 18 terms need a new generic `thr` variant of `BALocReg1_pathAt_map`, about 100 lines) and
the file-1 estimate 1,240 lines (row 8, (c)): in Lean all 18 terms close with the band's own replacement lemmas `localReg2_VRepl.same` (14 terms) and `localReg2_VRepl.deriv` (`lanlwD`, `lw4` tail, `AD`, `BD`;
LR2:852 → `localReg2_Fam.repl_deriv` LR2:549 → `thr` LR2:381), read at the vertex map `owxEmb n` of the extension. No `thr` variant was written; file 1 has the line count shown below.

## (b) Script output — stage 1b, L3b2a (target 1 (a)) — Mon Oct 12 21:42:14 UTC 2026
Scripts: `scratchpad/T2469/` (`table.py`, `stmt.py`, `parity.py`, `unused.py`, `axsum.sh`, `clash.sh`, `mlnames.lean`). Commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2469`.
```
$ git log --oneline -5; git diff --stat main...t/T2469; wc -l RBM3D/Graph/BALocReg2.lean
ff8a75b9 T2469 (L3b2a): BALocReg2 docstring corrections (A2 selector, contents)
68754f7c T2469 (L3b2a): BALocReg2 nondegeneracy check of the instance data
604645c3 T2469 (L3b2a): BALocReg2 instances with the invariant at P_A, P_B and a weight witness (section 6)
0da9b88e T2469 (L3b2a): BALocReg2 GG, ggSplit terms, term lists, instances (sections 3-6)
0fe08703 T2469 (L3b2a): BALocReg2 tools and the weight terms (section 1-2)
 RBM3D/Graph/BALocReg2.lean | 886 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 886 insertions(+)
     886 RBM3D/Graph/BALocReg2.lean
```
Lines against the stop line: file 1 = 886 lines (stop line 2,000; reserve `BALocReg2C` only above 1,800: not used; preflight estimate for file 1: 1,240).
```
$ lake build RBM3D.Graph.BALocReg2 2>&1 | tail -2
modifies the current goal, which was modified by the flexible tactic `simp` on line 473!
Build completed successfully (3829 jobs).
```
(The first line is the tail of a replayed warning of `RBM3D/BA/CouplingWindow.lean`, not of the new file. The uncached build of the final content printed, in the tool log: `✔ [3829/3829] Built RBM3D.Graph.BALocReg2 (5.3s)`; `lake env lean RBM3D/Graph/BALocReg2.lean` prints no linter output.)
```
$ lake build RBM3D   # at ff8a75b9 with `import RBM3D.Graph.BALocReg2` added to RBM3D.lean locally (reverted by `git checkout RBM3D.lean`, not committed); log lines
5398:info: RBM3D.lean:535:0: axiom audit: 13637 theorems, 4347 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
5637:Build completed successfully (4303 jobs).
5638:exit 0
```
```
$ #print axioms of every public declaration of the file (3 in `BALocReg2Inst`) — grouped
34 declarations with axioms [propext, Classical.choice, Quot.sound]
 4 declarations with axioms [none]: BALocReg2_cends_bpS BALocReg2_bpS_σ BALocReg2_bpS_src BALocReg2_bpS_dst
 1 declarations with axioms [propext, Quot.sound]: BALocReg2_cov
```
```
$ grep -nE 'sorry|admit|native_decide|^axiom|^inductive|^structure|: Prop' RBM3D/Graph/BALocReg2.lean; echo "grep exit=$?"
grep exit=1
```
Term table as proved (`python3 table.py`; lines = theorem statement and proof; wrapper `ext2`/`ext4` = `BALocReg2_pathAt_ext2`/`_ext4`; route = the band replacement lemma used):
```
$ python3 table.py
term lemma | lines | wrapper | VRepl route | band twin (ticket pairing)
lw2Head     | 272-293 (22) | ext2 | same | owxT1
lanlwD      | 296-315 (20) | ext2 | deriv | oe1xD
lw4Head     | 317-336 (20) | ext4 | same | owxT2
lw4Tail     | 339-359 (21) | ext4 | deriv | owxT4
withinHead  | 361-380 (20) | ext2 | same | oe1xOwx
ggA1        | 391-408 (18) | ext2 | same | (stage 2 only)
ggA2        | 411-428 (18) | ext2 | same | R2
ggA3        | 430-447 (18) | ext2 | same | R2
ggA4        | 449-466 (18) | ext2 | same | R3
ggA5        | 468-485 (18) | ext2 | same | R5
ggAD        | 487-505 (19) | ext2 | deriv | R7
ggB1        | 507-524 (18) | ext4 | same | R4
ggB2        | 526-543 (18) | ext4 | same | R6
ggBD        | 545-563 (19) | ext4 | deriv | R8
ggSplitD1   | 573-594 (22) | ext2 | same | R5 at a
ggSplitD2   | 596-616 (21) | ext2 | same | R2
ggSplitD3   | 618-638 (21) | ext2 | same | R2
ggSplitD4   | 640-660 (21) | ext2 | same | R2 twice
```
Statements of the five list forms (extracted by `stmt.py`; the consumers of file 2 read these):
```
$ python3 stmt.py BALocReg2_lw2 BALocReg2_lw4 BALocReg2_within BALocReg2_gg2 BALocReg2_gg4
theorem BALocReg2_lw2 (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) : ∀ X ∈ Γ.lw2 p, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b
theorem BALocReg2_lw4 (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) : ∀ X ∈ Γ.lw4 p, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b
theorem BALocReg2_within (Γ : BAGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true) (hsame : Γ.sameAtom p.1.src p.1.dst = true) : ∀ X ∈ BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] :: (lwSplit p.2).map (BAGraph.lanlwD Γ p), ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b
theorem BALocReg2_gg2 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src) (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) : ∀ X ∈ Γ.gg2 p q, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b
theorem BALocReg2_gg4 (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ = true ∧ p.1.circ = true) (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src) (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) (hint : Γ.intAtom p.1.src = true) : ∀ X ∈ Γ.gg4 p q, ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b
```
Statement parity with the cost twins (`BAShapeO2_*`, `BAScostLL_S1`; same binders, only the conclusion `BAScostLL Γ X` is replaced by `∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b`):
```
$ python3 parity.py | tail -1   # compares the binder lists of 23 pairs
23 of 23 pairs have identical hypothesis binders
```
Hypotheses of the cost twins that the path lemmas do not use (linter `unusedVariables` on a copy of the file):
```
$ SP=... python3 unused_group.py
unused [hN]: lanlwD lw4Tail
unused [hsame]: withinHead
unused [hwf1 hwf2]: ggA1 ggA2 ggA3 ggA4
unused [hint hwf1 hwf2]: ggA5 ggB1 ggB2 ggSplitD1
unused [hN hint hwf1 hwf2]: ggAD ggBD
unused [hsame hwf1 hwf2]: ggSplitD2 ggSplitD3 ggSplitD4
```
Compiled nonempty instances (section 6 of the file starts at line 736; `example`s and the three families `BALocReg2Inst.pathInv2_A/_B/_L`):
```
$ grep -nE '^example|^theorem pathInv2|^def baPL|^def pL' RBM3D/Graph/BALocReg2.lean | cut -c1-175
742:example : (∀ X ∈ baPW.lw2 pW, ∀ (k : ℕ) (a b : Fin 1), BALocReg1_PathAt baPW k a b → BALocReg1_PathAt X k a b) ∧
747:example : ∀ X ∈ BAGraph.ext 2 baPB pB.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 pB.1.dst)] [bpW false (bpv 0) (bpv 1)]
753:example : (∀ X ∈ baPA.gg2 pA qA, ∀ (k : ℕ) (a b : Fin 2), BALocReg1_PathAt baPA k a b → BALocReg1_PathAt X k a b) ∧
760:example : BALocReg1_PathAt (BAGraph.ext 2 baPC qC.2 [bpS false (owxEmb 2 qC.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 qC.1.dst), bpS false (bpv 1) (owxEmb 2 pC.1.dst)]
777:example : ∀ q ∈ lwSplit BALocReg1Inst.pEr.2, BALocReg1_PathAt (BAGraph.lanlwD BALocReg1Inst.baPEr BALocReg1Inst.pEr q) 1 0 1 :=
785:theorem pathInv2_A : (baPG baPA).img.PathInv2 2 := by
804:theorem pathInv2_B : (baPG baPB).img.PathInv2 1 := by
830:def baPL : BAGraph (Fin 2) (Fin 1) :=
833:def pL : SEdge (Fin 2 ⊕ Fin 1) × List (SEdge (Fin 2 ⊕ Fin 1)) :=
837:theorem pathInv2_L : (baPG baPL).img.PathInv2 1 := by
862:example : (∀ X ∈ BALocReg2Inst.baPL.lw2 BALocReg2Inst.pL, BALocReg1_PathAt X 1 0 1) ∧ (∀ X ∈ BALocReg2Inst.baPL.lw4 BALocReg2Inst.pL, BALocReg1_PathAt X 1 0 1) :=
867:example : ∀ X ∈ BAGraph.ext 2 baPB pB.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 pB.1.dst)] [bpW false (bpv 0) (bpv 1)]
872:example : (∀ X ∈ baPA.gg2 pA qA, BALocReg1_PathAt X 2 0 1) ∧ (∀ X ∈ baPA.gg4 pA qA, BALocReg1_PathAt X 2 0 1) :=
879:example : (baPA.gg2 pA qA).length = 6 ∧ (baPA.gg4 pA qA).length = 3 ∧ (BALocReg2Inst.baPL.lw2 BALocReg2Inst.pL).length = 3 ∧
```
```
$ clash.sh   # name-clash grep of the new names on main and on all t/* branches
new public theorems BALocReg2_*: 36; in namespace BALocReg2Inst: pathInv2_A, pathInv2_B, pathInv2_L, baPL, pL
git grep -c 'BALocReg2' on main in RBM3D/*.lean and RBM3D.lean: 0
t/* branches other than t/T2469 scanned: 473, total hits: 0
files other than Graph/BALocReg2.lean in the T2469 worktree mentioning BALocReg2: 0
```
```
$ lake env lean mlnames.lean | grep -c error; grep -c '^#check' mlnames.lean   # errors, names checked
0
46
```

Narrative.
1. Scope: this run is L3b2a (CONTROL H257 (3)): target 1 (a), file `RBM3D/Graph/BALocReg2.lean` only. Targets 1 (b)-(d), 2, 3, 4, the `T2469_*` pins and `BALocReg2B` are L3b2b and untouched. `RBM3D.lean` is not edited on the branch (the hub adds
   `import RBM3D.Graph.BALocReg2` after the last import line at merge); the full-library lines above come from a local edit that was reverted.
2. Stop rule (CONTROL H134): `wc -l` at the five section commits 0fe08703, 0da9b88e, 604645c3, 68754f7c, ff8a75b9 gave 388, 783, 882, 886, 886 lines; the stop line is 2,000.
3. Proved: 18 term lemmas (the 17 builder terms of `T2447-prove.md:9-28` and `A1` of `gg2`) and the five list forms `BALocReg2_lw2`, `_lw4`, `_within`, `_gg2`, `_gg4`, with the binders of the cost twins and the conclusion
   `∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b`. The Lean statements hold for every `k`, `a`, `b`, `Γ`; the preflight numerics (a) row 7 (0 violations in 44,116,876 term-level checks) were not rerun.
4. Route: `BALocReg2_pathAt_map_fam` is the first half of the merged `BALocReg1_pathAt_map` (`BALocReg1.lean:89-132` at ad52b370, same project; no port from `../RBM1D`, `../RBM2D`): the family of `Γ` read in the molecules of the
   extension through `owxEmb n` (LR2:616), with no budget moved. `BALocReg2_pathAt_ext` then needs only a replacement `localReg2_VRepl` of the selected edges `sel` (`Γ.solid ~ sel ++ rest`) by the new edges `S`, read in the molecules. `_ext2` (one waved edge
   `α ~ β`, an `M`-edge `x ~ α`) and `_ext4` (waved `0 ~ 1`, `2 ~ 3`, `M`-edges `x ~ 0`, `0 ~ x`, `1 ~ 2`) pass the molecule identifications to the replacement, so a term proof holds no graph expression: it names `D₁ A A' D₂` of `localReg2_VRepl.same` / `.deriv`.
5. Molecule identifications come from the `M`-dotted and waved edges of the extension (`BALocReg2_mu_md`, `_mu_wav`); only `d1` uses the atom relation of `Γ` (`hsame`, `BALocReg2_mu_atom`). Every colour-presence clause of `same`/`deriv` is covered by an edge of the selected
   edges (`BALocReg2_cov`), none by the rest of the graph.
6. The path lemmas need fewer hypotheses than the cost twins (table above): `hN` is not used by the 4 term lemmas that carry it (`lanlwD`, `lw4` tail, `AD`, `BD`), `hwf1`, `hwf2` are not used by the 13 `gg`/`ggSplit` terms, `hint` by 6, `hsame` by 4. They stay in the signatures so that file 2 calls the lists with the arguments of
   `BAShapeO2_lw2` etc. (`BAShapeO2B:169, 204`), at `tr` as at `P.g`.
7. Instances: the premise `BALocReg1_PathAt Γ k a b` is satisfied, not assumed, at `P_C` (k = 2: `d1`-`d4`, `lanlwD`; `BALocReg1Inst.pathInv2_C`), `baPEr` (k = 1: `lanlwD`), `P_B` (k = 1: the `within` list), `P_A` (k = 2: `gg2`, `gg4` lists) and `baPL` (k = 1: `lw2`,
   `lw4` lists). The families for `P_A`, `P_B`, `baPL` are new (`BALocReg2Inst.pathInv2_A/_B/_L`, moved along `BALocReg1_pathAt_map` from `LCr`, `baPEr`); the data `baPL`, `pL` are instance defs. `P_W` is used for the constructor hypotheses only. The list lengths of the
   data are checked by `decide` (6, 3, 3, 3, 2).

## (c) Verified Mathlib names used
Every name below elaborates under `#check @name` in `scratchpad/T2469/mlnames.lean` (46 names, 0 errors, see (b)); names verified absent: none (no name was tried and dropped).
- `Finset`: `mem_singleton`
- `Function`: `surjInv`, `surjInv_eq`
- `List.Perm`: `of_eq`
- `List`: `append_nil`, `map_append`, `map_congr_left`, `map_cons`, `map_map`, `map_nil`, `mem_append`, `mem_append_left`, `mem_cons`, `mem_cons_self`, `mem_map`, `mem_singleton`, `not_mem_nil`, `perm_append_singleton`
- `Matrix`: `cons_val_one`, `cons_val_zero`
- `Multiset`: `coe_add`, `coe_eq_coe`, `coe_nil`, `cons_coe`, `insert_eq_cons`, `map_add`, `map_coe`, `map_cons`, `map_singleton`, `map_zero`, `mem_cons`, `mem_singleton`, `singleton_add`
- `Prod`: `map_apply`
- `Relation.ReflTransGen`: `refl`
- `SimpleGraph.ConnectedComponent`: `eq`
- `Sum`: `inl`, `inr`, `map`, `map_inl`, `map_inr`
- `Sym2`: `eq_swap`, `map`, `map_mk`, `mem_iff`, `mk_isDiag_iff`

## (d) Open issues and paper-delta candidates
No open issue blocks L3b2a. For the L3b2b ticket (dispatcher): target 4 (i) and (iii) ask for hand-built families at `P_B` (k = 1) and `P_A` (k = 2); they are `BALocReg2Inst.pathInv2_B` and `pathInv2_A` in file 1 (public), and (ii) is `BALocReg1Inst.pathInv2_C`.
- `T2469a` (paper `B_graphical_lemmas.tex:416`, "all path properties stated in `lem:localregular` continue to hold" for the block Anderson model, no per-term argument): Lean proves the path invariant `PathInv2` for each of the 18 builder terms at the atomic image, each as one replacement of the selected edges in the
  molecular multigraph (14 `localReg2_VRepl.same`, 4 `.deriv`); `A1` and `d4` (both selected edges become loops) have no single band term. The BA-only shapes `e2`, `macroA`, `macroB` themselves (composition, stage 2) are L3b2b.
- `T2469b` (hypotheses): the well-formedness `hwf1`, `hwf2`, the internal atom `hint`, `hsame` (in `within`, `d2`-`d4`) and `Γ.Normal` that the cost lemmas of (6) carry are not used by the path lemmas where the table above lists them: the path property of those terms holds without them.
- `T2469c` (the A2 mirror, `BASim:196-198`): not needed for the path property; `BALocReg2_ggA2` is proved at the selector `(p, q)` itself with the binders of `BAShapeO2_ggA2`.
