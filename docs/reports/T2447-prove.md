Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 10:45:43 UTC 2026
Setting: C1, combinatorial. The targets are `BAShapeLL sh BAFrameStepTN` (sh = e2, macroA, macroB) and the conclusion of `BALocReg6` without its binder; there is no analytic exponent and no external hypothesis (no limit computation). Python only, no Lean (`$SP` = scratchpad `T2447/`; cost model `phi.py`/`sll.py` copied from T2426's scratchpad: `scostA = (promoteC Γ).scost`, atoms, the genuine `BAScostLL`: every merge s ≥ atoms(X) has s₀ ≥ atoms(Γ) separating the external pairs s separates with scostA Γ s₀ ≤ scostA X s).
Notation: [x] = atom; hwf p,q = `sameAtom p.src p.dst = false`, `sameAtom q.src q.dst = false`; psi1 = `BAScost_psi1` (BAScost:917); psi2 = new 4-vertex map (z/u ↦ [x]; y,α / w,α ↦ a; β ↦ b); vmap.rho2 = `(promoteC Γ).vmap ∘ BAScost_rho2` (BAScost:805, as `BAScostLL_S1`).
### (i) Exponent table (no exponent: the rows are the 17 builder terms of O2R-C2 (a), with the slack of (b) per term; the last column is `BAScostLL Γ X` pre-partition)
Commands: `drive47.py N SEED NE MODE` ×5 (NE=2 gen 1e5, NE=2 strict 2e5, NE=3 gen 4e4, NE=3 strict 1e5, NE=4 gen 8e3: random normal parents, all shapes of p,q; MODE strict adds hwf, hint, hnb), `img47.py N SEED NE hp` ×3 (2e5, 1e5, 4e4), then:
```
$ cd $SP && python3 table47.py
# | term | ctor; tag | band image: primitive/lemma; map | hypotheses used | image=band (inst/mismatch) | BAScostLL G X (checks/viol/min slack/slack-0)
 1 | lanlwD | lw2/within/edge/ggSplit tail; e2 | Dmove([x]->[y];q): `scostLL_dmove`, cp=decide([x]=[y]); psi1 at x | p sigma,circ; Normal | 510,269/0 | 673,706/0/0/292,209
 2 | lw2 head | weight; e2 | T1=Loop([x]): `scostLL_loop`/`localReg6d_ll_T1`; psi1 at x (or E1 + solid swap) | p sigma,circ,src=dst | 340,000/0 | 448,000/0/2/0
 3 | lw4 head | weight; e2 | T2=MoveLoop+Loop: `localReg6d_ll_T2`; psi2 (new, 4 vertices) | p sigma,circ,src=dst | 340,000/0 | 448,000/0/2/0
 4 | lw4 tail | weight; e2 | T4=MoveLoop+Dmove: `localReg6d_ll_T4`; psi2 | p sigma,circ,src=dst; Normal | 510,269/0 | 673,706/0/0/27,263
 5 | within head | within; e2 | =(lanlwT1 G p).splitG[0] (text): `BAScostLL_E1`; no band lemma | p sigma,circ; Normal | 340,000/0 | 448,000/0/2/0
 6 | gg2 A2 | gg; e2 | R2=Contract([x];[y'],[y]): `scostLL_contract`; vmap.rho2 (al->[x],be->[y']) | hwf p,q | 189,349/0 | 157,519/0/0/14,982
 7 | gg2 A3 | gg; e2 | R2: `scostLL_contract`; vmap.rho2 (al->[x],be->[y]) | hwf p,q | 189,349/0 | 157,519/0/0/14,982
 8 | gg2 A4 | gg; e2 | R3=Loop([x]), p,q kept: `scostLL_loop`; psi1 at x | hwf p | 189,349/0 | 157,519/0/0/26
 9 | gg2 A5 | gg; e2 | R5=MoveSC+AddLoop: `localReg6d_ll_R5`; psi1 at x | hwf p,q; hint | 189,349/0 | 157,519/0/0/40
10 | gg2 AD | gg; e2 | R7=Dmove([x]->[y];r): `localReg6d_ll_R7`; psi1 at x | hwf p,q; hint; Normal | 283,972/0 | 225,168/0/0/95,685
11 | gg4 B1 | gg; e2 | R4=MoveSC+Loop: `localReg6d_ll_R4`; psi2 | hwf p,q; hint | 189,349/0 | 157,519/0/2/0
12 | gg4 B2 | gg; e2 | R6=Loop+MoveSC: `localReg6d_ll_R6`; psi2 | hwf p,q; hint | 189,349/0 | 157,519/0/2/0
13 | gg4 BD | gg; e2 | R8=MoveSC+Dmove: `localReg6d_ll_R8`; psi2 | hwf p,q; hint; Normal | 283,972/0 | 225,168/0/0/5,579
14 | ggSplit d1 | ggSplit; e2 | R5 at x:=[a]: `localReg6d_ll_R5`; psi1 at a | hsame; hwf p,q; hint a | 53,442/0 | 61,685/0/0/16
15 | ggSplit d2 | ggSplit; macroB | R2=Contract([a];[y'],[y]): `scostLL_contract`; vmap.rho2 (al->[a],be->[y]) | hsame; hwf p,q | 53,442/0 | 61,685/0/0/4,690
16 | ggSplit d3 | ggSplit; macroB | R2: `scostLL_contract`; vmap.rho2 (al->[a],be->[y']) | hsame; hwf p,q | 53,442/0 | 61,685/0/0/4,690
17 | ggSplit d4 | ggSplit; macroB | Contract + [y']~[y] as `BAScostLL_S1`: `scostLL_contract`; vmap.rho2 (al->[a],be->[y]) | hsame; hwf p,q | 53,442/0 | 61,685/0/0/33,012
sum of the 17 rows: checks 4,333,602, violations 0
```
Last column = checks / violations / minimum per-merge slack / checks with slack 0 (`p`, `q` as in the constructor; x external allowed for lanlwD, lw2, lw4). The `image=band` column: the atomic image of X equals the named band term applied to the image of Γ, up to relabelling of the fresh atoms and extra circled loops (Lemma A), same waved count (`img47.py`).
Findings on routes: (1) `localReg6c_inst_D` (x : I, `inr x ≠ v`) does not cover lanlwD at an external or same-atom x (the `weight`, `within` constructors do not exclude them): use `scostLL_dmove` (6c:1431), cp := decide([x]=[y]), which gives the cp = true/false split in one proof; likewise the (x : I) forms R4–R8 need `hint`, or use the primitives. (2) `within` head = `(lanlwT1 Γ p).splitG[0]` literally (text check below), so `BAScostLL_E1` covers it; `lw2` head has the two solid edges in the other order (E1 + a solid permutation, or `localReg6d_ll_T1`). (3) R2 is `scostLL_contract`: rows 6, 7, 15–17 share it with `BAScostLL_S1`. (4) A4 = R3 needs hwf p (the image of p must be uncircled): `python3 img47.py 2000 7 2 gen` gives 1081/2000 image mismatches for A4 and 0 for the other 16 rows; with hwf p (MODE hp) 0.
```
$ cd $SP && python3 agg47.py | tail -7        # stage 2 and the merged macro lemmas, same runs
macroA lemma BAScostLL G trA                 checks   448,000  violations 0  min slack 0  slack-0 checks   10,335
macroB lemma BAScostLL G trB                 checks    61,685  violations 0  min slack 0  slack-0 checks   34,156
macroA stage 2 X' in tr.lw2/lw4 pp: BAScostLL G X' checks 2,243,412  violations 0  min slack 0  slack-0 checks    4,888
macroA stage 2 X' in tr.lw2/lw4 pp: BAScostLL tr X' checks 2,243,412  violations 0  min slack 0  slack-0 checks  675,582
macroB stage 2 X' in tr.gg2/gg4 p' q': BAScostLL G X' checks   607,017  violations 0  min slack 0  slack-0 checks   44,320
macroB stage 2 X' in tr.gg2/gg4 p' q': BAScostLL tr X' checks   607,017  violations 0  min slack 0  slack-0 checks  153,761
ALL (17 terms + extras + stage 2)            checks 11,375,370  violations 0  min slack 0  slack-0 checks 1,841,791
$ python3 mutant47.py | grep -E '^  d[24]'   # control: the checker detects a wrong term
  d4 genuine                               checks  1184  with violation 0
  d4 mutant (waved edge dropped)           checks  1184  with violation 831
  d2 genuine                               checks  1184  with violation 0
  d2 mutant (waved edge dropped)           checks  1184  with violation 1075
```
**Stage 2, (c).** `P.outsT (fun _ => .macroA) (tr.lw2 pp)` (and `tr.lw4 pp`; `.macroB` with `tr.gg2 p' q'`, `tr.gg4 p' q'`) consists of `BAScost_pack P Q0` with `Q0 ∈ X.partition`, X a term of that list (`BASim_mem_outsT`). `tr` is `BAScost_trA`/`_trB` letter for letter; every solid edge of `tr` is circled, so `tr.splitG = [tr]`. Route (α) asks `locCostGeA far k (BAScost_pack P tr.packMerge) → locCostGeA far k Q`, a step lemma at the packed graph `BAScost_pack P tr.packMerge` (its graph is `tr.merge`, `packMerge` has `g := Γ.merge`), i.e. the band step there (ticket target 6). **Route (β) needs neither and the numerics close it:** `BAScostLL P.g X = (BAScostLL_macroA/_macroB P.g …).trans (target 5 at Γ := tr)`, then `baShapeLL_of_terms` for macroA (`baShapeLL_macroA` has only the (α) form) and disjunct 2 of `baShapeLL_macroB` for macroB; stage 1 of macroB (d2–d4) is disjunct 2 with X := d_i, `BAScostLL P.g d_i` from rows 15–17. Hypotheses of the lemmas at `tr` (lines below): weight: `pp ∈ lwSplit tr.solid`, e a blue circled loop at β; gg: `p' ∈ lwSplit tr.solid`, `q' ∈ lwSplit p'.2`, `p'.src = q'.dst = β` internal, hwf p',q' (β is a singleton atom), hint β; hnb is not used by any of the 17 lemmas (verified for `tr` anyway).
```
$ cd $SP && python3 check47c.py; python3 tr_text47.py
  trA: 120,000 instances, 2 properties, failures 0: (e, rest) in lwSplit tr.solid, e blue circled loop at beta; all solid edges circled
  trB:   1,870 instances, 6 properties, failures 0: all solid edges circled; hint at tr; hnb at tr; hwf at tr; p' in lwSplit tr.solid, q' in lwSplit p'.2; p'.src = q'.dst = beta, p', q' blue circled
trA  BASim withinOutsT == BAScost_trA: True
trB  BASim splitOutsT == BAScost_trB: True
within head solid [e, bpS true (bpv 0) dst] vs lanlwT1 solid [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) dst]: same list up to the circle flag of the 2nd edge: True
gg pair of stage 2: True ; weight pair: True
```
**(d) No hidden input.** The hypotheses used per term are the table's `hypotheses` column: the constructor's (σ, circ, shape of p,q, hsame, hwf, hint) and `Γ.Normal` (CircIffLoop of the image edges via `BAGraph.img_normal`, and 'rest circled' for the `within` head). None uses hnb, `LocStd`, the invariants (1)–(5) or the cutoff. The MODE gen runs (shape of p,q only: no hwf, hint, hnb) have 0 violations too.
### (ii) One concrete nondegenerate instance (R1 witnesses baPA, baPB, baPC: E = Fin 2, I = Fin 3, 5 vertices, all solid edges circled and blue, no =-dot)
```
$ cd $SP && python3 lit47.py | grep '==' ; python3 lit47b.py   # Lean literals == python data; gc = baPC (instance (iii))
gc == baPC: True
pc == pC : True
qc == qC : True
Lean literal == python data (solid, waved count, mdot): {'baPA': (True, True, True), 'baPB': (True, True, True), 'baPC': (True, True, True), 'baPW': (True, True, True), 'baPE': (True, True, True), 'gs': (True, True, True)} ; differs only in M-dot orientation (same atoms): ['gw']
$ python3 inst47.py          # tag census of the steps (BASim.lean:113-136) against the compiled `decide +kernel` counts BASim3.lean:1910-1913
P_A gg   : 31 {'e2': 8, 'band': 23} (BASim3.lean:1910: 31 = 23 band + 8 e2)
P_C split: 48 {'band': 8, 'e1': 1, 'e2': 5, 'macroB': 34} (BASim3.lean:1911-1913: 48 = 8 band + 1 e1 + 5 e2 + 34 macroB)
P_B within: 51 {'band': 14, 'e2': 3, 'macroA': 34} (e2 and macroA outputs are asked by target 7 (i))
$ python3 inst2_47.py        # BAShapeLL's statement Phi(Q) >= Phi(P) at each witness step; only constructors whose hypotheses hold fire
baPA     step ['gg']  Phi(P) all/far 0/2: e2 8 (viol all/far 0/0, min dPhi all/far 1/1)
baPB=gw  step ['within']  Phi(P) all/far 1/1: e2 3 (viol all/far 0/0, min dPhi all/far 2/2); macroA 34 (viol all/far 0/0, min dPhi all/far 3/3)
baPC=gc  step ['ggSplit']  Phi(P) all/far 0/2: e2 5 (viol all/far 0/0, min dPhi all/far 3/1); macroB 34 (viol all/far 0/0, min dPhi all/far 0/0)
$ python3 witness47.py --summary   # BAScostLL P.g X at the real p, q: all builder terms of the step, baPB/baPC also at tr (stage 2)
  baPA     terms   9  merges checked    800  violations 0  min per-merge slack 0  terms at slack 0: 4
  baPB     terms  10  merges checked   3448  violations 0  min per-merge slack 1  terms at slack 0: 0
  baPB tr  terms   6  merges checked   3240  violations 0  min per-merge slack 2  terms at slack 0: 0
  baPC     terms  15  merges checked   3550  violations 0  min per-merge slack 0  terms at slack 0: 8
  baPC tr  terms   9  merges checked   3359  violations 0  min per-merge slack 0  terms at slack 0: 4
  baPW     terms   4  merges checked    134  violations 0  min per-merge slack 2  terms at slack 0: 0
  baPE     terms   3  merges checked     45  violations 0  min per-merge slack 0  terms at slack 0: 1
  gs       terms   7  merges checked    146  violations 0  min per-merge slack 0  terms at slack 0: 3
$ python3 binit.py | grep '^p=2'; python3 step47b.py 3 400 | grep -E '^depth 2|^outputs|^  e2|^  macroB'   # target 4: the 16 start terms of p = 2; then 20 graphs reached after 2 steps to which ggSplit applies
p=2: terms 16 (2^(2p)=16), min Phi^all 4 (2p=4), min Phi^far 6 (3p=6), terms with atoms of x,y equal 7, BAScostLL(Gamma_p, Q) violations 0, min slack 0
depth 2: 6590 outputs; ggSplit applicable at 617
outputs by (constructor, tag): {'gg/band': 140, 'gg/e2': 18, 'ggSplit/band': 414, 'ggSplit/e1': 22, 'ggSplit/e2': 120, 'ggSplit/macroB': 1244}
  e2      outputs    138  violations all/far 0/0  min (Phi(Q)-Phi(P)) all/far 1/1
  macroB  outputs   1244  violations all/far 0/0  min (Phi(Q)-Phi(P)) all/far 0/0
```
Instance data: (i) `within` at baPB (p = 2→3, atom {2,3}): 3 e2 + 34 macroA outputs; (ii) `ggSplit` at baPC, j = 0 (a = 2 ≠ a' = 3, one atom; hwf, hint, hnb hold): 5 e2 + 34 macroB; (iii) gc = baPC, pc = pC, qc = qC literally (`rfl` for 1b to confirm); (iv) `gg` at baPA: 8 e2; (v) p = 2: Φ^all ≥ 4 = 2p, Φ^far ≥ 6 = 3p at all 16 start terms (slack 0), so locReg6InvA 2 holds, and the e2/macroB outputs one and two steps on satisfy BAShapeLL's statement.
**Verdict (O2R-C2 stop rule not triggered: (b) 0 violations in 11,375,370 term checks, (c) and (d) hold).** Target 1 `baShapeLL_e2_tn`: PASS. Target 2 `baShapeLL_macroA_tn`: PASS (route β). Target 3 `baShapeLL_macroB_tn`: PASS (route β). Target 4 `baLocReg6_holds`: PASS (`baLocReg6_reach` with 1–3). Target 5 (17 builder lemmas): PASS, routes as in the table. Target 6 (stage 2): PASS, route (β). Target 7 (instances (i)–(v)): PASS. Dispatcher readings confirmed: `within` head, `tr` letter for letter, `tr.splitG = [tr]`, pp/qq ∈ lwSplit, (iii) gc = baPC; open choice (1): (β); (2): gc = baPC; (3): E1 for `within`, E1 + solid swap or T1 for `lw2`. Item (e) of the ticket (predicted lines) is not part of section (a) (CLAUDE.md §4 step 1: no size estimates).

## (a′) Preflight corrections — Mon Oct 12 11:23:21 UTC 2026
None. No statement of (a) is contradicted by the files. Two route choices differ from the open choices of (a), not corrections: the `within` head is proved by `scostLL_loop` directly (as the `lw2` head), not through `BAScostLL_E1` (open choice (3)); stage 2 is route (β), the recommendation of (a).

## (b) Script output (stage 1b, ticket role `prover-hard`, model claude-sonnet-5-5; written Mon Oct 12 11:23:21 UTC 2026)
### Line counts against the stop line; the table of (a) as finally proved
```
$ wc -l RBM3D/Graph/BAShapeO2.lean RBM3D/Graph/BAShapeO2B.lean; echo "stop line 2000 per file"
    1094 RBM3D/Graph/BAShapeO2.lean
     447 RBM3D/Graph/BAShapeO2B.lean
    1541 total
stop line 2000 per file
$ grep -n "^/-! ##" RBM3D/Graph/BAShapeO2.lean RBM3D/Graph/BAShapeO2B.lean | sed "s/RBM3D.Graph.//" | cut -c1-110
BAShapeO2.lean:50:/-! ## 1. Tools -/
BAShapeO2.lean:115:/-! ### The four-vertex map -/
BAShapeO2.lean:304:/-! ## 2. The weight terms -/
BAShapeO2.lean:507:/-! ## 3. The `GGGamma` terms -/
BAShapeO2.lean:855:/-! ## 4. The `ggSplit` terms -/
BAShapeO2.lean:983:/-! ## 5. The term lists -/
BAShapeO2.lean:1053:/-! ## 6. Nonempty instances: the term lemmas at the R1 witnesses (`BASim3:1877-1905`), ev
BAShapeO2B.lean:40:/-! ## 1. Outputs and tags -/
BAShapeO2B.lean:73:/-! ## 2. Stage 2 -/
BAShapeO2B.lean:209:/-! ## 3. Targets 1-3: the shapes `e2`, `macroA`, `macroB` of `BAFrameStepTN` -/
BAShapeO2B.lean:346:/-! ## 4. Target 4: (6) along `BAReach` with no hypothesis -/
BAShapeO2B.lean:361:/-! ## 5. Nonempty instances (target 7) -/
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2447/table_final.py
# | term | constructor | tag | route (band lemma; map) | lemma (BAShapeO2.lean) | lines
 1 | lanlwD | lw2/within/edge/ggSplit tail | e2 | Dmove([x]->[y];q): scostLL_dmove, cp=([x]=[y]); psi1 | BAShapeO2_lanlwD | 34
 2 | lw2 head | weight | e2 | Loop([x]): scostLL_loop (hperm: Gamma.solid ~ p::rest); psi1 | BAShapeO2_lw2Head | 37
 3 | lw4 head | weight | e2 | T2 = MoveLoop+Loop: localReg6d_ll_T2; psi2 | BAShapeO2_lw4Head | 38
 4 | lw4 tail | weight | e2 | T4 = MoveLoop+Dmove: localReg6d_ll_T4; psi2 | BAShapeO2_lw4Tail | 36
 5 | within head | within | e2 | Loop([x]): scostLL_loop (not BAScostLL_E1); psi1 | BAShapeO2_withinHead | 37
 6 | gg2 A2 | gg | e2 | Contract([x];[yp],[y]): scostLL_contract; vmap.rho2 x y | BAShapeO2_ggA2 | 23
 7 | gg2 A3 | gg | e2 | Contract: scostLL_contract; vmap.rho2 x y | BAShapeO2_ggA3 | 23
 8 | gg2 A4 | gg | e2 | Loop([x]), p,q kept: scostLL_loop; psi1 | BAShapeO2_ggA4 | 39
 9 | gg2 A5 | gg | e2 | R5 = MoveSC+AddLoop: localReg6d_ll_R5; psi1 | BAShapeO2_ggA5 | 42
10 | gg2 AD | gg | e2 | R7 = Dmove: localReg6d_ll_R7; psi1 | BAShapeO2_ggAD | 43
11 | gg4 B1 | gg | e2 | R4 = MoveSC+Loop: localReg6d_ll_R4; psi2 | BAShapeO2_ggB1 | 46
12 | gg4 B2 | gg | e2 | R6 = Loop+MoveSC: localReg6d_ll_R6; psi2 | BAShapeO2_ggB2 | 45
13 | gg4 BD | gg | e2 | R8 = MoveSC+Dmove: localReg6d_ll_R8; psi2 | BAShapeO2_ggBD | 44
14 | ggSplit d1 | ggSplit | e2 | R5 at x:=[a]: localReg6d_ll_R5; psi1 | BAShapeO2_ggSplitD1 | 46
15 | ggSplit d2 | ggSplit | macroB | Contract([a];[yp],[y]): scostLL_contract; rho2 a y | BAShapeO2_ggSplitD2 | 21
16 | ggSplit d3 | ggSplit | macroB | Contract: scostLL_contract; rho2 a yp | BAShapeO2_ggSplitD3 | 21
17 | ggSplit d4 | ggSplit | macroB | Contract, edge dropped (as BAScostLL_S1); rho2 a y | BAShapeO2_ggSplitD4 | 24
sum of the 17 lemma blocks: 599
tools section (drivers, psi2, ker_psi2, helpers): lines 50-302 = 253 lines
stage 2 (BAShapeO2B.lean): macroA 14 macroB 35 ; helpers lwSplit_last/ext_normal/atomAdj_fresh/sameAtom_fresh/fresh_wf 71
targets: e2_tn 46 macroA_tn 32 macroB_tn 41 holds 11
```
Stage 2 as finally written is route (β) (narrative below): `BAShapeO2B_macroA` (`BAScostLL_macroA` composed with `BAShapeO2_lw2`/`_lw4` at `Γ := tr`) and `BAShapeO2B_macroB` (`BAScostLL_macroB` with `BAShapeO2_gg2`/`_gg4` at `Γ := tr`), packed by `baShapeLL_of_terms` (macroA) and disjunct 2 of `baShapeLL_macroB`.

### Builds, diff, axioms
```
$ lake build RBM3D.Graph.BAShapeO2 2>&1 | tail -1
Build completed successfully (3823 jobs).
$ lake build RBM3D.Graph.BAShapeO2B 2>&1 | tail -1
Build completed successfully (3827 jobs).
$ lake build 2>&1 | tail -2 | cut -c1-170
non-vacuity certificates: 0 of 90 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4273 jobs).
$ git diff main...t/T2447 --stat; git diff main...t/T2447 -- RBM3D/Test/Axioms.lean | wc -l
 RBM3D.lean                  |    2 +
 RBM3D/Graph/BAShapeO2.lean  | 1094 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAShapeO2B.lean |  447 ++++++++++++++++++
 3 files changed, 1543 insertions(+)
       0
$ grep -cE "sorry|admit|native_decide|^axiom|open private|^inductive|^structure" RBM3D/Graph/BAShapeO2.lean RBM3D/Graph/BAShapeO2B.lean
RBM3D/Graph/BAShapeO2.lean:0
RBM3D/Graph/BAShapeO2B.lean:0
$ lake env lean axioms.lean   # #print axioms of all 59 public declarations of the two files (scratch file)
standard three: 56
'BAShapeO2_map_id' does not depend on any axioms
'BAShapeO2_perm_rot' depends on axioms: [propext]
'BAShapeO2B_lwSplit_last' depends on axioms: [propext, Quot.sound]
'RBM.Graph.baShapeLL_e2_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapeLL_macroA_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapeLL_macroB_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLocReg6_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Target statements, extracted by script, against the check file (`docs/tickets/checks/T2447-check.lean`)
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2447/stmtdiff.py
baShapeLL_e2_tn vs T2447_E2TN: IDENTICAL (up to whitespace)
  check : BAShapeLL BAShape.e2 BAFrameStepTN
  lean  : BAShapeLL BAShape.e2 BAFrameStepTN
baShapeLL_macroA_tn vs T2447_MacroATN: IDENTICAL (up to whitespace)
  check : BAShapeLL BAShape.macroA BAFrameStepTN
  lean  : BAShapeLL BAShape.macroA BAFrameStepTN
baShapeLL_macroB_tn vs T2447_MacroBTN: IDENTICAL (up to whitespace)
  check : BAShapeLL BAShape.macroB BAFrameStepTN
  lean  : BAShapeLL BAShape.macroB BAFrameStepTN
baLocReg6_holds vs T2447_LocReg6Holds: IDENTICAL (up to whitespace)
  check : ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition → ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (
  lean  : ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition → ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (
```
### Acceptance on a scratch copy of the check file (not merged): `example : T2447_E2TN := baShapeLL_e2_tn`, the same for `T2447_MacroATN`, `T2447_MacroBTN`, `T2447_LocReg6Holds`, and `example : T2447_Binder` from the three
```
$ lake env lean scratchpad/T2447/T2447-check-copy.lean > checkcopy.out 2>&1; echo "exit $?"
exit 0
error lines: 0
'baShapeLL_e2_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'baShapeLL_macroA_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'baShapeLL_macroB_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'baLocReg6_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### Compiled nonempty instances (target 7 (i)-(v); targets 5 and 6 at the R1 witnesses), signatures extracted by script; all compile in the files above
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2447/inst_list.py
BAShapeO2.lean:1059: /-- `weight` at `P_W` (a blue circled loop at the internal vertex `0`) -/
BAShapeO2.lean:1063: /-- `within` at `P_B` (`2 → 3` inside the atom `{2, 3}`): the head and the terms `lanlwD` -/
BAShapeO2.lean:1068: /-- `edge` at `P_E` (a degree-3 internal vertex): the terms `lanlwD` -/
BAShapeO2.lean:1072: /-- `gg` at `P_A` (`p = 2 → 1`, `q = 0 → 2`; the internal atom `{2, 3}`): `gg2` (`A1`-`A5`, `AD`) and `gg4` (`B1`, `B2`, `BD`) -/
BAShapeO2.lean:1077: /-- `ggSplit` at `P_C`, `j = 0` (`a = 2 ≠ a' = 3` in one atom): the terms `d1`-`d4` -/
BAShapeO2B.lean:367: /-- (i) `within` at `P_B` (`hTB`; normal by `decide`; the cost bound is the crude one `-4`): targets 1 and 2 at an `e2` and a `macroA` output -/
BAShapeO2B.lean:375: /-- (iii) the macro (b) witness `BAScostInst.gc`, `pc`, `qc` (`a = 2 ≠ a' = 3` in one atom) is `P_C`, `pC`, `qC` literally -/
BAShapeO2B.lean:379: /-- (ii) `ggSplit` at `P_C`, `j = 0` (`a = 2 ≠ a' = 3` in one atom, `hTC`; 5 `e2` and 34 `macroB` outputs): targets 1 and 3 at an `e2` output, at a st
BAShapeO2B.lean:388: /-- (ii), stages: a `macroB` output of stage 1 (the terms `d2`, `d3`, `d4` of `BASim:133-134`) and one of stage 2 (`tr.gg2` at the pair of `BAScost_tr
BAShapeO2B.lean:416: /-- (iv) `gg` at `P_A` (`hTA`, 8 `e2` outputs): target 1 at an `e2` output, so that the `gg2`/`gg4` lemmas run -/
BAShapeO2B.lean:422: /-- (v) target 4 at `p = 2` (a start term by `decide`, as `BAStepS:508-517`), now with no `hX` -/
BAShapeO2B.lean:433: /-- stage 2 (target 6) at the witnesses: macro (a) at `P_B` (`BAShapeO2B_macroA`), macro (b) at `P_C` (`BAShapeO2B_macroB`), with every hypothesis dis
BAShapeO2B.lean:437: /-- stage 2 (target 6) at the witnesses: macro (a) at `P_B` (`BAShapeO2B_macroA`), macro (b) at `P_C` (`BAShapeO2B_macroB`), with every hypothesis dis
```
### Name-clash grep of the 65 new declarations (59 public, all `BAShapeO2_`/`BAShapeO2B_`-stemmed except the four pinned names; 6 private), and the final names against `main` and the other branches
```
$ grep -rnw <name> RBM3D RBM3D.lean (minus the two files), 65 names: names with a hit = 0
$ git grep -ln 'baShapeLL_e2_tn\|baShapeLL_macroA_tn\|baShapeLL_macroB_tn\|baLocReg6_holds\|BAShapeO2' main t/T2448 -- RBM3D | cut -c1-120
t/T2448:RBM3D/Graph/BAEngine.lean
```
Ports: none. No RBM1D/RBM2D file was read for a statement or copied; the pattern of `BAStepS_outsT_pack` (`BAStepS:288-293`, merged RBM3D) is re-stated as `BAShapeO2B_group` (no `open private`).

### Narrative (facts from the files and the logs above)
1. Targets 1-4 are `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn` (BAShapeO2B.lean:221, 269, 303) and `baLocReg6_holds` (:350). Statements: identical to `T2447_*` up to the name (script above); the scratch check copy compiles with exit 0 and `T2447_Binder` follows from the three.
2. File 1 (`Graph/BAShapeO2`, 1094 lines) holds target 5: the 17 builder lemmas `BAShapeO2_*` (table), the term lists `BAShapeO2_lw2`, `_lw4`, `_within`, `_gg2`, `_gg4`, and the shared tools. The tools are one driver `BAShapeO2_driver` (the reduction `BAScostLL_of_band` for any extension `ext k Γ rest S W md` with a vertex map `ψ`, a band term `Λ` known up to a permutation of its solid list, and a comparison of the new edges), instantiated for `ψ = BAScost_psi1` (`_driver1`), `ψ = vmap ∘ BAScost_rho2` (`_driver0`) and the new four-vertex map `BAShapeO2_psi2` (`_driver2`, kernel `BAShapeO2_ker_psi2`).
3. File 2 (`Graph/BAShapeO2B`, 447 lines) holds targets 6, 1-4 and 7. Stage 2 is route (β): the transfer graph `tr` is normal (`BAShapeO2B_ext_normal`), the next pair is the last element of `lwSplit tr.solid` (`BAShapeO2B_lwSplit_last`), the fresh vertex `β` of `BAScost_trB` has no `M`-dotted edge so its atom is a singleton (`BAShapeO2B_fresh_wf`: `hwf` and `hint` at `tr`); the result is `BAScostLL P.g X` by `BAScostLL.trans`. Route (α) (the band step at the packed transfer graph, `BAScost_pack P Q0`) is not used.
4. Hypotheses of the builder lemmas: the constructor's (`σ`, `circ`, the shape of `p`, `q`, `hsame`, `hwf` for the two edges `p.1`, `q.1` only, `hint` at `p.1.src`) and `Γ.Normal` for `lanlwD`, the `lw4` tail, `AD`, `BD`; none uses `hnb`, `LocStd`, the invariants (1)-(5) or the cutoff (1a (d)). `Γ.Normal` is also what gives `CircIffLoop` of the image edges (`BAShapeO2_imgE_loop`).
5. The `within` head (row 5) is the `Loop([x])` term like the `lw2` head (`scostLL_loop`), not `BAScostLL_E1`; no `baSplitSolid` computation was needed. The hypothesis `p.1.src ≠ p.1.dst` of the constructor `within` is not used.
6. `BAScostLL_S1` is `A1` of `gg2`; `BAShapeO2_gg2`/`_gg4` take `hxy : q.1.dst = p.1.src` and the two `sameAtom = false` facts, which the constructor `gg` gives (`hx`, `hwf`).
7. Root imports: `RBM3D.lean` carries `import RBM3D.Graph.BAShapeO2` and `...BAShapeO2B` after the last import on the branch (the ticket's sole writable files); `lake build` of the whole library, `#assert_rbm_axioms` included, completed successfully with `Test/Axioms.lean` unchanged (diff 0 lines); the premise scan inside `#assert_rbm_axioms` fails the build on a new premise, and the build completed.
8. Instances (listing above): (iii) `rfl` confirms `BAScostInst.gc = baPC`, `pc = pC`, `qc = qC` (BAShapeO2B.lean:375), so the `ggSplit` instance (ii) serves and no second graph is needed. The term lemmas of target 5 are also applied at `baPW`, `baPB`, `baPE`, `baPA`, `baPC` (BAShapeO2.lean:1053-1090) and the stage-2 lemmas of target 6 at `baPB`, `baPC` (BAShapeO2B.lean:433-443), every hypothesis `decide`d or `rfl`. Size: 1,541 lines in two files (the ticket's estimate 1,200-1,600), each under the stop line 2,000.

## (c) Verified Mathlib and core names used (`#check` printed a type for each, run Mon Oct 12 11:23:49 UTC 2026; none searched for as absent)
List.mem_of_getElem?, List.mem_of_mem_eraseIdx, List.perm_append_singleton, List.perm_append_comm, List.Perm.append_left, List.Perm.append_right, List.Perm.of_eq, List.Perm.subset, List.forall₂_cons, List.forall₂_nil_left_iff, Relation.ReflTransGen.cases_head, List.exists_mem_of_ne_nil, Bool.eq_false_iff, List.mem_cons_of_mem, List.map_id', List.mem_map, List.mem_append, List.mem_cons, List.mem_singleton.

## (d) Open issues and paper-delta candidates
1. **Paper delta `T2443d` is withdrawn when this row merges** (ticket, 0948 Q1 O4). Proposed line for `docs/paper-deltas.md`: "`T2443d` withdrawn: `BALocReg6` is no longer conditional on the O2 inputs; `baLocReg6_holds` (T2447, `Graph/BAShapeO2B`) proves (6) along `BAReach` with the binder discharged by `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn`." `BALocReg6` and `baLocReg6_reach` (`BAStepS`) stay as they are.
2. New Lean/paper differences: none (`T2447a` not used). The targets are the pinned statements, and the builder lemmas assume less than the constructors of `BAFrameStepT`.
3. Consumers L3d3 (`BAEngine`), L3d2 (`BAMomentGen`) may now use `baLocReg6_holds`; the branch `t/T2448` mentions it only in a docstring (`git grep` above). L3b1, L3b2 are not consumers.
4. The hub step (A.4) adds the two root imports after the last import; they are already in `RBM3D.lean` on `t/T2447`, so the hub should bring that file as is and not add them twice.
