Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 21:48:18 UTC 2026

Scope: mathematics only, no Lean. The model is the Python transcription of the merged `LocStep` outputs (`gen.py`, `pf.py` of T2142 (a), whose fidelity was tested there against `lvl1_step_good`; new scripts in scratchpad `T2151/`). `SC(Q)` = internal vertices without loop and with exactly two non-loop solid edges of equal colour (the shape of a distinguished vertex, `B:204`). Marking = (DL, DV): DL = distinguished light-weights (circled loops), DV ⊆ SC(Q); n_dvb = marked vertices created by case (i).

### (i) Exponent table
| row | value | constraint / source | slack |
|---|---|---|---|
| p | 2, 4 (even) | `B:176`: p ∈ 2ℕ, G^{(i)} = G for i ≤ p/2, Ḡ otherwise | - |
| Γ_p = `fxyPowGraph p` | (n_S,n_W,n_V,n_M) = (3p,p,2p,p), ord = p, M_x ≠ M_y | `B:201` (eq:initial_scaling) | 0; script: p=2 (6,2,4,2), p=4 (12,4,8,4) |
| marks at Γ_p | n_lw = p (loops at β_i), n_dv = p (α_i ∈ SC) | `B:204-205` | script (ii) |
| (A) weight phase | ord + n_dv + n_lw ≥ 3p, cases (i)-(vi) | `B:214-261`, eq:relateG1G0 `B:215` | at Γ_p: 3p, slack 0 |
| (C) count | 2 n_dv + n_lw ≤ 3p (n_dv grows only in case (i), at the cost of 2 lw) | `B:273` | at Γ_p: 3p, slack 0 |
| after weight phase | ord ≥ 3p − n_dv ≥ 3p/2 | `B:272-273` | - |
| (E) edge/GG, paper and ticket | removing a dv raises ord by ≥ 1/2, so 2 ord + n_dv does not decrease and ord ≥ 3p − n_dv/2 ≥ 9p/4 at a locally standard Q | `B:275-277` ("we omit the details") | vs 2p: p/4. **The step claim is false**: (ii) rows 1-2 |
| A3 (candidate) | ord + n_dv + n_lw ≥ 3p in every phase (stronger than the paper) | script (ii) | far outputs: absolute bound holds, not monotone |
| target (6) | ord(Q) ≥ 2p for every Q ∈ outs | `7_8:815-818`, `LocReg6` | least ord found at a LocStd output: p=2: 4, p=4: 8 (both with M_x = M_y), with M_x ≠ M_y: 6 at p=2 (locstd lines in (ii)); slack 0 for M_x = M_y |
| far assumption | M_x ≠ M_y | `7_8:792` (eq:far_ab); T2142a dropped it for (3),(5) | outputs with M_x = M_y occur (counts in (ii)) |
| (4) | every internal molecule on ≥ 2 distinct walks | `7_8:805-807`, `B:193-199` | at LocStd: Inv4 ⇒ (4) |
| constants | K(p) = ⌈(D + K0 n_M + d (n_V − n_W)₊)/c⌉ = 72 (p=2), 104 (p=4); c = 1/4, K0 = 1, d = 3, D = 10; W = 27, L = 3 | `lvl1Cutoff` as in T2142 (a) | L^d = 27 ≤ W^K0 = 27: 0; W^{-3/2} = 0.0071 ≤ Ψ = 0.4387 = W^{-c}: ratio 61.5 and 0 |

**Inv4(Q)** (for (4)): p walks W_i in the molecular multigraph from M_x to M_y, W_i of colour σ_i; (a) every inter-molecule solid edge lies on exactly one walk and walk i uses only edges of colour σ_i (loop steps free); (b) Hall (5) (the content of T2142 `PathInv`); (c) for every internal molecule C and colour σ: some non-loop solid edge of colour σ has an end in C ⇒ some σ-walk visits C. Step: a removed edge of W_i is replaced inside W_i by its new edges (same colour; T2142's ω); an edge inside a molecule pulled to M(x) yields two new edges, a closed detour of a σ-walk visiting that molecule (exists by (c)). At LocStd: Hall gives a walk through C, so a vertex of C has solid edges, so one G and one Ḡ edge there (standard neutral), so a blue and a red walk visit C.
**Inv6(Q; DL, DV)** (for (6), the paper's route): InvW = (A) ∧ (C); InvE = (DL = ∅ ∧ 2 ord + n_dv ≥ 9p/2). Marking rule R: DL' = surviving distinguished loops; DV' = images of DV still in SC; case (i) adds the vertex of the pulled distinguished loop; if an edge/GG step expands a marked x that leaves SC, the mark moves to the new vertex joined to x by a waved edge when that vertex is in SC (transfer). LocStd ⇒ SC = ∅, no loops ⇒ DV = ∅ ⇒ ord ≥ 9p/4.

### (ii) One concrete nondegenerate instance
Every hypothesis at once: p ∈ {2,4} even; size part c = 1/4, K0 = 1, d = 3, D = 10, L = 3, W = 27, Ψ = 27^{-1/4}; identity part E = 0, m = i, z = i/2, u = 1/2 on `lwWxInstSz` (d = 3, L = 3, W = 1) (both as in the merged instance of T2142 (a), row `regime` and `identity data`). External hypothesis: none (`lvl1_lemma_size`, `GaussIBP` are merged proofs), so no limit computation is owed.
```
$ cd scratchpad/T2151 && python3 inst.py
p=2: (nS,nW,nV,nM)=(6, 2, 4, 2) ord=2 | M_x != M_y: True | #internal molecules=2 | n_lw=2 n_dv=2 (alpha_i, all SC: True) | A: ord+n_dv+n_lw=6 vs 3p=6 ; 2n_dv+n_lw=6 vs 3p=6 ; B: ord+n_dvb+n_lw=4 vs 2p=4 ; target 2p=4, paper bound 9p/4=4.50
   lvl1Cutoff K = ceil((D + K0 nM + d (nV-nW)+)/c) = 72  (c=1/4, K0=1, d=3, D=10)
p=4: (nS,nW,nV,nM)=(12, 4, 8, 4) ord=4 | M_x != M_y: True | #internal molecules=4 | n_lw=4 n_dv=4 (alpha_i, all SC: True) | A: ord+n_dv+n_lw=12 vs 3p=12 ; 2n_dv+n_lw=12 vs 3p=12 ; B: ord+n_dvb+n_lw=8 vs 2p=8 ; target 2p=8, paper bound 9p/4=9.00
   lvl1Cutoff K = ceil((D + K0 nM + d (nV-nW)+)/c) = 104  (c=1/4, K0=1, d=3, D=10)
regime: L^d = 27 <= W^K0 = 27 : True ; W^(-d/2) = 0.0071 <= Psi = W^(-c) = 0.4387 <= W^(-c) : True
identity data: m = i, z = i/2, u = 1/2: Im z = 0.5 > 0, u > 0, m != 0, z + u m = 1j, -1/m = 1j
LocStd output (p=2, Mx=My allowed): path ['weight:T3', 'gg:R2', 'gg:R2', 'gg:R8'] ; ord=4 (nS,nW,nV,nM)=(0, 7, 5, 0) ; M_x != M_y: False ; SC=0 circled loops=0 ; ord >= 2p=4: True
   walks visiting each internal molecule (walk i is blue iff i<=p/2): [] ; edges per walk [0, 0] ; every inter-molecule edge on a walk: True
LocStd output (p=2, far only): path ['weight:T4', 'gg:R7', 'gg:R7', 'gg:R8'] ; ord=6 (nS,nW,nV,nM)=(8, 8, 9, 1) ; M_x != M_y: True ; SC=0 circled loops=0 ; ord >= 2p=4: True
   walks visiting each internal molecule (walk i is blue iff i<=p/2): [[1, 2]] ; edges per walk [4, 4] ; every inter-molecule edge on a walk: True
$ python3 cex.py    # (E) fails: Γ_2 --T3--> P (M_x ≠ M_y) --R2 at α_0--> Q (M_x = M_y)
step 1: weight term T3 -> P: ord 3 SC [(1, 0), (1, 2), (1, 3)] far True loops 0
  P solid (blue?, circ, src, dst): [(True, False, (0, 0), (1, 0)), (True, False, (1, 0), (0, 1)), (False, False, (0, 0), (1, 2)), (False, False, (1, 2), (0, 1)), (False, False, (1, 3), (1, 1)), (False, False, (1, 4), (1, 3)), (True, False, (1, 4), (1, 1))]
  weight-phase relation ord + n_dv + n_lw >= 3p = 6 with n_lw = 0 and n_dv <= |SC(P)| = 3 forces n_dv = 3, so 2*ord + n_dv = 9 >= 9p/2 = 9.0
step 2: GG term R2 -> Q: ord 3 SC [(1, 2), (1, 3)] far(M_x != M_y) False loops 0
  Q solid: [(False, False, (0, 0), (1, 2)), (False, False, (1, 2), (0, 0)), (False, False, (1, 3), (1, 1)), (False, False, (1, 4), (1, 3)), (True, False, (1, 4), (1, 1))]
  any marking of Q has n_dv <= |SC(Q)| = 2, so 2*ord + n_dv <= 8 < 9p/2 = 9.0 : the step lowers 2*ord + n_dv from 9 to at most 8
$ python3 dbg6.py | head -1    # (E) also fails with M_x ≠ M_y: R2 on the bubble G_{(1,3)(1,1)} G_{(1,1)(1,3)} (both red): Δord = 0, one marked dv lost
gg R2 far child; ord parent 4 child 4 dord 0 DV parent [(1, 0), (1, 2), (1, 3)] DV child [(1, 0), (1, 2)] SC child [(1, 0), (1, 2)] SC parent [(1, 0), (1, 1), (1, 2), (1, 3)] DL [] []
$ sh dbg4s.sh    # (dbg4.py piped through sed/grep) T3 sub-case (iv) of B:244-249 claims Δord ≥ 2, n_V(G1) ≤ n_V(G0); here q = (β, w) is incident to w
case (iv) dord 0; removed [3, 0] dropped {('n', 1)}
 parent counters (4, 6, 4, 0)
 vm moved {}
 child counters (4, 7, 5, 0)
$ python3 farbfs.py 2 3 0 200000    # every output of every state with ord ≤ 3 (ord never falls)
p=2 ORDMAX=3 far_only=0: states expanded 113, queue left 0, outputs generated 360640, states by ord {2: 1, 3: 112}, LocStd found (ord,far)={}, 8s
$ python3 beam2.py 4 60 24 8 3 | tail -1; python3 beam2.py 4 300 24 7 2 | tail -2    # p=4 beams, heuristic
step 5 cands 97 beam bad None locstd(ord,far): [((8, False), 97)] t=104
step 5 cands 494 beam bad 1 locstd(ord,far): [] t=1600
no cands
$ python3 sumexh.py exh_p2_d2_hall.out    # p=2: every output of Γ_2 and of all 946 states one step away (1399484 outputs)
depth 1 states expanded 1 new states 946 0s
depth 2 states expanded 946 new states 645057 190s
gg     Mx=My outputs=118492  Inv4 failures=0  ord+n_dv+n_lw>=3p: 118376 ok  (paper) A-or-E: 118460 ok  ord+n_dvb+n_lw>=2p: 118492 ok
gg     far   outputs=192640  Inv4 failures=0  ord+n_dv+n_lw>=3p: 192640 ok  (paper) A-or-E: 192640 ok  ord+n_dvb+n_lw>=2p: 192640 ok
weight Mx=My outputs=187600  Inv4 failures=0  ord+n_dv+n_lw>=3p: 187600 ok  (paper) A-or-E: 187600 ok  ord+n_dvb+n_lw>=2p: 187600 ok
weight far   outputs=900752  Inv4 failures=0  ord+n_dv+n_lw>=3p: 900752 ok  (paper) A-or-E: 900752 ok  ord+n_dvb+n_lw>=2p: 900752 ok
$ python3 agg.py hall_*.out; grep locstd hall_*.out | cut -c1-175    # descents p=2,4 (greedy/random), rule R, Hall checked in Inv4
runs: 3 descents: 48 p in ['2', '4']
far    outputs weight/edge/gg = 175354/14517/918975 ; failures: Inv4_fail=0, DV_not_SC=0, A_fail=0, E_fail=0, A3_fail=0, B_fail=0, A3_monotone_fail=2, B_monotone_fail=0
Mx=My  outputs weight/edge/gg = 24748/1227/805892 ; failures: Inv4_fail=0, DV_not_SC=0, A_fail=0, E_fail=124, A3_fail=124, B_fail=0, A3_monotone_fail=244, B_monotone_fail=2
hall_p4_far_s133.out:locstd reached (ord, far): [((16, 'far'), 2), ((30, 'far'), 1)] {'two walks at every internal molecule': 3}
hall_p4_all_s132.out:locstd reached (ord, far): [((8, 'Mx=My'), 4)] {'two walks at every internal molecule': 4}
hall_p2_all_s131.out:locstd reached (ord, far): [((4, 'Mx=My'), 6), ((6, 'far'), 1), ((7, 'Mx=My'), 2), ((8, 'Mx=My'), 2), ((9, 'Mx=My'), 2), ((10, 'Mx=My'), 1), ((10, 'far'),
$ cat hall_*.out fin_*.out fin2_*.out | grep -c "FAIL two walks"    # LocStd outputs lacking two walks at an internal molecule
0
$ python3 agg.py fin_*.out fin2_*.out    # 7 more descent runs, same rule (far-only runs skip M_x = M_y children)
runs: 7 descents: 215 p in ['2', '4']
far    outputs weight/edge/gg = 714188/17512/3232873 ; failures: Inv4_fail=0, DV_not_SC=0, A_fail=0, E_fail=0, A3_fail=0, B_fail=0, A3_monotone_fail=22, B_monotone_fail=6
Mx=My  outputs weight/edge/gg = 99486/3738/1321966 ; failures: Inv4_fail=0, DV_not_SC=0, A_fail=0, E_fail=248, A3_fail=250, B_fail=0, A3_monotone_fail=448, B_monotone_fail=0
$ python3 table.py 2 60 111 0.5    # case table, p=2; Δ = child − parent, 'far' = M_x ≠ M_y
p=2, 60 descents (seed 111, PR 0.5, marking rule R1+transfer); per term: #outputs far / Mx=My, min d(ord), min d(n_lw), min d(n_dv), min d(Phi=ord+n_dv+n_lw) far / Mx=My, Inv4 failures
T1       n=   542/140    dord>=1  dlw>=0   ddv>=0   dPhi>=1/1 inv4_fail=0
T2       n=   542/140    dord>=1  dlw>=-1  ddv>=0   dPhi>=0/0 inv4_fail=0
T3       n= 75040/15726  dord>=0  dlw>=-2  ddv>=-2  dPhi>=0/0 inv4_fail=0
T3(i)    n=  4024/734    dord>=1  dlw>=-2  ddv>=-2  dPhi>=0/0 inv4_fail=0
T3(ii)   n= 29800/7064   dord>=0  dlw>=-1  ddv>=-2  dPhi>=0/0 inv4_fail=0
T3(iii)  n=  4736/704    dord>=0  dlw>=-2  ddv>=0   dPhi>=0/0 inv4_fail=0
T3(iv)   n= 14840/3128   dord>=0  dlw>=-2  ddv>=-2  dPhi>=0/0 inv4_fail=0
T3(v)    n= 14016/2912   dord>=1  dlw>=-1  ddv>=-1  dPhi>=1/1 inv4_fail=0
T3(vi)   n=  7624/1184   dord>=2  dlw>=-2  ddv>=-2  dPhi>=1/1 inv4_fail=0
T4       n= 87192/28764  dord>=1  dlw>=-2  ddv>=-2  dPhi>=0/0 inv4_fail=0
Oe1xOwx  n=     8/8      dord>=1  dlw>=0   ddv>=0   dPhi>=1/1 inv4_fail=0
D        n=  2145/317    dord>=1  dlw>=0   ddv>=-1  dPhi>=1/1 inv4_fail=0
P3       n=   204/120    dord>=0  dlw>=0   ddv>=0   dPhi>=0/0 inv4_fail=0
P4       n=   202/224    dord>=0  dlw>=0   ddv>=0   dPhi>=0/0 inv4_fail=0
P5       n=   204/120    dord>=1  dlw>=0   ddv>=0   dPhi>=1/1 inv4_fail=0
P6       n=   202/224    dord>=1  dlw>=0   ddv>=0   dPhi>=1/1 inv4_fail=0
R2       n=   926/2524   dord>=0  dlw>=0   ddv>=-2  dPhi>=-1/-1 inv4_fail=0
R3       n=   270/140    dord>=1  dlw>=0   ddv>=0   dPhi>=1/1 inv4_fail=0
R4       n=  3820/6884   dord>=1  dlw>=0   ddv>=-2  dPhi>=0/0 inv4_fail=0
R5       n=  3820/6884   dord>=1  dlw>=0   ddv>=-2  dPhi>=0/0 inv4_fail=0
R6       n=  3820/6884   dord>=1  dlw>=0   ddv>=-2  dPhi>=0/0 inv4_fail=0
R7       n= 76538/24494  dord>=1  dlw>=0   ddv>=-2  dPhi>=0/0 inv4_fail=0
R8       n=252054/364722 dord>=1  dlw>=0   ddv>=-2  dPhi>=0/-1 inv4_fail=0
```

### Verdicts
- **Target 1, property (4): PASS.** Inv4 has 0 failures at every enumerated output (the exhaustive 1399484 and the descents above, with M_x = M_y included); locally standard outputs reached all have two walks at every internal molecule (p=2 far instance: nM = 1, walks [1,2]). It needs a new coloured family with an exact edge partition and the colour-visit clause (c); T2142's `PathInv` (uncoloured budget ≤) does not carry it (T2142 (d) 1); the detour of an edge inside a molecule is the new case.
- **Target 2, property (6): BLOCKED.** (a) The ticket's step claim (E) is false: Q above, for any marking (n_dv ≤ |SC| = 2), lowers 2 ord + n_dv from 9 to ≤ 8 (M_x = M_y). (b) It is false also for M_x ≠ M_y (bubble R2 above): (A), (E) and A3 hold as absolute bounds at all far outputs of the 10 descent runs (0 child violations whose parent satisfied them), but in the bubble example the parent has ord + n_dv = 7 > 3p = 6, i.e. the bound survives on slack that no invariant of the paper records; A3 is not monotone (22 far outputs), so `lvl1_induction` does not close with (A), (C), (E). (c) With M_x = M_y: in the 7 runs (E) fails at 248 and A3 at 250 outputs (A3's all at R2). (d) (6) itself is not refuted: least LocStd ord is 4 = 2p at p=2 (none ≤ 3, exhaustive), 8 = 2p at p=4 (none ≤ 7 in two beams); ord + n_lw + n_dvb ≥ 2p held at every output with M_x = M_y included (0 failures) but is not monotone (B_monotone_fail 6 far). Required from the dispatcher: (A) restrict (6) to M_x ≠ M_y as in the paper (`7_8:792`) and let stage 1b seek an inductive refinement of A3 (no paper support: research risk); or (B) obtain the omitted edge/GG analysis (`B:272-275`); or (C) release (4) and the assembly without (6). Paper-delta candidates: T2151a far assumption for (6); T2151b cases (iii),(iv) of `B:232-249` claim Δord ≥ 2, observed 0 (table T3(iii),(iv); dbg4: new loop at w without merge, n_V 4 → 5); T2151c the step claim (E) of `B:275-277`. Propose (4) and (6) as separate tickets (independent invariants); no size estimate (§4 step 1).
- **Target 3, assembly: BLOCKED** for the conjunct `Q.LocReg6 p` over all `Q ∈ outs` (by target 2); `(eq:local_Gs)` (merged `lw_localregular_expansion`), `LocReg1`, `LocReg2` and `LocReg345` (via target 1) are unaffected.

### (a′) Preflight corrections — Sun Oct  4 23:27:02 UTC 2026
1. Amend 1 (DECISIONS §47) removes target 2 (property (6)) and replaces target 3 by `lw_localregular_upto5`: the rows of (a) for (6) (`A`, `C`, `E`, A3, far assumption) and the BLOCKED verdicts of
   targets 2 and 3 are not used here (LW-10c); Inv4 (a)-(c) and the PASS of target 1 are the preflight of this stage.
2. Clause (c) of Inv4 in (a) says "some non-loop solid edge of colour σ"; `localReg2_Fam` states it for every solid edge, weights and edges inside a molecule included (the derivative terms act on
   weights, and the closed detour of `localReg2_Fam.thr` needs a walk of the weight's colour at its molecule).  Stronger than (a), proved at the start and along every `LocStep`; the verdict does not
   change.

## (b) Script output — Sun Oct  4 23:27:02 UTC 2026
```
$ git log --oneline 4f4612b..t/T2151 && git diff --stat 4f4612b...t/T2151   # branch t/T2151 in ../RBM3D-wt/T2151, base 4f4612b
bf3add3 T2151: LocalRegular2 docstring
79678ff T2151: LocalRegular2 section numbering
7a60e9f T2151: LocalRegular2 negative control and helper lemma
a90b778 T2151: LW-10b Graph/LocalRegular2 (property (4): coloured exact path invariant, assembly lw_localregular_upto5)
 RBM3D/Graph/LocalRegular2.lean | 2068 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2068 insertions(+)
$ date -u; lake env lean RBM3D/Graph/LocalRegular2.lean; echo "exit=$?"; date -u
Sun Oct  4 23:27:02 UTC 2026
exit=0
Sun Oct  4 23:27:08 UTC 2026
$ lake build RBM3D.Graph.LocalRegular2 2>&1 | grep -E "LocalRegular2|Build completed|error"
Build completed successfully (3384 jobs).
```
```
$ (temporary `import RBM3D.Graph.LocalRegular2` after the last import of RBM3D.lean; reverted by `git checkout RBM3D.lean`, not committed)
$ date -u; lake build 2>&1 | grep -E "axiom audit|premises found by scanning|registry:|Build completed|error|sorry"; lake build >/dev/null 2>&1; echo "lake build exit: $?"; date -u
Sun Oct  4 23:27:09 UTC 2026
info: RBM3D.lean:199:0: axiom audit: 4731 theorems, 1664 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 87 (borrowed 0, owed 67, structural 20).
registry: 1 borrowed + 89 owed + 49 structural; 52 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (3917 jobs).
lake build exit: 0
Sun Oct  4 23:27:31 UTC 2026
```
```
$ lake env lean ax_targets.lean   # #print axioms: the four targets
'RBM.Graph.fxyPowGraph_pathInv2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.pathInv2_locStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.PGraph.PathInv2.locReg345' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_localregular_upto5' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean axs.lean   # Lean.collectAxioms of the 102 theorem/def names of the file, grouped (instances included)
82 declarations, axioms [propext, Classical.choice, Quot.sound]
14 declarations, axioms [propext, Quot.sound]
4 declarations, axioms []
1 declarations, axioms [propext]
1 declarations, axioms [Quot.sound]
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Graph/LocalRegular2.lean; grep -c "RBM1D\|RBM2D" RBM3D/Graph/LocalRegular2.lean; wc -l RBM3D/Graph/LocalRegular2.lean
0
    2068 RBM3D/Graph/LocalRegular2.lean
```
Target statements, extracted from the file by script (`extract2.py`; the definitions with their bodies, then the theorems; `localReg2_Fam.thr` is the key lemma):
```
def localReg2_Fam (p : ℕ) (u v : N) (Int : N → Prop) (B : Multiset (Bool × Sym2 N)) : Prop
def LGraph.localReg2_PathFam (Γ : LGraph E I) (p : ℕ) (x y : E ⊕ I) : Prop
def PGraph.PathInv2 (p : ℕ) (Q : PGraph (Fin 2)) : Prop
theorem fxyPowGraph_pathInv2 (p : ℕ) : (fxyPowGraph p).pack.PathInv2 p
theorem pathInv2_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (hst : LocStep m P outs) {k : ℕ} (hP : P.PathInv2 k) : ∀ B ∈ outs, B.PathInv2 k
theorem PGraph.PathInv2.locReg345 {Q : PGraph (Fin 2)} {p : ℕ} (hL : Q.LocStd) (h : Q.PathInv2 p) : Q.LocReg345 p
theorem lw_localregular_upto5 (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) : ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs, Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ errs, ∀ (W L : ℕ)
    (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 → (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧ (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D (fxyPowGraph
    p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧ Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph
    p).pack.g.nW) ∧ (∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ → (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w
    * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp → (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : Fin 2 → Idx d (sz.L n) (sz.W n), ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
    (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum + (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧ (∀ Q ∈ outs, Q.LocReg1 ∧
    Q.LocReg2 p ∧ Q.LocReg345 p)
theorem localReg2_Fam.thr {p : ℕ} {u v : N} {Int : N → Prop} {R : Multiset (Bool × Sym2 N)} (σ : Bool) (a b X : N) : localReg2_Fam p u v Int (R + {(σ, s(a, b))}) → localReg2_Fam p u v Int (R + {(σ, s(a, X)), (σ, s(X, b))})
   body of localReg2_Fam: := ∃ (W : Fin p → List (N × N)) (col : Fin p → Bool), (∀ i, localReg_StepWalk u v (W i)) ∧ localReg2_offDiag (localReg2_stepMS col W) = localReg2_offDiag B ∧ (∀ A : Finset N, (∀ c ∈ A, Int c) → A.card ≤
    (Finset.univ.filter fun i : Fin p => ∃ c ∈ A, localReg_StepWalk.Visits u (W i) c).card) ∧ (∀ C σ, localReg2_present B C σ → ∃ i, col i = σ ∧ localReg_StepWalk.Visits u (W i) C)
   body of PGraph.PathInv2: := Q.g.localReg2_PathFam p (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1))
   body of LGraph.localReg2_PathFam: := localReg2_Fam p (Γ.molOf x) (Γ.molOf y) (fun c => ¬ Γ.IsExtMol c) Γ.localReg2_edgeMS
```
`lw_localregular_upto5` against the merged `lw_localregular_expansion` (script diff, `diffstmt.py`):
```
--- lw_localregular_expansion (merged, LocalRegular.lean)
+++ lw_localregular_upto5 (LocalRegular2.lean)
@@ -1 +1 @@
-theorem lw_localregular_expansion (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) : ∃
+theorem lw_localregular_upto5 (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) : ∃
@@ -39,3 +39 @@
-Q.LocReg35 p) ∧
-(∀
-Q ∈ outs ++ errs, Q.PathInv p)
+Q.LocReg345 p)
```
Compiled nonempty instances (same file, section 8; `inst2.py`; `localReg2_inst_Q` is the graph described in the narrative):
```
theorem localReg2_inst_step1 : ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false), B.PathInv2 2
theorem localReg2_inst_expansion : ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ errs, Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧ ∫ ω,
    (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) = (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1
    / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum + (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
    lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum ∧ (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg345 2)
theorem localReg2_inst_Q_locStd : localReg2_inst_Q.LocStd
theorem localReg2_inst_Q_pathInv2 : localReg2_inst_Q.pack.PathInv2 2
theorem localReg2_inst_Q_locReg345 : localReg2_inst_Q.pack.LocReg345 2
theorem localReg2_inst_R_not_pathInv2 : ¬ localReg2_inst_R.pack.PathInv2 1
1896: example : (fxyPowGraph 2).pack.PathInv2 2 := fxyPowGraph_pathInv2 2
1898: example : (fxyPowGraph 4).pack.PathInv2 4 := fxyPowGraph_pathInv2 4
```
Name-clash grep (`clash2.py`) and adaptation sources (`ports.py`; there is no RBM1D/RBM2D port: the `grep -c` above is 0, so no RBM1D/RBM2D diff-stat is owed):
```
git grep on main (04aedec), RBM3D/ and RBM3D.lean: declared theorem/def names 102; 97 carry the prefix localReg2_; unprefixed (targets): ['PGraph.PathInv2', 'pathInv2_locStep', 'fxyPowGraph_pathInv2', 'PGraph.PathInv2.locReg345', 'lw_localregular_upto5']
files on main mentioning the token localReg2_: 0; PathInv2: 0; pathInv2_locStep: 0; fxyPowGraph_pathInv2: 0; locReg345: 0; lw_localregular_upto5: 0; LocalRegular2: 0
adapted from the merged RBM3D file Graph/LocalRegular.lean (T2142, merge 3bf20e1), old line -> new line in Graph/LocalRegular2.lean:
localReg_Fam.map 273->218; localReg_Fam.of_add_diag 242->257; localReg_Fam.thr 333->381; localReg_pathFam_map 591->616; localReg_pathFam_partition 655->681; localReg_pathFam_stage1 706->730
localReg_pathFam_term 761->786; localReg_VRepl.deriv 816->852; localReg_pathFam_owxT3..oe2xR8 866->997; pathInv_locStep 1861->1582; localReg_fxyPowGraph_pathFam 1594->1629
lw_localregular_expansion 2004->1857; localReg_inst_expansion 2222->1909
```

Narrative (each statement is backed by the output above or by the file):
1. `RBM3D/Graph/LocalRegular2.lean` (2068 lines, 8 sections, 102 theorem/def declarations, 2 `example`s) is the only file that differs from the base; it imports only `RBM3D.Graph.LocalRegular`; helpers
   carry the prefix `localReg2_`, the five unprefixed names are the targets; `RBM3D/Test/Axioms.lean` is untouched and the full build above passes; the module elaborates in about 5 s (timestamps above).
2. Invariant. `PGraph.PathInv2 p Q` is `localReg2_Fam` on the molecular multigraph of `Q.g`: `p` walks from `M_x` to `M_y`, one colour per walk; (a) the non-loop steps with their walk's colour are exactly
   the non-loop solid edges with their colours (equality of the `offDiag` of coloured multisets); (b) Hall on the internal molecules; (c) if a solid edge of colour σ has an end in the molecule C, some
   σ-walk visits C.
3. The merged generic lemmas are not reusable: `localReg_Fam` has an uncoloured `≤` budget, and `localReg_Fam.thr` keeps the family when the rerouted edge is on no walk, which exactness forbids.  Reused
   unchanged: `localReg_StepWalk` and its lemmas, `localReg_stepEdges*`, `localReg_stepStrip`, `localReg_exists_molMap`, `LGraph.localReg_offDiag_edgeMS`, the adjacency lemmas, `lwSplit_perm`, the `fxy`
   lemmas.  Redone with colours (table above): `localReg2_Fam.map/of_add_diag/add_diag/flip/thr/repl_same/repl_deriv`, `localReg2_pathFam_map/partition/stage1/term`.
4. The new case is in `localReg2_Fam.thr`: `(σ,{a,b})` becomes `(σ,{a,X}), (σ,{X,b})`.  For `a ≠ b` the walk using the edge is rerouted through `X`; for `a = b` (a weight, or an edge inside a molecule) the
   edge is on no walk, and a closed detour `a → X → a` is inserted into a walk of colour σ visiting `a`, which exists by (c) (the pulled-edge-inside-a-molecule case of `B:197`).
5. The 17 output terms of `(Owx)`, `(Oe1x)`, `(Oe2x)` are `localReg2_VRepl.same` (edges moved inside `M(x)`) or `.deriv` (the edge hit by the derivative is replaced by two edges of its colour through
   `M(x)`); `T1`, `oe1xOwx`, `R3` only add a loop `Ǧ_{αα}` at `M(x)` (`localReg2_FamReplAt.add_loop`).  Every new loop has the colour of an edge removed or kept at `M(x)` (the `hcov` hypotheses, discharged
   term by term).  The term lemmas have the extra hypotheses `p hp hx` (T1), `v hx` (oe1xOwx), `y hp1` (R3), `hσ` (P5, P3, P6, P4), all available at the constructors of `LocStep`.
6. The output graphs are twisted frame terms: the coloured ends of `Γ` are those of `Rm + G` flipped by `c` (`localReg2_hΓ_one/two/three`, `localReg2_frame_cendsMS`, `localReg2_Fam.flip`).  The start: walk
   `i` is `x → M_i → y` of colour `decide (i < p/2)`; exactness by computing both sides as `∑ i` of the two non-loop edges of block `i` (`M_x ≠ M_i ≠ M_y` since `M_i` is internal).
7. `PathInv2.locReg345`: the family is `localReg_stepStrip (W i)`; (3) is an equality of multisets after forgetting the colours; (5) is Hall; for (4), Hall for `{C}` gives a walk, its first non-loop step
   into `C` an edge `e` at `C`, the vertex of `C` on `e` is standard neutral (`LGraph.localReg2_present_of_locStd`), so both colours are present at `C` and (c) gives a blue and a red walk, different since
   their colours differ.
8. `lw_localregular_upto5` re-applies `lvl1_lemma_size` and `lvl1_induction` with `PathInv2` (the existential of `lw_localregular_expansion` does not expose induction for a new predicate); the script diff
   above: the merged statement with `LocReg35 → LocReg345` and without the `PathInv` conjunct.
9. Instances: `fxyPowGraph_pathInv2` at p = 2, 4 (the two `example`s); `localReg2_inst_step1` (one `LocStep`, the merged `lvl1_inst_locStep_weight`); `localReg2_inst_Q` has two external and two internal
   vertices, the waved edge `S_{αβ}` and the edges `G_{xα}, Ḡ_{xα}, G_{βy}, Ḡ_{βy}`, is locally standard (`decide`), has `PathInv2 2` (a blue and a red walk through `{α,β}`) and so `LocReg345 2`;
   `localReg2_inst_expansion` is `lw_localregular_upto5` at p = 2, d = 3, c = 1/4, K0 = 1, D = 10 with the merged data `lwWxInstSz`, all hypotheses discharged; the negative control
   `localReg2_inst_R_not_pathInv2`: the locally standard graph `x -G- α -Ḡ- y` has no coloured family for p = 1.
10. Not in this ticket (Amend 1): property (6), `LocReg6`, `M_x ≠ M_y`.

## (c) Verified Mathlib names
Each name below was found in the project environment by `env.contains` and its module read with `Environment.getModuleIdxFor?` (script `mods.lean`, 114 candidates taken from the file; `Finset.univ.filter` is dot notation, not a declaration).  Verified absent: none checked.
```
Init.SimpLemmas: Bool.and_eq_true, Bool.or_eq_true | Init.Prelude: Bool.noConfusion, Prod.fst, Prod.snd | Mathlib.Algebra.BigOperators.Fin: Fin.sum_univ_def, Fin.sum_univ_two
Mathlib.Data.Finset.Card: Finset.card_image_le, Finset.card_image_of_injOn, Finset.card_le_card, Finset.card_pos, Finset.card_singleton | Mathlib.Data.Finset.Insert: Finset.induction_on, Finset.mem_singleton
Mathlib.Data.Finset.Filter: Finset.mem_filter | Mathlib.Data.Finset.Image: Finset.mem_image | Mathlib.Data.Fintype.Defs: Finset.mem_univ, Finset.univ | Mathlib.Data.Finset.Empty: Finset.nonempty_iff_ne_empty
Mathlib.Algebra.BigOperators.Group.Finset.Basic: Finset.sum_congr, Finset.sum_insert, Multiset.mem_sum | Mathlib.Algebra.BigOperators.Group.Finset.Piecewise: Finset.sum_eq_add_sum_sdiff_singleton_of_mem
Init.Data.Function: Function.Surjective | Init.Core: Function.comp_apply, Prod.map, Prod.map_apply, Prod.map_snd, Subsingleton.elim
Mathlib.Logic.Function.Basic: Function.surjInv, Function.surjInv_eq, Function.update, Function.update_of_ne, Function.update_self
Init.Data.List.Lemmas: List.any_eq_true, List.append_of_mem, List.filter_cons, List.length_pos_of_mem, List.map_append, List.map_congr_left, List.map_flatMap, List.map_map, List.mem_append, List.mem_cons, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_map_of_mem, List.mem_nil_iff, List.not_mem_nil
Init.Data.List.FinRange: List.finRange | Init.Data.List.Basic: List.map_cons, List.map_nil, List.mem_append_left | Mathlib.Data.Fin.VecNotation: Matrix.cons_val_one, Matrix.cons_val_zero
Mathlib.Data.Multiset.AddSub: Multiset.add_cons, Multiset.coe_add, Multiset.cons_add, Multiset.mem_add, Multiset.singleton_add, Multiset.zero_add | Mathlib.Data.Multiset.Defs: Multiset.coe_eq_coe, Multiset.mem_coe
Mathlib.Algebra.Order.Group.Multiset: Multiset.coe_mapAddMonoidHom, Multiset.mapAddMonoidHom
Mathlib.Data.Multiset.ZeroCons: Multiset.coe_nil, Multiset.cons_coe, Multiset.cons_swap, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, Multiset.mem_singleton_self
Mathlib.Data.Multiset.Filter: Multiset.filter_add, Multiset.filter_coe, Multiset.filter_congr, Multiset.filter_eq_nil, Multiset.filter_eq_self, Multiset.filter_filter, Multiset.filter_map, Multiset.mem_filter
Mathlib.Data.Multiset.MapFold: Multiset.map_add, Multiset.map_coe, Multiset.map_congr, Multiset.map_cons, Multiset.map_id, Multiset.map_id', Multiset.map_map, Multiset.map_singleton, Multiset.map_zero, Multiset.mem_map, Multiset.mem_map_of_mem
Init.Data.Nat.Basic: Nat.succ_le_iff | Mathlib.Analysis.SpecialFunctions.Pow.Real: Real.rpow_le_rpow_of_exponent_le | Mathlib.Data.Set.Operations: Set.InjOn
Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected: SimpleGraph.Adj.reachable, SimpleGraph.ConnectedComponent.eq, SimpleGraph.ConnectedComponent.ind, SimpleGraph.Reachable.refl
Mathlib.Data.Sym.Sym2: Sym2.IsDiag.map, Sym2.eq_iff, Sym2.eq_swap, Sym2.ind, Sym2.map, Sym2.map_map, Sym2.map_mk, Sym2.mem_iff, Sym2.mem_map, Sym2.mem_mk_left, Sym2.mem_mk_right, Sym2.mk_isDiag_iff
Mathlib.Algebra.Group.Semigroup: add_right_cancel | Mathlib.Algebra.BigOperators.Group.Finset.Defs: map_sum
```

## (d) Open issues and paper-delta candidates
Open issues:
1. Property (6) and `LocReg6` are LW-10c (Amend 1); `lvl1_lemma_induction` takes the predicate after the lists `outs`, `errs`, so the invariant of (6) can be conjoined with `PathInv2`.
2. `lw_localregular_upto5` does not repeat the `PathInv` conjunct of `lw_localregular_expansion` for `outs ++ errs` (the proof has `PathInv2` there); `PathInv2 → PathInv` is not stated (forgetting the
   colours; `PathInv2.locReg345` already gives (3), (5)).
3. Property (4) is for `outs` (locally standard graphs), as in the paper; the invariant itself holds for every graph reached from `fxyPowGraph p`.
Paper-delta candidates (to be numbered by the dispatcher):
- `T2151a`, `T2151b`, `T2151c`: as in (a) Verdicts (far assumption for (6); cases (iii), (iv) of `B:232-249` claim Δord ≥ 2, observed 0; the step claim (E) of `B:275-277`); they concern (6), are kept for
   LW-10c and are not used in this file.
- `T2151d`: (4) is proved from the coloured exact invariant (walks of one colour, every non-loop molecular edge on exactly one walk, colour-visit clause), not from the labelled correspondence "walk `i` ↔
   `M_i`" of `B:178-199`; walks, not simple paths, and no `(eq:far_ab)` (as `T2142a`).
- `T2151e`: the case of `B:197` in which the pulled `Ḡ`-edge lies inside a molecule (or is a weight) is the closed detour of `localReg2_Fam.thr`; it needs (c) for weights and edges inside a molecule, part
   of the invariant here (a′ 2).
Result: targets 1 and 3 delivered on `t/T2151` (built, axioms standard, compiled nonempty instances, full build with the root import passes); nothing external is assumed.
