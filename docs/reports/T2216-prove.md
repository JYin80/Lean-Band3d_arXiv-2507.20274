Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 22:18:52 UTC 2026

Own Python/C models (no Lean) of `LGraph.scost`/`skept`/`ScostLL` (`LocalRegular6a.lean:139-170`), the primitives (`:195-233`), the 17 term graphs (`LWWeightExp`, `LWSymm.lean:589-620`, `LWEdgeExp`, `LWGGExp`), twists and frames (`LWSymm`), `LGraph.partition` and the three `LocStep` constructors (`LWVocab.lean:1086-1303`, `LWLvl1.lean:3228-3275`), written from those files; scripts in `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2216`. min_all / min_far = min of `scost` over all set partitions of the vertices / over those separating `x = ext 0`, `y = ext 1`; for `E = Fin 2`, `ScostLL Γ T` iff min_all T >= min_all Γ and min_far T >= min_far Γ (scripts use the general ext-pattern form, |E| <= 3). slack = (min_all T - min_all Γ, min_far T - min_far Γ).

### (i) Exponent table

| row | value (script, (ii)) | constraint | slack |
|---|---|---|---|
| `Φ^all(Γ_p)`, p = 1..5 | 2, 4, 6, 8, 10 | `LocReg6Inv`: >= 2p | 0 (attained) |
| `Φ^far(Γ_p)`, p = 1..5 | 3, 6, 9, 12, 15 | >= 3p | 0 (attained) |
| `ord Γ_2`, `scost ⊥`, `H` = `Γ_2` minus light-weights | 2, 6; H (0, 2) | final step: LocStd gives `scost ⊥ = ord` | none |
| ten new terms, LL slack (all/far), `E = Fin 2`, min over 20000 draws x 2 modes | T1 2/2, T2 2/2, T4 0/0, P5 1/1, P6 0/0, R4 2/2, R5 0/0, R6 2/2, R7 0/0, R8 0/0 | >= 0 | 0 at T4, P6, R5, R7, R8 |
| seven merged terms (same draws) | Oe1xOwx 2/2, T3 0/0, R3 2/2, D 0/0, P3 0/0, P4 0/0, R2 0/0 | >= 0 | 0 at T3, D, P3, P4, R2 |
| Step 1 at `Γ_2` (4, 6) | terms (6,8) x6, (5,6) x4, (4,6) x2 | >= (4, 6) | (2,2), (1,0), (0,0) |
| Step 2 at `H` (0, 2) | Oe1xOwx (2,4), P6 (2,4), P4 (0,2), D (2,2) x2 | >= (0, 2) | (2,2), (2,2), (0,0), (2,0) |
| Step 3 at `H` (0, 2) | R2 (0,2); R3-R6 (2,4); R7, R8 (2,2) | >= (0, 2) | (0,0); (2,2); (2,0) |
| 2-cycle `u <-> z`, R2 with `y = y' = u` | `Γ` (-2,-2), T (-2,-2) (the collapse) | >= | 0 |
| hypothesis "`q` circled iff loop" (shapes (i), (o), (p), `D`) | without it `ScostLL` fails: D 123, R7 78, R8 28 of 4000 draws (T3, T4: 0) | needed | n/a |
| hypothesis `p.1.circ = false` (frames (c), (d)) | `uncirc` is a Perm of `Γ` iff `p.1` is uncircled (3709 circled non-loop cases: never a Perm) | needed | n/a |
| cutoff `K = ceil((D + K0 nM + d (nV - nW)^+)/c)` (`LWLvl1.lean:3981`), p = 2: nM 2, nV 4, nW 2, c = 1/4, K0 = 1, d = 3, D = 10 | 72; regime L^d = 27 <= W^K0 = 27, W^(-3/2) = 0.00713 <= Ψ = 0.43869 <= W^(-1/4) = 0.43869 | regime = conjunct 2, cutoff = conjunct 3 of `lw_localregular_upto5` (unchanged) | 0 at L^d and at Ψ |
| min `ord` of locally standard states on `Lvl1Reach`, p = 2, K = 5: ext0 = ext1 / ext0 != ext1 | 4 / 6 | >= 2p = 4 / >= 3p = 6 | 0 / 0 |
| `P.g.Normal` in the pins | not used by shapes (a)-(p) nor by `LGraph.scost_partition_ge` (`LocalRegular6a.lean:503`, no `Normal` hypothesis); used only through `lvl1_step_good (hN)` in `locReg6Inv_locStep` | kept as pinned | n/a |

### (ii) One concrete nondegenerate instance

`Γ_2 = fxyPowGraph 2 = p2Graph` (`E = Fin 2`, `I = Fin 4`, 6 solid, 2 waved edges, `ord 2`, `scost ⊥ 6`) and the merged examples `lvl1ExLoopExt`, `lvl1ExDeg1`, `lvl1ExSame` (`LWLvl1.lean:4109-4276`).  Target 1: `(c,t) = (true,true)`, `s = ⊥`, cost 6.  Targets 2, 3: `T2` at `p2Graph`, `lvl1ExP2p`, `x = inr 1` (line (2)).  Target 4: `LocStep.weight/edge/gg` at the four inputs, every constructor hypothesis (`hx hv hwf hbad hy hp1 hq1 hnb`), `Normal`, `CircIffLoop` true, `LocCostGe far k` at `k` = the true minima (so it holds with equality), lines (3)-(6).  Target 5: p = 2, c = 1/4, K0 = 1, d = 3, D = 10 (line (7)); `outs` is produced existentially by `lvl1_lemma_size`, so no explicit list is computed; the last conjunct is exercised by the 3303 locally standard states reached at p = 2 (below).  No external hypothesis: `grep -c "Step2LocalPT\|GbEXPHypV3\|KboundConcl" docs/tickets/checks/T2216-check.lean` gives 0; the lesson-14 limit computation does not apply.

Command: `bash $S/run_all.sh` (all draws seeded; 45 lines; `check_decomp.py 2000`, `check_ll.py 20000`, `check_pipeline.py 3000 11` are the sample sizes), output verbatim:
```
Gamma_p = fxyPowGraph p, all set partitions:  p |V| ord scost(bot) min_all (2p) min_far (3p)
 1    4    1        3          2 (2)        3 (3)   ok=True
 2    6    2        6          4 (4)        6 (6)   ok=True
 3    8    3        9          6 (6)        9 (9)   ok=True
 4   10    4       12          8 (8)       12 (12)   ok=True
 5   12    5       15         10 (10)       15 (15)   ok=True
H (Gamma_2 without its two light-weights): min_all, min_far = (0, 2)  scost(bot) = 2
scost_twist: Gamma_2: 4 twists x 203 setoids, failures 0
scost_twist: H: 4 twists x 203 setoids, failures 0
scost_twist: 300 random graphs (arbitrary circ): 45240 comparisons, failures 0
Step 1 @lw_beta0 of Gamma_2, terms by (min_all, min_far): {(6, 8): 'T1T2T3T4x6', (4, 6): 'T3T4x2', (5, 6): 'T3T4x4'}
Step 2 @x=alpha_0 of H, p = alpha_0->y: {'Oe1xOwx': (2, 4), 'P6[x->a0]': (2, 4), 'P4[x->a0]': (0, 2), 'D[0->4]': (2, 2), 'D[4->1]': (2, 2)}
Step 3 @x=alpha_0 of H, p = alpha_0->y, q = x->alpha_0: {'R2': (0, 2), 'R3': (2, 4), 'R4': (2, 4), 'R5': (2, 4), 'R6': (2, 4), 'R7/R8[0->4]': ((2, 2), (2, 2)), 'R7/R8[4->1]': ((2, 2), (2, 2))}
2-cycle u<->z: Gamma (-2, -2)  R2 with y=y'=u: (-2, -2)
phi o emb o emb = emb 2, first fresh -> inr(inr 0), second -> inr(inr 1): True
17 terms x 2 modes (circled iff loop / arbitrary circ on rest) x 2000 draws attempted (|E| 0..2, |I| 1..4): realised and identical up to Perm (solid) with equal waved length: 64241; mismatches 0; second-primitive hypothesis failures 0
control 1, hq dropped (q circled non-loop): ScostLL violated in T3 0/4000, T4 0/4000, D 123/4000, R7 78/4000, R8 28/4000 draws
control wrong decomposition (R4 with AddLoop(x) instead of Loop(alpha)): mismatches 500 of 500
ScostLL (separation pattern of E, |E| in 0..3, up to 8 vertices), 20000 draws attempted per term and mode: violations 0
min slack (all/far) for E = Fin 2, new ten: T1 2/2, T2 2/2, T4 0/0, P5 1/1, P6 0/0, R4 2/2, R5 0/0, R6 2/2, R7 0/0, R8 0/0
min slack (all/far) for E = Fin 2, merged seven: Oe1xOwx 2/2, T3 0/0, R3 2/2, D 0/0, P3 0/0, P4 0/0, R2 0/0   [53s]
Step 2 frame (p.1 uncircled): 5187 cases, uncirc is a Perm of Gamma and all 4 twisted frames have the same cost table as Gamma: 5187
Step 3 frame (p.1, q.1 uncircled): 8560 cases, same: 8560
p.1 circled non-loop: 3709 cases, uncirc not a Perm of Gamma: 3709; cost table differs in 1009
example (E=Fin 2, one internal vertex, solid [circled blue x->alpha], one waved edge): scost at the setoid {x,alpha}{y}: Gamma = 3 , uncirc(Gamma, p) = 2
(1) scost_twist at Gamma_2, s = bot: [(0, 0, 6), (0, 1, 6), (1, 0, 6), (1, 1, 6)] (merged localReg6a_inst_bot2: 6)
(2) T2 at p2Graph, lvl1ExP2p, x = inr 1 (vertex 3): hypothesis Perm True ; Gamma_2 (min_all,min_far) = (4, 6) ; T2 = (6, 8) ; ScostLL slack = 2 ; |V| = 8
   input p2Graph: Normal True, CircIffLoop True, |V| 6, nS 6, nW 2, (min_all, min_far) = (4, 6)
   input lvl1ExLoopExt: Normal True, CircIffLoop True, |V| 5, nS 5, nW 1, (min_all, min_far) = (1, 1)
   input lvl1ExDeg1: Normal True, CircIffLoop True, |V| 5, nS 1, nW 0, (min_all, min_far) = (-5, -5)
   input lvl1ExSame: Normal True, CircIffLoop True, |V| 5, nS 2, nW 0, (min_all, min_far) = (-4, -3)
   weight @p2Graph: hx True | weightExt @lvl1ExLoopExt: hx True
   edge @lvl1ExDeg1: hv (v=a0 != alpha_0) True , hx True , hwf True , hbad: deg, charge = (1, 1)
   gg @lvl1ExSame: hy (y=a0 != alpha_0) True , hp1 True , hq1 True , hwf True , hnb [(2, 0), (0, 0), (0, 0)]
(3) Step 1 @p2Graph [LocReg6Inv 2 start]: |terms|=12 distinct packed outputs=208; input min_all=4 min_far=6
   outputs: min of min_all=4, min of min_far=6 (far vacuous in 0); decreases 0; CircIffLoop holds in 208/208; Lemma B 76156 setoids, failures 0
(4) Step 1 @a0 (conj selector): |terms|=10 distinct packed outputs=134; input min_all=1 min_far=1
   outputs: min of min_all=1, min of min_far=1 (far vacuous in 7); decreases 0; CircIffLoop holds in 134/134; Lemma B 14254 setoids, failures 0
(5) Step 2 @lvl1ExDeg1 (transposing selector): |terms|=1 distinct packed outputs=1; input min_all=-5 min_far=-5
   outputs: min of min_all=-3, min of min_far=-3 (far vacuous in 0); decreases 0; CircIffLoop holds in 1/1; Lemma B 203 setoids, failures 0
(6) Step 3 @lvl1ExSame (transposing selector): |terms|=5 distinct packed outputs=42; input min_all=-4 min_far=-3
   outputs: min of min_all=-4, min of min_far=-3 (far vacuous in 18); decreases 0; CircIffLoop holds in 42/42; Lemma B 4148 setoids, failures 0
(7) lvl1Cutoff = ceil((D + K0 nM + d (nV-nW)^+)/c) = ceil((10+2+6)/0.25) = 72; regime: L^d = 27 <= W^K0 = 27: True; W^(-d/2) = 0.00713 <= Psi = 0.43869 <= W^(-c) = 0.43869: True
3000 random P (CircIffLoop; every second one loop-free), LocStep instances 11489 {'weight': 2798, 'edge': 6661, 'gg': 2030}; terms 71863, children 1921931
term-lemma hypothesis failures 0, ScostLL failures 0, Phi decreases 0, CircIffLoop failures 0 (39s)
```
Lemma B = `scost T (s o vm) <= scost Q s` for every setoid `s` of every output `Q` (all outputs with <= 8 vertices); the last two lines run all constructor instances (weight, edge, gg; `hbad`, `hnb` not imposed) on random normal `P` with all term lemmas' hypotheses re-derived from the frame.  Reachability (`bash $S/run_explore.sh`, `python3 explore.py p K tmax [maxstates]`: every `LocStep` constructor choice, all `(c,t)`; states up to isomorphism; sources with `ord < K`, not LocStd; `Phi` by brute force for <= 11 vertices); the last block is `python3 explore.py 3 6 600 400000` (its report lines; stopped by the time cap after level 3):
```
$ python3 explore.py 1 6 900 | tail -3
p=1 K=6: states 31123, parent->child edges 89785 (by constructor {'weight': 16488, 'gg': 65075, 'edge': 1212}; Phi skipped for |V|>11: 7010)
   Phi decreases along edges: all 0, far 0; states with circled-non-loop: 0; min Phi over states: all 2 (2p=2), far 3 (3p=3)
   locally standard states: 78 (31 with ext0 = ext1); min ord of them: all 4 (>= 2p=2: True), ext0 = ext1: 4, ext0 != ext1: 5 (>= 3p=3: True)
$ python3 explore.py 2 5 900 | tail -3
p=2 K=5: states 368405, parent->child edges 652328 (by constructor {'weight': 39982, 'gg': 611628}; Phi skipped for |V|>11: 718)
   Phi decreases along edges: all 0, far 0; states with circled-non-loop: 0; min Phi over states: all 4 (2p=4), far 6 (3p=6)
   locally standard states: 3303 (472 with ext0 = ext1); min ord of them: all 4 (>= 2p=4: True), ext0 = ext1: 4, ext0 != ext1: 6 (>= 3p=6: True)
$ python3 explore.py 3 5 900 | tail -3
p=3 K=5: states 6143, parent->child edges 8738 (by constructor {'weight': 8634}; Phi skipped for |V|>11: 104)
   Phi decreases along edges: all 0, far 0; states with circled-non-loop: 0; min Phi over states: all 6 (2p=6), far 9 (3p=9)
   locally standard states: 0 (0 with ext0 = ext1); min ord of them: all None (>= 2p=6: True), ext0 = ext1: None, ext0 != ext1: None (>= 3p=9: True)
p=3 K=6: states 248630, parent->child edges 357524 (by constructor {'weight': 55114, 'gg': 181583}; Phi skipped for |V|>11: 120827)
   Phi decreases along edges: all 0, far 0; states with circled-non-loop: 0; min Phi over states: all 6 (2p=6), far 9 (3p=9)
   locally standard states: 0 (0 with ext0 = ext1); min ord of them: all None (>= 2p=6: True), ext0 = ext1: None, ext0 != ext1: None (>= 3p=9: True)
```
Confirms candidate (c) of the ticket: at p = 2 the minimum of `ord` is 4 = 2p over locally standard states with ext0 = ext1 (so `B:277`'s strict `> 2p` fails there) and 6 = 3p with ext0 != ext1.

Verdict (the scripts are own models of the merged definitions; numerics are bounded samples, K <= 5 for p = 2, no locally standard state is reached for p = 3 within the time cap):
- Target 1 `LGraph.scost_twist`: PASS (4 twists x 203 setoids x 2 graphs and 300 random graphs, 0 failures; conjugation maps `(bi,bo,ri,ro)` to `(ri,ro,bi,bo)` and transposition to `(bo,bi,ro,ri)`, both preserve the set `{(1,1,0,0),(0,0,1,1)}` of `lwElem` (`LocalRegular6a.lean:121`)).
- Target 2 transfers (a)-(d): PASS (frames: same cost table as `Γ`, circled `p.1` excluded by the hypothesis).
- Target 3 ten decompositions: PASS (list identities up to Perm, 64241 realised draws, 0 mismatches, every second-primitive hypothesis supplied; `φ` identity checked; LL 0 violations, min slack 0 at five terms).
- Target 4 `circIffLoop_locStep`, `locCostGe_locStep`, `locReg6Inv_locStep`, (e), (f): PASS (every shape hypothesis is supplied by the constructors and `CircIffLoop`; 0 decreases of `Phi` and 0 `CircIffLoop` failures on 1.9 M children).
- Target 5 `lw_localregular`: PASS (`2p`, `3p` attained, no exponent gap; the far clause needs `ext 0 != ext 1` only).
- The ticket's item (iv) (line estimate) is not given here: stage 1a excludes size estimates.
## (b) Script output — Mon Oct  5 23:33:45 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2216`, branch `t/T2216`, 5 commits on `18a41d3` (author Jun Yin); sole writable file `RBM3D/Graph/LocalRegular6d.lean` (new module importing `RBM3D.Graph.LocalRegular6c` only). No port from RBM1D/RBM2D (nothing copied: no file:line, commit or diff-stat owed). Scripts and raw outputs: `SP/T2216/` (`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`).
### Build, direct compile, registry pre-check, full build
```
Mon Oct  5 23:29:46 UTC 2026
$ git rev-parse --abbrev-ref HEAD; git rev-parse HEAD; git status --short | wc -l
t/T2216
cdef5eaa1496acde864e9c08ca50d3a14da2a235
0
$ lake build RBM3D.Graph.LocalRegular6d 2>&1 | tail -1
Build completed successfully (3388 jobs).
Mon Oct  5 23:29:48 UTC 2026
$ lake env lean RBM3D/Graph/LocalRegular6d.lean > direct.txt 2>&1; echo exit=$?; wc -c < direct.txt   # direct compile of the committed file (no warning)
exit=0
0
Mon Oct  5 23:29:52 UTC 2026
$ lake env lean precheck.lean > precheck_full.txt 2>&1; echo exit=$?; head -1; wc -l; grep -c error; grep -c 'LocalRegular6d\|localReg6d'   # registry pre-check (DECISIONS §20 (2)); precheck.lean = import RBM3D, import RBM3D.Graph.LocalRegular6d, blank, #assert_rbm_axioms
exit=0
axiom audit: 6469 theorems, 2223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
265
0
0
Mon Oct  5 23:30:28 UTC 2026
$ lake build 2>&1 | tail -1   # full library in the worktree (the hub adds the root import at merge; the module itself is covered by the pre-check)
Build completed successfully (4019 jobs).
```
### Axioms, the five Pins, the shapes of the check file
```
Mon Oct  5 23:30:40 UTC 2026
$ lake env lean axioms.lean   # Lean.collectAxioms over every constant of the module (env.header.moduleData), the 5 pinned theorems, the 17 other target declarations
module RBM3D.Graph.LocalRegular6d: 159 constants (152 theorems, 7 definitions, 0 other); axioms used by any of them: propext, Classical.choice, Quot.sound; constants with a non-standard axiom: 0
the 4 transfers, the 10 target-3 declarations, the 2 step shapes and the case split (17 theorems): axioms used: propext, Classical.choice, Quot.sound
the 5 pinned theorems (scost_twist, circIffLoop_locStep, locCostGe_locStep, locReg6Inv_locStep, lw_localregular; 5 theorems): axioms used: propext, Classical.choice, Quot.sound
$ lake env lean pins_check.lean   # the 5 Pins of check-file section 2 (lines 231-279) in RBM.Graph.T2216Check, each `theorem chk_x : XPin := @name`
pins: 5 theorems checked by `@name`; axioms used: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean shapes_check.lean   # the 16 Prop shapes (a)-(p) and the 7 instance shapes of check-file section 3, each `theorem t_x : S_x := <file declaration>`
shapes: 23 theorems checked by the file declarations; axioms used: [propext, Classical.choice, Quot.sound]
exit=0
$ md5 of T2184-check.lean:379-427 and of T2216-check.lean:231-279 (the 49 pin lines of section 2)
2f779e1b5b85b0a29fe0650b0db9e00e
2f779e1b5b85b0a29fe0650b0db9e00e
```
### Diff scope, forbidden tokens, counts, unused hypotheses, name clash
```
$ git diff --stat main...t/T2216; git diff --name-only main...t/T2216
 RBM3D/Graph/LocalRegular6d.lean | 1510 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 1510 insertions(+)
RBM3D/Graph/LocalRegular6d.lean
$ grep -c 'sorry\|admit\|native_decide\|^axiom' F; grep -c '^open Classical$' F; grep -n '^import' F; grep -c maxHeartbeats F; wc -l F
0 0 6:import RBM3D.Graph.LocalRegular6c 0 1510
$ counts (grep on F): private theorem | private def | public theorem | public def | open Classical in | example | decide +kernel
49 | 1 | 61 | 6 | 3 | 0 | 0
$ lake env lean unused.lean   # explicit Prop-valued binders of the proof terms of the 20 target declarations that the body never mentions (non-empty lists only)
RBM.Graph.circIffLoop_locStep: [hN]
RBM.Graph.locCostGe_locStep: [hN]
$ clash.sh   # every public name of the new file (67: the `theorem`/`def` lines at column 0) as a whole word, outside the new file: the main worktree files, and `git grep` on `main` and every branch `t/*` except `t/T2216`
Mon Oct  5 23:31:05 UTC 2026
public names checked:       67
main worktree (RBM3D, RBM3D.lean; main at 0d5868e) hits: 0
branches searched (main + t/* except t/T2216): 223; total hits: 0
the pattern does match the new file (branch t/T2216): 196 lines
Mon Oct  5 23:33:05 UTC 2026
```
### Targets (`extract.py F pub`: line, statement from the name to the first depth-0 `:=`; the 24 public non-instance theorems)
```
122: theorem localReg6d_halfPat_twist {V : Type*} (c t : Bool) (es : List (SEdge V)) (K : V → Prop) [DecidablePred K] : lwElem (lwHalfPat (es.map (lwSymmTwistS c t)) K) = lwElem (lwHalfPat es K)
172: theorem LGraph.scost_twist (c t : Bool) (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : LGraph.scost (lwSymmTwistG c t Γ) s = LGraph.scost Γ s
192: theorem localReg6d_ll_twist (c t : Bool) (Γ : LGraph E I) (T : LGraph E I') : LGraph.ScostLL (lwSymmTwistG c t Γ) T → LGraph.ScostLL Γ (lwSymmTwistG c t T)
203: theorem localReg6d_ll_perm (Γ Γ' : LGraph E I) (T : LGraph E I') (hS : Γ.solid.Perm Γ'.solid) (hW : Γ.waved.length = Γ'.waved.length) : LGraph.ScostLL Γ T → LGraph.ScostLL Γ' T
211: theorem localReg6d_ll_frame (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (T : LGraph E I') (hp : p ∈ lwSplit Γ.solid) (hc : p.1.circ = false) (h : LGraph.ScostLL (lwSymmFrame c t Γ p) T) : LGraph.ScostLL Γ (lwSymmTwistG c t T)
221: theorem localReg6d_ll_frame2 (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (T : LGraph E I') (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hc : p.1.circ = false) (hc' : q.1.circ = false) (h : LGraph.ScostLL (lwSymmFrame2 c t Γ p q) T) : LGraph.ScostLL Γ (lwSymmTwistG c t T)
265: theorem localReg6d_ll_T1 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) : LGraph.ScostLL Γ (owxET1 m Γ x)
270: theorem localReg6d_ll_T2 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : E ⊕ I) (h : Γ.solid.Perm (⟨true, true, x, x⟩ :: p.2)) : LGraph.ScostLL Γ (owxET2 m Γ p x)
315: theorem localReg6d_ll_T4 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q.1.src = q.1.dst ↔ q.1.circ = true) (h : Γ.solid.Perm (⟨true, true, x, x⟩ :: q.1 :: q.2)) : LGraph.ScostLL Γ (owxET4 m Γ x q)
337: theorem localReg6d_ll_P5 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : Sum.inr x ≠ v) (h2 : Sum.inr x ≠ q.1.dst) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨false, false, Sum.inr x, q.1.dst⟩ :: q.2)) : LGraph.ScostLL Γ (oe1xP5 m Γ x v q)
349: theorem localReg6d_ll_P6 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : q.1.src ≠ Sum.inr x) (h2 : Sum.inr x ≠ v) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨true, false, q.1.src, Sum.inr x⟩ :: q.2)) : LGraph.ScostLL Γ (oe1xP6 m Γ x v q)
361: theorem localReg6d_ll_R5 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) : LGraph.ScostLL Γ (oe2xR5 m Γ q x y y')
374: theorem localReg6d_ll_R7 (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : Sum.inr x ≠ y) (hq : q'.1.src = q'.1.dst ↔ q'.1.circ = true) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q'.1 :: q'.2)) : LGraph.ScostLL Γ (oe2xR7 m Γ x y y' q')
388: theorem localReg6d_ll_R4 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) : LGraph.ScostLL Γ (oe2xR4 m Γ q x y y')
404: theorem localReg6d_ll_R6 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) : LGraph.ScostLL Γ (oe2xR6 m Γ q x y y')
429: theorem localReg6d_ll_R8 (m : ℂ) (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y) (hq : q'.1.src = q'.1.dst ↔ q'.1.circ = true) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q'.1 :: q'.2)) : LGraph.ScostLL Γ (oe2xR8 m Γ x y y' q')
955: theorem localReg6d_locCostGe_term {I'' : Type} [Fintype I''] [DecidableEq I''] (m : ℂ) (P : PGraph (Fin 2)) (T : LGraph P.E' I'') (far : Bool) (k : ℤ) (hLL : LGraph.ScostLL P.g T) (hk : PGraph.LocCostGe far k P) : ∀ Q0 ∈ T.partition m, PGraph.LocCostGe far k (Q0.lvl1Comp P.ext P.ext_surj)
976: theorem localReg6d_circIffLoop_term {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (m : ℂ) (T : LGraph E I) (Q0 : PGraph E) (hT : ∀ e ∈ T.solid, e.circ = true → e.src = e.dst) (hQ0 : Q0 ∈ T.partition m) : LGraph.CircIffLoop Q0.g
1016: theorem localReg6d_locStep_elim {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs) (hC : LGraph.CircIffLoop P.g) (Z : PGraph E → Prop) (hZ : ∀ {I'' : Type} [Fintype I''] [DecidableEq I''] (T : LGraph P.E' I''), (∀ e ∈ T.solid, e.circ = true → e.src = e.dst) → LGraph.ScostLL P.g T → ∀ Q0 ∈ T.partition m, Z (Q0.lvl1Comp P.ext P.ext_surj)) : ∀ B ∈ outs, Z B
1070: theorem circIffLoop_locStep {E : Type} {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs) (hN : P.g.Normal) (hC : LGraph.CircIffLoop P.g) : ∀ Q ∈ outs, LGraph.CircIffLoop Q.g
1077: theorem locCostGe_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (hst : LocStep m P outs) (hN : P.g.Normal) (hC : LGraph.CircIffLoop P.g) (far : Bool) (k : ℤ) (hk : PGraph.LocCostGe far k P) : ∀ Q ∈ outs, PGraph.LocCostGe far k Q
1085: theorem locReg6Inv_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (p : ℕ) (hst : LocStep m P outs) (hP : PGraph.LocReg6Inv p P) : ∀ Q ∈ outs, PGraph.LocReg6Inv p Q
1107: theorem lw_localregular (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) : ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs, Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 → (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧ (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧ Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW) ∧ (∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ → (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp → (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : Fin 2 → Idx d (sz.L n) (sz.W n), ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) = (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum + (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧ (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p ∧ Q.LocReg6 p ∧ (Q.ext 0 ≠ Q.ext 1 → 3 * (p : ℤ) ≤ Q.g.scalingOrder))
1144: theorem localReg6d_scost_ge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : 2 * (Γ.waved.length : ℤ) - 2 * (Fintype.card I : ℤ) ≤ Γ.scost s
```
### Compiled instances (`extract.py F inst | cut -c1-170`: the 37 public `localReg6d_inst_*` theorems and the 6 public defs `localReg6d_inst*`, the data of the instances)
```
1164: theorem localReg6d_inst_twist : (lwSymmTwistG true true (fxyPowGraph 2)).scost ⊥ = 6
1170: theorem localReg6d_inst_T2 : LGraph.ScostLL p2Graph (owxET2 (mE 0) p2Graph lvl1ExP2p (Sum.inr 1))
1175: theorem localReg6d_inst_step1 : ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false), B.LocReg6Inv 2
1181: theorem localReg6d_inst_circ_loopExt : LGraph.CircIffLoop lvl1ExLoopExt
1186: theorem localReg6d_inst_circ_deg1 : LGraph.CircIffLoop lvl1ExDeg1
1191: theorem localReg6d_inst_circ_same : LGraph.CircIffLoop lvl1ExSame
1197: theorem localReg6d_inst_weightExt : ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExLoopExt.pack → ∀ B ∈ lvl1Pack lvl1ExLoopExt.pack (lvl1WeightOuts0 (mE 0) lv
1206: theorem localReg6d_inst_edge : ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExDeg1.pack → ∀ B ∈ lvl1Pack lvl1ExDeg1.pack (lvl1EdgeOuts0 (mE 0) lvl1ExDeg1 lvl1
1215: theorem localReg6d_inst_gg : ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k lvl1ExSame.pack → ∀ B ∈ lvl1Pack lvl1ExSame.pack (lvl1GGOuts0 (mE 0) lvl1ExSame lvl1ExSa
1227: theorem localReg6d_inst_weightExt_conc : ∀ B ∈ lvl1Pack lvl1ExLoopExt.pack (lvl1WeightOuts0 (mE 0) lvl1ExLoopExt lvl1ExLoopExtp (Sum.inl (0 : Fin 2)) true false), P
1238: theorem localReg6d_inst_edge_conc : ∀ B ∈ lvl1Pack lvl1ExDeg1.pack (lvl1EdgeOuts0 (mE 0) lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true), PGrap
1249: theorem localReg6d_inst_gg_conc : ∀ B ∈ lvl1Pack lvl1ExSame.pack (lvl1GGOuts0 (mE 0) lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2)) (Sum.inl (
1261: theorem localReg6d_inst_T1 : LGraph.ScostLL p2Graph (owxET1 (mE 0) p2Graph (Sum.inl 0))
1265: theorem localReg6d_inst_T4 : LGraph.ScostLL p2Graph (owxET4 (mE 0) p2Graph (Sum.inr 1) (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨
1272: theorem localReg6d_inst_P6 : LGraph.ScostLL (fxyPowGraph 2) (oe1xP6 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [⟨true, true, Sum.inr
1279: theorem localReg6d_inst_R4 : LGraph.ScostLL (fxyPowGraph 2) (oe2xR4 (mE 0) (fxyPowGraph 2) (⟨true, true, Sum.inr 1, Sum.inr 1⟩, [⟨true, true, Sum.inr 1, Sum.inr 1⟩,
1287: theorem localReg6d_inst_R5 : LGraph.ScostLL (fxyPowGraph 2) (oe2xR5 (mE 0) (fxyPowGraph 2) (⟨true, true, Sum.inr 1, Sum.inr 1⟩, [⟨true, true, Sum.inr 1, Sum.inr 1⟩,
1294: theorem localReg6d_inst_R6 : LGraph.ScostLL (fxyPowGraph 2) (oe2xR6 (mE 0) (fxyPowGraph 2) (⟨true, true, Sum.inr 1, Sum.inr 1⟩, [⟨true, true, Sum.inr 1, Sum.inr 1⟩,
1301: theorem localReg6d_inst_R7 : LGraph.ScostLL (fxyPowGraph 2) (oe2xR7 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (Sum.inl 0) (⟨true, true, Sum.inr 1, Sum.inr 1⟩, [⟨false, t
1307: theorem localReg6d_inst_R8 : LGraph.ScostLL (fxyPowGraph 2) (oe2xR8 (mE 0) (fxyPowGraph 2) 0 (Sum.inl 1) (Sum.inl 0) (⟨true, true, Sum.inr 1, Sum.inr 1⟩, [⟨false, t
1314: def localReg6d_instG : LGraph (Fin 2) (Fin 1)
1321: theorem localReg6d_inst_P5 : LGraph.ScostLL localReg6d_instG (oe1xP5 (mE 0) localReg6d_instG 0 (Sum.inl 1) (⟨false, false, Sum.inr 0, Sum.inl 0⟩, []))
1326: theorem localReg6d_inst_ll_twist : LGraph.ScostLL (fxyPowGraph 2) (lwSymmTwistG true false (lwPrimLoop (lwSymmTwistG true false (fxyPowGraph 2)) (Sum.inl 0) true))
1331: theorem localReg6d_inst_ll_perm : LGraph.ScostLL { fxyPowGraph 2 with solid := (fxyPowGraph 2).solid.reverse } (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true)
1336: theorem localReg6d_inst_ll_frame : LGraph.ScostLL p2Graph (lwSymmTwistG true true (lwSymmFrame true true p2Graph (⟨false, false, Sum.inr 2, Sum.inl 1⟩, [⟨true, true
1343: theorem localReg6d_inst_ll_frame2 : LGraph.ScostLL p2Graph (lwSymmTwistG true true (lwSymmFrame2 true true p2Graph (⟨false, false, Sum.inr 2, Sum.inl 1⟩, [⟨true, tr
1356: def localReg6d_instEdgeG : LGraph (Fin 2) (Fin 3)
1365: def localReg6d_instEdgep : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3))
1370: theorem localReg6d_inst_locStep_edge3 : LocStep (mE 0) localReg6d_instEdgeG.pack (lvl1Pack localReg6d_instEdgeG.pack (lvl1EdgeOuts0 (mE 0) localReg6d_instEdgeG loca
1378: theorem localReg6d_inst_edge3_normal : localReg6d_instEdgeG.Normal
1381: theorem localReg6d_inst_edge3_circ : LGraph.CircIffLoop localReg6d_instEdgeG
1387: def localReg6d_instGGG : LGraph (Fin 2) (Fin 3)
1395: def localReg6d_instGGp : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3))
1400: def localReg6d_instGGq : SEdge (Fin 2 ⊕ Fin 3) × List (SEdge (Fin 2 ⊕ Fin 3))
1404: theorem localReg6d_inst_locStep_gg3 : LocStep (mE 0) localReg6d_instGGG.pack (lvl1Pack localReg6d_instGGG.pack (lvl1GGOuts0 (mE 0) localReg6d_instGGG localReg6d_ins
1413: theorem localReg6d_inst_gg3_normal : localReg6d_instGGG.Normal
1416: theorem localReg6d_inst_gg3_circ : LGraph.CircIffLoop localReg6d_instGGG
1422: theorem localReg6d_inst_edge3_terms : (lwSplit localReg6d_instEdgep.2).map (fun q => (lwSymmOe1xDs false true (mE 0) localReg6d_instEdgeG localReg6d_instEdgep 0 (Su
1427: theorem localReg6d_inst_gg3_terms : (lwSplit localReg6d_instGGq.2).length = 2
1432: theorem localReg6d_inst_edge3 : ∀ B ∈ lvl1Pack localReg6d_instEdgeG.pack (lvl1EdgeOuts0 (mE 0) localReg6d_instEdgeG localReg6d_instEdgep (0 : Fin 3) (Sum.inl (0 : F
1446: theorem localReg6d_inst_gg3 : ∀ B ∈ lvl1Pack localReg6d_instGGG.pack (lvl1GGOuts0 (mE 0) localReg6d_instGGG localReg6d_instGGp localReg6d_instGGq (0 : Fin 3) (Sum.i
1470: theorem localReg6d_inst_expansion : ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ errs, Q.g.scalingSize (((27 : ℕ) :
1496: theorem localReg6d_inst_last : ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs ++ errs, Q.g.Normal) ∧ ∀ Q ∈ outs, Q.LocStd ∧ Q.LocReg6 2 ∧ (Q.ext 0 ≠ Q.ext 1 → (6 
```
### Narrative (facts only)
- File: 1510 lines (ticket estimate 1500-2200, stop threshold 2500); counts above: 49 private theorems and 1 private def (`localReg6d_phi`), 61 public theorems (5 pins, 4 transfers, 10 term lemmas, `localReg6d_halfPat_twist`, `_circIffLoop_term`, `_locCostGe_term`, `_locStep_elim`, `_scost_ge`, 37 instances), 6 public defs (the data of the instances, listed above); no Prop-valued definition, so no registry line is owed or removed (the pre-check output has 0 lines naming the module).
- Target 1 (`LGraph.scost_twist`): `skept` of the twist is the twisted `skept` (`lwSymmTwistG_solid`, `List.filter_map`; `circ` kept by `lwSymmTwistS_circ`, the ends swap and `s` is symmetric), the waved length is unchanged, `sIntCls` does not mention the graph, `sElemCls` is unchanged by `localReg6d_halfPat_twist` (the pattern of the twisted list has its components permuted, `(bi,bo,ri,ro) ↦ (ri,ro,bi,bo)`, `(bo,bi,ro,ri)`, `(ro,ri,bo,bi)`, and `lwElem` is invariant: `localReg6d_elem_perm`, `omega`).
- Target 2: (a) is `scost_twist` on both sides, (b) `LGraph.scost_perm`; (c), (d): `lwSymmUncirc Γ p` (resp. `lwSymmUncirc2`) has the solid list `p.1 :: p.2` (resp. `p.1 :: q.1 :: q.2`) once the circle flags are `false` (`localReg6d_uncirc_eq`), a permutation of `Γ.solid` by `lwSplit_perm`; then (a), (b).
- Target 3: `T1` = `scostLL_loop` and `of_perm` (equal lists); `T2`, `T4` = `scostLL_moveLoop` then `scostLL_loop` resp. `scostLL_dmove` (`z = v = α`, `cp = true`); `P5` = `scostLL_moveOut` then `scostLL_addLoop` (red); `P6`, `R5` = `scostLL_moveSC` then `scostLL_addLoop` (blue); `R4` = `scostLL_moveSC` then `scostLL_loop`; `R6` = `scostLL_loop` then `scostLL_moveSC` at `owxEmb 1 x` (its `Perm` hypothesis from `hperm.map` and `List.Perm.append_right`); `R7` = `scostLL_dmove` (`cp = false`, `rest = ⟨true,false,y',x⟩ :: q'.2`); `R8` = `scostLL_moveSC` then `scostLL_dmove` (`z = α`, `v = owxEmb 1 y`, `cp = false`; `α ≠ owxEmb 1 y` by `cases y <;> simp`).
- Target 3, composition: `LGraph.ScostLL.trans`; the five two-fresh-vertex terms (`T2`, `T4`, `R4`, `R6`, `R8`) by `LGraph.ScostLL.of_relabel` along `localReg6d_phi` (onto, fixes `inl`; `φ ∘ owxEmb 1 ∘ owxEmb 1 = owxEmb 2` by `cases v <;> rfl`; the first fresh vertex goes to `inr (inr 0)`, the second to `inr (inr 1)`, both `rfl`; `owxDE` commutes with `SEdge.map φ`: `localReg6d_phi_owxDE_fst`, `_snd`), then `of_perm`: the solid lists are equal for `T2`, `T4` and are related by explicit `Perm` terms built from `List.Perm.swap`, `List.perm_middle`, `List.perm_append_singleton` for the others (`simp only`, then the `Perm` term; no `decide` on general lists); the waved lists have equal length by `simp`, their colours or ends may differ (`R6`: `x - β` for `α - β`).
- The seven merged terms are used as they are: `localReg6c_inst_ET3` (`T3`), `localReg6b_inst_T1` (`Oe1xOwx`, `R3`), `localReg6c_inst_D`, `localReg6c_inst_P3`, `localReg6c_inst_P4`, `localReg6b_inst_R2`.
- Target 4 (e) `localReg6d_locCostGe_term`: `LGraph.scost_partition_ge` gives `vm` (`vm (inl a) = inl (Q0.ext a)`, `T.scost (comap vm s) ≤ Q0.g.scost s`); `ScostLL P.g T` at `comap vm s` gives `s₀`, and `Setoid.comap_rel` turns the far hypothesis on `s` into the separation of `P.ext 0`, `P.ext 1` by `s₀`; then `LocCostGe far k P` at `s₀`. (f) `localReg6d_circIffLoop_term`: `lvl1_part_struct` and induction on `lvl1Split` (a kept edge is circled only if the image of a circled edge, hence a loop; `circ` circles a loop; `drop` removes one).
- Target 4, the step: `localReg6d_locStep_elim` is `cases hst` as `pathInv2_locStep` (`weight`: 4 terms; `edge`: `Oe1xOwx` and per `q ∈ lwSplit p.2` the list `oe1xDs` = `[P5, P3]`, `[P6, P4]` or `[D]` by its two `if`s; `gg`: `R2`-`R6` and `R7`, `R8` per `q' ∈ lwSplit q.2`); for every term the private `localReg6d_good_*` give (circled ⇒ loop) and `ScostLL P.g T` (target-3 lemma on the frame, then the transfers (a)-(d)). Constructor hypotheses used: `hp`, `hx` (`weight`); `hp`, `hv`, `hx`, `hwf` (`edge`); `hp`, `hq`, `hy`, `hp1`, `hq1`, `hwf` (`gg`), with `CircIffLoop P.g`: `p.1.circ = q.1.circ = false` (`localReg6d_uncirc_of_wf`), `y' ≠ inr x` (`localReg6d_gg_facts`), the frame lists (`localReg6d_frame_solid`, `localReg6d_frame2_solid`: the uncircled selected edges, then the twisted rest). `hbad`, `hnb` are not used.
- Hypotheses (script `unused.lean`): `P.g.Normal` (`hN`) is not used by `circIffLoop_locStep` nor by `locCostGe_locStep`; it is used by `locReg6Inv_locStep` (through `lvl1_step_good`); no other of the 20 declarations checked has an unused hypothesis. The five pins are `@name` of the check file's Pins (`pins_check.lean`); no hypothesis added, no pin or merged statement changed.
- Target 5 `lw_localregular`: `obtain` the five conjuncts of `lw_localregular_upto5`, the first four unchanged; `lvl1_induction` with `Pred := PGraph.LocReg6Inv p` on `Lvl1Reach` (third conjunct; start `fxyPowGraph_locReg6Inv p`, step `locReg6Inv_locStep`); `locReg6_of_locCostGe` and `locReg6far_of_locCostGe` with `(hInv Q _).2.2.1`, `.2.2.2` and `Q.LocStd` (first conjunct).
- Instances: (1) `localReg6d_inst_twist` (cost `6`), (2) `_T2`, (3) `_step1` (`locReg6Inv_locStep` at `lvl1_inst_locStep_weight` and `fxyPowGraph_locReg6Inv 2`, every hypothesis discharged), (4)-(6) `_weightExt`, `_edge`, `_gg` (the step lemma and `CircIffLoop`; `Normal` from `lvl1_inst_fail_*`, `CircIffLoop` by `decide`; `LocCostGe far k` stays a hypothesis for all `far`, `k`, as in the check file) and `_conc` (the same at `k = -4` resp. `-6`, from `localReg6d_scost_ge`: `2 n_W - 2 |I| ≤ scost`; these `k` are not the true minima), (7) `_expansion` (the data of `localReg2_inst_expansion`, conjunct (6) added) and `_last` (the check file's shape), (8)-(16) `_T1`, `_T4`, `_P6`, `_R4`, `_R5`, `_R6`, `_R7`, `_R8`, `_P5`, (17)-(20) `_ll_twist`, `_ll_perm`, `_ll_frame`, `_ll_frame2`; all 23 check-file shapes are discharged by file declarations (`shapes_check.lean`).
- Instances (21), (22): two new `LocStep` instances (`localReg6d_inst_locStep_edge3` at `localReg6d_instEdgeG`, `_gg3` at `localReg6d_instGGG`; `hbad`, `hwf`, `hnb` by `decide`, `Normal`, `CircIffLoop` by `decide`) with the pins applied at `k = -6`; `localReg6d_inst_edge3_terms` (`decide`) gives the derivative lists of the three edges of `p.2` the lengths `2, 2, 1` (the branches `[P5, P3]`, `[P6, P4]`, `[D]` of `oe1xDs`), `_gg3_terms` that `lwSplit q.2` has 2 elements (`R7`, `R8` twice); with (3) every one of the 17 term types occurs in a compiled step instance (the merged `lvl1_inst_locStep_edge`, `_gg` have `lwSplit p.2 = []`, resp. `lwSplit q.2 = []`).
- Preflight: section (a) needed no (a′); its statements on `Normal` (not used by the shapes), on the frame hypothesis `p.1.circ = false` and on the hypotheses of the second primitive agree with the proofs. The `lake build` printed right after the last Lean edit of the file: `✔ [3388/3388] Built RBM3D.Graph.LocalRegular6d (3.0s)`.
## (c) Verified Mathlib and core names (script `chk_names.lean`: `env.contains` on 71 identifiers, 63 found by a regex in the file with a core/Mathlib namespace and 8 used through dot notation: found 71, not found none; names verified absent: none searched)
- `Bool`: cond_false, cond_true, not_not
- `Equiv`: refl, sumAssoc, sumCongr, surjective
- `Finset`: card_image_le, card_le_card, card_map, card_univ, mem_filter, univ
- `Fintype`: card
- `Function`: Injective, Injective.eq_iff, Injective.sumMap, Surjective, Surjective.sumMap, comp, comp_def, injective_id, surjective_id
- `List`: Perm, Perm.append_left, Perm.append_right, Perm.cons, Perm.map, Perm.of_eq, Perm.refl, Perm.swap, Perm.symm, Perm.trans, append_assoc, cons_append, countP_map, filter_congr, filter_map, length_map, map_append, map_cons, map_map, map_nil, mem_append, mem_append_left, mem_cons, mem_cons_of_mem, mem_cons_self, mem_flatMap, mem_map, mem_singleton, nil_append, not_mem_nil, perm_append_singleton, perm_middle, reverse_perm
- `Prod`: mk.injEq
- `Real`: rpow_le_rpow_of_exponent_le
- `Setoid`: comap, comap_rel, refl', symm
- `Sum`: inl, inl_injective, inr, inr_injective, map
- `root`: decide_eq_decide, finSumFinEquiv, le_of_eq, le_trans
## (d) Open issues and paper-delta candidates
- Paper-delta candidates (numbered by the dispatcher; also in the module header): `T2216a`: `lem:localregular` (6) is proved for every output as `ord ≥ 2p` (`7_8:815-818`), and `ord ≥ 3p` when the two external vertices of the output differ (`Q.ext 0 ≠ Q.ext 1`), without the assumption `(eq:far_ab)` (`7_8:792`); the paper's route `ord ≥ 3p - n_dv/2 > 2p` (`B:268-277`) is replaced by the minimum over merges `Φ` of the local cost, monotone along `strat_local` (`T2151a`: the far assumption is not needed for (6); `T2151c`: the step claim of `B:275-277` is not used). `T2216b` (on `T2184c`, D492, D525): with the composition (D490), the twists and the step lemma, the edge and `GG` cases omitted at `B:272-275` are proved; the per-case bookkeeping of `B:232-249` (`T2151b`) is not used. `T2216c`: the remark `B:280-283` (`ord ≥ 3p`) holds for the outputs with `Q.ext 0 ≠ Q.ext 1`; the bound `2p` is attained when they are merged (section (a): `explore.py 2 5 900`, minimum of `ord` over the 3303 locally standard states, `4` if `ext0 = ext1`, `6` if `ext0 ≠ ext1`), so the strict inequality `> 2p` of `B:277` fails there.
- O1: in instances (4)-(6) `LocCostGe far k` is a hypothesis for all `far`, `k` (the shapes of the check file); the `_conc` versions and (21), (22) discharge it at `k = -4`, `-6`, not at the true minima (`(1, 1)`, `(-5, -5)`, `(-4, -3)` for the merged inputs: Python values of section (a), not compiled in Lean). O2: `lw_localregular` is an existential statement; its instance reads `outs`, `errs` from the theorem (as the merged `localReg2_inst_expansion`), no list is computed in Lean, and the non-emptiness of the output lists of the merged step instances (3)-(6) is by the section (a) script (208, 134, 1, 42 distinct packed outputs), not by Lean; for (21), (22) it is not checked.
- No obstruction was found; no statement of a merged file or of a Pin was changed, no hypothesis added; nothing needs a dispatcher decision.
