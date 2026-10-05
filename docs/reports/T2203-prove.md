Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 19:31:44 UTC 2026

Model: own Python re-implementation (scratchpad `T2203/core.py`) of `LGraph.scost` (`LocalRegular6a.lean:157`), `skept` (:139), `ScostLL` (:168), `lwPrimMoveSC/MoveOut/Dmove` (:209/:215/:223) with `owxDE` (`LWWeightExp.lean:468`); setoids = all set partitions; pins = check file section 2 (md5 of `T2184-check.lean:358-377` recomputed = `7205e0241cb5f47d0a8efde27f93c5a5`). "iff" = `rest` circled iff loop, "arb" = random `circ` on `rest` (more than any pin assumes); `p`, `q` obey the pin hypotheses (`z = v ↔ cp`, `q.src = q.dst ↔ q.circ`). F is a lead only; every number is from the output pasted in (ii). `Δc := T.scost s' − Γ.scost s₀`, `s₀` = restriction unless stated.

### (i) Exponent table

| row | constant / constraint | value (script) | slack |
|---|---|---|---|
| §55 base | `scost(Γ_p,⊥)`; need `min_s ≥ 2p`, `min_{s,¬s x y} ≥ 3p` over all applications of the three primitives | p=2: 17 applications, minima 4, 6; p=3: 27 applications, 6, 9 | 0 (4 at Dmove, MoveSC; 6 at all three) |
| target 1, α-alone identity | `Δc = #kept A − #kept R + 2 + (el(A at {α}) − 2) + Σ_{c₀ int}(el(X+A_c) − el(X+R_c))`, sum over classes of the old ends of `R,A`, or over all classes | 0 failures / 92793 setoids (both sums) | exact |
| placement (merged lemma), `k ≤ 1` | `T.scost s' − T.scost(split α s') ≥ 0` | min 0 at k=0,1 (all 4 shapes); k=2: −2 (MoveSC, Dmove blue), 0 (MoveOut, Dmove red) | 0 (tight); k=2 truly excluded for MoveSC, Dmove blue |
| MoveSC, α alone | `Δc ≥ 0` | `{z}{u}{v}`, `{z}{u,v}`: 0 (tight, z SC); `{u,z}{v}`, `{v,z}{u}`, `{u,v,z}`: 2 | 0 |
| MoveSC, k=2 (`[u]=[v]=U∋α`) | `Z≠U` collapse, `Z=U` no change | `Z≠U`: min −2 (−1 if exactly one of Z,U external; not negative if both); merge `{Z,U}` works in all 58961 cases tested, never joins two external classes; `Z=U`: 2 | restriction fails by 2; repaired 0 |
| MoveOut, α alone | `Δc ≥ 0` | `{z}{v}{d}`, `{z}{v,d}`, `{z,v}{d}`, `{z,d}{v}`: 0 (tight); `{z,v,d}`: 1 | 0 |
| MoveOut, k=2 (`[v]=[d]=U`) | no collapse (two colours) | `U≠Z`: 0; `U=Z`: 2; witness = restriction in all 2.13 M setoids tested (both modes) | 0 |
| Dmove blue, α alone (15 partitions of `{z,v,a,b}`, min over lw/edge variants) | `Δc ≥ 0` | tight (0): `{z,b}{v}{a}`, `{z,b}{v,a}`; 13 of 15 rows equal F's stated bound, none below; `{z,v,b}{a}`, `{z,a,b}{v}`: lw variant min 1 (edge 2), F states 0; `{z,v,a,b}`: two lw 1, else 2 | 0 on 2 rows; ticket's "light-weight variants tight" not attained (bound true) |
| Dmove blue, k=2 (`[a]=[v]=U`) | rows `Z,U,B` distinct / `Z=B≠U` / `Z=U≠B` / `B=U≠Z` / all equal | 0 / −2 (collapse; −1 with one external) / 1 / 1 / 0; merge `{Z,U}` works in all 9837 cases, never two external | repaired 0 |
| Dmove red, α alone (15 rows) | `Δc ≥ 0` | all rows ≥ 0; min 0 on 12 rows | 0 |
| Dmove red, k=2 (`[b]=[v]=U`) | no collapse | distinct 0; `A=Z≠U` 0; `Z=U≠A` 1; `A=U≠Z` 0; all equal 0; witness always the restriction | 0 |
| collapse instances | `instCyc`: `scost ⊥ = 0`; MoveSC and Dmove blue at `{inr1,α}` | `T.scost = −2`, restriction 0 (not a witness), merge `⊤`: −2 | restriction fails by 2; repaired 0 |
| `Γ_2`, MoveSC k=2 | `s'={x,y,α}` | `T.scost = 5`, restriction `{x,y}`: 6, merge `{x,y,α_0}`: 5 | repaired 0 |
| hypotheses | pins only (`u≠z, z≠v`; `z≠v, z≠d`; `z=v↔cp`, `q` circled iff loop) | no further hypothesis needed: 0 failures in the exhaustive and random runs below | n/a |

### (ii) One concrete nondegenerate instance

`Γ_2 = fxyPowGraph 2` (`E = Fin 2`, `I = Fin 4`, 6 solid, 2 waved edges, `scost ⊥ = 6`; `x=inl 0, y=inl 1, α_0=inr 0, β_0=inr 1` blue block, `α_1=inr 2, β_1=inr 3` red block) and `instCyc` (`E = Fin 0`, `I = Fin 2`, blue `inr0→inr1`, `inr1→inr0`, `scost ⊥ = 0`). `inst.py` asserts every hypothesis (`u≠z`, `z≠v`, `z≠d`, `z=v↔cp`, circled iff loop, `Γ.solid` a permutation of `p::q::rest`) and checks `ScostLL` over ALL setoids of `T`: (1) MoveSC(`α_0`;`x,y`) at `Γ_2`, rest `[lw β_0, lw β_1, x→α_1, α_1→y]`; (2) MoveSC(`inr0`;`inr1,inr1`) at `instCyc`; (3) MoveOut(`x`;`α_0,α_1`) at `Γ_2`; (4) Dmove red(`β_0`; lw `β_0`, `x→α_1`), `z=v`, `cp=true`; (5) Dmove blue(`inr0`; `inr0→inr1`, `inr1→inr0`) at `instCyc` (the added `z→b` is the uncircled loop `(True, False, 0, 0)`); (6)–(9) shapes `P3, P4, D, T3` (T3 at internal `w` and external `x0`) at `E=Fin 2, I=Fin 2`, `w=inr 0`, `s=inr 1`, with the ticket's Perm hypotheses; (10) `(min_s, min_far)` of `T.scost` for (1), (3), (4). No external hypothesis occurs (no limit computation owed).

Command (`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`, scripts in `$SP/T2203/`): `bash run_all.sh > out_all.txt 2>&1` (48 s, 107 lines, md5 `3f9a963c07f77d8aa8993a55da828a09`; runs `table ident decomp place rows rows4 rows2 inst s55 ll(1000) exh`). Below: lines of `out_all.txt` by line number (1-10, 15-22, 24-25, 29, 32, 35, 38-41, 44-48, 51-56, 58, 61, 64-66, 69-86, 88-91, 93-97, 99-103, 105-107); the 12 `placement` lines are 29, 32, 35, 38 shown plus 8 others, and `grep placement out_all.txt | grep -c "= 0  over"` gives 10. `exh.py`: `(nE,nI) ∈ {(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)}` with `rest` ≤ 2 edges (all edge types, `nW ∈ {0,1}`) and `{(1,3),(2,2),(0,4)}` with `rest` ≤ 1, every argument tuple. `ll.py`: 10000 random graphs per primitive and mode (0–2 external, 0–3 internal, `rest` ≤ 4 edges, 6 argument draws each).

```
scost(Gamma_2,bot) = 6
MoveSC(alpha_0;x,y) at Gamma_2
  s=bot (alpha alone)                                  T.scost=6  Gamma.scost(restriction)=6
  s={x,alpha}  (k=1)                                   T.scost=6  Gamma.scost(restriction)=6
  s={x,y,alpha} (k=2)                                  T.scost=5  Gamma.scost(restriction)=6
  repair merge {x,y,alpha_0}: Gamma.scost = 5
MoveOut(x;alpha_0,alpha_1) at Gamma_2
  s=bot                                                T.scost=6  Gamma.scost(restriction)=6
  s={alpha,alpha_0} (k=1)                              T.scost=6  Gamma.scost(restriction)=6
  s={alpha_0,alpha_1,alpha} (k=2)                      T.scost=6  Gamma.scost(restriction)=6
Dmove red (beta_0; lw_beta_0, x->alpha_1) at Gamma_2
  s=bot                                                T.scost=6  Gamma.scost(restriction)=6
  min_s T.scost = 5   min_{not s x y} = 6
instCyc scost(bot) = 0
MoveSC(inr0;inr1,inr1) at instCyc
  s={inr1,alpha}                           T.scost=-2 restriction Gamma.scost=0  merged(top) Gamma.scost=-2
Dmove blue (inr0; inr0->inr1, inr1->inr0) at instCyc
  s={inr1,alpha}                           T.scost=-2 restriction Gamma.scost=0  merged(top) Gamma.scost=-2
target-1 identity (alpha alone; C = classes of old ends of R and A): setoids tested 92793, failures 0; with C = all classes: failures 0
MoveSC(a0;x,y) at Gamma_2, s=bot: #kept(A)=2 #kept(R)=2, +2 (waved), el(A at {alpha})-2 = -1, [a0]: el(X+A)-el(X+R) = 0-1, X=(0, 0, 0, 0)
placement ('dmoveBlue', 'k=2') min(T.scost s - T.scost(split alpha s)) = -2  over 12555 setoids
placement ('dmoveRed', 'k=2') min(T.scost s - T.scost(split alpha s)) = 0  over 13647 setoids
placement ('moveOut', 'k=2') min(T.scost s - T.scost(split alpha s)) = 0  over 7705 setoids
placement ('moveSC', 'k=2') min(T.scost s - T.scost(split alpha s)) = -2  over 7181 setoids
moveSC configs 188 min Delta c by placement: {'alpha alone': 0, 'alpha shares class, k=0': 0, 'alpha shares class, k=1': 0, 'alpha shares class, k=2': -2}
   negative configs 6 by (k, value): {(2, -2): 2, (2, -1): 4}
     e.g. {z}{u,v} alpha in class of u,v lwp=0 lwq=0 k=2 Delta c = -2
moveOut configs 188 min Delta c by placement: {'alpha alone': 0, 'alpha shares class, k=0': 1, 'alpha shares class, k=1': 0, 'alpha shares class, k=2': 0}
   negative configs 0 by (k, value): {}
dmoveBlue configs 1328 min Delta c by placement: {'alpha alone': 0, 'alpha shares class, k=0': 0, 'alpha shares class, k=1': 0, 'alpha shares class, k=2': -2}
   negative configs 6 by (k, value): {(2, -2): 2, (2, -1): 4}
     e.g. {z,b}{v,a} alpha in class of v,a lwp=0 lwq=0 k=2 Delta c = -2
dmoveRed configs 1328 min Delta c by placement: {'alpha alone': 0, 'alpha shares class, k=0': 1, 'alpha shares class, k=1': 0, 'alpha shares class, k=2': 0}
   negative configs 0 by (k, value): {}
moveSC k=2 rows (min,max of Delta c over lw/edge variants and ext flags): {'Z!=U': (-2, 0), 'Z=U': (2, 2)}
moveOut k=2 rows (min,max of Delta c over lw/edge variants and ext flags): {'Z!=U': (0, 0), 'Z=U': (2, 2)}
dmoveBlue k=2 rows (min,max of Delta c over lw/edge variants and ext flags): {'B=U!=Z': (1, 2), 'Z,U,B distinct': (0, 1), 'Z=B!=U': (-2, 0), 'Z=U!=B': (1, 2), 'all equal': (0, 2)}
dmoveRed k=2 rows (min,max of Delta c over lw/edge variants and ext flags): {'A,Z,U distinct': (0, 1), 'A=U!=Z': (0, 2), 'A=Z!=U': (0, 0), 'Z=U!=A': (1, 2), 'all equal': (0, 2)}
   rows with min 0 (tight): ['{z}{u,v}', '{z}{u}{v}']
   rows with min 0 (tight): ['{d,z}{v}', '{v,z}{d}', '{z}{d,v}', '{z}{v}{d}']
   rows with min 0 (tight): ['{b,z}{a,v}', '{b,z}{v}{a}']
   rows where our min < F stated bound (or F row missing): []
   rows attained exactly (our min = F bound): 13 of 15
   dmoveBlue row {b,v,z}{a} min by variant: {'p=edge,q=edge': 2, 'p=lw,q=edge': 1}
   dmoveBlue row {a,b,z}{v} min by variant: {'p=edge,q=edge': 2, 'p=edge,q=lw': 1}
   dmoveBlue row {a,b,v,z} min by variant: {'p=edge,q=edge': 2, 'p=edge,q=lw': 2, 'p=lw,q=edge': 2, 'p=lw,q=lw': 1}
(1) MoveSC(a0;x,y) at Gamma_2                              ScostLL: all 877 setoids of T satisfied; witness kinds {'plain': 862, 'merge': 15}, min slack 0
    (10) min_s, min_far T.scost = (4, 6)
(2) MoveSC(inr0;inr1,inr1) at instCyc                      ScostLL: all 5 setoids of T satisfied; witness kinds {'plain': 4, 'merge': 1}, min slack 0
(3) MoveOut(x;a0,a1) at Gamma_2                            ScostLL: all 877 setoids of T satisfied; witness kinds {'plain': 877}, min slack 0
    (10) min_s, min_far T.scost = (6, 6)
(4) Dmove red(b0; lw_b0, x->a1) at Gamma_2                 ScostLL: all 877 setoids of T satisfied; witness kinds {'plain': 877}, min slack 0
    (10) min_s, min_far T.scost = (5, 6)
(5) Dmove blue(inr0; inr0->inr1, inr1->inr0) at instCyc    ScostLL: all 5 setoids of T satisfied; witness kinds {'plain': 4, 'merge': 1}, min slack 0
(6) P3 shape: MoveOut(w;x0,y0) at E=2,I=2                  ScostLL: all 52 setoids of T satisfied; witness kinds {'plain': 52}, min slack 0
(7) P4 shape: MoveSC(w;s,x0) at E=2,I=2                    ScostLL: all 52 setoids of T satisfied; witness kinds {'plain': 52}, min slack 0
(8) D shape: Dmove red(w; w->x0, w->y0) at E=2,I=2         ScostLL: all 52 setoids of T satisfied; witness kinds {'plain': 52}, min slack 0
(9) T3 shape: Dmove blue(internal w; lw, s->internal w) at E=2,I=2 ScostLL: all 52 setoids of T satisfied; witness kinds {'plain': 52}, min slack 1
(9) T3 shape: Dmove blue(external x0; lw, s->external x0) at E=2,I=2 ScostLL: all 52 setoids of T satisfied; witness kinds {'plain': 52}, min slack 1
p=2: Gamma_p has 6 solid, 2 waved edges; scost(Gamma_p, bot) = 6
   applications: 17  2p=4 3p=6
   min_{s, not s x y} scost over applications = 6  attained at ['Dmove', 'MoveOut', 'MoveSC']
   by primitive (min all, min far): {'MoveSC': (4, 6), 'MoveOut': (6, 6), 'Dmove': (4, 6)}
p=3: Gamma_p has 9 solid, 3 waved edges; scost(Gamma_p, bot) = 9
   applications: 27  2p=6 3p=9
   min_{s, not s x y} scost over applications = 9  attained at ['Dmove', 'MoveOut', 'MoveSC']
   by primitive (min all, min far): {'MoveSC': (6, 9), 'MoveOut': (8, 9), 'Dmove': (6, 9)}
moveSC iff graphs=10000 setoid-checks=1070770 {'plain': 1042093, 'merge': 28677} min slack by kind {'plain': 0, 'merge': 0}
    non-plain ('moveSC', 'merge', 'notalone', 'k=2', ('[u]=[v]=[alpha]', '[z]!=U'), 'repair merge {Z,U} works: True, joins two ext classes: False') 28677
moveSC arb graphs=10000 setoid-checks=1071775 {'plain': 1041491, 'merge': 30284} min slack by kind {'plain': 0, 'merge': 0}
moveOut iff graphs=10000 setoid-checks=1068790 {'plain': 1068790} min slack by kind {'plain': 0}
moveOut arb graphs=10000 setoid-checks=1064911 {'plain': 1064911} min slack by kind {'plain': 0}
dmove iff graphs=10000 setoid-checks=1876020 {'plain': 1871293, 'merge': 4727} min slack by kind {'plain': 0, 'merge': 0}
    non-plain ('dmoveBlue', 'merge', 'notalone', 'k=2', ('[a]=[v]=[alpha]', 'Z=B!=U'), 'repair merge {Z,U} works: True, joins two ext classes: False') 4727
dmove arb graphs=10000 setoid-checks=1829952 {'plain': 1824842, 'merge': 5110} min slack by kind {'plain': 0, 'merge': 0}
EXHAUSTIVE moveSC graph+argument tuples=66492 setoid checks=1498500 {'plain': 1446384, 'merge': 52116} min slack by kind {'plain': 0, 'merge': 0}
EXHAUSTIVE moveOut graph+argument tuples=66492 setoid checks=1498500 {'plain': 1498500} min slack by kind {'plain': 0}
EXHAUSTIVE dmove graph+argument tuples=912432 setoid checks=20780100 {'plain': 20710912, 'merge': 69188} min slack by kind {'plain': 0, 'merge': 0}
```

### Verdicts

- Target 1 (α-alone difference): PASS (identity exact, 0 failures; the localisation to old ends is exact).
- `scostLL_moveSC`: PASS (restriction witness except `k=2`, `Z≠U`; merge `{Z,U}` there; `Z=U` gives `+2`).
- `scostLL_moveOut`: PASS (restriction witness always; no collapse).
- `scostLL_dmove`: PASS (restriction witness except blue `k=2`, `Z=B≠U`, merge `{Z,U}`; red never collapses). Ticket text correction: the light-weight variants of `{z,v,b}{a}`, `{z,a,b}{v}` have min 1, not 0 (no effect on the proof).
- Instances (1)–(10): hypotheses hold at once with no degeneracy; `ScostLL` verified at all setoids. No missing input.

## (b) Script output — Mon Oct  5 20:33:02 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2203`, branch `t/T2203`, HEAD `93bb0070da297ece1539bdffd760165f4903d67f`; sole writable file `RBM3D/Graph/LocalRegular6c.lean` (new module importing `RBM3D.Graph.LocalRegular6b` only). Scripts and raw outputs: `SP/T2203/` (`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`). No port from RBM1D/RBM2D (nothing copied: no file:line, commit or diff-stat owed).
### Build, direct compile, registry pre-check, full build
```
Mon Oct  5 20:31:07 UTC 2026
$ lake build RBM3D.Graph.LocalRegular6c 2>&1 | tail -1
Build completed successfully (3387 jobs).
$ lake env lean RBM3D/Graph/LocalRegular6c.lean > direct.txt 2>&1; echo exit=$?; wc -c < direct.txt   # direct compile of the committed file
exit=0
       0
wall 15 s
Mon Oct  5 20:31:24 UTC 2026
$ lake env lean precheck.lean > precheck_full.txt 2>&1; echo exit=$?; head -1 precheck_full.txt; wc -l < precheck_full.txt; grep -c error precheck_full.txt   # registry pre-check (DECISIONS §20 (2)); precheck.lean = `import RBM3D`, `import RBM3D.Graph.LocalRegular6c`, blank, `#assert_rbm_axioms`
exit=0
axiom audit: 6017 theorems, 2105 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
     217
0
Mon Oct  5 20:31:52 UTC 2026
$ lake build   # full library in the worktree (the hub adds the root import at merge; the module itself is covered by the pre-check)
Build completed successfully (4006 jobs).
```
### Axioms, the three Pins, the fourteen shapes of the check file
```
Mon Oct  5 20:32:15 UTC 2026
$ lake env lean axioms.lean   # Lean.collectAxioms over every constant of the module (env.header.moduleData), then #print axioms of the 3 pinned theorems and of target 1
module RBM3D.Graph.LocalRegular6c: 151 constants (133 theorems, 18 definitions, 0 other); user-named public: 28; axioms used by any of them: [Quot.sound, Classical.choice, propext]; constants with a non-standard axiom: 0 
'RBM.Graph.scostLL_moveSC' depends on axioms: [propext, Classical.choice, Quot.sound] 
'RBM.Graph.scostLL_moveOut' depends on axioms: [propext, Classical.choice, Quot.sound] 
'RBM.Graph.scostLL_dmove' depends on axioms: [propext, Classical.choice, Quot.sound] 
'RBM.Graph.localReg6c_alone_diff' depends on axioms: [propext, Classical.choice, Quot.sound] 
Mon Oct  5 20:32:18 UTC 2026
$ lake env lean pins_check.lean   # the 3 Pins of check-file section 2 in RBM.Graph.T2203Check, each `theorem chk_x : XPin := @name`
pins: 3 theorems checked by `@name`; axioms used: [Quot.sound, Classical.choice, propext]
exit=0
$ lake env lean shapes_check.lean   # the 14 Prop-valued shapes of check-file section 3 (S1..S14), each `theorem tN : SN := <file instance>`
shapes: 14 theorems checked by the file instances; axioms used: [Quot.sound, Classical.choice, propext]
exit=0
$ md5 of T2184-check.lean:358-377 and of T2203-check.lean:192-211 (the c3 pin block of the check file); diff of the two
7205e0241cb5f47d0a8efde27f93c5a5
7205e0241cb5f47d0a8efde27f93c5a5
DIFF EMPTY (pins verbatim)
```
### Diff scope, forbidden tokens, name clash, counts, unused hypotheses
```
Mon Oct  5 20:32:24 UTC 2026
$ git diff --stat main...t/T2203; git diff --name-only main...t/T2203
 RBM3D/Graph/LocalRegular6c.lean | 1759 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 1759 insertions(+)
RBM3D/Graph/LocalRegular6c.lean
$ grep -c "sorry\|admit\|native_decide\|^axiom" F; grep -c "^open Classical$" F; grep -n "^import" F; grep -c maxHeartbeats F; wc -l F
0
0
6:import RBM3D.Graph.LocalRegular6b
0
    1759 RBM3D/Graph/LocalRegular6c.lean
Mon Oct  5 20:32:24 UTC 2026
$ bash clash.sh   # every public name of the new file (pubnames.txt: 24 names, the non-private theorem/def lines) as a whole word
public names checked: 24; hits outside the new file (worktree): 0
worktree, prefix localReg6c_ and the three pin names outside the new file: 0
main 9e0d6a7: files of main matching the prefix or the pin names: 0; module file RBM3D/Graph/LocalRegular6c.lean on main: 0
Mon Oct  5 20:32:29 UTC 2026
$ python3 count.py   # declaration and row counts of the file
private theorem 63 | private def 13 | public theorem 21 | public def 3 | example 1 | open Classical in 69 | Prop-valued defs 0
section Rows: 384 lines; 32 row lemmas; 88 leaf tactics (simp / exact absurd)
$ lake env lean nohyp_copy.lean > nohyp_out.txt 2>&1; echo exit=$?; wc -c < nohyp_out.txt; grep -c _nohyp nohyp_copy.lean   # the module text plus copies of scostLL_moveSC, scostLL_moveOut without the hypotheses hu hv resp. hv hd
exit=0
       0
2
```
### Targets (`extract.py F pub`: line, statement up to the first depth-0 `:=`; the four public non-instance declarations)
```
282: theorem localReg6c_alone_diff (Γ : LGraph E I) (rest R : List (SEdge (E ⊕ I))) (hΓ : Γ.solid.Perm (R ++ rest)) (c : ℂ) (A : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) (C : Finset (Quotient (Setoid.comap (owxEmb 1) s'))) (hR : ∀ e ∈ R, Quotient.mk (Setoid.comap (owxEmb 1) s') e.src ∈ C ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') e.dst ∈ C) (hA : ∀ e ∈ A, ∀ w ∈ [e.src, e.dst], w = Sum.inr (Sum.inr 0) ∨ ∃ v, w = owxEmb 1 v ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') v ∈ C) : (({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) c A W).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') = ((scostLL_kept A s').length : ℤ) - ((scostLL_kept R (Setoid.comap (owxEmb 1) s')).length : ℤ) + 2 * (W.length : ℤ) + (scostLL_el (scostLL_clsPat A s' (Quotient.mk s' (Sum.inr (Sum.inr 0)))) - 2) + ∑ c₀ ∈ C, (if c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s') then scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) - scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀) else 0)
1123: theorem scostLL_moveSC (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (hu : u ≠ z) (hv : z ≠ v) (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest)) : LGraph.ScostLL Γ (lwPrimMoveSC Γ rest z u v)
1196: theorem scostLL_moveOut (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I) (hv : z ≠ v) (hd : z ≠ d) (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨false, false, z, d⟩ :: rest)) : LGraph.ScostLL Γ (lwPrimMoveOut Γ rest z v d)
1431: theorem scostLL_dmove (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp : Bool) (q : SEdge (E ⊕ I)) (hcp : z = v ↔ cp = true) (hq : q.src = q.dst ↔ q.circ = true) (hperm : Γ.solid.Perm (⟨true, cp, z, v⟩ :: q :: rest)) : LGraph.ScostLL Γ (lwPrimDmove Γ rest z v q)
```
### Compiled instances (`extract.py F inst | cut -c1-200`: 3 maps and 17 instance theorems, the target-1 `example`; its source head follows)
```
1506: def localReg6c_mapXYA : Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1) → ℕ
1511: def localReg6c_mapCyc : Fin 2 ⊕ (Fin 2 ⊕ Fin 1) → ℕ
1515: def localReg6c_mapInj : Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1) → ℕ
1520: theorem localReg6c_inst_moveSC : LGraph.ScostLL (fxyPowGraph 2) (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, 
1528: theorem localReg6c_inst_moveSC_values : (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, fals
1555: theorem localReg6c_inst_moveSC_cyc : LGraph.ScostLL localReg6b_instCyc (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1))
1561: theorem localReg6c_inst_moveSC_cyc_values : (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1)).scost (Setoid.ker localReg6c_mapCyc) = -2 ∧ ¬ localReg6b_instCyc.scost (Setoi
1579: theorem localReg6c_inst_moveOutPerm : (fxyPowGraph 2).solid.Perm ((⟨true, false, Sum.inl 0, Sum.inr 0⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨false, false, Sum.inl 0, Sum.inr 2⟩ :: [⟨true, true, Sum
1592: theorem localReg6c_inst_moveOut : LGraph.ScostLL (fxyPowGraph 2) (lwPrimMoveOut (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3,
1600: theorem localReg6c_inst_dmovePerm : (fxyPowGraph 2).solid.Perm ((⟨true, true, Sum.inr 1, Sum.inr 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨false, false, Sum.inl 0, Sum.inr 2⟩ :: [⟨true, false, Sum.i
1609: theorem localReg6c_inst_dmove : LGraph.ScostLL (fxyPowGraph 2) (lwPrimDmove (fxyPowGraph 2) [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Su
1617: theorem localReg6c_inst_dmove_cyc : LGraph.ScostLL localReg6b_instCyc (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩)
1622: theorem localReg6c_inst_dmove_cyc_values : (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩).scost (Setoid.ker localReg6c_mapCyc) = -2 ∧ ¬ localReg6
1643: theorem localReg6c_inst_P3 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : Sum.inr x ≠ v) (h2 : Sum.inr x ≠ q.1.dst) (hperm : Γ.solid.Perm (⟨true, f
1652: theorem localReg6c_inst_P4 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : q.1.src ≠ Sum.inr x) (h2 : Sum.inr x ≠ v) (hperm : Γ.solid.Perm (⟨true, f
1660: theorem localReg6c_inst_D (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : Sum.inr x ≠ v) (hq : q.1.src = q.1.dst ↔ q.1.circ = true) (hperm : Γ.solid
1668: theorem localReg6c_inst_T3 (m : ℂ) (Γ : LGraph E I) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q.1.src = q.1.dst ↔ q.1.circ = true) (hperm : Γ.solid.Perm (⟨true, true, Sum.inr x, S
1676: theorem localReg6c_inst_ET3 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q.1.src = q.1.dst ↔ q.1.circ = true) (hperm : Γ.solid.Perm (⟨true, true, x, x⟩ :
1685: theorem localReg6c_inst_s55 : ((∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)), 4 ≤ (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, 
1716: example
1742: theorem localReg6c_inst_alone_values : (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false
example := localReg6c_alone_diff (fxyPowGraph 2)
  [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
    ⟨false, false, Sum.inr 2, Sum.inl 1⟩]
  [⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩] localReg6b_inst_contractPerm 1
  [⟨true, false, owxEmb 1 (Sum.inl 0), Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 (Sum.inl 1)⟩]
  [⟨false, true, owxEmb 1 (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] (Setoid.ker localReg6c_mapInj)
```
### Narrative (facts only)
- File `RBM3D/Graph/LocalRegular6c.lean`: 1759 lines (ticket estimate 1700-2400, stop threshold 2500). Public: `localReg6c_alone_diff` (target 1), the three Pins, 3 maps, 17 instance theorems, 1 `example`; 63 private theorems and 13 private defs; 69 `open Classical in`, no file-level `open Classical`; no Prop-valued definition (`count.py`: 0; `precheck_full.txt` has no line naming the module), so no registry line is owed.
- Target 1 (`localReg6c_alone_diff`, line 282): `scostLL_fresh_scost` at `Γ_rest.owxExt (owxEmb 1) c A W` with `α` alone, minus `scostLL_scost_eq` of `Γ` at `s₀ = comap (owxEmb 1) s'`; `Γ.solid ~ R ++ rest` through `scostLL_kept_perm`, `scostLL_clsPat_perm`; the sum is localised to `C` by `scostLL_sum_support`, the summand being `0` off `C` (`scostLL_clsPat_zero_of_ends`; for `A` the private `localReg6c_end_ne`: an end is `α` or an old vertex whose class lies in `C`). The statement is the ticket's recommended shape with `2 * |W|` for the waved edges, `W`, `A`, `C` arbitrary under the end hypotheses `hR`, `hA`.
- Per-class bound: private `localReg6c_dlb A R` is `0` if `A = R`, `0` if `R` has two colours or two ins or two outs, else `-1`; `localReg6c_dlb_le : dlb A R ≤ el (X + A) - el (X + R)` for every residual `X` is `scostLL_elem_E0` and `scostLL_elem_E6col/out/in` (`scostLL_elem_E3`, the tautology of T2195 audit O1, is not cited).
- `localReg6c_alone_ge` (`A ~ A₀.map emb ++ Ain.map mkIn ++ Aout.map mkOut`: the added old edges, the added edges `w → α` and `α → w`) gives `localReg6c_lb ≤ T.scost s' - Γ.scost s₀` from target 1, `localReg6c_clsPat_eq`, `localReg6c_kept_length` (class pattern and kept count of an edge list as sums over its descriptors) and `localReg6c_dlb_le` termwise. `localReg6c_k2_ge` (`α` in a class, `scostLL_kept Aα s' = []`): `T.scost s' = ({Γ with solid := A₀ ++ rest}).scost s₀ + 2 |W|` by `scostLL_fresh_scost` (`α` not alone), then `scostLL_local_diff_C`; it gives `localReg6c_lb2 ≤ T.scost s' - Γ.scost s₀`.
- Rows: `localReg6c_row_*` (`count.py`: 32 lemmas, 88 leaf tactics) state `0 ≤ localReg6c_lb ...` / `localReg6c_lb2 ...` on the equality pattern of the classes of the named vertices (three for `MoveSC`, `MoveOut`, four for `Dmove`): restricted-growth `rcases eq_or_ne` trees closed by `simp` (the 15 partitions of `{z, v, a, b}` of F §4.5 for blue and for red `q`, split by the light-weight flags `cp`, `c`, which are `subst`ed when true). The two collapse rows are hypotheses, not cases: `localReg6c_row_sc_k2_raw (h : Z = U)`, `localReg6c_row_dmb_k2_ff (hnc : ¬ (Z = B ∧ Z ≠ U))`. The abstract lemmas take the finset of named classes by membership (`hC : ∀ x, x ∈ C ↔ ...`): the `Finset.insert` instance of `Quotient` differs from the classical one (error message of the first attempt).
- Pins: `localReg6c_ll_of_cases` (`α` alone: the restriction is the witness; not alone and `¬ K2` (`k ≤ 1`): `scostLL_split`, `scostLL_split_comap`, `scostLL_split_alone` and the merged `localReg6b_inst_*_placement`; `K2` (`k = 2`): below). At `k = 2`: `MoveSC` with `[u] ≠ [z]` is the merged `localReg6b_inst_moveSC_k2`; `MoveSC` with `[u] = [z]`, `MoveOut` and red `Dmove` are `localReg6c_k2_ge` with the restriction; blue `Dmove` with `[z] = [b] ≠ [v]` (`cp = false`, `c = false` from the classes and the Pin's `↔` hypotheses) is `scostLL_fresh_dropped` (all three added edges dropped) with `scostLL_repair Γ rest true z v a b v s₀`.
- Hypotheses: `hu`, `hv` of `scostLL_moveSC` and `hv`, `hd` of `scostLL_moveOut` are unused (`nohyp_copy.lean`, the module text plus copies of the two theorems without them, compiles with exit 0); of the `↔` hypotheses of `scostLL_dmove` only `cp = true → z = v` and `c = true → a = b` are used (`dm_weak_copy.lean`, the `Dmove` section with its `↔` hypotheses weakened to `→`, compiled at 20:34:36 UTC: its only errors are at lines 1665, 1673, 1681, the `⟨_, _⟩` arguments of `localReg6c_inst_D`, `_T3`, `_ET3`).
- Instances: concrete costs by the private `localReg6c_scost_ker` (the cost at `Setoid.ker f` as a decidable expression; `rw` then `decide`): (1') `5`, `6`, `5`; (2'), (5') `-2` and `¬ (0 ≤ -2)` (the restriction is the trivial setoid, cost `0`: the repair is forced); target 1 at `Γ_2` and the trivial setoid: `6` and `6` (`localReg6c_inst_alone_values`). The merged setoid of (1') is shown equal to a `Setoid.ker` of an explicit map by `Setoid.ext` and `decide`. (6)-(9): `oe1xP3` (`List.Perm.swap` of its two added edges), `oe1xP4`, `oe1xD`, `owxT3`, `owxET3` through `LGraph.ScostLL.of_perm`; (10): `localReg6b_inst_s55` at (1), (3), (4).
- Preflight: its ticket-text correction (the light-weight variants of `{z,v,b}{a}`, `{z,a,b}{v}` have minimum 1, not 0) has no effect on the proofs; section (a) needed no (a′). The direct compile takes 15 s; no `maxHeartbeats` option.
## (c) Verified Mathlib and core names (script `chk_names.lean`: `env.contains` on 69 names the file uses or relies on: found 69, not found none; names verified absent: none searched)
- `Finset`: `card_image_of_injective`, `ext`, `filter`, `image_image`, `mem_filter`, `mem_insert`, `mem_singleton`, `mem_univ`, `sum_congr`, `sum_insert`, `sum_le_sum`, `sum_singleton`, `sum_sub_distrib`; `Function`: `Injective`, `Injective.eq_iff`, `comp_def`; `Iff.rfl`; `Or.inl`, `Or.inr`; `Nat.cast_one`; `Prod.ext_iff`
- `List`: `Perm.append_left`, `Perm.cons`, `Perm.length_eq`, `Perm.mem_iff`, `Perm.refl`, `Perm.swap`, `filter_congr`, `filter_cons`, `filter_eq_self`, `filter_nil`, `length_append`, `length_map`, `length_singleton`, `map_map`, `mem_append`, `mem_cons`, `mem_map`, `not_mem_nil`, `perm_middle`, `sum_cons`, `sum_nil`
- `Quotient`: `exact`, `inductionOn`, `lift`, `mk`, `sound`; `Setoid`: `comap`, `comap_rel`, `ext`, `ker`, `ker_def`; `Sum`: `elim`, `inl`, `inr`
- root: `add_assoc`, `add_comm`, `add_zero`, `eq_false`, `eq_or_ne`, `eq_true`, `le_trans`, `ne_eq`, `not_false_eq_true`, `or_false`, `or_true`, `sub_self`, `true_and`, `zero_add`
## (d) Open issues and paper-delta candidates
- Paper-delta candidates (numbered by the dispatcher; also in the module header): `T2203a` (on `T2184c`/D492, the edge and `GG` cases omitted at `B:272-275`): the local lemma for `MoveSC`, `MoveOut`, `Dmove` (F §4.5) is proved; with c2 every edge, `GG` and weight term of `strat_local` reduces to primitives with a proved local lemma (the paper's per-term bookkeeping `B:213-262`); instances (6)-(9) apply the Pins at `P3`, `P4`, `D`, `T3`. `T2203b` (extends D491/`T2195b`): the 2-cycle collapse also occurs in `MoveSC` and blue `Dmove` at `k = 2` (the terms `P4`, `D`, `T3`, `R7`, `R8` are built from these primitives; the restriction is not a witness, instances (2), (5)), repaired by merging the two classes of the cycle, never two external ones (`scostLL_repair`); `MoveOut` and red `Dmove` never collapse (two colours). `T2203c` (proof route, not a statement difference): the hand rows of F §4.5 are replaced by one per-class pattern bound (`localReg6c_dlb`) and a finite case split on the equality pattern of the classes of the named vertices.
- O1 (statement forms chosen, listed above by script): target 1 has `W`, `A`, `C` general with the end hypotheses `hR`, `hA`; the only public API for c4 is the three Pins and target 1, every other helper is `private`. O2: the instance of target 1 is the anonymous `example` of the listing (line 1716), its values are `localReg6c_inst_alone_values`. O3: the Pin hypotheses `hu`, `hv`, `hd` are not used by the proofs (narrative); the Pins are unchanged.
- No statement of a merged file or of a Pin was changed, no hypothesis was added, no obstruction was found; nothing needs a dispatcher decision; no (a′) corrections were needed.
