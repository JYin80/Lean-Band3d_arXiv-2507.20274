Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 14:01:31 UTC 2026

Citations: `6a:N`..`6d:N` = `RBM3D/Graph/LocalRegular6a.lean`..`6d`; `BEW` = `BAExpandW.lean`; `BGG` = `BAGGOp.lean`; `BV` = `BAVocab.lean`; `BAt` = `BAAtomic.lean`. Scripts are Python in `$SP` = the scratchpad dir `T2426/` (no Lean). `BAScostLL Γ T` = for every merge `s ⊇ atoms(T)` there is `s₀ ⊇ atoms(Γ)` that separates every external pair `s` separates, with `scostA Γ s₀ ≤ scostA T s` (T2397 probe 81-85); `scostA = (promoteC Γ).scost` (`BAt:96`, `6a:157`). The checker (`sll.py`) tests the genuine statement for all merges and all separation patterns of `NE` external vertices; its cost agrees with the T2397 cost code: `python3 xcheck.py` gives `sll.costs vs phi.phi_g: 4000 random graphs (random circles), mismatches 0`.

### (i) Exponent table

No exponent, `g`, `κ`, `c`, `ρ` enters (C1: counts only). No external hypothesis: `fxyPowGraph_locCostGe` (6a:927) is merged, so there is no limit computation.

| row | value | constraint | slack |
|---|---|---|---|
| start threshold `Φ^all` (BAInit) | `2p` | `Φ^all(Q) ≥ 2p`, every `Q ∈ (ofLGraph Γ_p).partition` | min over the `2^{2p}` terms = 2, 4, 6, 8 for p = 1..4: slack 0 |
| start threshold `Φ^far` | `3p` | `Φ^far(Q) ≥ 3p` if atoms of x, y differ (vacuous otherwise) | min = 3, 6, 9, 12: slack 0; vacuous terms 1/4, 7/16, 37/64, 175/256 |
| Lemma A step | +1 per added circled loop | `scost Γ s ≤ scost (e :: Γ) s` (6a:434) | ≥ 0 |
| Lemma B (`T → Q ∈ splitG T`) | `s₀ = s` | `BAScostLL T Q` | min per-merge slack 0 (witness below) |
| S1 | per-merge slack 0; E13 `ΔΦ^all` ≥ (0,0) both ext, (0,2) other | `BAScostLL Γ T` | 0 |
| E1 | per-merge slack 2; E13 `ΔΦ^all` ≥ 2 | same | 2 |
| E2 | per-merge slack 1; E13 `ΔΦ^all` ≥ 0 | same | 1 (E13: 0) |
| macroA, macroB intermediates | per-merge slack 0; E13 (0,0) | same | 0 |

Five-shape table (the builder output, the band primitive its atomic image equals, the band lemma). `img` = merge along atoms (`BAt:108`). Band lemmas quantify over all setoids and return an arbitrary `s₀` (`6a:168`), so they apply on the atom-quotient graph `img Γ` only (there every setoid is `⊇` atoms), transferred by `scost_relabel` (6a:401).

| shape | Lean term | image of T = | band lemma (hypotheses) |
|---|---|---|---|
| S1 | `BAGGOp_A1` (BGG:102; first term of `gg2`, BGG:73), `p = Ǧ_{xy}`, `q = Ǧ_{y'x}` | `Contract(z=[x]; u=[y'], v=[y])` (`lwPrimContract` 6a:233), then `[y]~[y']` makes `u→v` an uncircled loop (dropped, 6a:463) | `scostLL_contract` 6b:1391 (`u≠z`, `z≠v`, perm) |
| E1 | `lanlwT1` (BEW:122), `M`-split of `G_{αy}`, `[x]≠[y]` | merge-and-drop of `x→y`, then `Loop(z)` (`lwPrimLoop` 6a:195) | `scostLL_loop` 6b:621 (none) |
| E2 | any output of `BAGraph.splitG` (BV:170) of any builder term | `T`'s image = `Q`'s image minus extra circled loops | Lemma A 6a:434, repeated |
| macroA | `lanlwT1` split, `[x]=[y]`, `x≠y` | `MoveLoop(z)` (`lwPrimMoveLoop` 6a:204) | `scostLL_moveLoop` 6b:638 (perm of the circled loop) |
| macroB | `lanlwD` (BEW:133), `q` blue `u→w`, `w∈[x]`, only `G_{αw}` split | `MoveSC(z=[x]; u, v=[y])` (`lwPrimMoveSC` 6a:209) | `scostLL_moveSC` 6c:1123 (`u≠z`, `z≠v`) |

**Macro (b) primitive: no new `Dmove`-size lemma is needed.** For blue `q` the intermediate is `MoveSC` at `z=[x]`; for red `q` (the split edge is the first derivative edge) it is `MoveOut(z; v, d)` (`lwPrimMoveOut` 6a:215, `scostLL_moveOut` 6c:1196). `Dmove` (6a:223, `scostLL_dmove` 6c:1431) is not used. Graph-level evidence (the check T2397 limit (8) lacked) is in (ii), `imgcheck.py`.

Packed form: `localReg6d_locCostGe_term` (6d:955) packs `ScostLL P.g T` for the **pre-partition** `T`, and its partition outputs by `scost_partition_ge` (6a:503). The BA twin needs the same two steps: `BAScostLL Γ T` for the builder term (statements above), then Lemma B for `T.splitG`; plus the relabel along `packMerge` (BV:220), which changes the vertex types.

### (ii) One concrete nondegenerate instance

`E = Fin 2` (vertices 0, 1 external), `I` internal vertices 2.., `Γ` BA-normal (every solid edge circled, no `=`-dotted edge), one waved edge. Hypotheses at the witness: `p = Ǧ_{xy}`, `q = Ǧ_{y'x} ∈ lwSplit p.2`; for macroB `u=0`, `v=1`, `x=2` in three distinct atoms; macroA has `x=2`, `y=3` in one atom. `Γ*` = path `0→2→1` (S1: `y=1`, `y'=0`, `x=2`; E1: `[2]≠[1]`; macroB `q = 0→2`). Builders transcribed from `BEW:122-134`, `BGG:73-84` (`sll.py`).
```
$ cd $SP && python3 witness.py
Gamma* = path 0->2->1: (2, 3, [(True, True, 2, 1), (True, True, 0, 2)], 1, []) atoms [[0], [1], [2]]
S1   = gg2 A1 (y=1, y'=0, x=2)     merges of T checked     2  violations 0  min per-merge slack 0  ord(Gamma)=2 atoms [[0, 1, 4], [2, 3]]
E1   = lanlwT1 split=[2] ([x]!=[y]) merges of T checked     5  violations 0  min per-merge slack 2  ord(Gamma)=2 atoms [[0], [1, 2, 3], [4]]
macroB = lanlwD split={e2}         merges of T checked    15  violations 0  min per-merge slack 0  ord(Gamma)=2 atoms [[0], [1], [2, 3], [4]]
macroA = lanlwT1 split, x~y (x=2,y=3) merges of T checked    15  violations 0  min per-merge slack 0  ord(Gamma)=1 atoms [[0], [1], [2, 3, 4], [5]]
E2   = gg2 AD split={0}            merges of T checked    15  violations 0  min per-merge slack 1  ord(Gamma)=1 atoms [[1], [3], [0, 2, 4], [5]] [classified E2]
Lemma B: BAScostLL T Q for all 8 outputs Q of splitG(gg2 AD term): 0 violations
Q* = Gamma_2, all circled: [(True, True, 3, 3), (True, True, 0, 2), (True, True, 2, 1), (False, True, 5, 5), (False, True, 0, 4), (False, True, 4, 1)] waves 2
S1   at Q*                         merges of T checked    52  violations 0  min per-merge slack 0  ord(Gamma)=2
E1   at Q*                         merges of T checked   203  violations 0  min per-merge slack 2  ord(Gamma)=2
macroB at Q* (q = 0->2)            merges of T checked   877  violations 0  min per-merge slack 0  ord(Gamma)=2
```
(`macroA` graph: edge `2→3` with `M`-dot `(3,2)`; `E2` graph: edges `2→3`, `0→2`, red `0→3`; `Q*` = `Γ_2` of `fxyPowGraph 2` with every edge circled, the start term of BAInit; `p = (2→1)`, `q = (0→2)`.) BAInit (`ofLGraph (fxyPowGraph p)`, `baSplitSolid`, `Γ_p` as `LocalRegular.lean:1354`):
```
$ cd $SP && python3 binit.py
p=1: terms 4 (2^(2p)=4), min Phi^all 2 (2p=2), min Phi^far 3 (3p=3), terms with atoms of x,y equal 1, BAScostLL(Gamma_p, Q) violations 0, min slack 0
p=2: terms 16 (2^(2p)=16), min Phi^all 4 (2p=4), min Phi^far 6 (3p=6), terms with atoms of x,y equal 7, BAScostLL(Gamma_p, Q) violations 0, min slack 0
p=3: terms 64 (2^(2p)=64), min Phi^all 6 (2p=6), min Phi^far 9 (3p=9), terms with atoms of x,y equal 37, BAScostLL(Gamma_p, Q) violations 0, min slack 0
p=4: terms 256 (2^(2p)=256), min Phi^all 8 (2p=8), min Phi^far 12 (3p=12), terms with atoms of x,y equal 175, BAScostLL(Gamma_p, Q) violations 0, min slack 0
```
E13 rerun at a fresh seed (`r_shapes.py` = copy of T2397's; 1:45 wall, `time.out`):
```
$ cd $SP && python3 r_shapes.py 100000 20261011 > e13_seed20261011.out; grep -E 'E1 \[y\]|S1 y|transfer intermediate|total checks|min \(' e13_seed20261011.out
  E1 [y] external                                      checks    36,702  violations 0
  E1 [y] internal                                      checks    13,064  violations 0
  S1 y,y' two atoms: both ext                          checks    10,558  violations 0
  S1 y,y' two atoms: both int                          checks     1,881  violations 0
  S1 y,y' two atoms: one ext                           checks    14,747  violations 0
  macro(a) P -> transfer intermediate                  checks    50,234  violations 0
  macro(b) P -> transfer intermediate (blue q)         checks    52,200  violations 0
  macro(b) P -> transfer intermediate (red q)          checks    51,861  violations 0
  total checks 9,155,330, violations 0
  min (Phi^all(child) - Phi^all(parent), ord(child) - ord(parent)) per shape: E1 [y] external: (2, 0), E1 [y] internal: (2, 2), E2: (0, 2), S1 y,y' two atoms: both ext: (0, 0), S1 y,y' two atoms: both int: (0, 2), S1 y,y' two atoms: one ext: (0, 2), macro(a) intermediate: (0, 0), macro(b) intermediate: (0, 0)
```
The genuine local lemma, all outputs of `lw2`, `lw4`, `gg2`, `gg4`, `lanlw` (`T1`, `D`) and their `splitG` at random normal parents (`drive.py 100000 20261011 NE XM`; NE = 4: 20000 parents; `x` external allowed in `any`); classes are outputs/violations/min per-merge slack; `drive2.py 20000 20261012 NE XM` checks Lemma B and the pre-partition `BAScostLL Γ T`:
```
$ cd $SP && python3 summ2.py | cut -c1-230
NE=2 x=any parents 100000 total 7,920,802 outputs, violations 0; outputs/violations/min-slack: S1 49366/0/0; E1 49243/0/2; E2 346960/0/1; mA 50757/0/0; mB 76463/0/0; rest 7348013/0/0
NE=3 x=any parents 100000 total 7,920,268 outputs, violations 0; outputs/violations/min-slack: S1 62460/0/0; E1 62534/0/2; E2 349635/0/1; mA 37466/0/0; mB 56688/0/0; rest 7351485/0/0
NE=3 x=int parents 100000 total 7,902,031 outputs, violations 0; outputs/violations/min-slack: S1 62455/0/0; E1 62373/0/2; E2 342199/0/1; mA 37627/0/0; mB 56782/0/0; rest 7340595/0/0
NE=4 x=any parents 20000 total 1,578,546 outputs, violations 0; outputs/violations/min-slack: S1 14131/0/0; E1 14291/0/2; E2 61225/0/1; mA 5709/0/0; mB 8570/0/0; rest 1474620/0/0
NE=2, x any      Lemma B (T -> splitG T): 1,586,840 checks, 0 violations; pre-partition (Gamma -> T): 350,855 checks, 0 violations
NE=3, x any      Lemma B (T -> splitG T): 1,586,840 checks, 0 violations; pre-partition (Gamma -> T): 350,855 checks, 0 violations
NE=3, x int      Lemma B (T -> splitG T): 1,584,840 checks, 0 violations; pre-partition (Gamma -> T): 350,605 checks, 0 violations
```
The images equal the band primitives (graph-level, up to relabelling; a difference of extra circled loops is allowed, as Lemma A raises the cost):
```
$ cd $SP && python3 imgcheck.py
  E1 = merge-and-drop + Loop           instances 19,695  image mismatches 0
  S1 = Contract, then [y]~[y']         instances  6,278  image mismatches 0
  macroA = MoveLoop                    instances  9,768  image mismatches 0
  macroB blue = MoveSC                 instances  2,935  image mismatches 0
  macroB red = MoveOut                 instances  2,824  image mismatches 0
```

### Verdicts

- **Target 1 (vocabulary): PASS.** Interface notes: `BAShape` needs `deriving DecidableEq` (T2423's probe `:74-77` has it, the T2397 probe 123 does not; `baStep_of_simC` uses `by_cases sh = band`); `BAFinal` is copied vertex-level and restated at `BAGraph.LocStd` by L3b4′ (L4-C3).
- **Target 2 (Lemma B, E2): PASS.** `BAScostLL T Q` for every `Q ∈ T.splitG` with `s₀ = s`: 0 violations in the Lemma B lines above, and `imgcheck.py` shows `T`'s image is `Q`'s minus circled loops.
- **Target 3 (five lemmas): PASS** as term lemmas `BAScostLL Γ T'` (`T' ∈ splitG` of the builder term; no atom hypothesis is needed numerically, so the primitives' `u≠z`, `z≠v` may be assumed and need not be proved away). Three constraints for 1b. (1) The packed `BAShapeLL sh T` is false for an arbitrary `BTStep` (a step with a junk `sh`-tagged output), so the packed theorem needs a hypothesis that the `sh`-tagged outputs of `T` are packaged outputs of the builder term (T2423's `outsT`, probe `:85`). (2) T2423 `(a)` F1 (`T2423-prove.md:83`): `s1` is never assigned there (`A1` is the band's `R2 (δ,m)`), so `BAShapeLL s1` is vacuous in that tagging; `BAScostLL Γ A1` is true regardless (S1 and `A1 [y]=[y']` both 0 violations) and is proved here as the ticket asks. (3) Band lemmas apply on `img Γ`, not on `promoteC Γ` (6a:168 returns an arbitrary `s₀`).
- **Target 4 (BAInit): PASS** (`binit.py`; proof route: Lemma B + `fxyPowGraph_locCostGe`, with the `packMerge` relabel, 6a:401).
- **Target 5 (instances): PASS**: witnesses above, one per shape, each with every hypothesis discharged (Γ normal, shape atom conditions, `q ∈ lwSplit p.2`); `BAInit 2` has 16 terms.
- **Target 6 (C1): PASS**; target 7: none. **(iv) predicted lines: not given** (stage 1a excludes size estimates); the ticket's rule "`BAScost2.lean` if more than 1,500" is for 1b to apply by `wc -l`.

## (a′) Preflight corrections — Sun Oct 11 15:04:01 UTC 2026

- (a)'s table row E2 cites "Lemma A 6a:434, repeated". `LGraph.scost_cons_loop_ge` (6a:434) needs a loop (`e.src = e.dst`); the circled edge of an extra output joins two distinct vertices of one atom, so Lemma A is used in the form "the ends lie in one class" (`BAScost_cons_inclass_ge`, `BAScost.lean:222`, the same proof). No verdict changes.
- (a)'s table describes the macro (b) intermediate as `lanlwD` "with only `G_{αw}` split" (the two other derivative edges uncircled). The transfer graph of the frame (`t/T2423` probe `splitOuts`, `tr`) also circles `G_{y'β}`, `G_{βy}`; the image is the same `MoveSC`. `BAScostLL_macroB` is stated for `tr` (`BAGraph.BAScost_trB`). No verdict changes.

## (b) Script output — Sun Oct 11 15:03:14 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2426`, branch `t/T2426`, last commit `1140fac`; scripts and logs in the scratchpad `T2426/lean/`.
```
$ wc -l RBM3D/Graph/BAScost.lean RBM3D/Graph/BAScost2.lean        (stop line 2,000 per file: not reached)
    1530 RBM3D/Graph/BAScost.lean
     225 RBM3D/Graph/BAScost2.lean
    1755 total
```
**The five shapes as finally proved** (lemma = `BAScost.lean` line; band lemma by import; each lemma is `BAScostLL Γ T`, hypotheses besides `p ∈ lwSplit Γ.solid`, `p.1` blue circled):
| shape | builder output (file:line) | Lean lemma | band lemma (file:line) | further hypotheses |
|---|---|---|---|---|
| S1 | `BAGGOp_A1` (BAGGOp:102, head of `gg2` :73) | `BAScostLL_S1` :836 | `scostLL_contract` 6b:1391 | `q ∈ lwSplit p.2` blue circled, `q.1.dst = p.1.src`, `p.1`, `q.1` not atom-level loops; no `[y] ≠ [y']` |
| E1 | `lanlwT1` (BAExpandW:122) | `BAScostLL_lanlwT1` :1140, `BAScostLL_E1` :1299 (all of `G = Ǧ + M`) | `scostLL_loop` 6b:621 (`[x]≠[y]`), `scostLL_moveLoop` 6b:638 (`[x]=[y]`) | none |
| E2 | any `X.splitG` (BAVocab:170) | Lemma B `BAScost_splitG_le` :465, `BAScostLL_splitG` :487; `BAScostLL_E2` :1305 | Lemma A for a circled edge inside a class, `BAScost_cons_inclass_ge` :222 (6a:434-459 with "ends in one class" for "loop") | `BAScostLL_E2`: `BAScostLL Γ X` |
| macroA | `BAGraph.BAScost_trA` :1048 | `BAScostLL_macroA` :1057 | as E1, both regimes in one lemma | none |
| macroB | `BAGraph.BAScost_trB` :1229 | `BAScostLL_macroB` :1237 | `scostLL_moveSC` 6c:1123 (no `Dmove`-size lemma) | `q` blue circled, `[p.1.src] = [q.1.dst]`, `p.1`, `q.1` not atom-level loops |
```
$ lake build RBM3D.Graph.BAScost RBM3D.Graph.BAScost2 2>&1 | grep -E "Build completed|warning: RBM3D/Graph/BAScost|error"
Build completed successfully (3815 jobs)                        (no warning line for the two files)
$ lake env lean docs/tickets/checks/T2426-check.lean; echo exit=$?                       exit=0
$ RBM3D.lean with `import RBM3D.Graph.BAScost`, `import RBM3D.Graph.BAScost2` after `import RBM3D.Graph.BASymm1` (reverted afterwards, not committed): lake build
info: RBM3D.lean:470:0: axiom audit: 12038 theorems, 3743 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4238 jobs)                        [`date -u` after it: Sun Oct 11 15:01:51 UTC 2026]
$ #print axioms of the 126 new declarations (names by script `genax.py`, output `ax.out`): 112 x [propext, Classical.choice, Quot.sound]; 11 x [propext];
  1 x [propext, Quot.sound]; 2 without axioms (BAShape, BAScost_fe)
$ grep -c "sorry\|admit\|native_decide" / grep -c "^axiom" on the two files: 0 0 / 0 0
$ git diff --stat main...t/T2426
 RBM3D/Graph/BAScost.lean  | 1530 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAScost2.lean |  225 +++++++
 2 files changed, 1755 insertions(+)
$ git grep -nwE '<the 96 new public names>' <rev> -- RBM3D ':!RBM3D/Probe' (the two own files excluded), rev = main (4bd65c3), t/T2417 ... t/T2425: 0 matches in each; the namespaces BAScostInst, BAScost2Inst: 0
$ python3 vocabdiff.py (the vocabulary against `t/T2397:RBM3D/Probe/T2397Pins.lean`, docstrings stripped): identical: scostA locStdA locCostGeA locReg6InvA BAInit BAFinal BAStep
  BANormal BAScostLL BAScostLL.trans BTStep untag BAShapeLL; BAShape: `+ deriving DecidableEq`; BReach: a definition, not the inductive (Narrative)
$ grep -cE "κ|ρ|BAct_rate|g0|Im m|Ψ" on the two files: 0 0      (C1: counts only; no `g`, `κ`, `c`, `ρ`)
Ports from `../RBM1D`, `../RBM2D`: none (no file of either project was read or copied; the vocabulary is copied from the T2397 probe, `BAScost_cons_inclass_ge` adapts `LocalRegular6a.lean:434-459` of this repository).
```
**Targets, extracted by script** (`stmts.py`, cut at 170 characters; the files hold the full text):
```
BAScost.lean:465: theorem BAScost_splitG_le (T : BAGraph E I) {Q : BAGraph E I} (hQ : Q ∈ T.splitG) (s : Setoid (E ⊕ I)) (hs : atomSetoid Q ≤ s) : scostA T s ≤ scostA Q s
BAScost.lean:487: theorem BAScostLL_splitG (T : BAGraph E I) {Q : BAGraph E I} (hQ : Q ∈ T.splitG) : BAScostLL T Q
BAScost.lean:1305: theorem BAScostLL_E2 {Γ : BAGraph E I} {X : BAGraph E I'} (hX : BAScostLL Γ X) {Q : BAGraph E I'} (hQ : Q ∈ X.splitG) : BAScostLL Γ Q
BAScost.lean:1299: theorem BAScostLL_E1 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true) : ∀
BAScost.lean:836: theorem BAScostLL_S1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ = tru
BAScost.lean:1140: theorem BAScostLL_lanlwT1 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true
BAScost.lean:1057: theorem BAScostLL_macroA (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true)
BAScost.lean:1237: theorem BAScostLL_macroB (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ 
BAScost.lean:582: theorem baInit_holds (p : ℕ) : BAInit p
BAScost.lean:680: theorem BAScost_locCostGeA_term (P : BAPGraph (Fin 2)) {I'' : Type} [Fintype I''] [DecidableEq I''] (T : BAGraph P.E' I'') (far : Bool) (k : ℤ) (hLL : B
BAScost2.lean:70: theorem baShapeLL_s1 {T : BTStep} (h : ∀ P LT, T P LT → ∀ Q, (BAShape.s1, Q) ∈ LT → ∃ p q, p ∈ lwSplit P.g.solid ∧ q ∈ lwSplit p.2 ∧ (p.1.σ = true ∧ p.1
BAScost2.lean:82: theorem baShapeLL_e1 {T : BTStep} (h : ∀ P LT, T P LT → ∀ Q, (BAShape.e1, Q) ∈ LT → ∃ p, p ∈ lwSplit P.g.solid ∧ (p.1.σ = true ∧ p.1.circ = true) ∧ ∃ Q0
BAScost2.lean:93: theorem baShapeLL_e2 {T : BTStep} (h : ∀ P LT, T P LT → ∀ Q, (BAShape.e2, Q) ∈ LT → ∃ X : BAScost_Term P, BAScostLL P.g X.X ∧ ∃ Q0 ∈ X.X.partition, Q = 
BAScost2.lean:102: theorem baShapeLL_macroA {T : BTStep} (h : ∀ P LT, T P LT → ∀ Q, (BAShape.macroA, Q) ∈ LT → ∃ p, p ∈ lwSplit P.g.solid ∧ (p.1.σ = true ∧ p.1.circ = tru
BAScost2.lean:114: theorem baShapeLL_macroB {T : BTStep} (h : ∀ P LT, T P LT → ∀ Q, (BAShape.macroB, Q) ∈ LT → (∃ p q, p ∈ lwSplit P.g.solid ∧ q ∈ lwSplit p.2 ∧ (p.1.σ = 
```
**Instances** (all compile in the builds above; every hypothesis by `rfl`, `decide` or membership): `BAScost.lean` §14, namespace `BAScostInst`: `gs` = Γ* of (a) (ii) (`0→2→1`, every atom a vertex),
`gw` (atom `{2,3}`, edge `2→3` inside), `gc` (atom `{2,3}`, pair `2→1`, `0→3`), `g2` (two parallel uncircled edges `2→1`). S1, E1, raw `T1`, macroA, macroB at `gs`; `T1` and macroA at `gw` (`[x]=[y]`);
macroB at `gc` (`a≠a'`); Lemma B and E2 at `g2` (an output `Q` with `Q.sameAtom 2 1`, `¬ g2.sameAtom 2 1`) and at `lanlwT1 gs ps`; `BAScostLL.trans`; `BAScost_locCostGeA_term` at `baPG gs` (`k = 0`); `BReach` and its
`induction`; `BAInit 2` (16 terms: `partition.length = 16`, one term with `locReg6InvA 2`). `BAScost2.lean` §3: step relations `ts1 te1 te2 tma tmb` at `gs gs gs gw gc` with `*_shape : BAShapeLL sh t` (five theorems),
applied through the crude bound `Φ ≥ 2 (n_W - |I|)` (`BAScost_locCostGeA_crude`; `k = 0, 0, 0, -4, -4`). The transfer graph `trA` has the solid and waved edges of the `M`-branch of `lanlwT1` at `gs` (compiled `rfl`).

**Narrative.**
- Cost at atoms = band cost of R0's `promoteC Γ`. Engine: `BAScost_Up s l l'` (the solid list `l'` is `l` with circles added and circled edges inside classes added) gives `scost l ≤ scost l'` (`BAScost_scost_le_of_Up`);
  its base is `BAScost_cons_inclass_ge`, the proof of `LGraph.scost_cons_loop_ge` with "the ends lie in one class" for "loop" (an atom-level edge is not a vertex loop).
- Lemma B pointwise, `BAScost_splitG_le`: induction on `baSplitSolid` (a circled edge stays, an uncircled one is circled, or dropped as an `M`-edge, which puts its ends in one class of `s ≥ atomSetoid Q`); the extra outputs `E2` are the circled-edge case.
- `BAScostLL_of_band`: the band local lemmas quantify over all setoids and return an arbitrary `s₀`, so they are used on the atom quotient `(promoteC Γ).merge`, where a merge pulls back along `vmap` to a merge that contains the atoms. A surjection `ψ` of the vertices of `T`
  onto those of a band graph `Λ` (externals to externals, kernel inside the atoms of `T`) carries a merge of `T` to one of `Λ` (`hcost` is `BAScost_Up` between `Λ` and `(promoteC T).relabel ψ`). ψ = `vmap ∘ BAScost_rho2` (S1: α↦x, β↦y) or `BAScost_psi1` (α↦a, β fresh).
- `BAInit`: Lemma B, `BAScost_scostA_le_merge` (`LGraph.scost_relabel` and `BAScost_Up` for the merge of the `=`-dotted classes), `fxyPowGraph_locCostGe`. `BAScost_locCostGeA_term` is the BA twin of `localReg6d_locCostGe_term` (Lemma B, `BAScostLL`, the merge).
- **Deviation from the pin: `BReach` is a definition** (`Relation.ReflTransGen`) with `BReach.refl`, `BReach.step` and `BReach.ind` (`@[induction_eliminator]`; `induction hQ with | refl | step hQ' hst hmem ih` compiles). With the pinned `inductive` the full build with the two imports fails:
  `error: RBM3D.lean:470:0: axiom audit: 2 premise(s) that no theorem of this development proves ... [RBM.Graph.BReach, RBM.Graph.BReach.below]` (`RBM3D/Test/Axioms.lean` registers `Lvl1Reach.below` for the same reason).
- The macro (a) transfer graph has the solid and waved edges of the E1 graph (the `M`-branch of `lanlwT1`); `BAScostLL_macroA` has no atom hypothesis (`[x]=[y]`: `MoveLoop`; `[x]≠[y]`: `Loop`, the edge `x → y` lies in one class). S1 needs no `[y] ≠ [y']`. `BAScostLL_of_band` is stated for any band graph `Λ` over the image, so it also transports other band term lemmas.

## (c) Verified Mathlib and core names (`#check @name` for the 66 identifiers of the namespaces Bool, Finset, Fintype, Function, Int, List, Prod, Quotient, Relation, Setoid, Sum that a script finds in the two files; `chk.lean`, 0 errors); the lemmas among them:
Bool: and_eq_true false_eq_true false_ne_true or_eq_true true_and; Finset: card_image_le card_le_card mem_erase mem_filter pred_card_le_card_erase; Function: Injective Surjective surjInv surjInv_eq; Int: natCast_nonneg;
List: any_append any_eq_true append_assoc append_nil countP_map exists_mem_of_ne_nil filter_append filter_cons filter_eq_self getElem_mem length_cons length_map map_append map_cons map_id' map_map map_nil mem_append mem_cons mem_cons_of_mem
  mem_cons_self mem_flatMap mem_map mem_singleton mem_singleton_self not_mem_nil perm_append_comm perm_append_comm_assoc perm_append_singleton perm_middle Perm.append_left; Prod: mk.inj; Quotient: mk sound;
Relation: EqvGen.rel ReflTransGen ReflTransGen.lift (`r ≤ p on f` form: `lift (p := ...) f h a b hab`) ReflTransGen.mono (explicit `a b`) ReflTransGen.refl ReflTransGen.single ReflTransGen.tail; Setoid: comap ext; Sum: inl inr inr_injective.
`Relation.ReflTransGen.lift` and `.mono` are stated for relations (`r ≤ p on f`), applied as `lift (p := ..) f h u v hab`, `mono h u v hab`.

## (d) Open issues and paper-delta candidates
1. Inputs of the packed forms (all else is proved): `baShapeLL_e2` takes `BAScostLL P.g X` for the builder term `X` (the band shape of the step: a band term lemma `ScostLL` at the matched image, transportable by `BAScostLL_of_band`);
   `baShapeLL_macroA/B` take the step lemma at the packed transfer graph (the band step at `img(tr)`; `Φ(P) ≥ k ⟹ Φ(tr) ≥ k` is proved); the second disjunct of `baShapeLL_macroB` takes `BAScostLL P.g X` for the stage-1 terms `d2, d3, d4` (T2423 probe `splitOutsT`).
2. `s1`: T2423 (a) F1 says `s1` is never assigned; `baShapeLL_s1` is proved and vacuous in that tagging. 3. macroB: `q` is blue (T2423 probe `BAFrameStep.ggSplit`); a red `q` (MoveOut in (a)) is not proved.
4. Hub: add `import RBM3D.Graph.BAScost` and `import RBM3D.Graph.BAScost2` after the last import line of `RBM3D.lean` (`BASymm1` at the branch base); `BReach` needs no registration. Section (a′) below (a) records two refinements of (a), no verdict changes.
5. Paper-delta candidates: `T2426a` the macro (a) transfer graph is the `M`-branch of the first term of `lanlw` (E1 graph); one local lemma for `[x]≠[y]` and `[x]=[y]`. `T2426b` `E2` has no separate cost lemma: it is Lemma B at a split that joins two atoms joined by a kept edge (T2397 E14 item 1).
   `T2426c` `BReach` is a definition (above).

