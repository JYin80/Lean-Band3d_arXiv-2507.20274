Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 07:06:05 UTC 2026

Scripts (own code, Python, no Lean): `$SP/T2184/pre.py`, `ll.py`, `inst.py`, `nc.py`, with
`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad`.
`scost` is coded exactly as the check file's `LGraph.scost`: `#kept + 2(n_W - #intCls) + #elemCls`; kept = circled or
ends in different classes; class pattern = `(b-in,b-out,r-in,r-out)` of the kept edges at the members; elementary =
`(1,1,0,0)` or `(0,0,1,1)`; internal class = no external member.

### (i) Exponent table (the only parameter is `p`; no exponent, window or `d` enters; §29 checklist empty)

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `ord(Γ_p)`, `n_S, n_W, n_V` | `p`; `3p, p, 2p` | `ord = n_S + 2(n_W - n_V)` | `= p` exactly |
| 2 | `nElem(Γ_p)` | `2p` (`α_i`: `(1,1,0,0)`/`(0,0,1,1)` by colour, `β_i`: lone light-weight) | `scost ⊥ = ord + nElem` | `3p = p + 2p` |
| 3 | `scost` at trivial `⊥` / `⊤` | `3p` / `3p` (`⊤`: `#kept=p`, `#intCls=0`, `2n_W=2p`) | `≥ 3p` far (`⊥` far; `⊤` is not far) | 0 (attained at `⊥`) |
| 4 | `scost` at `{x,y,α_i},{β_i}` (ker `x,y,α_i↦0`, `β_i↦i+1`) | `2p` | `≥ 2p` all | 0 (attained); `#kept=p`, `#intCls=p`, `#elem=p` |
| 5 | `scost` at `{x,α_i},{y},{β_i}` | `3p` | `≥ 3p` far | 0 (attained); `#kept=2p`, `#intCls=p`, `#elem=p` |
| 6 | chain (a): `n_W`, `#kept` | `p`; `3p - dr` | `dr` = #`i` with `s x α_i` + #`i` with `s α_i y` | exact |
| 7 | chain (c): `2#intCls - #elemCls` | `≤ 2p - A - B` | per internal class `2 - [elem] ≤ |K|` (`|K|=1` ⇒ elementary: `1 ≤ 1`; `|K|≥2`: `2 ≤ |K|`) | slack `|K| - 2 + [elem]` per class |
| 8 | chain (d): `scost ≥ 3p - dr + A + B` | far: `dr ≤ A` ⇒ `≥ 3p + B`; all: `dr ≤ 2A ≤ A + p` ⇒ `≥ 2p + B` | `A,B ≤ p`; far ⇒ `¬(s x α_i ∧ s α_i y)` | `B` (far), `B + (p - A)` (all) |
| 9 | Lemma A: `Δ = 1 + Δelem` | `Δelem ∈ {-1,0,1}`, `-1` only for internal `K` with `elem(H)` before adding the loop pair | `Δ ≥ 0` | `0` when `K` internal elementary |
| 10 | Lemma B: effect of `keep/circ/drop` | uncircled loop `v→v` is never kept (`s v v`); `circ` adds a circled loop; `drop` nothing | `(Γ.solid) ↦ (Γ'.solid)` | see finding F1 |
| 11 | `LocStd ⇒ nElem = 0` | pattern `(0,0,0,0)` (deg 0) or one blue + one red half-edge (no loops) | elementary needs one colour, `|H| = 2` | `localReg2_inst_Q`: `(1,0,1,0)` at `α`, `(0,1,0,1)` at `β` |
| 12 | instance graph `localReg6a_instXY` | `scost = 4` if `¬ s x y`, `2` if `s x y`; `ord = 4`, `nElem = 0` | far `≥ 4`, all `≥ 2` | far bound sharp (`ord = 4`) |

### (ii) Concrete nondegenerate instance (targets 2-6; the instances (1)-(9) of the ticket)

Command: `cd $SP/T2184 && python3 pre.py` (brute force over all set partitions of `Γ_p`, chain inequalities, random tests).
```
== Gamma_p: min scost over all set partitions, chain bound scost >= 3p-dr+A+B
p=1: #partitions=15 min_all=2 (2p=2) min_far=3 (3p=3) violations=0
   trivial 3  {x,y,alphas} 2  {x,alphas},{y} 3  top 3  expected 3 2 3 3  ord= 1  nElem= 2
p=2: #partitions=203 min_all=4 (2p=4) min_far=6 (3p=6) violations=0
   trivial 6  {x,y,alphas} 4  {x,alphas},{y} 6  top 6  expected 6 4 6 6  ord= 2  nElem= 4
p=3: #partitions=4140 min_all=6 (2p=6) min_far=9 (3p=9) violations=0
   trivial 9  {x,y,alphas} 6  {x,alphas},{y} 9  top 9  expected 9 6 9 9  ord= 3  nElem= 6
== random tests (violations): LemmaA 0  split(4a) 0  relabel(2b) 0  bot(5a) 0
```
(`violations` counts every partition failing any of: `scost ≥ 3p-dr+A+B`; far ⇒ `dr ≤ A`; `dr ≤ 2A ≤ A+p`; `scost ≥ 2p`; far ⇒ `scost ≥ 3p`.
Random tests: Lemma A 3000 random graphs/setoids; split 400 graphs × all setoids, order-preserving random `circ`/`drop` of uncircled loops;
relabel 600 graphs × all setoids on the image, random onto `vm` with `vm(inl a) = inl(ext a)`, `ext ∈ {id, collapse}`; `scost ⊥` on 3000 normal graphs.)

Command: `python3 inst.py` (hypotheses of the targets and the nine compiled instances).
```
(8) p=2: Normal-iii/CircIffLoop/DotWF/Normal-ii = (True, True, True, True); ord=2; scost bot=6 (=3p=6); nElem=4 (=2p); ord+nElem=6
     all-bound setoid ker(x,y,alpha_i->0, beta_i->i+1): scost=4 (=2p=4); far setoid {x,alphas},{y},{beta_i}:  6 (=3p=6)
(8) p=3: Normal-iii/CircIffLoop/DotWF/Normal-ii = (True, True, True, True); ord=3; scost bot=9 (=3p=9); nElem=6 (=2p); ord+nElem=9
     all-bound setoid ker(x,y,alpha_i->0, beta_i->i+1): scost=6 (=2p=6); far setoid {x,alphas},{y},{beta_i}:  9 (=3p=9)
(1) perm: bot 6 6
(2) relabel: vm onto = True ; mismatches over all 203 setoids: 0
(3) LemmaA: bot 6 <= 7
(4) split: setoid (0, 0, 0) scost 0 <= 1 True
(4) split: setoid (0, 0, 1) scost -2 <= 0 True
(4) split: setoid (0, 1, 0) scost 0 <= 1 True
(4) split: setoid (0, 1, 1) scost 0 <= 1 True
(4) split: setoid (0, 1, 2) scost -2 <= 0 True
(7) nElem(localReg2_inst_Q) = 0 ; halfPat alpha = (1, 0, 1, 0)  beta = (0, 1, 0, 1)
    scost bot = 2  ord = 2  (= ord + nElem since nElem=0)
(9) instXY: scost by setoid (0,0)=x~y: 2  (0,1)=x!~y: 4  ord = 4  nElem = 0
    Normal: no loops, XBetween 0 1 = SBetween 0 1 (dotted x!=y, solid x->y) ; LocStd: no loops, no internal vertex
```
Reading: instance (1) reversal of the solid list, (3) `e = ⟨true,true,inl 0,inl 0⟩` at `p = 2`, (4) both graphs on `Fin 2 ⊕ Fin 1` (empty waved list,
so `hW` holds; `lvl1Split.circ` with `{e with circ := true}`), (5) `Γ_2` is normal with `DotWF` (script column `DotWF = True`; `partition_of_normal`
gives the one-term partition, `vm` = the singleton-class bijection, `scost` equal), (6) `scost ⊥ = 6, 9` at `p = 2, 3`, (8) `4, 6` (all) and `6, 9` (far),
(9) hypotheses `LocStd`, `ext 0 ≠ ext 1` hold; far `4 ≤ ord = 4`, all `2 ≤ 4`. No external hypothesis: no limit computation is owed.

Section-4 pins (not proved here): command `python3 -c` (`ll.py`, 6000 random trials per mode; `Γ` on `Fin 2 ⊕ Fin (1..3)`, `rest` random 0-3 edges,
`mode=circiff`: `rest` circled iff loop; `mode=arbitrary`: `rest` has random `circ`; all pin hypotheses imposed; every `s` on `T` checked against all `s₀` on `Γ`):
```
circiff {'addLoop': (860, 0), 'contract': (471, 0), 'moveSC': (520, 0), 'moveLoop': (850, 0), 'dmove': (829, 0), 'moveOut': (461, 0), 'loop': (855, 0)} (prim: (#instances, #failures of ScostLL))
arbitrary {'addLoop': (838, 0), 'moveLoop': (890, 0), 'contract': (466, 0), 'moveSC': (484, 0), 'loop': (896, 0), 'dmove': (848, 0), 'moveOut': (452, 0)} (prim: (#instances, #failures of ScostLL))
```
Finding F1 (Lemma B(a), route of target 4): `scost` of a list is not monotone under a common prefix. `python3 nc.py` (one setoid, vertices `x,y,a,b` all singletons):
```
counterexample: es [(True, True, 1, 1), (True, True, 1, 1)] es' [(False, True, 2, 2)] e (False, True, 2, 2) scost es, es' = -2 -2 ; with e: 0 -2
```
So `scost es ≤ scost es'` does not imply `scost (e::es) ≤ scost (e::es')`; "induction on `lvl1Split`, `keep` changes nothing" is not literally valid.
The true auxiliary form carries a prefix `b`: `lvl1Split es es' d → ∀ b, scost (b ++ es) ≤ scost (b ++ es')` with Lemma A (list form, via `scost_perm`/`List.Perm` for
`b ++ c :: es'` vs `c :: (b ++ es')`) for `circ` and `scost (b ++ e :: es) = scost (b ++ es)` for `drop` (an uncircled loop is never kept and `skept` is a filter).
The statement of target 4(a) is true (random test above: 0 violations); only the proof route needs the generalised prefix.

### Verdict
- Target 1 (vocabulary): PASS. Definitions are consistent (`scost ⊥ = ord + nElem` on normal graphs, random test 0 violations).
- Target 2 (`scost_perm`, `scost_relabel`): PASS (random relabel test and instance (2): 0 mismatches over all setoids).
- Target 3 (Lemma A): PASS (`Δ = 1 + Δelem ≥ 0`; 0 violations on 3000 random cases).
- Target 4 (`scost_le_of_lvl1Split`, `scost_partition_ge`): PASS for the statements (0 violations); route of (a) needs the prefix generalisation (F1);
  (b) needs no hypothesis on `Δ`: `Δ.relabel vm` has `solid = Δ.solid.map (SEdge.map vm)`, `waved.length` equal by `P.g.waved = Δ.waved.map _`, `ext = P.ext` onto.
- Target 5 (`scost_bot`, `nElem_eq_zero_of_locStd`, `locReg6_of_locCostGe`, `locReg6far_of_locCostGe`): PASS (random `scost ⊥` test 0 violations; rows 11-12).
- Target 6 (`fxyPowGraph_locCostGe`, `fxyPowGraph_locReg6Inv`): PASS (exhaustive for `p = 1,2,3`: `min_all = 2p`, `min_far = 3p`, chain inequalities 0 violations;
  the general-`p` chain (a)-(d) of rows 6-8 is a per-`i` argument, so it does not depend on `p`).
- Section-4 pins (informational): no counterexample to any of the 11 `ScostLL`/primitive pins at 6000 random trials per mode.
- Overall: PASS.

## (b) Script output — Mon Oct  5 14:56:01 UTC 2026

Branch `t/T2184`, HEAD `7889bd2` (`git log --oneline main..t/T2184` below); sole file `RBM3D/Graph/LocalRegular6a.lean` (1188 lines, `import RBM3D.Graph.LocalRegular2`). No port (ticket: RBM1D/RBM2D have no light-weight layer): no RBM1D/RBM2D diff-stat.
```
$ git log --oneline main..t/T2184 ; git diff --stat main...t/T2184 ; git diff --name-only main...t/T2184
7889bd2 T2184: instance (10): final step at the locally standard graph loca
f8e1677 T2184: LW-10c1 Graph/LocalRegular6a (scost vocabulary, Lemmas A and
 RBM3D/Graph/LocalRegular6a.lean | 1188 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 1188 insertions(+)
RBM3D/Graph/LocalRegular6a.lean
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/LocalRegular6a.lean
0
$ lake build RBM3D.Graph.LocalRegular6a      # run after the last edit of the file (`git hash-object` of the file = `git rev-parse HEAD:<file>`)
✔ [3385/3385] Built RBM3D.Graph.LocalRegular6a (4.0s)
Build completed successfully (3385 jobs).
$ python3 (json.load of `.lake/build/lib/lean/RBM3D/Graph/LocalRegular6a.trace`, field `log`)
1 log entries: the LEAN_PATH trace line only (no warning, no error)
$ lake build      # full library in the worktree (the hub adds the root import at merge, so the module itself is covered by the pre-check below)
Build completed successfully (3988 jobs).
$ cat precheck.lean ; lake env lean precheck.lean ; echo exit=$?      # registry pre-check (DECISIONS §20 (2))
import RBM3D
import RBM3D.Graph.LocalRegular6a

#assert_rbm_axioms
axiom audit: 5459 theorems, 1925 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
exit=0
```

### Axioms (`#print axioms`, `lake env lean`; the last line collects every declaration of the module with `Lean.collectAxioms`)
```
'RBM.Graph.LGraph.scost_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_cons_loop_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_le_of_lvl1Split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_partition_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.nElem_eq_zero_of_locStd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.locReg6_of_locCostGe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.locReg6far_of_locCostGe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.fxyPowGraph_locCostGe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.fxyPowGraph_locReg6Inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6a_instXY_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6a_instXY_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg6a_instQ_all' depends on axioms: [propext, Classical.choice, Quot.sound]
module RBM3D.Graph.LocalRegular6a: 105 declarations (79 theorems, 26 definitions); axioms used by any of them: [propext, Classical.choice, Quot.sound]
```

### Target statements (extracted from the file by script `extract.py`: from `theorem NAME` to the first depth-0 `:=`; line number first)
```
309: theorem LGraph.scost_perm (Γ Γ' : LGraph E I) (hS : Γ.solid.Perm Γ'.solid) (hW : Γ.waved.length = Γ'.waved.length) (s : Setoid (E ⊕ I)) : Γ.scost s = Γ'.scost s
401: theorem LGraph.scost_relabel (Δ : LGraph E I) (ext : E → E') (hext : Function.Surjective ext) (vm : E ⊕ I → E' ⊕ I') (hvm : Function.Surjective vm) (hvl : ∀ a : E, vm (Sum.inl a) = Sum.inl (ext a)) (s : Setoid (E' ⊕ I')) : LGraph.scost (Δ.relabel vm) s = LGraph.scost Δ (Setoid.comap vm s)
434: theorem LGraph.scost_cons_loop_ge (Γ : LGraph E I) (e : SEdge (E ⊕ I)) (he : e.src = e.dst) (hc : e.circ = true) (s : Setoid (E ⊕ I)) : Γ.scost s ≤ ({ Γ with solid := e :: Γ.solid } : LGraph E I).scost s
493: theorem LGraph.scost_le_of_lvl1Split (Γ Γ' : LGraph E I) (d : ℕ) (hS : lvl1Split Γ.solid Γ'.solid d) (hW : Γ'.waved.length = Γ.waved.length) (s : Setoid (E ⊕ I)) : Γ.scost s ≤ Γ'.scost s
503: theorem LGraph.scost_partition_ge (m : ℂ) (Δ : LGraph E I) (P : PGraph E) (hP : P ∈ Δ.partition m) : ∃ vm : E ⊕ I → P.E' ⊕ P.I', (∀ a : E, vm (Sum.inl a) = Sum.inl (P.ext a)) ∧ ∀ s : Setoid (P.E' ⊕ P.I'), LGraph.scost Δ (Setoid.comap vm s) ≤ LGraph.scost P.g s
560: theorem LGraph.scost_bot (Γ : LGraph E I) (hN : Γ.Normal) : LGraph.scost Γ ⊥ = ord Γ.counters + (LGraph.nElem Γ : ℤ)
617: theorem LGraph.nElem_eq_zero_of_locStd (Γ : LGraph E I) (hL : Γ.LocStd) : Γ.nElem = 0
645: theorem locReg6_of_locCostGe {Q : PGraph (Fin 2)} {k : ℤ} (hQ : Q.LocStd) (h : Q.LocCostGe false k) : k ≤ Q.g.scalingOrder
653: theorem locReg6far_of_locCostGe {Q : PGraph (Fin 2)} {k : ℤ} (hQ : Q.LocStd) (hxy : Q.ext 0 ≠ Q.ext 1) (h : Q.LocCostGe true k) : k ≤ Q.g.scalingOrder
927: theorem fxyPowGraph_locCostGe (p : ℕ) : (fxyPowGraph p).pack.LocCostGe false (2 * (p : ℤ)) ∧ (fxyPowGraph p).pack.LocCostGe true (3 * (p : ℤ))
956: theorem fxyPowGraph_locReg6Inv (p : ℕ) : (fxyPowGraph p).pack.LocReg6Inv p
```

### Target 1 (vocabulary) and targets 2-6 against the check file (script diffs)
```
$ awk '/^section Pattern/{f=1} f{print} /^end Prims/{if(f){exit}}' <file>  # on docs/tickets/checks/T2184-check.lean and on the new file; diff
(no output: section 2 of the check file == the file, 129 lines each, 19 `def`s; no file-level `open Classical` (`grep -c '^open Classical$'` = 0); `open Classical in` occurs 3 times in the vocabulary, as in the check file, and 29 times in the file)
$ awk '/^\/-! ## 3\./{f=1} /^\/-! ## 4\./{f=0} f{print}' T2184-check.lean   # the 11 Pins (62 lines), put into `namespace RBM.Graph.T2184Pins` with `open RBM RBM.Graph`, then:
theorem chk_perm : ScostPermPin := @LGraph.scost_perm
theorem chk_relabel : ScostRelabelPin := @LGraph.scost_relabel
theorem chk_loop : ScostConsLoopPin := @LGraph.scost_cons_loop_ge
theorem chk_split : ScostSplitPin := @LGraph.scost_le_of_lvl1Split
theorem chk_partition : ScostPartitionPin := @LGraph.scost_partition_ge
theorem chk_bot : ScostBotPin := @LGraph.scost_bot
theorem chk_nelem : NElemLocStdPin := @LGraph.nElem_eq_zero_of_locStd
theorem chk_locreg6 : LocReg6OfLocCostGePin := fun _ _ hQ h => locReg6_of_locCostGe hQ h
theorem chk_locreg6far : LocReg6FarOfLocCostGePin := fun _ _ hQ hxy h => locReg6far_of_locCostGe hQ hxy h
theorem chk_fxycost : FxyLocCostGePin := fxyPowGraph_locCostGe
theorem chk_fxyinv : FxyLocReg6InvPin := fxyPowGraph_locReg6Inv
$ lake env lean pins_check.lean ; echo exit=$?
exit=0     # each Pin is discharged by the file's theorem as a term (no added hypothesis, no reordering)
```

### Compiled nonempty instances (named theorems in the same file, section 7; vertex sets `Fin 2 ⊕ Fin 4`, `Fin 2 ⊕ Fin 6` (`p = 2, 3`), `Fin 2 ⊕ Fin 2` (`localReg2_inst_Q`), `Fin 2 ⊕ Fin 1`, `Fin 2 ⊕ Fin 0` (instance (9), as the ticket pins))
```
966: theorem localReg6a_inst_perm : (fxyPowGraph 2).scost ⊥ = ({ fxyPowGraph 2 with solid := (fxyPowGraph 2).solid.reverse } : LGraph (Fin 2) (Fin (2 * 2))).scost ⊥
972: theorem localReg6a_inst_relabel (s : Setoid (Fin 2 ⊕ Fin (2 * 2))) : ((fxyPowGraph 2).relabel (Sum.map id (Equiv.swap (0 : Fin (2 * 2)) 1))).scost s = (fxyPowGraph 2).scost (Setoid.comap (Sum.map id (Equiv.swap (0 : Fin (2 * 2)) 1)) s)
979: theorem localReg6a_inst_consLoop : (fxyPowGraph 2).scost ⊥ ≤ ({ fxyPowGraph 2 with solid := (⟨true, true, Sum.inl 0, Sum.inl 0⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: (fxyPowGraph 2).solid } : LGraph (Fin 2) (Fin (2 * 2))).scost ⊥
999: theorem localReg6a_inst_splitCirc (s : Setoid (Fin 2 ⊕ Fin 1)) : localReg6a_instSplit0.scost s ≤ localReg6a_instSplit1.scost s
1005: theorem localReg6a_inst_splitDrop (s : Setoid (Fin 2 ⊕ Fin 1)) : localReg6a_instSplit0.scost s ≤ ({ localReg6a_instSplit0 with solid := [] } : LGraph (Fin 2) (Fin 1)).scost s
1011: theorem localReg6a_inst_partition : ∃ P : PGraph (Fin 2), P ∈ (fxyPowGraph 2).partition 1 ∧ ∃ vm : Fin 2 ⊕ Fin (2 * 2) → P.E' ⊕ P.I', (∀ a, vm (Sum.inl a) = Sum.inl (P.ext a)) ∧ ∀ s : Setoid (P.E' ⊕ P.I'), (fxyPowGraph 2).scost (Setoid.comap vm s) ≤ P.g.scost s
1025: theorem localReg6a_inst_bot2 : (fxyPowGraph 2).scost ⊥ = 6
1031: theorem localReg6a_inst_bot3 : (fxyPowGraph 3).scost ⊥ = 9
1037: theorem localReg6a_inst_nElemLocStd : localReg2_inst_Q.nElem = 0
1040: theorem localReg6a_inst_cost2 : (fxyPowGraph 2).pack.LocCostGe false 4 ∧ (fxyPowGraph 2).pack.LocCostGe true 6
1047: theorem localReg6a_inst_cost3 : (fxyPowGraph 3).pack.LocCostGe false 6 ∧ (fxyPowGraph 3).pack.LocCostGe true 9
1054: theorem localReg6a_inst_inv2 : (fxyPowGraph 2).pack.LocReg6Inv 2
1057: theorem localReg6a_inst_inv3 : (fxyPowGraph 3).pack.LocReg6Inv 3
1085: theorem localReg6a_instXY_far : localReg6a_instXY.pack.LocCostGe true 4
1097: theorem localReg6a_instXY_all : localReg6a_instXY.pack.LocCostGe false 2
1111: theorem localReg6a_instXY_far_ord : (4 : ℤ) ≤ localReg6a_instXY.pack.g.scalingOrder
1115: theorem localReg6a_instXY_all_ord : (2 : ℤ) ≤ localReg6a_instXY.pack.g.scalingOrder
1155: theorem localReg6a_instQ_all : localReg2_inst_Q.pack.LocCostGe false 2
1176: theorem localReg6a_instQ_all_ord : (2 : ℤ) ≤ localReg2_inst_Q.pack.g.scalingOrder
1180: theorem localReg6a_instQ_far_ord : (2 : ℤ) ≤ localReg2_inst_Q.pack.g.scalingOrder
```
Data: `localReg6a_instSplit0/1` (one internal vertex, uncircled/circled loop, no waved edge; the strict case `scost -2 ≤ 0` at the discrete setoid is the line `(4) split: setoid (0, 1, 2) scost -2 <= 0 True` of (a)), `localReg6a_instXY` (the data of `auxGraph_instXY`, `AuxGraph.lean:1766`, copied; `LocStd`, `ord = 4`, no internal vertex), `localReg2_inst_Q` (merged; `LocStd`, `ord = 2` by `decide`, internal `α`, `β`).
Application lines of the targets inside section 7 (script over the file): `scost_perm` 968, `scost_relabel` 975, `scost_cons_loop_ge` 982, `scost_le_of_lvl1Split` 1001/1007, `scost_partition_ge` 1016, `scost_bot` 1027/1033, `nElem_eq_zero_of_locStd` 1037, `fxyPowGraph_locCostGe` 1042/1049, `fxyPowGraph_locReg6Inv` 1054/1057, `locReg6far_of_locCostGe` 1112/1181, `locReg6_of_locCostGe` 1116/1177.

### Name-clash grep of the new public names
```
$ python3 nameclash.py   # for each constant of the module (`axioms.out` list minus `.congr_simp`): `grep -rnw --include=*.lean -- <name without RBM.Graph.>` and `<last component>` over RBM3D/ of the main worktree (f23811b) and of the worktrees T2180 T2181 T2182 T2183 T2185 T2187 T2184, excluding the new file
new public names checked: 105; names with hits outside the new file: 0
```

### Scratch checks (not in the file, which must not define the names pinned for c2-c4); `lake env lean`, exit 0; `#print axioms` of the pin proofs and of four of the six claims below: `[propext, Classical.choice, Quot.sound]`
```
theorem chk_trans    : ScostLLTransPin    := by intro …; obtain ⟨s1,hs1,hc1⟩ := h2 s; obtain ⟨s0,hs0,hc0⟩ := h1 s1; exact ⟨s0, fun a b h => hs0 a b (hs1 a b h), hc0.trans hc1⟩
theorem chk_perm     : ScostLLPermPin     := by intro …; obtain ⟨s0,hs0,hc0⟩ := h s; exact ⟨s0, hs0, hc0.trans (le_of_eq (LGraph.scost_perm T T' hS hW s))⟩
theorem chk_relabel  : ScostLLRelabelPin  := by intro …; obtain ⟨s0,hs0,hc0⟩ := h (Setoid.comap φ s); refine ⟨s0, fun a b hab => hs0 a b ?_, ?_⟩  -- 2nd goal: rw [LGraph.scost_relabel T id Function.surjective_id φ hφ hφl s]; exact hc0
theorem chk_addLoop  : ScostLLAddLoopPin  := by intro …; exact ⟨s, fun a b h => h, LGraph.scost_cons_loop_ge Γ ⟨col, true, z, z⟩ rfl rfl s⟩
-- design claims of target 1 (`theorem … := rfl`; `{E I : Type}`, `m : ℂ`, `q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))`):
(lwPrimDmove Γ q.2 (Sum.inr x) (Sum.inr x) q.1).solid = (owxT3 m Γ x q).solid   -- and `.waved`
(lwPrimDmove Γ q.2 (Sum.inr x) v q.1).solid = (oe1xD m Γ x v q).solid          -- and `.waved`
(lwPrimContract Γ q.2 (Sum.inr x) y' y).solid.Perm (oe2xR2 m Γ q x y y').solid ; (…).waved.length = (oe2xR2 m Γ q x y y').waved.length
```

### Narrative (facts only)
- Target 1: the 19 definitions are the check file's text (diff empty); targets 2-6 are the 11 Pins as terms (above). `CircIffLoop` is concluded by `localReg6a_fxy_circIffLoop` and is a conjunct of `LocReg6Inv`; `ScostLL` is used by no theorem of the file; `LocCostGe` is concluded by `fxyPowGraph_locCostGe`, `localReg6a_instXY_far/_all`, `localReg6a_instQ_all`; so `RBM3D/Test/Axioms.lean` is not touched (pre-check exit 0).
- `scost_perm`: `skept` is a `List.filter` (`List.Perm.filter`), the pattern of a list is permutation invariant (`localReg6a_halfPat_perm`), `scost` sees `waved` only through its length.
- `scost_relabel`: `localReg6a_qmap vm s : Quotient (Setoid.comap vm s) → Quotient s` (`[v] ↦ [vm v]`) is injective; `sIntCls`, `sElemCls` of `Δ.relabel vm` are its images (`localReg6a_sIntCls_relabel`, `localReg6a_sElemCls_relabel`; uses `vm (inl a) = inl (ext a)`, `ext` and `vm` onto); `skept` of the relabelled graph is the image of `skept` (`localReg6a_skept_relabel`); `localReg6a_halfPat_map` is the `List.countP_map` step.
- Lemma A (`scost_cons_loop_ge`): `skept (e :: solid) = e :: skept`; `(sElemCls Γ).erase [e.src] ⊆ sElemCls Γ'` (a loop outside a class leaves its pattern, `localReg6a_halfPat_cons_loop`); `Finset.pred_card_le_card_erase`; `omega`.
- Lemma B(a) (`scost_le_of_lvl1Split`): induction on `lvl1Split` for the statement with a prefix, `localReg6a_split_aux : ∀ b, scost {Γ0 with solid := b ++ es} ≤ scost {Γ0 with solid := b ++ es'}` (finding F1 of (a): the form without a prefix is not inductive). `keep`: prefix `b ++ [e]`; `circ`: `localReg6a_scost_drop` (an uncircled loop is never kept), the induction hypothesis, Lemma A, `scost_perm` with `List.perm_middle`; `drop`: `localReg6a_scost_drop`.
- Lemma B(b) (`scost_partition_ge`): `lvl1_part_struct` gives `vm` (onto, `vm (inl a) = inl (P.ext a)`, `P.g.waved = Δ.waved.map _`, `lvl1Split (Δ.solid.map (SEdge.map vm)) P.g.solid d`); `scost_relabel` with `ext = P.ext` (`P.ext_surj`), then (a) on `Δ.relabel vm`; no hypothesis on `Δ`.
- `scost_bot`: `Normal` makes every loop circled (`hN.2.2`), so `skept ⊥ = solid`; `sIntCls ⊥` has `Fintype.card I` elements and `sElemCls ⊥` has `nElem` elements (`Quotient.mk ⊥` is injective). `nElem_eq_zero_of_locStd`: no loops, so `b-in + b-out`, `r-in + r-out` at `inr i` count the blue and red edges of `lvl1SolidAt (inr i)`, which has degree `0` or one blue and one red edge, never `(1,1,0,0)`/`(0,0,1,1)`.
- `fxyPowGraph_locCostGe`: `localReg6a_fxy_scost_ge`: `5p ≤ scost s + Σ_i (d_i + a_i + b_i)` for every setoid (`d_i` dropped edges of block `i`; `a_i`, `b_i` indicators that `α_i`, `β_i` lie in internal classes); `localReg6a_two_intCls_le` (`2 #intCls ≤ #elemCls + |S|` from `2 - [K elementary] ≤ |K|`, `Finset.card_eq_sum_card_image`, every singleton internal class elementary by `localReg6a_fxy_elem`); per block `d_i + a_i + b_i ≤ 3`, and `≤ 2` if `¬ s x y` (`localReg6a_fxy_block_ineq`, four case splits); sums over `Fin p` by `localReg6a_sum_fin2`; `omega` gives `2p` and `3p`.
- Instance (10), the final step at a locally standard graph with internal vertices (`localReg2_inst_Q`: `x`, `y`; `α`, `β`; solid `G_{xα}, Ḡ_{xα}, G_{βy}, Ḡ_{βy}`; one waved edge; `ord = 2`): `localReg6a_instQ_all` shows `2 ≤ scost s` for every setoid from `localReg6a_instQ_kept` (`#kept + 2[s x α] + 2[s β y] = 4`) and `localReg6a_instQ_int_card` (`#intCls + [s x α] + [s β y] ≤ 2`), `#elemCls ≥ 0`; `locReg6_of_locCostGe`, `locReg6far_of_locCostGe` then give `2 ≤ ord`, sharp (`localReg6a_instQ_ord`).
- Not in this file (c2-c4): `ScostLL.trans/of_perm/of_relabel`, the primitives' local lemmas, composition, decompositions, twists, step lemma, assembly.

## (c) Verified Mathlib and core names used (script `names.lean`: `env.contains` and `getModuleIdxFor?` on the 97 dotted identifiers of the file with a core or Mathlib root namespace; 0 not found; names verified absent: none searched)
- `Mathlib.Data.Finset.Card`: `Finset.card_empty`, `card_eq_zero`, `card_image_of_injective`, `card_le_card`, `card_le_one`, `card_le_two`, `card_map`, `card_pos`, `pred_card_le_card_erase`
- `Mathlib.Data.Finset.{Disjoint, Empty, Filter, Basic, Lattice.Basic, Erase, Image}`: `Finset.disjoint_left`; `eq_empty_of_forall_notMem`, `subset_empty`; `filter_eq_empty_iff`, `mem_filter`; `filter_mem_eq_inter`; `inter_eq_right`, `mem_union`; `mem_erase`; `mem_image`, `mem_map`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`: `Finset.card_eq_sum_card_image`, `sum_add_distrib`, `sum_congr`, `sum_image`, `sum_union`; `...Group.Finset.Piecewise`: `Finset.card_filter`, `sum_ite_eq'`; `...Ring.Finset`: `Finset.sum_boole`; `...Fin`: `Fin.sum_univ_def`; `Mathlib.Algebra.Order.BigOperators.Group.Finset`: `Finset.sum_le_sum`
- `Mathlib.Data.Fintype.{Card, Defs, BigOperators}`: `Finset.card_univ`, `Fintype.card`; `Finset.mem_univ`; `Fintype.sum_sum_type`
- `Mathlib.Data.Sum.Basic`: `Function.Surjective.sumMap`, `Sum.inr_injective`; `Mathlib.Data.Quot`: `Quotient.map`; `Mathlib.Data.Setoid.Basic`: `Setoid.comap`, `Setoid.refl'` (and `Setoid.comap_rel` in the scratch pin check); `Mathlib.Logic.Equiv.Basic`: `Equiv.swap`; `Mathlib.Logic.Embedding.Basic`: `Function.Embedding.coeFn_mk`; `Mathlib.Data.Nat.Cast.Defs`: `Nat.cast_zero`; `Mathlib.Algebra.Ring.Parity`: `Nat.even_or_odd'`; `Mathlib.Data.Nat.Cast.Order.Ring`: `Nat.cast_nonneg`
- Init (core): `Bool.and_eq_true`, `Fin.ext`, `Fin.forall_fin_two`, `Function.surjective_id`, `Function.comp_def`, `Int.natCast_nonneg`, `Prod.ext`, `Quotient.{exact, exists_rep, mk, sound}`, `Sum.{inl.inj, inr.injEq, map}`, `List.{Perm.refl, perm_middle, reverse_perm, finRange, append_assoc, nil_append, flatMap_cons, map_cons, map_nil, length_cons, length_map, length_flatMap, length_eq_zero_iff, mem_cons, mem_cons_of_mem, mem_cons_self, mem_singleton_self, not_mem_nil, countP_{append, congr, cons, filter, map}, filter_{append, cons, eq_self, flatMap, map}}`

## (d) Open issues and paper-delta candidates
- Paper-delta candidates (the ticket's expected list; numbered by the dispatcher):
  - `T2184a`: (6) is proved through the local cost `c = ord + #elem` minimised over merges (`scost`, `LocCostGe`), not through `ord + n_dv + n_lw` (`B:200-278`); the initial values `Φ^far(Γ_p) ≥ 3p`, `Φ^all(Γ_p) ≥ 2p` (`fxyPowGraph_locCostGe`) replace `3p - n_dv/2 > 2p`.
  - `T2184b`: a merge is a `Setoid (E ⊕ I)`; a class is external iff it has an external member; an edge is kept iff it is circled or joins two classes; `scost = #kept + 2 n_W - 2 #intCls + #elemCls`.
  - `T2184c`: the edge and `GG` cases omitted at `B:272-275` are supplied by c2-c4 (numbered with them).
- O1 (ticket route, no statement change): the route of target 4(a), "induction on `lvl1Split`, `keep` changes nothing", is not valid as written (finding F1 of (a): `scost es ≤ scost es'` does not give `scost (e :: es) ≤ scost (e :: es')`); the proof is the prefix form `localReg6a_split_aux`.
- O2 (instances): instance (5) is at the normal `fxyPowGraph 2`, whose partition is the one-term trivial merge, as the ticket pins; a non-trivial merge is not compiled. Instance (9) has no internal vertex, as the ticket pins; instance (10) (not in the ticket) applies the final-step theorems at a locally standard graph with two internal vertices. The optional all-bound sharpness instance (`Setoid.ker` of `x, y, α_i ↦ 0`, `β_i ↦ i + 1`) is not compiled; the minima are the brute-force lines of (a) (`min_all = 2p`, `min_far = 3p`, `p = 1, 2, 3`). The far bound is sharp in Lean: instance (6) `scost ⊥ = 6, 9 = 3p`, instance (9) `4 ≤ ord = 4`.
- O3 (section-4 pins, informational): the local lemmas of the other six primitives (`scostLL_loop`, `_moveLoop`, `_contract`, `_moveSC`, `_moveOut`, `_dmove`) and the c4 statements were not touched here ((a) reports 0 failures in 6000 random trials per mode, for all seven primitives); `ScostLLTransPin`, `ScostLLPermPin`, `ScostLLRelabelPin`, `ScostLLAddLoopPin` follow in a few lines from `scost_perm`, `scost_relabel`, `scost_cons_loop_ge` (scratch above), and the design claims of target 1 for `lwPrimDmove`, `lwPrimContract` hold (scratch above). c2-c4 import `RBM3D.Graph.LocalRegular6a` and must not redefine `ScostLL`, `scost`, the primitives.
