Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 16:23:41 UTC 2026

Model: own Python re-implementation of `LGraph.scost` (`LocalRegular6a.lean:157`), the primitives (`:195-233`) and the pins (check file section 4, md5 of lines 316-357 recomputed = `4826cdc5250a809ff964ec63d6442fa2`, as the ticket states). Setoids = all set partitions; "iff" = `CircIffLoop` graphs, "arbitrary" = random `circ` flags, loops uncircled or circled, circled non-loops (more than any pin assumes). F is a lead only; every number below is from the script output pasted in (ii).

### (i) Exponent table (`Δ := T.scost s − Γ.scost s₀` for the chosen `s₀`; values = minima over the tested setoids)

| statement | constant / constraint | value | slack |
|---|---|---|---|
| `trans`, `of_perm`, `of_relabel` | separation composes; `≤` composes; `scost_perm` (needs only `waved.length`), `scost_relabel` (`ext = id`, `φ` onto, `φ (inl a) = inl a`) | no numeric constant; pins used with no extra hypothesis | n/a |
| surgery (a) class sum | `scost = #kept + 2 n_W + Σ_{c int}([elem pat_c] − 2)` | 0 failures / 34522 setoids | exact |
| surgery (c), fresh vertex | `#kept(Γ,s₀) + #kept(A,s') + 2(n_W + \|W\|) + Σ_{c₀ ∈ int(s₀)}([elem(pat Γ s₀ c₀ + pat A s' (qmap c₀))] − 2) + [α alone]([elem pat A s' ⟦α⟧] − 2)` | 0 failures / 125100 setoids (34922 with α alone, rest α not alone) | exact |
| surgery, localisation (one vertex type) | classes containing no end of `R ++ A` give the same summand | 0 failures / 35045 setoids | exact |
| pattern (E0) | `[elem(H−R+A)] − [elem H] ≥ −1`, `= −1 → elem H` | 0 violations / 1679616 | −1 attained |
| pattern (E1)/(E5), `elem H → H ≠ 0` | `elem(X+(1,1,0,0)) = [X=0]`, same for `(0,0,1,1)` | 0 violations | exact |
| pattern (E4), (E6) | two colours, or ≥2 outs, or ≥2 ins ⇒ ¬elem; same for `H + A`, `A` a pair of two colours or one direction | 0 violations (`ℕ⁴`, entries ≤ 3) | only 4 ordered pairs `A` escape (E6): one colour, one in, one out |
| placement, threshold `k ≤ 1` | `T.scost s − T.scost (split α s) ≥ 0`, shapes: circled loop (k = 0) and two uncircled edges, any colours/directions | min 0 (k=0), 0 (k=1), −2 (k=2, excluded); 0 violations for k ≤ 1 / 187030 setoids | 0 (tight); k=2 fails 3489 times; minimal failure in output |
| repair | `s₀ ∈ {s, merge s u z}`, `Γ.scost s₀ ≤ Γ_L.scost s + 2` | `Δc := Γ_L.scost s + 2 − Γ.scost s` = −2 (`instCyc`, ⊥), −1 (`Γ_2`, `{x,y}`); merge branch (two modes, 3000 graphs): merge cost = base in all cases, 0 FAIL, 0 merges of two external classes, 0 negative `Δc` without an internal class with `X = 0` | 0 (merge exact) |
| `scostLL_loop` | `Δ ≥ 0` | min `Δ = 2` (α alone), restriction witness always | 2 |
| `scostLL_addLoop` | `Δ ≥ 0`, `s₀ = s` | min 0 | 0 (tight: `Γ_2`, β₀: 6 → 6) |
| `scostLL_moveLoop` | `Δ ≥ 0`, restriction | min 0; `α ~ β₀`: 8 vs 6 | 0 (tight: 6 → 6) |
| `scostLL_contract` | `Δ ≥ 0`, `s₀ ∈ {s, merge}` | min 0 for both kinds; merge only in case `[u]=[v]≠[z]` | 0; repair forced at `instCyc` (0 → −2) |
| §55 constants, `Γ_p` | `min_s ≥ 2p`, `min_{s, ¬s x y} ≥ 3p` over all applications | p=2: 4, 6 (27 applications); p=3: 6, 9 (36) | 0 (attained at AddLoop, MoveLoop, Contract) |

### (ii) One concrete nondegenerate instance and checks

Instance: `Γ_2 = fxyPowGraph 2` (`E = Fin 2`, `I = Fin 4`; `x = inl 0, y = inl 1, α₀ = inr 0, β₀ = inr 1` blue block, `α₁ = inr 2, β₁ = inr 3` red block; solid `[β₀ loop, x→α₀, α₀→y, β₁ loop, x→α₁, α₁→y]`, 2 waved edges, `scost ⊥ = 6`). All hypotheses hold at once at it: `loop`: `z = x`, blue; `addLoop`: `z = β₀`, blue; `moveLoop`: `z = β₀`, `rest` = the other five edges, `Perm` holds; `contract`: `z = α₀`, `u = x`, `v = y`, `rest = [β₀ loop, β₁ loop, x→α₁, α₁→y]`, `u ≠ z`, `z ≠ v`, `Perm` holds (permutation, not equality); placement: `MoveSC(α₀; x, y)` shape `[x→α, α→y]` with `s = {α ~ x}`, `k = 1`; `Loop(x)` and `MoveLoop(β₀)` shapes with `α ~ x`, `α ~ β₀` (`k = 0`); repair: the same `Γ_2` with `z = z' = α₀`, `u = u' = x`, `v = y`, `s = {x,y}` others singletons (`s u v`, `s u u'`, `s z z'`, `¬ s u z` hold, both edges kept), `L = rest`. `ScostLL` for `of_relabel`/`of_perm`: `φ = Sum.map id (swap 0 1)` (onto, fixes `inl`), reversed solid list. Second instance, `instCyc` on `Fin 2 ⊕ Fin 2` (two blue edges `inr 0 ⇄ inr 1`): the repair branch is forced. No external hypothesis occurs (no limit computation owed).

Command (scripts in `SP/T2195/`, `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`; `ll.py N` = N random graphs, 0–2 external × 1–4 internal vertices, all setoids of the output graph, witness searched in the order restriction/`s`, one merge, any setoid):

`bash $SP/T2195/run_all.sh > out_all.txt 2>&1` (70 s), `out_all.txt` verbatim:

```
scost(Gamma_2, bot) = 6
Loop(x) blue: bot 6 -> 8 ; alpha ~ x: 9
AddLoop(b0,blue): bot 6 -> 6
MoveLoop(b0): bot 6 -> 6 ; alpha ~ b0: 8
Contract(a0;x,y): bot 6 -> 6 ; {x,y}: 6 -> 5 ; repair {x,y,a0}: 5
instCyc scost bot = 0
Contract(z=2;u=v=3) on instCyc: bot -> -2 ; Gamma merged {2,3}: -2
Fin2+Fin1 Contract(z;x,y): bot 1 -> 1 ; {x,y}{z}: 1 -> 0 ; merged {x,y,z}: 0
placement Loop(x), alpha~x: 9 >= 8
placement MoveLoop(b0), alpha~b0: 8 >= 6
placement MoveSC(a0;x,y), alpha~x (k=1, SC pair): 6 >= 6 value 0
k=2 example Fin1+Fin0, x->a, a->x: T.scost(all one class) = 0  T.scost(split) = 1
Gamma_2 repair instance: u=x v=y u'=x z=z'=alpha_0, s={x,y}{a0}{b0}{a1}{b1}: Gamma.scost s = 6  Gamma_L.scost s + 2 = 5
  merged s0 = {x,y,a0}: separation x,y kept apart by s? s x y = True ; Gamma.scost s0 = 5 <= 5
loop      mode=iff       graphs=3000 setoids=433272 witness kinds={'plain': 433272} min slack by kind={'plain': 2} (8s)
loop      mode=arbitrary graphs=3000 setoids=405972 witness kinds={'plain': 405972} min slack by kind={'plain': 2} (7s)
addLoop   mode=iff       graphs=3000 setoids=107830 witness kinds={'plain': 107830} min slack by kind={'plain': 0} (2s)
addLoop   mode=arbitrary graphs=3000 setoids=101530 witness kinds={'plain': 101530} min slack by kind={'plain': 0} (2s)
moveLoop  mode=iff       graphs=3000 setoids=433272 witness kinds={'plain': 433272} min slack by kind={'plain': 0} (9s)
moveLoop  mode=arbitrary graphs=3000 setoids=405972 witness kinds={'plain': 405972} min slack by kind={'plain': 0} (8s)
contract  mode=iff       graphs=3000 setoids=131569 witness kinds={'plain': 108520, 'merge': 23049} min slack by kind={'plain': 0, 'merge': 0} (3s)
contract  mode=arbitrary graphs=3000 setoids=133092 witness kinds={'plain': 107359, 'merge': 25733} min slack by kind={'plain': 0, 'merge': 0} (3s)
moveSC arbitrary ({'plain': 24982, 'merge': 988}, {'plain': 0, 'merge': 0})
moveOut arbitrary ({'plain': 26187}, {'plain': 0})
dmove arbitrary ({'plain': 18332, 'merge': 87}, {'plain': 0, 'merge': 0})
contract, 6000 graphs, witnesses restricted to {s, merge(s,u,z)}: s0=s 251678, s0=merge 59771 (all in case [u]=[v]!=[z]: 59771), merge with both classes external 0, FAIL 0
(2a) class-sum form: setoids tested 34522, failures 0
(2c) identity with fresh vertex: setoids tested 125100 (of which alpha alone 34922), failures 0
(2c) localisation (one vertex type): setoids tested 35045, failures 0
placement loop     mode=arbitrary {('k', 0): 97903}  min(T.scost s - T.scost (split a s)) by k: {0: 0}
placement two-edge mode=arbitrary {('k', 2): 14243, 'k2 fails': 3489, ('k', 0): 59709, ('k', 1): 29418}  min(T.scost s - T.scost (split a s)) by k: {2: -2, 0: 0, 1: 0}
repair mode=iff: s0=s 84344, s0=merge 49057 | FAIL 0, merge with both classes external 0, merge cost != base 0, negative Delta without internal X=0 class 0
repair mode=arbitrary: s0=s 79215, s0=merge 63516 | FAIL 0, merge with both classes external 0, merge cost != base 0, negative Delta without internal X=0 class 0
E0: [elem(H-R+A)]-[elem H] >= -1 and = -1 -> elem H: violations 0 0 over 1679616
E1: elem(X+(1,1,0,0)) = decide(X=0): violations 0
E5: elem(X+(0,0,1,1)) = decide(X=0): violations 0
elem H -> H != 0: violations 0
E4: violations 0
E6: violations 0 over 3072
pairs not excluded by E6 (one colour, one in one out): 4
p=2: applications=27; 2p=4, 3p=6
min_s scost over all applications = 4 (2p = 4 ); attained at ['AddLoop', 'Contract', 'MoveLoop']
min_{s,not s x y} scost over all applications = 6 (3p = 6 ); attained at ['AddLoop', 'Contract', 'MoveLoop']
p=3: applications=36; 2p=6, 3p=9
min_s scost over all applications = 6 (2p = 6 ); attained at ['AddLoop', 'Contract', 'MoveLoop']
min_{s,not s x y} scost over all applications = 9 (3p = 9 ); attained at ['AddLoop', 'Contract', 'MoveLoop']
Dmove: instances 162 violations of "two uncircled non-loop alpha-edges + one old-only edge": 0
alpha-edge pattern types (q colour, alpha half-edges): [('blue', (('in', 'blue'), ('out', 'blue'))), ('red', (('out', 'blue'), ('out', 'red')))]
```

Reading of the output: lines 1-14 are the table's worked examples (`Γ_2`: `Loop(x)` 6 → 8, α~x: 9; `AddLoop(β₀)` 6 → 6; `MoveLoop(β₀)` 6 → 6, α~β₀: 8; `Contract(α₀;x,y)` 6 → 6, `{x,y}`: 6 → 5, repair `{x,y,α₀}`: 5; `instCyc`: `scost ⊥ = 0`, contract output `−2`, repair `−2`; placement 9 ≥ 8, 8 ≥ 6, 6 ≥ 6 with value 0; k = 2 counterexample 0 vs 1). Every witness for `loop`/`addLoop`/`moveLoop` is the restriction (resp. `s`), for `contract` `s` or the merge of the classes of `u` and `z` (only in case (b), never two external classes); for the c3 pins (informational; own copies of the primitives, hypotheses as pinned) `moveOut` needs only the restriction, `moveSC` and `dmove` need a one-merge witness for 988 resp. 87 setoids, and no setoid needs a witness outside restriction/one merge. The `Dmove` shape check: for both colours of `q`, the added list is two uncircled non-loop edges at `α` (`{a→α, α→v}` blue, `{α→b, α→v}` red) plus one edge on old vertices (`z→b` resp. `a→z`, goes into `L`), for every `q` (also `a = b`, `z = v`).

### Verdicts

Evidence for the generality notes (no statement change needed, none of them is a hypothesis of a pin): (1) the pins hold with no `CircIffLoop`/`Normal`; (2) the placement lemma holds for any colours and directions of the two `α` edges, so c3 needs no per-row version; (3) the repair lemma's two cycle edges must be uncircled non-loops: c3's `Dmove` pin supplies this (`z = v ↔ cp`, `q.src = q.dst ↔ q.circ`; at `k = 2`, `Z ≠ U` gives `z ≠ v` and `Z = B ≠ U` gives `a ≠ b`); (4) `k = 2` fails for placement (excluded, as the ticket says), so c3 needs the repair/direct route there; (5) the surgery identity (c) is exact for α alone and not alone.

- Targets 1 (composition API, `scostLL_refl`): PASS.
- Target 2 (surgery identity (a), (b), (c), localisation): PASS.
- Target 3 (pattern facts E0, E1/E5, E4, E6): PASS.
- Target 4 (placement, `k ≤ 1`, both shapes): PASS.
- Target 5 (repair, Γ-side form, no hypothesis on `Γ`): PASS.
- Target 6 (`scostLL_loop`, `_addLoop`, `_moveLoop`, `_contract`, pins without added hypotheses): PASS.
- §55 check (iii): PASS (4 and 6 at p = 2; 6 and 9 at p = 3); no statement here has a far/all switch.

## (b) Script output — Mon Oct  5 17:50:54 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2195`, branch `t/T2195`, HEAD `a768e91a2aa8ac1feb264dac0145b472c2a06a09`; sole writable file `RBM3D/Graph/LocalRegular6b.lean` (a new module importing `RBM3D.Graph.LocalRegular6a` only). Scripts and raw outputs are in `SP/T2195/` (`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`); no port from RBM1D/RBM2D (nothing copied).
### Build, registry pre-check, full build
```
Mon Oct  5 17:34:14 UTC 2026
$ lake build RBM3D.Graph.LocalRegular6b 2>&1 | tail -4

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
✔ [3386/3386] Built RBM3D.Graph.LocalRegular6b (5.0s)
Build completed successfully (3386 jobs).
Mon Oct  5 17:48:57 UTC 2026
$ python3 trace.py   # json.load of .lake/build/lib/lean/RBM3D/Graph/LocalRegular6b.trace: number of log entries, first 12 chars of each
1 log entries
['.> LEAN_PATH']
$ lake build RBM3D.Graph.LocalRegular6b 2>&1 | grep -c "LocalRegular6[ab].lean"   # warnings that name this module or its parent in an up-to-date build (the `Note:` line in the build tail above is replayed from an upstream module)
0
Mon Oct  5 17:36:34 UTC 2026
$ cat precheck.lean
import RBM3D
import RBM3D.Graph.LocalRegular6b

#assert_rbm_axioms
$ lake env lean precheck.lean > precheck_full.txt 2>&1; echo exit=$?; head -3 precheck_full.txt; wc -l < precheck_full.txt; grep -c error precheck_full.txt   # registry pre-check (DECISIONS §20 (2))
exit=0
axiom audit: 5751 theorems, 2043 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
     213
0
Mon Oct  5 17:36:24 UTC 2026
$ lake build   # full library in the worktree (the hub adds the root import at merge; the module itself is covered by the pre-check)
non-vacuity certificates: 0 of 128 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3999 jobs).
```
### Axioms
```
Mon Oct  5 17:35:12 UTC 2026
$ lake env lean axioms.lean   # Lean.collectAxioms over every constant of the module (env.header.moduleData), then #print axioms of the 7 pinned theorems
module RBM3D.Graph.LocalRegular6b: 212 constants (198 theorems, 14 definitions, 0 other); user-named public: 121; axioms used by any of them: [Quot.sound, Classical.choice, propext]; constants with a non-standard axiom: 0
'RBM.Graph.LGraph.ScostLL.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.ScostLL.of_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.ScostLL.of_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.scostLL_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.scostLL_addLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.scostLL_moveLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.scostLL_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### The seven pins and the instance shapes against the check file
```
Mon Oct  5 17:38:28 UTC 2026
$ md5 of T2184-check.lean:316-357 and of the 42-line c2 pin block of T2195-check.lean; diff
4826cdc5250a809ff964ec63d6442fa2
4826cdc5250a809ff964ec63d6442fa2
DIFF EMPTY (pins verbatim)
$ lake env lean pins_check.lean; echo exit=$?   # the 7 Pins in RBM.Graph.T2195Check, each `theorem chk_x : XPin := @name`
pins: 7 theorems checked by `@name` / by the instance; axioms used: [Quot.sound, Classical.choice, propext] 
exit=0
$ lake env lean shapes_check.lean; echo exit=$?   # the 7 Prop examples of section 3 of T2195-check.lean (S1..S7), each discharged by a file instance
shapes: 7 theorems checked by `@name` / by the instance; axioms used: [Quot.sound, Classical.choice, propext] 
exit=0
```
### Diff scope, forbidden tokens, name clash
```
Mon Oct  5 17:37:07 UTC 2026
$ git diff --stat main...t/T2195; git diff --name-only main...t/T2195
 RBM3D/Graph/LocalRegular6b.lean | 2382 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 2382 insertions(+)
RBM3D/Graph/LocalRegular6b.lean
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/LocalRegular6b.lean; grep -c "^open Classical$" RBM3D/Graph/LocalRegular6b.lean; grep -n "^import" RBM3D/Graph/LocalRegular6b.lean; wc -l RBM3D/Graph/LocalRegular6b.lean
0
0
6:import RBM3D.Graph.LocalRegular6a
    2382 RBM3D/Graph/LocalRegular6b.lean
$ grep -c "open Classical in" RBM3D/Graph/LocalRegular6b.lean; grep -c "^private theorem" RBM3D/Graph/LocalRegular6b.lean; grep -c "^theorem\|^def" RBM3D/Graph/LocalRegular6b.lean
62
42
112
Mon Oct  5 17:40:02 UTC 2026
$ grep -rn --include="*.lean" -E "scostLL_|localReg6b_|ScostLL\.(trans|of_perm|of_relabel)" RBM3D/RBM3D RBM3D-wt/*/RBM3D | grep -v "^RBM3D-wt/T2195/RBM3D/Graph/LocalRegular6b.lean" | wc -l   # main worktree and all 406 worktrees
       0
$ grep -c -E "scostLL_|localReg6b_|ScostLL\.(trans|of_perm|of_relabel)" <the new file>   # the pattern does match the new file
752
$ names of the 121 public constants of the module (Lean script names.lean): hits of each name (with `RBM.Graph.` stripped, `grep -rnw`) outside the new file
total hits outside the new file over the 121 names: 0
```
### Public declarations of the file (74; script `extract.py`: line, from `theorem NAME` to the first depth-0 `:=`; key statements one per line, the rest joined by ` || `, then the two `where` bodies)
```
86: theorem scostLL_refl {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) : LGraph.ScostLL Γ Γ
92: theorem LGraph.ScostLL.trans {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I') (U : LGraph E I'') : LGraph.ScostLL Γ T → LGraph.ScostLL T U → LGraph.ScostLL Γ U
102: theorem LGraph.ScostLL.of_perm {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (Γ : LGraph E I) (T T' : LGraph E I') : T.solid.Perm T'.solid → T.waved.length = T'.waved.length → LGraph.ScostLL Γ T → LGraph.ScostLL Γ T'
111: theorem LGraph.ScostLL.of_relabel {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I') (φ : E ⊕ I' → E ⊕ I'') : Function.Surjective φ → (∀ a : E, φ (Sum.inl a) = Sum.inl a) → LGraph.ScostLL Γ T → LGraph.ScostLL Γ (T.relabel φ)
137: def scostLL_kept (L : List (SEdge V)) (s : Setoid V) : List (SEdge V)
143: def scostLL_clsPat (L : List (SEdge V)) (s : Setoid V) (c : Quotient s) : ℕ × ℕ × ℕ × ℕ
325: theorem scostLL_scost_eq (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : Γ.scost s = ((scostLL_kept Γ.solid s).length : ℤ) + 2 * (Γ.waved.length : ℤ) + ∑ c ∈ Γ.sIntCls s, (scostLL_el (scostLL_clsPat Γ.solid s c) - 2)
465: theorem scostLL_fresh_scost (Γ : LGraph E I) (c : ℂ) (A : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) : (Γ.owxExt (owxEmb 1) c A W).scost s' = ((scostLL_kept Γ.solid (Setoid.comap (owxEmb 1) s')).length : ℤ) + ((scostLL_kept A s').length : ℤ) + 2 * ((Γ.waved.length : ℤ) + (W.length : ℤ)) + ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'), (scostLL_el (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) - 2) + (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then scostLL_el (scostLL_clsPat A s' (Quotient.mk s' (Sum.inr (Sum.inr 0)))) - 2 else 0)
500: theorem scostLL_local_diff (Γ Γ' : LGraph E I) (R A X : List (SEdge (E ⊕ I))) (s : Setoid (E ⊕ I)) (hΓ : Γ.solid.Perm (R ++ X)) (hΓ' : Γ'.solid.Perm (A ++ X)) : Γ'.scost s - Γ.scost s = ((scostLL_kept A s).length : ℤ) - ((scostLL_kept R s).length : ℤ) + 2 * ((Γ'.waved.length : ℤ) - (Γ.waved.length : ℤ)) + ∑ c ∈ Γ.sIntCls s, (scostLL_el (scostLL_clsPat A s c + scostLL_clsPat X s c) - scostLL_el (scostLL_clsPat R s c + scostLL_clsPat X s c))
621: theorem scostLL_loop (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) : LGraph.ScostLL Γ (lwPrimLoop Γ z col)
633: theorem scostLL_addLoop (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) : LGraph.ScostLL Γ (lwPrimAddLoop Γ z col)
638: theorem scostLL_moveLoop (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z : E ⊕ I) (col : Bool) (hperm : Γ.solid.Perm (⟨col, true, z, z⟩ :: rest)) : LGraph.ScostLL Γ (lwPrimMoveLoop Γ rest z col)
685: def scostLL_merge (s : Setoid V) (u z : V) : Setoid V where r a b
968: theorem scostLL_merge_scost (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (u z : E ⊕ I) (huz : ¬ s u z) : Γ.scost (scostLL_merge s u z) = Γ.scost s - ((scostLL_joined Γ.solid s u z).length : ℤ) + (if ((∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z)) then scostLL_el (scostLL_clsPat Γ.solid (scostLL_merge s u z) (Quotient.mk _ u)) - 2 else 0) - (if (∀ a : E, ¬ s (Sum.inl a) u) then scostLL_el (scostLL_clsPat Γ.solid s (Quotient.mk s u)) - 2 else 0) - (if (∀ a : E, ¬ s (Sum.inl a) z) then scostLL_el (scostLL_clsPat Γ.solid s (Quotient.mk s z)) - 2 else 0)
1256: theorem scostLL_repair (Γ : LGraph E I) (L : List (SEdge (E ⊕ I))) (col : Bool) (z v u' z' u : E ⊕ I) (s : Setoid (E ⊕ I)) (hΓ : Γ.solid.Perm (⟨col, false, z, v⟩ :: ⟨col, false, u', z'⟩ :: L)) (hv : s u v) (hu' : s u u') (hz' : s z z') (huz : ¬ s u z) : ∃ s₀ : Setoid (E ⊕ I), (s₀ = s ∨ s₀ = scostLL_merge s u z) ∧ (∀ a b : E, ¬ s (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧ Γ.scost s₀ ≤ ({ Γ with solid := L } : LGraph E I).scost s + 2
1391: theorem scostLL_contract (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (hu : u ≠ z) (hv : z ≠ v) (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest)) : LGraph.ScostLL Γ (lwPrimContract Γ rest z u v)
1483: def scostLL_split (a : V) (s : Setoid V) : Setoid V where r u v
1732: theorem scostLL_placement_loop (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I))) (col : Bool) (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++ [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩])) (s : Setoid (E ⊕ (I ⊕ Fin 1))) : T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ T.scost s
1826: theorem scostLL_placement_two (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I))) (e₁ e₂ : SEdge (E ⊕ (I ⊕ Fin 1))) (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++ [e₁, e₂])) (c₁ : e₁.circ = false) (h₁ : (e₁.src = Sum.inr (Sum.inr 0) ∧ e₁.dst ≠ Sum.inr (Sum.inr 0)) ∨ (e₁.dst = Sum.inr (Sum.inr 0) ∧ e₁.src ≠ Sum.inr (Sum.inr 0))) (c₂ : e₂.circ = false) (h₂ : (e₂.src = Sum.inr (Sum.inr 0) ∧ e₂.dst ≠ Sum.inr (Sum.inr 0)) ∨ (e₂.dst = Sum.inr (Sum.inr 0) ∧ e₂.src ≠ Sum.inr (Sum.inr 0))) (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk : ¬ (s e₁.src e₁.dst ∧ s e₂.src e₂.dst)) : T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ T.scost s
1848: theorem scostLL_placement (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I))) (Aα : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++ Aα)) (hA : (∃ col : Bool, Aα = [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]) ∨ ∃ e₁ e₂ : SEdge (E ⊕ (I ⊕ Fin 1)), Aα = [e₁, e₂] ∧ e₁.circ = false ∧ ((e₁.src = Sum.inr (Sum.inr 0) ∧ e₁.dst ≠ Sum.inr (Sum.inr 0)) ∨ (e₁.dst = Sum.inr (Sum.inr 0) ∧ e₁.src ≠ Sum.inr (Sum.inr 0))) ∧ e₂.circ = false ∧ ((e₂.src = Sum.inr (Sum.inr 0) ∧ e₂.dst ≠ Sum.inr (Sum.inr 0)) ∨ (e₂.dst = Sum.inr (Sum.inr 0) ∧ e₂.src ≠ Sum.inr (Sum.inr 0)))) (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk : ∀ e₁ e₂ : SEdge (E ⊕ (I ⊕ Fin 1)), Aα = [e₁, e₂] → ¬ (s e₁.src e₁.dst ∧ s e₂.src e₂.dst)) : T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ T.scost s
1890: theorem scostLL_local_diff_C (Γ Γ' : LGraph E I) (R A X : List (SEdge (E ⊕ I))) (s : Setoid (E ⊕ I)) (hΓ : Γ.solid.Perm (R ++ X)) (hΓ' : Γ'.solid.Perm (A ++ X)) (C : Finset (Quotient s)) (hR : ∀ e ∈ R, Quotient.mk s e.src ∈ C ∧ Quotient.mk s e.dst ∈ C) (hA : ∀ e ∈ A, Quotient.mk s e.src ∈ C ∧ Quotient.mk s e.dst ∈ C) : Γ'.scost s - Γ.scost s = ((scostLL_kept A s).length : ℤ) - ((scostLL_kept R s).length : ℤ) + 2 * ((Γ'.waved.length : ℤ) - (Γ.waved.length : ℤ)) + ∑ c ∈ C, (if c ∈ Γ.sIntCls s then scostLL_el (scostLL_clsPat A s c + scostLL_clsPat X s c) - scostLL_el (scostLL_clsPat R s c + scostLL_clsPat X s c) else 0)
1912: theorem scostLL_fresh_dropped (Γ : LGraph E I) (c : ℂ) (A : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (hA : scostLL_kept A s' = []) (hna : ¬ ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) : (Γ.owxExt (owxEmb 1) c A W).scost s' = Γ.scost (Setoid.comap (owxEmb 1) s') + 2 * (W.length : ℤ)
147: def scostLL_el (h : ℕ × ℕ × ℕ × ℕ) : ℤ || 149: theorem scostLL_el_nonneg (h : ℕ × ℕ × ℕ × ℕ) : 0 ≤ scostLL_el h || 152: theorem scostLL_el_le_one (h : ℕ × ℕ × ℕ × ℕ) : scostLL_el h ≤ 1 || 173: def scostLL_hin (σ : Bool) : ℕ × ℕ × ℕ × ℕ || 176: def scostLL_hout (σ : Bool) : ℕ × ℕ × ℕ × ℕ || 178: theorem scostLL_mem_kept (L : List (SEdge V)) (s : Setoid V) (e : SEdge V) : e ∈ scostLL_kept L s ↔ e ∈ L ∧ (e.circ = true ∨ ¬ s e.src e.dst) || 183: theorem scostLL_kept_append (L₁ L₂ : List (SEdge V)) (s : Setoid V) : scostLL_kept (L₁ ++ L₂) s = scostLL_kept L₁ s ++ scostLL_kept L₂ s
186: theorem scostLL_kept_perm {L₁ L₂ : List (SEdge V)} (h : L₁.Perm L₂) (s : Setoid V) : (scostLL_kept L₁ s).Perm (scostLL_kept L₂ s) || 190: theorem scostLL_clsPat_append (L₁ L₂ : List (SEdge V)) (s : Setoid V) (c : Quotient s) : scostLL_clsPat (L₁ ++ L₂) s c = scostLL_clsPat L₁ s c + scostLL_clsPat L₂ s c || 196: theorem scostLL_clsPat_perm {L₁ L₂ : List (SEdge V)} (h : L₁.Perm L₂) (s : Setoid V) (c : Quotient s) : scostLL_clsPat L₁ s c = scostLL_clsPat L₂ s c || 201: theorem scostLL_clsPat_nil (s : Setoid V) (c : Quotient s) : scostLL_clsPat [] s c = 0
212: theorem scostLL_halfPat_single (e : SEdge V) (K : V → Prop) [DecidablePred K] : lwHalfPat [e] K = (if K e.dst then scostLL_hin e.σ else 0) + (if K e.src then scostLL_hout e.σ else 0) || 218: theorem scostLL_halfPat_zero (es : List (SEdge V)) (K : V → Prop) [DecidablePred K] (h : ∀ w, ¬ K w) : lwHalfPat es K = 0 || 226: theorem scostLL_elem_E0 (X R A : ℕ × ℕ × ℕ × ℕ) : -1 ≤ scostLL_el (X + A) - scostLL_el (X + R) ∧ (scostLL_el (X + A) - scostLL_el (X + R) = -1 → lwElem (X + R) = true) || 237: theorem scostLL_elem_E3 (X R : ℕ × ℕ × ℕ × ℕ) : scostLL_el (X + R) - scostLL_el (X + R) = 0
240: theorem scostLL_elem_E1 (X : ℕ × ℕ × ℕ × ℕ) : scostLL_el (X + (1, 1, 0, 0)) = if X = 0 then 1 else 0 || 246: theorem scostLL_elem_E5 (X : ℕ × ℕ × ℕ × ℕ) : scostLL_el (X + (0, 0, 1, 1)) = if X = 0 then 1 else 0 || 252: theorem scostLL_elem_ne_zero {H : ℕ × ℕ × ℕ × ℕ} (h : lwElem H = true) : H ≠ 0 || 258: theorem scostLL_elem_E4col (H : ℕ × ℕ × ℕ × ℕ) (h1 : 0 < H.1 + H.2.1) (h2 : 0 < H.2.2.1 + H.2.2.2) : lwElem H = false || 265: theorem scostLL_elem_E4out (H : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ H.2.1 + H.2.2.2) : lwElem H = false || 271: theorem scostLL_elem_E4in (H : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ H.1 + H.2.2.1) : lwElem H = false
277: theorem scostLL_elem_E6col (H A : ℕ × ℕ × ℕ × ℕ) (h1 : 0 < A.1 + A.2.1) (h2 : 0 < A.2.2.1 + A.2.2.2) : lwElem (H + A) = false || 282: theorem scostLL_elem_E6out (H A : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ A.2.1 + A.2.2.2) : lwElem (H + A) = false || 286: theorem scostLL_elem_E6in (H A : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ A.1 + A.2.2.1) : lwElem (H + A) = false || 341: theorem scostLL_kept_map {V W : Type} (L : List (SEdge V)) (f : V → W) (s : Setoid W) : scostLL_kept (L.map (SEdge.map f)) s = (scostLL_kept L (Setoid.comap f s)).map (SEdge.map f)
350: theorem scostLL_clsPat_map {V W : Type} (L : List (SEdge V)) (f : V → W) (s : Setoid W) (c : Quotient (Setoid.comap f s)) : scostLL_clsPat (L.map (SEdge.map f)) s (localReg6a_qmap f s c) = scostLL_clsPat L (Setoid.comap f s) c || 362: theorem scostLL_emb_cases (w : E ⊕ (I ⊕ Fin 1)) : (∃ v : E ⊕ I, w = owxEmb 1 v) ∨ w = Sum.inr (Sum.inr 0) || 369: theorem scostLL_emb_ne_alpha (v : E ⊕ I) : owxEmb 1 v ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) || 372: theorem scostLL_inl_ne_alpha (a : E) : (Sum.inl a : E ⊕ (I ⊕ Fin 1)) ≠ Sum.inr (Sum.inr 0)
375: theorem scostLL_clsPat_map_alpha (L : List (SEdge (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) : scostLL_clsPat (L.map (SEdge.map (owxEmb 1))) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) = 0 || 386: theorem scostLL_qmap_range (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (c' : Quotient s') : (∃ c₀, localReg6a_qmap (owxEmb 1) s' c₀ = c') ↔ ¬ ((∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) ∧ c' = Quotient.mk s' (Sum.inr (Sum.inr 0)))
409: theorem scostLL_intCls_emb (Γ : LGraph E I) (T : LGraph E (I ⊕ Fin 1)) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) : T.sIntCls s' = (Γ.sIntCls (Setoid.comap (owxEmb 1) s')).image (localReg6a_qmap (owxEmb 1) s') ∪ (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then {Quotient.mk s' (Sum.inr (Sum.inr 0))} else ∅) || 442: theorem scostLL_sum_intCls_emb (Γ : LGraph E I) (T : LGraph E (I ⊕ Fin 1)) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (g : Quotient s' → ℤ) : ∑ c' ∈ T.sIntCls s', g c' = ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'), g (localReg6a_qmap (owxEmb 1) s' c₀) + (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then g (Quotient.mk s' (Sum.inr (Sum.inr 0))) else 0)
532: theorem scostLL_sum_single {Q : Type} (S : Finset Q) (d : Q → ℤ) (c₀ : Q) (h : ∀ c, c ≠ c₀ → d c = 0) : ∑ c ∈ S, d c = if c₀ ∈ S then d c₀ else 0 || 539: theorem scostLL_clsPat_loop {V : Type} (col : Bool) (v : V) (s : Setoid V) (c : Quotient s) : scostLL_clsPat [⟨col, true, v, v⟩] s c = if Quotient.mk s v = c then scostLL_hin col + scostLL_hout col else 0 || 547: theorem scostLL_el_pair (col : Bool) : scostLL_el (scostLL_hin col + scostLL_hout col) = 1 || 722: def scostLL_qmerge (s : Setoid V) (u z : V) : Quotient s → Quotient (scostLL_merge s u z)
728: theorem scostLL_qmerge_eq_iff (s : Setoid V) (u z : V) (c c' : Quotient s) : scostLL_qmerge s u z c = scostLL_qmerge s u z c' ↔ c = c' ∨ (c = Quotient.mk s u ∧ c' = Quotient.mk s z) ∨ (c = Quotient.mk s z ∧ c' = Quotient.mk s u) || 760: def scostLL_joined (L : List (SEdge V)) (s : Setoid V) (u z : V) : List (SEdge V) || 881: theorem scostLL_mk_mem_sIntCls (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (v : E ⊕ I) : Quotient.mk s v ∈ Γ.sIntCls s ↔ ∀ a : E, ¬ s (Sum.inl a) v || 1105: theorem scostLL_sum_two {Q : Type} (S : Finset Q) (a b : Q) (hab : a ≠ b) (d : Q → ℤ) (h : ∀ c, c ≠ a → c ≠ b → d c = 0) : ∑ c ∈ S, d c = (if a ∈ S then d a else 0) + (if b ∈ S then d b else 0)
1118: theorem scostLL_el_zero : scostLL_el (0 : ℕ × ℕ × ℕ × ℕ) = 0 || 1122: theorem scostLL_el_pair_add (col : Bool) (X : ℕ × ℕ × ℕ × ℕ) : scostLL_el (scostLL_hin col + scostLL_hout col + X) = if X = 0 then 1 else 0 || 1322: theorem scostLL_clsPat_single_kept {V : Type} (σ : Bool) (a b : V) (s : Setoid V) (h : ¬ s a b) (c : Quotient s) : scostLL_clsPat [⟨σ, false, a, b⟩] s c = (if Quotient.mk s b = c then scostLL_hin σ else 0) + (if Quotient.mk s a = c then scostLL_hout σ else 0) || 1330: theorem scostLL_clsPat_single_dropped {V : Type} (σ : Bool) (a b : V) (s : Setoid V) (h : s a b) (c : Quotient s) : scostLL_clsPat [⟨σ, false, a, b⟩] s c = 0
1502: theorem scostLL_split_alone (a : V) (s : Setoid V) : ∀ w, scostLL_split a s w a → w = a || 1507: theorem scostLL_split_of_alone (a : V) (s : Setoid V) (halone : ∀ w, s w a → w = a) : scostLL_split a s = s || 1523: theorem scostLL_split_merge (a w₀ : V) (s : Setoid V) (hw : s w₀ a) (hne : w₀ ≠ a) : s = scostLL_merge (scostLL_split a s) a w₀ || 1576: theorem scostLL_split_comap (s : Setoid (E ⊕ (I ⊕ Fin 1))) : Setoid.comap (owxEmb 1) (scostLL_split (Sum.inr (Sum.inr 0)) s) = Setoid.comap (owxEmb 1) s || 1588: theorem scostLL_split_inl (s : Setoid (E ⊕ (I ⊕ Fin 1))) (a b : E) : scostLL_split (Sum.inr (Sum.inr 0)) s (Sum.inl a) (Sum.inl b) ↔ s (Sum.inl a) (Sum.inl b)
1873: theorem scostLL_sum_support {Q : Type} [DecidableEq Q] (S C : Finset Q) (d : Q → ℤ) (h : ∀ c, c ∉ C → d c = 0) : ∑ c ∈ S, d c = ∑ c ∈ C, (if c ∈ S then d c else 0) || 1881: theorem scostLL_clsPat_zero_of_ends {V : Type} (R : List (SEdge V)) (s : Setoid V) (c : Quotient s) (h : ∀ e ∈ R, Quotient.mk s e.src ≠ c ∧ Quotient.mk s e.dst ≠ c) : scostLL_clsPat R s c = 0
685-686: def scostLL_merge ... where r a b := s a b ∨ (s a u ∧ s z b) ∨ (s a z ∧ s u b)   (iseqv by cases)  ||  1483-1484: def scostLL_split ... where r u v := u = v ∨ (u ≠ a ∧ v ≠ a ∧ s u v)
```
### Compiled instances of the file (38 declarations `localReg6b_inst*`, `localReg6b_instCyc*`, `localReg6b_phi*`, `localReg6b_instS`; same script; data of `localReg6b_instCyc`: solid `[⟨true, false, inr 0, inr 1⟩, ⟨true, false, inr 1, inr 0⟩]`, no waved or dotted edge, coefficient 1)
```
1940: theorem localReg6b_inst_loop : LGraph.ScostLL (fxyPowGraph 2) (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true)
1946: theorem localReg6b_inst_T1 (m : ℂ) (Γ : LGraph E I) (x : I) : LGraph.ScostLL Γ (owxT1 m Γ x)
1951: theorem localReg6b_inst_addLoop : LGraph.ScostLL (fxyPowGraph 2) (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true)
1961: theorem localReg6b_inst_moveLoop : LGraph.ScostLL (fxyPowGraph 2) (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
1974: theorem localReg6b_inst_contract : LGraph.ScostLL localReg6b_instCyc (lwPrimContract localReg6b_instCyc [] (.inr 0) (.inr 1) (.inr 1))
2017: theorem localReg6b_inst_repair : ∃ s₀ : Setoid (Fin 2 ⊕ Fin 2), (s₀ = ⊥ ∨ s₀ = scostLL_merge ⊥ (Sum.inr 1) (Sum.inr 0)) ∧ (∀ a b : Fin 2, ¬ (⊥ : Setoid (Fin 2 ⊕ Fin 2)) (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧ localReg6b_instCyc.scost s₀ ≤ ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).scost ⊥ + 2
2031: theorem localReg6b_inst_R2 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (y y' : E ⊕ I) (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y) (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) : LGraph.ScostLL Γ (oe2xR2 m Γ q x y y')
2044: theorem localReg6b_inst_trans : LGraph.ScostLL (fxyPowGraph 2) (lwPrimAddLoop (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) (Sum.inr (Sum.inr 0)) false)
2063: theorem localReg6b_inst_T2 : LGraph.ScostLL (fxyPowGraph 2) ((lwPrimLoop (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true) (Sum.inr (Sum.inr 0)) true).relabel localReg6b_phi)
2074: theorem localReg6b_inst_T2_all : ∀ φ : Fin 2 ⊕ ((Fin (2 * 2) ⊕ Fin 1) ⊕ Fin 1) → Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 2), Function.Surjective φ → (∀ a : Fin 2, φ (Sum.inl a) = Sum.inl a) → LGraph.ScostLL (fxyPowGraph 2) ((lwPrimLoop (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true) (Sum.inr (Sum.inr 0)) true).relabel φ)
2089: theorem localReg6b_inst_transfer : ∀ {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (Γ : LGraph (Fin 2) I) (T : LGraph (Fin 2) I') (far : Bool) (k : ℤ), LGraph.ScostLL Γ T → (∀ s₀ : Setoid (Fin 2 ⊕ I), (far = true → ¬ s₀ (Sum.inl 0) (Sum.inl 1)) → k ≤ LGraph.scost Γ s₀) → ∀ s : Setoid (Fin 2 ⊕ I'), (far = true → ¬ s (Sum.inl 0) (Sum.inl 1)) → k ≤ LGraph.scost T s
2100: theorem localReg6b_inst_moveSC_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk : ¬ (s (owxEmb 1 u) (Sum.inr (Sum.inr 0)) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 v))) : (lwPrimMoveSC Γ rest z u v).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ (lwPrimMoveSC Γ rest z u v).scost s
2112: theorem localReg6b_inst_moveOut_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I) (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk : ¬ (s (Sum.inr (Sum.inr 0)) (owxEmb 1 v) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 d))) : (lwPrimMoveOut Γ rest z v d).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ (lwPrimMoveOut Γ rest z v d).scost s
2125: theorem localReg6b_inst_dmoveBlue_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (q : SEdge (E ⊕ I)) (hq : q.σ = true) (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk : ¬ (s (owxEmb 1 q.src) (Sum.inr (Sum.inr 0)) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 v))) : (lwPrimDmove Γ rest z v q).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ (lwPrimDmove Γ rest z v q).scost s
2143: theorem localReg6b_inst_dmoveRed_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (q : SEdge (E ⊕ I)) (hq : q.σ = false) (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk : ¬ (s (Sum.inr (Sum.inr 0)) (owxEmb 1 q.dst) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 v))) : (lwPrimDmove Γ rest z v q).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ (lwPrimDmove Γ rest z v q).scost s
2163: theorem localReg6b_inst_moveSC_k2 (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest)) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (hu : s' (owxEmb 1 u) (Sum.inr (Sum.inr 0))) (hv : s' (Sum.inr (Sum.inr 0)) (owxEmb 1 v)) (huz : ¬ s' (owxEmb 1 u) (owxEmb 1 z)) : ∃ s₀ : Setoid (E ⊕ I), (∀ a b : E, ¬ s' (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧ Γ.scost s₀ ≤ (lwPrimMoveSC Γ rest z u v).scost s'
2204: theorem localReg6b_inst_patterns : scostLL_el (((1, 1, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = 0 ∧ scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = 1 ∧ scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + (0, 0, 1, 1)) = 1 ∧ (scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + 0) - scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = -1 ∧ lwElem ((0 : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = true) ∧ scostLL_el (((1, 0, 2, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 0, 1)) - scostLL_el (((1, 0, 2, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 0, 1)) = 0 ∧ lwElem ((1, 0, 1, 0) : ℕ × ℕ × ℕ × ℕ) = false ∧ lwElem ((0, 1, 0, 1) : ℕ × ℕ × ℕ × ℕ) = false ∧ lwElem ((1, 0, 1, 0) : ℕ × ℕ × ℕ × ℕ) = false ∧ lwElem (((1, 0, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 1, 0)) = false ∧ lwElem (((0, 0, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 0, 1)) = false ∧ lwElem (((0, 0, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (1, 0, 1, 0)) = false ∧ ((1, 1, 0, 0) : ℕ × ℕ × ℕ × ℕ) ≠ 0
2343: theorem localReg6b_inst_contractGamma2 : LGraph.ScostLL (fxyPowGraph 2) (lwPrimContract (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1))
2350: theorem localReg6b_inst_s55 {I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph (Fin 2) I') (hT : LGraph.ScostLL (fxyPowGraph 2) T) : (∀ s : Setoid (Fin 2 ⊕ I'), 4 ≤ T.scost s) ∧ (∀ s : Setoid (Fin 2 ⊕ I'), ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ T.scost s)
1956: theorem localReg6b_inst_moveLoopPerm : (fxyPowGraph 2).solid.Perm (⟨true, true, Sum.inr 1, Sum.inr 1⟩ :: (fxyPowGraph 2).solid.tail) || 1966: def localReg6b_instCyc : LGraph (Fin 2) (Fin 2) where solid || 1980: theorem localReg6b_instCyc_bot : localReg6b_instCyc.scost ⊥ = 0 || 1991: theorem localReg6b_instCyc_contract_bot : (lwPrimContract localReg6b_instCyc [] (.inr 0) (.inr 1) (.inr 1)).scost ⊥ = -2 || 2006: theorem localReg6b_instCyc_L_bot : ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).scost ⊥ = -4 || 2025: theorem localReg6b_instCyc_repair_forced : ¬ localReg6b_instCyc.scost ⊥ ≤ ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).scost ⊥ + 2
2052: def localReg6b_phi : Fin 2 ⊕ ((Fin (2 * 2) ⊕ Fin 1) ⊕ Fin 1) → Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 2) || 2056: theorem localReg6b_phi_surj : Function.Surjective localReg6b_phi || 2188: theorem localReg6b_inst_loop_placement (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) (s : Setoid (E ⊕ (I ⊕ Fin 1))) : (lwPrimLoop Γ z col).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ (lwPrimLoop Γ z col).scost s
2194: theorem localReg6b_inst_moveLoop_placement (s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1))) : (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost s || 2239: theorem localReg6b_inst_refl : LGraph.ScostLL (fxyPowGraph 2) (fxyPowGraph 2) || 2243: theorem localReg6b_inst_scost_eq (s : Setoid (Fin 2 ⊕ Fin (2 * 2))) : (fxyPowGraph 2).scost s = ((scostLL_kept (fxyPowGraph 2).solid s).length : ℤ) + 2 * ((fxyPowGraph 2).waved.length : ℤ) + ∑ c ∈ (fxyPowGraph 2).sIntCls s, (scostLL_el (scostLL_clsPat (fxyPowGraph 2).solid s c) - 2)
2252: theorem localReg6b_inst_fresh_classes (s' : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1))) : (∀ c' : Quotient s', (∃ c₀, localReg6a_qmap (owxEmb 1) s' c₀ = c') ↔ ¬ ((∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) ∧ c' = Quotient.mk s' (Sum.inr (Sum.inr 0)))) ∧ (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).sIntCls s' = ((fxyPowGraph 2).sIntCls (Setoid.comap (owxEmb 1) s')).image (localReg6a_qmap (owxEmb 1) s') ∪ (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then {Quotient.mk s' (Sum.inr (Sum.inr 0))} else ∅) || 2264: def localReg6b_instS : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1))
2272: theorem localReg6b_inst_moveSC_Gamma2 : (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost (scostLL_split (Sum.inr (Sum.inr 0)) localReg6b_instS) ≤ (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost localReg6b_instS
2287: theorem localReg6b_inst_surgery (s' : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1))) : (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).scost s' = ((scostLL_kept (fxyPowGraph 2).solid (Setoid.comap (owxEmb 1) s')).length : ℤ) + ((scostLL_kept [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)))] s').length : ℤ) + 2 * (((fxyPowGraph 2).waved.length : ℤ) + 1) + ∑ c₀ ∈ (fxyPowGraph 2).sIntCls (Setoid.comap (owxEmb 1) s'), (scostLL_el (scostLL_clsPat (fxyPowGraph 2).solid (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)))] s' (localReg6a_qmap (owxEmb 1) s' c₀)) - 2) + (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then scostLL_el (scostLL_clsPat [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)))] s' (Quotient.mk s' (Sum.inr (Sum.inr 0)))) - 2 else 0)
2308: theorem localReg6b_inst_localise (s : Setoid (Fin 2 ⊕ Fin (2 * 2))) : (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).scost s - (fxyPowGraph 2).scost s = ((scostLL_kept [(⟨true, true, Sum.inr 1, Sum.inr 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2)))] s).length : ℤ) - ((scostLL_kept ([] : List (SEdge (Fin 2 ⊕ Fin (2 * 2)))) s).length : ℤ) + 2 * (((lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).waved.length : ℤ) - (fxyPowGraph 2).waved.length) + ∑ c ∈ ({Quotient.mk s (Sum.inr 1)} : Finset (Quotient s)), (if c ∈ (fxyPowGraph 2).sIntCls s then scostLL_el (scostLL_clsPat [(⟨true, true, Sum.inr 1, Sum.inr 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2)))] s c + scostLL_clsPat (fxyPowGraph 2).solid s c) - scostLL_el (scostLL_clsPat ([] : List (SEdge (Fin 2 ⊕ Fin (2 * 2)))) s c + scostLL_clsPat (fxyPowGraph 2).solid s c) else 0)
2329: theorem localReg6b_inst_contractPerm : (fxyPowGraph 2).solid.Perm ((⟨true, false, Sum.inr 0, Sum.inl 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨true, false, Sum.inl 0, Sum.inr 0⟩ :: [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩])
2360: theorem localReg6b_inst_s55_prims : ((∀ s, 4 ≤ (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).scost s) ∧ (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).scost s)) ∧ ((∀ s, 4 ≤ (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).scost s) ∧ (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).scost s)) ∧ ((∀ s, 4 ≤ (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost s) ∧ (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost s)) ∧ ((∀ s, 4 ≤ (lwPrimContract (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost s) ∧ (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ (lwPrimContract (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost s))
```
### Scratch check (not in the file)
```
Mon Oct  5 17:50:06 UTC 2026
$ lake env lean normal_check.lean   # example : ¬ localReg6b_instCyc.Normal := by decide
'RBM.Graph.localReg6b_instCyc_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
### Narrative (facts only)
- File `RBM3D/Graph/LocalRegular6b.lean`: 2382 lines (ticket estimate 1400-1900, stop threshold 2500), 74 public non-instance declarations (listed above), 42 `private theorem` helpers, 38 instance declarations, 62 `open Classical in`, no file-level `open Classical`, no new Prop-valued definition (no registry line is owed; the pre-check has exit 0), 0 `sorry`/`axiom`.
- Target 1: the three composition theorems have the binder order of the Pins (each Pin is discharged by `@name`, no wrapper); `trans` composes `s ↦ s₁ ↦ s₀`; `of_perm` is `LGraph.scost_perm`; `of_relabel` takes the witness of `Setoid.comap φ s` and uses `LGraph.scost_relabel` with `ext = id`.
- Target 2: `scostLL_scost_eq` is `unfold LGraph.scost` with `sElemCls = sIntCls.filter` (`Finset.card_filter`); `scostLL_fresh_scost` splits the sum over `T.sIntCls s'` into the image of `Γ.sIntCls s₀` under `localReg6a_qmap` and the class of `α` if alone (`scostLL_intCls_emb`, `scostLL_qmap_range`, `Finset.sum_union`, `Finset.sum_image`); `scostLL_local_diff` and `_C` are the class-sum difference for one vertex type (`_C`: localised to a `Finset (Quotient s)` containing the classes of the ends); `scostLL_merge_scost` is the exact cost change of merging two classes: `- #joined + [both int](el m - 2) - [U int](el a - 2) - [Z int](el b - 2)`.
- Target 6, routes: `loop` and `moveLoop` use no placement lemma: `scostLL_fresh_loop` gives `Γ₁.scost s₀ + 2 |W| ≤ T.scost s'` for every `s'` (α alone: every `A_{q c₀}` is `0`; α in a class: one nonzero term, `scostLL_sum_single`), and `moveLoop` adds `Γ.scost s₀ ≤ Γ₁.scost s₀ + 2` from `scostLL_local_diff`; `addLoop` is Lemma A; `contract`: `scostLL_contract_aux` (the patterns of `A` and `R` agree off `[z]`, so `T.scost s - Γ.scost s ≥ #kept A - #kept R + 1`) covers the cases (a), (c1), (c2), (d) with `s₀ = s`, and `scostLL_repair` with `scostLL_contract_dropped` covers `[u] = [v] ≠ [z]`.
- Target 5: `scostLL_repair_diff` gives `Γ_L.scost s - Γ.scost s = -2 + [U int] f_U + [Z int] f_Z`, `scostLL_repair_merge` and `scostLL_repair_m` give the merged cost (`m = X_U + X_Z` when no other edge joins the two classes); the proof splits on (`U` internal, `Z` internal, `X_U = 0 ∨ X_Z = 0`): `s₀ = s` if both are external or both internal with `X_U ≠ 0 ≠ X_Z`, the merge otherwise; the merge is never used with both classes external (`scostLL_merge_iff`).
- Target 4: `s = scostLL_merge (scostLL_split α s) α w₀` (`scostLL_split_merge`), `scostLL_placement_gen` applies `scostLL_merge_scost` at the split setoid; loop shape: `#joined = 0`, `[elem A_α] = 1`; two-edge shape: `#joined = k ≤ 1` and, for `k = 1` with `[elem A_α] = 1`, `scostLL_psi_sc` (16 cases by `decide`) gives `A_α` = the pair of the dropped edge, hence `m = b`; `scostLL_placement_two_aux` assumes `¬ s e₂.src e₂.dst`, `scostLL_placement_two` swaps the edges (`List.Perm.swap`) for the other case.
- Target 3: the pattern facts are stated with the residual `X` (`H = X + R`, no truncated subtraction in `ℕ⁴`): `scostLL_elem_E0 X R A : -1 ≤ el (X + A) - el (X + R) ∧ (… = -1 → lwElem (X + R) = true)`.
- Pins: none of the seven theorems has a hypothesis on `Γ` (no `CircIffLoop`, no `Normal`); the hypotheses `u ≠ z`, `z ≠ v` of the `scostLL_contract` Pin are not used by its proof.
- Instances (1)-(7) are those of the ticket (`localReg6b_inst_loop`, `_T1`, `_addLoop`, `_moveLoop`, `_contract`, `_R2`, `_trans`, `_T2` with the explicit `localReg6b_phi`, `_T2_all`, `_transfer`); (8): `localReg6b_inst_moveSC/moveOut/dmoveBlue/dmoveRed_placement` apply `scostLL_placement` itself (shape `Or.inr`, every shape hypothesis discharged, `hk` is the `k ≤ 1` hypothesis; the third added edge of `Dmove` is moved into `L` by `List.Perm`), `localReg6b_inst_moveSC_k2` applies `scostLL_repair` after `scostLL_fresh_dropped`, `localReg6b_inst_moveSC_Gamma2` is a concrete case (`Γ_2`, `α ~ x`, `k = 1`); `localReg6b_inst_s55_prims`: `4 ≤ scost` and, for far merges, `6 ≤ scost` for `Loop`, `AddLoop`, `MoveLoop`, `Contract` at `Γ_2`, from `localReg6b_inst_transfer` and `localReg6a_inst_cost2`.
- `localReg6b_instCyc` is not `Normal` (no `×`-dotted edge between its two joined vertices), so its values are computed with `localReg6a_sIntCls_bot_card` and `localReg6a_sElemCls_bot_card`: `scost ⊥ = 0`, contracted `-2`, cycle removed `-4`; `localReg6b_instCyc_repair_forced`: `s₀ = ⊥` is not a witness at `s = ⊥`; `localReg6b_inst_repair`: the lemma still provides one.
## (c) Verified Mathlib and core names (script `chk_names.lean`: 126 identifiers of the file with a core/Mathlib root or a lemma-like name, `env.contains`: 115 found; the 11 others are 6 `.1`/`.2` projection tokens of 5 lemmas, the field `length_eq` (of `List.Perm`) and the tactic names `push_cast`, `set_option`, `simp_all`, `split_ifs`; script `chk_names2.lean` (Mon Oct 5 17:50:54 UTC 2026): `[(Finset.disjoint_singleton_right, true), (Finset.mem_filter, true), (Finset.mem_image, true), (Finset.mem_inter, true), (List.mem_map, true), (List.Perm.length_eq, true)] `; names verified absent: none searched)
- `Bool`: `and_eq_true`, `not_eq_true'`
- `Equiv`: `refl`, `sumAssoc`, `sumCongr`
- `Finset`: `card_filter`, `inter_comm`, `inter_subset_left`, `mem_filter`, `mem_image`, `mem_singleton`, `mem_singleton_self`, `mem_union`, `notMem_empty`, `sum_add_distrib`, `sum_congr`, `sum_const`, `sum_const_zero`, `sum_eq_single_of_mem`, `sum_eq_zero`, `sum_filter`, `sum_image`, `sum_ite_eq'`, `sum_ite_mem`, `sum_singleton`, `sum_sub_distrib`, `sum_subset`, `sum_union`, `union_empty`
- `Function`: `Surjective`, `Surjective.sumMap`, `surjective_id`
- `Iff`: `rfl`, `symm`, `trans`
- `Int`: `natCast_nonneg`
- `List`: `Perm.append_left`, `Perm.cons`, `Perm.refl`, `Perm.swap`, `append_assoc`, `append_nil`, `cons.injEq`, `countP_eq_zero`, `eq_nil_iff_forall_not_mem`, `filter_append`, `filter_append_perm`, `filter_congr`, `filter_eq_self`, `filter_filter`, `filter_map`, `filter_nil`, `length_append`, `length_cons`, `length_map`, `length_nil`, `length_singleton`, `map_append`, `map_cons`, `map_id''`, `map_nil`, `mem_cons`, `mem_filter`, `mem_singleton`, `nil_append`, `not_mem_nil`, `perm_append_singleton`, `perm_middle`
- `Nat`: `cast_one`, `cast_zero`
- `Or`: `inl`, `inr`
- `Prod`: `ext`, `ext_iff`, `fst_add`, `fst_zero`, `mk.injEq`, `snd_add`, `snd_zero`
- `Quotient`: `eq`, `exact`, `exists_rep`, `map`, `mk`, `sound`
- `Set`: `InjOn`
- `Setoid`: `comap`, `comap_rel`, `ext`, `ker`
- `Subsingleton`: `elim`
- `Sum`: `inl`, `inr`, `map`
- `(root)`: `add_comm`, `add_left_cancel`, `add_right_cancel`, `add_zero`, `and_false`, `and_self`, `and_true`, `by_cases`, `by_contra`, `decide_eq_false_iff_not`, `decide_eq_true_eq`, `false_and`, `ite_false`, `ite_true`, `le_of_eq`, `le_rfl`, `or_false`, `smul_eq_mul`, `sub_eq_zero`, `sub_self`, `zero_add`
## (d) Open issues and paper-delta candidates
- Paper-delta candidates (numbered by the dispatcher; text also in the module header): `T2195a`: the local lemma composes (F §3) and a merge that puts the fresh vertex into a class meeting at most one of its neighbours costs no less than leaving it alone (F §4.3), so the 17 terms reduce to 7 primitives (not in the paper, whose bookkeeping is per term, `B:213-262`); `T2195b`: the `GG` term `R2` (`Contract`): the 2-cycle collapse lowers the trivial-merge cost (`localReg6b_instCyc_repair_forced`: `0 ≤ -4 + 2` is false), so `B:272-273` has no per-step counterpart; the minimum over merges is restored by merging the two classes of the cycle (`scostLL_repair`), never two external ones; `T2195c` (on `T2184c`): c2 supplies the local lemma for `Loop` (`Oe1xOwx`, `R3`, `T1`), `Contract` (`R2`) and the factors `AddLoop` (`P5`, `P6`, `R5`), `Loop` (`R4`, `R6`), `MoveLoop` (`T2`, `T4`); `MoveSC`, `MoveOut`, `Dmove` (c3) close the remaining edge and `GG` terms.
- O1 (statement forms chosen, listed above by script): the pattern facts use the residual `X`; `scostLL_placement` carries the shape as a hypothesis `hA` (loop or two edges) and `hk : ∀ e₁ e₂, Aα = [e₁, e₂] → ¬ (s e₁.src e₁.dst ∧ s e₂.src e₂.dst)` (`k ≤ 1`); `scostLL_repair` expects `Γ.solid` as `⟨col, false, z, v⟩ :: ⟨col, false, u', z'⟩ :: L` up to `List.Perm`, with no hypothesis on `Γ` or `L`.
- O2 (c3 interface, informational): c3 can build `MoveSC`, `MoveOut`, `Dmove` from `scostLL_fresh_scost` (α alone), `scostLL_fresh_dropped` and `scostLL_placement` (α in a class, `k ≤ 1`), `scostLL_repair` (`k = 2`, collapse), `scostLL_local_diff(_C)`, `scostLL_clsPat_single_kept/dropped/loop`, `scostLL_sum_single/two/support` and the pattern facts E4/E6; these are public, the glue lemmas are `private`.
- No statement of a merged file or of a Pin was changed, no hypothesis was added to a Pin, no obstruction was found; nothing needs a dispatcher decision; no (a′) corrections were needed.
