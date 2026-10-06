Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 06:46:01 UTC 2026

### (i) Exponent table
No numeric exponents occur in the pins; the quantities that must close are (columns: quantity | value or constraint | numbers from the scripts below | slack).
| quantity | constraint | at the instances | slack |
|---|---|---|---|
| Hall crossing `cross(S) ≥ \|S\|` (`AnpKey5CrossPin`) | all `S ⊆ Fin q`, `M` with `perPath` | `figIVext` `S={α}`: 3 ≥ 1; resAux `S={α0,α1}`: 2 ≥ 2 | 2; 0 |
| inside bound (`AnpKey5InnerPin`) | `crossAt(v) ≤ 1 ∀v∈S ⇒ inside(S) ≥ \|S\|` | resAux `S={α0,α1}`: crossAt 1,1; inside 2 ≥ 2 | 0 |
| edges per vertex in a nested order | `\|rest\| ≥ 2q` | `figIVext` 4 ≥ 2; resAux 4 ≥ 4; `figAuxGh` 4 ≥ 4 | 2; 0; 0 |
| certificate depth `n` (`AnpSumCert n`) | `n ≤` #stuck components `≤ ⌊q/2⌋` (a stuck component has `≥ 2` vertices: loop-free and inside `≥ \|R'\|`) | `figAux^k`, all `9^k` one-edge-per-path `M`: max depth `k = q/2` (k=3: 8 of 729) | 0 (attained) |
| LW-12f exponent | `ordN − nngh = \|rest\| − 2q` (`\|M\| = nngh`, `nSolid − nngh = \|rest\|`) | `figIVext` 2 = 4−2; resAux 0 = 4−4; `figAuxGh` 0 = 4−4 | 0 (equality) |
| LW-12f constants | `c = 1/(1+Σ_j\|𝔓_j\|) ≤ 1/\|𝔓_j\|`, `c ≤ 1`; `C = Π_{ghost-free j} max(1,\|𝔓_j\|) ≥` #choice functions | `figAux` (no ghost, `\|𝔓_j\|=3`): `c = 1/7`, `C = 9`; `figIVext`: no ghost-free path, `C = 1` | `c`: `1/7 ≤ 1/3` |
| AM-GM weights | `½ + ½ = 1`, both branches keep `\|E\|` | `E.set k' (E.get k)`, `E.set k (E.get k')` have the same length | 0 |
| `figIVext` (case (IV)) | `q = 1 < p = 2` (paper's `q = p` fails); types at `α`: edge 0 B2, edge 1 B1, edge 4 B2; edge 2 `a_1 b_0` ends at an external vertex | `degS α = 3`, `nSolid = 4`, `ordN = 2`, `nngh = 0`; `NoA2`, `¬CaseI`, `¬CaseIII` (inst.py below) | — |
Per-`M` rows of `figIVext` (`M=∅`), `figAux` (all 9 one-edge-per-path `M`, resAux = `{0,5}`) and `figAuxGh` (`M=∅`): `rest`, greedy order, stuck set, components, non-bridge edges, AM-GM pair, depth are the rows of `tab.py` below (stuck only for `M={0,5}` and `{4,1}`, pair `(k,k') = (0,3)`, depth 1).

### (ii) Concrete nondegenerate instance and checks
Scripts are Python only (scratch `<scratchpad>/T2264/`; `lib.py` transcribes the check file's vocabulary literally, `certLit` is the literal `sumCertPin` with `List.set`). Instance: `figIVext` (`p=2,q=1`, `M=∅`: `IsNested`, `GhostOK`, `perPath`, order `[0]`); `figAux` with `M={0,5}` (`p=q=2`: `IsNested`, `perPath`, no order, certificate depth 1 with `(k,k')=(0,3)`, orders `[0,1]`, `[1,0]`); `AnpKey5GraphPin` hypotheses at `E = rest(figAux,{0,5})` (loop-free, cross, inner all True, `inst.py` last block). No external hypothesis occurs (no limit computation needed).
`$ bash run.sh` (runs `tab.py inst.py run1.py run2.py neg.py pinsafter.py run3.py`; output verbatim):
```
$ python3 tab.py
nested figIVext True ghostok True nSolid 4 ordN 2 nngh 0
figIVext M=∅                 perPath=True  rest=['α0b0', 'a1b0', 'b0α0', 'α0a0'] greedy=['α0'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
nested figAux True
figAux M={0,1}               perPath=True  rest=['α0α1', 'α0α1', 'α1b0', 'α1b1'] greedy=['α1', 'α0'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
figAux M={0,3}               perPath=True  rest=['a1α0', 'α0α1', 'α1b0', 'α1b1'] greedy=['α1', 'α0'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
figAux M={0,5} (resAux)      perPath=True  rest=['a1α0', 'α0α1', 'α0α1', 'α1b0'] greedy=[] stuck=['α0', 'α1'] comps=1 nonbridge(first comp)=['α0α1', 'α0α1'] amgm(k,k')=(0, 3) depth,literalOK=(1, True)
figAux M={2,1}               perPath=True  rest=['a0α0', 'α0α1', 'α1b0', 'α1b1'] greedy=['α1', 'α0'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
figAux M={2,3}               perPath=True  rest=['a0α0', 'a1α0', 'α1b0', 'α1b1'] greedy=['α0', 'α1'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
figAux M={2,5}               perPath=True  rest=['a0α0', 'a1α0', 'α0α1', 'α1b0'] greedy=['α0', 'α1'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
figAux M={4,1}               perPath=True  rest=['a0α0', 'α0α1', 'α0α1', 'α1b1'] greedy=[] stuck=['α0', 'α1'] comps=1 nonbridge(first comp)=['α0α1', 'α0α1'] amgm(k,k')=(0, 3) depth,literalOK=(1, True)
figAux M={4,3}               perPath=True  rest=['a0α0', 'a1α0', 'α0α1', 'α1b1'] greedy=['α0', 'α1'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
figAux M={4,5}               perPath=True  rest=['a0α0', 'a1α0', 'α0α1', 'α0α1'] greedy=['α0', 'α1'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
figAuxGh M=∅                 perPath=True  rest=['a0α0', 'a1α0', 'α0α1', 'α0α1'] greedy=['α0', 'α1'] stuck=[] comps=0 nonbridge(first comp)=[] amgm(k,k')=None depth,literalOK=(0, True)
resAux: no order among perms of [0,1]: True
$ python3 inst.py
figIVext: nested True GhostOK True p,q 2 1 nSolid 4 ordN 2 nngh 0 degS(α) 3
 pi = all-false: ((np.False_, np.False_),) NoA2 True CaseI False CaseIII False
 ending edges (path,last?,edge,internal endpoints,type): [(0, False, 0, [0], 'B2'), (0, True, 1, [0], 'B1'), (1, False, 2, [], 'ext (no internal end)'), (1, True, 4, [0], 'B2')]
 rest [(('m', 0), ('b', 0)), (('a', 1), ('b', 0)), (('b', 0), ('m', 0)), (('m', 0), ('a', 0))] perPath(∅) True order [0]: True
 CrossPin/InnerPin: True True | S={α}: cross 3 crossAt 3 inside 0
 perPath with edge 1 reserved: False (path 0 has ghost 0 and edge 1)
 paper pigeonhole: q = 1 < p = 2 ; edge 2 (a1 b0) joins two external vertices
figAux, M={0,5}: perPath True rest [(('a', 1), ('m', 0)), (('m', 0), ('m', 1)), (('m', 0), ('m', 1)), (('m', 1), ('b', 0))] nested True
 orders among permutations of [0,1]: []
 certificate depth 1 (AM-GM pair k=0,k'=3; orders [0,1] and [1,0]) literal check: True  ; depth 0 impossible: False
  branch1 E.set 3 E[0] = [(('a', 1), ('m', 0)), (('m', 0), ('m', 1)), (('m', 0), ('m', 1)), (('a', 1), ('m', 0))] | branch2 E.set 0 E[3] = [(('m', 1), ('b', 0)), (('m', 0), ('m', 1)), (('m', 0), ('m', 1)), (('m', 1), ('b', 0))]
GraphPin hypotheses at E=rest(figAux,{0,5}) (loop-free, q=2): True True True | S={α0,α1}: cross 2 inside 2 crossAt 1 1
 figIVext M=∅: |rest|=4 nSolid-nngh=4 2q=2 ordN-nngh=2 |rest|-2q=2
 figAux M={0,5}: |rest|=4 nSolid-nngh=4 2q=4 ordN-nngh=0 |rest|-2q=0
 figAuxGh M=∅: |rest|=4 nSolid-nngh=4 2q=4 ordN-nngh=0 |rest|-2q=0
$ python3 run1.py
tries 92926 nested graphs 590 q dist {0: 0, 1: 229, 2: 66, 3: 155, 4: 100, 5: 40, 6: 0} p dist {0: 0, 1: 0, 2: 58, 3: 256, 4: 196}
 with ghost not at an ending edge: 136 | path through an external vertex (non-ending): 499 | edge on no path: 246 | path revisiting a vertex: 306 | not GhostOK: 136
(g,M) pairs (perPath holds; generator skipped 0 ): 5310
CrossPin violations: 0 | InnerPin violations: 0 | (S nonempty with all crossAt<=1, so InnerPin non-vacuous): 82
certificate (strategy, literal sumCertPin check; order-0 cases cross-checked by all permutations) failures: 0 | depth histogram: {0: 10456, 1: 164} | max depth: 1
independent exhaustive search (min depth <= q), small cases compared: 2931 with no certificate: 0
time 3.6s
$ python3 run2.py
figAux^1 (p=q=2, nested): 9 one-edge-per-path M, all satisfy CrossPin, InnerPin, certificate found
figAux^2 (p=q=4, nested): 81 one-edge-per-path M, all satisfy CrossPin, InnerPin, certificate found
figAux^3 (p=q=6, nested): 729 one-edge-per-path M, all satisfy CrossPin, InnerPin, certificate found
 depth histogram {(k,depth):count}: {(1, 0): 7, (1, 1): 2, (2, 0): 49, (2, 1): 28, (2, 2): 4, (3, 0): 343, (3, 1): 294, (3, 2): 84, (3, 3): 8}
(b) random loop-free multigraphs, tries 15127, samples satisfying both hypotheses: 10000, by q {2: 1938, 3: 1704, 4: 2952, 5: 1255, 6: 2151}
   greedy completes (no stuck): 2872 | stuck set nonempty: 7128 | strategy depth histogram (pick 0): {0: 2872, 1: 4828, 2: 2204, 3: 96}
   strategy failures (3 deterministic picks + 1 random nonbridge choice): 0 | literal sumCertPin check failures: 0 | stuck-set-after-branch != R minus component: 0
   independent exhaustive search on 400 samples (|E|<=8, q<=3, first 400): no certificate found for 0
time 8.7s
$ python3 neg.py
negative control: random loop-free multigraphs 4000 | no certificate of depth<=q (exhaustive): 2666 | of those satisfying both hypotheses: 0
example E=[α0α1, α0a0, α1b0]: CrossPin True InnerPin False min depth None
$ python3 pinsafter.py
3000 graphs with nonempty stuck set; AM-GM branch lists (2 each) violating CrossPin: 731 | InnerPin: 0
$ python3 run3.py
table rows (figAux x 9 M, figAuxGh): 10 edge lists, max certificate depth 1, 320 (E,L,psi,xi,theta,a,b) cases, violations 0, max sum/(theta^q psi(0)^(|E|-2q)) = 1.0000
 depth>=1 among the 20 random lists: 7
20 random nested graphs (rest lists): 20 edge lists, max certificate depth 1, 560 (E,L,psi,xi,theta,a,b) cases, violations 0, max sum/(theta^q psi(0)^(|E|-2q)) = 0.6113
```
Reading of the output. `run1`: 590 nested graphs (q up to 5, paths through external vertices, edges on no path, ghosts anywhere, revisits, 136 not `GhostOK`), 5310 `(Γ,M)` with `perPath`: `CrossPin`, `InnerPin` (all `S`, brute force), certificate, 0 failures. `run2(b)`: 10^4 loop-free multigraphs (q ≤ 6) satisfying both `GraphPin` hypotheses, 7128 with a nonempty stuck set: 0 failures (3 deterministic and 1 random non-bridge choice per graph, literal check); `neg.py` shows the hypotheses are needed. `pinsafter.py`: the AM-GM branch list can violate `CrossPin` (731 of 6000), so the induction on stuck components must carry an invariant on subsets of the stuck set (`crossAt`/`inside` for `S ⊆ R∖R'` are unchanged by the branch), not the pins themselves. `run3` (`d=3`, `L∈{3,5}`, `ψ=1/(1+r)`, `exp(-r/2)`, tight and random `ξ`, `θ ∈ {1,1.7}·max row sum ξ²`): `AnpKey6SumPin` ratio ≤ 1.

Inspection (by the paper and `LWVocab.lean:296-399`, no script):
1. Stuck phase: a stuck vertex has `≤ 1` edge to joined/external labels, so `crossAt(R) ≤ 1` and `\|R\| ≤ cross(R) ≤ \|R\|` (equality, 1 leaving edge each). A component `R'` of `R` has its leaving edges outside `R`; `InnerPin` gives `inside(R') ≥ \|R'\|`, so the multigraph has a cycle or parallel pair and a non-bridge edge `α1α2`. In branch `E.set k' (E.get k)` `α1` has two copies of `k`, so it joins; a stuck `T ⊆ R'∖{α1}` would have `≤ 1` edge to `R'∖T`, which would make `α1α2` a bridge; other components and the earlier order are unchanged (`k'` was never counted for its outer end since `α2` was not joined). `run2` checks, for every non-bridge edge of the first stuck component: stuck set after each branch `= R∖R'`, 0 violations.
2. Crossing/inside proofs use only `IsNested` conjuncts 1 (no loops), 2–4 (walks, edge-disjoint, no repeated edge on a path) for `crossing ≥ 2` per visiting path, 6 (Hall) for `\|S\|` visiting paths, 5 for `Σ_P m_P ≥ 2\|S\|`; with `cross(S) ≤ Σ_v crossAt = \|S\|` each visiting path has exactly one remaining crossing and two crossings in all, so its run in `S` uses `≥ m_P − 1` remaining inside edges. `NoA2`, region, `¬AnpCaseI`, `¬AnpCaseIII`, `AnpIH`, `(eq:Psi)` and the ending-edge clause of `GhostOK` are not used (`perPath` needs only `≤ 1` ghost per path).
3. For the dispatcher: yes. For `GhostOK`, `IsNested` `Γ`, labels `lbl`: for each ghost-free path `j` `anpKey_long_edge` gives an edge `e_j` with `\|a_j−b_j\| ≤ \|𝔓_j\|·len(e_j)`, hence `ξ_{e_j} ≤ ψ(c\|a_j−b_j\|)` for `c ≤ 1/\|𝔓_j\|`. All terms are `≥ 0`, so `val ≤ Σ_{choice f} Π_j ψ(c r_j) Σ_ℓ Π_{e ∉ M_f} ξ_e` with `\|choices\| ≤ C`; `M_f` has one edge per ghost-free path (edge-disjoint paths), ghost paths have one ghost, so `perPath` holds, `\|rest\| = nSolid − nngh`; `anpKey5_cert` and the sums along the certificate (`Σ_x ξ(y1,x)ξ(y2,x) ≤ θ` by Cauchy–Schwarz, other edges `≤ ψ(0)`, AM-GM `½(B+B') ≤ B`) give `θ^q ψ(0)^{\|rest\|−2q}` and `\|rest\|−2q = ordN − nngh`. `C, c` as in Consumers. Only `perPath` of `GhostOK` is used; no case (I)–(III) hypothesis, no induction hypothesis.
4. §29: (1) no time variable; (2) no `1 − ilambda²/L²`; (3) no `L^d ≤ W^K`; (4) no `∀ᶠ n`; (5) no `(a,b)` in `anpKey5_*` (statements on edge lists); (6) no parameter lower bound; (7) no scale.

### Verdicts
- `anpKey5_cross_ge` (`AnpKey5CrossPin`): PASS. `anpKey5_inside_ge` (`AnpKey5InnerPin`): PASS. `anpKey5_graph` (`AnpKey5GraphPin`): PASS (no counterexample; note the invariant remark above). `anpKey5_cert` (`AnpKey5CertPin`): PASS (instances (1)–(4) of the ticket are realised by the Python rows above).

### (a′) Preflight corrections — Tue Oct  6 07:26:26 UTC 2026
(a) Inspection 2 lists IsNested conjunct 1 (no loops) among the facts of the crossing/inside proofs.  They use conjuncts 2-6 only; conjunct 1 is used once, for the loop-free premise of `anpKey5_graph` inside `anpKey5_cert`.  No verdict of (a) changes.
```
$ grep -n "hN\.[12]" RBM3D/Graph/AnpKey5.lean | cut -c1-96   # hN.1 = conjunct 1, hN.2.1 = 2, hN.2.2.1 = 3, hN.2.2.2.1 = 4, hN.2.2.2.2.1 = 5, hN.2.2.2.2.2 = 6
1092:  have hchain := (anpKey2_walkOK_iff Γ j).1 (hN.2.1 j)
1093:  have hnd := hN.2.2.1 j
1121:  have hchain := (anpKey2_walkOK_iff Γ j).1 (hN.2.1 j)
1122:  have hnd := hN.2.2.1 j
1153:  have key := anpKey5_path_sum (Γ.path j) (hN.2.2.1 j) (fun k => (Γ.es.get k).ghost || deci
1168:  exact hN.2.2.2.1 i j hij st hst st' hst' h.symm
1255:  have hHall := hN.2.2.2.2.2 S
1274:  have hHall := hN.2.2.2.2.2 S
1301:      obtain ⟨i, i', hii, hi, hi'⟩ := hN.2.2.2.2.1 α
1341:    exact hN.1 _ (List.get_mem _ k)
```

## (b) Script output — Tue Oct  6 07:26:59 UTC 2026
Branch `t/T2264`, commit `c21b6c0`; `RBM3D/Graph/AnpKey5.lean` (new, 1427 lines), `RBM3D/Test/Axioms.lean` (+1 registry line).  Scratch: `<scratchpad>/T2264/` (`lean/*.lean`, `extract.py`).
```
$ lake build RBM3D.Graph.AnpKey5 2>&1 | tail -1
Build completed successfully (3349 jobs).
$ lake env lean RBM3D/Graph/AnpKey5.lean 2>&1 | wc -l   # all messages of this file
       0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/AnpKey5.lean | wc -l
       0
$ lake env lean ax.lean   # #print axioms
'RBM.Graph.anpKey5_cert' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_cross_ge' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inside_ge' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_graph' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_figIVext' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_resAux' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_figAuxGh' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_figIVext_cert' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_cross_inside' : [propext, Classical.choice, Quot.sound]
$ python3 extract.py <targets and instances>   # statements as in the file
-- anpKey5_cert (AnpKey5.lean:1327)
theorem anpKey5_cert : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∃ n : ℕ, AnpSumCert n (anpKey5_rest Γ M)
-- anpKey5_cross_ge (AnpKey5.lean:1250)
theorem anpKey5_cross_ge : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∀ S : Finset (Fin q), S.card ≤ anpKey5_cross (anpKey5_rest Γ M) S
-- anpKey5_inside_ge (AnpKey5.lean:1268)
theorem anpKey5_inside_ge : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∀ S : Finset (Fin q),
      (∀ v ∈ S, anpKey5_crossAt (anpKey5_rest Γ M) S v ≤ 1) →
        S.card ≤ anpKey5_inside (anpKey5_rest Γ M) S
-- anpKey5_graph (AnpKey5.lean:931)
theorem anpKey5_graph : ∀ (p q : ℕ) (E : List (NV p q × NV p q)), (∀ e ∈ E, e.1 ≠ e.2) →
    (∀ S : Finset (Fin q), S.card ≤ anpKey5_cross E S) →
    (∀ S : Finset (Fin q), (∀ v ∈ S, anpKey5_crossAt E S v ≤ 1) → S.card ≤ anpKey5_inside E S) →
    ∃ n : ℕ, AnpSumCert n E
-- anpKey5_inst_figIVext (AnpKey5.lean:1367)
theorem anpKey5_inst_figIVext :
    anpKey5_figIVext.GhostOK ∧ anpKey5_figIVext.IsNested ∧ anpKey5_figIVext.NoA2 anpKey5_piIV ∧
      ¬ AnpCaseI anpKey5_figIVext anpKey5_piIV ∧ ¬ AnpCaseIII anpKey5_figIVext anpKey5_piIV ∧
      anpKey5_figIVext.degS 0 = 3 ∧ anpKey5_figIVext.ordN = 2 ∧ anpKey5_figIVext.nngh = 0 ∧
      AnpSumOrder (anpKey5_rest anpKey5_figIVext ∅) [0]
-- anpKey5_inst_resAux (AnpKey5.lean:1384)
theorem anpKey5_inst_resAux :
    anpKey5_perPath figAux anpKey5_resAux ∧
      (∀ σ ∈ (List.finRange 2).permutations, ¬ AnpSumOrder (anpKey5_rest figAux anpKey5_resAux) σ) ∧
      AnpSumCert 1 (anpKey5_rest figAux anpKey5_resAux)
-- anpKey5_inst_figAuxGh (AnpKey5.lean:1395)
theorem anpKey5_inst_figAuxGh :
    anpKey5_perPath anpKey2_figAuxGh ∅ ∧ ∃ n : ℕ, AnpSumCert n (anpKey5_rest anpKey2_figAuxGh ∅)
-- anpKey5_inst_figIVext_cert (AnpKey5.lean:1402)
theorem anpKey5_inst_figIVext_cert :
    anpKey5_perPath anpKey5_figIVext ∅ ∧ (∃ n : ℕ, AnpSumCert n (anpKey5_rest anpKey5_figIVext ∅)) ∧
      ¬ anpKey5_perPath anpKey5_figIVext
        (Finset.univ.filter fun k : Fin anpKey5_figIVext.es.length => k.1 = 1)
-- anpKey5_inst_cross_inside (AnpKey5.lean:1412)
theorem anpKey5_inst_cross_inside :
    (Finset.univ : Finset (Fin 2)).card ≤ anpKey5_cross (anpKey5_rest figAux anpKey5_resAux) Finset.univ ∧
      (Finset.univ : Finset (Fin 2)).card ≤ anpKey5_inside (anpKey5_rest figAux anpKey5_resAux) Finset.univ ∧
      ∃ n : ℕ, AnpSumCert n (anpKey5_rest figAux anpKey5_resAux)
$ sed -n 1388,1393p RBM3D/Graph/AnpKey5.lean   # instance (2): the explicit AM-GM pair `0`, `3` and the orders `[0,1]`, `[1,0]`
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro σ hσ
    rcases anpKey5_perm_two σ hσ with rfl | rfl <;> decide +kernel
  refine Or.inr ⟨⟨0, by decide +kernel⟩, ⟨3, by decide +kernel⟩, by decide +kernel, ⟨[0, 1], ?_⟩, ⟨[1, 0], ?_⟩⟩
  all_goals decide +kernel
$ lake env lean lean/conf.lean; echo exit=$?   # section 2 of docs/tickets/checks/T2264-check.lean verbatim in `RBM.Graph.T2264Check`, then examples
exit=0
161:theorem sumCert_iff {p q : ℕ} : ∀ (n : ℕ) (E : List (NV p q × NV p q)), sumCertPin n E ↔ AnpSumCert n E := by
174:example : AnpKey5CertPin := fun p q Γ M hN hM =>
176:example : AnpKey5CrossPin := @anpKey5_cross_ge
177:example : AnpKey5InnerPin := @anpKey5_inside_ge
178:example : AnpKey5GraphPin := fun p q E h1 h2 h3 =>
  # 11 further examples `@pin = @file_def := rfl` (8 vocabulary names inS cross crossAt inside early sumOrder rest perPath, and `figIVext`, `piIV`, `resAux`);
  # `sumCertPin = AnpSumCert` is NOT `rfl` (two separate structural recursions), hence `sumCert_iff` (induction) for the two pins that mention it; the other two pins are `@theorem`
$ lake build RBM3D.Test.Axioms; lake env lean lean/reg.lean; echo exit=$?   # reg.lean = import RBM3D; import RBM3D.Graph.AnpKey5; import RBM3D.Test.Axioms; #assert_rbm_axioms
exit=0   axiom audit: 7806 theorems, 2599 definitions, 0 axioms in `RBM` (compiler-generated declarations exc ...   grep -c "anpKey5|anpKey2_stepOK" of its output: 0
$ git diff main...t/T2264 -- RBM3D/Test/Axioms.lean | grep '^[+]' | cut -c1-175
+   `RBM.Graph.anpKey5_perPath, -- every path of a nested graph has at most one edge that is a ghost or in the reserved set `M` (the long edges of LW-12f's ...
$ git diff --stat main...t/T2264
 RBM3D/Graph/AnpKey5.lean | 1427 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    1 +
 2 files changed, 1428 insertions(+)
$ name-clash grep of `anpKey5_|AnpSumOrder|AnpSumCert` in RBM3D/ (worktree, except AnpKey5.lean), RBM3D/ and docs/tickets/T2262..T2267(.md, checks) of the main worktree
RBM3D/Test/Axioms.lean:309:   `RBM.Graph.anpKey5_perPath, -- every path of a nested graph 
docs/tickets/T2264.md
docs/tickets/checks/T2264-check.lean
$ public declarations of AnpKey5.lean as line:name (prefix anpKey5_ omitted; 112 declarations, no `private`; targets: cert, cross_ge, inside_ge, graph)
62:inS 66:cross 70:crossAt 74:inside 78:early 86:AnpSumOrder 95:AnpSumCert 102:rest 107:perPath 110:decSumOrder 114:decPerPath 124:ite_pos 127:ite_neg 130:countP_eq_sum 144:countP_eq_card 148:two_le_countP
158:one_le_countP 163:countP_le_sum 179:countP_set 185:rest_countP 228:inS_inl 230:inS_inr 233:inS_mono 240:inS_true 247:comp 249:mem_comp 254:valid 259:sumOrder_of_valid 262:valid_nil 265:early_comp
271:valid_append 301:comp_append_card 315:greedy 341:valid_edge 361:valid_set 379:inS_sdiff 383:inS_inter 388:cut 392:countP_le_add3 404:pw_split 410:pw_cutmono 417:forest 472:nb 503:pend 506:crossAt_eq
509:pend_inS 516:pend_mono 530:pend_unique 540:pend_not_cut 556:pend_conflict 567:get_set_ne 572:get_set_self 577:ok 580:untouched_pend 591:cross_pred_false 596:inside_pred_false 602:ok_set 616:cross_le_sum
634:branch 744:cert_mono 754:cert_mono_le 760:countP_le_add2 771:pw_cuttrans 778:cut_trans 787:inS_empty 790:cut_self 796:pw_closed 803:crossAt_closed 820:pend_untouched 835:main 931:graph 947:step_cross
956:walk_one 974:walk_two 998:path_sum 1016:eidx 1020:gd 1024:rm 1028:cr 1032:ins 1035:gd_add_rm 1050:cr_add_ins_le 1055:cr_two_ins 1061:ite_and 1065:rest_cross 1073:rest_inside 1081:sum_eq_inS 1089:pl1 1103:or_le
1110:pl2 1150:pl3 1161:paths_disjoint 1170:sum_paths_le 1177:gdcr 1187:gdins 1197:rm_cr_ins 1206:mj 1210:pa 1225:path_bound 1250:cross_ge 1268:inside_ge 1327:cert 1347:decIsNested 1354:figIVext 1361:piIV
1364:resAux 1367:inst_figIVext 1375:perm_two 1384:inst_resAux 1395:inst_figAuxGh 1402:inst_figIVext_cert 1412:inst_cross_inside
$ git -C ../RBM2D|../RBM1D: not used (RBM1D and RBM2D have no light-weight graph layer; no port, no diff-stat)
$ lake build 2>&1 | tail -1   # whole library, exit 0, 07:25:28 UTC; the root imports of `RBM3D.lean` are added by the hub at merge
Build completed successfully (4070 jobs).
```

Narrative.
1. Scope: one new file (1427 lines, below the 1500 of the ticket, so no split to e′); imports `RBM3D.Graph.AnpKey3` and Mathlib only; the vocabulary is section 2 of the check file verbatim up to the names (script above); the four theorems state the pins with no added hypothesis; `AnpDetGhCaseIV` and every merged declaration are untouched.  Registered: `RBM.Graph.anpKey5_perPath` in `structuralProps` (a defining predicate of the pair `(Γ, M)`); nothing deleted, nothing owed.
2. `anpKey5_cross_ge`, `anpKey5_inside_ge` (section 6).  For a path `j`, `anpKey5_eidx` is its (nodup) edge-index set; `cr`, `ins`, `gd`, `rm` are the 0/1 indicators of "one end in S", "both ends in S", "kept in rest", "ghost or in M".  The walk lemmas `anpKey5_walk_one/two` (on `anpKey2_chain`) give: a path visiting S has `Σ cr ≥ 2` (`anpKey5_pl1`); a path visiting `α ∈ S` has `≥ 2` edges at `α`, so `2 m_j ≤ Σ (cr + 2 ins)` (`anpKey5_pl2`); `perPath` gives `Σ rm ≤ 1` (`anpKey5_pl3`); edge-disjointness (conjunct 4) gives `Σ_{j∈P} Σ_{E_j} h ≤ Σ_k h`.  Hall (conjunct 6) gives `cross_ge`.  For `inside_ge`: `cross ≤ Σ_v crossAt ≤ |S|` forces `|P| = |S|` and exactly one kept crossing edge per visiting path, hence two crossings of which one is removed and no removed inside edge; the degree count `2 inside_j + cross_j ≥ 2 m_j` (no explicit contiguous runs) and `Σ_j m_j ≥ 2|S|` (conjunct 5) give `inside ≥ |S|`.
3. `anpKey5_graph` (sections 3-5).  `anpKey5_valid` is a valid prefix of an order, `anpKey5_greedy` extends it until stuck, `anpKey5_main` is the induction on the number of unlisted vertices.  Its invariant is `anpKey5_ok` (both bounds) on every SUBSET of the unlisted set, not on the list itself: (a)'s `pinsafter.py` found that the AM-GM list can violate the crossing bound.  In the stuck set `R` a minimal nonempty closed `U` (no edge between `U` and `R \ U`) has a pendant edge at every vertex (crossing bound at `U`) and `inside(U) ≥ |U|`.  The non-bridge pair does not use Mathlib's `isAcyclic_iff_forall_adj_isBridge` (suggested in the ticket) but an elementary Forest lemma on cuts: `anpKey5_forest` (if every inside edge of `U` is separated by a cut with one edge, every nonempty `U' ⊆ U` has `inside + 1 ≤ |U'|`) and `anpKey5_nb` (a pair `x ≠ y` in `U` such that every `T ⊆ U` separating them has `≥ 2` edges to `U \ T`).  `anpKey5_branch`, applied to `(x,y,k,k')` and `(y,x,k',k)`, shows that after `E.set k' (E.get k)` the prefix `σ' ++ [x]` is valid and its greedy extension lists all of `U` (a stuck part `T` of `U` would have `≤ 1` edge to `U \ T`, against minimality (`≥ 1`) or the cut bound (`≥ 2`)), and that the rest keeps `anpKey5_ok` (the replaced edges touch no remaining vertex); depth `max + 1`.
4. Instances: ticket (1)-(4) as stated, plus `anpKey5_inst_cross_inside` for the three intermediate theorems (at `figAux` minus `anpKey5_resAux`, `p = q = 2`: both bounds for all four subsets and loop-freeness by `decide +kernel`).  `(List.finRange 2).permutations` is not evaluated by `decide +kernel` (well-founded `permutationsAux`), so instance (2) first reduces to `[0,1]`, `[1,0]` by `anpKey5_perm_two` (`List.mem_permutations`, `List.length_eq_two`).  Added instances: `anpKey5_decSumOrder`, `anpKey5_decPerPath`, and a general `anpKey5_decIsNested` (`Decidable Γ.IsNested`).

## (c) Verified Mathlib / core names: `#check @name` of the 52 names below gave 0 errors (`lean/names.lean`); the 3 names marked absent gave `unknown constant`
- `List.countP_filterMap`, `List.countP_set` (`h : i < l.length`), `List.countP_eq_length_filter`, `List.countP_cons`: `anpKey5_rest_countP`, `anpKey5_countP_set`, `anpKey5_pl3`
- `List.countP_pos_iff`, `List.countP_eq_zero`, `List.countP_congr`, `List.countP_mono_left`: existence of edges, closedness, monotone counts
- `Finset.card_filter`, `Fin.sum_univ_succ`, `Fin.sum_univ_def`: `anpKey5_countP_eq_sum`, `anpKey5_rest_countP`
- `Finset.sum_biUnion`, `Finset.sum_le_sum_of_subset`: `anpKey5_sum_paths_le` (disjoint paths)
- `Finset.sum_eq_sum_iff_of_le`, `Finset.sum_lt_sum`, `Finset.single_le_sum`, `Finset.sum_comm`, `Finset.sum_ite_eq`, `Finset.sum_pair`, `Finset.sum_insert`, `Finset.sum_add_distrib`, `Finset.mul_sum`: counting
- `Finset.exists_min_image`, `Finset.sdiff_ssubset`, `Finset.card_sdiff_add_card_eq_card`, `Finset.card_lt_card`, `Finset.card_le_card`, `Finset.card_pair`: minimal closed set, Forest lemma
- `List.toFinset_cons`, `List.mem_toFinset`, `List.nodup_append`, `List.mem_filterMap`, `List.mem_iff_get`, `List.get_mem`, `List.getElem_mem`, `List.mem_of_mem_take`: lists
- `List.getElem_set_ne`, `List.mem_or_eq_of_mem_set`, `List.take_left`, `List.take_append_of_le_length`: `E.set`, `σ ++ [v]`
- `Finset.disjoint_left`, `Finset.inter_subset_right`, `Finset.nonempty_iff_ne_empty`, `Finset.sdiff_subset`, `Finset.ssubset_iff_subset_ne`, `Finset.sum_const`: sets
- `List.mem_permutations`, `List.length_eq_two`, `Fin.cast_injective`, `Nat.strong_induction_on`, `Nat.le_induction`, `Option.some.inj`
- absent: `Finset.card_le_card_of_forall_subsingleton`, `List.get_set`, `List.sum_finRange` (not used; `Fin.sum_univ_def` and `List.getElem_set_*` instead).  In this toolchain `if_pos`/`if_neg`/`if_true`/`push_neg` are deprecated (warnings); the file avoids them (0 messages above).
- not used: `SimpleGraph.isAcyclic_iff_forall_adj_isBridge`, `SimpleGraph.IsTree.card_edgeFinset` (ticket's optional route; replaced by `anpKey5_forest`).

## (d) Open issues and paper-delta candidates
- T2264a: `7_8:1388-1393` (pigeonhole: `q = p`, one A1/B1 edge per vertex, every path with a B2 edge) fails for nested graphs whose paths pass through external vertices: `anpKey5_figIVext` is `GhostOK`, `IsNested`, `NoA2`, not case (I), not case (III) (`anpKey5_inst_figIVext`), with `q = 1 < p = 2` and an ending edge between two external vertices.  Replaced by the crossing bound `anpKey5_cross_ge` (Hall).
- T2264b: `(eq:degali)` (`7_8:1403-1406`, `deg_s ≥ 3`) is replaced by `anpKey5_inside_ge` (`inside(S) ≥ |S|` for every set whose vertices have one leaving edge); `deg_s` is not used.
- T2264c: the re-rooting (i)-(iii) (`7_8:1440-1449`) is replaced by one AM-GM split at a pair `x ≠ y` of a minimal closed set separated by no single-edge cut (`anpKey5_nb`, `anpKey5_branch`).  Case (iii) needs a spanning tree rooted at `α₁` in which `α₂` is not a child of `α₁`; for a bridge `α₁ α₂` there is none (the ticket's remark, mathematics not compiled here); what the Lean proof needs is the hypothesis `hsep` of `anpKey5_branch` (`≥ 2` edges across every cut separating `x` from `y`), which holds for the pair of `anpKey5_nb`.
- T2264d: the order exists for every nested graph with one edge removed per path (`perPath`): no region, no `NoA2`, no case (I)-(III), no induction hypothesis, no ending-edge clause of `GhostOK` (`anpKey5_cert` uses `IsNested` and `perPath` only).
- Not here (LW-12f): `AnpKey6SumPin`, the union bound, `AnpDetGh`, `anpDetGhStep_holds`, registry deletions.  No external hypothesis occurs in the targets, so no limit check is owed.
- Observation: `sumCertPin = AnpSumCert` is not `rfl` (two structural recursions); `sumCert_iff` (in the script, not in the file) bridges them; the ticket's "each vocabulary shown `rfl`" holds for the 11 non-recursive names.
