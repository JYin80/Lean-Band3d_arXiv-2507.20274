Auditor model: claude-opus-5-5

# T2050 audit (round 1): LW-03 graph vocabulary, `RBM3D/Graph/LWVocab.lean`
Time: Sat Oct  3 14:00:52 UTC 2026 (`date -u`). Branch `t/T2050` at `8f2b0ee`; audit worktree `RBM3D-wt/T2050-audit1` (detached).
Scratch: `scratchpad/T2050/` (`ax.lean`, `precheck.lean`, `extra.lean`); no source edited.

## 1. Build, scope, hygiene
```
$ lake build RBM3D.Graph.LWVocab 2>&1 | grep -E "error|warning|Build completed"
Build completed successfully (2062 jobs).
$ git diff --name-only main...t/T2050
RBM3D/Graph/LWVocab.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2050 --stat -- RBM3D/Graph/Model.lean RBM3D/Graph/ScalingOrder.lean RBM3D/Graph/Expansions.lean | wc -l
       0
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom |\baxiom\b" RBM3D/Graph/LWVocab.lean
0
$ grep -n "^import" RBM3D/Graph/LWVocab.lean      # never `import RBM3D`
6:import RBM3D.Graph.ScalingOrder   (7-13: seven Mathlib modules)
$ git diff main...t/T2050 -- RBM3D/Test/Axioms.lean | grep "^[+-] "    (registry lines only)
-   `RBM.Gauss.Sizes.STFlow] -- ...
+   `RBM.Gauss.Sizes.STFlow, -- ...
+   `RBM.Graph.LGraph.DotWF, -- at most one dotted edge per pair of vertices, none a loop (`def_graph1`, `7_8:141`; T2050)
+   `RBM.Graph.LGraph.Consistent] -- a term `Dot · Γ` ... (`dot-def`, `7_8:221`; T2050)
$ git diff --stat 56c30fb main -- RBM3D/Test/Axioms.lean | wc -l    # merge-base 56c30fb; main did not touch the registry since
       0
```

## 2. Axioms (every public declaration of the file) and the registry pre-check
```
$ lake env lean ax.lean > ax.out   # import RBM3D.Graph.LWVocab; 153 `#print axioms`, one per public theorem/def/structure
exit 0
$ grep -o "depends on axioms: .*\|does not depend on any axioms" ax.out | sort | uniq -c
 126 depends on axioms: [propext, Classical.choice, Quot.sound]
   2 depends on axioms: [propext]              # figAux, figAux_ord (copied probe)
  25 does not depend on any axioms
$ lake build RBM3D && lake env lean precheck.lean   # import RBM3D; import RBM3D.Graph.LWVocab; #assert_rbm_axioms
Build completed successfully (3746 jobs).
axiom audit: 1655 theorems, 801 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
premises found by scanning: 52 (borrowed 2, owed 36, structural 14).
registry: 5 borrowed + 43 owed + 25 structural; ...
exit 0
```
Importing `RBM3D` and the new module together compiles: no public-name clash.

## 3. Target 1: verbatim copy of the probe (DECISIONS §24, representation A)
```
$ git show eeda441:RBM3D/Probe/T2040Graphs.lean > probe.lean
$ diff <(sed -n 54,281p probe.lean) <(sed -n 65,292p LWVocab.lean) && echo "sec1 identical"
sec1 identical
$ diff <(sed -n 331,432p probe.lean) <(sed -n 294,395p LWVocab.lean) && echo "sec3 identical"
sec3 identical
```
Section 2 (candidate B) not copied: `grep -c GTerm LWVocab.lean` → `0`. **PASS.**

## 4. Target 2: the vocabulary of `7_8_light_weight.tex:116-287`, statement by statement
Read against the paper TeX (`7_8:116-287`) and the merged `ord` (`ScalingOrder.lean:65`: `ord c = nS + 2(nW - nV)`).
| paper | Lean | check |
|---|---|---|
| `def_graph1` 116-147 | `SEdge{σ,circ}` (G, Ḡ, G−M, conj(G−M); loops = weights/light-weights), `WEdge{col,σ}` (S, S⁺, S⁻ = `star (Sp y x)` = `((S⁺)^*)_{xy}`, `7_8:110`), `DEdge{eq}` (`1_{x=y}`, `1_{x≠y}`), `coeff : ℂ`; `IsWeight`, `IsLightWeight`, `charge`, `IntEnds`, `DotWF` | matches; polynomial coefficient → ℂ (T2050a) |
| `ValG` 159-164 | `LGraph.val = ∑ ℓi, coeff·∏ factors`; `LComb.val` over `List (PGraph E)` | matches; `PGraph.val = 0` when merged externals disagree (T2050b(2)) |
| `def_poly` 171-188 | `mol` (closure under waved + `=`-dotted), `mem_mol_iff` (= `molGraph.Reachable`), `Mol`, `IsExtMol`, `InsideMol`, `molSolid`; `nM_eq_card` | matches; ×-dotted do not connect (T2050d) |
| `defnlvl0` 196-210 | `Normal` = (ii) no `=`-dotted ∧ (iii) `∀ u ≠ v, XBetween ↔ SBetween` (non-loop solid) ∧ (iv) loops have `circ` | matches; (i) O(1) → consumer bound (T2050e); "G-edge"/"solid edge", loops (T2050c) |
| `dot-def` 214-225 | `aPairs`/`bEdges`/`dotChoices`/`withDots`, `Consistent`, `merge` (EqvGen classes; ext class if it has an ext vertex), `splitWeights` (`G_xx = (G−M)_xx + m`, red `star m`), `partition : List (PGraph E)` | `val_eq_partition` (hyp. only `∀ x, D.M x x = m`), `partition_normal` (no extra hyp.), `partition_of_normal` (hyp. `Normal`, `DotWF`) |
| `def scaling` 232-255 | `Counters.scalingSize = (L^d)^nM Ψ^nS W^{-d(nW−nV)}` (zpow); `LGraph.scalingSize`; `scalingSizeG = max` over partition (0 if empty) | matches `(eq_defsize)`; empty max (T2050b(5)); typing (T2050f) |
| `def scaling order` 270-284 | `scalingOrder = ord counters`; `scalingOrderG = min` (`WithTop ℤ`, ⊤ if empty); `scalingSize_eq` (274-275, hyp. `Ψ ≠ 0`), `scalingSize_le` (276-277, hyps `0<Ψ`, `1 ≤ W^dΨ²`, `nV ≤ nW`); `one_le_pow_mul_sq_iff` (`W^{-d/2} ≤ Ψ ↔ 1 ≤ W^dΨ²`) | identity and bound have exactly the paper's hypotheses |
No hypothesis sits in a structure field: `LGraph`, `SEdge`, `WEdge`, `DEdge`, `LData` are data only; `PGraph` carries `ext_surj : Surjective ext`, a property of its data used to make `PGraph.val` well defined, discharged by `extMap_surj` and `Function.surjective_id` (`pack`). No cycle: the file imports only `Graph.ScalingOrder` (merged) and Mathlib. The two registered hypotheses `DotWF`, `Consistent` are data conditions (structural, DECISIONS §20); both are satisfiable (`p2Graph.DotWF ∧ figGraph.DotWF ∧ lwNwGraph.DotWF` by `decide`, `¬ audInc.Consistent` below). **PASS.**

## 5. Target 3: basic lemmas (signatures from the file, instance arguments elided)
```
theorem LGraph.val_of_isEmpty [IsEmpty I] (Γ) (D) (ℓe) (ℓi) : Γ.val D ℓe = Γ.term D (Sum.elim ℓe ℓi)
theorem LGraph.val_relabel_equiv (Γ) (eE : E ≃ E') (eI : I ≃ I') (D) (ℓe') :
    (Γ.relabel (Equiv.sumCongr eE eI)).val D ℓe' = Γ.val D (ℓe' ∘ eE)
theorem LGraph.val_map_equiv (Γ) (σ : ι ≃ ι') (D) (ℓe) : Γ.val (D.map σ) (σ ∘ ℓe) = Γ.val D ℓe
theorem LGraph.val_disjUnion ... : (Γ₁.disjUnion Γ₂).val D (Sum.elim ℓ₁ ℓ₂) = Γ₁.val D ℓ₁ * Γ₂.val D ℓ₂
theorem LGraph.{nS,nW,nV,nM}_disjUnion : (Γ₁.disjUnion Γ₂).nX = Γ₁.nX + Γ₂.nX
theorem LGraph.ord_disjUnion : ord (Γ₁.disjUnion Γ₂).counters = ord Γ₁.counters + ord Γ₂.counters
theorem LGraph.counters_relabel_equiv (φ : E ⊕ I ≃ E' ⊕ I') (hφ : ∀ v, (φ v).isRight = v.isRight) : nS, nW, nV, nM equal
example : ord p2Graph.counters = 2 := by decide        -- LWVocab.lean:2404
example : ord figGraph.counters = 4 := by decide       -- LWVocab.lean:2405
```
All hypothesis-free except the honest `hφ` (an equivalence must preserve the internal/external split). **PASS.**

## 6. Compiled nonempty instances (section 15, `LWVocab.lean:2331-2557`; 44 `example`s, all compiled by the build of §1)
Data `lwD : LData (Fin 3)`: `G = [[1,2,3],[4,5,6],[7,8,10]]`, `M = diag(1/2)`, `S` real symmetric with all entries nonzero, `Sp = 1`; hypotheses `lwD_S_real`, `lwD_M_diag` proved.
- Probe examples: `p2Graph.val lwD ![0,1] = 67081 = 259²` (via `p2Graph_val_eq`, hyp. discharged), `figGraph_val lwD 0 1`, counters, `ord` 2 and 4 by `decide`, both `Normal` by `decide`.
- Ticket's "normal graph with a dotted edge": `lwNwGraph` (ext `x`, int `a,b`; `G_{xa}`, `Ḡ_{xa}`, `(G−M)_{bb}`, `S_{ab}`, ×-dotted `1_{a≠x}`): `Normal`, counters (3,1,2,1), `ord = 1`, `scalingOrderG = 1`, `scalingSizeG = 27` at `Ψ,W,d,L = 1/2,2,3,3`. A `=`-dotted edge is excluded from normal graphs by `defnlvl0 (ii)`, so the ×-dotted reading is the only satisfiable one; `=`-dotted edges are instanced in `lwEqGraph` (merge, `mergeP_val`, `mergeSplitP_val`, value 1).
- Partition: `LComb.val (lwSumGG.partition (1/2)) lwD ![0] = 14` (value of `∑_a G_{0a}Ḡ_{0a}` = 1+4+9; nonzero, so the partition is nonempty), `partition_normal`, `dotChoices = [(1,[=]),(1,[≠])]` by `decide`.
- Scaling: `scalingSize_eq` at `p2Graph`, `scalingSize_le` at `lwSwGraph` (`nW = nV = 1`, `1 ≤ 2³·(1/2)²` discharged), sizes 729 and 729/4.
- Target 3: `val_of_isEmpty_prod` (proved from `val_of_isEmpty`), `val_relabel_equiv`, `val_map_equiv`, `val_disjUnion` (= 67081·2), `n*_disjUnion`, `ord_disjUnion` (= 3), `counters_relabel_equiv`.
Public lemmas with no §15 use (script): `term_relabel`, `PGraph.val_of_factor`, `val_of_not`, `extMap_surj`, `term_eq_sum_dotChoices`, `term_eq_zero_of_not_consistent`, `val_eq_zero_of_not_consistent`, `val_of_isEmpty` (plus hypothesis-free probe theorems). None is a ticket target; the only one with a nontrivial premise is checked here:
```
$ lake env lean extra.lean; echo exit $?      # auditor scratch, not part of the branch
-- audInc: solid G_{xa}, dotted [1_{a=x}, 1_{a≠x}];  audInc_not : ¬ audInc.Consistent (EqvGen.rel)
-- example : audInc.val lwD ![0] = 0 := audInc.val_eq_zero_of_not_consistent lwD audInc_not ![0]
-- example : lwEdgeGraph.val lwD ![0,1] = lwEdgeGraph.term lwD (Sum.elim ![0,1] finZeroElim) := lwEdgeGraph.val_of_isEmpty ...
exit 0
```
No `N = 0`, empty index, `False` premise or huge witness. **PASS.**

## 7. Paper-delta coverage (prove report (d))
| Lean/paper difference | candidate |
|---|---|
| coefficient polynomial in `m, m̄, …` kept as `ℂ`; `M = mI` as `∀ x, D.M x x = m` | T2050a |
| merged ext/int classes, label agreement (`PGraph.val = 0`), per-term vertex types, DotWF not enforced, empty max/min (`0`, `⊤`) | T2050b |
| `defnlvl0 (iii)` "solid edge" vs `dot-def` "G-edge"; loops excluded from (iii) | T2050c |
| only `=`-dotted edges connect molecules | T2050d |
| `defnlvl0 (i)` O(1) not a record property | T2050e |
| `Ψ : ℝ`, `W d L : ℕ`, zpow; `Ψ ≥ W^{-d/2}` as `1 ≤ W^dΨ²` | T2050f |
| odd `L`, `f` resolvent polynomial, `∂_{h_{αx}}` | T2040c, d, i cited (DECISIONS §24) |
Every difference found in §4 is covered. **PASS.**

## 8. Observations (no RETURN)
1. `merge` maps the ×-dotted edges by `vmap` without deduplication (`LWVocab.lean:781`). With solid edges `α–β`, `α–γ`, `β–γ` and the choice `1_{α≠β}·1_{α≠γ}·1_{β=γ}` (consistent), the merged term has two ×-dotted edges between `α` and `[βγ]`: it is `Normal` but not `DotWF`, so `partition_of_normal`/`scalingOrderG_of_normal` (hyp. `DotWF`) do not apply to it directly. Value and counters are unaffected (`1_{x≠y}² = 1_{x≠y}`; dotted edges are not counted). Suggest the dispatcher add to T2050b: "partition terms satisfy `defnlvl0` but may repeat a ×-dotted pair; `def_graph1`'s at-most-one is restored by deduplication, not proved here".
2. The record's waved edges are oriented; the paper's "orientation of non-solid edges does not matter" (`7_8:151`) holds in Lean only for symmetric `S`, `S⁺` (no lemma in this file depends on it). Could be appended to T2050a/b by the dispatcher.
3. `Counters.scalingSize` at `W = 0` uses `0 ^ (negative) = 0` in Lean; irrelevant for the model (`W ≥ 1`), no theorem here uses `W = 0`.
4. Branch base `56c30fb` is behind `main` `6b2494e`; the files touched by the branch are unchanged on `main` since the base (§1), and the full library with the module imported builds (§2).

## Verdict
| target | verdict |
|---|---|
| 1. verbatim probe sections 1 and 3 | PASS |
| 2. vocabulary `def_graph1`, `ValG`, `def_poly`, `defnlvl0`, `dot-def`, `def scaling`, `def scaling order` | PASS |
| 3. basic lemmas (no internal vertices, relabeling, disjoint union, `ord` 2 and 4) | PASS |
| instances, build, axioms, registry, scope, paper deltas | PASS |
**Overall: PASS.** No dispatcher sign-off needed (observations 1-2 are paper-delta wording for the dispatcher).
