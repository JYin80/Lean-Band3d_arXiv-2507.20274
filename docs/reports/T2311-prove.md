Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct  7 08:48:34 UTC 2026

Targets in mathematics only. `PartitionSim`: for every model node `N` (`LGraph (Fin (N.a+1)) (Fin N.b)`, `N.ext : Fin 2 → Fin (N.a+1)` onto) and every `m : ℂ`, the lists `cPartitionX N.g N.ext` and `(N.g.partition m).map (pcomp (N.toP h))` are `Forall₂` for `(r,Q) ↦ Rel r.2 Q ∧ Q.g.coeff = m^{r.1.1} m̄^{r.1.2} r.2.g.coeff`. `ChildrenSim`: for every `N` and `c ∈ cands N.g`, `childrenX N c` and `(Cand.toR N h c hc).kids` are `Forall₂` for `(r,Q) ↦ Rel r.2 Q.2 ∧ r.1 = Q.1`.
Source of the merged definitions: `RBM3D/Graph/LWExpCert.lean` (namespace `RBM.Graph.LWCert`: `MNode` :46, `cMerge` :87, `Cand` :113), `RBM3D/Graph/LWExpTerm5.lean` (namespace `RBM.Gauss.Sizes`: `partitionX`, `pcomp`, `RCand.kids`, `lwSplitLoopsX_spec` :281), `RBM3D/Graph/LWVocab.lean` (`LGraph.partition` :1303, `partitionTerms` :1295, `merge`, `dotChoices` :1086, `dotAtoms`), `RBM3D/Graph/LWGGExp.lean` (`oe2xR2/R4–R8`), `RBM3D/Graph/LWWeightExp.lean` (`owxT1`, `owxExt` :458).

### (i) Exponent table (all rows are exact combinatorial identities; no analytic exponent enters)

| quantity | value | constraint it must satisfy | slack |
|---|---|---|---|
| `A` = #external reps of `labsOf` (so `N'.a = A-1`) | `1 ≤ A ≤ a+1` | `Fin (A-1+1) ≃ ExtCls Δ` needs `A ≥ 1` and `A = #ExtCls`: external vertices have the least indices, so a class contains an external vertex iff its least vertex is `< a+1`; `labs[0] = 0` | `A = 1` occurs (first root member: `a = 0`), `A = 2` occurs (member with `a = 1`); `A ≥ 1` has no failure case |
| `B` = `reps.length − A` (`N'.b`) | `0 ≤ B ≤ b` | `Fin B ≃ IntCls Δ`, Nat-subtraction harmless since the external reps are among the reps; internal reps are `≥ a+1` | exact |
| `labsOf` label of `v` | least vertex of its class | `unite` keeps `labs[i] ≤ i`, `labs[labs[i]] = labs[i]` | exact; checked on 3000 random lists (below) |
| `posOf` (class number) | index of the class among reps in increasing order | `pos < A` iff external; `mkV (A-1) B pos = inl ⟨pos⟩` or `inr ⟨pos−A⟩`, `(pos−A) % B = pos−A` | exact |
| consistency test of `cMerge` | `none` iff `×`-edge inside a class | equals `¬ Δ.Consistent` (`∀ e∈dotted, e.eq=false → cls e.x ≠ cls e.y`); equals `partitionTerms` filter | exact (iff via `labsOf` spec) |
| exponent pair of `lwSplitLoopsX` | `(j,j')`, `(1,0)` for σ=true loop, `(0,1)` for σ=false | `m^j m̄^j'` equals the coefficient of `lwSplitLoops m` (`lwSplitLoopsX_spec`) | exact |
| family shifts `(j,0)` of `famsX` | `R2:3, T1:1, R4:3, R5:1, R6:3, R7:1, R8:3` | equal to `sh 3,1,3,1,3` and `sh 1`, `sh 3` of `RCand.kids`; model adds `(r.1.1+j, r.1.2+0)`, real adds `(r.1.1+j, r.1.2)` | slack 0 (`n+0 = n`) |
| added internal vertices `k` | `R2:0, T1:1, R4:2, R5:1, R6:2, R7:1, R8:2` | `renum = relabel (Sum.map id finSumFinEquiv)`: `Fin b ⊕ Fin k ≃ Fin (b+k)`; `famsX` indices `b, b+1, b+2, b+1, b+2, b+1, b+2` | slack 0 (equal) |
| #families at `c` | `5 + 2·|c.q.2|` (`|c.q.2| = |solid| − 2`) | `famsX` and `kids` enumerate `lwSplit c.q.2` in the same order | first node with a candidate: `|solid| = 5`, 11 families (script) |
| #partition terms of the root `LWG5Graph k s` | 163 for each of the 4 `(k,s)` | both lists have equal length | script: 163 = 163; equals the 163 stated in `LWExpCert.lean` (`root_FF_shape` docstring) and T2307 report |
| `|E| < 2`, `0 < t < 1` (§29) | not present | the bridges are quantified over all `m : ℂ`, all `N` with `Function.Surjective N.ext`; no spectral parameter, no `ℓ` | not applicable |
| external hypothesis | none | no `[YY_25]`/`Θ` input; both targets are algebra of lists | no limit computation needed |

Facts from the files that the Lean proof must respect (no Lean written here):
- `Rel.cand` / `cands_spec` need exactly `hc : c ∈ cands N.g` (plus `Rel N P` for `Rel.cand`); `cands` builds `⟨x, p.1.dst, q.1.src, p, q⟩` with the tests `p.1.σ ∧ ¬circ ∧ dst ≠ inr x`, `q.1.σ ∧ ¬circ ∧ q.1.dst = inr x ∧ q.1.src ≠ inr x` (`LWExpCert.lean` `cands`), which are the six conjuncts of `cands_spec`.
- `partitionX_spec` (T2307, public) is only the coefficient list; the list-of-graphs form `Γ.partition m = (partitionX Γ).map (scale coefficient)` is `private theorem lwExpTerm5_partition_eq` (`LWExpTerm5.lean:299`, proof 8 lines from `lwSplitLoopsX_spec`). So `PartitionSim` reduces to the `partitionX` statement (exponents + `Rel`) plus this scaling (to be re-proved in the new file).
- `dotAtoms`, `aPairs` (`lwDedupPairs`), `bEdges`, `withDots`, `Consistent`, `merge`, `lwSplitLoopsX` are list functions that commute with an injective vertex map, so one general lemma "model graph `Γ_m` and real graph `Γ` with `Γ.solid = Γ_m.solid.map (SEdge.map (Sum.map eE eI))` (same for waved projection, dotted, `ext`) ⟹ `Forall₂` of `cPartitionX` and `partitionX`" yields `PartitionSim` (`eE=eI=id`) and, for the families, `ChildrenSim` (`eE = id`, `eI = finSumFinEquiv.symm`) without a separate relabel-naturality lemma; the scripts below verify exactly this relation.
- Type-level: `Rel`'s ext clause for `Q = pcomp (N.toP h) P` reads `Δ.extMap (N.ext i) = eE (N'.ext i)`; the equivalences are `eE j` = class of the `j`-th external rep, `eI j` = class of the `(A+j)`-th rep.

### (ii) One concrete nondegenerate instance

Data: root `LWG5Graph false false : LGraph (Fin 2) (Fin 3)` (`LWExpTerm3.lean:54`), `N = ⟨a=1, b=3, g, ext=![0,1]⟩` (ext onto `Fin 2`, 5 solid, 2 waved, 0 dotted edges), `m = 0.3+0.2i`; for `ChildrenSim`: members of `cPartitionX` with candidates, e.g. `a=1, b=1, ext=![0,1]`, `x=0`, `c.y = inl 1`, `c.y' = inl 0` (all 7 families, 11 of them with `lwSplit c.q.2`). Script (python only; own engine: classes by BFS, real class order reversed relative to least-vertex order, `Rel` witnesses searched from the edge lists, not built from the proof recipe; `labsOf`/`cMerge`/`cPartitionX`/`cands`/`famsX` transcribed from `LWExpCert.lean`, families from `LWGGExp.lean:485–539`, `LWWeightExp.lean:458–470, 658`):

```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2311 && python3 -I kids.py
PartitionSim root (k=F,s=F), a=1,b=3,ext=[0,1] surjective, m=0.3+0.2i: Forall2 OK=True, #terms=163
model first member: exponents (0, 0)  a=0 b=0 ext=[0, 0]  cands=0
ChildrenSim: 12 (node,cand) pairs checked, 3208 children total, all Forall2 OK = True, max #families 11
first node with cands: a=0 b=1 ext=[0, 0], cand x=0 y=('L', 0) y'=('L', 0); childrenX length=384, #families=11, OK=True
$ python3 -I extra.py
L1 labsOf = least vertex of BFS class: 3000 random instances, violations = 0
PartitionSim k=False s=False: OK=True #terms=163
PartitionSim k=False s=True: OK=True #terms=163
PartitionSim k=True s=False: OK=True #terms=163
PartitionSim k=True s=True: OK=True #terms=163
first member with a>=1 (ext0!=ext1) and a candidate: exps=(0, 0) a=1 b=1 ext=[0, 1] x=0 y=('L', 1) y'=('L', 0)
  ChildrenSim there: OK=True #children=434 #families=11
  ChildrenSim for all candidates of the first 15 such members: pairs=17 OK=True
control: rel(model,real) = True ; after flipping a circ flag in real solid[0]: False
```

`Forall2 OK` = equal length, equal exponent pairs (`r.1 = Q.1`), `Rel` (search for `eE`, `eI` with `P.ext i = eE (N.ext i)`, solid list, waved endpoint pairs, dotted list matched position-wise, cardinalities `a+1 = #ExtCls`, `b = #IntCls`), and for `PartitionSim` the coefficient equality against the literal `lwSplitLoops m` coefficients (tolerance 1e-12). The control line shows `Rel` fails on a tampered edge.
Nondegeneracy: `N.ext` onto; `N.a ∈ {0,1}`, `N.b ∈ {0,1,3}`; 163 partition terms; 11 families and 384 / 434 children; no empty index set, no `False` premise. The `m` coefficient test uses a complex `m` with `m ≠ m̄`.
Compile check of the pinned text (hub file, run now): `cd /Users/junyin/Lean_proof/RBM3D && lake env lean docs/tickets/checks/T2311-check.lean; echo exit=$?` printed `exit=0` (earlier `done:` lines in CONTROL record exit 1 on the previous version of the file).

### Verdicts
- `partitionSim` (Bridge 1): PASS. All hypotheses hold at the instance; statement true by the argument in (i) and the checks above.
- `childrenSim` (Bridge 2): PASS. Same.
- `rel_self` (optional): PASS (`eE = eI = Equiv.refl`; `N.toP h` has `ext = N.ext`, `g = N.g`).
- Note for stage 1b (not a verdict change): the ticket's target namespace line says `RBM.Gauss.Sizes`, but `MNode`, `Cand`, `cands`, `cMerge`, `tgt`, `leaf` are `RBM.Graph.LWCert.*` (`LWExpCert.lean:46,113`); field notation `N.toP`, `c.toR`-style calls need `MNode.toP` / `Cand.toR` declared as `RBM.Graph.LWCert.MNode.toP` / `RBM.Graph.LWCert.Cand.toR`.

## (a′) Preflight corrections — Wed Oct  7 09:36:34 UTC 2026

One statement of (a) is inaccurate; it changes no verdict. Facts bullet 3 of (a) says one general lemma gives both bridges "without a separate relabel-naturality lemma". The proof of that lemma (`lwExpSim_partition_sim`) uses the naturality of `dotChoices`, `withDots`, `Consistent` and the classes under a relabelling by an equivalence (file sections 4 and 6, 54 + 116 lines), because `cPartitionX (renum Γ)` enumerates the dotted choices of the renumbered graph and `partitionX Γ` those of `Γ`. This is the ticket's L4. The other claims of (a) used by the proof (163 terms, 11 families, the `ext` clause of `Rel` through `Δ.extMap`, `partitionX_spec` being only the coefficient list, the namespaces) hold.

## (b) Script output (section written Wed Oct  7 09:36:34 UTC 2026)

Commit on branch `t/T2311`: `2464793`, one file `RBM3D/Graph/LWExpSim.lean`.

```
$ lake build RBM3D.Graph.LWExpSim > build3.log 2>&1; echo exit=$?; sed -n '/Built RBM3D.Graph.LWExpSim/,$p' build3.log
exit=0
✔ [3884/3884] Built RBM3D.Graph.LWExpSim (5.6s)
Build completed successfully (3884 jobs).
```

```
$ TZ=UTC stat -f '%Sm %N' -t '%Y-%m-%d %H:%M:%S UTC' RBM3D/Graph/LWExpSim.lean build3.log   # log newer than the last edit
2026-10-07 09:27:34 UTC RBM3D/Graph/LWExpSim.lean
2026-10-07 09:27:41 UTC build3.log
```

```
$ lake env lean Ax.lean | python3 -I axgroup.py   # `#print axioms` of all 19 public declarations, grouped by axiom set
(root `Rel` of Mathlib, shown because `Rel` is ambiguous under `open RBM.Gauss.Sizes`): 'Rel' does not depend on any axioms
[propext, Classical.choice, Quot.sound]: 18 declaration(s): partitionSim childrenSim rel_self cands_spec Rel.scalingOrder_eq Rel.tgt_eq Rel.leaf_iff Rel.cand lwG5Cand_of_cands fams_eq_famsX PartitionSim ChildrenSim Rel cPartitionX famsX childrenX MNode.toP Cand.toR
[propext, Quot.sound]: 1 declaration(s): lwSplit_map
```

```
$ git diff --stat main...t/T2311; grep -c 'sorry\|admit\|native_decide' RBM3D/Graph/LWExpSim.lean; grep -c '^axiom' RBM3D/Graph/LWExpSim.lean; wc -l RBM3D/Graph/LWExpSim.lean; grep -c '^private' RBM3D/Graph/LWExpSim.lean; grep '^private' RBM3D/Graph/LWExpSim.lean | grep -vc lwExpSim_
 RBM3D/Graph/LWExpSim.lean | 1211 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1211 insertions(+)
0
0
    1211 RBM3D/Graph/LWExpSim.lean
67
0
```

Target statements (extracted from the file by script):

```
$ python3 -I extract.py
-- LWExpSim.lean:120
def Rel (N : MNode) (P : PGraph (Fin 2)) : Prop :=
  ∃ (eE : Fin (N.a + 1) ≃ P.E') (eI : Fin N.b ≃ P.I'),
    (∀ i, P.ext i = eE (N.ext i)) ∧
    P.g.solid = N.g.solid.map (SEdge.map (Sum.map eE eI)) ∧
    P.g.waved.map (fun e => (e.x, e.y)) = N.g.waved.map (fun e => (Sum.map eE eI e.x, Sum.map eE eI e.y)) ∧
    P.g.dotted = N.g.dotted.map (DEdge.map (Sum.map eE eI))
-- LWExpSim.lean:201
def PartitionSim : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (m : ℂ),
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : PGraph (Fin 2)) => Rel r.2 Q ∧ Q.g.coeff = m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff)
      (cPartitionX N.g N.ext) ((N.g.partition m).map (pcomp (N.toP h)))
-- LWExpSim.lean:208
def ChildrenSim : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (c : Cand N.a N.b) (hc : c ∈ cands N.g),
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
      (childrenX N c) (Cand.toR N h c hc).kids
-- LWExpSim.lean:1093
theorem partitionSim : PartitionSim := by
-- LWExpSim.lean:1143
theorem childrenSim : ChildrenSim := by
-- LWExpSim.lean:1157
theorem rel_self (N : MNode) (h : Function.Surjective N.ext) : Rel N (N.toP h) := by
```

Compiled nonempty instances (section 10 of the file; docstrings and blank lines dropped by the command; all are `example`s of the build above):

```
$ awk '/^\/-! ## 10/{f=1} f' RBM3D/Graph/LWExpSim.lean | grep -v '^/--\|^`\|^(`\|^$' | sed '/^end RBM.Gauss.Sizes/,$d'
/-! ## 10. The compiled instances -/
private def lwExpSim_rootN : MNode := ⟨1, 3, LWG5Graph false false, ![0, 1]⟩
private theorem lwExpSim_rootN_surj : Function.Surjective lwExpSim_rootN.ext := by decide
example : List.Forall₂
    (fun (r : (ℕ × ℕ) × MNode) (Q : PGraph (Fin 2)) =>
      Rel r.2 Q ∧ Q.g.coeff = (⟨1 / 2, 1 / 3⟩ : ℂ) ^ r.1.1 * star (⟨1 / 2, 1 / 3⟩ : ℂ) ^ r.1.2 * r.2.g.coeff)
    (cPartitionX lwExpSim_rootN.g lwExpSim_rootN.ext)
    ((lwExpSim_rootN.g.partition ⟨1 / 2, 1 / 3⟩).map (pcomp (lwExpSim_rootN.toP lwExpSim_rootN_surj))) :=
  partitionSim lwExpSim_rootN lwExpSim_rootN_surj ⟨1 / 2, 1 / 3⟩
example : (cPartitionX lwExpSim_rootN.g lwExpSim_rootN.ext).length = 163 := by decide +kernel
example : Rel lwExpSim_rootN (lwExpSim_rootN.toP lwExpSim_rootN_surj) := rel_self _ _
private def lwExpSim_instN : MNode := ⟨1, 1, lwExpTerm3_instGraph, ![0, 1]⟩
private theorem lwExpSim_instN_surj : Function.Surjective lwExpSim_instN.ext := by decide
private def lwExpSim_instC : Cand lwExpSim_instN.a lwExpSim_instN.b := (cands lwExpSim_instN.g)[0]'(by decide)
example : List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) => Rel r.2 Q.2 ∧ r.1 = Q.1)
    (childrenX lwExpSim_instN lwExpSim_instC)
    (Cand.toR lwExpSim_instN lwExpSim_instN_surj lwExpSim_instC (List.getElem_mem _)).kids :=
  childrenSim lwExpSim_instN lwExpSim_instN_surj lwExpSim_instC (List.getElem_mem _)
example : (cands lwExpSim_instN.g).length = 1 ∧ (famsX lwExpSim_instN.g lwExpSim_instC).length = 11 ∧
    (childrenX lwExpSim_instN lwExpSim_instC).length = 550 := by
  decide +kernel
```

```
$ clash.sh   # declarations with a new public name elsewhere in RBM3D (Probe and the new file excluded)
[Rel] RBM3D/Graph/Model.lean:236:def Rel : Case → Counters → Counters → Prop
(`RBM.Graph.Case.Rel`: Model.lean:50 `namespace RBM.Graph`, :232 `namespace Case`; the new name is `RBM.Gauss.Sizes.Rel`: no clash)
```

```
$ python3 -I pincheck.py | awk '{n+=/True/; m+=/False/} END {print "ticket pin blocks occurring in the file: " n " True, " m " False"}'; lake env lean PinScratch.lean; echo lean-exit=$?
ticket pin blocks occurring in the file: 9 True, 0 False
partitionSim : PartitionSim
childrenSim : ChildrenSim
lean-exit=0
(PinScratch.lean: the 9 ticket blocks in `namespace Scratch`, then `example : Scratch.X = X := rfl` for each; `#check` of the two theorems)
```

```
$ python3 -I probecheck.py | grep -v '^all' | awk '{n+=/True/; m+=/False/} END {print "probe blocks equal to the file: " n " True, " m " False"}'   # blocks of the probe t/T2288:RBM3D/Probe/T2288Cert.lean
probe blocks equal to the file: 16 True, 0 False
```

```
$ lake env lean Pre.lean > pre_final.log; echo exit=$?; grep -c error pre_final.log; grep 'premises found' pre_final.log   # Pre.lean: import RBM3D, import RBM3D.Graph.LWExpSim, #assert_rbm_axioms
exit=0
0
premises found by scanning: 148 (borrowed 1, owed 89, structural 41, refuted 6, superseded 11).
```

### Narrative

- Deliverables. One new file, `RBM3D/Graph/LWExpSim.lean` (1211 lines, commit above): the 16 pinned definitions and lemmas (equal to the ticket and to the probe, above), the targets `partitionSim` and `childrenSim`, the optional target `rel_self`, 67 private helpers (all prefixed `lwExpSim_`) and 5 `example`s. No hypothesis, no `sorry`, only the three standard axioms. `RBM3D/Test/Axioms.lean` is unchanged (see (d) 1).
- Namespaces. The ticket's targets line says `RBM.Gauss.Sizes`; the comment of the check file (section 2) says `RBM.Graph`. Everything is in `RBM.Gauss.Sizes` except `MNode.toP` and `Cand.toR`, which are in `RBM.Graph.LWCert` (note at the end of (a)): the pinned text writes `N.toP h`, and field notation looks for `RBM.Graph.LWCert.MNode.toP`.
- Design. One general lemma carries both bridges (`lwExpSim_partition_sim`): for `Γ : LGraph (Fin (N.a+1)) I` and an equivalence `τ : Fin (N.a+1) ⊕ I ≃ Fin (N.a+1) ⊕ Fin b'` fixing the external vertices, `cPartitionX (Γ.relabel τ) N.ext` and `partitionX Γ` are `List.Forall₂` for the exponents, `Rel` (read through `N.ext`) and the coefficients. `partitionSim` is `τ = Equiv.sumCongr (Equiv.refl _) (Equiv.refl _)`; `childrenSim` uses `τ = Equiv.sumCongr (Equiv.refl _) finSumFinEquiv`, for which `Γ.relabel τ` is `renum Γ` up to unfolding (accepted by `exact`). `Rel` is built for the real graph directly: no second packed graph and no composition of two `Rel`s.
- Layers (line ranges of the file). §2 (213-686): `lwExpSim_labsOf_good` shows by induction on the edge list through `unite` that `labsOf` returns least class vertices (`labs[i] ≤ i`, `labs[labs[i]] = labs[i]`, `labs[u] = labs[v] ↔ EqvGen`); `posOf` and `repsOf` are `Nat.count` ranks (`Nat.count_strict_mono`, `Nat.count_injective`, an induction for onto-ness); `lwExpSim_phi_spec`: the labelling inside `cMerge` has the classes as fibres, is onto `Fin (A-1+1) ⊕ Fin (#reps-A)` and sends exactly the external classes left; `lwExpSim_cMerge_none/some` (`none ↔ ¬ Consistent`). §3 (687-759) `lwExpSim_equivs`: such a labelling gives `eE`, `eI` with `vmap = Sum.map eE eI ∘ ψ`. §4, §6 (760-813, 913-1028): naturality of `cls`, `Consistent`, `aPairs`, `bEdges`, `dotBase`, `dotAtoms`, `dotChoices`, `withDots` under `relabel` by an equivalence. §5 (814-912) `lwExpSim_term_some`: one consistent dotted term, `cMerge` against `merge`, `lwSplitLoopsX` relabelled. §7 (1029-1064): the filter/`flatMap` induction. §8, §9: the bridges; §9 has seven blocks (R2 with `τ = id`; `owxT1`, R4, R5, R6, and the R7/R8 pair under `lwSplit c.q.2` with `renum`).
- Sizes. 1211 lines against the ticket's 650 / 800 / 1100 and cap 1500; §2 (474 lines) is the largest piece (portmap L1 + L2: 250). No cut 3a/3b is proposed.
- Instances. `partitionSim`: the root `LWG5Graph false false` as a model node (a = 1, b = 3, ext = ![0, 1]), `m = 1/2 + i/3` (`m ≠ m̄`), 163 partition terms (kernel-checked); `childrenSim`: `lwExpTerm3_instGraph` (a = 1, b = 1) at its unique candidate, 11 families and 550 children (kernel-checked); `rel_self` at the root node. `ext` is onto by `decide`; no `N = 0`, no empty index set, no `False` premise.
- Not done: `RelInvariance`, `SoundStep`, `SoundRoot` (ticket 4). The full `lake build` is the hub's merge step (the root import is the hub's file); the pre-check above imports `RBM3D` and the new module instead.

## (c) Verified Mathlib and core names (one `#check @name` each, 98 names used in the file, none invented)

```
$ python3 -I names.py > names.txt; (echo 'import RBM3D.Graph.LWExpSim'; sed 's/^/#check @/' names.txt) > NamesCheck.lean; lake env lean NamesCheck.lean | grep -c error
0
```
```
Bool.and_eq_true Bool.false_eq_true Bool.not_eq_true' Bool.or_eq_true EmbeddingLike.apply_eq_iff_eq Equiv.ofBijective
Equiv.refl Equiv.sumCongr Fin.ext Fin.val Fintype.card_congr Function.Injective Function.Surjective Function.comp_def
List.Forall₂ List.any_eq_true List.any_map List.append_assoc List.append_nil List.countP_eq_length_filter List.filter
List.filter_append List.filter_congr List.filter_cons List.filter_eq_self.2 List.filter_map List.flatMap_append
List.flatMap_assoc List.flatMap_congr List.flatMap_cons List.flatMap_map List.flatMap_nil List.foldl_map
List.forall₂_map_left_iff List.forall₂_map_right_iff List.forall₂_map_right_iff.2 List.forall₂_same
List.getD_eq_getElem List.getElem_mem List.getElem_range List.length List.map List.map_append List.map_congr_left
List.map_cons List.map_flatMap List.map_map List.mem_append.1 List.mem_append_left List.mem_append_right
List.mem_cons_of_mem List.mem_cons_self List.mem_filter List.mem_filter.1 List.mem_filter.2 List.mem_filterMap
List.mem_flatMap List.mem_map List.mem_map.2 List.mem_range.1 List.mem_singleton List.mem_singleton_self
List.nil_append List.range List.range_succ List.rel_append Nat.count Nat.count_injective Nat.count_monotone
Nat.count_strict_mono Nat.count_succ Nat.count_zero Nat.lt_succ_iff_lt_or_eq.1 Nat.lt_succ_self Nat.mod_eq_of_lt
Prod.map Prod.snd Quotient.eq Quotient.exists_rep Quotient.lift Quotient.sound Relation.EqvGen Relation.EqvGen.mono
Relation.EqvGen.refl Relation.EqvGen.rel Relation.EqvGen.symm Relation.EqvGen.trans Subtype.ext Subtype.val
Sum.elim_inl Sum.elim_inr Sum.inl Sum.inl.inj Sum.inr Sum.inr.inj Sum.map Sum.map_inl Sum.map_inr
```
Verified absent from the import closure of the file: `Nat.nth` (exists in `Mathlib/Data/Nat/Nth.lean`; not used; `lwExpSim_exists_count` is a 17-line induction on `Nat.count_succ` instead). The suffixes `.1`/`.2` above are `Iff` projections.

## (d) Open issues and paper-delta candidates

1. Registry (§16, §20). `RBM3D/Test/Axioms.lean` is unchanged. With `rel_self` present the pre-check lists nothing. On the earlier version of the module (before `rel_self` and section 10 were added) the same `Pre.lean` printed, in that run's tool log: `error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of ...: [RBM.Gauss.Sizes.Rel]`. So `PartitionSim` and `ChildrenSim` are not listed (a theorem with that head is proved here), and `Rel` is listed only while no theorem concludes with `Rel`; `rel_self` is one. If the dispatcher prefers `Rel` registered as a structural predicate (portmap §7), add `RBM.Gauss.Sizes.Rel` to `structuralProps`; the registry line then prints it under "carry nothing yet".
2. `Rel` and Mathlib's `_root_.Rel`: under `open RBM.Gauss.Sizes` outside the namespace the bare name is ambiguous in commands, while `Rel N P` in terms elaborates (the first two `example`s of `RelAmb.lean` compile, `#check @Rel` fails):
```
$ lake env lean RelAmb.lean   # `open RBM.Graph RBM.Graph.LWCert RBM.Gauss.Sizes`; line 3 `example ... : Prop := Rel N P`, line 4 `rel_self`, line 5 `#check @Rel`
RelAmb.lean:5:7: error: Ambiguous term
  @Rel
Possible interpretations:
  _root_.Rel : Type ?u.2 → Type ?u.1 → Type (max ?u.2 ?u.1)
  
  RBM.Gauss.Sizes.Rel : MNode → PGraph (Fin 2) → Prop
```
   Ticket 4 should write the full name `RBM.Gauss.Sizes.Rel` where a bare `Rel` stands alone in a command.
3. Namespace difference between the ticket's targets line and the check file's comment: see narrative; both targets are `RBM.Gauss.Sizes.partitionSim` and `RBM.Gauss.Sizes.childrenSim`.
4. The general lemmas (`lwExpSim_partition_sim`, `lwExpSim_term_some`, `lwExpSim_equivs`) are private. The O3 note of the ticket lists what ticket 4 uses (`Rel.scalingOrder_eq`, `Rel.tgt_eq`, `Rel.cand`, `PartitionSim`, `ChildrenSim`); all are public here. A public relabel form would need a primed name.
5. Paper-delta candidates: none (no paper content; both sides are merged Lean definitions). Ports from `../RBM1D` / `../RBM2D`: none, so no diff-stat.
