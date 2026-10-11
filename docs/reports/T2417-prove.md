Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 10:17:15 UTC 2026

Verdict: target 1 PASS, target 2 PASS, target 3 PASS, target 4 PASS, target 5 PASS. No statement fails as written (checked by the Python model below; no Lean was run, as 1a requires).
Reading of the ticket's "M-edge inside an atom": an `M`-dotted edge `M_{αβ}` parallel to a solid edge `α→β`, so the solid edge lies inside one atom (the K1 case); the "between atoms" case is a solid edge joining two different atoms.

### (i) Exponent table (the targets are combinatorial: no analytic exponent, no threshold; the constants are counters and slots)

| Quantity | Value | Constraint the pin imposes | Slack |
|---|---|---|---|
| `Counters` of the image, slots `(nS, nW, nV, nM, 0, 0)` (`LGraph.counters`, `LWVocab.lean:182`) | image slot `nV` = `card IntCls` | equals the BA slot `nV := nA` of `BAGraph.counters` (`BAVocab.lean:141-143`), the other slots equal | equalities, slack 0 |
| `ord = nS + 2(nW - nA)` (`BAVocab.lean:146-148`) | follows from the counters | `ord(img) = ord(Γ)` | 0 |
| `nExt` = number of atoms with an external vertex | `card (img).E'` | equal | 0 |
| atom-level loops / pairs | `lvl1NLoops` (`LWLvl1.lean:603`), `lvl1NPairs` (`:606`) of the image | equal `nLoops`, `nPairs` | 0 |
| `circ` flag of an image solid edge | `e.circ && decide (same atom)` | `CircIffLoop` (`LocalRegular6a.lean:162`) needs `circ = true ↔ loop`; holds when every solid edge of `Γ` is circled (`BAGraph.Normal`, `BAVocab.lean:158`) | exact on normal `Γ`; fails for an uncircled in-atom edge of a non-normal `Γ` (only `(m0)`-type claims need it, and they assume `Normal`) |
| `PathInv2 k` (`LocalRegular2.lean:1577`), `k` free | `k` the same on both sides | `(img (liftC P0)).PathInv2 k ↔ P0.PathInv2 k` for every `k` | no relation between `k` and the graph is needed |
| External hypotheses | none | every pin below is proved here from `BAVocab` and merged band lemmas | no limit computation applies |

**The choice of the one map (ticket (i)).** Order: `promoteC` first, then `LGraph.mergeP`, i.e. T2397's `img` (probe 29-48); `BAPGraph.img` is `lvl1Comp` of it (T2395 `BAPGraph.img`, probe 228); with this choice T2397's `img` on `BAPGraph (Fin 2)` is `BAPGraph.img` by `rfl`. State `BAGraph.img Γ := (promoteC Γ).mergeP : PGraph E`; `(m0)`-`(m2)` and `BAimg` over arbitrary `E` (nothing uses `Fin 2` there); only `BAPathLift` stays at `Fin 2` (`PathInv2` is defined only there). Reasons:
1. The flags are fixed before the quotient: `circ := e.circ && decide (atomSetoid …)` and the `×`-dots are statements about the vertices of `Γ`, with no `decide (e.src = e.dst)` on `ExtCls ⊕ IntCls` (classical `DecidableEq`, `LWVocab.lean`, instances of `Cls`).
2. The downstream pins (`scostA` probe 40, `BAImgMol` 118, `liftC`/`scostA_liftC` 221-246, `BABridge` via `LGraph.scost_relabel` `LocalRegular6a.lean:401`) are written against `promoteC`; this order keeps them verbatim (T2397 statements unchanged).
3. T2395's order is not lost: `BAimg` is stated on the same map; the other construction is proved equivalent (next paragraph).

**Relation to the other construction (target 2).** Call `BAGraph.img95 Γ` T2395's (probe 222-227: `mergeP` of `{Γ.toLGraph with dotted := Γ.dotted ++ eq1}`, then solid edges rebuilt with `circ := decide (src = dst)` and `×`-dots on non-loops). Equality of the packed graphs cannot be stated: `ExtCls`, `IntCls` are quotients by `eqSetoid` of two different `dotted` lists (equal as relations, not definitionally), as T2397 audit D1 noted. The statement to prove (`PGraph` equivalence = relabelling, as `LGraph.relabel`, `LWVocab.lean:460`): for `Γ.Normal` there are bijections `eE : ExtCls₁ ≃ ExtCls₂`, `eI : IntCls₁ ≃ IntCls₂` with `ext₂ = eE ∘ ext₁` and `img₂.g = img₁.g.relabel (Sum.map eE eI)` as records (lists equal: solid with `circ`, waved, `×`-dots in the same order). For general `Γ` the same holds with the `circ` flags ignored; the flags differ exactly on solid edges that are uncircled in `Γ` and lie in one atom (T2397 keeps them uncircled, T2395 circles every loop). Paper-delta candidate `T2417a` for that difference (one construction, `promoteC` verbatim). Evidence: script 1 below (`eq_normal_fail 0`, `eq_nonnormal_circ_only 12958`, `eq_nonnormal_other 0`).
The one fact both constructions need: for `L := promoteC Γ`, `L.cls u = L.cls v ↔ v ∈ Γ.atom u` (`EqRel L` is `atomAdj`, `BAVocab.lean:92`; `EqvGen` of a symmetric relation is `ReflTransGen`, `BAGraph.mem_atom_iff` `BAVocab.lean:387`). Hence `vmap u = vmap v ↔ same atom`, `(vmap u).isRight ↔ intAtom u`, `IntCls ≃ {internal atoms}`, `ExtCls ≃ {atoms with an external vertex}`.

**Vocabulary (target 1).** Copy probe T2395 27-41 (`sameAtom … nPairs`) and 56-66 (`atEdges`, `atCharge`, `LocStd`) verbatim, `baPG` 218. The probe lines 42-55 (`BALvl1Good`, `BALvl1GoodLit`) are in the range "27-63" of the ticket but belong to rows L3a3-L3a5 (T2395-design §6 row "L3a3-L3a5: measure 27-41, `BALvl1Good` 44, `BALvl1GoodLit` 50, `LocStd` 63"): not copied here (finding for the dispatcher; adding them would risk a name clash with L3a3).

**Split decision (ticket (iv)):** a second file is recommended: yes. Boundary: `BAAtomic.lean` = targets 1-3 together with `(m0)`, `(m1)`, `(m2)` as theorems with their pin `def`s (they are inputs of `BAimg`: counters need `(m1)`, `(m2)`; normality needs `(m0)`); `BAAtomic2.lean` = `liftG`, `liftC`, `liftC_normal`, `BAPathLift` and the target-5 instances. This differs from the ticket's "boundary at target 4" only in that `(m0)`-`(m2)` stay in file 1.

### Pin table (ticket (ii)): what each pin reduces to, and what is new

| Pin (statement source) | Merged lemmas it reduces to (file:line) | New |
|---|---|---|
| `(m0)` `BAImgNormal` (T2397:108) | `LGraph.Normal` `LWVocab.lean:990` (unfold with `LGraph.merge` `:778`), `CircIffLoop` `LocalRegular6a.lean:162`, `BAGraph.mem_atom_iff` `BAVocab.lean:387` | key lemma above; `SBetween ↔ XBetween` on the image (non-loop solid edges of the image are exactly the edges between different atoms); loops circled since `Γ` circled |
| `(m2)` `BAImgMol` (T2397:118) | `BAGraph.mem_mol_iff` `BAVocab.lean:394`, `atom_subset_mol` `:400`, `LGraph.molGraph` `LWVocab.lean:491`, `molOf` `:573` | a `ReflTransGen` of `Γ.adj` maps to one of the image's waved graph (atom steps collapse), and a waved path of the image lifts (each class is connected by `atomAdj`) |
| `(m1)` `BAImgCounters` (T2397:115) | `BAGraph.counters_ofLGraph` `BAVocab.lean:533` (case without dotted edges only; the private `BAVocab_merge_counters` `:1107` needs `vmap` injective, which fails here) | `nS`, `nW` by `List.length_map`; `nV = nA` by `IntCls ≃ internal atoms`; `nM` by `(m2)` and surjectivity of `vmap` (a molecule has an external vertex iff its image does, since atoms lie in molecules) |
| `BAimg` conjunct 1 (counters) | `(m1)` | none |
| `BAimg` conjunct 2 (loops) | `lvl1Loops` `LWLvl1.lean:77` (no `circ`, so independent of the flag) | `countP` over `map` and the key lemma |
| `BAimg` conjunct 3 (pairs) | `lvl1Share` `:80`, `lvl1Pairs` `:85` with `int = Sum.isRight` | termwise: `[src = src' ∧ int]` etc. equals the `filter … length` of `nShare`, by `vmap`-equality ↔ same atom and `isRight ↔ intAtom` |
| `BAimg` conjunct 4 (`card E' = nExt`) | `Fintype.card_congr` | `ExtCls ≃` image of the external atoms |
| `BAimg` conjunct 5 (`Normal`) | `(m0)` | none |
| `BAimg` conjunct 6 (`LocStd ↔`), `Γ.Normal` | `LGraph.LocStd` `LWLvl1.lean:3204`, `StdNeutral` `:3199`, `lvl1SolidAt/DegAt/ChargeAt` `:1540-1546` | image `solidAt (vmap v)` = `atEdges v` (same list order, same `σ`, same charge formula); `∀ q : IntCls` ↔ `∀ i, intAtom (inr i)` (every internal class has an `inr` member); `(m0)` for the `Normal` conjunct |
| `BAPathLift` (T2397:355) | `LGraph.localReg2_pathFam_map` `LocalRegular2.lean:616` (both directions: `vmap` and its inverse, `Equiv.ofBijective`), `PGraph.PathInv2` `:1577` | `atom (ofLGraph …) = {v}` for a graph without `=`-dots (`BAVocab_atom_ofL` `BAVocab.lean:510` is private: re-prove as T2397:130-215), `vmap` bijective then; the image has the same `(σ, src, dst)` and `waved` as `P0.g` up to `vmap` and `mapMS_comp`; `circ` and `×`-dots are not read by `localReg2_PathFam` |

Observations (no change to a pin): `BAImgMol` is a statement about `Q.g` alone, so it is stated over `BAGraph E I` (free) and read at `Q.g`; the ticket's "`molNV`/`molNW`" (`LocalRegular.lean:1771-1774`) do not occur in the probe's pin (`molOf` iff); they are consumers of `(m2)` (`molNV_le_molNW_add_one` `LocalRegular.lean:1778` at the image), not targets.

### (ii) One concrete nondegenerate instance

Vertices `x = 0, y = 1` external, `α = 2, β = 3, γ = 4` internal (`inr 0,1,2`). `Γ0`: solid `blue α→β` (circled), `blue x→α`, `red γ→y`, `blue γ→γ` (all circled); waved `β—γ`; one original `×`-dot `x—α`; `M`-dotted `M_{αβ}` (blue). Atoms `{x}, {y}, {α,β}, {γ}`: the solid edge `α→β` is inside an atom (K1), `x→α` and `γ→y` join different atoms, `γ→γ` is a self-loop: `n_S = 4`, `n_W = 1`, `n_A = 2`, `n_M = 1`, `nLoops = 2`, `nExt = 2`; all hypotheses of the pins hold (`BAGraph.Normal`: no `=`-dot, all solid circled). `Γ1` (`LocStd` case): `E = Fin 2`, `I = Fin 2`, solid `blue x→α`, `red y→β`, `M_{αβ}`; the atom `{α,β}` has two edges `[blue, red]` of charge `+1 - 1 = 0`. `liftC P0`: `P0 = p2Graph.pack` (`LWVocab.lean`: `E = Fin 2`, `I = Fin 4`, normal, `CircIffLoop`), all solid edges circled, no `Ψ`/`M`. Script 2 re-implements the definitions in Python (union-find atoms, `promoteC`, merge, the band counters, `Normal`, `LocStd`) and prints both constructions on the three instances; script 1 tests the pins on 60,000 random BA graphs (36,187 of them BA-normal, `nE ∈ 1..3`, `nI ∈ 0..4`, up to 5 solid edges, `Ψ`, `M`, `=`-dots).

Command (script 1): `cd <scratchpad>/T2417 && python3 check.py`
```
{'n': 60000, 'normal': 36187, 'locstd': 9913, 'pin_fail': 0, 'eq_normal_fail': 0, 'eq_nonnormal_circ_only': 12958, 'eq_nonnormal_other': 0, 'm2_fail': 0, 'm0_fail': 0, 'locstd_iff_fail': 0, 'nonnormal_img97_not_normal': 0}
```
(`pin_fail` counts any failure of conjuncts 1-4 of `BAimg` for either construction on any graph; `m0_fail`, `locstd_iff_fail` count conjuncts 5-6 on BA-normal graphs; `m2_fail` is `(m2)` on all graphs; `nonnormal_img97_not_normal` is a placeholder counter that is never incremented, not a test.)

Command (script 2): `cd <scratchpad>/T2417 && python3 inst.py`
```
G0 (K1: solid alpha->beta inside atom {alpha,beta}; x->alpha between atoms; loop at gamma) atoms [0, 1, 3, 3, 4] BAnormal True
  BA counters (nS,nW,nA,nM) (4, 1, 2, 1) nLoops 2 nPairs 0 nExt 2 LocStd False
  T2397 img counters (4, 1, 2, 1) lvl1NLoops 2 lvl1NPairs 0 card Ext 2 Normal True CircIffLoop True LocStd False
  T2395 img counters (4, 1, 2, 1) lvl1NLoops 2 lvl1NPairs 0 card Ext 2 Normal True CircIffLoop True LocStd False
  solid [(True, True, 2, 2), (True, False, 0, 2), (False, False, 4, 1), (True, True, 4, 4)] waved [(False, True, 2, 4)] dotted [(False, 0, 2), (False, 4, 1)] equal to T2395 construction: True m2 True
G1 (LocStd) atoms [0, 1, 3, 3] BAnormal True
  BA counters (nS,nW,nA,nM) (2, 0, 1, 1) nLoops 0 nPairs 1 nExt 2 LocStd True
  T2397 img counters (2, 0, 1, 1) lvl1NLoops 0 lvl1NPairs 1 card Ext 2 Normal True CircIffLoop True LocStd True
  T2395 img counters (2, 0, 1, 1) lvl1NLoops 0 lvl1NPairs 1 card Ext 2 Normal True CircIffLoop True LocStd True
  solid [(True, False, 0, 2), (False, False, 1, 2)] waved [] dotted [(False, 0, 2), (False, 1, 2)] equal to T2395 construction: True m2 True
p2Graph band Normal: True  CircIffLoop: True
lift: BAnormal True counters (6, 2, 4, 2) band counters of P0 (6, 2, 4, 2)
img(liftC P0) vs P0: solid ends/colours equal True  waved equal True  molecule partition equal True  dotted as sets True
random normal band graphs 20000 mismatches of img(liftC P0) with P0 on (solid ends, waved, x-dots, vertex map = id): 0
```
(In the printed image, vertex labels are the least vertex of the class: class `2` = `{α,β}`, `4` = `γ`; `G0`'s image has the loop `2→2` circled and the non-loops uncircled, with `×`-dots `x—{αβ}`, `γ—y`.) Both `Γ0` and `Γ1` are non-degenerate: nonempty `E`, `I`, solid edges, a non-trivial atom, `nExt = 2`.

### Verdicts per target
- **1 (vocabulary), PASS:** definitions over merged `BAVocab`; nothing to prove beyond decidability instances.
- **2 (one map), PASS:** `BAGraph.img Γ := (promoteC Γ).mergeP`; equivalence to T2395's construction for `Γ.Normal` (circ flags ignored for general `Γ`); script 1.
- **3 (`BAimg`), PASS:** all six conjuncts hold as stated (`pin_fail 0`, `m0_fail 0`, `locstd_iff_fail 0` on 60,000 random graphs for both constructions).
- **4 (`(m0)`, `(m1)`, `(m2)`, `BAPathLift`), PASS:** all hold as stated (`m2_fail 0`, `m0_fail 0`; script 2 and its 20,000-graph lift test agree with the reduction of `BAPathLift` to `localReg2_pathFam_map`).
- **5 (instances), PASS:** data `Γ0`, `Γ1`, `liftC p2Graph.pack` above; every deterministic hypothesis (`Normal`, `CircIffLoop`, `Fin` types) holds at them.
- **Paper-delta candidates:** `T2417a` (the image keeps an uncircled in-atom edge of a non-normal `Γ` uncircled: `promoteC` verbatim; the pins assume `Normal` where it matters).

## (b) Script output (commands run in `RBM3D-wt/T2417`, branch `t/T2417`; `date -u` at assembly: Sun Oct 11 11:00:57 UTC 2026)
```
$ wc -l RBM3D/Graph/BAAtomic.lean RBM3D/Graph/BAAtomic2.lean
     985 RBM3D/Graph/BAAtomic.lean
     262 RBM3D/Graph/BAAtomic2.lean
    1247 total
$ lake build RBM3D.Graph.BAAtomic RBM3D.Graph.BAAtomic2 | grep -E "Built RBM3D.Graph.BAAtomic|Build completed"
Build completed successfully (3388 jobs).
$ echo "warnings in the two files: $(lake build RBM3D.Graph.BAAtomic RBM3D.Graph.BAAtomic2 2>&1 | grep -c "warning: RBM3D/Graph/BAAtomic")"
warnings in the two files: 0
$ lake env lean docs/tickets/checks/T2417-check.lean; lake build | tail -1
check file T2417-check.lean: exit 0
Build completed successfully (4226 jobs).
$ printf "import RBM3D\nimport RBM3D.Graph.BAAtomic\nimport RBM3D.Graph.BAAtomic2\n#assert_rbm_axioms\n" > pre.lean; lake env lean pre.lean | head -1
pre-check exit 0
axiom audit: 11675 theorems, 3571 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean ax.lean | head -1   # collectAxioms over every public declaration of the two modules
public declarations: 67 theorems, 28 other; with a non-standard axiom: 0 []
$ lake env lean ax2.lean   # #print axioms of the 16 targets and graph forms, grouped
  16 [propext, Classical.choice, Quot.sound]
$ python3 pindiff.py   # the 21 pinned declarations (T2395 probe 27-66, 218-232; T2397 probe 29-48, 108-118, 219-246, 355) against this file, `img` -> `BAPGraph.img`, binders normalised
  21 SAME
$ name-clash check (every public name of the two files against every tracked RBM3D file; `ax.out`, `clash.py`)
public names of the two files: 85 ; declared under the same name in the other 456 tracked RBM3D files: 0
$ git diff --stat main...t/T2417
 RBM3D/Graph/BAAtomic.lean  | 985 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAAtomic2.lean | 262 ++++++++++++
 2 files changed, 1247 insertions(+)
```
Target statements (extracted by `extract.py`; `BAimg`, `BAImg*`, `BAPathLift` are the pins, `*_holds` their proofs):
```
BAAtomic : def BAGraph.img (Γ : BAGraph E I) : PGraph E := (promoteC Γ).mergeP
BAAtomic : def BAPGraph.img {E : Type} (P : BAPGraph E) : PGraph E := PGraph.lvl1Comp P.g.img P.ext P.ext_surj
BAAtomic : def BAimg : Prop := ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I), Γ.img.g.counters = Γ.counters ∧ Γ.img.g.lvl1NLoops = Γ.nLoops ∧ Γ.img.g.lvl1NPairs = Γ.nPairs ∧ Fintype.card Γ.img.E' = Γ.nExt ∧ (Γ.Normal → Γ.img.g.Normal) ∧ (Γ.Normal → (Γ.LocStd ↔ Γ.img.g.LocStd))
BAAtomic : theorem BAimg_holds : BAimg
BAAtomic : def BAImgNormal : Prop := ∀ P : BAPGraph (Fin 2), P.g.Normal → (BAPGraph.img P).g.Normal ∧ LGraph.CircIffLoop (BAPGraph.img P).g
BAAtomic : def BAImgMol : Prop := ∀ (Q : BAPGraph (Fin 2)) (u v : Q.E' ⊕ Q.I'), (promoteC Q.g).merge.molOf ((promoteC Q.g).vmap u) = (promoteC Q.g).merge.molOf ((promoteC Q.g).vmap v) ↔ v ∈ Q.g.mol u
BAAtomic : def BAImgCounters : Prop := ∀ Q : BAPGraph (Fin 2), (BAPGraph.img Q).g.counters = Q.g.counters
BAAtomic2 : def BAPathLift : Prop := ∀ P0 : PGraph (Fin 2), P0.g.Normal → ∀ k, (BAPGraph.img (liftC P0)).PathInv2 k ↔ P0.PathInv2 k
BAAtomic2 : theorem BAPathLift_holds : BAPathLift
BAAtomic : theorem BAGraph.img95_equiv_gen (Γ : BAGraph E I) : ∃ (eE : Γ.img95.E' ≃ Γ.img.E') (eI : Γ.img95.I' ≃ Γ.img.I'), (∀ a, Γ.img.ext a = eE (Γ.img95.ext a)) ∧ Γ.img.g.waved = (Γ.img95.g.relabel (Sum.map eE eI)).waved ∧ Γ.img.g.dotted = (Γ.img95.g.relabel (Sum.map eE eI)).dotted ∧ Γ.img.g.coeff = (Γ.img95.g.relabel (Sum.map eE eI)).coeff ∧ (Γ.img95.g.relabel (Sum.map eE eI)).solid = Γ.img.g.solid.map fun e => { e with circ := decide (e.src = e.dst) }
BAAtomic : theorem BAGraph.img95_equiv (Γ : BAGraph E I) (hN : Γ.Normal) : ∃ (eE : Γ.img95.E' ≃ Γ.img.E') (eI : Γ.img95.I' ≃ Γ.img.I'), (∀ a, Γ.img.ext a = eE (Γ.img95.ext a)) ∧ Γ.img.g = Γ.img95.g.relabel (Sum.map eE eI)
BAAtomic2 : theorem liftC_normal (P : PGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) : (liftC P).g.Normal
```
Compiled nonempty instances (`example`s, same files; each theorem above is applied at concrete data with every deterministic hypothesis discharged):
```
$ grep -n "^example" RBM3D/Graph/BAAtomic.lean RBM3D/Graph/BAAtomic2.lean   # line numbers
BAAtomic.lean: 917 922 928 934 940 943 946 953 958 964 967 971 973 976
BAAtomic2.lean: 228 232 237 241 246 252
$ sed -n 922,925p BAAtomic.lean; sed -n 958,961p BAAtomic.lean; sed -n 228,229p BAAtomic2.lean
example : BAAtomic_G0.img.g.counters = BAAtomic_G0.counters ∧ BAAtomic_G0.img.g.lvl1NLoops = BAAtomic_G0.nLoops ∧
    BAAtomic_G0.img.g.lvl1NPairs = BAAtomic_G0.nPairs ∧ Fintype.card BAAtomic_G0.img.E' = BAAtomic_G0.nExt ∧
    (BAAtomic_G0.Normal → BAAtomic_G0.img.g.Normal) ∧ (BAAtomic_G0.Normal → (BAAtomic_G0.LocStd ↔ BAAtomic_G0.img.g.LocStd)) :=
  BAimg_holds BAAtomic_G0
example : ∃ (eE : BAAtomic_G0.img95.E' ≃ BAAtomic_G0.img.E') (eI : BAAtomic_G0.img95.I' ≃ BAAtomic_G0.img.I'),
    (∀ a, BAAtomic_G0.img.ext a = eE (BAAtomic_G0.img95.ext a)) ∧
      BAAtomic_G0.img.g = BAAtomic_G0.img95.g.relabel (Sum.map eE eI) :=
  BAAtomic_G0.img95_equiv BAAtomic_G0_normal
example (k : ℕ) : (BAPGraph.img (liftC p2Graph.pack)).PathInv2 k ↔ p2Graph.pack.PathInv2 k :=
  BAPathLift_holds p2Graph.pack BAAtomic_p2_normal k
```
Data: `G0` (BAAtomic `BAAtomic_G0`: `E = Fin 2`, `I = Fin 3`, four solid edges, one waved, one `M`-dotted edge `M_{αβ}` parallel to the solid edge `α→β` inside the atom `{α,β}`, `x→α` and `γ→y` between atoms, a self-loop); `G1` (locally standard, `nPairs = 1`); `G2` (`G0` with `α→β` uncircled, not normal); the lift `liftC p2Graph.pack` (`E = Fin 2`, `I = Fin 4`).  `decide` checks `nS = 4, nW = 1, nA = 2, nM = 1, nLoops = 2, nExt = 2` at `G0` (example at BAAtomic:917).

### Narrative
**Size.** `BAAtomic.lean` and `BAAtomic2.lean` against the stop line 2,000 per file: the `wc -l` above. The split is the 1a's: file 2 holds `liftG`, `liftC`, `liftC_normal`, `BAPathLift` and the instances at the lift; `(m0)`-`(m2)` stay in file 1.
**(i) The one map.** `BAGraph.img Γ := (promoteC Γ).mergeP` (BAAtomic:108), T2397's order (reasons in (a)); `BAPGraph.img` (:111) is `lvl1Comp` of it and at `E = Fin 2` is T2397's `img` by `rfl` (example :964). T2395's order is `BAGraph.img95` (:726, the probe's construction; its `eq1` graph is the private `BAAtomic_dot95`). `img95_equiv_gen` (:805, every `Γ`): bijections `eE`, `eI` of the vertex types, compatible with `ext`, under which waved edges, `×`-dotted edges and coefficient agree as lists, and the solid list of `img95` is that of `img` with every circle set to "is a loop". `img95_equiv` (:867, `Γ.Normal`): record equality `Γ.img.g = Γ.img95.g.relabel (Sum.map eE eI)`. Equality of the packed graphs is not stated: the vertex types are quotients by two relations that agree only propositionally (T2397 audit D1). At non-normal `G2` the image keeps the uncircled loop while `img95` circles it (example :976).
**(ii) Pin table as finally proved** (graph forms over every `E`, `I`; the pins over `Fin 2` are `fun P => P.g.<graph form>`):

| pin (Lean pin; graph form) | merged lemmas it reduces to (file:line) | new here |
|---|---|---|
| (m1) `BAImgCounters` (:548; `img_counters` :538); `BAimg` conj. 1 | `LGraph.counters` LWVocab:182, `BAGraph.counters` BAVocab:141 (`counters_ofLGraph` BAVocab:533 is not used: it needs no `=`-dots) | `card_intCls` :460 (internal classes = internal atoms, by class counting) and `nM_merge` :520 (via (m2)); `nS`, `nW` by `List.length_map` |
| (m2) `BAImgMol` (:429; `img_molOf_eq_iff` :388) | `LGraph.molOf_eq_iff` LWVocab:576, `LGraph.mem_mol_iff` :551, `BAGraph.mem_mol_iff` BAVocab:394, `atom_subset_mol` :400 | a path of the image lifts to `Γ.adj` steps through atoms and conversely |
| (m0) `BAImgNormal` (:336; `img_normal` :308); `BAimg` conj. 5 | `LGraph.Normal` LWVocab:990, `CircIffLoop` LocalRegular6a:162 | the image lists `BAAtomic_img_solid` :269, `BAAtomic_img_dotted` :282: circle = circled and one atom; `×`-dot iff solid between two atoms |
| `BAimg` conj. 2-4 (`img_nLoops` :569, `img_nPairs` :592, `card_extCls` :482) | `lvl1Loops` LWLvl1:77, `lvl1Share` :80, `lvl1Pairs` :85 | termwise `BAAtomic_share_eq` :577; external classes = external atoms |
| `BAimg` conj. 6 (`img_locStd_iff` :661; pin `BAimg` :702) | `LGraph.LocStd` LWLvl1:3204, `StdNeutral` :3199, `lvl1SolidAt` :1540, `lvl1ChargeAt` :1546 | solid edges and charge at `vmap v` are `atEdges v`, `atCharge v` |
| `BAPathLift` (BAAtomic2:198; `BAPathLift_holds` :201) | `LGraph.localReg2_pathFam_map` LocalRegular2:616 (both directions, `vmap` a bijection), `localReg2_mapMS_comp` :584, `PGraph.PathInv2` :1577 | `BAAtomic_atom_ofL` :59 (atoms are vertices without `=`-dots), `BAAtomic_pathFam_iff` :127 |

**Findings (changes against the starting material).** (1) The T2397 pins read `img P`; here `BAPGraph.img P` (same term at `Fin 2`, example above). (2) `BAGraph.img` is T2397's order, not the T2395 probe-222 definition (target 2 asks for one map); the probe definition is `img95`. (3) The ticket's range "T2395 27-63" contains `BALvl1Good`, `BALvl1GoodLit` (probe 42-55): not copied, as the 1a decided (rows L3a3-L3a5; risk of a name clash with L3a3, per (a)). (4) `Decidable Γ.Normal` and `Decidable Γ.LocStd` are declared here as instances (the T2395 probe declared them too, probe 213-216); a later file that declares them again would duplicate them. (5) `RBM3D.lean` is not edited: the hub adds `import RBM3D.Graph.BAAtomic` and `import RBM3D.Graph.BAAtomic2` at merge (CLAUDE.md §3 (A) step 4); the pre-check above used both imports. (6) No port from `../RBM1D` or `../RBM2D` (none read). Copied and adapted from private lemmas of main `b51fead`: `LWVocab.lean:2225, 2237, 859, 872` (`BAAtomic_vmapC_injective`, `_vmap_surjective`, `_vmap_inl`, `_exists_inr`), `BAVocab.lean:361, 374, 378` (`BAAtomic_rtg_symm`, `_atomAdj_comm`, `_ladj_comm`), T2397 probe 195 (`BAAtomic_atom_ofL`).

## (c) Verified Mathlib/core names used (each compiled; one group per line)
`Setoid.ker_def`, `Quotient.eq`, `Quotient.congr`, `Quotient.exists_rep`; `Relation.ReflTransGen.{single,head,tail,trans,mono}` (`mono` takes `a b` and the path: `mono h u w path`), `Relation.EqvGen.{rel,refl,symm,trans}`;
`SimpleGraph.reachable_iff_reflTransGen`, `SimpleGraph.fromRel_adj`, `SimpleGraph.Adj.reachable`; `Equiv.subtypeEquiv`, `Equiv.ofBijective`, `Equiv.symm_apply_eq`, `Equiv.symm_apply_apply`, `Sum.map_injective`;
`List.countP_map`, `List.countP_congr`, `List.filter_map`, `List.filter_congr`, `List.map_congr_left`, `List.map_map`, `List.map_id`; `Finset.card_image_of_injOn`, `Fintype.card_of_subtype`, `Multiset.map_coe`, `decide_eq_true_iff`, `Bool.eq_iff_iff`, `if_congr`.
Verified absent: `List.map_id_of_mem` (`Unknown constant` in the build log).

## (d) Open issues and paper-delta candidates
- `T2417a`: the one map keeps an uncircled solid edge inside an atom of a non-normal `Γ` uncircled (`promoteC` verbatim), T2395's `img95` circles every loop; they agree on normal graphs (`img95_equiv`) and in everything but the circles otherwise (`img95_equiv_gen`). The pins assume `Normal` where it matters.
- `T2417b`: T2397's (m0)-(m2) and `BAPathLift` are stated over `Fin 2` as in the probe; the graph forms (`BAGraph.img_normal`, `img_counters`, `img_molOf_eq_iff`) hold for every `E`, `I`. Downstream rows may use either.
- No section (a′): no statement of section (a) was wrong. Not done by this ticket (by its scope): (m3) `BABridge`, `BAMolVW`, the `BALvl1Good` pins.
