Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 11:25:15 UTC 2026

Scripts (Python, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2287`; `ba.py` (counters of BA graphs from the definitions of `T2287-check.lean` sec. 2: atoms = classes of `=`, Ψ, M edges; molecules = also waved; `splitG`; merge), `inst.py`, `inst2.py`.

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `ord` (B:353) | `n_S + 2(n_W − n_A)`; Lean `ord` (`ScalingOrder.lean:65`) is `nS + 2(nW − nV)`, slot `nV := nA` in `BAGraph.counters` | identity, no inequality | exact |
| 2 | `size` (B:349-350) | `(L^d)^{n_M} Ψ^{n_S} W^{-d(n_W−n_A)}`; `Counters.scalingSize` (`LWVocab.lean:1619`) is the same with `nV := nA` | identity | exact |
| 3 | `scalingSize_eq` | `size = (L^d)^{nM} Ψ^{ord} (W^d Ψ²)^{nA−nW}` | `Ψ ≠ 0` only (`Counters.scalingSize_eq`, `:1623`); no relation among `L, W, d` | `Ψ = 1/2, W = 4, d = 3, L = 8`: both sides equal (rows below) |
| 4 | closure length `Fintype.card (E ⊕ I)` for `atom`, `mol` | each step before the fixed point adds ≥ 1 vertex, so ≤ `n − 1` steps are needed | `n ≥ 1` (any `v` exists) | 1 step |
| 5 | `nA ≤ card I` | each internal atom contains an internal vertex, atoms are disjoint | none | tight at `baGGLhs` (`nA = 1 = card I`) |
| 6 | `nM ≤ nA` | an internal molecule is a union of atoms (atoms ⊆ molecules, V3), so it contains an internal atom | none | tight at `baGGLhs` (`nM = nA = 1`); strict at `lem_lweight` t1 M⁺S⁺ (`nM = 1 < nA = 3`) |
| 7 | `splitG` length | `2^k`, `k` = number of solid edges without circle | none | `k = 3` gives 8 terms (g1 below) |
| 8 | `splitG_edges` | `Δ.nW = Γ.nW`, `Δ.dotted = Γ.dotted`, `Δ.psi = Γ.psi`, `Δ.nS + |Δ.mdot| = Γ.nS + |Γ.mdot|` | equality | 0 (g1: 4 = 4 on all 8 terms) |
| 9 | `ord` of a term vs `Γ` | `nS` falls by the number `j` of `M` edges added, `nA` falls by 0..j: `ord(Δ) − ord(Γ) = −j + 2(nA(Γ) − nA(Δ))` | none (def. of `ord`) | sign not fixed: `G_{xx}` (x internal) raw `−1`, partition `−2` (row below); `lanlw` t1 raw 2, partition 1 |
| 10 | `scalingOrderG` / `scalingSizeG` | min over partition (`⊤` if empty) / max (`0` if empty) | `B:354-355` | no `D` hypothesis anywhere (G = (G−M)+M literal in `SEdge.val`, `LWVocab.lean:115`) |
| 11 | D402 coefficient (I2) | `M⁺_{xu}S⁺_{uβ} = M_{xu}M_{ux}S⁺_{uβ}` (`docs/paper-deltas.md:1361`) | counters `⟨0,1,1,0⟩`, ord 0 | exact (row `sum1`) |
| 12 | external hypotheses | none; the only hypotheses of the 18 targets: `Ψ ≠ 0` (#3), "no `=`-dotted edge" (`counters_ofLGraph`, `scalingOrder_ofLGraph`), `Γ.Normal` (`partition_of_normal`, `scalingOrderG_of_normal`) | no limit computation needed | — |
| 13 | §29 | no `s, t`, gate, `L`–`W` relation, `∀ n`, probability, `g` hypothesis (`gPsi` is free data), constant | — | — |

Paper-implicit points (checked against `B:286-356`, `7_8:116-175`): (V2) "regular dotted" in `def_atom` (B:303) and `defn_normalBA` (ii) (B:334) is `=`-dotted: B:312 discards `×`-dotted edges in the atomic graph, and `7_8:141` gives `×` the factor `1_{x≠y}`, so joining `x, y` into one atom would contradict it (candidate T2287a). (V3) B:298-300 say molecules "remain the same" while atoms "form mesoscopic structures within each molecule"; atoms ⊆ molecules forces Ψ- and M-edges to join molecules (candidate T2287b). The paper's `n_A` of the partition terms counts the new `M` edges of `G = Ǧ + M` (B:342 and B:352: "internal atoms of a normal graph").

### (ii) Concrete nondegenerate instance (all numbers; `ι = Fin 2`, `Ψ = 1/2`, `W = 4`, `d = 3`, `L = 8`)

Command: `cd $S && python3 ba.py` (output verbatim, 19 lines; columns = counters from the definitions, `ordG` = min over `split` + `merge`):
    p2Graph                            nS=6 nW=2 nA=4 nM=2 ord=2 ordG=2 nterms=16
    p2Graph with 2-vertex atoms nS,nW,nA,nM = (6, 2, 4, 2) ord 2
    figGraph raw: counters (8, 4, 6, 2) ord 4
    --- GGGamma (y'=e0,y=e1; x internal)
    LHS G_{y'x}G_{xy} (circ)           nS=2 nW=0 nA=1 nM=1 ord=0 ordG=0 nterms=1
    sum1 M+_{xu}S+_{ub}M_{by}M_{y'b}   nS=0 nW=1 nA=1 nM=0 ord=0 ordG=0 nterms=1
    sum2 M+S+ Ǧ_{by}M_{y'b}            nS=1 nW=1 nA=1 nM=0 ord=1 ordG=1 nterms=1
    sum3 t1 delta: M_{xa}S_{ab}Ǧ_bb G_{ay}Ǧ_{y'x} nS=3 nW=1 nA=2 nM=1 ord=1 ordG=1 nterms=2
    sum3 t1 M+S+: M+_{xu}S+_{uw}M_{wa}S_{ab}Ǧ_bb G_{ay}Ǧ_{y'w} nS=3 nW=2 nA=3 nM=1 ord=1 ordG=1 nterms=2
    --- lem_lweight (x internal)
    LHS Ǧ_xx                           nS=1 nW=0 nA=1 nM=1 ord=-1 ordG=-1 nterms=1
    t1 delta: M_{xa}S_{ab}Ǧ_{ax}Ǧ_{bb} nS=2 nW=1 nA=2 nM=1 ord=0 ordG=0 nterms=1
    t1 M+S+: M+_{xu}S+_{uy}M_{ya}S_{ab}Ǧ_{ay}Ǧ_bb nS=2 nW=2 nA=3 nM=1 ord=0 ordG=0 nterms=1
    --- lanlw (x,y external)
    LHS Ǧ_xy                           nS=1 nW=0 nA=0 nM=0 ord=1 ordG=1 nterms=1
    t1 M_{xa}S_{ab}Ǧ_bb G_{ay}         nS=2 nW=1 nA=1 nM=0 ord=2 ordG=1 nterms=2
    --- one G edge
    G_{ax}                             nS=1 nW=0 nA=1 nM=1 ord=-1 ordG=-1 nterms=2
    G_{xx} weight, x internal          nS=1 nW=0 nA=1 nM=1 ord=-1 ordG=-2 nterms=2

Matches: (I1) `baGGLhs` `⟨2,0,1,1⟩` ord 0; (I2) `baGGT1` = row `sum1` `⟨0,1,1,0⟩` ord 0; (I3) `baLWT1` = row `t1 delta` `⟨2,1,2,1⟩` ord 0; (I4) `G_{ax}`: ord −1, 2 terms, partition orders `−1` (Ǧ) and `0` (M), min `−1`; (I5) `p2Graph` ord 2 (6,2,4,2), `figGraph` ord 4 (8,4,6,2), both with only `×`-dotted edges so the `=`-free hypothesis holds. Every number of the ticket's dispatcher table reproduces (including `lanlw` t1: raw 2, partition 1).

Command: `cd $S && python3 inst.py | tail -n +20` (value identity `Γ.val = Σ partition` at free random Gaussian-integer data `G, M, S, S⁺, gPsi` on `Fin 2`, no `M_{xx} = m`, no symmetry; `g1` has a `=` edge int–ext, a `×` edge, Ψ-, M-, waved, red/blue, a non-circled weight; `g2` has a `=` edge between the two external vertices, so 2 of 4 labellings give 0 on both sides):
    g1 (= int-ext, x edge, psi, M, red+blue, weight, non-circ): E=2 I=2 nonzero lhs for 4/4 labellings; terms=8; max|val-partition|=0
    g2 (= edge between the two external vertices): E=2 I=1 nonzero lhs for 2/4 labellings; terms=2; max|val-partition|=0
    g1 raw (nS,nW,nA,nM)= (3, 1, 0, 0) ord= 5
    g1 partition counters (nS,nW,nA,nM) and ord: [((3, 1, 0, 0), 5), ((2, 1, 0, 0), 4), ((2, 1, 0, 0), 4), ((1, 1, 0, 0), 3), ((2, 1, 0, 0), 4), ((1, 1, 0, 0), 3), ((1, 1, 0, 0), 3), ((0, 1, 0, 0), 2)]
    g1 splitG: len= 8 ; 2^#noncirc = 8 ; nS+|mdot| over terms: {4} ; Gamma: 4
    g1 counters (3, 1, 0, 0) size = 1/512 identity RHS = 1/512 equal: True
    baGGLhs counters (2, 0, 1, 1) size = 8192 identity RHS = 8192 equal: True
    lanlw t1 counters (2, 1, 1, 0) size = 1/4 identity RHS = 1/4 equal: True
    random graphs violating nM<=nA<=card I: 0 of 3000

Command: `cd $S && python3 inst2.py` (g3: `=` between internal vertices, an M edge, a non-circled weight; then 2844 random normal graphs, 2884 random graphs with `=` edges):
    g3 raw (nS,nW,nA,nM),ord: (3, 1, 2, 1) 1
    g3 terms (nS,nW,nA,nM),ord: [((3, 1, 2, 1), 1), ((2, 1, 2, 1), 0), ((2, 1, 1, 0), 2), ((1, 1, 1, 0), 1)]
    normal random graphs: 2844 ; counters(merge)!=counters or |splitG|!=1: 0
    graphs with '=' edges: 2884 ; counters(merge g)!=counters(g): 0

Reading: all hypotheses of all 18 targets hold at the instances (`Ψ = 1/2 ≠ 0`; `p2Graph`, `figGraph` `=`-free; `baGedge`-terms and `baGGLhs`, `baGGT1`, `baLWT1` normal: no `=` edge, all solid edges circled, e.g. the `Ǧ`-term of `G_{ax}`); no `N = 0`, empty index, or collapsed window (`card ι = 2`, `card E ≤ 2`, `card I ≤ 4`, nonzero values). The only non-instance caveat: `val_eq_partition` is checked numerically here, not as a Lean `example`; that is stage 1b's (I6).

### Verdict per target

- Vocabulary (target 1, the declarations of check sec. 2) and the 18 theorems (value, atoms/molecules, scaling/bridge, `G = Ǧ + M`, partition): **PASS** (every statement is true at the instances above and in the 3000-graph checks; no hypothesis set is unsatisfiable; exponents close with the slacks of table rows 1-10).
- Preflight (ii) paper agreement (`ord`, `size`, partition terms normal in the sense of B:333-341: no `=` edge, all circled; atoms as B:302-304): **PASS** (with T2287a, T2287b).
- Preflight (iv): **PASS** (`val_splitG`, `val_eq_partition` use no hypothesis on the data; g1, g2 above).
- Preflight (v), consumer use: **PASS with one note for 1b/BA-L2.** `splitG_edges` fixes `nW`, `dotted`, `psi` and `nS + |mdot|` but not `nA`, `nM` of a term, so by itself it does not give the order of a term. The order of a term of a `=`-free `Γ` comes from `splitG_circ` + `splitG_edges` (`Δ.dotted = Γ.dotted`, so `Δ` is normal), then `partition_of_normal` (counters of the merged term = counters of `Δ`; on a circled list `baSplitSolid` returns the single pair `(solid, [])`, so `Δ.partition = [packMerge Δ]`), then `le_scalingOrderG_iff`. All 18 pinned theorems suffice; no extra public theorem is needed.
- Observation (not a defect): `ordG` can be below raw `ord` (`G_{xx}`: −2 vs −1; `lanlw` t1: 1 vs 2), as in the merged `LGraph.partition` (weights are split); BA-L2 must state term orders with `scalingOrderG` or term counters.

## (b) Script output — stage 1b, prover claude-sonnet-5-5, worktree RBM3D-wt/T2287, branch t/T2287, commit d3964d5 (Tue Oct 6 04:42:40 2026 -0700)

Stage 1b report section written at Tue Oct  6 11:43:17 UTC 2026.

### Build
    $ lake build RBM3D.Graph.BAVocab   (worktree)
    Build completed successfully (2063 jobs).
    exit 0
    $ lake build   (full library, worktree; BAVocab not yet imported by RBM3D.lean, the hub adds it at merge)
    Build completed successfully (4094 jobs).
    lake build  1.50s user 3.53s system 242% cpu 2.074 total
    $ lake env lean reg.lean   (registry pre-check; reg.lean = `import RBM3D`, `import RBM3D.Graph.BAVocab`, `#assert_rbm_axioms`; temp file in the scratchpad, not in the worktree; exit 0)
    axiom audit: 8302 theorems, 2761 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
    All within [propext,
     Classical.choice,
    ...
     RBM.Gauss.Sizes.STOeqNQ'].
    non-vacuity certificates: 0 of 147 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
    (same check without BAVocab: "axiom audit: 8236 theorems, 2681 definitions, 0 axioms"; with BAVocab: 8302 / 2761 / 0)

### Axioms of the 18 public theorems and of the 19 instance theorems (`#print axioms`, scratch file importing the module)
    $ lake env lean ax.lean | grep -c "depends on axioms: [propext, Classical.choice, Quot.sound]"
    37 of 37 lines
    'RBM.Graph.BAGraph.val_ofLGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.term_addM' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.mem_atom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.mem_mol_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.atom_subset_mol' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.nA_le_card' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.nM_le_nA' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.counters_ofLGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.scalingOrder_ofLGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.scalingSize_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.val_splitG' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.splitG_circ' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.splitG_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.val_eq_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.partition_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.partition_of_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.le_scalingOrderG_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Graph.BAGraph.scalingOrderG_of_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
    $ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/BAVocab.lean | wc -l
    0

### Check-file equality
    $ python3 eqcheck.py   (check section 2 vs the file block between `namespace RBM.Graph` and `/-! ## 3.`, whitespace-normalized, the `attribute [instance]` line ignored)
    check block chars 10075 file block chars 10075
    EQUAL
    $ python3 stmt.py && lake env lean stmt_check.lean   (18 `example : <body of T2287_<name>> := @BAGraph.<name>`)
    18 theorems
    lake env lean exit 0

### Targets (statements extracted from the file by script, `extract.py`)
    theorem BAGraph.val_ofLGraph {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : RBM.Graph.LGraph E I) (D : BALData ι) (ℓe : E → ι) : (BAGraph.ofLGraph Γ).val D ℓe = Γ.val D.toLData ℓe
    theorem BAGraph.term_addM {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (e : BAMEdge (E ⊕ I)) (D : BALData ι) (ℓ : E ⊕ I → ι) : (Γ.addM e).term D ℓ = Γ.term D ℓ * e.val D ℓ
    theorem BAGraph.mem_atom_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (v w : E ⊕ I) : w ∈ Γ.atom v ↔ Relation.ReflTransGen (fun a b => Γ.atomAdj a b = true) v w
    theorem BAGraph.mem_mol_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (v w : E ⊕ I) : w ∈ Γ.mol v ↔ Relation.ReflTransGen (fun a b => Γ.adj a b = true) v w
    theorem BAGraph.atom_subset_mol {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (v : E ⊕ I) : Γ.atom v ⊆ Γ.mol v
    theorem BAGraph.nA_le_card {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) : Γ.nA ≤ Fintype.card I
    theorem BAGraph.nM_le_nA {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) : Γ.nM ≤ Γ.nA
    theorem BAGraph.counters_ofLGraph {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : RBM.Graph.LGraph E I) : (∀ e ∈ Γ.dotted, e.eq = false) → (BAGraph.ofLGraph Γ).counters = Γ.counters
    theorem BAGraph.scalingOrder_ofLGraph {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : RBM.Graph.LGraph E I) : (∀ e ∈ Γ.dotted, e.eq = false) → (BAGraph.ofLGraph Γ).scalingOrder = Γ.scalingOrder
    theorem BAGraph.scalingSize_eq {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) {Ψ : ℝ} (W d L : ℕ) (hΨ : Ψ ≠ 0) : Γ.scalingSize Ψ W d L = ((L : ℝ) ^ d) ^ Γ.nM * Ψ ^ Γ.scalingOrder * ((W : ℝ) ^ d * Ψ ^ 2) ^ ((Γ.nA : ℤ) - Γ.nW)
    theorem BAGraph.val_splitG {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι) : (Γ.splitG.map fun Δ => Δ.val D ℓe).sum = Γ.val D ℓe
    theorem BAGraph.splitG_circ {E I : Type} (Γ : BAGraph E I) : ∀ Δ ∈ Γ.splitG, ∀ e ∈ Δ.solid, e.circ = true
    theorem BAGraph.splitG_edges {E I : Type} (Γ : BAGraph E I) : ∀ Δ ∈ Γ.splitG, Δ.nW = Γ.nW ∧ Δ.dotted = Γ.dotted ∧ Δ.psi = Γ.psi ∧ Δ.nS + Δ.mdot.length = Γ.nS + Γ.mdot.length
    theorem BAGraph.val_eq_partition {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι) : Γ.val D ℓe = BAComb.val Γ.partition D ℓe
    theorem BAGraph.partition_normal {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) : ∀ P ∈ Γ.partition, P.g.Normal
    theorem BAGraph.partition_of_normal {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) : Γ.Normal → ∃ P : BAPGraph E, Γ.partition = [P] ∧ P.counters = Γ.counters
    theorem BAGraph.le_scalingOrderG_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (k : ℤ) : ((k : ℤ) : WithTop ℤ) ≤ Γ.scalingOrderG ↔ ∀ P ∈ Γ.partition, k ≤ P.scalingOrder
    theorem BAGraph.scalingOrderG_of_normal {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) : Γ.Normal → Γ.scalingOrderG = ((Γ.scalingOrder : ℤ) : WithTop ℤ)

### Compiled nonempty instances (namespace `RBM.Graph.BAVocabInst`, `inst_extract.py`; all compile in the build above)
    theorem baGGLhs_counters : baGGLhs.counters = ⟨2, 0, 1, 1, 0, 0⟩
    theorem baGGLhs_ord : baGGLhs.scalingOrder = 0
    theorem baGGT1_counters : baGGT1.counters = ⟨0, 1, 1, 0, 0, 0⟩
    theorem baGGT1_ord : baGGT1.scalingOrder = 0
    theorem baLWT1_counters : baLWT1.counters = ⟨2, 1, 2, 1, 0, 0⟩
    theorem baLWT1_ord : baLWT1.scalingOrder = 0
    theorem baGedge_ord : baGedge.scalingOrder = -1
    theorem baGedge_splitG_length : baGedge.splitG.length = 2
    theorem baGedge_not_normal : ¬ baGedge.Normal
    theorem baGedge_splitG_circ : ∀ Δ ∈ baGedge.splitG, ∀ e ∈ Δ.solid, e.circ = true
    theorem p2Graph_ba_ord : (BAGraph.ofLGraph p2Graph).scalingOrder = 2
    theorem figGraph_ba_ord : (BAGraph.ofLGraph figGraph).scalingOrder = 4
    theorem baGedge_splitG : baGedge.splitG = [baGedge1, baGedge2]
    theorem baGedge1_normal : baGedge1.Normal
    theorem baGedge2_normal : baGedge2.Normal
    theorem baGedge_ordG : baGedge.scalingOrderG = (((-1 : ℤ)) : WithTop ℤ)
    private theorem BAVocab_val_fin_one {ι E : Type} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E (Fin 1)) (D : BALData ι) (ℓe : E → ι) : Γ.val D ℓe = ∑ x : ι, Γ.term D (Sum.elim ℓe fun _ => x)
    theorem baGedge_val : baGedge.val baD (fun _ => 0) = 3
    theorem baGedge1_val : baGedge1.val baD (fun _ => 0) = -8
    theorem baGedge2_val : baGedge2.val baD (fun _ => 0) = 11
    theorem baGGLhs_size : baGGLhs.scalingSize (1 / 2) 4 3 8 = 8192
    theorem baGedge_split_sum : (baGedge.splitG.map fun Δ => Δ.val baD (fun _ => 0)).sum = 3
    theorem baGedge_partition_val : BAComb.val baGedge.partition baD (fun _ => 0) = 3
    example : (Sum.inr 2 : Fin 2 ⊕ Fin 3) ∈ baGGT1.atom (.inl 0)
    example : (Sum.inr 1 : Fin 2 ⊕ Fin 3) ∈ baGGT1.mol (.inl 0)
    example : (Sum.inr 1 : Fin 2 ⊕ Fin 3) ∉ baGGT1.atom (.inl 0)
    example : baGGT1.nA ≤ Fintype.card (Fin 3)
    example : baGGT1.nM ≤ baGGT1.nA
    $ grep -n "^example" RBM3D/Graph/BAVocab.lean   (one application of each of the 18 theorems at the graphs above, `ι = Fin 2`, data `baD`)
    1376:example := BAGraph.val_ofLGraph p2Graph baD ![0, 1]
    1378:example := BAGraph.term_addM baGedge ⟨true, .inl 0, .inr 0⟩ baD (fun _ => 0)
    1381:example : (Sum.inr 2 : Fin 2 ⊕ Fin 3) ∈ baGGT1.atom (.inl 0) :=
    1386:example : (Sum.inr 1 : Fin 2 ⊕ Fin 3) ∈ baGGT1.mol (.inl 0) :=
    1390:example : (Sum.inr 1 : Fin 2 ⊕ Fin 3) ∉ baGGT1.atom (.inl 0) := by decide
    1392:example := BAGraph.atom_subset_mol baGGT1 (.inl 0)
    1394:example : baGGT1.nA ≤ Fintype.card (Fin 3) := BAGraph.nA_le_card baGGT1
    1396:example : baGGT1.nM ≤ baGGT1.nA := BAGraph.nM_le_nA baGGT1
    1398:example := BAGraph.counters_ofLGraph p2Graph (by decide)
    1400:example := BAGraph.scalingOrder_ofLGraph figGraph (by decide)
    1402:example := BAGraph.scalingSize_eq baGGLhs (Ψ := 1 / 2) 4 3 8 (by norm_num)
    1404:example := BAGraph.val_splitG baGedge baD (fun _ => 0)
    1406:example := BAGraph.splitG_circ baGedge
    1408:example := BAGraph.splitG_edges baGedge
    1410:example := BAGraph.val_eq_partition baGedge baD (fun _ => 0)
    1413:example := BAGraph.val_eq_partition baEqGraph baD (fun _ => 0)
    1415:example := BAGraph.partition_normal baEqGraph
    1417:example := BAGraph.partition_of_normal baGGLhs ⟨by decide, by decide⟩
    1419:example := BAGraph.le_scalingOrderG_iff baGedge (-1)
    1421:example := BAGraph.scalingOrderG_of_normal baGGT1 ⟨by decide, by decide⟩

### Name-clash grep (`clash.sh`: grep -rn --include=*.lean <name> RBM3D, minus the new file)
    BALData: 0 hits outside RBM3D/Graph/BAVocab.lean
    BAPsiEdge: 0 hits outside RBM3D/Graph/BAVocab.lean
    BAMEdge: 0 hits outside RBM3D/Graph/BAVocab.lean
    BAGraph: 0 hits outside RBM3D/Graph/BAVocab.lean
    BAPGraph: 0 hits outside RBM3D/Graph/BAVocab.lean
    BAComb: 0 hits outside RBM3D/Graph/BAVocab.lean
    baSplitSolid: 0 hits outside RBM3D/Graph/BAVocab.lean
    BAVocabInst: 0 hits outside RBM3D/Graph/BAVocab.lean
    baGGLhs: 0 hits outside RBM3D/Graph/BAVocab.lean
    baGGT1: 0 hits outside RBM3D/Graph/BAVocab.lean
    baLWT1: 0 hits outside RBM3D/Graph/BAVocab.lean
    baGedge: 0 hits outside RBM3D/Graph/BAVocab.lean
    baEqGraph: 0 hits outside RBM3D/Graph/BAVocab.lean
    baGedge1: 0 hits outside RBM3D/Graph/BAVocab.lean
    baGedge2: 0 hits outside RBM3D/Graph/BAVocab.lean
    baD: 0 hits outside RBM3D/Graph/BAVocab.lean
    p2Graph_ba_ord: 0 hits outside RBM3D/Graph/BAVocab.lean
    figGraph_ba_ord: 0 hits outside RBM3D/Graph/BAVocab.lean
    BAVocab_: 0 hits outside RBM3D/Graph/BAVocab.lean
    (`val_fin_one` was grepped as the substring of the private helper `BAVocab_val_fin_one`; its 2 hits are `Matrix.cons_val_fin_one` in Induction/Step6Kit.lean:321 and Induction/Step2Events.lean:1288, unrelated.)

### Diff and ports
    $ git diff --stat main...t/T2287
     RBM3D/Graph/BAVocab.lean | 1424 ++++++++++++++++++++++++++++++++++++++++++++++
     1 file changed, 1424 insertions(+)
    No port. `git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks grep -il "BAVocab\|scalingBA\|BAGraph" -- "*.lean"` (HEAD 9e0f275) and the same in /Users/junyin/Lean_proof/RBM1D (HEAD de0de42): no output, exit 1 in both. The proofs are adapted from the merged `RBM3D/Graph/LWVocab.lean` (37db678), private copies prefixed `BAVocab_`: closures `:491-570`, merge `:771-957`, partition value `:1339-1351`, `le_scalingOrderG_iff` `:1685`, relabel/normal case `:2075-2329`.

### Narrative
- Result: the vocabulary of check section 2 (copied verbatim; the equality script above prints EQUAL, the `attribute [instance]` line for `BAPGraph` added at `BAVocab.lean:243`) and all 18 targets are proved, with no hypothesis added and no signature changed. The file has 1424 lines, below the ticket's 1500-line stop, so the cut T2287a/T2287b was not needed.
- The only hypotheses of the 18 theorems are those of the pins: `Ψ ≠ 0` (`scalingSize_eq`), "no `=`-dotted edge" (`counters_ofLGraph`, `scalingOrder_ofLGraph`), `Γ.Normal` (`partition_of_normal`, `scalingOrderG_of_normal`). `val_splitG` and `val_eq_partition` hold for every `BALData`: `G = (G - M) + M` is literal in `SEdge.val`.
- Atoms and molecules: `mem_atom_iff`, `mem_mol_iff` follow from one private lemma `BAVocab_mem_iterate_iff` (closure of `{v}` after `card α` steps of a symmetric Boolean relation is the reflexive-transitive closure), by the route of `LGraph.mem_mol_iff` (`LWVocab.lean:491-570`, path length `< card`) stated for `ReflTransGen`. `nA_le_card`, `nM_le_nA` use `atom_subset_mol` and that atoms (molecules) are equivalence classes.
- `val_splitG`: induction on the solid list (`BAVocab_split_val`), then the sum over internal labels commutes with the list sum (`BAVocab_sum_comm`).
- `val_eq_partition`: a BA twin of `LGraph.val_eq_merge_val` / `mergeP_val` (`LWVocab.lean:881-957`). The `Ψ`- and `M`-factors are read through `vmap` (`BAVocab_term_merge`); the private `LGraph` lemmas it needs (`term_merge`, `term_eq_zero_of_not_good`, `Good.eq_of_cls`, the `vmap_inl/inr` facts) are re-proved with prefix `BAVocab_` because they are `private` in `LWVocab.lean` (no merged file changed).
- `partition_of_normal`: with no `=`-dotted edge `vmap` is a bijection keeping external and internal vertices apart; atoms and molecules of the merge are the images (`BAVocab_merge_atomAdj`, `BAVocab_merge_adj`, `BAVocab_iterate_equiv`, `BAVocab_cnt_equiv`, the BA twin of `counters_relabel_equiv` `:2114`), so the counters agree (`BAVocab_merge_counters`). The BA normal graph has no `×`-iff-solid clause, hence no `DotWF` hypothesis.
- Instances: (I1)-(I6) as listed in the ticket, plus `baEqGraph` (a `=`-dotted edge between the external `a` and the internal `x`, a `Ψ`-dotted edge and a weight), at which `val_eq_partition` and `partition_normal` are applied, and `baGGLhs_size = 8192` at `Ψ = 1/2, W = 4, d = 3, L = 8`. (I6) is evaluated at the data `baD` (integer entries, `M` not a multiple of the identity): `val(G_{ax}) = 3`, the terms `Ǧ_{ax}`, `M_{ax}` give `-8` and `11`, and `scalingOrderG(G_{ax}) = -1` through the counters of the two terms (`ord = -1` and `0`).
- Section (a) needed no correction (no (a′)); the counters of (I1)-(I5) and (I6) agree with its table (instance theorems above compile).
- Registry: `reg.out` contains no line about `BAVocab`, `BAGraph` or `BALData` (grep count 0); `RBM3D/Test/Axioms.lean` is not touched. The file defines no `def … : Prop` other than `BAGraph.Normal`.

## (c) Verified Mathlib names (used in the compiled file; each checked by grep in the file and by the build)
- `Relation.ReflTransGen` with `.refl`, `.single`, `.tail`, `.head`; `Relation.ReflTransGen.mono` has the form `r ≤ p → ReflTransGen r ≤ ReflTransGen p` (`Mathlib/Logic/Relation.lean:757`), applied as `mono h a b hab`.
- `Relation.ReflTransGen.symmetric` is deprecated (alias of `stdSymm`, `Relation.lean:513`, deprecated 2026-06-10) and takes `Std.Symm`; not used (own lemma `BAVocab_rtg_symm`).
- `SimpleGraph.fromRel_adj`, `SimpleGraph.reachable_iff_reflTransGen`, `SimpleGraph.Walk.length_cons`, `SimpleGraph.Reachable.exists_isPath`, `SimpleGraph.Walk.IsPath.length_lt` (Paths.lean:431, via `hp.length_lt`).
- `Finset.card_image_le`, `Finset.card_le_card`, `Finset.card_image_of_injective`, `Finset.singleton_injective`, `Finset.map_injective`, `Finset.mem_map_equiv`, `Finset.sum_image`, `Finset.sum_subset`, `Finset.sum_add_distrib`.
- `List.map_flatMap`, `List.flatMap_cons`, `List.sum_append`, `List.sum_map_mul_left`, `List.map_congr_left`, `List.any_map`, `List.any_cons`, `List.any_eq_true`, `List.prod_eq_zero`.
- `Equiv.funUnique`, `Equiv.ofBijective`, `Fintype.sum_equiv`, `Function.iterate_succ_apply`, `Function.iterate_succ_apply'`, `Function.iterate_add_apply`, `Sum.inr_injective`, `WithTop.coe_le_coe`, `min_top_right`, `min_eq_left`, `star_sub`, `Quotient.exists_rep`.
- Merged RBM3D names used: `LGraph.vmap`, `vmapC`, `extMap`, `extMap_surj`, `cls`, `EqRel`, `Good`, `ExtCls`, `IntCls` (the `Fintype`/`DecidableEq` instances of `LWVocab.lean:749-760`), `Counters.scalingSize_eq`, `ord`, `p2Graph_ord`, `figGraph_ord`, `LGraph.adj`, `LGraph.step`, `LGraph.mol`, `LGraph.nM`.
- Verified absent / not usable: `LGraph.adj_iff`, `LGraph.term_merge` and the other `vmap` lemmas are `private` in `LWVocab.lean` (not accessible; re-proved with prefix `BAVocab_`).

## (d) Open issues and paper-delta candidates
- **T2287a** (delta candidate): "regular dotted" in `def_atom` (`B:303`) and `defn_normalBA` (ii) (`B:334`) is read as `=`-dotted; `×`-dotted edges do not join atoms (`BAGraph.atomAdj`, `BAGraph.Normal`).
- **T2287b** (delta candidate): `Ψ`- and `M`-dotted edges join molecules (`BAGraph.adj`; `B:298-300`, atoms lie inside molecules, `atom_subset_mol`).
- Note for BA-L2 (statement-level, from the instances): the raw `scalingOrder` can differ from `scalingOrderG` on a non-normal graph; `splitG_edges` fixes `nW`, `dotted`, `psi` and `nS + |mdot|` but not `nA`, `nM` of a term, so the order of a term needs `partition_of_normal` (counters of the merge) or the counters of the term itself, then `le_scalingOrderG_iff`.
- D402 (`docs/paper-deltas.md:1361`) is used only in the instance `baGGT1` (I2), as in the ticket; the identity is BA-L2's.
- Open: none for the 18 targets; no other-gate pin is a hypothesis of any theorem or example here.
