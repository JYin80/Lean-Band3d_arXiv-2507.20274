Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 16:48:17 UTC 2026

Notation: `Γ_p` = `fxyPowGraph p`, `p = 2k`; `x = Q.ext 0`, `y = Q.ext 1`; `M_x, M_y` their molecules; `H(Q)` = multigraph on the molecules whose edge occurrences are the solid-edge positions of `Q.g` (an edge joins the molecules of its ends; ends in one molecule = loop). Files cited are in `RBM3D/Graph/`. No Lean is written here (rule of stage 1a): the Lean encoding of the predicates is stage 1b's, from the mathematical forms below.

### (i) Exponent table

| row | value | constraint / source | slack |
|---|---|---|---|
| `n_S, n_W, n_V, n_M` of `Γ_p` | `3p, p, 2p, p` (script: (6,2,4,2) at p=2, (12,4,8,4) at p=4) | `B:201`; blocks `[Ǧ_{β_iβ_i}, G_{xα_i}, G_{α_i y}]`, waved `S_{α_iβ_i}`, `×`-dotted `(α_i,x),(α_i,y)` | equalities, 0 |
| `ord Γ_p` | `3p + 2(p-2p) = p` (`ScalingOrder.lean:65`) | `(eq:initial_scaling)`; `lvl1_lemma_size` gives `ord Q ≥ ord Γ_p = p` only | 0; item (6) `ord ≥ 2p` needs `+p` more: LW-10b, not here |
| vertex layout | `α_i = inr(2i)`, `β_i = inr(2i+1)`, blue iff `i < p/2` | `p2Graph` (`LWVocab:191`) | `Γ_2 = p2Graph` as lists, same vertex order (script line 1): exact, not only up to order |
| value identity | `Γ_p.val D ![x,y] = f^{p/2} · conj(f)^{p/2}`, `f = fxyVal D x y`, `S` real | factorises over `i` (sum over `(α_i,β_i)` separately); red block = `conj` of blue block since `S = conj S` | numeric check, error `≤ 7e-17` (p=2,4) |
| `Γ_p` normal | `×`-dotted pairs `= {x,α_i},{α_i,y}` = non-loop solid pairs; the only loops are circled | `defnlvl0` (`LWVocab:990`) | 0 |
| `lvl1_lemma_size` data | `c = 1/4, K0 = 1, d = 3, D = 10`; `K(p) = ⌈(D+(K0+d)p)/c⌉` = 72 (p=2), 104 (p=4) | `lvl1Cutoff` (`LWLvl1:3981`); p=2 equals `lvl1_inst_cutoff` | `c>0`: 1/4 |
| regime (size part) | `W=27, L=3, Ψ=27^{-1/4}` | `L^d ≤ W^{K0}`: `27 ≤ 27`; `W^{-d/2} ≤ Ψ ≤ W^{-c}`: `0.0071 ≤ 0.4387 ≤ 0.4387` | 0; ratio 61.5; 0 (by choice, as `lvl1_inst_lemma_size`) |
| identity data | `E=0`, `m = mE 0 = i`, `t=1/2`, `z = zt 0 (1/2) = i/2`, `u = 1/2`, `d=3,L=3,W=1` (`lwWxInstSz`) | `Im z>0`, `u>0`, `m≠0`, `z+um = -m⁻¹`; the rest is the merged `lwWx_inst_*` | `Im z = 1/2`, `u = 1/2`; `z+um = i = -1/m` exactly |
| (1) | `Q.g.LocStd` (`LWLvl1:3204`) | `lvl1_lemma_size`, first conjunct of `outs` | 0 |
| (2) counts | `#internal molecules ≤ n_M(Γ_p) = p`; for every molecule `C` of a normal graph: `#{v : v∈C} ≤ #{waved e inside C} + 1` (all vertices of `C`, external included; it implies the internal-only count) | first: `Q.g.nM ≤ Γ.g.nM` of `lvl1_lemma_size`; second: spanning tree of the waved graph, a normal graph has no `=`-dotted edge (`defnlvl0`(ii)) | `Γ_p`: `{α_i,β_i}`: `2 ≤ 1+1`, `{x}`: `1 ≤ 0+1`: 0 |
| (3) walks | `p` walks `W_1..W_p` in `H(Q)` from `M_x` to `M_y`, pairwise edge-occurrence-disjoint, closed if `M_x = M_y` | `7_8:801-803`; walks, not simple paths (the paper's own proof replaces an edge by a 2-edge walk) | `Γ_p`: `W_i = (G_{xα_i}, G_{α_i y})`, uses `2p` of `3p` edges; slack `p` (the loops) |
| (4) | (3) and every internal molecule on `≥ 2` different walks | `7_8:805-807` | LW-10b |
| (5) Hall | (3) and for every set `A` of internal molecules `#{i : W_i visits A} ≥ |A|` | `7_8:809-813`; one common family for (3),(5) | `Γ_p`: equality for every `A` (`W_i` visits exactly `M_i = {α_i,β_i}`), 0 |
| (6) | `ord Q ≥ 2p` | `7_8:815-818` | LW-10b |
| far assumption | decision: (3),(5) and the invariant are stated **without** `(eq:far_ab)` (`M_x ≠ M_y` is not assumed; walks are closed when `M_x = M_y`); the version with `M_x ≠ M_y` is a corollary | script: `M_x = M_y` occurs at 16434 + 2457 + 10336 outputs and the invariant still holds | paper-delta `T2142a` (paths → walks; far assumption dropped) |

Invariant `Pred(Q)`: there is a family of `p` lax walks (steps = any solid-edge occurrence, loops allowed) in `H(Q)` from `M_x` to `M_y`, occurrence-disjoint, with Hall. Loop steps are deleted at the end to get strict (3),(5) (visited molecules are unchanged). Transfer rule (`Subst`): if there is `ψ : Mol(Q) → Mol(Q')` onto, with `ψ(M_x) = M_x'`, `ψ(M_y) = M_y'`, `ψ` sends external molecules to external ones, and every edge occurrence `e = (a,b)` of `Q` has a lax walk `ω(e)` in `H(Q')` from `ψ(M(a))` to `ψ(M(b))` with pairwise disjoint `ω(e)`, then `Pred(Q) ⇒ Pred(Q')`: `W'_i = ∏ ω(e)` over the steps of `W_i` (visits `ψ(` visited set`)`); Hall: for a set `A'` of internal molecules of `Q'` choose internal preimages (internal because `ψ(external)` is external), get `A` with `|A| = |A'|`, and `#{W'_i meets A'} ≥ #{W_i meets A} ≥ |A|`.

Case table (every output of `lvl1WeightOuts0 / lvl1EdgeOuts0 / lvl1GGOuts0`, `LWLvl1:3228-3250`; `α,β` new internal vertices, all joined to `x` by waved edges: `owxExt` keeps `Γ.waved`, `Γ.dotted` mapped by `emb` (`LWWeightExp:458`), so `ψ` is well defined, onto, never splits a molecule). `(c,t)` twists only swap ends / flip colour (`LWSymm:164-180`): they do not change `H`, only the orientation of steps (walks are undirected).

| term (source) | removed edges `e` | `ω(e)` (new edges) | molecule fact |
|---|---|---|---|
| `(Owx)` T1 `owxET1` (`LWSymm:589`) | none | — | leaf `α ∈ M(x)` |
| T2 `owxET2` | weight `p.1` | nil | loop is inside `M(x)` |
| T3 `owxET3`, `q=(a,b)` | `p.1`, `q.1` | `p.1`: nil; `q.1`: `(a,α),(x,b)` (blue) or `(a,x),(α,b)` (red, `owxDE` `LWWeightExp:468`) | `α ∈ M(x)`: `M(a)→M(x)→M(b)` |
| T4 `owxET4` | `p.1`, `q.1` | nil; `(a,β),(α,b)` / `(a,α),(β,b)` | `β,α ∈ M(x)` |
| `(Oe1x)` `Oe1xOwx` = `owxT1` on the frame | none | — | leaf |
| `Oe1xDs` D (`LWEdgeExp:606`) | `e_0 = (x,v)`, `q=(a,b)` | `e_0`: `(α,v)`; `q`: two edges through `α,x` | `α ∈ M(x)` |
| P5, P3 (`:1084,:1093`), `q=(x,d)` red | `e_0, q` | `e_0`: `(α,v)`; `q`: `(α,d)` | `α ∈ M(x)` |
| P6, P4 (`:1102,:1111`), `q=(s,x)` blue | `e_0, q` | `e_0`: `(α,v)`; `q`: `(s,α)` | `α ∈ M(x)` |
| `(Oe2x)` R2 (`LWGGExp:485`) | `p.1=(x,y)`, `q.1=(y',x)` | `p.1`: nil; `q.1`: `(y',y)` | waved `x~y`: `M(x)=M(y)` |
| R3 = `owxT1` on frame2 | none | — | leaf |
| R4, R5, R6 (`:491,:500,:508`) | `p.1, q.1` | `p.1`: `(α|β, y)`; `q.1`: `(y', α|β)` | `α,β ∈ M(x)` |
| R7 (`:518`), `q'=(a,b)` | `p.1, q.1, q'` | `p.1`: `(α,y)`; `q.1`: `(y',x)` (re-added); `q'`: two edges through `α,x` | `α ∈ M(x)` |
| R8 (`:529`) | `p.1, q.1, q'` | `(β,y)`; `(y',α)`; `q'`: two edges through `β,α` | `α,β ∈ M(x)` |
| `m 1_{x=y_1}` of `(Oe1x)`, `R1` of `(Oe2x)` | — | not listed in `lvl1EdgeOuts0`/`lvl1GGOuts0` (zero on normal graphs, docstrings `LWLvl1:3235,3242`) | — |
| `partition` (`LWVocab:1303`): `merge` (`:778`) then `splitWeights` (`:1246`) | only loops after merging (the coefficient branch of `lwSplitLoops`, `:1209`) | nil (a loop is inside its molecule) | vertex map onto the classes (`lvl1_vmap_surj`, `LWLvl1:238`); `vmap (inl a) = inl (extMap a)` (`:234`), so `x',y'` are the images and `lvl1Pack` (`:3252`) only precomposes `ext`; `x = y` may merge: closed walks |

Each removed edge gets a walk built from new edges used by no other edge; kept edges map to themselves. No output breaks the invariant: no counterexample, verdicts below.

### (ii) One concrete nondegenerate instance

`p ∈ {2,4}` (`p = 2` is the compiled instance; `p = 4` for the starting graph), `d = 3, L = 3, W = 27` (size part), `c = 1/4, K0 = 1, D = 10`; external vertices `x ≠ y`, all internal vertices present, `M_x ≠ M_y`, `p` internal molecules. The model `pf.py`/`final.py` is a Python transcription of the Lean definitions cited in (i) (not Lean; coefficients dropped); fidelity is tested by the merged `lvl1_step_good` (normal, `n_M`, `n_V-n_W`, `ord` monotone: all zero failures below). Python is also the verifier of the walk-substitution (`ω`) of the table: `subst fail`.

```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2142 && python3 final.py
fxyPow(2) == p2Graph (solid, waved, dotted lists, same vertex order): True
p=2 (nS,nW,nV,nM)=(6, 2, 4, 2) ord=2 | normal=True | M_x!=M_y=True | #int molecules=2 | walks disjoint=True ends ok=True visit 2 distinct molecules, Hall=True | search: (True, True)
p=4 (nS,nW,nV,nM)=(12, 4, 8, 4) ord=4 | normal=True | M_x!=M_y=True | #int molecules=4 | walks disjoint=True ends ok=True visit 4 distinct molecules, Hall=True | search: (True, True)
control: edge x-alpha_1 deleted -> False ; extra isolated internal vertex -> False
value identity p=2: max |val - fxy^(p/2) conj(fxy)^(p/2)| over (x,y) in 4 pairs = 6.68e-17
value identity p=4: max |val - fxy^(p/2) conj(fxy)^(p/2)| over (x,y) in 4 pairs = 3.35e-17
LocStep inputs: p2Graph + 60 of its 1472 weight-outputs + 25 edge-type + 6 gg-type graphs of level 2; first error: None
terms exercised: D:11160, Oe1xOwx:100, P3:1606, P4:2722, P5:1606, P6:2722, R2:180, R3:20, R4:510, R5:510, R6:510, R7:1711, R8:11956, T1:246, T2:246, T3:31916, T4:42964
weight outputs= 75372  subst fail=0  Pred fail=0  not-normal=0  (eq:MolVW) fail=0  nM up=0  (nV-nW) up=0  ord down=0  |  Mx=My: 16434
edge   outputs= 19916  subst fail=0  Pred fail=0  not-normal=0  (eq:MolVW) fail=0  nM up=0  (nV-nW) up=0  ord down=0  |  Mx=My: 2457
gg     outputs= 15397  subst fail=0  Pred fail=0  not-normal=0  (eq:MolVW) fail=0  nM up=0  (nV-nW) up=0  ord down=0  |  Mx=My: 10336
p=2 cutoff K=ceil((D+K0 nM+d (nV-nW)+)/c)=72  (p=2 must be 72 = lvl1_inst_cutoff)
p=4 cutoff K=ceil((D+K0 nM+d (nV-nW)+)/c)=104
regime: L^d=27 <= W^K0=27 : True | W^(-d/2)=0.007128 <= Psi=W^-c=0.438691 <= W^-c : True
identity data: m=mE(0)=1j, z=zt(0,1/2)=0.5j, Im z=0.50>0, u=0.50>0, z+u*m = 1j, -1/m = 1j
elapsed 10s
```

External hypothesis: none. The targets have no external premise (`lvl1_lemma_size` and the merged `GaussIBP` are proved inputs; no registry line), so no limit computation is owed. The identity data are those of the merged `lvl1_inst_lemma_size` (`LWLvl1:4404`).

### Verdicts

- Target 1 (`fxyPowGraph`, value identity, `Normal`, counters, `ord = p`): PASS. `Γ_2 = p2Graph` exactly.
- Target 2 (predicates (1)-(6)): PASS. (3)-(5) hold without `(eq:far_ab)` with walks (closed when `M_x = M_y`); (4), (6) are stated but proved in LW-10b.
- Target 3 (`lw_localregular_expansion`: (eq:local_Gs), (1), (2), (3), (5), invariant on `outs ++ errs`): PASS. (2) counts from `Q.g.nM ≤ Γ_p.nM = p`; (eq:MolVW) is one spanning-tree argument for every normal graph.
- Target 4 (path invariant under every `LocStep`): PASS; no output term breaks it (table; 110685 outputs, 0 failures); no BLOCKED graph.

### (a′) Preflight corrections — Sun Oct  4 18:02:03 UTC 2026
None. The Lean case lemmas follow the case table of (a) term by term (17 terms and the `lwSymmOe1xDs` aggregator) and its far-assumption decision.

## (b) Script output — Sun Oct  4 18:02:03 UTC 2026

```
$ cd ../RBM3D-wt/T2142 && lake build RBM3D.Graph.LocalRegular 2>&1 | grep -E "LocalRegular|Build completed|error"
Build completed successfully (3383 jobs).
$ (temporary `import RBM3D.Graph.LocalRegular` after the last import of RBM3D.lean, reverted, not committed) lake build   # Sun Oct  4 18:01:13 UTC 2026 .. Sun Oct  4 18:01:31 UTC 2026
info: RBM3D.lean:189:0: axiom audit: 4564 theorems, 1609 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 88 (borrowed 0, owed 68, structural 20).
Build completed successfully (3907 jobs).
exit=0
$ the same full build before two fixes (first run) ended with
error: RBM3D.lean:189:0: axiom audit: 2 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Graph.LGraph.IsExtMol, RBM.Graph.localReg_StepWalk.below]
$ lake env lean ax.lean   # #print axioms, identical lists grouped; no `sorry` in the output
29 declarations, axioms [propext, Classical.choice, Quot.sound]:  fxyPowGraph_two fxyPowGraph_val_eq fxyPowGraph_normal fxyPowGraph_counters 
fxyPowGraph_ord fxyPowGraph_nM fxyPowGraph_pathInv pathInv_locStep PGraph.PathInv.exists_walks LGraph.molNV_le_molNW_add_one 
lw_localregular_expansion lw_fxyPow_integral_eq localReg_inst_val2 localReg_inst_val4 localReg_inst_step1 localReg_inst_expansion PGraph.LocReg1 
PGraph.LocReg2 PGraph.LocReg3 PGraph.LocReg4 PGraph.LocReg5 PGraph.LocReg6 PGraph.LocReg35 PGraph.LocReg345 fxyPowGraph localReg_inst_noX_not 
localReg_Fam.not_of_isolated LGraph.localReg_pathFam_partition localReg_pathFam_term
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Graph/LocalRegular.lean; grep -c "RBM1D\|RBM2D" RBM3D/Graph/LocalRegular.lean
(no output)   0     # nothing is ported from RBM1D/RBM2D, so no RBM1D/RBM2D diff-stat is owed
$ git diff --stat main...t/T2142   # branch t/T2142, commits 0fc632c 118470e a9654ca 5f33854
 RBM3D/Graph/LocalRegular.lean | 2258 +++++++++++++++++++++++++++++++++++++++++
$ clash2.sh   # git grep -P on `main`, RBM3D/
declared names in RBM3D/Graph/LocalRegular.lean: 165
helper names (prefix localReg_) hits on main:        0 files
  control lvl1_lemma_size: files on main mentioning it:        1
  the 24 unprefixed target names (fxyPowGraph*, pathInv_locStep, lw_localregular_expansion, lw_fxyPow_integral_eq, PathInv, LocReg1-6/35/345, molNV, molNW, molNV_le_molNW_add_one, exists_walks): files on main mentioning them: 0 in total
```

Target statements, extracted from the file by script (`extract.py`; definitions with their bodies):
```
def fxyPowGraph (p : ℕ) : LGraph (Fin 2) (Fin (2 * p)) where solid := (List.finRange p).flatMap (localReg_fxyBlock p) waved := (List.finRange p).map
    fun i => ⟨false, true, .inr (localReg_fxyAlpha i), .inr (localReg_fxyBeta i)⟩ dotted := (List.finRange p).flatMap fun i => [⟨false, .inr
    (localReg_fxyAlpha i), .inl 0⟩, ⟨false, .inr (localReg_fxyAlpha i), .inl 1⟩] coeff := 1
theorem fxyPowGraph_two : fxyPowGraph 2 = p2Graph
theorem fxyPowGraph_val_eq (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (p : ℕ) (hp : Even p) (x y : ι) : (fxyPowGraph p).val D ![x, y] =
    fxyVal D x y ^ (p / 2) * star (fxyVal D x y) ^ (p / 2)
theorem fxyPowGraph_normal (p : ℕ) : (fxyPowGraph p).Normal
theorem fxyPowGraph_counters (p : ℕ) : (fxyPowGraph p).nS = 3 * p ∧ (fxyPowGraph p).nW = p ∧ (fxyPowGraph p).nV = 2 * p ∧ (fxyPowGraph p).nM = p
theorem fxyPowGraph_ord (p : ℕ) : ord (fxyPowGraph p).counters = p
theorem fxyPowGraph_nM (p : ℕ) : (fxyPowGraph p).nM = p
theorem fxyPowGraph_pathInv (p : ℕ) : (fxyPowGraph p).pack.PathInv p
def PGraph.PathInv (p : ℕ) (Q : PGraph (Fin 2)) : Prop := Q.g.localReg_PathFam p (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1))
theorem pathInv_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (hst : LocStep m P outs) {k : ℕ} (hP : P.PathInv k) : ∀ B ∈ outs,
    B.PathInv k
theorem PGraph.PathInv.exists_walks {Q : PGraph (Fin 2)} {p : ℕ} (h : Q.PathInv p) : Q.LocReg35 p
def LGraph.molNV (Γ : LGraph E I) (c : Γ.Mol) : ℕ := (Finset.univ.filter fun v : E ⊕ I => Γ.molOf v = c).card
def LGraph.molNW (Γ : LGraph E I) (c : Γ.Mol) : ℕ := (Γ.waved.filter fun e => Γ.molOf e.x = c).length
theorem LGraph.molNV_le_molNW_add_one (Γ : LGraph E I) (hN : Γ.Normal) (c : Γ.Mol) : Γ.molNV c ≤ Γ.molNW c + 1
def PGraph.LocReg1 (Q : PGraph (Fin 2)) : Prop := Q.LocStd
def PGraph.LocReg2 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := Q.g.nM ≤ p ∧ ∀ c : Q.g.Mol, Q.g.molNV c ≤ Q.g.molNW c + 1
def PGraph.LocReg3 (Q : PGraph (Fin 2)) (p : ℕ) (W : Fin p → List (Q.g.Mol × Q.g.Mol)) : Prop := (∀ i, localReg_StepWalk (Q.g.molOf (Sum.inl (Q.ext
    0))) (Q.g.molOf (Sum.inl (Q.ext 1))) (W i)) ∧ (∑ i, localReg_stepEdges (W i)) ≤ Q.g.localReg_molEdgeMS
def PGraph.LocReg4 (Q : PGraph (Fin 2)) (p : ℕ) (W : Fin p → List (Q.g.Mol × Q.g.Mol)) : Prop := ∀ c : Q.g.Mol, ¬ Q.g.IsExtMol c → ∃ i j : Fin p, i ≠
    j ∧ localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (W i) c ∧ localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (W j) c
def PGraph.LocReg5 (Q : PGraph (Fin 2)) (p : ℕ) (W : Fin p → List (Q.g.Mol × Q.g.Mol)) : Prop := ∀ A : Finset Q.g.Mol, (∀ c ∈ A, ¬ Q.g.IsExtMol c) →
    A.card ≤ (Finset.univ.filter fun i : Fin p => ∃ c ∈ A, localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (W i) c).card
def PGraph.LocReg6 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := (2 * p : ℤ) ≤ Q.g.scalingOrder
def PGraph.LocReg35 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := ∃ W, Q.LocReg3 p W ∧ Q.LocReg5 p W
def PGraph.LocReg345 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := ∃ W, Q.LocReg3 p W ∧ Q.LocReg4 p W ∧ Q.LocReg5 p W
theorem lw_localregular_expansion (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) : ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs,
    Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^
    K0 → (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧ (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff
    c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧ Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧
    Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW) ∧ (∀ {sz : Sizes d} {n :
    ℕ} {z : ℂ} {u : ℝ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m
    = -m⁻¹ → (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp → (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe
    : Fin 2 → Idx d (sz.L n) (sz.W n), ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) = (outs.map fun Q
    => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum + (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS
    sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧ (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg35 p) ∧ (∀ Q ∈ outs ++ errs, Q.PathInv p)
```
Compiled nonempty instances (same file, section 10); extracted statements, then the list of the other `example`s with file lines:
```
theorem localReg_inst_val2 : (fxyPowGraph 2).val lwD ![0, 1] = 67081
theorem localReg_inst_val4 : (fxyPowGraph 4).val lwD ![0, 1] = 4499860561
theorem localReg_inst_step1 : ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false), B.PathInv 2
theorem localReg_inst_noX_not : ¬ localReg_inst_noX.pack.PathInv 1
theorem localReg_inst_expansion : ∃ outs errs : List (PGraph (Fin 2)), (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ errs, Q.g.scalingSize
    (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧ ∫ ω, (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2))
    (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) = (outs.map fun Q => ∫ ω, Q.val (lwSampleData
    lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum + (errs.map fun Q
    => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP
    lwWxInstSz)).sum ∧ (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg35 2) ∧ (∀ Q ∈ outs ++ errs, Q.PathInv 2)
2081:example : (fxyPowGraph 2).nS = 3 * 2 ∧ (fxyPowGraph 2).nW = 2 ∧ (fxyPowGraph 2).nV = 2 * 2 ∧ (fxyPowGrap
2084:example : ord (fxyPowGraph 2).counters = 2 := fxyPowGraph_ord 2
2086:example : (fxyPowGraph 2).Normal := fxyPowGraph_normal 2
2088:example : (fxyPowGraph 4).nS = 3 * 4 ∧ (fxyPowGraph 4).nW = 4 ∧ (fxyPowGraph 4).nV = 2 * 4 ∧ (fxyPowGrap
2091:example : ord (fxyPowGraph 4).counters = 4 := fxyPowGraph_ord 4
2093:example : (fxyPowGraph 4).Normal := fxyPowGraph_normal 4
2095:example : fxyPowGraph 2 = p2Graph := fxyPowGraph_two
2098:example : (fxyPowGraph 2).pack.PathInv 2 := fxyPowGraph_pathInv 2
2100:example : (fxyPowGraph 4).pack.PathInv 4 := fxyPowGraph_pathInv 4
2103:example : (fxyPowGraph 4).molNV (localReg_fxyMol 0) ≤ (fxyPowGraph 4).molNW (localReg_fxyMol 0) + 1 :=
2108:theorem localReg_inst_step1 :
2113:example : (fxyPowGraph 2).pack.LocReg2 2 :=
2117:example : (fxyPowGraph 2).pack.LocReg35 2 := (fxyPowGraph_pathInv 2).exists_walks
2119:example : ¬ (fxyPowGraph 2).pack.LocReg6 2 := by
2125:example : lvl1ExStd.pack.LocReg1 := lvl1_inst_locStd_pack
2127:example : figGraph.pack.LocReg6 2 := by
2192:theorem localReg_inst_noX_not : ¬ localReg_inst_noX.pack.PathInv 1 := by
2222:theorem localReg_inst_expansion :
2246:example :
```

Narrative (each statement is backed by the output above or by the file):
1. `RBM3D/Graph/LocalRegular.lean`: 2258 lines, 10 sections, 165 declarations, namespace `RBM.Graph`; every helper has the prefix `localReg_`; the only file that differs from `main`.
2. Target 1. `fxyPowGraph p` is built from the blocks `localReg_fxyBlock` by `flatMap` over `List.finRange p`; `fxyPowGraph_two` is proved by `rfl`, so `fxyPowGraph 2 = p2Graph` with the same vertex order.
   `fxyPowGraph_val_eq`: the term at a labelling is the product over the blocks (`localReg_fxy_term`); the sum over `Fin (2p) → ι` factorises through `Fin p → ι × ι` (`localReg_fxy_sum_pairs`); a blue block sums to
   `fxyVal`, a red one to its conjugate (`S` real), and `Fin.card_filter_val_lt` gives `p/2` of each (`p` even).  Normal: both the `×`-dotted and the solid non-loop pairs are `{x, α_i}`, `{α_i, y}`.  `n_M = p`: two vertices are in
   one molecule iff they are in one block (`localReg_fxy_molOf_eq_iff`), and `LGraph.nM_eq_card`.
3. Target 2, Lean forms. A walk is a list of steps `(a, b)` (`localReg_StepWalk`, a recursive `def` on the list); "pairwise edge-disjoint" is the multiset inequality `∑ i, stepEdges (W i) ≤ molEdgeMS` over unordered pairs of
   molecules of `molSolid`; Hall is `LocReg5`; the walks of (3)-(5) are one family `W` (`LocReg35`, `LocReg345` state them as `∃ W`).  `(eq:MolVW)` (`LGraph.molNV_le_molNW_add_one`): a molecule is a connected component, so Mathlib's
   `Connected.card_vert_le_card_edgeSet_add_one` applies to the induced graph, whose edges inject into the waved edges of the molecule (a normal graph has no `=`-dotted edge).
4. Target 4 (the heart). `localReg_Fam p u v Int B` is a family of `p` walks with a multiset budget `B` of edges (loop steps free) and the Hall condition.  Generic lemmas: `Fam.map` (along `ψ` onto the internal nodes), `Fam.thr` (one use of an
   edge `{a, b}` rerouted as `{a, X}, {X, b}`), `Fam.of_add_diag`, `Fam.strict` (delete loops), and the replacement relation `FamRepl`/`VRepl` (`deriv`, `same`).  On graphs: `localReg_PathFam`, `pathFam_map` (a vertex map respecting waved and
   `=`-dotted edges), `pathFam_partition` (from the merged `lvl1_part_struct`: dropped or circled weights are loops), `pathFam_term` (a twisted `owxExt` term; any `μ` constant on its molecules), then 17 term lemmas `localReg_pathFam_*`
   (`owxT1..T4`, `oe1xOwx`, `oe1xD`, `oe1xP5/P3/P6/P4`, `oe2xR2..R8`) and `localReg_pathFam_oe1xDs`; each reduces to `deriv` (a removed edge replaced through the molecule of `x`) or `same`/`of_diag`/`of_le` (edges moved to `α ∈ M(x)`,
   loops, no edge removed, the merge of `R2`).  `pathInv_locStep` destructs `LocStep` as the merged `lvl1_step_good` does; `fxyPowGraph_pathInv` is the explicit family `x → α_i → y`.
5. Target 3. `lw_localregular_expansion` is `lvl1_lemma_size` at `(fxyPowGraph p).pack` plus `lvl1_induction` for `PathInv`, `molNV_le_molNW_add_one`, `n_M ≤ p` and `PathInv.exists_walks`; `lw_fxyPow_integral_eq` rewrites the left
   side as the expectation of `f^{p/2} \overline{f}^{p/2}`.  No `(eq:far_ab)` is assumed (the decision of (a)).
6. Registry. The first full build with the temporary root import reported two unclassified premises (lines above): `LGraph.IsExtMol` as a hypothesis of a helper lemma, and `localReg_StepWalk.below` (the auxiliary of the recursive
   inductive).  Both are removed in the file (the helper takes `∀ a, molOf (inl a) ≠ c`; `StepWalk` is a recursive `def`); `RBM3D/Test/Axioms.lean` is untouched; the second and third full builds pass.
7. A negative control: `localReg_inst_noX_not` (for `p = 1` without the edge `G_{xα₁}` there is no family of walks; generic `localReg_Fam.not_of_isolated`).  The instance of `pathInv_locStep` exercises the weight constructor at
   `p2Graph`; the edge and GG constructors are covered by the proof for all inputs, not by a separate instance.

## (c) Verified Mathlib names
Each name below was found in the project environment by `env.contains`, and its module read by `Environment.getModuleIdxFor?` (script output, 160 names of the file in all):
`SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one` — Mathlib.Combinatorics.SimpleGraph.Acyclic (line 471; absent unless that module is imported)
`SimpleGraph.ConnectedComponent.connected_toSimpleGraph`, `.toSimpleGraph` — Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected (lines 643, 685)
Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected: SimpleGraph.Adj.reachable SimpleGraph.ConnectedComponent SimpleGraph.ConnectedComponent.ind SimpleGraph.ConnectedComponent.lift SimpleGraph.Reachable.refl
Mathlib.Data.Sym.Sym2: Sym2.eq_iff Sym2.eq_swap Sym2.ind Sym2.map Sym2.map.injective Sym2.map_map Sym2.map_mk Sym2.mem_iff Sym2.mem_mk_left Sym2.mk_isDiag_iff
Mathlib.Data.Multiset.Filter: Multiset.count_filter Multiset.filter_add Multiset.filter_coe Multiset.filter_eq_nil Multiset.filter_eq_self Multiset.filter_le Multiset.filter_le_filter Multiset.filter_map Multiset.le_filter Multiset.mem_filter Multiset.monotone_filter_right
Mathlib.Data.Multiset.ZeroCons: Multiset.coe_nil Multiset.cons_coe Multiset.cons_swap Multiset.insert_eq_cons Multiset.mem_cons Multiset.notMem_zero Multiset.zero_le
Mathlib.Data.Multiset.AddSub: Multiset.add_cons Multiset.add_le_add_iff_right Multiset.coe_add Multiset.cons_add Multiset.count_add Multiset.le_add_right Multiset.singleton_add Multiset.zero_add
Mathlib.Data.Multiset.MapFold: Multiset.map_add Multiset.map_coe Multiset.map_congr Multiset.map_cons Multiset.map_le_map Multiset.map_map Multiset.map_singleton Multiset.map_zero Multiset.mem_map
Mathlib.Data.Multiset.Count: Multiset.count_eq_zero Multiset.count_le_of_le Multiset.count_singleton Multiset.le_iff_count
Mathlib.Data.Multiset.Defs: Multiset.coe_eq_coe Multiset.coe_le Multiset.mem_coe Multiset.mem_of_le
Mathlib.Algebra.Order.Group.Multiset: Multiset.mapAddMonoidHom
Mathlib.Algebra.BigOperators.Group.Finset.Piecewise: Finset.prod_ite Finset.sum_eq_add_sum_sdiff_singleton_of_mem
Mathlib.Algebra.BigOperators.Ring.Finset: Finset.prod_univ_sum
Mathlib.Algebra.BigOperators.Fin: Fin.prod_univ_def Fin.sum_univ_def Fin.sum_univ_three
Mathlib.Data.Fintype.Fin: Fin.card_filter_val_lt
Mathlib.Data.Fintype.Pi: Fintype.piFinset_univ
Mathlib.Data.Fintype.BigOperators: Fintype.sum_prod_type
Mathlib.Data.Finset.Card: Finset.card_filter_add_card_filter_not Finset.card_image_le Finset.card_image_of_injOn Finset.card_le_card List.toFinset_card_le
Mathlib.SetTheory.Cardinal.Finite: Nat.card Nat.card_congr Nat.card_eq_fintype_card Nat.card_le_card_of_injective
Mathlib.Logic.Function.Basic: Function.surjInv Function.surjInv_eq Function.update
Verified absent (Unknown constant, tool log): `Multiset.map_sum`, `Multiset.coe_map`, `Multiset.coe_filter`, `Sym2.map_pair_eq`, `Sym2.isDiag_iff_proj_eq`, `List.mem_split`, `Finset.sum_eq_add_sum_diff_singleton`; deprecated: `List.Sublist.cons₂` (→ `cons_cons`).

## (d) Open issues and paper-delta candidates
Open issues:
1. Properties (4) and (6) and the assembly of `lem:localregular` are LW-10b.  (4) needs the labelled correspondence "path `i` ↔ molecule `𝓜_i`" of `B:178-199`; the Hall invariant here does not carry it.  The stage lemmas
   `localReg_pathFam_partition`, `localReg_pathFam_term`, `localReg_VRepl.deriv/same` are generic in the budget and the walk family, so a labelled family can reuse them.
2. With `𝓜_x = 𝓜_y` the empty walks satisfy (3); (5) still binds (an internal molecule must be visited), so this is the paper's statement without `(eq:far_ab)`.
3. The file has 2258 lines (the ticket's bound for proposing a further split was 2500).
4. The helpers are public with the prefix `localReg_` (CLAUDE.md §3 (E): "private or prefixed with the file stem"), not `private`, so that LW-10b can reuse them; the ticket's "private helpers with the prefix `localReg_`" was read as the prefix rule.
Paper-delta candidates (to be numbered by the dispatcher):
- `T2142a`: (3)-(5) are for walks in the molecular multigraph (each edge occurrence used once, a molecule may be revisited), not simple paths: the proof of the paper replaces an edge by two edges through another molecule
  (`B:184-196`).  `(eq:far_ab)` (`7_8:792`) is not assumed; closed walks if `𝓜_x = 𝓜_y`.
- `T2142b`: (5) is carried by the Hall condition inside the invariant, not by the labelled path-molecule correspondence of `B:178-199`.
- `T2142c`: `(eq:MolVW)` (`7_8:798`) is proved for all vertices of the molecule (external ones included), which is stronger than for the internal ones.
- `T2142d`: `fxyPowGraph p`, the invariant and `lw_localregular_expansion` are for every `p`; evenness (`p ∈ 2ℕ`) is used only by `fxyPowGraph_val_eq` and `lw_fxyPow_integral_eq`.
Result: targets 1-4 delivered on `t/T2142` (built, axioms standard, compiled nonempty instances, full build with the root import passes); nothing external is assumed (no registry line).
