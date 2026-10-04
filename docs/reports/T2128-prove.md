Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 11:01:09 UTC 2026
Notation: ord = nS + 2(nW - nV) (7_8:270); w = number of solid self-loops; deg(v) = non-loop solid edges at v; Phi = sum over internal v of max(deg v - 2, 0); "blue-out" = `G_{xy}` at its source x. Method: `lvl1.py` in the scratchpad (Python, no Lean) implements `LGraph.partition` (dot-def, weights split) and the three expansions with the term lists of the merged `owxT1-4` (LWWeightExp.lean:658-695), `oe1x*` (T2119 report items 4-5) and `oe2xR1-R8` (LWGGExp.lean:484-546); edge types other than the merged blue ones are modelled by the images under conjugation (flip every sigma) and transposition (swap src/dst), which are NOT merged (rows C1-C4).

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| counters, `p2Graph` / `figGraph` | (nS,nW,nV,nM)=(6,2,4,2), ord 2 / (8,4,6,2), ord 4 | LWVocab `p2Graph_counters`, `figGraph_counters` | script reproduces both |
| Dord, Owx T1,T2,T4 (after partition) | min +1 | >= 0 (lvl1: ord G' >= ord G) | +1 |
| Dord, Owx T3 | min 0: derivative loop `G_xx` is split, the constant-`m` part drops an edge; Dw = -1 or -2 (bullet 1 of 7_8:353-362) | >= 0 | 0 (tight) |
| Dord, Oe1x T1,T2 / Oe1x `oe1xD` | min +1 / min 0: pull of `G_{xy1}` with `Gbar_{xy'}` or `G_{wx}`, loop dropped; DPhi in {-1..-4}, Dw = 0 (bullet 2) | >= 0 | 0 (tight) |
| Dord, Oe2x R1,R3-R8 / R2 | min +1 / min 0 (`G_{xy}G_{yx}` -> `S^+_{xy}`, y'=y, bullet 3); DnS = -2, Dw = DPhi = 0 | >= 0 | 0 (tight) |
| termination measure | mu = ((K-ord)^+, w, Phi, nS) in N^4, lexicographic | each output: ord up, or ord equal and (w,Phi,nS) lex-smaller | script: 290335 outputs, 0 violations |
| Delta(nV-nW), Delta nM, Delta nV | max 0, max 0, max +2 (every term, after partition) | size corollary needs nV-nW and nM not to grow | 0 (tight) |
| cutoff (a) `ord >= K` | K >= (D + K0 nM(G) + (d-2c)(nV-nW)^+(G))/c, from size <= (L^d)^nM Psi^K (W^d Psi^2)^(nV-nW)^+ | Psi = W^-c, W^-d/2 <= Psi <= 1, L^d <= W^K0 | instance K = 68, log_W bound = -10.00 (tight at D=10) |
| cutoff (b) `size <= W^-D` at fixed (Psi,W,L) | reduces to (a): size <= W^-D follows from ord >= K above | Psi < 1 | none; (a) chosen |
| regime (instance) | d=3, L=3, W=27, Psi = 27^(-1/4) = 0.439, c = 1/4, K0 = 1 (N=(WL)^3 <= W^4 iff L^3 <= W) | W^-3/2 = 0.0071 <= Psi <= W^-1/4 | Psi/W^-3/2 = 62; L^d = W (tight) |
| flow data, all three `*_graph_E` | E=0, m = mE 0 = i, u = t = 1/2, z = zt 0 (1/2) = i/2 | 0 < Im z, 0 < u, m != 0, z + u m = -1/m, `|m|^2 u < 1` | Im z = 1/2; residual 0; `|m|^2 u` = 1/2 |
| `hSp`, `hM` | Sp - m^2 Sp S = S, M_aa = m; `lwClaimSize` has M = m I | resummation, S row sums = u | residual 8.5e-17 (W=2, N=216), 6.9e-17 (block algebra, W=27) |
| size of the tree | p2Graph nodes 487745 (K=5), 13349536 (K=6): factor 27 per unit of K | lists exist for every K, size exponential in K | K = 68 cannot be enumerated: existence by well-founded induction only |
| C1 conj forms | merged: blue weight `Gc_xx` (`owx_graph_E` hx), blue-out `G_{xy}` (`oe1x_graph_E` hx), blue `G_{xy}G_{y'x}` (`oe2x_graph_E` hp1, hq1) | strat_local meets red weights, red edges, `Gbar Gbar` | missing: no theorem for sigma = false |
| C2 transposed forms | `oe1x_graph_E` needs `p.1 = <true,false,inr x,v>` (blue edge leaving x) | Step 2 at a vertex with in-edges only | missing; example below |
| C3 external weights | `owx_graph_E` takes `x : I` (internal) | a light-weight on an external vertex must be expanded (deflvl1 (ii), 7_8:367-386; Strategy Step 1, B:135-157) | missing |
| C4 circled non-loop edges | `oe1x/oe2x` need `circ = false`; `hM` only gives `M a a = m` | input may contain `(G-M)_{xy}`, x != y | needs `M a b = 0` for a != b, as in `lwClaimSize` hM |

### (ii) One concrete nondegenerate instance
Data: d=3, L=3, W=27 (flow checks also run directly at W=2, N=216), g=1, E=0, t=u=1/2, Psi=W^(-1/4), D=10; graph `p2Graph` (ord 2, nM=2) with K=5 for the enumerated run, K=68 for the size bound.
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2128 && python3 instance.py`
```
m=1j z=0.5j Im z=0.500 u=0.50 | z+u*m+1/m = 0.0e+00 | |m|^2 u = 0.500 (<1) | m!=0: True
W=2 N=216: row sums of S in [0.500000,0.500000] (=u) | S symmetric True | max|Sp-m^2 Sp S-S| = 8.5e-17 | Sp symmetric True | M=m*I: M_aa=m
W=27 (block algebra, N=(27*3)^3=531441): max|Spb-m^2 Spb Kb-Kb| = 6.9e-17, row sums of K*u = 0.500
p2Graph counters nS,nW,nV,nM,ord = 6,2,4,2,2 ; d=3,L=3,W=27,Psi=W^-1/4,D=10,K0=1 -> K>=68 ; log_W(size bound)=-10.00 <= -D
one-step: 290335 outputs of random normal graphs (<=4 internal, all colours/directions): violations of [dord>=0, and dord=0 => (w,Phi,nS) lex-decreases] = 0
min dord per (step,term): {'S1:owxT1': 1, 'S1:owxT2': 1, 'S1:owxT3': 0, 'S1:owxT4': 1, 'S2:oe1xD': 0, 'S2:oe1xT1': 1, 'S2:oe1xT2': 1, 'S3:R1': 1, 'S3:R2': 0, 'S3:R3': 1, 'S3:R4': 1, 'S3:R5': 1, 'S3:R6': 1, 'S3:R7': 1, 'S3:R8': 1}
p2Graph ord0=2 K=5: nodes 487745, outs 26 (all locally standard: True), out orders {4: 26}, all out ord>=ord0: True, errs(ord>=K) 487432, lex violations 0 [4s]
p2Graph ord0=2 K=6: nodes 13349536, outs 278 (all locally standard: True), out orders {5: 252, 4: 26}, all out ord>=ord0: True, errs(ord>=K) 13342391, lex violations 0 [127s]
figGraph ord0=4 K=6: nodes 68028, outs 0 (all locally standard: True), out orders {}, all out ord>=ord0: True, errs(ord>=K) 68003, lex violations 0 [1s]
figGraph ord0=4 K=7: nodes 1384141, outs 188 (all locally standard: True), out orders {6: 188}, all out ord>=ord0: True, errs(ord>=K) 1383443, lex violations 0 [13s]
G_{x v0}G_{v0 y} (GG vertex) ord0=0 K=2: nodes 799, outs 4 (locstd True), out orders {0: 1, 1: 3}, ord>=ord0 True, errs 786, lex violations 0
G_{x v0}G_{y v0} (in-edges only) ord0=0 K=2: nodes 260, outs 2 (locstd True), out orders {1: 2}, ord>=ord0 True, errs 255, lex violations 0
Gc_{v0v0} G_{x v0} Gbar_{x v0} (weight) ord0=1 K=3: nodes 2839, outs 16 (locstd True), out orders {2: 16}, ord>=ord0 True, errs 2811, lex violations 0
p2Graph first step: 736 outputs, 352 carry a light-weight on an EXTERNAL vertex (merged (Owx) needs x internal)
loop-free random graphs needing Step 2: 2648; of these 1206 have NO bad vertex with a blue out-edge (merged (Oe1x) inapplicable)
python3 instance.py  140.17s user 0.31s system 95% cpu 2:27.58 total
```
External hypotheses: none. `GaussIBP sz` is the proved `gaussIBP` (Green/IBPPoly.lean:305); the stochastic bounds `STGbEXP*` do not enter (T2124b: `lwClaimSize` is deterministic), so no limit computation is owed; the regime row above is the only asymptotic input and holds at W=27.
Fixed-selection note: `outs` depends on the selection rule (p2Graph K=6: 280 outs in one run, 278 in the next); the lemma needs existence only.

### Verdicts
- Target 1 `deflvl1`: PASS. Clauses (i)-(iii) are decidable on records (`LGraph.Normal` is decidable on main); the model's predicate for (i)-(iii) holds for every output of every run above, and `G_{x v0}G_{y v0}`, `Gc_{v0v0} G_{x v0} Gbar_{x v0}` are non-examples (charge +2; a loop).
- Target 5 cutoff: PASS with choice (a): `ord >= K`, K as in the table; corollary `size <= W^-D` for the errs' counters (nM and nV-nW do not grow: the Delta(nV-nW) row).
- Target 2 `LocStep` and its expectation identity: BLOCKED (missing inputs C1-C4). The merged theorems give the identity only for blue weights at internal vertices, blue-out edges, blue `G_{xy}G_{y'x}`. Needed: (S1) conjugation of graphs (pure algebra: flip sigma, swap ends of coloured waved edges; needs `D.S` real, true for `lwS`); (S2) invariance of `seqP` under the flip of the imaginary-part coordinates, giving `G(w') = G(w)^T` and hence the in-edge forms (variances do not depend on the Bool coordinate, FineModel.lean:89-93); (S3) `(Owx)` at an external vertex. Evidence: `G_{x v0} G_{y v0}` (normal, v0 internal, deg 2, charge +2, no blue-out edge) needs Step 2 and none of the merged theorems applies; 1206 of 2648 random loop-free normal graphs needing Step 2 have no bad vertex with a blue-out edge; 352 of 736 first-step outputs of `p2Graph` carry a light-weight on an external vertex.
- Target 3 `lvl1 lemma`: mathematically PASS (measure above; all runs terminate, every output locally standard with ord >= ord G), but BLOCKED as a Lean target until target 2's inputs exist.
- Target 4 `lvl1_induction`: BLOCKED with target 2 (it is a corollary of the relation `LocStep`).
- Risk rule: no step with Dord < 0 and no cycle found; the T2120c case y = x does not occur (Step 3 runs only on weight-free graphs, so y != x, y' != x); the merged `oe1x_graph_E_loop` is not used by Step 2 (no weights present).
## (a′) Preflight corrections — Sun Oct  4 15:38:34 UTC 2026
No verdict of (a) changes. Three refinements, none of which falsifies a row of the table:
1. Measure: (a) has mu = ((K-ord)^+, w, Phi, nS); the proof uses `Lvl1Mu` = ((K-ord)^+, nLoops, nS, nPairs), nPairs = pairs of solid non-loop edges with a common internal end. `Lvl1Good` (ord up, or ord equal and (nLoops, nS, nPairs) lex-smaller) is proved for every term of the three expansions (`lvl1_good_*`, `lvl1_step_good`).
2. Cutoff: (a) row "cutoff (a)" gives K = 68 using the factor (d-2c) of (W^d Psi^2)^(nV-nW)+; `lvl1Cutoff` uses d (Psi <= 1 in that factor): K = 72 at p2Graph (c = 1/4, K0 = 1, d = 3, D = 10; `lvl1_inst_cutoff`). Both are valid cutoffs.
3. "Targets 2-4 BLOCKED (C1-C4)": C1-C3 are merged (`git log`: a871db4 T2131 Graph/LWSymm), C4 is the data hypothesis `M a b = 0`. The data of the identity instances are the merged `lwWxInstSz` (d = 3, L = 3, W = 1, g = 1/2, E = 0, t = 1/2) of T2107/T2131; (a)'s W = 27, L = 3, Psi = 27^(-1/4) enter `lvl1_inst_lemma_size` (size bound) only.

## (b) Script output
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2128`, branch `t/T2128`, commit 7768a79. `git diff --stat main...t/T2128`:
```
 RBM3D/Graph/LWLvl1.lean | 4462 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    4 +
 2 files changed, 4466 insertions(+)
```
### Build and registry pre-check
```
$ lake build RBM3D.Graph.LWLvl1 > log; echo rc=$?        # started Sun Oct  4 15:37:07 UTC 2026
rc=0   Build completed successfully (3365 jobs).
errors 0, `sorry` 0 (grep of the log); warnings of the module: 164 = unused hypotheses in type 56, unused simp args 37, long lines 30, deprecated lemma names 29, flexible simp 7, `show` 4, other 1
$ lake build        # full library of the worktree; the root import of the new module is the hub's step at merge
RBM3D.lean:180:0: axiom audit: 4105 theorems, 1418 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3881 jobs).
$ lake env lean precheck.lean        # import RBM3D; import RBM3D.Graph.LWLvl1; #assert_rbm_axioms
axiom audit: 4276 theorems, 1492 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
registry: 1 borrowed + 75 owed + 43 structural; 44 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ lake build   # hub's merge step simulated: `import RBM3D.Graph.LWLvl1` temporarily added after the last import of RBM3D.lean (reverted, not committed)
RBM3D.lean:181:0: axiom audit: 4276 theorems, 1492 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3882 jobs).
(before the four registry lines of `RBM3D/Test/Axioms.lean` were added the same pre-check ended: error: axiom audit: 4 premise(s) ... [RBM.Graph.LGraph.XBetween, RBM.Graph.lvl1Split, RBM.Graph.lvl1Split.below, RBM.Graph.Lvl1Reach.below])
```
### Axioms (`#print axioms`; the script groups identical outputs)
```
RBM3D.Graph.LWLvl1: 276 declarations (188 theorems); axioms used (union): [Quot.sound, Classical.choice, propext]
31 declarations depend on exactly [propext, Classical.choice, Quot.sound]:
  LGraph.LocStd, PGraph.LocStd, LocStep, lvl1_step_good, lvl1_step_identity, lvl1_exists_step, lvl1_induction, lvl1_exists_aux, lvl1_lemma, lvl1_lemma_induction, lvl1_size_le, lvl1_lemma_size, lvl1_inst_locStd, lvl1_inst_not_locStd, lvl1_inst_locStep_weight, lvl1_inst_locStep_edge, lvl1_inst_locStep_gg, lvl1_inst_step1, lvl1_inst_step1_terms, lvl1_inst_step2_terms, lvl1_inst_step3_terms, lvl1_inst_locStep_weightExt, lvl1_inst_step1Ext, lvl1_inst_step2, lvl1_inst_step3, lvl1_inst_cutoff, lvl1_inst_size_le, lvl1_inst_lemma, lvl1_inst_lemma_size, lvl1_inst_induction, lvl1_inst_lemma_induction
```
### Target statements (extracted by script from `RBM3D/Graph/LWLvl1.lean`; `⋮` = elision printed by the script; (L) = file line)
```
-- StdNeutral (L3199)
def LGraph.StdNeutral (Γ : LGraph E I) (v : E ⊕ I) : Prop :=
  ((Γ.lvl1SolidAt v).map SEdge.σ = [true, false] ∨ (Γ.lvl1SolidAt v).map SEdge.σ = [false, true]) ∧ Γ.lvl1ChargeAt v = 0
-- LocStd (L3204)
def LGraph.LocStd (Γ : LGraph E I) : Prop :=
  Γ.Normal ∧ (∀ e ∈ Γ.solid, e.src ≠ e.dst) ∧
    ∀ i : I, Γ.StdNeutral (Sum.inr i) ∨ Γ.lvl1DegAt (Sum.inr i) = 0
-- PGraph.LocStd (L3215)
def PGraph.LocStd {E : Type} (P : PGraph E) : Prop := P.g.LocStd
-- decidable (L3217)
instance {E : Type} (P : PGraph E) : Decidable P.LocStd := by
-- LocStep (L3260)
inductive LocStep (m : ℂ) : PGraph E → List (PGraph E) → Prop
  | weight (P : PGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (x : P.E' ⊕ P.I') (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) :
      LocStep m P (lvl1Pack P (lvl1WeightOuts0 m P.g p x c t))
  | edge (P : PGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (x : P.I') (v : P.E' ⊕ P.I') (hv : v ≠ Sum.inr x) (c t : Bool)
      (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) (hwf : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
      (hbad : P.g.lvl1DegAt (Sum.inr x) ≠ 0 ∧ (P.g.lvl1DegAt (Sum.inr x) ≠ 2 ∨ P.g.lvl1ChargeAt (Sum.inr x) ≠ 0)) :
      LocStep m P (lvl1Pack P (lvl1EdgeOuts0 m P.g p x v c t))
  | gg (P : PGraph E) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (hq : q ∈ lwSplit p.2) (x : P.I') (y y' : P.E' ⊕ P.I') (hy : y ≠ Sum.inr x) (c t : Bool)
      (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
      (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hwf : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
      (hnb : ∀ i : P.I', P.g.lvl1DegAt (Sum.inr i) = 0 ∨ (P.g.lvl1DegAt (Sum.inr i) = 2 ∧ P.g.lvl1ChargeAt (Sum.inr i) = 0)) :
      LocStep m P (lvl1Pack P (lvl1GGOuts0 m P.g p q x y y' c t))
-- Lvl1Reach (L3277)
inductive Lvl1Reach (m : ℂ) (K : ℤ) : PGraph E → PGraph E → Prop
  | refl (P : PGraph E) : Lvl1Reach m K P P
  | step (P Q R : PGraph E) (L : List (PGraph E)) : Lvl1Reach m K P Q → ord Q.g.counters < K → ¬ Q.g.LocStd →
      LocStep m Q L → R ∈ L → Lvl1Reach m K P R
-- data variables of the identity section (L3431)
variable {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} {m : ℂ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
variable (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
  (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
  (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
-- lvl1_step_identity (all variables above are `include`d) (L3590)
theorem lvl1_step_identity {E : Type} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs)
    (hN : P.g.Normal) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, P.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum
-- lvl1_exists_step (L3655)
theorem lvl1_exists_step (m : ℂ) (P : PGraph E) (hN : P.g.Normal) (hn : ¬ P.g.LocStd) : ∃ outs, LocStep m P outs
-- lvl1_step_good (L3290)
theorem lvl1_step_good {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs) (hN : P.g.Normal) :
    ∀ Q ∈ outs, Q.g.Normal ∧ Lvl1Good P.g Q.g
-- lvl1_induction (L3763)
theorem lvl1_induction {m : ℂ} {K : ℤ} {P Q : PGraph E} (h : Lvl1Reach m K P Q) (Pred : PGraph E → Prop) (h0 : Pred P)
    (hstep : ∀ (A : PGraph E) (L : List (PGraph E)), LocStep m A L → Pred A → ∀ B ∈ L, Pred B) : Pred Q
-- lvl1_lemma (L3907)
theorem lvl1_lemma (m : ℂ) (K : ℤ) (Γ : PGraph E) (hN : Γ.g.Normal) :
    ∃ outs errs : List (PGraph E),
      (∀ Q ∈ outs, Q.g.LocStd ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧
      (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ outs ++ errs, Lvl1Reach m K Γ Q ∧ Q.g.Normal ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧
        Q.g.nM ≤ Γ.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ (Γ.g.nV : ℤ) - Γ.g.nW) ∧
      ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
        (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
        (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
        (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : E → Idx d (sz.L n) (sz.W n),
          ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
            (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
            (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum
-- lvl1_lemma_size (L4047)
theorem lvl1_lemma_size (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (Γ : PGraph E) (hN : Γ.g.Normal) :
    ∃ outs errs : List (PGraph E),
      (∀ Q ∈ outs, Q.g.LocStd ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
        (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
      (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D Γ.g.counters : ℤ) Γ Q ∧ Q.g.Normal ∧
        Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ Γ.g.nM ∧ (Q.g.nV : ℤ) - Q.g.nW ≤ (Γ.g.nV : ℤ) - Γ.g.nW) ∧
      ⋮ (8 lines: the identity conjunct of lvl1_lemma, for the fixed d, `∀ {sz : Sizes d} ...`)
-- lvl1_lemma_induction (L3940)
theorem lvl1_lemma_induction (m : ℂ) (K : ℤ) (Γ : PGraph E) (hN : Γ.g.Normal) :
    ⋮ (outs, errs and the two clauses on them as in lvl1_lemma)
      (∀ Pred : PGraph E → Prop, Pred Γ →
        (∀ (A : PGraph E) (L : List (PGraph E)), LocStep m A L → Pred A → ∀ B ∈ L, Pred B) →
        ∀ Q ∈ outs ++ errs, Pred Q) ∧
      ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
      ⋮ (identity conjunct of lvl1_lemma)
-- lvl1Cutoff (L3981)
def lvl1Cutoff (c : ℝ) (K0 d : ℕ) (D : ℝ) (G : Counters) : ℕ
  ⌈(D + (K0 : ℝ) * G.nM + (d : ℝ) * (((G.nV : ℤ) - G.nW).toNat : ℝ)) / c⌉₊
-- lvl1_size_le (L3989)
theorem lvl1_size_le (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (G : Counters) (W L : ℕ) (Ψ : ℝ)
    (hW : 1 ≤ W) (hL : 1 ≤ L) (hLW : (L : ℝ) ^ d ≤ (W : ℝ) ^ K0)
    (hlow : (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) (hup : Ψ ≤ (W : ℝ) ^ (-c))
    (Q : Counters) (hK : (lvl1Cutoff c K0 d D G : ℤ) ≤ ord Q) (hM : Q.nM ≤ G.nM)
    (hV : (Q.nV : ℤ) - Q.nW ≤ (G.nV : ℤ) - G.nW) :
    Q.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)
```
### Compiled nonempty instances (theorems of the same file)
Data: merged `lwWxInstSz` (d = 3, L = 3, W = 1), m = mE 0 = i, z = zt 0 (1/2), u = 1/2, `lwWxInstSp`, `lwWxInstM`, `gaussIBP lwWxInstSz`, labels `lwSymmInstL`; graph `p2Graph` (2 external, 4 internal vertices, counters (6,2,4,2)); every hypothesis is discharged by a term, `decide` or `norm_num`.
```
L4147-4186 deflvl1 on records: lvl1_inst_locStd, lvl1_inst_locStd_pack, lvl1_inst_std_counts, lvl1_inst_fail_{normal,loop,loopExt,deg1,deg3,same,charge}, lvl1_inst_not_locStd
L4202-4239 one LocStep of each kind and its identity: lvl1_inst_locStep_{weight,edge,gg,weightExt}, lvl1_inst_step{1,2,3,1Ext} (the last at an external red weight)
L4309-4335 outputs of the three explicit steps before the dotted edge partition, counters and orders by `decide`: lvl1_inst_step{1,2,3}_terms (Step 1 on p2Graph: 12 terms, all of order 3 = ord + 1)
L4355 lvl1_inst_cutoff; L4368 lvl1_inst_size_le (lvl1_size_le at counters (80,4,6,1)); L4384 lvl1_inst_lemma (K = 72); L4431 lvl1_inst_induction; L4441 lvl1_inst_lemma_induction; L4404 lvl1_inst_lemma_size:
theorem lvl1_inst_lemma_size :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧
      ∫ ω, p2Graph.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum
```
### Name clash, ports, kernel evaluation
```
$ python3 clash.py   # for each public name of the module (git grep -E on `main` 1ef8fa7, pattern: declaration keyword + same short name)
205 public declarations; same short name declared on main: 1
  RBM.Graph.Lvl1Reach.trans <-> 5 unrelated declarations named `trans` in other namespaces (e.g. RBM3D/Defs/Domination.lean:109:theorem trans (h₁ : UnifDetDo)
$ grep -c "RBM1D\|RBM2D" RBM3D/Graph/LWLvl1.lean    -> 0   (no port recorded; no RBM1D/RBM2D diff-stat to give)
$ lake env lean partition_decide.lean   # example : (p2Graph.partition 1).length = 1 := by decide
Tactic `decide` failed for proposition
  (LGraph.partition 1 p2Graph).length = 1
... Classical.propDecidable ... reduction got stuck at the `Decidable` instance (`Classical.propDecidable` occurs in the unfolded list: 1 line)
```
### Narrative (every statement is supported by the blocks above or by the file)
- `LWLvl1.lean` has 16 numbered sections (module docstring, `## Contents`): counters of the terms of the dotted edge partition (1), support lemmas (2-4), degree and charge (5), one-step claims for Steps 1, 2, 3 (6-8), packed outputs (9), `deflvl1` and `LocStep` (10), the identity of one step (11), existence of a step (12), induction, measure, lists (13), the lemma (14), the cutoff (15), instances (16).
- Provenance: sections 1-14 are scratch modules found in `scratchpad/T2128/lean/` (mtimes 2026-10-04 05:42-06:43 PDT, from an earlier attempt of this stage); they were recompiled in dependency order (each exit code 0) and assembled with what this round wrote: `PGraph.LocStd` decidability, `ord < K` for `outs` in `lvl1_lemma`, `lvl1_lemma_induction`, sections 15-16, the `lvl1` prefix on the public helper names that lacked it (`nLoops`, `nPairs`, `IncAt`, `chargeAt`, `solidAt`, `degAt`, `PGraph.comp`, `PGraph.comp_val`; CLAUDE.md §3 E), the paper line citations in docstrings, the module docstring, the four registry lines.
- Target 1: `LocStd` is the three clauses of `deflvl1` (`7_8:367-386`). `StdNeutral`: the non-loop solid edges at `v` are one `G` and one `Ḡ` (either order) and the charge `(eq:neutralcharge)` is 0 (`lvl1ChargeAt`: +1 for an incoming blue or outgoing red edge, -1 otherwise). Degrees do not count self-loops (`B:128`).
- Target 2: `LocStep` = Steps 1-3 of `B:135-157`. "A later step only when the earlier ones are null" is `hwf` (no self-loop) in `edge` and `gg`, `hbad` (Step 2 applies) in `edge`, `hnb` (Step 2 null) in `gg`. Outputs: the terms of the T2131 forms `lwSymmOwxT*`, `lwSymmOe1x*`, `lwSymmOe2xR*` for the selector `(c, t)`, each followed by `LGraph.partition m` and packed (`lvl1Pack`); `m 1_{x=y1}` and `R1` are not listed (zero on normal graphs: `lvl1_oe1xT1_zero`, `lvl1_oe2xR1_zero`). `lvl1_step_identity` is proved from `lwSymm_weight_graph_E`, `lwSymm_oe1x_graph_E`, `lwSymm_oe2x_graph_E` and `LGraph.val_eq_partition`.
- Target 3 and termination: `lvl1_step_good` (every output of a `LocStep` at a normal graph is normal and `Lvl1Good`, from the term lemmas `lvl1_good_*`); `lvl1_exists_step` (a step exists at every normal graph that is not `LocStd`); `lvl1_exists_aux` is the well-founded induction on `Lvl1Mu K` (`InvImage.wf`, lexicographic `Lvl1Lt`) with the base cases `K ≤ ord Γ` (`errs = [Γ]`) and `Γ.LocStd` (`outs = [Γ]`). The `∃ outs errs` precedes the data `d, sz, n, z, u, Sp, M, ℓe`: the lists do not depend on them.
- Target 4: `Lvl1Reach` = reached by steps applied below the cutoff to graphs that are not `LocStd`; `lvl1_lemma` gives `Lvl1Reach m K Γ Q` for every graph of both lists, `lvl1_induction` and `lvl1_lemma_induction` as printed above.
- Target 5: cutoff (a) `ord ≥ K`, `K = lvl1Cutoff` (independent of `n`). `lvl1_size_le` proves `size ≤ W^{-D}` from `ord Q ≥ K`, `n_M(Q) ≤ n_M(G)`, `n_V - n_W` not larger (the facts `lvl1_lemma` gives for the outputs) by `Counters.scalingSize_eq` and one bound per factor; `lvl1_lemma_size` is the paper's form of the lemma (`Err` of size `≤ W^{-D}`).
- Instances: `LGraph.partition` is not kernel-computable (output above), so the lists of `lvl1_lemma` at `p2Graph` stay existential and the instances state their properties and the identity at the data. The outputs of the explicit steps are listed at the level of the expansion terms (before the dotted edge partition): `lvl1_inst_step1_terms` (12 terms of Step 1 on `p2Graph`, counters (7,3,5,2) / (7,4,6,2), all of order 3 = ord + 1), `lvl1_inst_step2_terms` (1 term), `lvl1_inst_step3_terms` (5 terms), by `decide`; `lvl1_inst_locStep_*` give the packed output lists symbolically (`lvl1Pack .. (lvl1WeightOuts0 ..)`, `lvl1EdgeOuts0`, `lvl1GGOuts0`). Section (a) reports 736 first-step outputs of its Python model on `p2Graph`; this round did not compute them in Lean.
- Hypotheses of the identity beyond the three merged `*_graph_E` theorems: `M a b = 0` (ticket Amend 1) and `Spᵀ = Sp` (the symmetric forms of T2131); see T2128a. `RBM3D/Test/Axioms.lean`: four names added to `structuralProps` (`XBetween`, `lvl1Split`, `lvl1Split.below`, `Lvl1Reach.below`).

## (c) Verified Mathlib names (found by `env.find?` in the project environment; module in which Lean finds them)
`Real.rpow_le_one_of_one_le_of_nonpos` — Mathlib.Analysis.SpecialFunctions.Pow.Real
`Real.rpow_pos_of_pos` — Mathlib.Analysis.SpecialFunctions.Pow.Real
`Real.rpow_natCast` — Mathlib.Analysis.SpecialFunctions.Pow.Real
`Real.rpow_mul` — Mathlib.Analysis.SpecialFunctions.Pow.Real
`Real.rpow_add` — Mathlib.Analysis.SpecialFunctions.Pow.Real
`Real.rpow_le_rpow_of_exponent_le` — Mathlib.Analysis.SpecialFunctions.Pow.Real
`zpow_le_zpow_right₀` — Mathlib.Algebra.Order.GroupWithZero.Basic
`zpow_le_zpow_right_of_le_one₀` — Mathlib.Algebra.Order.GroupWithZero.Basic
`pow_le_pow_right₀` — Mathlib.Algebra.Order.GroupWithZero.Basic
`pow_le_pow_left₀` — Mathlib.Algebra.Order.GroupWithZero.Basic
`one_le_pow₀` — Mathlib.Algebra.Order.GroupWithZero.Basic
`pow_le_one₀` — Mathlib.Algebra.Order.GroupWithZero.Basic
`mul_le_of_le_one_right` — Mathlib.Algebra.Order.GroupWithZero.Basic
`div_le_iff₀` — Mathlib.Algebra.Order.GroupWithZero.Basic
`zpow_nonneg` — Mathlib.Algebra.Order.GroupWithZero.Basic
`zpow_natCast` — Mathlib.Algebra.Group.DivInvMonoid
`Nat.le_ceil` — Mathlib.Algebra.Order.Floor.Semiring
`Nat.ceil_eq_iff` — Mathlib.Algebra.Order.Floor.Semiring
`Int.self_le_toNat` — Init.Data.Int.Order
Present, used in sections 1-13 (same lookup): `Nat.card_le_card_of_injective`, `Fintype.card_le_of_surjective`, `List.Perm.countP_eq`, `List.sum_eq_zero`, `WellFounded.prod_lex`, `wellFounded_lt`, `InvImage.wf`, `Finset.card_univ_diff` (present, deprecated alias of `Finset.card_univ_sdiff`, which is present; warning in section 1). Names verified absent: none to report.

## (d) Open issues and paper-delta candidates
Paper-delta candidates (same tags as the module docstring):
- `T2128a`: data hypotheses beyond the three merged `*_graph_E`: `Spᵀ = Sp` (T2131) and `M a b = 0` (Amend 1, C4). `lwSymm_lwSplus_symm` gives the first for `S⁺ = lwSplus` when `0 ≤ u` and `‖m‖² u < 1`.
- `T2128b`: cutoff (a) `ord ≥ K` replaces `(eq:smallsize)` (`B:140`); `errs` also holds locally standard graphs of order `≥ K`; `lvl1Cutoff` uses d (not d-2c of (a)); `lvl1_size_le` has constant 1 and needs `1 ≤ W`, `1 ≤ L`, `L^d ≤ W^{K0}`, `W^{-d/2} ≤ Ψ ≤ W^{-c}`.
- `T2128c`: the terms `m 1_{x=y₁}` of `(Oe1x)` and `R1` of `(Oe2x)` are not in the outputs of `LocStep` (value 0 on normal graphs).
- `T2128d`: termination measure `(K-ord, nLoops, nS, nPairs)` instead of the preflight's `(.., w, Φ, nS)` (internal, no statement changes).
- `T2128e`: the lemma is stated for normal packed graphs; the regular-weight decomposition `(G_αα - m) + m` is done by `LGraph.partition m` of each output (ticket item 2), not inside Step 1 (`B:138-145`).
Open issues:
1. Output lists are not computable in the kernel (`decide` output in (b)); the instances of `lvl1_lemma`, `lvl1_lemma_size` state properties of the existential lists and the identity at the data.
2. The four registry lines are on `a871db4`; main was at `1ef8fa7` at the name check: the hub applies them onto main (CONTROL H23 b) and adds `import RBM3D.Graph.LWLvl1` to `RBM3D.lean`; the full build of the worktree includes the module only in the simulated import run above.
3. 164 warnings in the module, no errors (classes in (b)); 163 are at file lines before section 15 (sections 1-14), 1 is in section 16 (`lvl1_locStd_iff`: unused hypotheses in type).
4. For LW-10: `lvl1_lemma_induction` / `lvl1_induction` with `lvl1_step_good`; `Lvl1Reach.step` also carries `ord < K` and `¬ LocStd` of the input if an invariant needs them (unfold `Lvl1Reach`).
Result: targets 1-5 are delivered on `t/T2128` (built, axioms standard, compiled instances); the open points are the lists above.
