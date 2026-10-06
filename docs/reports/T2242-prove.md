Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 02:17 UTC 2026

### (i) Exponent table (p = q = 2 numbers from the scripts below; `π i j = true` iff `α_i` strictly closer to `b_j`)

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| regions `𝐃_π` (T2) | `2^{pq} = 16` | each `ℓ` lies in exactly one (`π_ℓ i j = decide(|ℓ_i-b_j| < |ℓ_i-a_j|)`) | exact partition: `val = Σ_π valOn`, rel. err ≤ 2.8e-16 (num_main, part 1) |
| `C` (T2) | `Σ_π C_π`, 16 terms, `> 0` (`Fin q → Fin p → Bool` nonempty) | `val ≤ Σ_π C_π θ^q ψ(0)^e Π ψ(c_π r)` | none lost |
| `c` (T2) | `min_π c_π ∈ (0,1]` | `c ≤ c_π` and `ψ` antitone on `[0,∞)`, `r ≥ 0` give `ψ(c_π r) ≤ ψ(c r)`; exponent `ord - nngh` and `θ^q` do not depend on `π`; all factors `> 0` (`θ>0`, `ψ>0`) | exact |
| half-distance (T3) | factor `2` | `|z-x| ≤ |z-y| ⇒ |x-y| ≤ |x-z|+|z-y| ≤ 2|z-y|` (triangle + `sub_comm`); region: `π i j = false ⇒ |a_j-b_j| ≤ 2|ℓ_i-b_j|`, `π i j = true ⇒ |a_j-b_j| ≤ 2|ℓ_i-a_j|` | none lost beyond the triangle inequality |
| ending-edge types (T3) | A1 iff `noGhostPath j ∧ π i j = s`; A2 iff `noGhostPath j ∧ π i j = !s`; B1 iff path has ghost, edge solid; B2 iff edge ghost | exhaustive: split on `noGhostPath j` (Bool), then `π i j = s` or `!s` (Bool), or the ghost flag (Bool) | no hypothesis needed (not even `IsNested`) |
| `figAuxGh`, all 16 `π` | types `{B1,B1,B2,B2}`, NoA2, `AnpCaseI`, `AnpCaseIII`, `degS = [4,2]` | pinned instance (1) | holds for every `π` |
| `figAux`, 16 `π` | 6 type classes (pre_main); NoA2 only at `π = ((F,F),(T,T))` (all four A1); `¬NoA2` at `π ≡ false` (A2 at `(j,s,k,i) = (0,T,4,1),(1,T,5,1)`); `AnpCaseIII` never | pinned instance (2) | — |
| A2 replacements (T4) | `figAux`, `π ≡ false`: 2, ending at `figAuxGh` | `≤ nngh ≤ p`; each one lowers `nngh` by 1, `nSolid` by 1 | `2 ≤ p = 2`, tight |
| `ord - nngh` under A2 replacement (T4) | `figAux`: `2-2 = 0`; `figAuxGh`: `0-0 = 0`; `nSolid 6→4`, `nngh 2→0` | invariant (merged `anpKey_ghostify_ord`) | exact |
| `C` (T4) | unchanged | `valOn Γ ≤ ψ(|a_j-b_j|/2)·valOn Γ̃` pointwise on the region (`ξ(a_j,ℓ_i) ≤ ψ(|ℓ_i-a_j|) ≤ ψ(r_j/2)` by T3, `ξ ≥ 0`, other factors equal) | num_main part 2: max ratio 0.7788 ≤ 1 (4352 cases) |
| `c` (T4) | `c' = min(c, 1/2)`, iterated ≤ p times stays `min(c,1/2)` (no accumulation) | `c' ≤ 1/2` so `ψ(r_j/2) ≤ ψ(c' r_j)`; `c' ≤ c` so `ψ(c r_i) ≤ ψ(c' r_i)`; `c' ≤ 1` | `1/2 - c' ≥ 0` |
| IH (T4, T6) | merged form: `∀ p' k, k < q → ∀ Γ' …` (`AnpIHPin d q` = IH of `AnpDetGhStep`) | needed only inside the case pins | — |
| T5 `q → q-1`, edges | `p' = p + Σ_j k_j` (`k_j` = visits of `α_{i₀}` by `𝔓_j`); `figAuxGh`: `p' = 4 = 2+2` (both `i₀`); `nSolid' = nSolid` | (F8) | `ordN' = ordN + 2` (`0 → 2`) |
| T5 `i₀` row | only the row `π i₀` survives (sum over `x ∈ regionOne`), other rows dropped using `ξ ≥ 0` | `lhs ≤ rhs` of (F3) | fix.py: 1848 cases, 0 violations, max ratio 1.0000 |
| Case-I interface (for LW-12c, not a target) | after `fix` and 2 ghostify of the one-step A1/B1 paths: `ordN'' = 0 = ordN`, `nngh'' = 0 = nngh` | `(eq:change_of_order)` | exact |
| `θ`-step (for c/d) | `Σ_x ξ(a_1,x)ξ(a_2,x) ≤ θ` (Cauchy–Schwarz, `Σ_β ξ² ≤ θ` for both rows) | — | instance: `valOn/(θ² ψ(0)^0) = 0.2681` for `figAuxGh` with `C = 1` |

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 5` (125 sites), `p = q = 2`, `Γ = figAuxGh` (`GhostOK`, `IsNested`, `NoA2`, `AnpCaseI`, `AnpCaseIII`, `degS(ℳ₂) = 2`) and `figAux` (`¬NoA2`), `π ≡ false`, `ψ(r) = 1/(1+r)`, random admissible `ξ` with `θ = max_α Σ_β ξ² = 7.727`.
Every deterministic hypothesis of T2–T6 is checked in the output (`xi<=psi`, symmetry, `θ>0`, `GhostOK`, `IsNested`, `NoA2`). The hypotheses `AnpDetGhRegStep d` (T6) and the case pins are other gates' pins (LW-12c–f), left as hypotheses; their conclusion is evaluated at the instance (ratio lines of `inst.py`, all `≤ 1` with `C = 1`, `c = 1/4`). There is no external or limit hypothesis (all targets are deterministic, `L`, `d` arbitrary; §29 below).

Command (scratch dir `<scratchpad>/T2242/`, Python only):
`for s in pre_main num_main fix inst; do python3 $s.py; done` (outputs verbatim, headers added by `echo`):
```
$ python3 pre_main.py
== (i) tables, p=q=2, 16 regions pi (pi[i][j]=True iff alpha_i closer to b_j)
figAux nSolid 6 ordN 2 nngh 2 ord-nngh 0 nested True ghostok True degS [4, 4]
  types ('A1', 'A1', 'A1', 'A1') NoA2 True CaseI True CaseIII False #pi 1
  types ('A1', 'A1', 'A1', 'A2') NoA2 False CaseI True CaseIII False #pi 4
  types ('A1', 'A1', 'A2', 'A2') NoA2 False CaseI False CaseIII False #pi 4
  types ('A1', 'A1', 'A2', 'A2') NoA2 False CaseI True CaseIII False #pi 2
  types ('A1', 'A2', 'A2', 'A2') NoA2 False CaseI False CaseIII False #pi 4
  types ('A2', 'A2', 'A2', 'A2') NoA2 False CaseI False CaseIII False #pi 1
figAuxGh nSolid 4 ordN 0 nngh 0 ord-nngh 0 nested True ghostok True degS [4, 2]
  types ('B1', 'B1', 'B2', 'B2') NoA2 True CaseI True CaseIII True #pi 16
figAux  pi=0: ending edges [((0, False, 0), 0, 'A1'), ((0, True, 4), 1, 'A2'), ((1, False, 1), 0, 'A1'), ((1, True, 5), 1, 'A2')]
figAuxGh pi=0: ending edges [((0, False, 0), 0, 'B1'), ((0, True, 4), 1, 'B2'), ((1, False, 1), 0, 'B1'), ((1, True, 5), 1, 'B2')]
figAux pi=0: A2 replacements until NoA2: 2 (<= p=2); result == figAuxGh: True ord-nngh 0
target4 constant: c -> min(c,1/2); iterated n<=p times stays min(c,1/2); C unchanged. target2: C=sum_pi C_pi over 2^(pq)=16 terms, c=min_pi c_pi
figAux: pi with NoA2: [((np.False_, np.False_), (np.True_, np.True_))]
$ python3 num_main.py
== (ii)(1) val = sum_pi valOn(region pi), figAux, d=3
 L=3 psi=1/(1+r) theta=3.362 max rel.err |val-sum_pi|/val = 2.13e-16
 L=3 psi=exp(-r/2) theta=5.389 max rel.err |val-sum_pi|/val = 0.00e+00
 L=5 psi=1/(1+r) theta=7.551 max rel.err |val-sum_pi|/val = 2.81e-16
 L=5 psi=exp(-r/2) theta=9.484 max rel.err |val-sum_pi|/val = 1.21e-16
== (ii)(2) A2 inequality valOn(G) <= psi(|a_j-b_j|/2) valOn(G~) on region pi (max ratio over all A2 edges)
 graphs q>=1 (nested, ghostOK): 80 ; q=1: 77 q=2: 3 p=3: 41
 checked 4352 (graph,pi,A2 edge,psi,xi,a,b) cases; max valOn(G)/(psi(r/2) valOn(G~)) = 0.778801 (<= 1 required)
$ python3 fix.py
== (ii)(3) anpKey2_fix at figAuxGh
 i0=0: p'=4 q'=1 own=[0, 0, 1, 1] ea=[('a', 0), None, ('a', 1), None] eb=[None, ('b', 0), None, ('b', 1)]
   paths': [[(0, ('b', 0))], [(2, ('m', 0)), (4, ('b', 1))], [(1, ('b', 2))], [(3, ('m', 0)), (5, ('b', 3))]]
   edges': [(0, ('a', 0), ('b', 0)), (0, ('a', 2), ('b', 2)), (0, ('a', 1), ('m', 0)), (0, ('a', 3), ('m', 0)), (1, ('m', 0), ('b', 1)), (1, ('m', 0), ('b', 3))]
   F-checks: {'F1': True, 'F2': True, 'F4': True, 'F5': True, 'F6': True, 'F7': True, 'F8': True}
 i0=1: p'=4 q'=1 own=[0, 0, 1, 1] ea=[('a', 0), None, ('a', 1), None] eb=[None, ('b', 0), None, ('b', 1)]
   paths': [[(0, ('m', 0)), (2, ('b', 0))], [(4, ('b', 1))], [(1, ('m', 0)), (3, ('b', 2))], [(5, ('b', 3))]]
   edges': [(0, ('a', 0), ('m', 0)), (0, ('a', 2), ('m', 0)), (0, ('m', 0), ('b', 0)), (0, ('m', 0), ('b', 2)), (1, ('a', 1), ('b', 1)), (1, ('a', 3), ('b', 3))]
   F-checks: {'F1': True, 'F2': True, 'F4': True, 'F5': True, 'F6': True, 'F7': True, 'F8': True}
 random nested ghostOK graphs q>=1 (t2.py generator): 120 ; with a path visiting alpha twice: 18 ; with an edge on no path at an alpha: 29
 (graph,i0) pairs checked: 136; max p'=7; pairs with some F1,F2,F4..F8 failure: 0; per-condition all-pass: {'F1': True, 'F2': True, 'F4': True, 'F5': True, 'F6': True, 'F7': True, 'F8': True}
 F3 numeric: 1848 (graph,i0,pi) cases, violations lhs>rhs: 0, max lhs/rhs = 1.0000
$ python3 inst.py
== instance: d=3 L=5 (|Z_L^d|=125) p=q=2 pi==false psi(r)=1/(1+r)
 hyps: psi>0 antitone; xi>=0 True symm True xi<=psi(|.|) True theta=7.7270>0, row-sum xi^2<=theta
 figAuxGh: GhostOK True IsNested True NoA2 True CaseI True CaseIII True degS [4, 2]
 figAux: GhostOK True IsNested True NoA2 False CaseI True CaseIII False degS [4, 4]
 figAuxGh: max valOn/(theta^q psi0^(ord-nngh) prod psi(c r)^chi), C=1, c=0.25, 6 random (a,b): 0.2681
 figAux: max valOn/(theta^q psi0^(ord-nngh) prod psi(c r)^chi), C=1, c=0.25, 6 random (a,b): 0.0154
 fix(figAuxGh,i0=0): p'=4, one-step paths of the two B1 edges: [(0, [(0, ('b', 0))], ('a', 0), None), (2, [(1, ('b', 2))], ('a', 1), None)]
 case-I interface: ordN(G)=0 ordN(G')=2 -> after 2 ghostify ordN''=0; nngh(G)=0 nngh(G')=2 nngh''=0; G'' ghostOK True nested True
```

### Checks by inspection (against `7_8:1103-1599`)
- No primed successor of `AnpDetGhStep` is needed: Cases (I)-(IV) and the setup use only `ψ > 0`, `ψ` antitone (half-distance, `ψ(c r) ≤ ψ(c' r)`, `ξ ≤ ψ(r) ≤ ψ(0)`), `ξ ≥ 0` symmetric, `ξ ≤ ψ(|·|)`, `Σ_β ξ² ≤ θ` (Cauchy-Schwarz `:1178`, `:1348`, `:1421`, `:1437`; `xy ≤ x²+y²` `:1430`) and the IH; `c` is halved per step (`(eq:induc_Ggraph)`, `:1166`, `ψ(c|a_i-b_i|/2)`); no `(eq:Psi)`.
- (F7): the head step of `𝔓_j` is `(k, v)` with `a_j` external and `inr i₀` an endpoint of `k`, so `v = inr i₀` (WalkOK): the first segment is the one step `k` (symmetrically for `s = true`); an edge on no path at `α_{i₀}` is sent to any copy (nonempty: `α_{i₀}` lies on two paths); fix.py covers 29 graphs with such an edge and 18 with a path visiting `α_{i₀}` twice.
- `IsNested` conjunct 6 for `Γ'`: for `A ⊆ Fin q` and `A' = succAbove '' A`, each old path visiting `A'` has a segment visiting `A` (the step's edge keeps its `inr (succAbove⁻¹ ·)` endpoint), and `own` is a function, so `#{r} ≥ #{j} ≥ |A'| = |A|`. Conjuncts 1-5: edge images are injective on vertex symbols (`a_j ↦ ea`-copy, `b_j ↦ eb`-copy, `α_{i₀} ↦` a copy with label `none`, distinct indices), segments are nonempty (no self-loop), edge-disjointness/Nodup are inherited. `GhostOK`: a ghost is the head of the first or the last of the last segment.
- Pinned lemma `anpKey2_caseI_ne` (not a pinned target): two A1/B1 ending edges `(j₁,s₁) ≠ (j₂,s₂)` at one vertex have `j₁ ≠ j₂`: A1+A1 on one path needs `π i j = false` and `= true`; A1+B1 contradicts `noGhostPath`; B1+B1 contradicts `GhostOK` (the ghost is an ending edge, both ending edges are solid).

### Verdicts
- T1 vocabulary (`valOn`, regions, `EndAt`, A1–B2, `NoA2`, `degS`, `fixLab`; `val = valOn … univ` by `rfl`): PASS.
- T2 `anpDetGh_of_reg`: PASS. T3 `anpKey2_half`, `anpKey2_reg_half`, `anpKey2_endTypes`: PASS.
- T4 `anpDetGhReg_of_noA2`: PASS (strong induction on `nngh`, `c ↦ min c ½`, `C` unchanged).
- T5 `anpKey2_fix`: PASS (F1–F8 hold on `figAuxGh` and 136 `(Γ, i₀)` pairs; `IsNested` conjunct 6 and (F7) are not obstructions; no counterexample found).
- T6 `anpDetGhStep_of_reg`, `anpDetGhRegStep_of_cases`: PASS (target 4 for every `Γ` gives `RegAt π` for all `π`, then T2; `by_cases` on `AnpCaseI`, `AnpCaseIII`).

### §29 checklist
(1) no time variable. (2) no `1 - ilambda²/L²`. (3) no `L^d ≤ W^K`. (4) no `∀ᶠ n`. (5) uniform in `(a,b)`: `∀ a b` inside, `C, c` before `L`. (6) no parameter lower bound (`d`, `L` arbitrary, `[NeZero L]`). (7) no scale: `ψ`, `θ` abstract.

## (b) Script output — written Tue Oct  6 03:15:13 UTC 2026

Build, scan, commits (commands and output verbatim):
```
$ lake build RBM3D.Graph.AnpKey2 2>&1 | grep -E "AnpKey2|error|Build completed"
Build completed successfully (3347 jobs).
$ lake env lean RBM3D/Graph/AnpKey2.lean; echo "exit $?"
exit 0
$ lake build   # whole library (the root does not import the new module yet)
Build completed successfully (4045 jobs).
exit 0
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/AnpKey2.lean; wc -l RBM3D/Graph/AnpKey2.lean
0
    2057 RBM3D/Graph/AnpKey2.lean
$ git log --oneline -4; git diff main...t/T2242 --stat
da47890 T2242: AnpKey2 instances (3a), (3b) at d = 3, L = 5
0bd639a T2242: AnpKey2 docstrings
342e6c2 T2242: LW-12b Graph/AnpKey2 (regions, ending-edge types, A2 replacement on a region, vertex fixing, case interface)
25362ad T2239: merge S6-09a Induction/ExpIntI
 RBM3D/Graph/AnpKey2.lean | 2057 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    8 +
 2 files changed, 2065 insertions(+)
```
Pins = file. `mkstat.py` copies check-file sections 2-3 (lines 77-273, verbatim, namespace `RBM.Graph.T2242Check`) and appends 27 links; `lake env lean statcheck.lean` exits 0 with no error (only the check file's own unused-variable warnings):
```
@valOnPin = @NGraph.valOn; @regionPin = @anpKey2_region; @regionOnePin = @anpKey2_regionOne; @EndAtPin = @NGraph.EndAt; @IsA1Pin = @NGraph.IsA1; @IsA2Pin = @NGraph.IsA2; @IsB1Pin = @NGraph.IsB1; @IsB2Pin = @NGraph.IsB2; @NoA2Pin = @NGraph.NoA2; @degSPin = @NGraph.degS; @fixLabPin = @anpKey2_fixLab; @AnpDetGhRegAtPin = @AnpDetGhRegAt; @AnpIHPin = @AnpIH; @AnpDetGhRegStepPin = @AnpDetGhRegStep; @CaseIPin = @AnpCaseI; @CaseIIIPin = @AnpCaseIII; @AnpDetGhCaseIPin = @AnpDetGhCaseI; @AnpDetGhCaseIIIPin = @AnpDetGhCaseIII; @AnpDetGhCaseIVPin = @AnpDetGhCaseIV; AnpDetGhOfRegPin := @anpDetGh_of_reg; AnpKey2HalfPin := @anpKey2_half; AnpKey2RegHalfPin := @anpKey2_reg_half; AnpKey2EndTypesPin := @anpKey2_endTypes; AnpDetGhRegOfNoA2Pin := @anpDetGhReg_of_noA2; AnpKey2FixPin := @anpKey2_fix; AnpDetGhStepOfRegPin := @anpDetGhStep_of_reg; AnpDetGhRegStepOfCasesPin := @anpDetGhRegStep_of_cases
```
Registry pre-check (`pre.lean` = `import RBM3D`, `import RBM3D.Graph.AnpKey2`, `#assert_rbm_axioms`). Before the registry lines (whitespace folded), then after `lake build RBM3D.Test.Axioms`:
```
$ lake env lean pre.lean   # before
error: axiom audit: 8 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`: [RBM.Graph.AnpDetGhCaseIV, RBM.Graph.AnpDetGhCaseIII, RBM.Graph.AnpDetGhCaseI, RBM.Graph.NGraph.IsA2, RBM.Graph.NGraph.EndAt, RBM.Graph.NGraph.NoA2, RBM.Graph.NGraph.IsA1, RBM.Graph.NGraph.IsB1]
$ lake env lean pre.lean; echo "exit $?"   # after
axiom audit: 7096 theorems, 2410 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit 0
$ git diff -U0 main...t/T2242 -- RBM3D/Test/Axioms.lean | grep -E '^@@|^\+ ' | sed -E 's/, -- .*//'
@@ -161,0 +162,3 @@ def owedProps : List Name :=
+   `RBM.Graph.AnpDetGhCaseI
+   `RBM.Graph.AnpDetGhCaseIII
+   `RBM.Graph.AnpDetGhCaseIV
@@ -283,0 +287,5 @@ def structuralProps : List Name :=
+   `RBM.Graph.NGraph.EndAt
+   `RBM.Graph.NGraph.IsA1
+   `RBM.Graph.NGraph.IsA2
+   `RBM.Graph.NGraph.IsB1
+   `RBM.Graph.NGraph.NoA2
```
Axioms. `#print axioms` of the targets, then `axsum.lean` (`collectAxioms` over all 163 public declarations of the file, grouped by axiom set):
```
'RBM.Graph.anpDetGh_of_reg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_reg_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_endTypes' depends on axioms: [propext]
'RBM.Graph.anpDetGhReg_of_noA2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_fix' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGhStep_of_reg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGhRegStep_of_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey2_caseI_ne' depends on axioms: [propext, Quot.sound]
99 declarations depend on exactly [Classical.choice, Quot.sound, propext]
22 declarations depend on exactly []
18 declarations depend on exactly [propext]
21 declarations depend on exactly [Quot.sound, propext]
3 declarations depend on exactly [Classical.choice, propext]
   [RBM.Graph.anpKey2_pred, RBM.Graph.anpKey2_succAbove_pred, RBM.Graph.anpKey2_pred_succAbove]
```
Target statements, extracted from the file by `extract.py` (comments dropped, whitespace folded):
```
RBM3D/Graph/AnpKey2.lean:191: theorem anpDetGh_of_reg (d p q : ℕ) (Γ : NGraph p q) (h : ∀ π, AnpDetGhRegAt d Γ π) : AnpDetGhAt d Γ
RBM3D/Graph/AnpKey2.lean:261: theorem anpKey2_half (d L : ℕ) [NeZero L] (x y z : Zd d L) (h : zdistInf d L (z - x) ≤ zdistInf d L (z - y)) : zdistInf d L (x - y) ≤ 2 * zdistInf d L (z - y)
RBM3D/Graph/AnpKey2.lean:269: theorem anpKey2_reg_half (d L p q : ℕ) [NeZero L] (a b : Fin p → Zd d L) (π : Fin q → Fin p → Bool) (ℓ : Fin q → Zd d L) (hℓ : ℓ ∈ anpKey2_region a b π) (i : Fin q) (j : Fin p) : (π i j = false → zdistInf d L (a j - b j) ≤ 2 * zdistInf d L (ℓ i - b j)) ∧ (π i j = true → zdistInf d L (a j - b j) ≤ 2 * zdistInf d L (ℓ i - a j))
RBM3D/Graph/AnpKey2.lean:288: theorem anpKey2_endTypes (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (j : Fin p) (s : Bool) (k : Fin Γ.es.length) (i : Fin q) (h : Γ.EndAt j s k i) : Γ.IsA1 π j s k i ∨ Γ.IsA2 π j s k i ∨ Γ.IsB1 π j s k i ∨ Γ.IsB2 π j s k i
RBM3D/Graph/AnpKey2.lean:569: theorem anpDetGhReg_of_noA2 (d p q : ℕ) (π : Fin q → Fin p → Bool) (h : ∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested → Γ.NoA2 π → AnpDetGhRegAt d Γ π) : ∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested → AnpDetGhRegAt d Γ π
RBM3D/Graph/AnpKey2.lean:1821: theorem anpKey2_fix (p q : ℕ) (Γ : NGraph p (q + 1)) (i₀ : Fin (q + 1)) (hG : Γ.GhostOK) (hN : Γ.IsNested) : ∃ (p' : ℕ) (Γ' : NGraph p' q) (ea eb : Fin p' → Option (Fin p ⊕ Fin p)) (own : Fin p' → Fin p) (em : Fin Γ.es.length ≃ Fin Γ'.es.length),  (Γ'.GhostOK ∧ Γ'.IsNested) ∧  (∀ k, (Γ'.es.get (em k)).ghost = (Γ.es.get k).ghost) ∧ (∀ (ι : Type) (a b : Fin p → ι) (x : ι) (ℓ : Fin q → ι) (k : Fin Γ.es.length), Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r))) ℓ (Γ'.es.get (em k)).u = Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).u ∧ Sum.elim (Sum.elim (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r))) ℓ (Γ'.es.get (em k)).v = Sum.elim (Sum.elim a b) (Fin.insertNth (α := fun _ => ι) i₀ x ℓ : Fin (q + 1) → ι) (Γ.es.get k).v) ∧  (∀ (d L : ℕ) [NeZero L] (ξ : Zd d L → Zd d L → ℝ), (∀ α β, 0 ≤ ξ α β) → ∀ (a b : Fin p → Zd d L) (π : Fin (q + 1) → Fin p → Bool), Γ.valOn ξ a b (anpKey2_region a b π) ≤ ∑ x ∈ anpKey2_regionOne a b (π i₀), Γ'.val ξ (fun r => anpKey2_fixLab a b x (ea r)) (fun r => anpKey2_fixLab a b x (eb r))) ∧  (∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none) ∧ (∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none) ∧ (∀ j, ∃! r, ea r = some (Sum.inl j)) ∧ (∀ j, ∃! r, eb r = some (Sum.inr j)) ∧  (∀ (j : Fin p) (k : Fin Γ.es.length), (∃ v : NV p (q + 1), (k, v) ∈ Γ.path j) ↔ ∃ (r : Fin p') (v' : NV p' q), own r = j ∧ (em k, v') ∈ Γ'.path r) ∧  (∀ r, Γ.noGhostPath (own r) = true → Γ'.noGhostPath r = true) ∧ (∀ j, Γ.noGhostPath j = false → ∃! r, own r = j ∧ Γ'.noGhostPath r = false) ∧  (∀ (j : Fin p) (s : Bool) (k : Fin Γ.es.length), Γ.EndAt j s k i₀ → ∃ r, own r = j ∧ Γ'.path r = [(em k, Sum.inl (Sum.inr r))] ∧ (if s = true then ea r = none ∧ eb r = some (Sum.inr j) else ea r = some (Sum.inl j) ∧ eb r = none)) ∧  Γ'.nSolid = Γ.nSolid
RBM3D/Graph/AnpKey2.lean:1885: theorem anpDetGhStep_of_reg (d : ℕ) (h : AnpDetGhRegStep d) : AnpDetGhStep d
RBM3D/Graph/AnpKey2.lean:1891: theorem anpDetGhRegStep_of_cases (d : ℕ) (hI : AnpDetGhCaseI d) (hIII : AnpDetGhCaseIII d) (hIV : AnpDetGhCaseIV d) : AnpDetGhRegStep d
RBM3D/Graph/AnpKey2.lean:318: theorem anpKey2_caseI_ne {p q : ℕ} (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (hG : Γ.GhostOK) {i : Fin q} {j₁ j₂ : Fin p} {s₁ s₂ : Bool} {k₁ k₂ : Fin Γ.es.length} (hne : (j₁, s₁) ≠ (j₂, s₂)) (h₁ : Γ.IsA1 π j₁ s₁ k₁ i ∨ Γ.IsB1 π j₁ s₁ k₁ i) (h₂ : Γ.IsA1 π j₂ s₂ k₂ i ∨ Γ.IsB1 π j₂ s₂ k₂ i) : j₁ ≠ j₂
RBM3D/Graph/AnpKey2.lean:115: theorem anpKey2_val_eq_valOn {p q : ℕ} (Γ : NGraph p q) {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ) (a b : Fin p → ι) : Γ.val ξ a b = Γ.valOn ξ a b Finset.univ
```
Compiled nonempty instances (same extraction). Premises left as hypotheses are the pins of LW-12c-f: `hreg`, `h`, `AnpDetGhCaseI/III/IV 3`, `AnpDetGhRegStep 3`:
```
RBM3D/Graph/AnpKey2.lean:1934: theorem anpKey2_inst_figAuxGh : anpKey2_figAuxGh.GhostOK ∧ anpKey2_figAuxGh.IsNested ∧ anpKey2_figAuxGh.NoA2 (fun _ _ => false) ∧ AnpCaseI anpKey2_figAuxGh (fun _ _ => false) ∧ AnpCaseIII anpKey2_figAuxGh (fun _ _ => false) ∧ anpKey2_figAuxGh.degS 1 = 2
RBM3D/Graph/AnpKey2.lean:1950: theorem anpKey2_inst_figAux_a2 : ¬ figAux.NoA2 (fun _ _ => false) ∧ figAux.IsA2 (fun _ _ => false) 0 true (anpKey2_eAux 4) 1 ∧ figAux.IsA2 (fun _ _ => false) 1 true (anpKey2_eAux 5) 1
RBM3D/Graph/AnpKey2.lean:1956: theorem anpKey2_inst_figAux_reg (hreg : ∀ Γ : NGraph 2 2, Γ.GhostOK → Γ.IsNested → Γ.NoA2 (fun _ _ => false) → AnpDetGhRegAt 3 Γ (fun _ _ => false)) : AnpDetGhRegAt 3 figAux (fun _ _ => false)
RBM3D/Graph/AnpKey2.lean:1963: theorem anpKey2_inst_cover (h : ∀ π, AnpDetGhRegAt 3 anpKey2_figAuxGh π) : AnpDetGhAt 3 anpKey2_figAuxGh
RBM3D/Graph/AnpKey2.lean:1967: theorem anpKey2_inst_chain : AnpDetGhCaseI 3 → AnpDetGhCaseIII 3 → AnpDetGhCaseIV 3 → LWAnpKeyGh 3
RBM3D/Graph/AnpKey2.lean:1973: theorem anpKey2_inst_figAux_det (h : AnpDetGhRegStep 3) : AnpDetGhAt 3 figAux
RBM3D/Graph/AnpKey2.lean:1979: theorem anpKey2_inst_half : let x : Zd 3 5 := fun _ => 0 let y : Zd 3 5 := fun _ => 2 let z : Zd 3 5 := fun _ => 1 zdistInf 3 5 (x - y) ≤ 2 * zdistInf 3 5 (z - y)
RBM3D/Graph/AnpKey2.lean:1992: theorem anpKey2_inst_reg_half : ((fun _ => anpKey2_pt 1 : Fin 1 → Zd 3 5) ∈ anpKey2_region (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2) (fun _ _ => false : Fin 1 → Fin 1 → Bool) ∧ zdistInf 3 5 (anpKey2_pt 0 - anpKey2_pt 2) ≤ 2 * zdistInf 3 5 (anpKey2_pt 1 - anpKey2_pt 2)) ∧ ((fun _ => anpKey2_pt 2 : Fin 1 → Zd 3 5) ∈ anpKey2_region (fun _ => anpKey2_pt 0) (fun _ => anpKey2_pt 2) (fun _ _ => true : Fin 1 → Fin 1 → Bool) ∧ zdistInf 3 5 (anpKey2_pt 0 - anpKey2_pt 2) ≤ 2 * zdistInf 3 5 (anpKey2_pt 2 - anpKey2_pt 0))
RBM3D/Graph/AnpKey2.lean:2014: theorem anpKey2_inst_endTypes : anpKey2_figAuxGh.IsB1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∧ (anpKey2_figAuxGh.IsA1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∨ anpKey2_figAuxGh.IsA2 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∨ anpKey2_figAuxGh.IsB1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∨ anpKey2_figAuxGh.IsB2 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0)
RBM3D/Graph/AnpKey2.lean:2024: theorem anpKey2_inst_caseI_ne : (0 : Fin 2) ≠ 1
RBM3D/Graph/AnpKey2.lean:2032: theorem anpKey2_inst_fix : ∃ (p' : ℕ) (Γ' : NGraph p' 1) (ea eb : Fin p' → Option (Fin 2 ⊕ Fin 2)) (own : Fin p' → Fin 2) (em : Fin anpKey2_figAuxGh.es.length ≃ Fin Γ'.es.length), Γ'.GhostOK ∧ Γ'.IsNested ∧ Γ'.nSolid = 4 ∧ (∃ r, own r = 0 ∧ Γ'.path r = [(em (anpKey2_eGh 0), Sum.inl (Sum.inr r))] ∧ ea r = some (Sum.inl 0) ∧ eb r = none) ∧ (∃ r, own r = 1 ∧ Γ'.path r = [(em (anpKey2_eGh 1), Sum.inl (Sum.inr r))] ∧ ea r = some (Sum.inl 1) ∧ eb r = none)
RBM3D/Graph/AnpKey2.lean:2052: theorem anpKey2_inst_fixP : anpKey2_P anpKey2_figAuxGh 0 = 4
```
Public declarations of the file, `line:name` (163; 4 private helpers: `anpKey2_foldl_none`, `anpKey2_prod_set`, `anpKey2_xi_le`, `anpKey2_single`); full statements are in the file (the 300-line limit of CLAUDE.md §6 does not allow listing them):
```
54:valOn 61:EndAt 67:IsA1 72:IsA2 77:IsB1 82:IsB2 87:NoA2 91:degS 94:anpKey2_decEndAt 97:anpKey2_decIsA1 100:anpKey2_decIsA2 103:anpKey2_decIsB1 106:anpKey2_decIsB2 109:anpKey2_decNoA2 115:anpKey2_val_eq_valOn 120:anpKey2_region 126:anpKey2_regionOne 133:anpKey2_fixLab 137:AnpDetGhRegAt 151:AnpIH 155:AnpDetGhRegStep 161:AnpCaseI 166:AnpCaseIII 171:AnpDetGhCaseI 177:AnpDetGhCaseIII 183:AnpDetGhCaseIV
191:anpDetGh_of_reg 261:anpKey2_half 269:anpKey2_reg_half 288:anpKey2_endTypes 302:anpKey2_noGhost_iff 308:anpKey2_ghostStep 318:anpKey2_caseI_ne 348:anpKey2_stepOK 352:anpKey2_chain 364:anpKey2_foldl_iff 392:anpKey2_walkOK_iff 396:anpKey2_chain_append 406:anpKey2_chain_snoc 412:anpKey2_chain_end 418:anpKey2_chain_visit 437:anpKey2_endAt_ends 467:anpKey2_ep 470:anpKey2_ep_nonneg 493:anpKey2_ep_ghostify
524:anpKey2_A2_factor 547:anpKey2_A2_val 569:anpDetGhReg_of_noA2 668:anpKey2_seg 673:anpKey2_seg_nil 675:anpKey2_seg_zero 678:anpKey2_seg_succ 681:anpKey2_seg_zero_pos 684:anpKey2_seg_zero_neg 687:anpKey2_seg_succ_pos 690:anpKey2_seg_succ_neg 693:anpKey2_seg_sublist 706:anpKey2_seg_nil_of_gt 720:anpKey2_seg_cover 740:anpKey2_seg_unique 776:anpKey2_seg_shape 799:anpKey2_seg_last 819:anpKey2_seg_snoc
842:anpKey2_seg_head 855:anpKey2_isA 857:anpKey2_isA_eq 861:anpKey2_seg_chain 904:anpKey2_K 907:anpKey2_Seg 910:anpKey2_P 913:anpKey2_ee 916:anpKey2_steps 921:anpKey2_ea 925:anpKey2_eb 930:anpKey2_own 933:anpKey2_pred 936:anpKey2_succAbove_pred 939:anpKey2_pred_succAbove 943:anpKey2_rel0 951:anpKey2_tgt 961:anpKey2_edge 966:anpKey2_es 969:anpKey2_es_length 973:anpKey2_fixV 979:anpKey2_em 984:anpKey2_steps_sublist
987:anpKey2_steps_mem_path 991:anpKey2_cover 997:anpKey2_edge_unique 1014:anpKey2_steps_chain 1020:anpKey2_steps_shape 1034:anpKey2_steps_ne_nil 1051:anpKey2_noneV 1055:anpKey2_tgt_none 1064:anpKey2_tgt_first 1094:anpKey2_tgt_last 1124:anpKey2_rel0_self 1127:anpKey2_rel0_succAbove 1133:anpKey2_rel0_ne 1141:anpKey2_noneV_ne_a 1150:anpKey2_noneV_ne_b 1159:anpKey2_noneV_ne_inr 1164:anpKey2_rel0_inj 1199:anpKey2_es_get
1203:anpKey2_ee_symm_snd 1207:anpKey2_ee_symm_fst 1211:anpKey2_ea_ee 1215:anpKey2_eb_ee 1221:anpKey2_lab 1240:anpKey2_chain_new 1286:anpKey2_seg_eq_zero 1292:anpKey2_seg_eq_last 1299:anpKey2_fixV_path 1307:anpKey2_fixV_edge 1315:anpKey2_steps_dropLast 1325:anpKey2_steps_arrival 1341:anpKey2_fixV_walk 1374:anpKey2_fixV_visits 1390:anpKey2_fixV_nested 1444:anpKey2_ghost_unique 1460:anpKey2_steps_first
1468:anpKey2_steps_last 1486:anpKey2_fixV_ghost 1491:anpKey2_fixV_ghostOK 1532:anpKey2_prod_eq 1538:anpKey2_ep_eq 1549:anpKey2_fixV_value 1599:anpKey2_fixV_steps 1624:anpKey2_fixV_noGhost1 1636:anpKey2_fixV_noGhost2 1674:anpKey2_filter_len 1684:anpKey2_nSolid_sum 1691:anpKey2_fixV_nSolid 1696:anpKey2_seg_end_nil 1704:anpKey2_fixV_end 1773:anpKey2_exists_s₀ 1784:anpKey2_ea_unique 1800:anpKey2_eb_unique
1821:anpKey2_fix 1885:anpDetGhStep_of_reg 1891:anpDetGhRegStep_of_cases 1904:anpKey2_decGhostOK 1906:anpKey2_decCaseI 1910:anpKey2_decCaseIII 1916:anpKey2_figAuxGh 1922:anpKey2_figAuxGh_ghostOK 1926:anpKey2_figAuxGh_nested 1930:anpKey2_figAux_ghostOK 1934:anpKey2_inst_figAuxGh 1942:anpKey2_eAux 1945:anpKey2_eGh 1950:anpKey2_inst_figAux_a2 1956:anpKey2_inst_figAux_reg 1963:anpKey2_inst_cover 1967:anpKey2_inst_chain
1973:anpKey2_inst_figAux_det 1979:anpKey2_inst_half 1987:anpKey2_pt 1992:anpKey2_inst_reg_half 2014:anpKey2_inst_endTypes 2024:anpKey2_inst_caseI_ne 2032:anpKey2_inst_fix 2052:anpKey2_inst_fixP
```
Name clash (`clash.py`: every public name against definitions in other `RBM3D/*.lean`, and against T2243's draft `T2243.md`, `checks/T2243-check.lean`):
```
163 distinct public names; definitions of the same name elsewhere in RBM3D/*.lean: 0
names of this file mentioned in T2243 draft (T2243.md, T2243-check.lean): 0
```
Ports: none (RBM1D/RBM2D have no light-weight graph layer); no diff-stat.
### Narrative (every statement below is backed by the output above or by the file)
- Delivered on `t/T2242` (commits 342e6c2, 0bd639a, da47890): `RBM3D/Graph/AnpKey2.lean` (2057 lines, 163 public declarations) and 8 registry lines in `RBM3D/Test/Axioms.lean` (8 insertions, no deletion). `git diff main...t/T2242` touches only these two files.
- Targets 1-6 are proved: `anpDetGh_of_reg`, `anpKey2_half`, `anpKey2_reg_half`, `anpKey2_endTypes`, `anpDetGhReg_of_noA2`, `anpKey2_fix`, `anpDetGhStep_of_reg`, `anpDetGhRegStep_of_cases`; also the unpinned `anpKey2_caseI_ne`. Each pin of the ticket is the file's definition (`rfl`) or the file's theorem (`@name`), no hypothesis added, no pinned signature changed.
- No primed successor of `AnpDetGhStep` was needed: `anpDetGhStep_of_reg` proves the merged `AnpDetGhStep` from `AnpDetGhRegStep` (target 2 for the `2^{pq}` regions, target 4 for the A2 edges), with the merged IH `AnpIH d q` passed through unchanged.
- Target 2: the regions are the fibres of `ℓ ↦ (decide (|ℓ_i - b_j| < |ℓ_i - a_j|))_{i,j}` (`Finset.sum_fiberwise`); `C = Σ_π C_π`, `c = Finset.inf'` of the `c_π`; `ψ(c_π r) ≤ ψ(c r)` by antitonicity.
- Target 4: strong induction on `nngh`. An A2 edge is the first or last step of a ghost-free path, so `ghostify` (merged) applies; `anpKey2_endAt_ends` gives its endpoints, `anpKey2_A2_val` the bound `valOn Γ ≤ ψ(|a_j - b_j|/2) · valOn (Γ.ghostify k)` on the region; the constants are `(C, min c ½)`, so repeated replacement does not accumulate.
- Target 5 (construction, `anpKey2_fixV`): `anpKey2_seg` cuts a step list after every step that arrives at `α_{i₀}`; `K j` arrivals give `K j + 1` segments and `p' = Σ_j (K j + 1)` (`anpKey2_P`, enumerated by `finSigmaFinEquiv`). The edge list of `Γ'` is `List.ofFn` of the relabelled edges, so `em` is a cast. `a_j`, `b_j` go to the start of the first / the end of the last segment of `𝔓_j`; `α_{i₀}` goes to the start (resp. end) of the segment of which the edge is the first (resp. last) step, else to the end of a fixed segment `s₀` (it exists because `α_{i₀}` lies on two paths, `anpKey2_exists_s₀`). Uniqueness of that segment is `anpKey2_edge_unique` (`IsNested` conjuncts 3-4).
- (F1)-(F8) hold for every `GhostOK`, `IsNested` graph and every `i₀`. `IsNested` conjunct 6 of `Γ'` follows from conjunct 6 of `Γ` by `Finset.card_le_card_of_surjOn` along `own`; (F7) comes from the walk property of the path (`anpKey2_walkOK_iff`) and the shape of the first and last segment (`anpKey2_seg_zero_pos`, `anpKey2_seg_snoc`, `anpKey2_seg_end_nil`). Neither is an obstruction; no counterexample was found.
- Instances (1)-(4) of the ticket are compiled (`anpKey2_inst_*`, listed above); `anpKey2_inst_fixP` computes `p' = 4` at `figAuxGh`, `i₀ = 0`.
- Registry. Added to `owedProps`: `AnpDetGhCaseI`, `AnpDetGhCaseIII`, `AnpDetGhCaseIV` (as expected by the ticket). The pre-check also listed `NGraph.EndAt`, `IsA1`, `IsA2`, `IsB1`, `NoA2` (predicates that define the objects, like `IsNested`, `NoGhost`, `GhostOK` next to them): added to `structuralProps`, not to the owed table as the ticket's text says. `AnpDetGhRegStep` was not listed (it is proved by `anpDetGhRegStep_of_cases`), nor was `NGraph.IsB2`.
- The file has 2057 lines, above the ticket's estimate 1250-1550; the 1500-line stop rule applied to the stage-1a estimate, and section (a) contains none.

## (c) Verified Mathlib names
`used_scan.lean`: regex over the source for dotted/underscored identifiers (tactic words `by_cases`, `by_contra`, `norm_num` excluded), then `env.contains`; split by the defining module root. Names without `_` or `.` are not in the scan (`finSigmaFinEquiv`: below).
```
Mathlib names used (resolved by full name in the source): 62
Equiv.prod_comp Equiv.sum_comp Equiv.symm_apply_apply Fin.exists_succAbove_eq Fin.insertNth Fin.insertNthEquiv Fin.insertNth_apply_same Fin.insertNth_apply_succAbove Fin.succAbove_ne Fin.succAbove_right_injective Finset.card_image_of_injective Finset.card_le_card_of_surjOn Finset.coe_filter Finset.filter_mem_eq_inter Finset.inf'_le Finset.lt_inf'_iff Finset.mem_filter Finset.mem_univ Finset.mul_sum Finset.prod_congr Finset.prod_le_prod₀ Finset.prod_mul_distrib Finset.prod_nonneg Finset.sum_congr Finset.sum_fiberwise Finset.sum_filter Finset.sum_le_sum Finset.sum_le_sum_of_subset_of_nonneg Finset.sum_mul Finset.sum_pos Finset.univ Finset.univ_inter Fintype.sum_prod_type List.get_ofFn List.inj_on_of_nodup_map List.mem_of_mem_dropLast List.ofFn_getElem_eq_map List.prod_nonneg List.prod_ofFn List.sum_ofFn Nat.cast_nonneg Nat.strong_induction_on Set.Ici Set.mem_ofPred_eq le_of_eq le_refl le_rfl lt_min min_le_left min_le_right mul_assoc mul_comm mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_nonneg mul_one nonpos_iff_eq_zero one_mul pow_pos zero_add zero_le_one zpow_pos
core/Std names used (resolved by full name): 71
Bool.false_eq_true Bool.false_ne_true Bool.noConfusion Classical.choose Classical.choose_spec Fin.cast Fin.ext Fin.last Fin.val_last Fin.val_zero Function.Injective List.Nodup.sublist List.all_eq_true List.cons_append List.countP_append List.countP_cons_of_neg List.countP_cons_of_pos List.countP_nil List.dropLast_concat List.dropLast_cons_of_ne_nil List.eq_nil_or_concat List.filter_map List.foldl_cons List.getElem_cons_succ List.getLast?_cons_cons List.get_mem List.head?_cons List.length_cons List.length_map List.length_nil List.length_ofFn List.map_cons List.map_map List.map_nil List.mem_append_right List.mem_cons List.mem_cons_of_mem List.mem_cons_self List.mem_of_getLast? List.mem_of_mem_head? List.mem_singleton List.mem_singleton_self List.nil_sublist List.not_mem_nil List.ofFn List.prod_cons List.set List.set_cons_succ List.subperm_of_subset Nat.le_of_lt_succ Nat.lt_succ_of_le Nat.lt_succ_self Nat.zero_le Option.bind Option.bind_some Option.some.injEq Or.inl Or.inr Prod.fst Prod.mk.inj Sum.elim Sum.elim_inr Sum.inl Sum.inl.inj Sum.inr Sum.inr.inj Sum.inr.injEq ite_false ite_true or_false true_and
OK  finSigmaFinEquiv : {m : ℕ} → {n : Fin m → ℕ} → (i : Fin m) × Fin (n i) ≃ Fin (∑ i, n i)
this Mathlib, not used: if_pos (deprecated); if_neg (deprecated); dif_pos (deprecated); dif_neg (deprecated); dite_cond_eq_true (deprecated); List.Sublist.cons₂ (deprecated); Set.mem_setOf_eq (deprecated); absent: push_neg; Finset.prod_le_prod (present, not deprecated)
```

## (d) Open issues and paper-delta candidates
1. Registry classification (see narrative): the five predicates `NGraph.EndAt`, `IsA1`, `IsA2`, `IsB1`, `NoA2` are registered as structural, not owed; the dispatcher can move them (lines `RBM3D/Test/Axioms.lean:287-291`).
2. For LW-12c-f the file exports: `anpKey2_fix` (F1-F8), `anpKey2_caseI_ne`, `anpKey2_endAt_ends`, `anpKey2_walkOK_iff` and the walk lemmas `anpKey2_chain*`, the edge-product lemmas `anpKey2_ep`, `anpKey2_ep_eq`, `anpKey2_ep_ghostify`, `anpKey2_ep_nonneg`, `anpKey2_A2_factor`, `anpKey2_A2_val`, and the instances `anpKey2_inst_*`. The ending edges at the fixed vertex are one-step paths (F7), as the ticket's notes for LW-12c assume.
3. Paper-delta candidates (temporary tags):
   - T2242a: regions and ending-edge types are combinatorial data (`π : Fin q → Fin p → Bool`, side bit `s`); A1 at either end is `π i j = s`, A2 is `π i j = !s`; the regions partition the torus exactly (the paper: "at most `2^{pq}` subregions" that cover).
   - T2242b: "the two ending edges belong to distinct paths" (`7_8:1157`) is `anpKey2_caseI_ne`, from `GhostOK` and the type definitions (A1+A1 on one path would need `π i j = false` and `= true`; B1+B1 contradicts "the ghost is an ending edge").
   - T2242c: vertex fixing at an arbitrary `α_{i₀}` (no WLOG `α_q`), all edges kept (`em` is a bijection); every path is cut at every arrival at `α_{i₀}` (`k_j + 1` segments, also for `j ∈ {1,2}`), whereas the paper's Case (II) removes `(a_1,α_q)`, `(a_2,α_q)` and has `k_j` segments for `j ∈ {1,2}` (`7_8:1209-1237`); one statement serves Cases (I) and (II).
   - T2242d: the A2 replacements (`7_8:1143-1148`, "it is easy to see") cost `c ↦ min c ½` in total: each replacement applies `min · ½`, which is idempotent, so nothing accumulates over the (at most `p`) edges; the bound used is pointwise on the region, `valOn Γ ≤ ψ(|a_j - b_j|/2) · valOn Γ̃`.
   - T2242e: the induction hypothesis is the merged one (all `k < q`, any `p`, any number of edges; ticket header, T2234-audit §8) instead of "at most `K` solid edges" (`7_8:1107`).
