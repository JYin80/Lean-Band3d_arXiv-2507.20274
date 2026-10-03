Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 19:38:10 UTC 2026

Targets (RBM2D `c9a24cf`, 13 files -> `RBM3D/Hierarchy/ContractionSecondLoop.lean`): exact finite-matrix identities at a fixed sample
`(u, ω, z)`: coordinate contractions `Σ_γ gvarF·tr(… B_γ … B_γ …)` = `W^d·ΣΣ loopL·SB·loopL`, and list combinatorics of edge/pair splits.
No probability, no estimate, no external hypothesis: every hypothesis is deterministic (`0 ≤ u`, `σ.length = a.length`, `NeZero L, W`).

### (i) Exponent table

| # | Quantity | Value at d ≥ 3 | Constraint | Slack |
|---|---|---|---|---|
| 1 | contraction coefficient (every `(W:ℂ)^2` of the 13 files) | `(W:ℂ)^d` | `svarF = W^{-d}·SBR` (FineModel.lean:47) and `Eblk` entry `W^{-d}` (GLoop.lean:55): `W^{-d} / (W^{-d})² = W^d`; matches merged `sum_allCoords_trace_blocks` (ContractionBasic.lean:619) | none: equality; check (ii) shows `W²` is off by exactly `W^{d-2}=2` at d=3 |
| 2 | second-derivative factor | `2` (`d²G = 2GBGBG`, LoopCoordinate.lean:259) | dimension-free | exact |
| 3 | pair-sum factor | `coordinateSecondWordDeriv = same + 2•pair` (each unordered pair once) | dimension-free; coefficient `2uW^d` for same-edge, `uW^d` per ordered pair then ×2 | exact (checked in (ii)) |
| 4 | `u` factor | `(√u)² = u` | needs `0 ≤ u` (`Real.mul_self_sqrt`); `u=3/5` | any `u ≥ 0` |
| 5 | index/type renames | `Z2 L→Zd d L`, `BlockIndex L W→Vtx d L W`, `Coord→CoordF d L W`, `gvar→gvarF d L W g`, `SB L→SB d L g`, `Gsig H z s→Gres H z s`, `gloop→loopL`, `LoopIdx (Z2 L)→Loop.LoopIdx (Zd d L)` | new real parameter `g` (law/variance carry it); no hypothesis on `g` in ContractionBasic.lean:619,709 | `g=1/2` in (ii) |
| 6 | lattice sizes | `N=(WL)^d`, block fibre `Fin (W^d)`, `3 ≤ L` | only inside the merged `split`/`SB`; the 13 files use none of `L^d, N, ell, scale` (count below: other tokens 0) | d=3,L=3,W=2: N=216 |
| 7 | cut positions | `k=|σ₁|+1`, `l=|σ₁|+|σ₂|+2`, `1≤k<l≤n` | `n=|σ₁|+|σ₂|+|σ₃|+2` | n=3 and n=6 in (ii) |

Occurrences of `d=2` tokens per source file (command `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2065/count.py`, git show of each file at `c9a24cf`; equals portmap columns W2/Z2 of T2015-portmap.md rows 65-77):
```
  SecondLoop                     (W:C)^2=3 Z2=21 other-d=2-tokens=0
  SecondLoopSameEdge             (W:C)^2=2 Z2=6 other-d=2-tokens=0
  SecondLoopSameEdgeWord         (W:C)^2=1 Z2=4 other-d=2-tokens=0
  SecondLoopSameEdgeCut          (W:C)^2=1 Z2=7 other-d=2-tokens=0
  EdgeSplits                     (W:C)^2=0 Z2=0 other-d=2-tokens=0
  PairSplits                     (W:C)^2=0 Z2=0 other-d=2-tokens=0
  FirstDerivativePositionSum     (W:C)^2=0 Z2=4 other-d=2-tokens=0
  SecondDerivativePositionSum    (W:C)^2=0 Z2=12 other-d=2-tokens=0
  SecondDerivativeTraceSum       (W:C)^2=0 Z2=1 other-d=2-tokens=0
  PositionLoopBridge             (W:C)^2=0 Z2=7 other-d=2-tokens=0
  SameEdgePositionCut            (W:C)^2=2 Z2=7 other-d=2-tokens=0
  PairPositionCut                (W:C)^2=2 Z2=11 other-d=2-tokens=0
  SecondLoopAllCuts              (W:C)^2=6 Z2=12 other-d=2-tokens=0
```
Per-statement verdict (dimension-specific -> replacement; the rest is dimension-free):
- `W^2 → W^d` (coefficient only): SecondLoop: `sum_twoEdge_mixed_cutChains`, `_coordinate`, `sum_twoEdge_mixed_deriv` (3); SameEdge: `sum_coordinateBlock_trace_pair`, `sum_gsigCoordinateSecondDeriv_Eblk` (2); SameEdgeWord: `sum_gsigCoordinateSecondDeriv_word` (1); SameEdgeCut: `sum_sameEdge_cutLoops` (1); SameEdgePositionCut: `sum_coordinateSameEdgeTerm_cutLoops`, `_of_mem` (2); PairPositionCut: `sum_coordinatePairTerm_cutLoops`, `_of_mem` (2); AllCuts: `sum_coordinateSecondWordDeriv_allCuts` (2 + 2 in its `change`), `sum_gloopSecondWordDeriv_allCuts` (2): total 19.
- Dimension-free (no `W`, only `Z2→Zd d` as index type): `EdgeSplit/edgeSplits/edgeSplits_unique_position`, `PairSplit/pairSplits/pairSplits_unique_positions` (generic `α`, lists only, no `Z2` at all); `coordinateWordDeriv_eq_edgeSplits_sum`, `coordinateSecondWordDeriv_eq_position_sums`, `sum_coordinateSecondWordDeriv_trace_positions` (matrix/list identities, product rule); `segmentLoopIdx*`, `coordinateWordProduct_eq_gloopProd`, `edgeSplit/pairSplit_segment_products`; `trace_gsigCoordinateSecondDeriv_Eblk/_word` (coefficient `2u`, no `W`); `trace_sameEdge_cutLoop/oneLoop`, `trace_twoEdge_mixed_eq_cutChains`.
- No statement is false at d ≥ 3 as ported after the renames; none needs a changed exponent beyond row 1.
- `ContractionSecondLoopReverse` (42 lines, imported by SameEdge) is not among the 13 files; `git grep` at `c9a24cf` finds its theorem `coordinateSecondWordDeriv_two_edges` only in its own file and the import line in SameEdge: no consumer, dropped (paper-delta candidate: none, statement-level nothing lost).

### (ii) One concrete nondegenerate instance (d=3, L=3, W=2)
Data: `d=3, L=3 (3≤L), W=2` so `N=(WL)^3=216`, block fibre `Fin 8`, `|Zd 3 3|=27`; `g=1/2, u=3/5, z=0.3+0.7i` (`Im z≠0`); sample `ω` Gaussian with the model variances `gvarF` on all `93312=2·216²` coordinates (46656 used); `z` spectral, `H=√u X` Hermitian (asserted).
Loop of length 3: `σ₁=[], σ₂=[−], σ₃=[], s=+, t=−`, labels `a₂=[lab 2], a=lab 5, c=lab 1` (cuts `k=1, l=3`, length hypotheses `0=0, 1=1`); second sample, length 6: `σ₁=[+], σ₂=[−,+], σ₃=[+]`.
Both sides use the literal definitions: `LHS=Σ_γ gvarF·tr(P (D_s E_a) M (D_t E_c) T)`, `D=−G(√u B_γ)G`, `B_γ` = Xmat(Pi.single γ 1) read through `split`; `RHS=u W^d ΣΣ loopL(cutGlueL p)·SB p q·loopL(cutGlueR q)` with `cutGlueL/R` as `take/drop` of Loop/TreeRep.lean:84-91. Dense `P(D_s E_a)M(D_t E_c)T` is compared with the sparse trace form on 3 coordinates (asserts, tolerance 1e-10). Extra checks: same-edge word identity (`2uW^d`), and recursive `coordinateSecondWordDeriv` vs `same + 2•pair` vs a 5-point second `t`-derivative on one coordinate.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2065/check.py`
```
  coordinates: 93312 used: 46656
  sum_twoEdge_mixed_deriv [length 3, n=3]  LHS=-0.0000080526-0.0000449884j  RHS=-0.0000080526-0.0000449884j  rel.diff=1.4e-15  |RHS|=4.570e-05  nonzero (p,q) terms=189/729
    LHS/(RHS with W^2 in place of W^d) = 2.000000  (= W^(d-2) = 2)
  sum_twoEdge_mixed_deriv [length 6, n=6]  LHS=-0.0000000000-0.0000000000j  RHS=-0.0000000000-0.0000000000j  rel.diff=2.6e-15  |RHS|=1.690e-16  nonzero (p,q) terms=189/729
    LHS/(RHS with W^2 in place of W^d) = 2.000000  (= W^(d-2) = 2)
  sum_gsigCoordinateSecondDeriv_word  LHS=-0.0000000166-0.0000000222j  RHS=-0.0000000166-0.0000000222j  rel.diff=2.4e-16  |RHS|=2.773e-08
  coordinateSecondWordDeriv_eq_position_sums |rec-(same+2 pair)| = 1.41e-23 (|rec|max=6.05e-08)
  2nd t-derivative (5-pt stencil, h=0.05) vs recursion: max|diff| = 3.61e-13
```
Reading: relative error ≤ 2.6e-15 on LHS=RHS (both nonzero; 189 of 729 `(p,q)` terms nonzero, not a collapsed sum; the `1e-16` size at n=6 is the `(W^{-d})^n` weights of `Eblk`, not a zero). The `W²` variant is off by the factor `W^{d-2}=2`, so row 1 has no slack. `edgeSplits`/`pairSplits` on a 3-edge word give 3 and 3 splits, prefix lengths `[0,1,2]` (asserted in the script).
External hypotheses: none (nothing taken from `Step2LocalPT`-type pins; all targets are deterministic identities), so no limit computation applies.

### Verdict
- ContractionSecondLoop (`sum_twoEdge_mixed_deriv`), SameEdge, SameEdgeWord, SameEdgeCut, EdgeSplits, PairSplits, FirstDerivativePositionSum, SecondDerivativePositionSum, SecondDerivativeTraceSum, PositionLoopBridge, SameEdgePositionCut, PairPositionCut, SecondLoopAllCuts: **PASS** (hypotheses satisfiable at the instance; the only exponent change is `W²→W^d`; checked numerically at d=3).

## (a′) Preflight corrections — Sat Oct  3 19:48:58 UTC 2026
- Section (a), (i), line "Per-statement verdict", `W^2 → W^d` total: the listed counts 3+2+1+1+2+2+6 sum to 17, not 19. Command `python3` count over the 13 sources at `c9a24cf`: 17 occurrences of `(W : ℂ) ^ 2`; the port has 17 of `(W : ℂ) ^ d`. No verdict changes.


## (b) Script output — Sat Oct  3 19:48:34 UTC 2026

Branch `t/T2065`, commit `4a1433e`; one new file `RBM3D/Hierarchy/ContractionSecondLoop.lean` (1390 lines); `RBM3D/Test/Axioms.lean` unchanged (no registry line: see narrative).

```
$ lake build RBM3D.Hierarchy.ContractionSecondLoop 2>&1 | tail -3
Build completed successfully (3299 jobs).
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Hierarchy/ContractionSecondLoop.lean | wc -l
       0
$ git diff main...t/T2065 --stat | tail -3
 RBM3D/Hierarchy/ContractionSecondLoop.lean | 1390 ++++++++++++++++++++++++++++
 1 file changed, 1390 insertions(+)
```

Axioms of every public declaration (`#print axioms`, scratch file `scratchpad/T2065/axioms.lean`, grouped by script):
```
$ lake env lean scratchpad/T2065/axioms.lean | grep -v '^$' | sed -E "s/^'RBM\.Gauss\.//; s/' (depends on axioms|does not depend on any axioms)/ \1/" | awk '{n=$1; $1=""; g[$0]=g[$0] " " n; c[$0]++} END {for (k in g) print c[k] " decl:" k " <-" g[k]}'
35 decl: depends on axioms: [propext, Classical.choice, Quot.sound] <- trace_twoEdge_mixed_eq_cutChains sum_twoEdge_mixed_cutChains sum_twoEdge_mixed_coordinate sum_twoEdge_mixed_deriv sum_coordinateBlock_trace_pair trace_gsigCoordinateSecondDeriv_Eblk sum_gsigCoordinateSecondDeriv_Eblk trace_gsigCoordinateSecondDeriv_word sum_gsigCoordinateSecondDeriv_word trace_sameEdge_cutLoop trace_sameEdge_oneLoop sum_sameEdge_cutLoops edgeSplits_unique_position pairSplits_positions_valid pairSplits_unique_positions coordinateWordProduct coordinateEdgeTerm coordinateWordDeriv_eq_edgeSplits_sum coordinateSameEdgeTerm coordinatePairTerm coordinateSameEdgeSum coordinatePairSum coordinateSecondWordDeriv_eq_position_sums sum_coordinateSecondWordDeriv_trace_positions coordinateWordProduct_eq_gloopProd edgeSplit_segment_products pairSplit_segment_products sum_coordinateSameEdgeTerm_cutLoops sum_coordinateSameEdgeTerm_cutLoops_of_mem sum_coordinatePairTerm_cutLoops sum_coordinatePairTerm_cutLoops_of_mem sameEdgeCutValue pairCutValue sum_coordinateSecondWordDeriv_allCuts sum_gloopSecondWordDeriv_allCuts
5 decl: does not depend on any axioms <- EdgeSplit edgeSplits PairSplit pairSplits segmentLoopIdx
3 decl: depends on axioms: [propext, Quot.sound] <- edgeSplits_reconstruct edgeSplits_prefix_lengths pairSplits_reconstruct
2 decl: depends on axioms: [propext] <- segmentLoopIdx_WF segmentLoopIdx_zip_eq
```

Key target statements, extracted from the file by script (`awk` from the `theorem` line to `:=`):
```
$ awk '/^theorem sum_twoEdge_mixed_deriv( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem sum_twoEdge_mixed_deriv
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let M := gloopProd d L W H z ⟨σ₂, a₂⟩
    let T := gloopProd d L W H z ⟨σ₃, a₃⟩
    (∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (P *
          (gsigCoordinateDeriv d L W u ω γ z s * Eblk d L W a) * M *
          (gsigCoordinateDeriv d L W u ω γ z t * Eblk d L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SB d L g p q *
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
$ awk '/^theorem sum_gsigCoordinateSecondDeriv_Eblk( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem sum_gsigCoordinateSecondDeriv_Eblk
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W)
    (z : ℂ) (s : Bool) (a : Zd d L) :
    let G := Gres (HflowBlock d L W u ω) z s
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (gsigCoordinateSecondDeriv d L W u ω γ z s * Eblk d L W a)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace ((G * Eblk d L W a * G) * Eblk d L W p) * SB d L g p q *
          Matrix.trace (G * Eblk d L W q) := by
$ awk '/^theorem sum_gsigCoordinateSecondDeriv_word( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem sum_gsigCoordinateSecondDeriv_word
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W)
    (z : ℂ) (s : Bool) (a : Zd d L)
    (P T : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    let G := Gres (HflowBlock d L W u ω) z s
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv d L W u ω γ z s *
          Eblk d L W a) * T)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace ((((G * Eblk d L W a * T * P) * G) * Eblk d L W p)) *
          SB d L g p q * Matrix.trace (G * Eblk d L W q) := by
$ awk '/^theorem sum_sameEdge_cutLoops( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem sum_sameEdge_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let T := gloopProd d L W H z ⟨σ₂, a₂⟩
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv d L W u ω γ z s *
          Eblk d L W a) * T)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        loopL d L W H z
          ⟨s :: (σ₂ ++ (σ₁ ++ [s])), a :: (a₂ ++ (a₁ ++ [p]))⟩ *
          SB d L g p q * loopL d L W H z ⟨[s], [q]⟩ := by
$ awk '/^theorem edgeSplits_unique_position( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem edgeSplits_unique_position {α : Type*} (l : List α)
    (i : ℕ) (hi : i < l.length) :
    ∃! e : EdgeSplit α, e ∈ edgeSplits l ∧ e.before.length = i := by
$ awk '/^theorem pairSplits_unique_positions( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem pairSplits_unique_positions {α : Type*} (l : List α)
    (i j : ℕ) (hij : i < j) (hj : j < l.length) :
    ∃! p : PairSplit α,
      p ∈ pairSplits l ∧ p.before.length = i ∧
        p.before.length + 1 + p.middle.length = j := by
$ awk '/^theorem coordinateWordDeriv_eq_edgeSplits_sum( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem coordinateWordDeriv_eq_edgeSplits_sum
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    coordinateWordDeriv d L W u ω γ z l =
      ((edgeSplits l).map (coordinateEdgeTerm d L W u ω γ z)).sum := by
$ awk '/^theorem coordinateSecondWordDeriv_eq_position_sums( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem coordinateSecondWordDeriv_eq_position_sums
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    coordinateSecondWordDeriv d L W u ω γ z l =
      coordinateSameEdgeSum d L W u ω γ z l +
        (2 : ℕ) • coordinatePairSum d L W u ω γ z l := by
$ awk '/^theorem sum_coordinateSecondWordDeriv_allCuts( |$)/{p=1} p{print} p&&/(:= by|:=)$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
theorem sum_coordinateSecondWordDeriv_allCuts
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    ∑ γ : CoordF d L W,
      (((gvarF d L W g γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv d L W u ω γ z l)) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ((edgeSplits l).map (sameEdgeCutValue d L W g u ω z)).sum +
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ((pairSplits l).map (pairCutValue d L W g u ω z)).sum := by
```

Port provenance (RBM2D read-only, `git show`; nothing written there):
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the 13 RBM2D/Hierarchy/Contraction*.lean files>
 RBM2D/Hierarchy/ContractionEdgeSplits.lean         | 17 +-----
 RBM2D/Hierarchy/ContractionPairPositionCut.lean    | 27 ---------
 RBM2D/Hierarchy/ContractionPairSplits.lean         | 58 -------------------
 RBM2D/Hierarchy/ContractionPositionLoopBridge.lean | 34 -----------
 .../Hierarchy/ContractionSameEdgePositionCut.lean  | 22 --------
 RBM2D/Hierarchy/ContractionSecondLoopAllCuts.lean  | 30 ----------
 RBM2D/Hierarchy/ContractionSecondLoopSameEdge.lean | 66 +---------------------
 7 files changed, 2 insertions(+), 252 deletions(-)
$ python3 scratchpad/T2065/stmt_diff.py   # statements of RBM2D after the rename map vs this file
DIFF sum_coordinateSecondWordDeriv_allCuts token changes (2D renamed -> 3D): [('', '->', 'g'), ('', '->', 'g')]
identical after renaming: 44 different: 1 ported public names in 2D: 45
2D public declarations not in 3D file: []
```

Name-clash grep of every new public name against RBM3D outside this file (count of whole-word hits; none printed means none):
```
$ for n in <the 45 public names>; do grep -rnw $n RBM3D --include='*.lean' | grep -v <this file> | wc -l; done | awk '$2>0' | wc -l
       0
```

Compiled nonempty instances (section 14 of the file; `example`s at `d=3, L=3, W=2, g=u=1/2, z=i`, flow matrix `HflowBlock 3 3 2 (1/2) ω` with `ω` a variable sample):
```
$ grep -c '^example' RBM3D/Hierarchy/ContractionSecondLoop.lean
24
$ awk '/^\/-- `sum_twoEdge_mixed_deriv`/{p=1} p{print} p&&/rfl rfl$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
/-- `sum_twoEdge_mixed_deriv`. -/
example (ω : Ω 3 3 2) :=
  sum_twoEdge_mixed_deriv 3 3 2 (1 / 2) (1 / 2) (by norm_num) ω Complex.I
    [true, false] [false, true] [true] [lab 4, lab 17] [lab 9, lab 22] [lab 0]
    true false (lab 5) (lab 2) rfl rfl
$ awk '/^\/-- `edgeSplits_reconstruct`, /{p=1} p{print} p&&/by simp \[word3\]\)⟩$/{exit}' RBM3D/Hierarchy/ContractionSecondLoop.lean
/-- `edgeSplits_reconstruct`, `edgeSplits_prefix_lengths`, `edgeSplits_unique_position`. -/
example : e1.before ++ e1.selected :: e1.after = word3 ∧
    (edgeSplits word3).map (fun e => e.before.length) = List.range word3.length ∧
    ∃! e : EdgeSplit (Bool × Zd 3 3), e ∈ edgeSplits word3 ∧ e.before.length = 1 :=
  ⟨edgeSplits_reconstruct word3 e1 e1_mem, edgeSplits_prefix_lengths word3,
    edgeSplits_unique_position word3 1 (by simp [word3])⟩
```

Registry pre-check (ST1-COMMON item 8): scratch file `scratchpad/T2065/precheck.lean` = `import RBM3D`, `import RBM3D.Hierarchy.ContractionSecondLoop`, `#assert_rbm_axioms`:
```
$ lake env lean scratchpad/T2065/precheck0.lean | head -1   # same without the new import
axiom audit: 2231 theorems, 990 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean scratchpad/T2065/precheck.lean | head -3; tail -2
axiom audit: 2280 theorems, 1017 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
non-vacuity certificates: 4 of 89 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
exit=0
```

### Narrative
- One new file, 13 sections `/-! ## n. ... -/` in the RBM2D import order, all in namespace `RBM.Gauss` (RBM2D's `SecondLoop`, `SameEdge`, ... were partly in `RBM`; in RBM3D the merged vocabulary `Gres`, `loopL`, `Eblk`, `cutLeftChain` sits in `RBM.Gauss`).
- Renames as in the (a) table: `Z2 L -> Zd d L`, `BlockIndex L W -> Vtx d L W`, `Coord -> CoordF`, `gvar -> gvarF d L W g`, `SB L -> SB d L g`, `Gsig -> Gres`, `gloop -> loopL`, `(W:C)^2 -> (W:C)^d`. The merged parameter `g` is a section variable `(g : ℝ)`; it is explicit exactly in the declarations whose statement mentions `gvarF` or `SB` (hence `sameEdgeCutValue d L W g`, `pairCutValue d L W g`, the only statement-level residual in the diff above, token `g`).
- Duplicated private helpers of the 2D files (`trace_blockRelabel*`, `blockRelabel_mul*`, `trace_coordinateBlock_pair*`, `trace_two_smul*`, `sum_map_mul_left`) are kept once as `private`. The merged private `gloopProd_cons/nil/append`, `loopL = trace gloopProd` are re-proved privately with the stem `secondLoop_` (as ContractionBasic does with `contraction_`).
- Dropped: `RBM2D/Hierarchy/ContractionSecondLoopReverse` (`coordinateSecondWordDeriv_two_edges`, 42 lines, not among the 13): `git grep` at `c9a24cf` finds it only in its own file, the import in `SameEdge`, `RBM2D.lean`, the blueprint and docs; no Lean consumer.
- `edgeSplits`, `pairSplits` and their lemmas are generic in `α` and dimension-free. The coefficient `W^d` was checked in (a)(ii) numerically (LHS/RHS = 1 at d=3, `W^2` off by `W^(d-2) = 2`).
- Hypotheses of all targets are deterministic (`0 <= u`, length equalities, membership in `edgeSplits`/`pairSplits`, `WF`); every one is discharged in the 24 examples. No `Prop`-valued predicate on sample, matrix or parameters occurs, so no `RBM3D/Test/Axioms.lean` registry line is needed and that file is untouched.
- The examples take `omega : Omega 3 3 2` as a variable (any sample), `u = 1/2`, `z = i`, block labels `lab n : Zd 3 3` with distinct values, loop length 7 with cuts `k = 3, l = 6`; edge/pair splits at a 3-edge word of `Zd 3 3` labels.
- The full `lake build` in the worktree does not see the new module (root import is added by the hub); the registry pre-check (`import RBM3D` + the module + `#assert_rbm_axioms`, exit 0) does: 2231 -> 2280 theorems.

## (c) Verified Mathlib names used (all `#check`ed in `scratchpad/T2065/chk.lean`, 0 errors)
`Equiv.sum_comp`, `Finset.mul_sum`, `Finset.sum_add_distrib`, `Finset.sum_congr`, `List.eq_nil_of_length_eq_zero`, `List.flatMap_map`, `List.map_flatMap`, `List.mem_flatMap`, `List.inj_on_of_nodup_map`, `List.nodup_range`, `List.range_succ_eq_map`, `List.map_fst_zip`, `List.map_snd_zip`, `List.zip_cons_cons`, `List.sum_append`, `Matrix.submatrix_mul_equiv`, `Matrix.trace_add`, `Matrix.trace_mul_comm`, `Matrix.trace_smul`, `Matrix.trace_zero`, `Real.mul_self_sqrt`. Names verified absent: none needed.

## (d) Open issues and paper-delta candidates
- T2065a: all 17 contraction coefficients `W^2` of the 13 RBM2D files become `W^d` (the coefficient of the merged `sum_allCoords_trace_blocks`, T2032); the statements carry the real parameter `g` of `svarF`/`SB` (RBM2D had none). No other statement differs after renaming (script diff above).
- T2065b: `ContractionSecondLoopReverse` is not ported (no consumer); a later ticket that needs `coordinateSecondWordDeriv_two_edges` must request it.
- Open issues: none. No target is unproved; no hypothesis was added, weakened or changed.
