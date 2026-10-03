Auditor model: claude-opus-5-5
# T2065 audit (S1-04, second-derivative contraction of loops) — Sat Oct  3 19:52:41 UTC 2026

Branch `t/T2065` = `4a1433e` (merge-base `ed199e7`; main now `bbd22a5`). Audit worktree `RBM3D-wt/T2065-audit1` (detached at `4a1433e`).
Scratch: `scratchpad/T2065/{src2d/*.lean, adiff.py, defdiff.py, ax.lean, pre.lean}`; RBM2D read only with `git show c9a24cf:...`.

## 1. Statements (pin = RBM2D `c9a24cf` statements after ST1-COMMON item 2 renames, `W^2 -> W^d`)
Script `adiff.py`: extracts every public `theorem/def/structure` header up to `:=`/`where` from the 13 RBM2D files and from the RBM3D file, maps 2D by
`Gauss./RBM.` stripped, `Z2 L->Zd d L`, `BlockIndex->Vtx`, `Coord->CoordF`, `gvar->gvarF d L W g`, `Gsig->Gres`, `gloop->loopL`, `LoopIdx->Loop.LoopIdx`,
`L W->d L W`, `segmentLoopIdx L->segmentLoopIdx d L`, `SB L->SB d L g`, `(W : ℂ) ^ 2->(W : ℂ) ^ d`, and token-diffs.
```
$ python3 adiff.py <scratch> RBM3D/Hierarchy/ContractionSecondLoop.lean
DIFF ContractionSecondLoopAllCuts sum_coordinateSecondWordDeriv_allCuts [('insert', '', 'g'), ('insert', '', 'g')]
2D public decls: 45 identical after rename: 44 different: 1
2D decls missing in 3D: []
3D public decls: 45 not in 2D: []
```
Residual: `sameEdgeCutValue d L W g …`, `pairCutValue d L W g …` take the merged variance parameter `g` explicitly, because their bodies contain `SB d L g`
(2D `SB L` had none). This is the merged vocabulary's parameter (R4, ST1-COMMON item 11), not a change of the statement.
Definition bodies (script `defdiff.py`, whole body to the next blank line, same renames):
```
EdgeSplit IDENTICAL / edgeSplits IDENTICAL / PairSplit IDENTICAL / pairSplits IDENTICAL / coordinateWordProduct IDENTICAL
coordinateEdgeTerm IDENTICAL / coordinateSameEdgeTerm IDENTICAL / coordinatePairTerm IDENTICAL / coordinateSameEdgeSum IDENTICAL
coordinatePairSum IDENTICAL / segmentLoopIdx IDENTICAL / sameEdgeCutValue IDENTICAL / pairCutValue IDENTICAL
```
(output lines joined with ` / ` for length; 13 lines, all `IDENTICAL`.)

Coefficient `W^d` against the merged vocabulary (signatures read):
```
FineModel.lean:47   def svarF (i j : Idx d L W) : ℝ := ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1
FineModel.lean:89   def gvarF (c : CoordF d L W) : ℝ≥0 := ⟨if c.1 = c.2.1 then svarF … else svarF … / 2, …⟩
GLoop.lean:55       def Eblk (a : Zd d L) … := Matrix.diagonal fun x => if x.1 = a then ((W : ℂ) ^ d)⁻¹ else 0
ContractionBasic.lean:619 sum_allCoords_trace_blocks : ∑ c, gvarF·tr(A·coordinateMatrix c·C·coordinateMatrix c)
                          = (W : ℂ) ^ d * ∑ a, ∑ b, tr(blockRelabel A * Eblk a) * SB d L g a b * tr(blockRelabel C * Eblk b)
```
So `W^{-d}` (variance) / `(W^{-d})^2` (two `Eblk`) = `W^d`: the `d`-dimensional exponent of RBM2D's `W^2`, as the paper's `S_xy = W^{-d} S^(B)_{ab}`
(`(eq:variancematrix)`). Preflight (a)(ii) numerics at d=3, L=3, W=2 agree (rel.diff ≤ 2.6e-15; `W^2` variant off by `W^{d-2}=2`).
No hypothesis `3 ≤ d` is needed: every target is an exact finite identity valid for all `d`; the split/pair lemmas are generic in `α` (dimension-free).
Quantifiers/hypotheses of the key targets (extracted in the prove report (b), re-read in the file at lines 198, 280, 347, 462, 537, 632, 693, 843, 1173):
`u ≥ 0`, `σᵢ.length = aᵢ.length`, `i < l.length`, `i < j < l.length`, membership in `edgeSplits`/`pairSplits`, `I.WF` — identical to RBM2D (diff above).
Cut indices `(σ₁.length + 1) (σ₁.length + σ₂.length + 2)` and sum ranges `∑ p q : Zd d L`, `∑ γ : CoordF d L W` unchanged.

Dropped declaration: `RBM2D/Hierarchy/ContractionSecondLoopReverse.lean` (not among the ticket's 13 files, not in portmap P.7):
```
$ git -C ../RBM2D --no-optional-locks grep -n "coordinateSecondWordDeriv_two_edges\|ContractionSecondLoopReverse" c9a24cf -- '*.lean'
c9a24cf:RBM2D.lean:145:import RBM2D.Hierarchy.ContractionSecondLoopReverse
c9a24cf:RBM2D/Hierarchy/ContractionSecondLoopReverse.lean:24:theorem coordinateSecondWordDeriv_two_edges
c9a24cf:RBM2D/Hierarchy/ContractionSecondLoopSameEdge.lean:6:import RBM2D.Hierarchy.ContractionSecondLoopReverse
```
No Lean consumer at `c9a24cf`; it is outside the ticket's file list, so not a target. Recorded as T2065b in the prove report.

## 2. Vacuity, hidden hypotheses, cycles
```
$ sed -n 496,499p; sed -n 560,565p   # the only structures
structure EdgeSplit (α : Type*) where  before : List α  selected : α  after : List α
structure PairSplit (α : Type*) where  before : List α  first : α  middle : List α  second : α  after : List α
$ grep -nE '^\s*\(h[A-Za-z0-9₁₂_]* :' ContractionSecondLoop.lean | … | uniq -c   # hypothesis binder names
   7 (h   1 (he   1 (hfirst   1 (hp   1 (hsecond
```
Data-only structures, no `Prop` field. All hypotheses are deterministic (`0 ≤ u`, list lengths, list membership, `WF`); no external or
`Prop`-valued sample predicate, so no registry line and no limit check is required. Imports: `RBM3D.Hierarchy.ContractionBasic`, `RBM3D.Gauss.LoopCoordinate`
only (both merged: T2032, T2037); the file is new and nothing imports it: no cycle.

## 3. Compiled nonempty instances
Section 14 (lines 1226–1388): 24 `example`s at `d = 3, L = 3, W = 2, g = 1/2, u = 1/2, z = Complex.I`; loop data with nonempty `σ₁ = [+,-]`,
`σ₂ = [-,+]`, `σ₃ = [+]` (length 7, cuts 3 and 6), a 3-edge word `word3`, split `e1` (middle edge) and pair `p13` (first/last edge) with
membership proved by `simp`; length hypotheses by `rfl`, `0 ≤ 1/2` by `norm_num`, positions `1 < 3`, `0 < 2 < 3` by `simp`/`norm_num`.
Coverage of every public theorem by an applying `example` (docstring lines excluded):
```
$ for n in <public theorems>; do grep -cw "$n" ex.txt; done | …
public theorems: 32 ; without an applying example: none
```
`ω : Ω 3 3 2` stays a variable of the examples; every target is an identity for every sample, and no deterministic hypothesis concerns `ω`. Not degenerate:
`N = 216`, 27 blocks, fibre `Fin 8`, nonempty words and sums. PASS.

## 4. Build, axioms, hygiene, diff
Module olean/ir removed from the audit worktree's copied cache first, then:
```
$ lake build RBM3D.Hierarchy.ContractionSecondLoop 2>&1 | grep -E 'error|warning|Build completed|sorry|Built RBM3D.Hierarchy.ContractionSecondLoop'
✔ [3299/3299] Built RBM3D.Hierarchy.ContractionSecondLoop (3.9s)
Build completed successfully (3299 jobs).
$ lake env lean ax.lean | sed -E "s/^'RBM\.Gauss\.[^']*' //" | sort | uniq -c      # #print axioms of all 45 public decls
  35 depends on axioms: [propext, Classical.choice, Quot.sound]
   3 depends on axioms: [propext, Quot.sound]
   2 depends on axioms: [propext]
   5 does not depend on any axioms
$ grep -nwE 'sorry|admit|native_decide|axiom' RBM3D/Hierarchy/ContractionSecondLoop.lean | wc -l
       0
$ git diff --name-status main...t/T2065
A	RBM3D/Hierarchy/ContractionSecondLoop.lean
$ printf 'import RBM3D\nimport RBM3D.Hierarchy.ContractionSecondLoop\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean | grep -E 'axiom audit|error'
axiom audit: 2280 theorems, 1017 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit=0
```
Only the sole writable file is touched (`RBM3D/Test/Axioms.lean` unchanged, correct since no structural/owed predicate occurs); no frozen
signature is modified (new file only). Name clashes of the 45 public names against current `main` (`bbd22a5`) via `git grep -lwE "(theorem|def|structure|abbrev|lemma) <name>" main`: 0 hits;
`RBM3D/Hierarchy/ContractionSecondLoop.lean` absent on `main`.

## 5. Paper deltas
Lean/RBM2D-statement differences: (i) `W^2 -> W^d` in 17 coefficients; (ii) explicit variance parameter `g` in `sameEdgeCutValue`/`pairCutValue`
and through `gvarF`/`SB`; (iii) `ContractionSecondLoopReverse` not ported. Proposed as T2065a (i, ii) and T2065b (iii) in the prove report (d).
No Lean/paper difference beyond these: the paper's coefficient is `W^d` (`(eq:variancematrix)`, `W^{-d}` per variance and per `E_a`). Covered.

## Observations (no verdict effect)
- O1. Prove report (b) quotes `git -C ../RBM2D diff --stat c9a24cf HEAD` (RBM2D drift after the pinned commit); irrelevant to the port, which reads `c9a24cf`.
- O2. Ticket header gives per-file "kept" line counts below the RBM2D totals; the port carries all 45 public declarations (a superset), which the ticket allows.
- O3. Prover's statement diff (44 identical, 1 differing by `g`) reproduced independently above.

## Verdict
| Target (13 RBM2D files, 45 public decls) | Statement | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|
| ContractionSecondLoop (`sum_twoEdge_mixed_deriv`, …) | = 2D, `W^d` | yes | ok | T2065a | PASS |
| SecondLoopSameEdge / SameEdgeWord / SameEdgeCut | = 2D, `W^d` | yes | ok | T2065a | PASS |
| EdgeSplits / PairSplits (dimension-free) | = 2D | yes | ok | — | PASS |
| First/SecondDerivativePositionSum, SecondDerivativeTraceSum | = 2D | yes | ok | — | PASS |
| PositionLoopBridge / SameEdgePositionCut / PairPositionCut | = 2D (`W^d`) | yes | ok | T2065a | PASS |
| SecondLoopAllCuts | = 2D + `g` | yes | ok | T2065a | PASS |

**T2065: PASS.** No dispatcher sign-off needed.
