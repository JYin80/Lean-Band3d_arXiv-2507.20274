Auditor model: claude-opus-5-5
# T2374 (BA-K05b) — 1a-audit (design gate) — Sat Oct 10 07:48:21 UTC 2026

Inputs: ticket `docs/tickets/T2374.md`; section (a) of `docs/reports/T2374-prove.md` (lines 2-106); supervisor `2026-10-10-0350.md` C1-C5; `main` at e004671 (T2370 merged as 06fd533, `RBM3D/BA/KTreeDeriv.lean` 612 lines). No Lean on `t/T2374` (branch not yet created, by the ticket). Scripts: `S=…/scratchpad/T2374` (preflight's), my reruns in `$S/rerun/`, my checks in `$S/audit/`.

## 1. C3 per-chord numerics (binding): rerun
`cd $S; time python3 chord.py 6` (aggregate block, verbatim):
```
AGGREGATE over configs
  n  per-F max   per-J max   (c) total max   bijection  partition  #(F,J) checked  list-checks  max|term|
  3  0.00e+00   0.00e+00   1.78e-15        True      True      0      0     0.0e+00
  4  4.44e-15   4.44e-15   1.42e-14        True      True      56384      265536     5.8e+00
  5  7.12e-15   4.90e-15   8.89e-15        True      True      11520      17280     2.4e+01
  6  2.85e-14   3.40e-14   1.35e-13        True      True      142848      62208     1.1e+02
elapsed 112s
python3 chord.py 6  110.31s user 1.43s system 99% cpu 1:52.64 total
```
Identical to the report's table (lines 39-44). Max error 1.35e-13 ≤ 1e-12. Small scripts, rerun and compared with the preflight's saved outputs:
```
instance: identical to preflight's saved output
control: identical to preflight's saved output
nonsym: identical to preflight's saved output
table: identical to preflight's saved output
```
(rerun `control.txt`: inner-glue-charge flip fails at 5.45e+00 / 1.13e+01 / 5.25e+01 for n=4/5/6, faithful ≤ 7.3e-15; `nonsym.txt`: `max |M - M^T| = 0.80`, `Theta^{(-,+)} == (Theta^{(+,-)})^T … True  Theta^{(+,-)} symmetric: False`, per-F ≤ 1.07e-14, per-J ≤ 3.9e-16.)

**Mirror faithfulness (read against the Lean text).** `chord.py` lines 9-18 against `Loop/KLCut.lean:361-375, 581-598` and `Loop/KLTree.lean:50`:
- `KLshiftIn`: `min (d.k - J.1) (KLwIn J)` with ℕ-truncation ↔ `min(max(d[k]-J[0],0),w)`; `KLFIn` filter `KLArcLe d J ∧ d ≠ J` (`KLArcLe d J := J.1 ≤ d.1 ∧ d.2 ≤ J.2`) ↔ `arcLe(d,J) and d != J`;
- `KLcol`, `KLshiftOut`, `KLFOut` (filter `¬KLArcLe d J`), `KLinV`, `KLoutV`, `KLglueV` ↔ `col`, `shiftOut`, `FOut`, `inV`, `outV`, `glueV`: same formulas.
- `cutGlueL/R` in `c3.py` ↔ `Loop/TreeRep.lean:75-82` (take/drop, 1-indexed): same.
- Chord orientation: the mirror puts chord `J` from `('in',J)` to `('out',J)`; Lean: `BACactusValSrc` = `BAslotIn`, `BACactusValTgt` = `BAslotOut` (`BA/KCactus.lean:462-468`). Same.
- Non-tautology: the left side is the cactus with `Θ·Θ` on chord `J`; the right side evaluates `Γ_{F_out}`, `Γ_{F_in}` independently on the `p`- and `q`-gons, with `σ` read from `cutGlueL/R`, then the `(i+1,j+1)` summand through the spliced `K` (`c3.Data.K`). The control shows a one-charge error is detected at O(1).
Verdict C3: **met** (n = 3..6, every σ, all a at n ≤ 4, 6 random a at n = 5, 6, four (q,g,t,W) configurations; tolerance 1.35e-13; mirrors of all six maps; total (c) check included).

## 2. Target-2 pin (deliverable (i), public statement)
Token diff of the pin's left-side summand (report lines 74-78, after `W^{-d(n-1)} * ∑ F ∈ TSP n,`) against the chord part of the merged `BAGammaDerivRHS`:
```
$ diff <(tokens report:74-78) <(tokens RBM3D/BA/KTreeDeriv.lean:75-79) && echo …
IDENTICAL token stream (pin LHS summand vs BAGammaDerivRHS chord part, KTreeDeriv.lean:75-79)
$ diff <(KTreeDeriv.lean:92-94) <(report:71-73) && echo …
binders (3 lines) IDENTICAL to BALeafPairsStmt
```
Elaboration on `main` (scratch file outside the repository: the pin text verbatim from report lines 70-81, in a scratch namespace, plus `example : Prop := ∀ d, BAChordPairsStmt d`):
```
$ lake env lean $S/audit/PinCheck.lean
@BAKcac_spliced : ∀ {d L W : ℕ} [inst : NeZero L] {g E : ℝ} {m : ℂ}, BASplicedFam d L W g E m (BAKcac d L W g E m)
baLeafPairs : ∀ (d : ℕ), BALeafPairsStmt d
exit 0
```
Statement check against the ticket's mathematics: left = chord part of `W^{-d(n-1)} Σ_{F∈TSP n} BAGammaDerivRHS` (verbatim); right = `Σ_{J ∈ diagonals n} W^d Σ_x K t (cutGlueL (i+1)(j+1) x I) · K t (cutGlueR (i+1)(j+1) x I)`, i.e. the `(i+1,j+1)` summands of `treeEqRhsS d L W 1 (K t) I` with `Σ_{a,b} K·1_{ab}·K = Σ_x` (same convention as the merged `BALeafPairsStmt`). Hypotheses `BAReal`, `0 ≤ t < 1` are unused by the proof route but are dischargeable (`P.real`, `t = 1/2`) and kept for the `BALeafPairsStmt` shape; `n ≥ 3`, all `σ`, `a`, any `K` with `BASplicedFam`: the general statement, not a special case. No hidden hypothesis (no structure carrying an assumption). At `n = 3` both sides are empty sums; `n = 4` (the planned instance, `J = (0,2)`) is nonempty.

## 3. The written argument (deliverable (i)) against C1-C4
- **Relabelling** (report line 84): slots `BAslot F_out ⊕ BAslot F_in ≃ BAslot F` via the shift/col maps, `leaf(glue) ↦ out J`, `leaf(last) ↦ in J`. I checked the transport by hand: `BAslotStart (out J) = i ↦ KLglueV = i`, `BAslotStart (in J) = j ↦ w`; `BAMcharge s = σ(start(next s))` (`KCactus.lean:434`) with `σ_out = σ_0..σ_i,σ_j..σ_{n-1}`, `σ_in = σ_i..σ_j` (from `cutGlueL/R`) gives the same charges; outer glue leaf `Θ^{(σ_i,σ_j)}` = the `Q` leaf of `KLgval_split` (`KLCut.lean:116`, `c₀ = in J ∈ N₂`, `q₀ = out J ∈ N₁`, `P = Q = Θ^{(σ_i,σ_j)}`, `S = 1`), inner last leaf `Θ^{(σ_j,σ_i)} = Pᵀ`. Labels `a_out^x = a_0..a_{i-1},x,a_j..`, `a_in^x = a_i..a_{j-1},x` match `cutGlueL/R`. Sound; the slot-level commutation with `BAnextSlot` (via `BAnextSlot_eq_of_above`/`_of_wrap`, `KCactus.lean:374-388`) is the main formal risk and is named as such.
- **W powers**: `W^d·(W^d)⁻¹^{p-1}(W^d)⁻¹^{q-1} = (W^d)⁻¹^{n-1}` from `p+q = n+2`; at `W^d = 0` both sides vanish (`n-1 ≥ 2`). Correct.
- **Sum**: `Σ_F Σ_{J:↥F} = Σ_{J∈diagonals n} Σ_{F∋J}` then `KLsum_cut` (`KLCut.lean:1297`; summand a function of `(KLFOut F J, KLFIn F J)`), clause 3 of `BASplicedFam` at `p, q ≥ 3` (table: `min p = 3, min q = 3`, n = 4..9). Correct.
- **C1** (spliced family; 2-loop not a cactus): the route uses only `BASplicedFam` / `BAKcac`; `n = 2` from K03's closed form. Met.
- **C2** (orientation): reversed leaf by `Θ^{(s',s)} = (Θ^{(s,s')})ᵀ`, which holds with no hypothesis (`BAKTreeDeriv_Theta_swap`, `KTreeDeriv.lean:118`; `nonsym.py` confirms with non-symmetric `M`). The route needs no symmetry of `M`, so the C2 FAIL condition is not hit. Met.
- **C4** (`BATreeRep` through `baK_unique`): `baKsolve` → `BAKsol_isKLoopS` (`KSolve.lean:606`) → `baK_unique` (`:568`, both families `IsKLoopS … (Set.Ico 0 1)`) → `BAKcac_spliced` clause 3. Signatures read; the chain types. Met.
- Targets 3-4: derivative (leaf pairs + chord pairs, partition `n + n(n-3)/2 = n(n-1)/2`, `partition True` n = 3..6), initial value (`BACactusVal_sum_zero_BAMLoop`, `KCactus.lean:736`; `n = 2` from `baKsolveLe3_holds`), length 1 (clause 1); `(Kn2sol)` = `BAKcac_spliced.2.1` against `BAKsolve`'s 2-clause (`KSolve.lean:58-67`, `σ : Bool × Bool` vs `σ₁ σ₂`: a destructuring only). Sound.
- Target 7: the line to delete is `RBM3D/Test/Axioms.lean:141` on `main` (`grep -n BAKsolve` returns exactly that line). Correct.

## 4. C5 / Q4 (deliverable (iii))
`wc -l RBM3D/BA/KTreeDeriv.lean` on `main`: `612`. Report: K05b central 1300 (low 900, high 1800) → K05 total 1912 (1512 / 2412; 2612 at the stop line) against the 2051 Q4 line 3.3k (`2026-10-09-2051.md:126`). Arithmetic correct; **not crossed**, even at the stop line.

## 5. Plan against the stop line 2000 (deliverable (iv))
Nine sections, cumulative 70 / 250 / 420 / 620 / 780 / 900 / 1170 / 1220 / 1300, five section commits, each with `wc -l` and "at any boundary > 2000: commit, stop, RETURN". High estimate 1800 < 2000. Instances (target 6) at `P` (`BA/MFixedPoint.lean:893`, `def P : FlowPt 4 10`), `n = 4`, `F = {(0,2)}`, as the ticket requires. Met.

## 6. Exponent table and instance (CLAUDE.md §4 (i)-(ii))
Present (report lines 6-36); every row checked above or by the reruns. Numeric instance `(d,L) = (3,4)`, `N = 64`, `W = 2`, `t = 1/2`, `n = 4, 5`: chord-J values nonzero (`nonzero: True`), errors ≤ 4.5e-22 at values ~1e-7..1e-11 (relative ≤ 1e-14). Nondegenerate.

## Observations (no statement, instance, build, axiom or paper-delta effect)
- O1. Section (a)'s parts are ordered by CLAUDE.md §4 ((i) table, (ii) numerics, (iii) argument, (iv) Q4 + plan) rather than by the ticket's numbering ((i) argument, (ii) C3, (iii) C5, (iv) plan); all four ticket deliverables are present.
- O2. `BAKTreeDeriv_Theta_swap` is `private` on `main`; 1b must copy it with the stem `KTreeRep_` (≈ 8 lines) or use the public `BATheta_swap` + `BATheta_isSymm` (available: target 2 carries `BAReal`, `0 ≤ t < 1`). The plan does not itemize this; negligible.
- O3. `table.py`'s header announces a "W-power identity" column but each row prints one boolean; the identity is the exponent algebra of §3 and is exact.
- O4. The numerics run on a d = 1 toy torus (q = 4, 5 sites) and, for the instance, at `g = 1/2, E = 0.3` rather than at `P` (a choice); the identity is lattice-independent, and the Lean instance will be at `P`.
- O5. The "dropped outer chord" control is vacuous at n = 4 (`F_out = ∅`); disclosed in the report.
- Paper deltas: none needed at 1a (target 2 is an internal identity; `BATreeRep` at `3 ≤ n` is the pinned form, supervisor 0350 Q1).

## Verdict
| deliverable / stop line | result |
|---|---|
| (i) written argument + public statement of target 2 | met; pin elaborates on `main` (exit 0) |
| (ii) C3 per-chord numerics ≤ 1e-12, mirrors of the six maps, total (c) | met; rerun identical, max 1.35e-13 |
| (iii) C5 Q4 number | 1912 vs 3.3k, not crossed |
| (iv) plan vs stop line 2000 | met (central 1300, high 1800) |
| C2 FAIL (route needs non-symmetric-`M` facts) | not hit (no symmetry used) |
| indexing failure / false identity (pin repair / REQ) | none |

**1a-audit: PASS.** Stage 1b may start under the ticket's start condition (T2370 merged: 06fd533 on `main`). Target-2 pin for the 1b audit: report lines 70-81, verbatim. No dispatcher sign-off needed.
