Auditor model: claude-opus-5-5

# T2381 (BA-K10, `RBM3D/BA/KInduct.lean`) — stage 2 audit, round 1, Sat Oct 10 11:44:26 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2381-audit1`, detached at `t/T2381` = `bccb85b`. Merge base `442d3aa`.
`main` = `caa8d7a`, which has no Lean change since the merge base. Pin of record: the public statement table of the 1a report
(`T2381-prove.md` §(a)(i)). That table passed the 1a-audit (`T2381-1a-audit.md`), as the ticket's acceptance line requires.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.KInduct ; echo exit=$? ; grep KInduct build.txt | grep -E 'error|warning'
Build completed successfully (3768 jobs).
exit=0                                   (no error or warning line for KInduct.lean)
$ lake env lean Ax.lean | sort | uniq -c        # import RBM3D.BA.KInduct; #print axioms of the 13 public names
   1 'RBM.BA.baKBoundAt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
   ... (same line for baKBoundAt_two, baKBoundAt_three, BAKBoundAt, baKpi_cut_abs, baKpi_cut_S, baKpi_cut,
        baKpi_empty_short, baKpi_empty_slice, BAKpiBoundAt, baKsol_one, baKsol_three, baKsol_two)   13 lines, all identical axiom sets
$ lake env lean Reg.lean      # import RBM3D; import RBM3D.BA.KInduct; #assert_rbm_axioms   -> exit 0
axiom audit: 11013 theorems, 3223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
$ lake env lean RegBase.lean  # import RBM3D; #assert_rbm_axioms
axiom audit: 11000 theorems, 3221 definitions, 0 axioms in `RBM` ...
premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
$ git diff --name-only main...t/T2381
RBM3D/BA/KInduct.lean
$ git diff main...t/T2381 | grep '^+' | grep -nwE 'sorry|admit|axiom|native_decide' ; echo $?
1                                        (no hit)
$ git diff --stat 442d3aa main -- RBM3D RBM3D.lean        (empty: no frozen file touched, base not stale)
$ lake env lean docs/tickets/checks/T2381-check.lean ; echo exit=$?     (in the audit worktree)
exit=0
$ wc -l RBM3D/BA/KInduct.lean
     991                                 (stop line 2000)
```
Registry: the new module adds 13 theorems and 2 definitions. It adds no premise (113 before and after).
Private helpers: there are 22 `private` declarations, and all carry the stem `KInduct_`. Public declarations, from `grep -nE '^(theorem|def) '`:
`BAKBoundAt :55`, `BAKpiBoundAt :66`, `baKsol_one :77`, `baKsol_two :88`, `baKsol_three :105`, `baKBoundAt_one :270`,
`baKBoundAt_two :291`, `baKBoundAt_three :425`, `baKpi_cut :627`, `baKpi_cut_S :708`, `baKpi_cut_abs :734`,
`baKpi_empty_slice :758`, `baKpi_empty_short :776`. These are exactly the names of the 1a table.
`variable` lines (:123, :490) bind only `d L n J` and `NeZero` instances, so there is no hidden hypothesis.

## 2. Statements against the pin and the paper

```
$ diff <(git show t/T2360:RBM3D/Probe/T2360Pins.lean | sed -n '/^def BAKBoundAt/,/(n - 1)$/p') \
       <(git show t/T2381:RBM3D/BA/KInduct.lean   | sed -n '/^def BAKBoundAt/,/(n - 1)$/p') && echo identical
def BAKBoundAt: identical to probe t/T2360
$ grep -n 'label{Kn2sol}\|label{Kn3sol}' paper/tex/1_2_Intro_model_result.tex | cut -c1-210
1175: \cK^{(2)}_{t,\bsig,\ba} = ... = W^{-d}(\Theta_t^{(\sigma_1,\sigma_2)} M^{(\sig_1,\sig_2)})_{a_1a_2}
1176: \mathcal{K}^{(3)} = \sum_{b_1,b_2,b_3}\Theta^{(\sig_1,\sig_2)}(a_1,b_1)\Theta^{(\sig_2,\sig_3)}(a_2,b_2)\Theta^{(\sig_3,\sig_1)}(a_3,b_3)\cal M^{(3)}_{\bsig,\mathbf b}
$ sed -n 1056,1058p paper/tex/1_2_Intro_model_result.tex     # ML:Kbound
  \max_{\bsig}\max_{\ba} |{\cal K}^{(n)}_{t,\bsig,\ba}| \prec (W^{-d}B_{t,0})^{n-1}
```

| target | check | result |
|---|---|---|
| `BAKBoundAt` | identical to the probe pin (diff above). It is `(eq:bcal_k)` with `≺` read as `C L^τ`, `C` uniform in `L ≥ 3, W ≥ 1, g ∈ (0,Λ], E, t ∈ [0,1)`, `σ`, `a` | PASS |
| `BAKpiBoundAt` | twin of `KLKpiBoundAt` (`Loop/KLInduct.lean:105`, printed). The only change is `p : KLPar` → explicit `L, g, E, m, BAReal, t`. No `W` (`BAKpi` has none; `W^{-d(n-1)}` is in `(eq_K-Kpi)`, `A:622`). No theorem concludes it, so it is a definition only (1a D2) | PASS (def) |
| `baKsol_one/two/three` | the hypotheses are those of `baK_eq_sum_Kpi` (`0<κ, 0<g, 3≤L, BAReal, t∈[0,1)`). The right sides are `m(σ_0)`, `(Kn2sol)` and `(Kn3sol)` (indices shifted to `0..2`, last leaf `Θ^{(σ_2,σ_0)}`). `BATheta`/`BAMss` (`MFixedPoint.lean:511,515`) are `Θ_t^{(σσ')}` and `M^{(σσ')}`. The transfer runs through `baK_unique` against the `baKsolve` witness (0350 C4), at `:94-101` | PASS |
| `baKBoundAt_one` | `BAKBoundAt d 1 Λ κ` for all `d, Λ, κ`; `n = 1` needs no `d ≥ 3` (`‖m‖ ≤ 1`) | PASS |
| `baKBoundAt_two/three` | `3 ≤ d, 0 < Λ, 0 < κ` give `BAKBoundAt d n Λ κ`. The inputs are the unconditional theorems `baProp5_holds` (`Prop6Path:850`), `baProp5s_holds` (`Prop5Short:667`), `BAMB_row_l1` (`GreenSchur:139`) and `BAK_col_sum` (`KKernel:128`). None of them is a hypothesis or a structure field | PASS |
| `baKpi_cut` | the hypotheses are those of `KLKpi_cut` (`Loop/KLInduct.lean:606`) without `hL`/`hm` (BA has no `ξ`), and there is no hypothesis on `M` or `t`. On the right: one glue sum `Σ_u`; prefactor exactly `(t:ℂ)`, with no `∏ m`; the inner molecule `BASigmaPi … (sigmaIn σ J) ∅` with leaves `Θ^{(σin_k,σin_{k+1})}(a_{BAinVinv J k}, δ_k)`, `k ≠ last`, and `δ_last = u`; the outer `BAKpi` on `sigmaOut σ J`, `(π.erase J).image (KLshiftOut J)`, labels `BAdeltaOut J a u`. The chord `tΘ^{(σ_i,σ_j)}` is `t` times the outer polygon's standard glue leaf, which is the same convention as `KLKpi_cut`'s docstring ("standard leaf `Θ^{(σ_i,σ_j)}` of the outer polygon"). This matches the ticket's three ingredients and the 1a statement | PASS |
| `baKpi_cut_S` | the same identity with `(1 : Matrix) u w` in the `S^{(B)}_{uw}` slot of `KLKpi_cut`. This is correct because BA has `S^{(B)} = I` (paper `1_2:662`) | PASS |
| `baKpi_cut_abs` | `baKpi_cut` with `Sig = BASig` (`KMolecule.lean:74`) and the `BAThetaOf` leaves, over a family `ι`. The bridge example (:951) feeds `IndStepAbs … BASig … Θ` (`KLIndStepB.lean:77`) and closes the bound on `Σ_u ‖A(u)‖` by `exact` at `r = Fin.last`. So `A(u)` is verbatim the `IndStepAbs` summand (1a O3 resolved) | PASS |
| `baKpi_empty_slice/short` | twins of `KLInduct_Kpi_empty_slice/short` (`:781, :799`). Pure algebra; the hypotheses `hCm`, `hS` are explicit in the signature | PASS |

The cut is a proved Lean identity whose left side is the merged `BAKpi`, so it cannot be false. The 1a numerics give an independent cross-check: defect `≤ 3.1e-14` over `n = 4..6`, every `σ`, every layer and every innermost `J`, reproduced in the 1a-audit.

## 3. Vacuity, hidden hypotheses, cycles

- No public theorem has a `Prop`-valued structure argument or an external hypothesis.
- The import closure excludes `RBM3D` and `Loop.KLInduct`, which K09b edits in place. The imports are `BA.KMolecule`, `KCactusCut`, `KTreeRep`, `KSolve`, `Loop.KLIndStepB`, `BA.Prop6Path`, `GreenSchur` and `KKernel`, all merged, so there is no cycle.
- `baCactus_cut` is imported, not copied (DECISIONS §190). `grep -nE '^(private )?(theorem|def|lemma) [A-Za-z_]*[Cc]ut'` lists only `KInduct_tree_cut :555`, `baKpi_cut :627`, `_S :708` and `_abs :734`, and `grep -c baCactus_cut` gives 3 (uses only).
- No external hypothesis is introduced, so there is no limit check to run.

## 4. Compiled nonempty instances

Script: line of the `example` that applies each endpoint (in `namespace KInductInst`, elaborated by the build in §1).
```
baKsol_one: 819   baKsol_two: 824   baKsol_three: 829   baKBoundAt_one: 837   baKBoundAt_two: 846   baKBoundAt_three: 855
baKpi_cut: 862,871,926,934   baKpi_cut_S: 880   baKpi_cut_abs: 942 (+ bridge 951)   baKpi_empty_slice: 973   baKpi_empty_short: 985
```
Data for all instances: `P : FlowPt 4 10` at `(d,L) = (3,4)`, `W = 2`, `t = 1/2`, `Λ = 10`, `κ = Im m₀`. Every hypothesis is discharged by `P.real`, `P.g0_pos`, `P.g0_le` and `norm_num`.

| instances | data and hypotheses | result |
|---|---|---|
| base levels and bounds | `n = 1, 2, 3`, with mixed charges `(+,-)` and `(+,-,+)` and distinct labels | non-degenerate |
| `baKpi_cut`, `n = 4` (:862) | `σ = (+,+,-,+)`, `π = F₀ = {(0,2)}`. `F₀ ∈ TSP 4` by `TSP_four`, `KLFlong` by `decide` | non-degenerate |
| `baKpi_cut`, non-symmetric `M` (:871) | non-symmetric, charge-dependent `M` (0350 C2) | non-degenerate |
| `baKpi_cut`, `n = 5` (:926, :934) | `π = {(0,2),(2,4)}`, `σ = (+,+,-,+,+)`, cut at both edges. `F₀ ∈ TSP 5`, `KLFlong` and innermost proved by `decide` (private `KInduct_F5_*`). `π' = {(1,3)}` and `{(0,2)}` checked at :915 | non-degenerate |
| bridge example (:951) | its only hypothesis is `IndStepAbs`, K09a's unproved pin, which is allowed | allowed |
| `baKpi_empty_short` (:985) | `S > 0` from the uniform short-leaf `ℓ¹` bound; `Cm` a finite supremum | non-degenerate |

No instance uses `N = 0`, an empty index, a collapsed window, or a `False` premise.

## 5. Paper deltas

| difference | covered by |
|---|---|
| `BAKBoundAt` reads `≺` as a uniform `C L^τ` | `docs/paper-deltas.md:1594`, D635 (T2360e); report re-proposes it as `T2381b` |
| BA chord `tΘ` against `(f-internal2)`/`(eq:molecule-Kpi)`'s `tS^{(B)}Θ` (`A:561,625`), at `S^{(B)} = I` | D633 (`paper-deltas.md:1592`, T2360b) |
| the cut identity (one glue sum, chord as outer glue leaf; the paper states no cut, and BA has no `Θ − 1 = ξSΘ`) | candidate `T2381a` (report §(d)) |
| `3 ≤ n` in `baKpi_cut*`, while only `2 ≤ n` is used | a Lean hypothesis convention identical to `KLKpi_cut`, not a paper statement; no delta needed |

## 6. Observations (no RETURN)

- **O1.** The ticket asks for base levels "over abstract data", but they are stated in BA form only. The 1a statement table, which passed the 1a-audit (O1 there), routes them to K12. The 1b report records the routing with greps (`KLBoundAt_*` is used only by `KLboundPin_holds`).
- **O2.** `BAKsolveLe3` (K03), which the ticket lists as an input, is not used. The report gives the reason: `IsKLoopSLe 3` is not `IsKLoopS`, so `baK_unique` does not apply to it. No statement changes.
- **O3.** Dispatcher routing items, unchanged from the 1a; they are not a K10 sign-off precondition:
  - D1: K12 imports `BAKBoundAt` from here.
  - D2: `BAKpiBoundAt` is a new definition with no proof yet.
  - D3: the analytic `‖K^{(∅)}‖ ≲ B^{n-1}` goes to K09b or K12.
- **O4.** The prove report's §(c) cites 56 checked Mathlib names. I did not re-run that list; it affects no statement.

## Verdict

| target | verdict |
|---|---|
| `BAKBoundAt`, `BAKpiBoundAt` (defs) | PASS |
| `baKsol_one`, `baKsol_two`, `baKsol_three` | PASS |
| `baKBoundAt_one`, `baKBoundAt_two`, `baKBoundAt_three` | PASS |
| `baKpi_cut`, `baKpi_cut_S`, `baKpi_cut_abs` | PASS |
| `baKpi_empty_slice`, `baKpi_empty_short` | PASS |
| build / axioms / registry / diff / instances / deltas | PASS |

**T2381: PASS.** No dispatcher sign-off is required for the merge. D1–D3 (O3) are routing items for the K09b and K12 tickets.
