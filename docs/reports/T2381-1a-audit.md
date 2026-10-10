Auditor model: claude-opus-5-5

# T2381 (BA-K10) — 1a-audit (design gate), Sat Oct 10 10:52:19 UTC 2026

Input: `docs/reports/T2381-prove.md` §(a) (90 lines, header `Prover model: claude-sonnet-5-5`), ticket `docs/tickets/T2381.md`.
Branch `t/T2381`: no Lean yet (as expected at this gate).
```
$ git log --oneline -1 t/T2381; git diff --stat main...t/T2381
442d3aa Dispatcher V2: BA-K07 = T2380, BA-K10 = T2381, DECISIONS §192, H174
(empty)
```

## 1. Numerics rerun (deliverable (iii), binding)

I copied the prover's scripts (`k10.py`, `k10_lattice.py`, mirrors `k6.py`, `mirror.py`, `mgraph.py`, `kode.py`) to `scratchpad/T2381/audit/` and reran them unchanged.
```
$ python3 k10.py cut 6
BA(q=4) n=4: cases=16 (|pi|>=2: 0) max|K^pi-form1|=1.1e-15 max|K^pi-form2|=1.6e-15 max|K^pi|=1.5 | control(transposed chord) 1.6e-15
BA(q=4) n=5: cases=128 (|pi|>=2: 48) max|K^pi-form1|=5.3e-15 max|K^pi-form2|=4.1e-15 max|K^pi|=3.1 | control(transposed chord) 4.1e-15
BA(q=4) n=6: cases=832 (|pi|>=2: 544) max|K^pi-form1|=2.8e-14 max|K^pi-form2|=3.1e-14 max|K^pi|=6.5 | control(transposed chord) 3.1e-14
BA(q=3) n=4: cases=16 (|pi|>=2: 0) max|K^pi-form1|=5.6e-16 max|K^pi-form2|=5.7e-16 max|K^pi|=0.92 | control(transposed chord) 5.7e-16
BA(q=3) n=5: cases=128 (|pi|>=2: 48) max|K^pi-form1|=1.2e-15 max|K^pi-form2|=1.0e-15 max|K^pi|=1.8 | control(transposed chord) 1.1e-15
BA(q=3) n=6: cases=832 (|pi|>=2: 544) max|K^pi-form1|=3.1e-15 max|K^pi-form2|=3.6e-15 max|K^pi|=3.7 | control(transposed chord) 4.1e-15
RAND n=4: cases=16 (|pi|>=2: 0) max|K^pi-form1|=1.1e-17 max|K^pi-form2|=9.3e-18 max|K^pi|=0.026 | control(transposed chord) 2.1e-03
RAND n=5: cases=128 (|pi|>=2: 48) max|K^pi-form1|=2.1e-17 max|K^pi-form2|=2.2e-17 max|K^pi|=0.038 | control(transposed chord) 3.0e-03
RAND n=6: cases=832 (|pi|>=2: 544) max|K^pi-form1|=3.7e-17 max|K^pi-form2|=4.2e-17 max|K^pi|=0.07 | control(transposed chord) 5.6e-03
$ python3 k10.py base
q=4 g=0.5 E=0.3 t=0.7: (a) n=3 |Gamma(empty)-Kn3sol|=2e-15; (b) level eq. n=2 9e-16, n=3 1e-14; (c) ... |K2|<=A*colsum True (ratio 0.76), |K3|<=A^2*S*Cm^2 True (ratio 0.19)
q=3 g=1.1 E=0.0 t=0.6: (a) n=3 |Gamma(empty)-Kn3sol|=5e-16; (b) level eq. n=2 4e-16, n=3 2e-15; (c) ... True (ratio 0.66), ... True (ratio 0.17)
q=5 g=0.8 E=0.3 t=0.95: (a) n=3 |Gamma(empty)-Kn3sol|=1e-14; (b) level eq. n=2 3e-14, n=3 7e-13; (c) ... True (ratio 0.85), ... True (ratio 0.14)
q=4 g=0.5 E=0.3 t=0.3: (a) n=3 |Gamma(empty)-Kn3sol|=3e-16; (b) level eq. n=2 1e-16, n=3 4e-16; (c) ... True (ratio 0.71), ... True (ratio 0.18)
$ python3 k10_lattice.py        # (d,L)=(3,4), t=1/2
-- g=0.5 E=0.3: m=-0.0961+0.6814j kappa=0.6814 ...   worst |diff| 5.4e-16   (I1, I1eq n=4 pi={(0,2)}; I2 n=5 pi={(0,2),(2,4)}, J=(0,2) and J=(2,4))
-- g=1.2 E=-0.4: m=0.1818+0.5431j kappa=0.5431 ...   worst |diff| 1.1e-16
```
The output matches the report line by line. The worst defects are 3.1e-14 (cut) and 7e-13 (base, `n = 3`, `t = 0.95`); both are ≤ 1e-12.
Counts 16/128/832 equal T2376's (`T2376-prove.md:54,58`: `832`).
No ODE: an instrumented `base` run made zero `kode.rk4` calls, and `k6.Data` builds `Θ` by `np.linalg.inv`.
```
$ python3 -c "...kode.rk4 wrapped with a counter...; exec k10.py base"   ->   rk4 calls: 0
```
Coverage: the loop runs over `n = 4..6`, every `σ ∈ {±}^n`, every nonempty layer `flong(F,σ)`, and every innermost `J`, which is the scope the ticket asks for.
The transposed-chord control does not discriminate on symmetric BA data (expected). It does discriminate on the RAND non-symmetric data (2e-3..6e-3), and there the formula holds to 4e-17.

## 2. Written argument (deliverable (ii)), checked against merged signatures

- **Chord weight.** `BACactusValEdgeW` (`BA/KCactus.lean:457-459`) puts `(t:ℂ) • BAThetaOf M t (σ J.1) (σ J.2)` on every chord. So `baCactus_cut` (`BA/KCactusCut.lean:1111`) at `P = 1`, `S = t•1`, `Q = Θ^{σiσj}` has `P*S*Q` equal to the existing weight, and the `update` is the identity, as claimed.
- **Inner leaf.** `baCactus_cut`'s inner leaf weights are `BAdeltaIn J Lw Pᵀ` (`:1119`). With `P = 1` the last leaf is `1`. The leaves `k < last` are `Lw (BAinVinv J k)` (`BAdeltaIn`, `:54`). `KMolecule_gval_eq_sum` (private, `BA/KMolecule.lean:87`) is the copy target. This gives `A(u)`.
- **Outer leaf.** `baCactus_leafW_out` (`:1232`, hypothesis `J.1+2 ≤ J.2` only) identifies the outer leaves with `BACactusValLeafW M t (sigmaOut σ J)`. Then `S = t•1` collapses `w = u`, and the outer factor is `BAGamma` at `F_out`.
- **Reversed leaf (0350 C2).** C2 says "a route that needs these facts for non-symmetric `M` is a 1a FAIL". This route needs none of them. `Pᵀ = 1`; `KCactusCut_Theta_swap` (`:946`) is a transpose identity valid for any `M` and is internal to merged lemmas. The RAND run confirms the identity for independent non-symmetric `M(±)`.
- **Layer bijection.** `Flong_eq_iff_cut` (`Loop/KLSumZeroWard.lean:165`) and `KLsum_cut` (`Loop/KLCut.lean:1297`) exist, as used by `baSigmaPi_cut`.
- **W powers.** `BAKpi`/`BASigmaPi` (`BA/KMolecule.lean:53,67`) carry no `W`. `(n_in-2)+(n_out-1) = (w-1)+(n-w) = n-1` is correct.
- **Band shape.** `KLKpi_cut` (`Loop/KLInduct.lean:606-621`) is `Σ_{u,w} t·A(u)·SB u w·KLKpi(…aOut w…)`. The BA form 1 is this shape with `SB ↦ 1`, and `baKpi_cut_S` states it literally.
- **Base levels.** `BAKsolve` (`BA/KSolve.lean:58`) carries `(Kn2sol)`. `baK_unique` (`:568`) needs `IsKLoopS` on both sides, so `BAKsolveLe3` (`IsKLoopSLe 3`) cannot feed it, and the report's deviation from the ticket's source list is correct (0350 C4 route).
- **`n = 3`.** `BACactusVal_three_BAMLoop` (`BA/KCactus.lean:763`) carries the `W^{-2d}`/`BAMLoop` bookkeeping, and `TSP_three` (`Loop/Partition.lean:108`) gives `TSP 3 = {∅}`.
- **Bound chains.** I checked the signatures of the inputs:
  - `BAProp5`/`BAProp5s` (`BA/FlowPins.lean:171,182`): sup and short `ℓ¹`, `3 ≤ d`;
  - `BAPropM` (`BA/MFixedPoint.lean:567`): row sum of squares `= 1`, `‖m‖ ≤ 1`, two decay regimes;
  - `BAK_col_sum`, `BAMss_norm_eq_BAK` (`BA/KKernel.lean:128,102`);
  - `KLIndStepA_Bparam_le_zero` (`Loop/KLIndStepA.lean:124`).

  The `n = 3` chain is valid: among `(σ0σ1),(σ1σ2),(σ2σ0)` at least one pair is equal; its leaf is summed (`S`), the other two are sup-bounded (`C_d B` each), and `|M| ≤ 1` plus two `ℓ¹` sums give `C_M²`.

Name existence (grep of `def|theorem` on `main`): every name the plan uses exists. The new names `BAKBoundAt`, `BAKpiBoundAt`, `baKpi_cut`, `KInduct_` have 0 hits.
```
BACactusVal_three_BAMLoop KCactus.lean:763 | TSP_three Partition.lean:108 | KMolecule_theta_perm (private) KMolecule.lean:166
baProp5_holds Prop6Path.lean:850 | baProp5s_holds Prop5Short.lean:667 | baPropM_holds CombesThomas.lean:562 | BAm_norm_le_one Ward.lean:136
sum_exp_decay_centre PureLoop.lean:144 | KLone_le_rpow KLInduct.lean:219 (to copy private) | BAKBoundAt/BAKpiBoundAt/baKpi_cut/KInduct_: NONE
```
Import closure of the planned imports (script `imports.py`): `BA.Prop5Short`, `BA.Ward`, `BA.KCactus`, `BA.KBase`, `Loop.KLSumZeroWard`, `Loop.KLCut`, `Loop.Partition`, `Loop.KLIndStepA`, `BA.MFixedPoint` are all reachable. `Loop.KLInduct` is NOT imported, consistent with the plan, which avoids K09b's in-place file.

## 3. Statements and consumers (deliverable (i))

| statement (report §(i)) | check | result |
|---|---|---|
| `baKsol_one/two/three` | hypotheses `H` = those of `baK_eq_sum_Kpi`; `Λ := g`; closed forms = `BAKsolve`'s `(Kn2sol)` and `BACactusVal_three_BAMLoop` | consistent |
| `BAKBoundAt` | verbatim probe `t/T2360:RBM3D/Probe/T2360Pins.lean:38-44` (printed in this audit); `(W^{-d}B)^{n-1}` matches `BAMLoop`'s `W^{-d(n-1)}` | consistent |
| `baKBoundAt_one/two/three` | the `W`-exponent at `n = 2` is that of `(Kn2sol)`; at `n = 3`, `BATreeRep`'s `W^{-2d}` | consistent |
| `baKpi_cut` | hypotheses = `KLKpi_cut`'s, minus `hL`/`hm` (no `ξ` in BA); no hypothesis on `M`; long `J` follows from `J ∈ KLFlong` | consistent |
| `baKpi_cut_abs` | `A(u)` = summand of `IndStepAbs` (`Loop/KLIndStepB.lean:77`) at `r = Fin.last`, `Sig = BASig` (`BA/KMolecule.lean:74`); `σin_last = σ_j ≠ σ_i = σin_0` | consistent |
| `BAKpiBoundAt`, `baKpi_empty_slice/short` | twins of `KLKpiBoundAt` (`:105`) and `KLInduct_Kpi_empty_slice/short` (`:781,799`) | consistent |

Instances (ticket item 2):
- `(d,L) = (3,4)`, `P : FlowPt 4 10`. `FlowPt`/`P` exist at `BA/MFixedPoint.lean:877,893` with field `real : BAReal …`.
- `n = 4`, `π = {(0,2)}`.
- `n = 5`, `π = {(0,2),(2,4)}`, `σ = (+,+,-,+,+)`: both edges are long and innermost, and the charges are mixed.
- The base levels at `n = 1,2,3`.

None of these is degenerate.

## 4. Plan against the stop line (deliverable (iv))

The plan's section total is ≈1220 lines: §1 190, §2 220, §3 280, §4 300, §5 80, §6 150. The binding stop line is 2000 (`wc -l` at each section commit), so the plan leaves 780 lines. It sits inside the ticket's estimate band 800/1100/1800. No binding stop line is hit.

## 5. Observations (no RETURN)

- **O1. Base levels over abstract data.** Ticket item 1, bullet 3 asks for base levels "over the abstract data"; the report states them only in BA form (`BAKBoundAt`), with consumer K12. A grep confirms the generic step does not use them: `KLKpi_step` uses only `KLInduct_Kpi_empty_bound` (`:990`) and `KLKpi_cut` (`:1058`), while `KLBoundAt_one/two/three` are used only by `KLboundPin_holds` (`:1191-1193`), the K12 assembly (design row K12, `T2360-design.md:133`). The 1b report should state this routing explicitly in one line.
- **O2. Dispatcher routing items D1–D3.** None of these changes a K10 statement, and 1b can proceed without them:
  - D1: `BAKBoundAt` is defined in K10 and imported by K12.
  - D2: the new def `BAKpiBoundAt`.
  - D3: the analytic empty-layer bound (`KLInduct_Kpi_empty_bound` twin, band §6) needs K07 (`T2380`, unmerged) and a proved `IndStepAbs`, so it is not deliverable here. Note that `KLKpi_step` consumes it (`:990`). The dispatcher must assign it to K09b or K12 when writing those tickets.
- **O3. `baKpi_cut_abs` in prose.** Its statement is given as "`A(u)` verbatim the summand of `IndStepAbs`". The 1b must write it with explicit `ι`, `L`, `g`, `E`, `m`, `t` families in `BASig`'s argument order. The precise form is determined by `BASig` and `IndStepAbs`.
- **O4. `W = 1` in the base numerics.** The base numerics run at `W = 1`. The `W` bookkeeping at `n = 3` is carried by the merged `BACactusVal_three_BAMLoop`, so this is not a gap.
- **O5. Paper deltas.** Candidates `T2381a` (one glue sum, chord `tΘ` as outer glue leaf; no `S^{(B)}`/`ξSΘ`) and `T2381b` (= `T2360e`) are proposed in the report.

## Verdict

| deliverable | verdict |
|---|---|
| (i) public statements with consumers | PASS (O1, O3) |
| (ii) written argument: bijection, `tΘ` glue, `W` powers, reversed leaf | PASS |
| (iii) numerics, tol ≤ 1e-12, no ODE, `n = 4..6`, every `σ`/layer/innermost `J`, base vs K03 | PASS (reproduced) |
| (iv) plan against stop line 2000 | PASS (≈1220) |
| binding stop lines (0350 C2 non-symmetric `M`; 2000 lines; false identity) | none hit |

**T2381 stage 1a: PASS.** 1b may start. D1–D3 (O2) are routing items for the dispatcher; they are not a sign-off precondition for K10.
