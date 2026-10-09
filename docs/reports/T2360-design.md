# T2360 (BA-DK) stage-K design: route, findings, row table

Prover `claude-sonnet-5-5` (prover-max, design only, CONTROL H149). Branch `t/T2360` (base `1fcb883`), probe `RBM3D/Probe/T2360Pins.lean` (396 lines, limit 400), commit `6a3b821`. Last edit: Fri Oct  9 20:01:27 UTC 2026.
Citations: `path:N` is relative to `RBM3D/` at the base (the files cited are the merged ones of `1fcb883`); `1_2:N`, `A:N`, `7_8:N` are lines of `paper/tex/1_2_Intro_model_result.tex`, `A_deterministic_estimates.tex`, `7_8_light_weight.tex`; `probe N` is line N of the probe; `(a) row k` is row k of the exponent table in `docs/reports/T2360-prove.md`; `Bk` is block k of its (b). File line counts are `wc -l`. The scripts are in the scratchpad subdirectory `T2360/` (not in the repository); their verbatim outputs are in (b).

## 0. The answer

| item | answer | where |
|---|---|---|
| K1 | 19 files, 16777 lines; 3166 are docstrings and instances; of the other 13611: **2610 reuse as is (R), 3238 generalise in place (G), 7541 twin (T), 222 not needed (X)**. `kProd` occurs in none (0 lines, B6): class (t) comes from the *star vertex* (one label per tree node, scalar `m(σ)`) and from the scalar-`ξ` closed forms of `Θ` (`Θ - 1 = ξSΘ`, row sums `(1-ξ)⁻¹`), not from a product structure (the explicit kernel `sbKernel` occurs once in the 19 files, `KLWard.lean:998`, B6). The BA tree sum is a different definition (cactus, non-scalar `M`), not an instance. **Route: G in place for K01, K02, K09a, K09b, twin for everything built on the star.** | §1 |
| K2 | **No gap.** `Θ_BA` is at real `t ∈ [0,1)` by type; the carrier data are `BAReal` for every `n` from `BAFlow` alone (merged `BAflow_real`); `STKboundgL` has no horizon. The reduction `BAKbound_of_uniform` is compiled (probe 110), with `inst_BAKbound` at `flow_sz0` (probe 343). | §2 |
| K3 | tree-representation_BA: gap in the TeX, formula verified numerically (`n ≤ 6`), band proof is not class (g); pure loops: complete one-sentence paper argument, merged inputs, class (t); sum-zero: gap in the TeX, verified (`n = 4, 6`), class (t); `lem_WI_K`: gap in the TeX, **class (g)** (band proof uses 4 facts about `S`), verified (`n ≤ 4`). | §3 |
| **F1** | **The merged `BAMLoop` (`BA/FlowPins.lean:274`) is not the paper's `(eq:KMloop)`** (`1_2:1003`): it pairs `σ_i` with `(a_i, a_{i+1})`, the trace `tr ∏ M(σ_i)E_{a_i}` and the paper's `M`-loop rule (`A:571`) pair it with `(a_{i-1}, a_i)`. For `n ≥ 3` and mixed charges the solution of the merged initial-value problem violates `(WI_calK)` (numerics, B8: defect 0.67 against right side 1.64 at `n = 3`) and the tree representation (error 0.32 against size 1.24). Repair first: row K00. | §3 |
| K4 | 16 compiled declarations, standard axioms; **16 rows, 12.7k central lines [9.2k .. 20.3k]**. | §4 |
| K5 | **Flag raised:** 16 rows > 12; (t) rows 9.1k central [6.5k .. 15.5k]. Reasons per file in §5. | §5 |
| K6 | BA ticket 35 (wide count); row count **16**; per-stage flag 1.5 × 16 = **24** tickets. | §6 |

Verdict: **design delivered, K1-K6 answered**; the paper's proof of the stage-K target does not apply to the merged carrier until F1 is repaired (K00); decisions needed from the supervisor are in §7.

## 1. K1: the 19 band KL files

Classes: **R** no band object in the statements (import and instantiate); **G** the band statement is about kernel-level objects (`IsKLoopS`, facts of `S`, abstract molecule weight `Sig` and edge family `TH`): restate in place, re-derive the band form; **T** twin (star vertex, scalar `m(σ)` or scalar-`ξ` closed forms of `Θ`); **X** not needed. Counts by segment (script `k1rows.py table`, B6); the segments are listed below the table: a boundary is a section header (`/-! ##`) or, inside a section (and in `KLCut`, which has none), the start of a declaration with its docstring (at most 2 lines off). The class of a segment is a reading of its statements, not compiled. "band tokens" = lines of non-docstring, non-instance code that mention `SB`, `Theta`, `thetaEdge`, `mSigma`, `mE`, `KLK*`, `KLSigmaPi`, `KLKpi`, `KLPT`, `Bparam`, `etaT`, `kTwo`.

| file (lines) | R | G | T | band tokens | class and reason | BA row |
|---|---|---|---|---|---|---|
| `KBound` (154) | 73 | 28 | 0 | 1% | (g): `inv_pow_pair_le` (`:90`) is real analysis; `KLoopBound` (`:74`, 28 lines) is the band pin, replaced by `BAKBoundAt` (probe 38) | K12 |
| `TreeRep` (188) | 141 | 0 | 0 | 4% | R: `LoopIdx`, `cutGlueL/R` are `S`-free; `treeEqRhs`, `IsKLoop` are the band wrappers of `IsKLoopS` (`KLTree.lean:846`, `Iff.rfl`) | none |
| `KLTree` (976) | 408 | 83 | 326 | 16% | mixed: laminar API (245), `KLtreeValW`, `IsKLoopS` (R); `KLPar`, `KLPT` interface (G); `KLK/KLn/KLgen`, `(Kn2sol)`, `KLSigmaPi` (T) | K04, K06 |
| `KLTreeDeriv` (1153) | 0 | 0 | 990 | 15% | (t): `hasDerivAt_Theta_mul_apply` (`Propagator/Deriv.lean:108`, `∂_tΘ_{tμ} = μΘSΘ`, scalar `μ`) on star values | K05a/b |
| `TreeThree` (471) | 0 | 0 | 431 | 33% | (t): `kThree`, the star at `n = 3` in `Θ_{tm₁m₂}` | K03 |
| `TreeFour` (252) | 0 | 0 | 0 | 30% | (x): `n = 4` special case, covered by the general representation (X 222) | none |
| `PureLoop` (290) | 0 | 0 | 244 | 4% | (t): `ThetaDecayShort (m σ)` and the star at `n = 2` | K07 |
| `KLMolecule` (1029) | 0 | 0 | 834 | 6% | (t): `KLselfW`, `KLSigmaPi` (δ-vertices), `KLShort`; §6 sum-zero | K07, K08 |
| `KLSumZero` (1080) | 88 | 0 | 697 | 9% | (t): closed forms `Q(σ,π)`, `A(σ,π)` from `Σ_bΘ(a,b) = (1-ξ)⁻¹` (`sum_Theta_row_of_three_le`) and `m(±)` | K08 |
| `KLSumZeroWard` (1265) | 174 | 0 | 937 | 7% | (t): molecule factorisation at an innermost long edge (star), uses `KLK_sumAll_le` (`KLSumAll.lean:729`), Lipschitz step | K06, K08 |
| `KLSumAll` (842) | 146 | 0 | 532 | 10% | (t): total sums of `KLK`, pure sign vectors, scalar `m`, row sums `(1-ξ)⁻¹` | K08 |
| `KLWard` (1224) | 132 | 966 | 0 | 13% | **(g)**: `S` enters through `SB_transpose` (`:504`), `sum_SB_row` (`:364`), `conj (SB a b) = SB a b` (`:996`), `norm_SB_apply_le` (`:739`); all four hold for `S = 1` (`kernelFacts_one`, probe 211) | K02 |
| `KLWardIneq` (1083) | 0 | 0 | 878 | 22% | (t): `K^{(π)}` with the last label summed, star trees, `sum_norm_Theta_row_le` | K11 |
| `KLUnique` (766) | 93 | 456 | 0 | 7% | **(g)**: uniqueness, rotation, translation; `S` only through `‖S a b‖ ≤ 1` (`Unique.lean:112`), symmetry (`SB_transpose`, `:357`) and translation invariance (`SB_apply_add_right`, `:156`) | K01 |
| `KLCut` (1648) | 829 | 0 | 438 | 0% | R: the surgery on `TSP` trees (`KLFIn`, `KLFOut`, `KLglueF`, `KLsum_cut` `:1297`) and the generic `KLgval` (`:58`); T: `KLtreeValW_cut`, `KLgval_in_eq`, `KLgval_out_eq`, `KLhasDerivAt_treeValW` (star) | reuse; K05 |
| `KLFinal` (541) | 52 | 149 | 131 | 8% | G: `stKbound_holds` assembly; T: `KLPT_holds` (BA has `baProp5to8_holds`); R: `L_rpow_le` | K12 |
| `KLInduct` (1394) | 22 | 258 | 836 | 24% | G: §7 (the induction step, with the cut identity as hypothesis); T: base `n ≤ 3`, cut at an internal edge, §6 layer `π = ∅` (`KLKpi_eq_sum_SigmaPi`) | K09b, K10 |
| `KLIndStepA` (1474) | 255 | 686 | 267 | 17% | **(g)** through `Sig`, `TH` (`IndStepAbs`, probe 261), except §4 `KLSigmaPi_reflect` (100) and §5 `KLsumZero_weighted` (167): they derive properties of the star molecule (T) and become hypotheses on `Sig`, proved by the BA molecule rows | K09a; K06, K08 |
| `KLIndStepB` (947) | 197 | 612 | 0 | 13% | **(g)** through `Sig`, `TH` | K09a |
| **total** (16777) | 2610 | 3238 | 7541 | 13% | `kProd`: 0 lines; star-tree objects (`KLtreeValW`, `KLselfW`, `KLSigmaPi`, `KLKpi`, `KLgval`): 284 lines | |

Segments (`python3 k1rows.py table`/`segments`, B6): `a-b:C` is lines `a` to `b` of class `C`, H header and docstring, I instances.
```
KBound        1-53:H 54-81:G 82-154:R
TreeRep       1-47:H 48-188:R
KLTree        1-34:H 35-119:R 120-244:T 245-327:G 328-349:R 350-490:T 491-735:R 736-795:T 796-851:R 852-976:I
KLTreeDeriv   1-72:H 73-1062:T 1063-1153:I
TreeThree     1-40:H 41-471:T
TreeFour      1-30:H 31-252:X
PureLoop      1-46:H 47-290:T
KLMolecule    1-40:H 41-874:T 875-1029:I
KLSumZero     1-50:H 51-138:R 139-835:T 836-1080:I
KLSumZeroWard 1-61:H 62-235:R 236-1172:T 1173-1265:I
KLSumAll      1-72:H 73-218:R 219-750:T 751-842:I
KLWard        1-68:H 69-200:R 201-1166:G 1167-1224:I
KLWardIneq    1-85:H 86-963:T 964-1083:I
KLUnique      1-75:H 76-203:G 204-296:R 297-624:G 625-766:I
KLCut         1-55:H 56-167:R 168-211:T 212-260:R 261-360:T 361-454:R 455-580:T 581-745:R 746-913:T 914-1322:R 1323-1648:I
KLFinal       1-52:H 53-183:T 184-235:R 236-384:G 385-541:I
KLInduct      1-82:H 83-342:T 343-364:R 365-940:T 941-1198:G 1199-1394:I
KLIndStepA    1-43:H 44-94:R 95-469:G 470-673:R 674-773:T 774-879:G 880-1046:T 1047-1251:G 1252-1474:I
KLIndStepB    1-45:H 46-68:G 69-265:R 266-854:G 855-947:I
Unique        1-52:H 53-111:R 112-308:G 309-373:T 374-374:H
Primitive     1-37:H 38-158:T 159-159:H
```
Dependencies outside the 19: `Loop/Unique.lean` (374; R 59: cut-length lemmas and `LoopVec`; G 197: `norm_SB_apply_le` `:112`, `eq_on_level`, `isKLoop_unique`, `KLretire_twoLoopBounded`, where `S` enters only through `norm_SB_apply_le` and `hL` only feeds it; T 65: `kTwoFormula_of_isKLoop`, `pureLoop_two_of_isKLoop`, which use `kTwo`, `norm_SB`), `Loop/Primitive.lean` (159; T 121: `kTwo`). No file is class (b) in the ticket's sense; the BA-only objects without a band counterpart are row K00 (the `Θ_BA` calculus: `∂_tΘ = ΘMΘ`, `Θ = 1 + tMΘ`, invertibility for all four charge pairs) and row K04 (the cactus).

**Band consumers of the (g) files and how they are re-derived** (script `consumers.py`, B6; the statements stay as they are, the old name becomes a wrapper):
* `Unique`: `isKLoop_unique` (used by `KLUnique`), `KLretire_twoLoopBounded` (`KLUnique`, `KLWard`, `TreeThree`): the generic statement at `S = SB d L g`, `M = MLoop` (`IsKLoop` is `IsKLoopS` by `Iff.rfl`); **compiled** for `isKLoop_unique` (`UniqS`, probe 232; `isKLoop_unique_of_UniqS`, probe 241; BA instance `baK_unique_of_UniqS`, probe 250); `kTwoFormula_of_isKLoop` (`KLUnique`, `TreeThree`) and `pureLoop_two_of_isKLoop` are band 2-loop formulas, not re-derived: twin in K03.
* `KLUnique`: `KLK_unique` (`KLWard`), `KLK_rotate` (`Graph/LWExpTerm`, `LWExpTerm4`; `Induction/ExpWardII`, `NewPQ`, `SEforLn1`, `SEforLn2`, `WardII`; `KLSumAll`, `KLWard`), `KLK_translate` (`KLSumAll`): instances at `(SB d L g, mSigma E, MLoop)` applied to `K = KLK` (`KLK_isKLoop`, `KLTreeDeriv.lean`).
* `KLWard`: `KLK_ward` (`Induction/B45`, `NewPQ`, `QLevelsA`; `KLSumAll`), `KLWard_flip` (no consumer): instance at `S = SB` with `kernelFacts_SB` (probe 218, compiled).
* `KLIndStepA/B`: `KLindStep_nonAlt` (`KLIndStepB`), `KLindStepPin_holds` (`KLInduct` ×2, `KLWardIneq` ×2), `KLindStepAt_holds`, `KLindStep_alt` (no consumer): `KLindStepAt` is `IndStepAbs` at `(KLPar, KLSigmaPi, thetaEdge)` by `Iff.rfl` (`KLindStepAt_iff`, probe 271, compiled). The band proofs carry `hPT : KLPT d κ gmax` (`KLIndStepB.lean:832`); the abstract version takes the Θ-property bundle of `TH` as its hypothesis in place of `KLPT`, to be supplied by the BA bundle `baProp5to8_holds` (K12).
* `KLInduct` §7: `KLboundPin_holds` (`KLFinal`), `KLKpiBoundPin_holds`, `KLInduct_BoundAt_of_Kpi` (no consumer): the generic induction takes the cut identity `KLKpi_cut` as hypothesis; the band instance supplies it.
* `KBound`, `KLTree` §3: `KLoopBound` (used by `KLFinal` ×2) and `KLPar`, `KLPT` (used by `KLFinal`, `KLIndStepA/B`, `KLInduct`, `KLWardIneq`, `KLMolecule`, `KLTree`; `KLPar` also by `Induction/NQEndFlowLift`) are not restated: BA has its own `BAKBoundAt` (probe 38) and its own bundle (K12).
* R segments are imported unchanged by the BA files, no restatement: `KLsum_cut` (used by `KLInduct`, `KLSumZeroWard`, `KLTreeDeriv`), `inv_pow_pair_le` (`KLIndStepA`), the laminar API, `KLtreeValW` and `KLwholeP` of `KLTree` (also used by `Induction/KDecay`), `TreeRep`.
* `KLFinal`: `stKbound_holds` (`Induction/KDecay`, `NQEndLin`, `QDriftA`, `QDriftB`, `QEndA`, `QEndGrid`, `QtNonzeroEnd`), `stKward_holds` (`KDecay`), `KLbound_holds` (`NQEndFlowLift`) stay as they are; the private `KLFinal_prec_of_loss` (`:212`) is `precL_of_loss` at the band law (`Prec_of_loss`, probe 351, one line).

**Route.** G in place exactly where the band statement is already about kernel-level objects (K01, K02, K09a, K09b: 1.9k central lines, 452 + 612 + 472 + 357, for 3175 G lines in `Unique` 197, `KLUnique` 456, `KLWard` 966, `KLIndStepA` 686, `KLIndStepB` 612, `KLInduct` §7 258; a twin of the same lines is 2.7k at 0.85, 0.8k more); twin for everything built on the star vertex. The "G in place" of the star objects is not possible, §5.

## 2. K2: inputs and quantifiers

* `FlowFM.K`, `BAKloop`, `BAKsol` and `BATheta` take `t : ℝ` (`BA/FlowPins.lean:336, 296, 281`; `BA/MFixedPoint.lean:515`), `IsKLoopS` is on `T : Set ℝ` (`Loop/KLTree.lean:828`): a complex `t` cannot occur.
* Every `Θ_BA` and `M` of the carrier `baFMz sz z` (`FlowPins.lean:550`) is at the data `(g₀_n, κ, E_n, m₀_n)` with `BAReal`, for every `n`, from `BAFlow` alone: merged `BAflow_real` (`BA/GreenSchur.lean:59`) through `BAdom_real` (`MFixedPoint.lean:479`); `BAReal` does not depend on `t`. `BAflow_lam0_window` (`GreenSchur.lean:72`): `0 < g₀_n ≤ 𝔡⁻¹` eventually.
* `STKboundgL` quantifies every `τ ∈ [0,1)` (`FlowPins.lean:424-428`): no horizon enters. `lemT` (`Defs/Semicircle.lean:193`) is the band horizon; the BA horizon is `BAflowT0` (`FlowPins.lean:537`), not used.
* The pin states `B` at the coupling `sz.lam n`, the carrier is at `g₀_n = √t₀ sz.lam n ≤ sz.lam n`: `B(g₀) ≤ ((κ+1)/κ) B(g)` (`bparam_comp`, probe 84, and `t0_ge`, probe 99), so the pin follows with the constant `C((κ+1)/κ)^{k-1}`.
* **The pin** (probe 49): `BAKbound d := 3 ≤ d → ∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∀ 𝔠 sz z, BAFlow sz κ ε 𝔠 𝔡 z → STKboundgL (baFMz sz z) (seqP (sz.withLam 0))`, constants first as `STMainIndG` (`FlowPins.lean:565`). Its uniform deterministic form (probe 38): `BAKBoundAt d n Λ κ`, loss `C L^τ`, real `t ∈ [0,1)`, `BAReal d L g κ E m`, `g ∈ (0, Λ]`, `W ≥ 1`.
* **Compiled:** `BAKbound_of_uniform` (probe 110): `(∀ Λ κ n, … → BAKBoundAt d n Λ κ) → BAKbound d`; `precL_of_loss` (probe 58, any law: the failure event is eventually empty); `BAKBoundAt_one` (probe 318, the case `n = 1`, unconditional); `inst_BAKbound` (probe 343, `d = 3`, `sz0`, `flow_sz0`, every deterministic hypothesis discharged, the uniform bounds stay the hypothesis `U`).
* **Limit check of `U` at `d = 3`** (B9, Python, finite tori `Z_L^3`, `L ≤ 5`, `W = 1`, `g ∈ {0.1, 0.2, 0.5, 1.0}`, `E = 0.3`, `1-t` from 1e-1 to 1e-5, `n = 2..5` (`n ≤ 4` at `L = 4`, `n ≤ 3` at `L = 5`), the tree sum of §3 (a)): `max_{σ,a}|𝒦^{(n)}| / B_{t,0}^{n-1}` lies in `[0.007, 1.57]` (largest at `g = 1`, `n = 5`, `1-t = 1e-2`) while `B` ranges from 1.3 to 3.8e3; the pinned bound is not contradicted, this is a finite-size check at `W = 1`, not a limit.
* **Differences from the T2161 probe pins** (`T2161-portmap.md:553-569`): `BAKbound` is stated with `STKboundgL` (merged, `FlowPins.lean:424`) at the law `seqP (sz.withLam 0)` and `3 ≤ d →`, where the old pin had `STKboundg`; `BAKsolve` has no uniqueness clause: uniqueness is `UniqS` (probe 232, row K01) together with the 2-loop bound of `KLretire_twoLoopBounded` (`Loop/Unique.lean:294`, continuity of any family of `K`-loops on `[0,T₀]`), not compiled here.
* Two further facts. (i) `BAKsol` is a `Classical.choose`, `0` without a solution (`FlowPins.lean:285-286`): `BAKbound` is empty without existence, so the closing condition of stage K contains **`BAKsolve`** (probe 281: existence on `[0,1)` and `(Kn2sol)`); `BAKsol_isKLoopS` (probe 293) shows `BAKsol` is the solution it provides. (ii) F1.

## 3. K3 (paper status of the BA-specific items) and finding F1

Definitions fixed here, used by all numerics (B8): `M(+) = M^{(B)}`, `M(-) = M^{(B)*}`, `M^{(σ₁σ₂)}_{ab} = M_{ba}(σ₁)M_{ab}(σ₂)`, `Θ^{(σ₁σ₂)} = (1 - tM^{(σ₁σ₂)})⁻¹` (`1_2:1073`), `S = I`; for the symmetric `M` of BA, `Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}` (`BATheta_swap`, probe 387). The ODE is `treeEqRhsS` (`KLTree.lean:809`), solved with RK4 on `Z_q` (`d = 1`, `W = 1`), `M` from `(self_m)` (`Ward row sum 1.0000000000000002`, `M - M^* = 2i Im m MM^*` to 2.5e-16, B8).

| item | paper | does the band proof transfer as class (g)? | argument |
|---|---|---|---|
| (a) `tree-representation_BA` (`A:592-598`) | statement and the `M`-graph rules `A:380-583`; proof = "[RBSO1D L4.16]"; stated for `n ≥ 4` (`A:593`), `n = 3` is `(Kn3sol)` (`1_2:1176`), the same formula with one tree | **no**: `KLTreeDeriv` differentiates star values with `∂_tΘ_{tμ} = μΘSΘ`; here `∂_tΘ^{σσ'} = ΘM^{σσ'}Θ`, `∂_t(tΘ^{σσ'}) = Θ²`, and a node is an `M`-cycle (K04, K05) | **gap in the TeX.** Formula verified: `max |Σ_F Γ_M(F) - K_ODE|` ≤ 2.0e-8 for `n = 3..6` (1, 3, 11, 45 trees), all `σ`, all `a`, 3 data sets (`n = 6` on the third; B8). Rules read from `A:552-583`: leaf `v`: `Θ^{(σ_v,σ_{v+1})}(a_v, ·)`; chord `J = (i,j)`: `tΘ^{(σ_i,σ_j)}`; the `M`-edge between consecutive edges of a node has the charge `σ_x` of the boundary edge ending at the first vertex `x` of the next edge's vertex range (the paper's rule, `A:571`: the edge `b_{j-1} → b_j` carries `σ_j`; which region an edge lies in is read from the figure). Outline for the 1a of K05 (ours): leaf `v` ↔ the pair `(v+1,v+2)` of `treeEqRhsS` (a bigon `K^{(2)}(a_v,x) = (ΘM)(a_v,x)` times the `n`-loop with `a_v ← x`); chord `(i,j)` ↔ the pair `(i+1,j+1)` (`Θ² = Σ_uΘ(·,u)Θ(u,·)`, two polygon cacti glued at `u`, through the `S`-free bijection `KLsum_cut`); `n ≤ 3` from K03; uniqueness (K01) identifies `BAKsol`. |
| (b) pure loops (`A:643-654`, `Mbound_AO(2)` `7_8:1891, 1902`) | one-sentence argument `A:654`: only `M`-edges and short edges, `(prop:ThfadC_short)` and `(Mbound_AO)` | no (class t: cactus instead of star) | **complete paper argument**; merged inputs: `baPropM_holds` (`BA/CombesThomas.lean:562`; items (5),(6) of `BAPropM`, `MFixedPoint.lean:567`, = `Mbound_AO`, `Mbound_AO2`), `baProp5s_holds` (`BA/Prop5Short.lean:667`), `BAK_off_le` (`KKernel.lean:198`). BA twin of `KLMolecule` §2-5 with a spanning-tree reduction (every edge kernel is `≤ B e^{-κ|x-y|}`) |
| (c) sum-zero (`A:728-734`, Claim 4.30) | cited: `[YY_25 L3.10]`, `[RBSO1D L4.29, Claim 4.30]`; ingredients listed `A:734` | no: the band proof (2300 T lines: `KLMolecule` §6, `KLSumZero`, `KLSumZeroWard` without its §3 (in K06), `KLSumAll`, `KLIndStepA` §5 weighted) is stated over `KLSigmaPi` and scalar closed forms | **gap in the TeX.** First estimate verified on the BA molecule `Σ^{(∅)}` (all trees without long chord, leaf edges removed), alternating `σ`: signed slice sum `0` at `t = 1` (≤ 1.3e-15) and `|sum|/(1-t)` = 1.0208 at `1-t = 1e-5` (`n = 4`, `q = 5`), 3.93 at `1e-3` (`n = 6`, `q = 3`), 0.72 at `1e-3` (`n = 4`, `q = 4`), B8. The second estimate is not tested (one data set, `g = 0.8`, absolute slice sum 2.36: no scaling in `g` is probed). The band skeleton is the blueprint: `(3.49)` from the Ward bound, `(3.50)` induction, Lipschitz step, `R_n(1) = 0` (`KLSumZeroWard` §6-9); BA changes: row sums of `M(σ)` and `M^{(σσ')}` replace `(1-ξ)⁻¹`; `Σ_bM^{(+,-)}_{ab} = 1` (`BAK_row_sum`, `KKernel.lean:124`) |
| (d) `lem_WI_K` (`1_2:1034-1046`) | cited: `[RBSO1D L3.17]` | **yes (class g)**: `KLK_ward` is an ODE-defect and Grönwall argument (`KLWard.lean:22-30`) that uses `S` through four facts, all true for `S = I` | band proof is the argument. BA data facts needed: `M`-loop Ward at `t = 0` (`M - M^* = 2i Im m MM^*`; `BAMB_ward_row`, `Ward.lean:108`), level 2 (`BAK_row_sum`), flip `M(-) = conj M(+)` (`BAMB_symm`), cyclic invariance (K01). Verified: `max|Σ_x K^{(n)} - (2iW^dη_t)⁻¹(K^{(n-1)}_+ - K^{(n-1)}_-)|` ≤ 9.7e-9 for `n = 2,3,4` (`η_t = (1-t) Im m`, `ztOf`, `GLoopFlow.lean:55`), B8. T2325 item (e) ("not supported by `BA/Ward` or `BA/KKernel`") is right for the data only. `lem_wardineq_K` (`A:811-827`): complete paper argument from `(eq:ind-step-bound)` plus the induction (K11) |

**F1 (the carrier is not the paper's `𝒦`).** `BAMLoop` (`FlowPins.lean:274-276`) is `W^{-(n-1)d} ∏ M(σ_i)_{a_i a_{i+1}}` (`I.a.zip (I.a.rotate 1)`). The paper's `(eq:KMloop)` (`1_2:1003`) is `tr ∏ M(σ_i)E_{a_i} = W^{-(k-1)d} ∏ M(σ_i)_{a_{i-1} a_i}`: the charge `σ_i` sits on the edge *ending* at `a_i`, as in `loopM` (`Loop/GLoopFlow.lean:92`) and in the cuts `cutGlueL/R` (`Loop/TreeRep.lean:75-82`, `1_2:930-931`), and as in the paper's rule for the `M`-loops of a tree (`A:571`: the edge `b_{i,j-1} → b_{i,j}` carries `σ_j`, `a_j = b_{i,j}`). B8: the trace equals the paper form to 5.6e-17 and differs from `BAMLoop` in 108 of 216 `(σ, a)` at `n = 3` (none at `n = 2`); with `BAMLoop` the ODE solution misses the tree sum (0.32 at `n = 3`, 0.62 at `n = 4`, against sizes 1.2, 2.2) and `(WI_calK)` (0.67, 1.2 at `n = 3`; 0.55, 1.9 at `n = 4`), with the paper form both hold to 1e-8. Lean witness (probe 168-197): `BAMLoop'` is the paper form; at `Z_3`, `σ = (+,+,-)`, labels `(0,1,2)`: `BAMLoop = 14`, `BAMLoop' = 15`. Consequence (inference, not compiled): `STLKgL (baFMz …)` cannot be expected at `t = 0` for `n ≥ 3` (`K_0` differs from `tr ∏ M E` by an `O(1)` factor at the order `W^{-(n-1)d}`, the pin allows `W^{-nd}`). `BAMLoop` occurs only at `FlowPins.lean:274, 283, 286` (grep B6); `baFM` is mentioned on 302 lines of 10 files, and only `FlowPins.lean` among them mentions `BAMLoop`. Row K00: change the body in place (no signature change); a primed successor would re-point those 302 mentions.

## 4. K4: deliverables

**Pins and proofs in the probe** (`lake env lean` exit 0, `lake build RBM3D.Probe.T2360Pins` clean, 16 declarations on the three standard axioms, 0 forbidden tokens: B1, B2): `BAKBoundAt` (38), `BAKbound` (49), `precL_of_loss` (58), `bparam_comp` (84), `t0_ge` (99), `BAKbound_of_uniform` (110), `BAMLoop'` (168), `BAMLoop_witness` (180), `KernelFacts` + `kernelFacts_one/_SB` (204-228), `UniqS` (232) + `isKLoop_unique_of_UniqS` (241) + `baK_unique_of_UniqS` (250), `IndStepAbs` (261) + `KLindStepAt_iff` (271), `BAKsolve` (281) + `BAKsol_isKLoopS` (293), `BAKward` (306), `BAKBoundAt_one` (318), `inst_BAKbound` (343), `Prec_of_loss` (351), `BATreeRep` (362: `Γ` a parameter, defined by K04), `SumZeroAbs` (374) + `KLsumZeroAt_iff` (381), `BATheta_swap` (387).

**Row table** (script `k1rows.py rows`, B7). Bases are sums of the segments of §1 (non-docstring, non-instance), shown in the last column. **Twin ratios, measured** (BA lines / band lines of merged stage-P twins): `BA/Prop5` 1.06, `PropUnit` 1.11, `Prop5Short` 1.61, `Prop6Path` 2.10, heat family 1.84; and `T2325-portmap.md:23`: 0.73 (S-chain), 0.85 (graph L2). Clean twin TW: lo 0.73, central 0.85, hi 1.11. Cactus twin CT (the structure changes): lo 0.85, central 1.20, hi 2.10. Class (g): edited fraction `g` of `T2326-pilot.md` §0: 0.15, 0.24, 0.30, plus wrappers (15 lines per band consumer name of §1: K01 5, K02 2, K09a 4, K09b 3) and the BA instance (assumed constants). Class (b) rows K04 and K12 carry assumed sizes (no band base); K12 is anchored on the 391 lines of the band assembly. These are assumptions with measured end points, not measurements of K. For comparison, the old K rows (`T2161-portmap.md:975`) were 5 rows, 6.1k central [4.6k .. 8.4k].

| row | file(s) | kind | lo | central | hi | deps | role | target | basis |
|---|---|---|---|---|---|---|---|---|---|
| K00 | `BA/KBase.lean`; in place `BA/FlowPins.lean` (`BAMLoop`) | b | 503 | 579 | 744 | - | prover-hard | `BAMLoop'` body in place; `Θ_BA` calculus at real `t ∈ [0,1)` (invertible, `∂_tΘ = ΘMΘ`, `Θ = 1+tMΘ`, symmetric, `(-,-) = conj (+,+)`, row sums of `(+,-)`) | 634 (`Propagator/{Basic,Deriv,Props4}`) × TW + 40 |
| K01 | `Loop/Unique.lean`, `Loop/KLUnique.lean` in place; `BA/KUnique.lean` | g | 323 | 452 | 571 | K00 | prover-hard | `UniqS` (probe 232), rotation, translation; BA instances | 653 G × g + 5×15 + 150/220/300 |
| K02 | `Loop/KLWard.lean` in place; `BA/KWard.lean` | g | 425 | 612 | 770 | K01 | prover-hard | generic Ward over `KernelFacts`; `BAKward` (probe 306) | 966 G × g + 2×15 + 250/350/450 |
| K03 | `BA/KSolve.lean` | t | 550 | 624 | 785 | K01 | prover-hard | `BAKsolve` for `n ≤ 3`: `K^{(2)} = W^{-d}ΘM^{(σσ')}` (verified, 4.1e-12), the star at `n = 3` | 617 T × TW + 100 |
| K04 | `BA/KCactus.lean` | b | 500 | 700 | 1000 | K00 | prover-max | cactus (nodes, slots, ranges, `M`-edge charges, `KLgval` instance); `BATreeRep`'s `Γ` | assumed |
| K05a | `BA/KTreeDeriv.lean` | t | 660 | 932 | 1630 | K03, K04 | prover-max | derivative of cactus values, leaf terms | 1553 T × CT / 2 |
| K05b | `BA/KTreeRep.lean` | t | 660 | 932 | 1630 | K05a | prover-max | chord terms, pair bijection; `BATreeRep` (probe 362) | 1553 T × CT / 2 |
| K06 | `BA/KMolecule.lean` | t | 482 | 680 | 1191 | K05b | prover-hard | `K^{(π)}`, `Σ^{(π)}`, `(eq_K-Kpi)`, `(eq:molecule-Kpi)`, factorisation at an innermost long edge | 567 T × CT |
| K07 | `BA/KPure.lean` | t | 718 | 1014 | 1774 | K06 | prover-hard | pure loops, `(eq:molecule-decay)` | 845 T × CT |
| K08a | `BA/KSumZeroA.lean` | t | 978 | 1380 | 2415 | K02, K07 | prover-max | Ward bound for sums of `K`, signed sum-zero | 2300 T × CT / 2 |
| K08b | `BA/KSumZeroB.lean` | t | 978 | 1380 | 2415 | K08a | prover-max | closed forms, absolute sum, `SumZeroAbs` (probe 374) | 2300 T × CT / 2 |
| K09a | `Loop/KLIndStepA.lean`, `KLIndStepB.lean` in place | g | 355 | 472 | 549 | - | prover-hard | `IndStepAbs` (probe 261); `KLindStepAt` by `Iff.rfl` | 1298 G × g + 4×15 + 100 |
| K09b | `Loop/KLInduct.lean` §7 in place; BA instance of the interface | g | 234 | 357 | 472 | K09a, K08b | prover-hard | generic induction on molecules; BA instance | 258 G × g + 3×15 + 150/250/350 |
| K10 | `BA/KInduct.lean` | t | 771 | 1063 | 1816 | K05b, K06 | prover-hard | base `n ≤ 3`, cut at an innermost long edge | 836 T × CT + 60 |
| K11 | `BA/KWardIneq.lean` | t | 746 | 1054 | 1844 | K02, K10 | prover-hard | `lem_wardineq_K` | 878 T × CT |
| K12 | `BA/KBound.lean` | b | 350 | 500 | 700 | K09b, K10, K11, K08b | prover-hard | `BAKBoundAt` for every `n`, `BAKbound` (from probe 110), `BAKward`, the carrier form of `STKward`; bundle `BAProp5to8` to the interface | assumed |
| **sum** | 16 rows | | 9233 | **12731** | 20306 | | | (t) rows: 6543 / 9059 / 15500 | |

Order: K00; then K01, K09a in parallel; K02, K03, K04; K05a, K05b; K06, K07; K08a, K08b, K10; K09b, K11; K12. A design check at K04 (the cactus API) before K05 is advised.

**Exponent table** (the bookkeeping of `(W^{-d}B_{τ,0})^{k-1}` uses these thresholds; all hold along `sz0`, `(a)` (ii)):

| quantity | value | constraint | slack |
|---|---|---|---|
| exponent | `k-1`; `k = 1` gives 1 (`BAKBoundAt_one`) | `k ≥ 1` | none |
| constant per factor | `(κ+1)/κ` | `Im m ≥ κ`, `Im z ≤ 1` (`BAdom`); `t0_ge` | `κ = 1/2`: 3; along `sz0`, `t₀ ≥ 2/3` (`t0_sz0`, `FlowPins.lean:1379`): 3/2 |
| loss | `C L^s ≤ N^τ`: `L^s ≤ N^{s/d}`, `C ≤ N^{τ/2}` eventually | `N → ∞` (`Admissible`) | any `τ > 0` |
| coupling | `0 < g₀_n ≤ 𝔡⁻¹` eventually | `(eq:WO)` | `𝔡 = 1/10`: `g₀ ≤ 10`; `sz0`: `g_n = (2(n+1))^{-6}` |

**Instance** (probe 343): `inst_BAKbound` is `BAKbound_of_uniform` at `d = 3`, `sz0`, `zSeq`, `κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10` (`flow_sz0`); `n = 0` of `sz0` is `L = 4`, `W = 32`, `N = 2097152`, `g = 1/64`, `Im m₀ = 0.9995`, `t₀ = 0.694` ((a) (ii), B4). `U` is a statement about `BAKsol`, hence about `BAMLoop`: at the merged body its truth is not known (F1); after K00 it is the paper's `ML:Kbound` at `BAReal` data, whose finite checks are B8 (identities, `d = 1`) and B9 (`d = 3`).

## 5. K5: why the (t) files cannot be generalised in place

Flag: 16 rows (> 12); (t) rows central 9.1k, hi 15.5k (> 10k at hi only). Common reason: the star vertex is *definitional* in `KLtreeValW` (one label per node, `b : ↥(KLnodes F) → Zd d L`, leaf entries `M v (a v) (b (leafPar v))`, `KLTree.lean:114-119`); a cactus has one label per slot. Every theorem about the star sum would be restated over a different sum, and the band instance would be recovered not by `Iff.rfl` but by a bridge theorem (cactus value at `M(σ) = m(σ)I` equals the star value, by induction over the tree), after which every band consumer that names `KLK`, `KLSigmaPi` or `KLKpi` (the 284 star-object lines and the consumers of §1: `KLK_isKLoop` is used by `Induction/AzumaProxyN`, `GridDriftN`, `HierAlgebra`, `NQEndFlowLift`) would go through it. The (g) route is used where no such bridge is needed.

* `KLTree` §1-5, §6 `KLSigmaPi_empty_symm` (326): defines `KLK`, `KLn`, `KLgen` by the star sum with scalar `m`; BA objects are other definitions.
* `KLTreeDeriv` (990): `hasDerivAt_Theta_mul_apply` has a scalar `μ` and a fixed `S`; the term bookkeeping (`leaf_term`, `internal_term`, `diag_pair_term`, private) is over star values.
* `TreeThree` (431): `kThree` is the star in `Θ_{tm₁m₂}`; BA `K^{(3)}` has `M`-edges.
* `PureLoop` (244), `KLMolecule` (834): `ThetaDecayShort (m σ)`, `KLShort`, and `KLselfW` with `δ`-vertices; BA molecules have `M`-edges (decay from `Mbound_AO`, spanning-tree reduction).
* `KLSumZero` (697), `KLSumZeroWard` (937), `KLSumAll` (532): closed forms from `Σ_bΘ(a,b) = (1-ξ)⁻¹` (`sum_Theta_row_of_three_le`) and `m(±)`, `norm_mul_mSigma_lt_one`; for BA the row sums are those of `M(σ)` and `M^{(σσ')}`.
* `KLIndStepA` §4 (100), §5 weighted (167): `KLSigmaPi_reflect`, `KLsumZero_weighted` derive reflection symmetry and the pointwise `g²` gain of `Σ^{(∅)}` from the star tree (`KLselfW_reflect`, `KLMolecule_selfW_bound_nc`, `KLMolecule_edge`).
* `KLWardIneq` (878): `K^{(π)}` with the last label summed over star trees; 22% of its code lines mention `Theta`, `thetaEdge`, `mSigma`, `Bparam`.
* `KLCut` star lemmas (438): `KLtreeValW_cut` (`:282`), `KLgval_in_eq` (`:455`), `KLgval_out_eq` (`:746`), `KLhasDerivAt_treeValW` (`:178`); the `TSP` surgery (829 lines, `KLsum_cut`) is reused.
* `KLInduct` (836): §6 layer `π = ∅` (`KLKpi_eq_sum_SigmaPi`), base cases `KLK_two`, `KLK_three` (band closed forms), `KLKpi_cut` (via `KLtreeValW_cut` with `P = ξ_J•I`, `S = S^{(B)}`: uses `Θ - 1 = ξ_J SΘ`, which BA does not have: its chord is `tΘ`).
* `KLFinal` §1-2 (131): `KLPT_holds` bridges the merged band props 5-8; BA has `baProp5to8_holds`.

## 6. K6

BA-DK is ticket 35 in the wide BA count (DECISIONS §163 (2)). Stage K: **16 rows**; per-stage flag 1.5 × 16 = **24** tickets; rows K05, K08 are the ones that may split further (hi 1.6k, 2.4k per half).

## 7. Decisions requested and paper-delta candidates

1. **F1 repair mode** (before any K proof ticket): in place (recommended, K00) or primed successors.
2. **Route:** G in place for K01, K02, K09a, K09b (edits four merged band files; wrappers keep every band name) against a twin of the same 3175 lines (+0.8k central lines).
3. **TEAM §3:** K05 and K08 start from our argument (the paper cites `[RBSO1D]`; DECISIONS §5: only [LANDON20191137] Thm 2.2 is an authorised external input, the `[RBSO1D]` results of §2 item 3 group 4 are internal): accept the band Lean proof plus the numerics of §3 as the blueprint for their 1a, or authorise the two cited lemmas.
4. **Closing conditions of stage K** add `BAKsolve` and `BAKward` to `BAKbound`; the carrier form of `STKward` (`Induction/Step34Pins.lean:229`; consumers `Graph/LWExpTerm`, `LWExpTerm4`, `Induction/KDecay`) does not exist (`grep STKwardgL`: 0) and is to be pinned by K12 in the shape of `BAKbound`.
5. The wide risk is K05, K08 (hi 3.3k, 4.8k).

Paper-delta candidates (temporary tags): `T2360a` the merged `BAMLoop` pairing against `(eq:KMloop)` and `A:571` (Lean defect, F1); `T2360b` `(f-internal2)` with `S^{(B)} = I`: the chord is `tΘ^{(σ_i,σ_j)}`, and which region an `M`-edge lies in (`A:570-574`) is read from the figure, §3 (a) states the rule combinatorially; `T2360c` `Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}` for the symmetric BA `M` (a remark, not a difference; `BATheta_swap`, probe 387); `T2360d` the pin `BATreeRep` (probe 362) states `n ≥ 3` where `tree-representation_BA` states `n ≥ 4` (`A:593`); `n = 3` is `(Kn3sol)` (`1_2:1176`), the same formula with one tree.; `T2360e` `BAKBoundAt` reads `≺` of `ML:Kbound` as a loss `C L^τ` with `C` uniform in `L`, `W`, `g ≤ Λ`, `E`, `t` (the merged convention of `KLBoundAt`, `Loop/KLInduct.lean:84-89`, which implies the paper's `≺`; the converse fails): stronger than the paper, the implication is `BAKbound_of_uniform` (probe 110).
