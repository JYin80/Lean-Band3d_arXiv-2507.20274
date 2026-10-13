Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 08:16:20 UTC 2026
Basis: worktree base `main` 6ccc6be2 (`main` is now 1843bd31 = T2494 merge; the five band files and `Test/Axioms.lean` are unchanged between the two). Paper `3_5_Loop_Hierarchy.tex:2308-2338` (`lem_dec_calE`), `PfStep5Grid:130` (D1 pin). Scripts and outputs in scratchpad `T2496/` (`$S`). No Lean written.

### (i) Exponent table (`B=(1-u_k)^-1`, `N=(WL)^d`, `Q=N^2`; ratios are measured/needed, need <= 1)
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | D1 numerals `64`, `7` | `pfStep5Grid_abs` (`PfStep5Grid:287`, model-free) gives `64 B^7 (R+ΔM)` from: `‖P_j‖,‖X_j‖ ≤ B²`, `‖X_j-1‖ ≤ 3ΔB²`, `‖X_j-1-ΔΘ_j‖ ≤ 3Δ²B²`, `‖Θ_j‖ ≤ 2B`, `‖Θ_j-Θ_{j+1}‖ ≤ 2ΔB²` | all six follow from K1-K3 alone: `T_t:=thetaKer_t=(uKer(s,t)-1)/(t-s)` (affine in `s`), so `‖T_t‖ ≤ (1-t)^-1` by K3; `T_v-T_w=(v-w)T_vT_w`; `X_j=a⊗b`, `a=1+ΔT_{u_{j+1}}`; row sums multiply on 2-tensors; `Θ=T⊗1+1⊗T`; terms: `(α-ΔT)⊗1+1⊗(β-ΔT)+α⊗β ≤ 3Δ²B²` | measured (B=5 / 20): P 1.000 / 1.000 (tight at `u_0=0`), X1 0.147 / 0.049, X2 0.889 / 0.675, Θ 0.833 / 0.513, ΘΘ 0.595 / 0.177 |
| 2 | D1 inequality (6 random draws of `A_0,F,Rem,Mart` per row) | LHS / `64B^7(R+ΔM)` ≤ 2.5e-6 | ≤ 1 | ≥ 4e5 (the bound is loose; the six inputs above carry the content) |
| 3 | D1 hypotheses K1-K3 at `X=M^{(+,-)}` (stochastic: Ward, row sums 1) | K1 residual ≤ 8e-14; K2, K3 equalities (residual ≤ 1.2e-12 = round-off) | `≤ (1-v)/(1-w)`, `≤ |t-s|(1-t)^-1` | 0 (equalities); ratios identical for `g=1/64,1,10`: norms of non-negative kernels see only row sums, so D1 holds with `g`-free constants |
| 4 | D2 entry modulus, `Xentry` off-diagonal `ω_re+iω_im`, `|ω_c| ≤ N` on `contGood` (`ContinuityNet:225`) | true sup `√2 N`; Lean `cont_norm_Xentry_le` (`ContinuityNet:526`) gives `2N` | text `≤ N^c √|Δu|` constant-free: `c=1` **fails** (ratio 1.4142 true / 2.0 crude); `c_min` = 1.024 / 1.048 (N=2097152), 1.105 / 1.210 (N=27) | amendment **A1**: text `≤ 2 * N^c * √|Δu|`, `c=1` (band and BA: `g₀Ψ` cancels in `H_u-H_u'`, `V` entries also `≤ 2N`); true sup is 0.707 of it |
| 5 | D2 Hölder 1/2 | `|√u-√u'| ≤ √|u-u'|` (`cont_abs_sqrt_sub_sqrt_le`, `ContinuityNet:499`) | sup ratio 1 (at `u'=0`) | 0 |
| 6 | loop modulus from D2 (`cont_green_flow_diff`, `ContinuityNet:582`): `N k Q^k Q² (Xb+1)√|Δu|`, `Xb=N·2N^c` | `≤ 3k N^{2k+c+6}`; `c=1`: `3kN^{2k+7}` = band `LemDecCalELip_Lloop_sub` (`:277`) | must equal the band type (G1: readers `QtXiRoundLift`, `QtNonzeroFlowLift`, `NQEndFlowLift`, `EtermsMid`) | k=2, N=27: 2.2e16 ≤ 3.3e16 (0.67); N=2097152: 1.4e70 ≤ 2.1e70; constant-free `c=2`: 3.0e17 > 3.3e16, type lost (needs A1) |
| 7 | D2 event `HighProbAt`: `P(G^c) ≤ 2N²·2e^{-N²/2}` (`cont_good_compl`) | log10 = -9.55e11 (N=2097152), -154.8 (N=27) | ≤ `N^-D` eventually (D=10: -63.2 / -14.3) | 9.5e11 / 140 orders of magnitude |
| 8 | D3 `𝒦^{(2)}`: `≤ N^{2k+2}|Δu|`, k=2: `N^6` | band true Lipschitz `N²` (`Θ_ζ-Θ_ξ=(ζ-ξ)Θ_ζSΘ_ξ`, `LemDecCalELip:349-351`); measured (BA-type kernel, g=10, N=27, `t=1-1/N`) max 506 | `≤ N^6`; **the merged `LemDecCalELip_STKloop_two_sub` states `N²√|Δu|` (Hölder), not the D3 text** | 506 ≤ 729 = N² ≤ 3.9e8 = N^6; amendment **A2** (Lipschitz variant of the band lemma, the step before `|Δu| ≤ √|Δu|`) |
| 9 | `‖m‖ ≤ 1` (inline; band `norm_mSigma`, BA `BAm_norm_le_one`); `‖z_u-z_u'‖ ≤ |Δu|` (`NQGood1Gen_norm_zt_sub`, `NQGood1Gen:451`) | `|m|²` = 0.999 / 0.471 / 0.445 at g=1/64,1,10 (L=3, E=0) | ≤ 1 | `1-|m|²` = 1.5e-3 / 0.53 / 0.56 |
| 10 | T2 depth `(L^d W^{6d})² ≤ W^D`, i.e. `2(d log_W L+6d) ≤ D` | sz0 n=0 (`d=3,L=4,W=32`): 38.40 | D=40 | 1.60 |
| 11 | T2 `1 ≤ J ≤ W^{1/2}`; window `1-t ≥ λ²`, `(1-t)^-1 ≤ N` | J=W^0.1=1.414 ≤ 5.657; 1e-2 ≥ 2.44e-4; 100 ≤ 2097152 | as stated | 4.2 / 41 / 2e4 |
| 12 | T2 exponents: `J²`, `(W^d|1-u|)^-1`, `(·)^{-1/2}J^{3/2}`, `4(log W)^{3/2}`, `J³`, `T²` | equal to `3_5_Loop_Hierarchy.tex:2328-2336` (`res_deccalE_lk/wG/dif`) and to the check text; at u=1/4: 1.09e-4, 1.348, 1.357 | equality | 0; note `(log W)^{3/2}=6.45 > L/2=2`: the indicator is ≡ 1 at n=0 |
| 13 | R1: `A=(κ+1)/κ` (`TwistStep2_lam0_sq`, `TwistStep2:740`), `κ=0.5/0.25/0.04` (supervisor 2026-10-10-2254 G2) | A=3 / 5 / 26 | `g₀² ≤ g² ≤ A g₀²`, `g₀=√t₀ g`, `t₀ ∈ [κ/(κ+1),1)` | `A g₀²/g²` = 2.70 / 4.50 / 23.4 at t₀=0.9; =1 at t₀=κ/(κ+1) (extreme); guard (g): 0 violations in 2e5 draws |
| 14 | pinned `∃` before `(sz,z)` | `𝔠d`, `C₀`, D1 numerals; `c` of D2 is the universal `1` after A1 | none after `(sz,z)` | — |

### (ii) One nondegenerate instance (all numbers from the commands below)
D1: `d=3, L=3` (27 sites), BA-type kernel `X_{ab}=|M_{ba}|²`, `M=(gΨ-E-m)^-1`, `m` from `(self_m)` (`BA/MFixedPoint:192`), `S=1`, `g=1/64,1,10`, `E=0`, `u_0=0`, `k=20`, `Δ=0.04, 0.0475` (`u_k=0.80,0.95`). D2/D3: sz0 n=0 (`d=3,L=4,W=32,λ=1/64`, `N=2097152`; `BA/ConArg:1835`) and `L=3,W=1` (`N=27`); BA reading adds `g₀Ψ`, which cancels. T2: sz0 n=0, `D=40`, `J=W^0.1`, `u=1/4`, `t=0.99`. External hypotheses (D2 `HighProbAt`, D3 `∀ᶠ`): the limit/tail computations are rows 7 and 8; the other gates' pins (rows 1-11 of the family table) stay hypotheses.
```
$ S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2496; python3 $S/d1.py
D1 at BA-type kernel X=M^(+,-) of (self_m), S=1; d=3 L=3 E=0; u0=0, k=20; ratios are LHS/bound (need <=1); Duhamel = max LHS/(64 B^7 (R+Delta M)) over 6 draws
g=0.01562 Im m=0.999 |m|^2=0.999 rows=1.0000..1.0000 K1/K2/K3 res 7e-14/1e-12/1e-12 u_k=0.8000 B=5 P 1.000 X1 0.147 X2 0.889 Th 0.833 ThTh 0.595 Duhamel 2.5e-06
g=0.01562 Im m=0.999 |m|^2=0.999 rows=1.0000..1.0000 K1/K2/K3 res 7e-14/1e-12/1e-12 u_k=0.9500 B=20 P 1.000 X1 0.049 X2 0.675 Th 0.513 ThTh 0.177 Duhamel 1.0e-09
g=1       Im m=0.686 |m|^2=0.471 rows=1.0000..1.0000 K1/K2/K3 res 6e-15/9e-13/9e-13 u_k=0.8000 B=5 P 1.000 X1 0.147 X2 0.889 Th 0.833 ThTh 0.595 Duhamel 7.3e-07
g=1       Im m=0.686 |m|^2=0.471 rows=1.0000..1.0000 K1/K2/K3 res 6e-15/9e-13/9e-13 u_k=0.9500 B=20 P 1.000 X1 0.049 X2 0.675 Th 0.513 ThTh 0.177 Duhamel 3.9e-10
g=10      Im m=0.667 |m|^2=0.445 rows=1.0000..1.0000 K1/K2/K3 res 8e-15/4e-13/4e-13 u_k=0.8000 B=5 P 1.000 X1 0.147 X2 0.889 Th 0.833 ThTh 0.595 Duhamel 7.4e-07
g=10      Im m=0.667 |m|^2=0.445 rows=1.0000..1.0000 K1/K2/K3 res 8e-15/4e-13/4e-13 u_k=0.9500 B=20 P 1.000 X1 0.049 X2 0.675 Th 0.513 ThTh 0.177 Duhamel 4.0e-10
$ python3 $S/inst.py
sizes d=3 L=4 W=32: N=(WL)^d=2097152
  D2 entry sup on contGood: true sqrt2*N = 2.96582e+06 (ratio to N^1 1.4142, c_min 1.0238); Lean cont_norm_Xentry_le 2N = 4194304 (ratio to N^1 2.0, c_min 1.0476); ratio of true sup to 2*N^1 = 0.7071
  P(contGood^c) <= 2N^2*2exp(-N^2/2): log10 = -9.55e+11; N^-10 has log10 = -63.22
  loop modulus k=2, Q=N^2: N k Q^k Q^2 (2N^(c+1)+1): c=1 1.3803e+70 <= band 3kN^(2k+7)=2.0705e+70: True; constant-free c=2 1.4474e+76 <= band: False
sizes d=3 L=3 W=1: N=(WL)^d=27
  D2 entry sup on contGood: true sqrt2*N = 38.1838 (ratio to N^1 1.4142, c_min 1.1052); Lean cont_norm_Xentry_le 2N = 54 (ratio to N^1 2.0, c_min 1.2103); ratio of true sup to 2*N^1 = 0.7071
  P(contGood^c) <= 2N^2*2exp(-N^2/2): log10 = -154.8; N^-10 has log10 = -14.31
  loop modulus k=2, Q=N^2: N k Q^k Q^2 (2N^(c+1)+1): c=1 2.2251e+16 <= band 3kN^(2k+7)=3.3354e+16: True; constant-free c=2 3.0020e+17 <= band: False
T2 hyp: (L^d W^(6d))^2 <= W^D  <=>  38.40 <= D=40 (log_W): slack 1.60; 1 <= J <= W^(1/2)=5.657, J=W^0.1=1.414
  window 1-t=0.01 >= lam^2=0.000244; (1-t)^-1=100 <= N=2097152; (logW)^(3/2)=6.452; zdistInf<=L/2=2
  lk RHS (1-u)^-1 (W^d|1-u|)^-1 J^2 = 1.0851e-04; wG RHS (1-u)^-1[1+(W^d|1-u|)^-1/2 J^1.5] = 1.3476; dif RHS J^3 term = 1.3574
R1 g=0.015625 kappa=0.5 A=(k+1)/k=3: t0=0.9 -> g0^2<=g^2<=A g0^2: True (A g0^2/g^2=2.70); t0=k/(k+1) -> A g0^2/g^2=1.0000
R1 g=1        kappa=0.25 A=(k+1)/k=5: t0=0.9 -> g0^2<=g^2<=A g0^2: True (A g0^2/g^2=4.50); t0=k/(k+1) -> A g0^2/g^2=1.0000
R1 g=10       kappa=0.04 A=(k+1)/k=26: t0=0.9 -> g0^2<=g^2<=A g0^2: True (A g0^2/g^2=23.40); t0=k/(k+1) -> A g0^2/g^2=1.0000
R1 guard (g) brute force violations: 0
D3 (g=10, N=27, t=1-1/N): max rowsum||K_u-K_u'||/|u-u'| = 506.012 <= N^2=729 <= N^6=387420489
```

### Verdicts
T1 (`LemDecCalELip` §1-4 under D2, D3) **PASS as amended** (A1, A2, A4); unamended D2 fails row 4 and then row 6. T2 (`STLemDecCalEConclgL`, `STLemDecCalEgL`, bridge) **PASS**: text = paper 2328-2336 (row 12), instance row 10-12, no generic proof (D4). T3 (D4 untouched) n/a. T4-T5 (`EtermsMid`, R1 never) **PASS** (A3). T6 (D1) **PASS** (rows 1-3). T7-T9 (`DuhamelI`, `stDuhamelIgL_of`, `stDuhamelIIgL_of`; R1 only at `duhamelI_Phi_STprof` `DuhamelI:516` and the profile average `DuhamelII:102-201`) **PASS**. T10 (instances) numbers above. No BA source missing for D1/D2 (`gridRepTailGen_ker_BA`, `Step2EventsGenTw_baGrid`); D3 BA: `baKsol_two` (`KInduct:88`); the check compiles (CONTROL H279 (2): exit 0). **Overall PASS.**
**A1** D2 text `‖Hm n u ω x y - Hm n u' ω x y‖ ≤ 2 * N^c * √|u-u'|`, `c=1` (row 4, 6). **A2** D3 band discharge needs a Lipschitz variant of `LemDecCalELip_STKloop_two_sub` (row 8; ~15 lines, counted). **A3** `EtermsMid` ends at 2,058 (range 1,905-2,159) > 1,800: sibling needed, but the ticket cut (new file = §8-§10) moves `stEtermsMid_of_LWT` (`:1670`) out of `EtermsMid`, whose only importer is `DuhamelI` (U4s3b), so under the split U4s3a would break the frozen name for `MainIndOut`; use the reverse cut: new `EtermsMid2` = §1-§7 (privates by `open private`), `EtermsMid` imports it and keeps §8-§10 and the pin. **A4** the loop-modulus engine is `cont_green_flow_diff` with `X:=(H_u-H_u')/√|Δu|` (op norm `≤ N·2N^c`) and `NQGood1Gen_norm_zt_sub`, not `loopFine_shiftNg_le` (a norm shift at fixed `M`); `norm_loopFine_crudeNg` gives `‖G‖` bounds. **A5** `duhamelIG_duhamel` reuses ~13 model-free privates of `PfStep5Grid` (xi) and needs generic `Uc/Tc` as private `ContinuousLinearMap`s (inside the 220-line D1 item).

### Fill-in table (CONTROL H250 (4))
| item | content |
|---|---|
| (i) | rows 1-14 above |
| (ii) | D2 band and BA (`c=1` with factor 2; P ≤ 10^-154 at N=27), D1 at BA-type kernels `g=1/64,1,10` (g₀<g enters through R1 row 13 and D2), outputs above |
| (iii) | moved to the 1b start (0149 `:98`); ticket rows re-read, two changes: row 8 text (A1), row 9 discharge (A2, `STKloop_two_sub` is Hölder-form) |
| (iv) | D1 default accepted: text = `PfStep5Grid_duhamel_pin` with `|E|≤2, g, E` dropped and `ThetaN/Ugen` → `Step2Gen_ThetaN/UN C`; proof route in row 1; band `pfStep5Grid_duhamel` unchanged |
| (v) | D2 decided with A1; family form `∀ κ ε 𝔡, ∃ c` guarded, `c=1` after A1. BA source exists: `Hm = sz.seqHflowBA l = l•PsiI + seqHflow` (`Step2EventsGenTw:60-73`, `Step2EventsGenTw_baGrid`; first conjunct `rfl`), `G = contGood (sz.withLam 0)` (`cont_highProbAt_good` is generic in `sz`) |
| (vi) | D3 decided: inline text accepted, discharge A2. Probe `T2496Pins.lean` (≤ 400): D1/D2 texts ~60, band discharges at `szB/zB` ~110, generic `Lloop_sub` from D2 (A4) ~90, one D1 instance at `gridRepTailGen_ker_BA` ~100, BA readings ~40; it must also check A2 and the `EtermsMid2` cut (A3) |
| (vii) | family rows 1-11: merged texts at `Step5CasesGen:140`, `IniTermIIGen:68`, `GridRepTailGen:54`, `Step2Gen:882` (`STGridMartgL`), `:651` (`STLWTgL`), `:681` (`STEMn2ExpgL`), `:1118` (`STK2decaygL'`), `Step5Gen:164` (`STNewKLKLgL'`), `Step2EventsGen:966`, `StepDecompGen:60`, `Step34Gen:164`; premise-by-premise check at the 1b start |
| (viii) | public decls (script): `LemDecCalELip` §1-4 18 public / 20 private (8 have readers → band corollaries `Lloop_sub, STKloop_two_norm, LK_sub, env, LK2, ELKLK, EGt, ee`, 7 of them read outside the row, `LK_sub` only by `DuhamelII`; 10 have none) , §5-7 5 / 4 band only; `EtermsMid` §1-7 0 / 48, §8-9 1 / 7; `DuhamelI` §1-6 18 / 22, §7-9 5 / 7 (→ `DuhamelI2`); `DuhamelII` 3 / 12. Reused unchanged (0 band tokens): `EtermsMid` §1-§2, `DuhamelI` §1-§2 (Φ), `DuhamelII` §2 |
| (ix) | as planned: R1 only in `duhamelI_Phi_STprof` (`DuhamelI:516`, copy of private `Step5KerGen_tailT_cross` `:275`) and `DuhamelII:102-201`; statements 1-5 never; guard (g) row 13 |
| (x) | scan preview, no Lean run: new Prop defs assumed by public theorems = D2 (`LemDecCalELipG_FlowMod`) only; D3 inline, D1 concluded inside. `STLemDecCalEgL`/`ConclgL` are assumed by no theorem here. Registry: edit owner text of `Axioms.lean:208-210` (`STEtermsMidgL`, `STDuhamelIgL`, `STDuhamelIIgL`, owedProps); new owedProps lines 0, at most 1 for D2 (if no in-file theorem has it as conclusion head; probe scan decides) plus the approved `STLemDecCalEgL` only if a consumer appears. Premises of changed theorems already registered: `STKboundgL :134`, `STLKgL :135`, `STLmaxUgL :198`, `STLKUgL :199`, `STDecaygL :217`, `STStep2ConclgL :232`, `STStep1LoopgL :239`; not listed (merged, consumed by passing theorems; whether a theorem concludes `STKwardgL`, `STDecayStronggL` is not shown here): those two, `FlowFacts`, `KerFacts`, `GridRepTailGen_Ker`, `STGridMartgL`, `STLWTgL`, `STEMn2ExpgL`, `STBdatagL`, `STK2decaygL'`, `STNewKLKLgL'`, `LoopForm`, `LCompat/KCompat` |
| (xi) | `DuhamelII` ← `DuhamelI` (stay: `drift mart grid tailW_eq rpow_quarter absorb`; → `DuhamelI2`: `whp_sec ELKLK_meas cardK measure_le`); `DuhamelII` ← `EMn2Exp2` `emn2Exp2_exists_CR`; `DuhamelI` ← `PfStep5Grid`: `pfStep5Grid_abs` (`:287`) + `_slot_apply/_add/_sub/_smul/_one`, `_norm_slot`, `_eta`, `_sum2`, `_update2`, `_update2'`, `_alg`, `_inv_le` (`:524-583, 613, 624`); `EtermsMid` ← `EtermsMid2` (A3), `DuhamelI2` ← `DuhamelI` privates read by §7-9 (count at 1b); copy: `Step5KerGen_tailT_cross` |
| (xii) | lines: below; layering/cycles in the `misc.py` output |
| (xiii) | 13 proposed names (`STLemDecCalEConclgL … T2496_DuhamelForm`, `EtermsMid2`, `DuhamelI2`): `git grep -w -F`: output below |

### (xii) Lines (D4 scope, in place): `added = c1·tokens + itemised extras`, `c1 = 2.0` (lo 1.2, hi 3.0); tokens = lines of the scope matching the C1 regex (+ `ThetaN, UN, bandFM, stGridRepN`)
```
$ python3 $S/lines.py     # tokens: Lip 117 (§1-4), EtermsMid 141, DuhamelI 143 (§1-9), DuhamelII 96; extras itemised in the script
lo c1= 1.2 [('Lip', 385), ('EtermsMid', 329), ('DuhamelI', 567), ('DuhamelII', 245)] total 1526
central c1= 2.0 [('Lip', 479), ('EtermsMid', 442), ('DuhamelI', 681), ('DuhamelII', 322)] total 1924
hi c1= 3.0 [('Lip', 596), ('EtermsMid', 583), ('DuhamelI', 824), ('DuhamelII', 418)] total 2421
U4s3a (Lip+EtermsMid) 921  U4s3b (DuhamelI+I2+II) 1003
final sizes (old + (c1-1)*tok + extras): {'Lip': 1727, 'EtermsMid': 2058, 'DuhamelI': 2532, 'DuhamelII': 1202}
central 1924 x1.57 (T2484 landing/1a) 3021 x1.38 (T2491 hi col) 2655 calibration line D4 3540
hi 2421 x1.57 3801
ticket D4 central 1770; this/ticket = 1.087
$ python3 $S/misc.py; bash $S/clash.sh | grep "total hits"
imports: 13 added Chain imports, cycles 0 ; reach a BA module transitively: ['NewKLKLGen', 'NewKLKGen'] ; direct BA imports in the 4 files: 0 ; reverse cone besides the five: 77
importers: EtermsMid <- ['RBM3D.Induction.DuhamelI'] ; DuhamelI <- ['RBM3D.Induction.DuhamelII'] ; DuhamelII <- ['MainIndOut']
main: total hits 0
t/T2491: total hits 0
t/T2493: total hits 0
t/T2494: total hits 0
t/T2495: total hits 0
t/T2496: total hits 0
```
Central **1,924** (`LemDecCalELip` 479, `EtermsMid`+`EtermsMid2` 442, `DuhamelI`+`DuhamelI2` 681, `DuhamelII` 322), lo 1,526, hi 2,421; 26 under the 1,950 line, so **one row** by the rule (knife-edge: at the hi value the pre-signed split applies; split rows would be 921 / 1,003). Against the ticket's 1,770: ×1.09 (D1 proof 220 and the `EtermsMid2` header are the new items). Final sizes: `LemDecCalELip` 1,727; `EtermsMid2` ~1,480 + `EtermsMid` ~580; `DuhamelI` ~1,690 + `DuhamelI2` ~840; `DuhamelII` 1,202: all < 1,800. Calibration: landing = added − verbatim-moved ≈ 1,924 (moved ≈ 675 `DuhamelI2` + ≈ 1,300 `EtermsMid2`); at the T2484 factor 1.57 → 3,021 < 3,540; hi 2,421 × 1.57 = 3,801 > 3,540 (only the hi case crosses). Reverse cone 77 modules (ticket 74 at 9df6a9e7).

## (a″) Probe compile — Tue Oct 13 08:41:05 UTC 2026
Probe `RBM3D/Probe/T2496Pins.lean` (375 lines), branch `t/T2496`, commit `4e5e3b82`, base `6ccc6be2` (includes the merged T2493 `BA/Step5IIIWalk`); not imported by `RBM3D.lean`. Section (a) is not edited. `$S` = scratchpad `T2496/`.
```
$ cd ../RBM3D-wt/T2496 && date -u && lake env lean RBM3D/Probe/T2496Pins.lean > $S/final_run.out 2>&1; echo "exit $?"
Tue Oct 13 08:39:00 UTC 2026
exit 0
$ cat $S/final_run.out
new premises found by the scan: []; with T2496_flowMod_band, T2496_flowMod_BA withheld: [RBM.BA.T2496_FlowMod]
RBM.BA.T2496_flowMod_band: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_flowMod_BA: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_sub: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_ev: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_ev_ba_sz0: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_ev_band_szB: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_STKloop_two_lip: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_duhamelForm_band: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_duhamelForm_of_ker: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_duhamel_ba_sz0: [propext, Classical.choice, Quot.sound]
$ wc -l RBM3D/Probe/T2496Pins.lean; grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2496Pins.lean | wc -l; grep -c Probe RBM3D.lean; git grep -n "T2496_" -- RBM3D RBM3D.lean ':!RBM3D/Probe/T2496Pins.lean' | wc -l
375 RBM3D/Probe/T2496Pins.lean
0
0
0
$ python3 $S/textdiff.py     # probe text of D1, D2, D3 against docs/tickets/checks/T2496-check.lean
D1 text identical to the check (:236-245): True
D2 text identical to the check (:251-256): False ; identical after inserting `2 *` before `((sz.size n : ℕ) : ℝ) ^ c` (A1): True
D3 text identical to the check example (:271-274): True
$ bash $S/d1port.sh          # the merged proof of D1 (T2493)
section Duhamel starts at 304; baStep5III_duhamel (BA wrapper, not ported) at 677; 'end Duhamel' at 693
ported block = lines 304-671 of RBM3D/BA/Step5IIIWalk.lean: 368 lines; non-blank, non-comment: 324
20
last commit of the file: f2af0245
$ python3 $S/a3.py           # cut A3
EtermsMid.lean lines 51-1358 (sections 1-7): 48 private, 0 public declarations; read by lines 1359-1757 (sections 8-10): 12 private
etermsMid_Bctl_window etermsMid_q_le etermsMid_A_big etermsMid_lam etermsMid_J etermsMid_A_prec etermsMid_zeta_ratio etermsMid_EEk_sub etermsMid_L2 etermsMid_S1W etermsMid_eta_pos etermsMid_sections
```
**What the probe compiles** (ticket Probe line; probe line numbers):
| item | declaration | result |
|---|---|---|
| D2 text with A1 (`2 *`) | `T2496_FlowMod` :48 | check :251-256 plus `2 *` (textdiff) |
| D2 band at `szB/zB` | `T2496_flowMod_band` :67 (every `sz`), example :74 at `(szB, zB)` | compiled |
| D1 text | `T2496_DuhamelForm` :162 | check :236-245 verbatim (textdiff) |
| D1 band at `szB/zB` | `T2496_duhamelForm_band` :174 (`pfStep5Grid_duhamel` through `Step2Kern_ThetaN_band`, `_UN_band`), example :337 | compiled |
| generic `Lloop_sub` from D2 | `T2496_Lloop_sub` :80 (explicit `Hm`), packaged `T2496_Lloop_ev` :252 (premise `T2496_FlowMod`; event `G`; bound `3k N^(2k+6) N^c sqrt|Δu|`); band `LemDecCalELip_Lloop_sub` (type of `LemDecCalELip:277`) recovered at :148 | compiled |
| target 1 instances | BA flow `(sz0, zSeq)`, `t ≡ 1/2` :313; band `(szB, zB)`, `t ≡ 15/16` :340; all deterministic hypotheses discharged | compiled |
| D1 at a BA kernel | `T2496_duhamelForm_of_ker` :278; `T2496_duhamel_ba_sz0` :282 (K1-K3 from `gridRepTailGen_ker_BA`, `BAflow_real`, `flow_sz0`); instance with data :288 (`d=3, n=0, L=4, W=32, k=3, Δ=1/48`, `Rem, Mart ≠ 0`) | compiled |
| D2 at BA | `T2496_flowMod_BA` :237 (`Hm = seqHflowBA`, `G = contGood (sz.withLam 0)`); family forms :269 (band), :273 (BA), `∃ c` before `(sz, z)`, guarded | compiled |
| D3 and A2 | `T2496_D3` :181; `T2496_STKloop_two_lip` :186; band `STKloop_two_sub` recovered :215; D3 at `(szB, zB)` :226; BA reading :301 | compiled; BA typechecked |
| BA readings | heads of targets 5, 8, 9 and D3 at the BA family :301 | typechecked |
| cut A3 | `open private` of the 12 names :33, used :44 | compiled |
| premise scan | :360 | `[]`; `[T2496_FlowMod]` with the two discharges withheld |

**Findings.**
* **F1 (D1 is already proved, and larger than (a) assumed).** `Step5IIIWalk_duhamel` (`BA/Step5IIIWalk.lean:578`, merged) has the conclusion of D1 for every `C` with `GridRepTailGen_Ker C n` (`T2496_duhamelForm_of_ker`, a term applying it). `BA/*` cannot be imported by the converted files, so the 1b copies the block `Step5IIIWalk.lean:304-671`: 368 lines (324 without blank and comment lines) plus the 12-line def, against 220 in (a) (xii). Effect: (a) central 1,924 becomes 2,040-2,084 (above the 1,950 split line: U4s3a 921, U4s3b 1,119-1,163); at the T2484 factor 1.57: 3,203-3,272 (below 3,540); hi 2,537-2,581 x 1.57 = 3,983-4,052 (above). The 1a-audit decides the split.
* **F2 (D2 form).** The packaged `∃ Hm G` cannot give the band corollaries their `hgood` form (`ω ∈ G n` is opaque), so the converted `Lloop_sub` must be the deterministic core with explicit `Hm`, `hLM`, `hherm`, `hmod` (:80); `T2496_FlowMod` enters only the packaged form (:252), which targets 5, 8, 9 use. The band corollary takes `Hm := seqHflow`, `c = 1` (:148).
* **F3 (A1, A4 confirmed in Lean).** `T2496_seqHflow_entry_sub` :55: entry modulus `2 N^1 sqrt|Δu|` from `cont_norm_Xentry_le`; engine `cont_green_flow_diff` at `X = (H_u - H_u')/sqrt|Δu|`, `‖X‖ ≤ N·2N^c`; exponent `N^(2k+6) N^c`, equal to the band `N^(2k+7)` at `c = 1`. Neither `norm_loopFine_crudeNg` nor `loopFine_shiftNg_le` is used.
* **F4 (registry).** The scan finds `T2496_FlowMod` as an unproved premise of `T2496_Lloop_ev` only when the band and BA discharge theorems are withheld: a public band discharge theorem concluding the class replaces the `owedProps` line for D2 that (a) (x) allowed.
* **F5 (A2).** `T2496_STKloop_two_lip` (N² |Δu|, 28 lines as a copy; in place the edit of `LemDecCalELip_STKloop_two_sub` is about 10 lines); the Hölder band statement follows (:215); D3 at `(szB, zB)` uses `szB_size_ge`.
* **F6 (A3).** In `EtermsMid.lean:51-1358` 12 of 48 private declarations are read by §8-§10 (0 public); the `open private` of these 12 compiles.
* **Not probed.** The other §1-§4 corollaries (`_env`, `_LK2`, `_ELKLK`, `_EGt`, `_ee`, `_LK_sub`, `_ee_sub`); the BA discharge of D3 (typechecked only: owner U3-BA, `baKsol_two`); the window `(η_t)⁻¹ ≤ N²` stays a hypothesis of both forms and is discharged at the two instances (`Im m ≥ 1/2`).

**Fill-in table (CONTROL H250 (4)); all rows filled.**
| item | content |
|---|---|
| (i) | (a) rows 1-14; Lean confirmation of rows 4, 6, 8 (F3, F5); (a)'s D1 size 220 replaced by 380 raw / 336 without comments (F1) |
| (ii) | D2 at band `(szB, zB)` :74 and BA :237/:273; D1 at the BA kernel of `(sz0, zSeq)` :282/:288 (`lam 0 = 1/64` by `sz0_values`); `g = 1, 10` stay numeric, in (a) |
| (iii) | at the 1b start (0149 `:98`) as in (a); the D2 field is `Hm` (core) or `T2496_FlowMod` (packaged), F2 |
| (iv) | D1 decided: text verbatim from the check; proof the merged `Step5IIIWalk_duhamel`, copied (F1) |
| (v) | D2 decided with A1; band and BA discharges compiled (:67, :237), family forms :269, :273 |
| (vi) | D3 decided: inline text verbatim from the check, band discharge by A2; probe lines in the table above |
| (vii) | as in (a); row 8 now has compiled band and BA discharges; row 9: D3 compiled at the band, `‖m‖ ≤ 1` at band and BA (inside :313, :340); check at the 1b start |
| (viii) | as in (a); new public name for A2: `T2496_STKloop_two_lip` (to be `LemDecCalELip_STKloop_two_lip`); two G1 corollaries probed (`Lloop_sub` :148, `STKloop_two_sub` :215) |
| (ix) | as in (a); the probe has no R1 text |
| (x) | scan run (:360): F4; registry text of `Axioms.lean:208-210` unchanged from (a); `STLemDecCalEgL` as in the ticket |
| (xi) | `EtermsMid` 12 names (F6); `LemDecCalELip` 7 names opened by the probe (:35); `Step5IIIWalk` opens 13 `pfStep5Grid_*` names (`Step5IIIWalk.lean:56-58`), the D1 copy opens the same |
| (xii) | F1: central 2,040-2,084, split U4s3a 921 / U4s3b 1,119-1,163, calibration 3,203-3,272 against 3,540 |
| (xiii) | `T2496_*` probe names: 0 tracked hits outside the probe (command above); the 13 proposed names of (a): 0 hits on `main` and the sibling branches |

## (a′) Preflight corrections at the 1b start — Tue Oct 13 09:05:31 UTC 2026
**Verdict: BLOCKED at the 1b-start name-level check (row U4s3a, targets 1-5; the 1a-audit fixed the split). No Lean written, no build run, nothing committed by the 1b: `t/T2496` is still at the probe commit 4e5e3b82.** Table (iii) of the ticket (0149 `:98`) shows four facts that the converted proofs of targets 1, 4, 5 read and that the premise list fixed at the 1a-audit (§4: family rows 1-11, D2 = check text with `2 *`, D3 inline, `‖m‖ ≤ 1` inline) does not carry. Each needs a new premise or a changed row, i.e. a new hypothesis (stage rule 4); the dispatcher amends (precedent: Amend 1 of T2418 and T2440, CONTROL merge log). Section (a) and (a″) are unchanged and still hold for D1, the loop modulus of D2 and the `EtermsMid2` cut.
| # | band fact read (file:line, `git diff --stat 6ccc6be2 main -- LemDecCalELip EtermsMid DuhamelI DuhamelII LemDecCalEPrec Test/Axioms` is empty at main 035c4b84) | home in rows 1-11 | band discharge | BA source | status |
|---|---|---|---|---|---|
| 1 | `abs E < 2`, `zt E`, `etaT E`, `Lloop = STLM (seqHflow)` (LemDecCalELip §1; EtermsMid:661-663, 1236) | LoopForm (10), FlowFacts (1), D2 (8) | `stepDecompGen_loopForm_band` (StepDecompGen:459), `step5CasesGen_flowFacts_band` (Step5CasesGen:156), probe `:67` | `Step2EventsGenTw_baGrid` (:73), probe `:237` | OK |
| 2 | `norm_mE` (LemDecCalELip:332, 563) | inline `‖m n‖ ≤ 1` (9) | `norm_mE` | `BAm_norm_le_one` | OK |
| 3 | weak law → matrix level: `‖STGMM sz n (E n) u (seqHflow n u ω) x y‖ ≤ δ₀` (EtermsMid:642-654, 680) | **none**: D2 (check :251-256, probe :48-53) reads `Cm.LM`, `Cm.L` only; F9 clause 1 (`Step2EventsGen:82`) is not in D2 | `rfl` (P4) | `Step2EventsGenTw:73-80` clause 1 `rfl` (P4) | **G1** |
| 4 | `Σ_y ‖SB x y‖ = 1`, `sum_norm_SB_row` (LemDecCalELip:457, 682; EtermsMid:993): bilinear/`ee`/`EEk` moduli | **none**: `FlowFM.S` is free (Carrier:65) | `sum_norm_SB_row` (P4) | `S = 1` (FlowPins:327; P4) | **G2** |
| 5 | `‖STKloop‖ ≤ N` (LemDecCalELip:328) → `LK_norm` :505 → `ELKLK_sub` :530; target 1 only (EtermsMid reads only `_Lloop_sub` :979, `_EGt` :1598, `_env` :1637) | **none**: D3 is the modulus (check :271-274) | :328 | `baKsol_two` (closed form, 1a-audit O3; the size is not derived) | **G3** |
| 6 | `stK2decay_holds`, `stNewKLKL_holds` at `STflowE z n` (EtermsMid:513, 1702-1703) | row 7: `STK2decaygL'`, `STNewKLKLgL' d mkE` read `(mk sz (fun _ => E))` (Step2Gen:1118-1121, Step5Gen:151-165), glue `mkM sz z = mkE sz (E sz z)` | band: fields at index `n` agree (`rfl`, P4 `Scr_Local`) but the glue does not give it (P3) | **BA: `stK2decaygL'_ba` is at `baStep2Fam sz E = baStep2Mat sz sz.lam E` (Step2BA:157); the BA carrier has `BAflowLam0 sz z n = √t₀ · sz.lam n` (FlowPins:386) and `mkE` has no `z`; the merged BA route is carrier-level (`baStep2_K2`, `baStep2_newKLK`; Step2IterBA:27-28, 489, 698-705, "finding F1")** | **G4** |
| 7 | `ST_Bdata_holds`, `stEMn2Exp_holds`, `STLWT`, `ST_LW_sections`, `STLocalEntryU`, `STGdecayW` | rows 1, 5, 6 (`STBdatagL` Step2EventsGen:966, `emn2ExpFacts` EMn2Exp1:811, `emn2ExpHK` EMn2Exp2:934, `STLWTgL` Step2Gen:651, `STEMn2ExpgL` :681), `STStep2ConclgL` (:514); `Step2EventsGen_Flow` (:68) from row 1 | merged | merged | OK |
*Note, Tue Oct 13 10:53:41 UTC 2026: superseded for the rerun.  Amend 1 (A6-A9) approved the four additions; G1 is closed by the clause `GMM` of D2 (A6), G2 by the premise `hSr` (A7), G3 by `lemDecCalELipG_Kn` (A8 (a); no inline premise (b)), G4 by the class `EtermsMid_NewKLKL` (A9).  The table is kept as the record of the 1b-start check; section (b) below replaces the BLOCKED verdict.*

## (b) Script output (1b rerun, row U4s3a = targets 1-5; U4s3b = targets 6-10 not started)
Branch `t/T2496` at e96c59dd (main bde392e4 merged by 6c9d3ccc).  **A9 class and band discharge, compiled first** (`scratchpad/T2496/1b2/a9.lean`, mtime 09:30:05 UTC, the first Lean of this round; text now `Induction/EtermsMid2.lean:46-62`):
```
def EtermsMid_NewKLKLAtN {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (Ck δ₀ : ℝ) : Prop :=
  ∀ (u D : ℝ), 0 ≤ u → u < 1 → 0 ≤ D →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg Cm n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLKMg Cm n u H σ a‖ ≤
          Ck / (1 - u) * (STJhatMg Cm n D ((sz.L n : ℕ) : ℝ) u H ^ 2 * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
            STJhatMg Cm n D ((sz.L n : ℕ) : ℝ) u H * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D))

def EtermsMid_NewKLKL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Ck δ₀ : ℝ, 0 < Ck ∧ 0 < δ₀ ∧
    ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, EtermsMid_NewKLKLAtN (mk sz z) n Ck δ₀
theorem etermsMid_newKLKL_band (d : ℕ) :
    EtermsMid_NewKLKL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z)) := by ...
```
```
$ lake build RBM3D.Induction.LemDecCalELip RBM3D.Induction.EtermsMid2 RBM3D.Induction.EtermsMid  ->  Build completed successfully (3910 jobs).
$ lake build        # at e96c59dd, finished Tue Oct 13 10:50:42 UTC 2026, wall 6:13.33
info: RBM3D.lean:597:0: axiom audit: 14871 theorems, 4601 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4366 jobs).
$ wc -l RBM3D/Induction/{LemDecCalELip,EtermsMid2,EtermsMid}.lean      # main: 1365 / - / 1757; stop size 2,000
 1778 LemDecCalELip.lean   1587 EtermsMid2.lean   498 EtermsMid.lean
$ git diff --numstat main...t/T2496 -- <the three files> RBM3D/Test/Axioms.lean
643 230 LemDecCalELip | 182 1441 EtermsMid | 1587 0 EtermsMid2 | 1 1 Test/Axioms
moved verbatim (non-blank lines removed from EtermsMid, present in EtermsMid2; script): 1002
UP-C2 (d) landing = added 2,413 - moved 1,002 = 1,411 (blank lines of the moved sections not subtracted); 1a-audit forecast for U4s3a 921 (x1.53); calibration line 3,540 (D4).
$ git diff --stat main...t/T2496: LemDecCalELip, EtermsMid, EtermsMid2, Test/Axioms (1 line), Probe/T2496Pins (375, branch only);  --name-only -- RBM3D/Chain RBM3D/BA RBM3D/Path <band readers> | wc -l -> 0
$ rep/newnames.py + collectAxioms:  30 new public declarations (LemDecCalELip 21, EtermsMid 2, EtermsMid2 7); axioms outside {propext, Classical.choice, Quot.sound}: []
   stEtermsMidgL_of | stEtermsMid_of_LWT | STLemDecCalE_iff_gL | LemDecCalELip_ee_sub | EtermsMid_NewKLKL: [propext, Classical.choice, Quot.sound]
```
**Target statements.**  Target 5 (extracted from `EtermsMid.lean`, long lines cut at 118; head = `T2496_EtermsMidHead`; no `hd` parameter, the conclusion carries its own `3 ≤ d →`):
```
theorem _root_.RBM.BA.stEtermsMidgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (s…
    (ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ)
    (hF : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hLW : STLWTgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hEMe : emn2ExpFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0 Hf ζf)
    (hHK : emn2ExpHK d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hBd : STBdatagL d Flow T0)
    (hK2 : Step2IterGen_K2 d Flow mkM) (hNew : EtermsMid_NewKLKL d Flow mkM)
    (hFM : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c)
    (hmn : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSr : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b, ‖(mkM sz z).S n a b‖ ≤ 1)
    (hLF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z)) :
    STEtermsMidgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
```
```
$ python3 rep/diffs.py      # against docs/tickets/checks/T2496-check.lean
$ diff <check: T2496_LemDecCalEConclgL vs STLemDecCalEConclgL>  ->  IDENTICAL
$ diff <check: T2496_LemDecCalEgL vs STLemDecCalEgL>  ->  IDENTICAL
$ bridge STLemDecCalE_iff_gL, right side of ↔ vs T2496_BandLemDecCalE -> IDENTICAL
$ diff <check: T2496_FlowMod with `2 *` (A1) vs LemDecCalELipG_FlowMod (A6 adds the clause `GMM`)>  ->  1 differing lines
  +    (∀ (n : ℕ) (u : ℝ) ω x y, Cm.GMM n u (Hm n u ω) x y = Cm.GM n u ω x y) ∧
$ forgetful lemma conclusion == 1a-audit D2 text (with `2 *`): True
$ lake env lean rep/auditcheck.lean -> exit 0   (auditor-style: `T2496_BandLemDecCalE := STLemDecCalE_iff_gL`; `T2496_LemDecCalEgL`, `_EConclgL` by `Iff.rfl`; `T2496_FlowMod Cm μ c := lemDecCalELipG_flowMod_base h`; `T2496_EtermsMidHead … := stEtermsMidgL_of d law Flow mkM T0 E Hf ζf h1 … h11`)
$ lake env lean rep/ba_chk.lean -> exit 0   (BA readings: D2 incl. clause GMM at baStep2Mat; A7 `S = 1`; EtermsMid_NewKLKL at BAFlow typechecks; A8 (a) at BAFlow from merged baStep2_K2, baSTBdatagL_holds)
```
**Instances** (`grep -n "^example"` heads): target 1: `EtermsMid2.lean:1540, 1548, 1557, 1565` (`LK2gL`, `ELKLKgL`, `EGtgL`, `eegL` at `bandStep2Mat sz0 (fun _ => 1/2)`, `Hm = seqHflow`, `G = contGood`, `c = 1`, `s ≡ 0`, `t ≡ 1/16`, nothing left open) and `:1576` (A8 (a): `lemDecCalELipG_Kn` at `(sz0, z0)`, κ = ε = 𝔡 = 1/10, 𝔠 = 1/6, from `step2IterGen_K2_band`, `bandFM_STBdata`); target 2: `LemDecCalELip.lean:1702` (`STLemDecCalEgL 3` band tuple as hypothesis, no generic proof, gives `InstIng5Concl` of `inst_lemDecCalE`); target 5: `EtermsMid.lean:493` (`STLWTgL 3` band tuple as hypothesis, L5's pin; gives `InstIng5Concl` at `(szB, zB, 7/8, 15/16)` for every `C_d > 0`), band `stEtermsMid_of_LWT` examples `:463, :468` unchanged.
```
$ rep/clash.sh        refs scanned: main + 512 t/* branches other than t/T2496;  total hits over refs: 0;  working tree (outside the three files): 0 hits
$ rep/c1scan.py       24 generic statements scanned: 2 regex hits, both in the band D3 discharge LemDecCalELip_STKloop_two_lip (`STKloop`, `|E|`); labelled band: STLemDecCalE_iff_gL (binding text),
                      lemDecCalELipG_flowMod_band, _mod_band, _seqHflow_entry_sub, etermsMid_band_gL, etermsMid_newKLKL_band
$ grep -nE "∀ \(sz : Sizes d\)" <3 files>: 15 hits = carrier-tuple binders (EtermsMid:357-360, LemDecCalELip:1648-1650, EtermsMid2:1247-1248), hFM/hmn/hSr/hLF (EtermsMid:367-371, each `0 < κ → Flow … →`), class (EtermsMid2:56-57, `Flow` inside)
$ X1-C4 regex (new definitions of the pinned names): 0;  `STGridRepNgL`: 0 0 0;  sorry|admit|axiom|native_decide: 0;  direct `import RBM3D.BA`: none;  closure of the three files: no NQEndFlowGen, no downstream band file;  `import RBM3D.Induction.EtermsMid2`: EtermsMid.lean:9 only
$ rep/part3.lean (pp.all types of the 62 names of Part 3 of the check, branch vs main): cmp -> identical (151,530 bytes each);  privates of main's LemDecCalELip/EtermsMid: 80, none missing;  public: 25, none missing
$ rep/scan.lean (premise scan, partial environment): LemDecCalELipG_FlowMod, _Mod, EtermsMid_NewKLKL are concluded by public band discharges; STLemDecCalEgL occurs only in an iff and an example; band STLemDecCalE is listed only because its prover LemDecCalEPrec is not in that environment: no owedProps line (the full build's #assert_rbm_axioms passes)
```
**Tables.**  (iii)+(vii) Hypotheses of `stEtermsMidgL_of` as used (band discharge in the repo / BA source / closes):
| premise | guard | band discharge | BA source (owner) | closes |
|---|---|---|---|---|
| `hF` FlowFacts (row 1) | built in | `step5CasesGen_flowFacts_band` | `EMn2BA_T0_lt_one`, `EMn2BA_mF_data` (U2-BA) | |
| `hLW` `STLWTgL` (5) | pin | `bandFM_STLWT` (from `STLWT`) | `stLWTgL_of_LWtermExpG` + L5's `LWtermExp` (T2494) | |
| `hEMe`, `hHK`, `hBd` (6) | as merged | `emn2Exp_bandFacts`, `emn2Exp2_bandHK`, `bandFM_STBdata` | `baEMn2ExpFacts`, `baEMn2ExpHK`, `baSTBdatagL_holds` | |
| `hK2` `Step2IterGen_K2`, `hNew` `EtermsMid_NewKLKL` (7, A9) | `∃ (Ck δ₀)` per `(κ, 𝔡)` before the sizes, `∀ᶠ n` | `step2IterGen_K2_band`, `etermsMid_newKLKL_band` | `baStep2_K2`; U4-BA at mixed coupling (pattern `baStep2_newKLK`, R1 inside) | G4 |
| `hFM` D2 (8, A6) | `∃ c` before `(sz, 𝔠, z)`, `Flow →` | `lemDecCalELipG_flowMod_band` (`c = 1`) | `ba_D2` (ba_chk: `seqHflowBA`, `contGood (sz.withLam 0)`, clause `GMM` by `rfl`) | G1 |
| `hmn` `‖m‖ ≤ 1`, `hSr` row sums (9, A7); `hLF` LoopForm (10) | `0 < κ → Flow →` | `norm_mE`, `sum_norm_SB_row`; `stepDecompGen_loopForm_band` | `BAm_norm_le_one`, `S = 1` (ba_chk); `baStep2Mat_loopForm` (U2-BA) | G2 |
| K size `‖𝒦^{(2)}‖ ≤ N` (A8) | not a premise of 5/8/9 | `lemDecCalELipG_Kn` (a) from `hK2` at `s := 0` and `hBd` | the same, `baStep2_K2` + `baSTBdatagL_holds` (ba_chk) | G3 |
| D3 `𝒦^{(2)}` modulus `N^6\|Δu\|` | hypothesis `hKs` of `LK2gL`, `ELKLKgL` only | `LemDecCalELip_STKloop_two_lip` | `baKsol_two` / U3-BA twin (typechecked only, 1a-audit O3) | U4s3b |
Not premises of target 5: rows 2-4 (`IniTermGen_KerFacts`, `GridRepTailGen_Ker`, `STGridMartgL`: targets 8, 9), `STK2decaygL'`, `STNewKLKLgL'`, the glue (A9).  UBA-C1: no `withLam`, `lam0` or comparison in a statement of 1-5 (C1 scan); R1 only inside the BA discharge of A9.
(viii) scope: in place: `LemDecCalELip` sections 3-4 (carrier-level; band statements are corollaries) and the pins of section 8; `EtermsMid` sections 3, 4, 6, 7, 8 and the target; reused by name: sections 1, 2, 5 (not `zeta_ratio`); band only: `Lloop_*`/`STLI_*` proofs, `LemDecCalELip` sections 5-7, `LemDecCalEPrec`.  (xi) `open private`: the 12 names of cut A3 (`EtermsMid2` into `EtermsMid`); `lemDecCalELipG_absorb`, `lemDecCalELip_inst_tN` (from `LemDecCalELip`).

**Narrative.**
* Layout.  `EtermsMid2` (new, reserve) holds sections 1-7 of the old `EtermsMid` (cut A3: reverse cut, `EtermsMid` keeps sections 8-10 and the pin; every frozen name stays in a file on the `MainIndOut` import path) and, beyond A3, the four packaged forms of target 1 (`LemDecCalELip_*gL`, with their instances).  Target 2: the pins and the bridge are the binding texts (diff above), no generic proof (D4).  Reason: with them `LemDecCalELip` was 1,929 lines (above the 1,800 rule; the audit predicted 1,727); the move (commit 8df9d102) took it to 1,770 and `EtermsMid2` from 1,391 to 1,573.  This placement is not in the 1a-audit; the auditor may rule.  Sizes: 1,778 / 1,587 / 498, all below 1,800.
* Target 1.  Generic proofs are the band proofs edited in place (`lemDecCalELip_bilin`, `avg_sub`, `avg_norm` are generalised, not deleted); the band `LK_sub`, `LK_norm`, `ELKLK_sub`, `EGt_sub`, `ee_sub` are corollaries of the carrier results and `STKloop_two_sub` of `_two_lip`, types unchanged (Part 3 identical).  `STLI_*`, `Lloop_*` keep their band proofs.  Exponents: carrier results carry `N^c` (`N^{10} N^c`, ...), the band `c = 1` gives the old exponents.
* Target 5.  `stEtermsMidgL_of` re-proves the band pin on the carrier; `stEtermsMid_of_LWT` is its corollary through `STEtermsMid_iff_gL`.  `ST_LW_sectionsg` needs `Step2EventsGen_Flow` unguarded; it is built from row 1 on the flow `0 < κ ∧ Flow` (no new premise).  The weak law enters through the clause `GMM` of D2 (A6), Hermiticity and the pathwise bound only on the event `G` of D2: `etermsMid_prec_twoG` adds a third failure event.
* A8: (a) closes (`lemDecCalELipG_Kn`); (b) is not used.  A9: no `STK2decaygL'`/`STNewKLKLgL'` premise. 
* Calibration: 1,411 landed against 921 forecast; U4s3b has 3,540 - 1,411 = 2,129 left before the new-file rule.
* Limits: D2, A7, A8 compile at BA (ba_chk, scratch); the BA proof of A9 is U4-BA's.  `RBM3D.lean` is not edited (the hub adds `import RBM3D.Induction.EtermsMid2`).  The probe on the branch no longer compiles (its `open private` names moved); never merged.

## (c) Verified Mathlib names
Used and compiling: `Finset.sum_le_sum`, `norm_sum_le`, `measure_union_le`, `measure_mono`, `ENNReal.ofReal_add`, `ENNReal.ofReal_le_ofReal`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.one_le_rpow`, `Real.sqrt_le_one`, `Real.mul_self_sqrt`, `abs_norm_sub_norm_le`, `Complex.abs_im_le_norm`, `inv_anti₀`, `one_le_inv₀`, `Matrix.one_apply`, `apply_ite`.  Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
* T2496a: D2 constant `2` (A1, 1a-audit): entries of `H_u - H_{u'}` are `≤ 2 N √|Δu|` (`cont_norm_Xentry_le`); clause `GMM` added (A6).  Lean-only.
* T2496b: carrier moduli carry the exponent `N^c` (`3k N^{2k+6} N^c`, `7 N^{10+c}`, `42 N^{16+c}`, `36 N^{19+c}`); the band `c = 1` recovers the old constants.  Lean-only.
* T2496c: D3 at the band is the Lipschitz form `N^2 |Δu|` (`LemDecCalELip_STKloop_two_lip`), the Hölder band lemma follows from it.  A8 (a): `‖𝒦^{(2)}‖ ≤ C_K (1 + c_B⁻¹)` from `STprof ≤ (1 + c_B⁻¹) W^{-d} B_{u,0}` (`ST_prof_le_Bctl`), not from `‖Θ‖ ≤ (1-t)⁻¹`.  T2496d: `EtermsMid_NewKLKL` is `lem:newKLK` at `ℓ = L`, sharp form, at a carrier (A9); the energy window of `STNewKLKLAt` becomes the eventual quantifier, as in `STNewKLKLgL'` (T2134a).
* Open: (1) the placement of the packaged forms in `EtermsMid2`; (2) the stale probe; (3) U4s3b: targets 6-10 on `t/T2496b` (`DuhamelI`, `DuhamelI2`, `DuhamelII`).
