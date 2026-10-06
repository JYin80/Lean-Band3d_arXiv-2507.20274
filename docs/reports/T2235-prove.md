Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 00:51:15 UTC 2026

Notation (ticket; files read: `Step6Pins.lean:40-70,285-440`, `Step6Kit.lean:55-135,375-530,595-640,735-820`, `Step34Pins.lean:605-630`, `Defs/Sizes.lean:157-215`, `Defs/Params.lean:36`, paper `6:90-96`, `3_5:1618-1624`). `x_u = 1-u`, `N = (WL)^d`, `B_u = Bctl n u = W^{-d}(λ²+x_u)⁻¹ + (N x_u)⁻¹` (`st6_Bctl_eq`; `Bparam` at `K=0` has `(0+1)^{d-2} = 1`), `G = (λ²W^d)^{-1/5}`, `T_u = B_u²(G+B_u)` (`STExpTarget`). Kernel: `‖𝒰_{v,u}A‖_∞ ≤ ((1-v)/(1-u))^n ‖A‖_∞` (`sum_res_Ndecay`, `3_5:1620`), used at `n=2`.

### (i) Exponent table

| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | kernel power `n_` | 2 | `STEKSumNdecay` needs `2 ≤ n_`; factor `((1-v)/(1-u))²` | equality (none needed) |
| 2 | drift exponents (iii) | `11/5` (`STExpLKLKHiConcl`), `5/2` (`STExpEGtHiConcl`), prefactor `x_v⁻¹` | after `B_v ≤ 2x_uB_u/x_v`: integrand `≤ x_u^{-2}(2x_uB_u)^r x_v^{1-r}`, `r∈{11/5,5/2}`; need `r-1>0` so row 3 applies | `r-1 = 6/5, 3/2 > 1`; grid max pointwise ratio `0.99999778` (≤ 1) |
| 3 | `u`-integral exponents (iii) | `x_v^{-6/5}` and `x_v^{-3/2}`: `r'=6/5, 3/2 > 1` | `∫_s^u x_v^{-r'}dv = ((x_u^{1-r'} - x_s^{1-r'})/(r'-1)) ≤ x_u^{1-r'}/(r'-1)`: constants `5`, `2` | `r'-1 = 1/5, 1/2 > 0` |
| 4 | powers of `x_u` (iii) | `x_u^{-2}·x_u^{11/5}·x_u^{-1/5}` and `x_u^{-2}·x_u^{5/2}·x_u^{-1/2}` | total exponent must be `0` (no stray `x_u`) | exactly `-2+11/5-1/5 = 0`, `-2+5/2-1/2 = 0` |
| 5 | integrand ratio `x_vB_v ≤ 2x_uB_u` | factor 2 | `st6_xB_III` at `(v,u)`, needs `λ² ≤ x_u` (`STReg5III`: `λ² ≤ 1-t ≤ 1-u`) | uses `W^{-d}x/(λ²+x) ≤ W^{-d}` and `≥ W^{-d}/2` |
| 6 | `B_u ≤ 2(λ²W^d)⁻¹` (iii) | factor 2 | `x_u ≥ λ² > 0`, `N ≥ W^d` (`L ≥ 1`): `B ≤ W^{-d}λ^{-2} + (Nλ²)⁻¹ ≤ 2(λ²W^d)⁻¹` | needs `λ ≠ 0` (at `λ=0`: `0^{-1/5}=0` in Mathlib); eventual by `WO` |
| 7 | `B^{1/5} ≤ 2^{1/5}G` | `2^{1/5} ≈ 1.1487 ≤ 3/2` | from row 6 | 0.35 |
| 8 | `B^{1/2} ≤ B^{1/5}+B` | — | `B ≤ 1`: `B^{1/2} ≤ B^{1/5}`; `B > 1`: `B^{1/2} ≤ B` | none needed |
| 9 | constant of rates (iii) | `5(2B)^{11/5}+2(2B)^{5/2} ≤ B²(G·39.39 + B·11.31)` | `≤ 64 B²(G+B) = 64 T_u`: `5·2^{12/5}+2·2^{5/2}·2^{1/5} = 39.386 ≤ 64`, `2·2^{5/2} = 11.314 ≤ 64` | `24.6` on the `G` coefficient, `52.7` on the `B` coefficient; grid max ratio `22.58` (so slack factor 2.8) |
| 10 | regime (iv) integral | `(x_v/x_u)² x_v⁻¹(Nx_v)^{-3} = N^{-3}x_u^{-2}x_v^{-2}`, `∫_s^u x_v^{-2} = x_u⁻¹ - x_s⁻¹ ≤ x_u⁻¹` | total `≤ M (N x_u)^{-3}` | tight (grid ratio `1-1e-9`, non-strict as stated) |
| 11 | `(N x_u)^{-3} ≤ B_u³ ≤ T_u` | constant 1 | `B_u ≥ (N x_u)⁻¹` (first term of `B` is `> 0`), `st6_cube_le_target` | grid max ratio `1-1.7e-8` (≤ 1, non-strict) |
| 12 | absorption of `64` | kernel at `τ/2`, `M = N^{τ/2}`; need `64 ≤ N^{τ/2}` | eventual in `n` since `N_n → ∞` (`SizeTendsto` in `Admissible`) | for `sz0`: `τ=0.1`: `n ≥ 45`; `τ=0.5`: `n ≥ 1` (script below) |
| 13 | time constraints | `0 ≤ s ≤ v ≤ u ≤ t ≤ lemT z < 1` | `STEKSumNdecay`: `0 ≤ s`, `s ≤ u`, `u < 1`; `st5_t_lt_one` | `x_u ≥ 1 - lemT > 0` |
| 14 | regime (iv) hypothesis | `1-s ≤ λ²/L^d` | **not used** by the integrated step: carried by the premise `STExpDriftLoConcl` | — |
| 15 | dimension | `d ≥ 3` only through `3 ≤ d` in `STEKSumNdecay`; `N=(WL)^d`, `N ≥ W^d`; `K=0` kills `(K+1)^{d-2}` | all constants (`5, 2, 2, 64, 1`) are `d`-independent; script rerun at `d=4`: maxima `22.35` (≤64), `0.768`, `1-1e-9`, `1-5.2e-8` (≤1) | — |

Row 2/3 link: `(x_v/x_u)²·x_v⁻¹·B_v^r ≤ x_u^{-2}(2x_uB_u)^r x_v^{2-1-r}`, `x_v^{1-r} = x_v^{-6/5}` (`r=11/5`) and `x_v^{-3/2}` (`r=5/2`), so the integrals of row 3 have `r' = r-1`: `11/5-1 = 6/5`, `5/2-1 = 3/2`.

Mathematical checks of the route (each against the files):
- Lift (§64 (4)): per time sequence `u_n ∈ [s_n,t_n]` the kernel step is a deterministic eventual bound uniform in `v ∈ [s_n,u_n]`, `σ` (finite), `a` (`pi_norm_le_iff_of_nonneg`, right side `N^τ X_v ≥ 0` since `B_v > 0`, `x_v > 0`); the integral bound has deterministic left side (`D_v` is an expectation, the integrand `‖𝒰_{v,u}D_v(a)‖` is a number) and right side `T_u`; so the lift over `u` is of a deterministic family (`st6_prec_det_iff` + `st6_precU_of_forall_seq`). The kernel bound is not lifted. Norm of the integral: `‖∫F‖ ≤ ∫g` from `‖F‖ ≤ g` with `g` continuous on `[s,u]` (`x_v ≥ x_u > 0`), no integrability of `F` needed. Drift premise on `TimeIcc s u ⊆ TimeIcc s t`; the sum `‖D‖ ≤ ‖𝔼ℰ^{LK×LK}‖+‖𝔼ℰ^{G̃}‖ ≤ N^τ x⁻¹(B^{11/5}+B^{5/2})`.
- Assembly: `STExpDuhEq` at `A=∅` (`zeroModeSet … ∅ = id`, `st5_zeroModeSet_empty`), triangle inequality, initial term `≤ N^τ F`, drift integral `≤ N^τ T_u`, so `‖f_u(a)‖ ≤ N^τ(F+T_u)`; deterministic both sides.
- Kernel hypotheses at `t ↦ u`: `0 ≤ s`, `s ≤ u`, `u < 1`, `‖mE E‖ = 1` (`norm_mE`, `|E| < 2` from `st6_flowE_lt_two`), `X ≥ 0`, any `σ`, `Admissible` from `hflow.1` (`STFlow := Admissible ∧ locDomain`, `Defs.lean:286`); `Ugen … = UN … (EKsgn …)` is the identity already used at `st6_ini_sumNdecay` (`Step6Kit.lean:629-633`).
- Consumers (§45 O2): `STExpIntIII d = STIngR6 d STReg5III (fun … => STExpDuhEq → STExpDriftHiConcl → STExpIntConcl sz ∅ STSigAll …)` (`Step6Pins.lean:425-427`) is `hInt` of `ST_step6_caseIII_of_pins` (`Step6Kit.lean:737`, applied at `:741`, `:752-753`); `STExpIntIV` (`:432-434`) is `hInt` of `ST_step6_caseIV_of_pins` (`:786`; `:790`, `:800-801`); `inst_expIntIII/IV` (`:634-641`) and `inst_step6IV` (`:572`) take `STExpIntIII 3`, `STExpIntIV 3`, `STStep6IV 3`. The binder lists match: premises `STExpDuhEq`, then `STExpDriftHiConcl` (a pair `⟨hlk, hegt⟩`) / `STExpDriftLoConcl`, conclusion `STExpIntConcl sz ∅ STSigAll E s t`, whose `F`-premise is the initial term `Ugen … (s n) (p.1) f_s` produced by `st6_ini_sumNdecay`. Pin text uses no mollifier.
- Paper: `6:94-96` (integrate over `u` with `sum_res_Ndecay`, `n=2`) and `3_5:1620-1624` (`‖𝒰A‖_∞ ≤ ((1-s)/(1-t))^n ‖A‖_∞`) agree with rows 1-4, 10; the paper's "`B_{u,0} ≍ |1-u|^{-1}`" is used only one-sidedly (row 5), as the ticket proposes.

### (ii) One concrete nondegenerate instance (d = 3)

Regime (iii): `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`, `Sizes.lean:260-265`), `s=0`, `t=1/16`, `u=1/16`, `n ∈ {0,10,100}`: `λ>0`, `λ² ≤ 1-t = 15/16` (`sz0_reg5III`), `s<t ≤ lemT(z0)` (`sz0_hst`, `sz0_ht`). Regime (iv): `szG` (`L=4`, `W=n+4`, `λ=5`), `s=5/8`, `t=u=3/4`: `1-s = 3/8 ≤ λ²/L^d = 25/64` (`szG_reg4`), `3/4 ≤ 31/32 ≤ lemT(zB n)` (`lemT_zB`, `szB_flow_ht`). Hypotheses that stay open (other gates' pins, allowed): `STExpDriftHiConcl`, `STExpDriftLoConcl`, `STExpDuhEq` (instance `inst_duhEq_holds`, merged), stochastic premises of `STIngR6`. No external (non-merged) analytic input enters: the kernel estimate is the merged `stek_sumNdecay_holds`. Limit computation for the one eventual constant `N^{τ/2} ≥ 64`: `sz0`, `τ=0.1`: first `n` is `45` (`N=1.78e36`); `τ=0.5`: `n=1` (`N=5.5e11`). The script also evaluates grid maxima: rates (iii) on `λ ∈ [1e-4,5]` (25 pts, kept only if `λ² ≤ x_u`), `W ∈ [1,1e3]` (25), `L ∈ {3,4,10,100}`, `x_u ∈ [1e-9,1]` (40); integrals on coarser grids (listed in `pre.py`: (iii) `λ` 9 pts, `W ∈ {1,10,100,1000}`, `L ∈ {3,10,100}`, `x_u` 10 pts; (iv) `L ∈ {3,4,10,100}`, `λ ∈ {1e-3,1,5}`, `x_u` 12 pts), `x_s ∈ {x_u(1+1e-4), 2x_u, 10x_u, 1e3x_u, 1}` (capped at 1).

Command: `cd <scratchpad>/T2235 && python3 pre.py 3`  (`pre.py`: numpy/scipy `quad`, in log-variable for (iii), closed form for (iv); 74 lines, scratchpad only). Output verbatim:
```
const checks: 5*2^(12/5)+2*2^(5/2)*2^(1/5) = 39.38619655715765  ; 2*2^(5/2) = 11.313708498984761  (need <=64 each, ticket: <=40, <=12)
(iii) rates: max [5(2B)^(11/5)+2(2B)^(5/2)]/T_u = 22.576409656349075 (need <=64)
(iii) integral: max int_s^u (x_v/x_u)^2 x_v^-1 (B_v^{11/5}+B_v^{5/2}) dv / [5(2B_u)^{11/5}+2(2B_u)^{5/2}] = 0.7422020607452474 (need <=1)
(iii) pointwise: max ratio of integrand to (x_u^-2 (2x_uB_u)^r x_v^(1-r)) = 0.9999977780057908 (need <=1)
(iv) integral/(N x_u)^-3 max = 0.9999999990000003 (need <=1); (N x_u)^-3/T_u max = 0.99999998257675 (need <=1)
sz0 n=0 W=32 L=4 lam=0.015625 N=2.097e+06 u=0.0625 s=0 x_u=0.9375 B=3.3052e-05 T=7.2078e-10 lam^2<=x_u:True
   iii: 64T=4.6130e-08  lhs=3.2588e-09 ok=True ; int_0^{1/16}(1-v)^-6/5=0.06496<=5(1-u)^-1/5=5.06496 ; int(1-v)^-3/2=0.06559<=2(1-u)^-1/2=2.06559
   lam!=0: True lam^2<=1-u: True
sz0 n=0 (iv-rate only) W=32 L=4 lam=0.015625 N=2.097e+06 u=0.0625 s=0 x_u=0.9375 B=3.3052e-05 T=7.2078e-10 lam^2<=x_u:True
   iv: (N x_u)^-3=1.3158e-19 <= B^3=3.6108e-14 <= T=7.2078e-10 : True
sz0 n=10 W=5.15363e+06 L=44 lam=8.81991e-09 N=1.166e+25 u=0.0625 s=0 x_u=0.9375 B=7.7928e-21 T=9.5046e-42 lam^2<=x_u:True
   iii: 64T=6.0829e-40  lhs=1.3273e-43 ok=True ; int_0^{1/16}(1-v)^-6/5=0.06496<=5(1-u)^-1/5=5.06496 ; int(1-v)^-3/2=0.06559<=2(1-u)^-1/2=2.06559
   lam!=0: True lam^2<=1-u: True
sz0 n=10 (iv-rate only) W=5.15363e+06 L=44 lam=8.81991e-09 N=1.166e+25 u=0.0625 s=0 x_u=0.9375 B=7.7928e-21 T=9.5046e-42 lam^2<=x_u:True
   iv: (N x_u)^-3=7.6558e-76 <= B^3=4.7324e-61 <= T=9.5046e-42 : True
sz0 n=100 W=3.36323e+11 L=404 lam=1.47195e-14 N=2.509e+42 u=0.0625 s=0 x_u=0.9375 B=2.8039e-35 T=3.2532e-71 lam^2<=x_u:True
   iii: 64T=2.0820e-69  lhs=2.2197e-75 ok=True ; int_0^{1/16}(1-v)^-6/5=0.06496<=5(1-u)^-1/5=5.06496 ; int(1-v)^-3/2=0.06559<=2(1-u)^-1/2=2.06559
   lam!=0: True lam^2<=1-u: True
sz0 n=100 (iv-rate only) W=3.36323e+11 L=404 lam=1.47195e-14 N=2.509e+42 u=0.0625 s=0 x_u=0.9375 B=2.8039e-35 T=3.2532e-71 lam^2<=x_u:True
   iv: (N x_u)^-3=7.6885e-128 <= B^3=2.2043e-104 <= T=3.2532e-71 : True
szG n=0 W=4 L=4 lam=5 N=4096: reg5IV 1-s=0.3750<=lam^2/L^d=0.39062:True ; (N x_u)^-3=9.3132e-10 <= T=5.8603e-07:True ; int=3.1044e-10<=(N x_u)^-3:True ; u=3/4<=lemT>=31/32:True
szG n=10 W=14 L=4 lam=5 N=175616: reg5IV 1-s=0.3750<=lam^2/L^d=0.39062:True ; (N x_u)^-3=1.1816e-14 <= T=1.4935e-10:True ; int=3.9388e-15<=(N x_u)^-3:True ; u=3/4<=lemT>=31/32:True
szG n=100 W=104 L=4 lam=5 N=71991296: reg5IV 1-s=0.3750<=lam^2/L^d=0.39062:True ; (N x_u)^-3=1.7153e-22 <= T=2.6673e-16:True ; int=5.7177e-23<=(N x_u)^-3:True ; u=3/4<=lemT>=31/32:True
```
Command: `python3 pre.py 4` (d=4), lines 2-5 of its output:
```
(iii) rates: max [5(2B)^(11/5)+2(2B)^(5/2)]/T_u = 22.34824718228857 (need <=64)
(iii) integral: max int_s^u (x_v/x_u)^2 x_v^-1 (B_v^{11/5}+B_v^{5/2}) dv / [5(2B_u)^{11/5}+2(2B_u)^{5/2}] = 0.7683629174287063 (need <=1)
(iii) pointwise: max ratio of integrand to (x_u^-2 (2x_uB_u)^r x_v^(1-r)) = 0.999999956000002 (need <=1)
(iv) integral/(N x_u)^-3 max = 0.9999999990000001 (need <=1); (N x_u)^-3/T_u max = 0.9999999477302522 (need <=1)
```
Threshold computation (inline python, `N_n = ((2(n+1))^5 · 4(n+1))^3`): `sz0: tau=0.1: least n with N_n^(tau/2) >= 64 is n=45 (N=1.783e+36)`; `sz0: tau=0.5: least n with N_n^(tau/2) >= 64 is n=1 (N=5.498e+11)`.

All maxima are `≤ 1` (resp. `≤ 64`) and every instance row is `True`; no `N=0`, no empty window (`s<u`: `0<1/16`, `5/8<3/4`; the `u`-integrals are over `[0,1/16]`, `[5/8,3/4]` of positive length), `N` between `4096` and `2.5e42`.

### Verdicts
- Targets 1 (`expIntEasy_integral_rpow`), 2a, 2b (rates), 3a, 3b (one size), 4 (`expIntEasy_kernel_seq`), 5a, 5b (lifts), 6 (`STExpIntConcl_of_int`), 7a, 7b (flow forms, pins `STExpIntIII`, `STExpIntIV`), 8 (`STStep6IV`), 9 (instances): **PASS** (all exponents close, rows 1-15; constants `5, 2, 64, 1` hold with the slacks above; one lift over `u` of a deterministic family; no hypothesis the pins lack: `λ ≠ 0` is eventual from `WO` in `STFlow`, used in (iii) only).
- Observation (not a failure): the (iv) integral bound and the (iv) rate are tight to `1-1e-9` / `1-1.7e-8` (non-strict, as the ticket states); no strict inequality may be asked of them.
- Overall: PASS.

## (b) Script output (stage 1b)

Commit `1a9c99f` on `t/T2235` (base `3a58663`, `main` now `f6650b2`).

### Module build (`cd RBM3D-wt/T2235 && lake build RBM3D.Induction.ExpIntEasy`, final run, replayed from the build cache; the same file content was compiled in the run of `Tue Oct  6 01:02:27 UTC 2026`)
```
691:ℹ [3859/3859] Replayed RBM3D.Induction.ExpIntEasy
715:Build completed successfully (3859 jobs).
716:exit 0
717:Tue Oct  6 01:05:27 UTC 2026
```
### `#print axioms` of every public declaration of the file (build output, `ExpIntEasy.lean:742-764`; file ends with the 23 `#print axioms` lines)
```
742 Sizes.expIntEasy_integral_rpow [propext, Classical.choice, Quot.sound]
743 Sizes.expIntIII_rates_le_target [propext, Classical.choice, Quot.sound]
744 Sizes.expIntIV_rate_le_target [propext, Classical.choice, Quot.sound]
745 Sizes.expIntIII_drift_integral_le [propext, Classical.choice, Quot.sound]
746 Sizes.expIntIV_drift_integral_le [propext, Classical.choice, Quot.sound]
747 Sizes.expIntEasy_kernel_seq [propext, Classical.choice, Quot.sound]
748 Sizes.expIntIII_int_unif [propext, Classical.choice, Quot.sound]
749 Sizes.expIntIV_int_unif [propext, Classical.choice, Quot.sound]
750 Sizes.STExpIntConcl_of_int [propext, Classical.choice, Quot.sound]
751 Sizes.STExpIntIIIConcl_of_flow [propext, Classical.choice, Quot.sound]
752 Sizes.STExpIntIVConcl_of_flow [propext, Classical.choice, Quot.sound]
753 Sizes.stExpIntIII_holds [propext, Classical.choice, Quot.sound]
754 Sizes.stExpIntIV_holds [propext, Classical.choice, Quot.sound]
755 Sizes.stStep6IV_holds [propext, Classical.choice, Quot.sound]
756 Step6Inst.inst_expIntIII_holds [propext, Classical.choice, Quot.sound]
757 Step6Inst.inst_expIntIV_holds [propext, Classical.choice, Quot.sound]
758 Step6Inst.inst_skeleton6III_Int [propext, Classical.choice, Quot.sound]
759 Step6Inst.inst_skeleton6IV_Int [propext, Classical.choice, Quot.sound]
760 Step6Inst.inst_expIntIII_concl [propext, Classical.choice, Quot.sound]
761 Step6Inst.inst_expIntIV_concl [propext, Classical.choice, Quot.sound]
762 Step6Inst.inst_expIntEasy_integral_rpow [propext, Classical.choice, Quot.sound]
763 Step6Inst.inst_expIntIII_rates_le_target [propext, Classical.choice, Quot.sound]
764 Step6Inst.inst_expIntIV_rate_le_target [propext, Classical.choice, Quot.sound]
```
### Target statements (script `extract.py`: the text of each public `theorem` header from `ExpIntEasy.lean`)
```
L48: theorem expIntEasy_integral_rpow {s u r : ℝ} (hsu : s ≤ u) (hu : u < 1) (hr : 1 < r) : ∫ v in s..u, (1 - v) ^ (-r) ≤ (r - 1)⁻¹ * (1 - u) ^ (1 - r)
L104: theorem expIntIII_rates_le_target {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) (hl : sz.lam n ≠ 0) (hg : sz.lam n ^ 2 ≤ 1 - u) : 5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ) ≤ 64 * STExpTarget sz n u
L185: theorem expIntIV_rate_le_target {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) : ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3 ≤ STExpTarget sz n u
L259: theorem expIntIII_drift_integral_le {d : ℕ} (sz : Sizes d) (n : ℕ) {s u M : ℝ} (F : ℝ → ℂ) (hM : 0 ≤ M) (hsu : s ≤ u) (hu : u < 1) (hg : sz.lam n ^ 2 ≤ 1 - u) (hF : ∀ v : ℝ, s ≤ v → v ≤ u → ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))) : ‖∫ v in s..u, F v‖ ≤ M * (5 * (2 * sz.Bctl n u) ^ (11 / 5 : ℝ) + 2 * (2 * sz.Bctl n u) ^ (5 / 2 : ℝ))
L305: theorem expIntIV_drift_integral_le {d : ℕ} (sz : Sizes d) (n : ℕ) {s u M : ℝ} (F : ℝ → ℂ) (hM : 0 ≤ M) (hsu : s ≤ u) (hu : u < 1) (hF : ∀ v : ℝ, s ≤ v → v ≤ u → ‖F v‖ ≤ M * (((1 - v) / (1 - u)) ^ 2 * ((1 - v)⁻¹ * ((((sz.size n : ℕ) : ℝ) * (1 - v))⁻¹) ^ 3))) : ‖∫ v in s..u, F v‖ ≤ M * ((((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) ^ 3
L355: theorem expIntEasy_kernel_seq {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s u : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsu : ∀ n, s n ≤ u n) (hu1 : ∀ n, u n < 1) (X : ℕ → ℝ → ℝ) (hX : ∀ n v, s n ≤ v → v ≤ u n → 0 ≤ X n v) (h : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool, ‖(fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n v) (τ : ℝ) (hτ : 0 < τ) : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ u n → ∀ σ : Fin 2 → Bool, ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u n) (fun b => STExpDrift sz n (STflowE z n) v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - v) / (1 - u n)) ^ 2 * X n v)
L504: theorem expIntIII_int_unif {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5III sz s t) (hDr : STExpDriftHiConcl sz (STflowE z) s t) : Prec sz (U := STIdx2 sz s t) (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 v (p.1 : ℝ) (fun b => STExpDrift sz n (STflowE z n) v p.2.1 b) p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ))
L531: theorem expIntIV_int_unif {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hDr : STExpDriftLoConcl sz (STflowE z) s t) : Prec sz (U := STIdx2 sz s t) (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1 v (p.1 : ℝ) (fun b => STExpDrift sz n (STflowE z n) v p.2.1 b) p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ))
L556: theorem STExpIntConcl_of_int {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (_ht1 : ∀ n, t n < 1) (hduh : STExpDuhEq sz E s t) (hint : Prec sz (U := STIdx2 sz s t) (fun n p _ => ‖∫ v in (s n)..(p.1 : ℝ), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1 v (p.1 : ℝ) (fun b => STExpDrift sz n (E n) v p.2.1 b) p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ))) : STExpIntConcl sz ∅ STSigAll E s t
L593: theorem STExpIntIIIConcl_of_flow {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5III sz s t) (hduh : STExpDuhEq sz (STflowE z) s t) (hDr : STExpDriftHiConcl sz (STflowE z) s t) : STExpIntConcl sz ∅ STSigAll (STflowE z) s t
L601: theorem STExpIntIVConcl_of_flow {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hduh : STExpDuhEq sz (STflowE z) s t) (hDr : STExpDriftLoConcl sz (STflowE z) s t) : STExpIntConcl sz ∅ STSigAll (STflowE z) s t
L610: theorem stExpIntIII_holds (d : ℕ) : STExpIntIII d
L618: theorem stExpIntIV_holds (d : ℕ) : STExpIntIV d
L626: theorem stStep6IV_holds (d : ℕ) : STStep6IV d
```
### Compiled nonempty instances (same file, namespace `RBM.Gauss.Step6Inst`, `ExpIntEasy.lean:633-740`; statements by the same script)
```
L639: theorem inst_expIntIII_holds : InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t) sz0 z0 sInst tInst
L645: theorem inst_expIntIV_holds : InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
L651: theorem inst_skeleton6III_Int : LWtermEXP 3 → InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst
L656: theorem inst_skeleton6IV_Int : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
L662: theorem inst_expIntIII_concl : STExpDriftHiConcl sz0 (STflowE z0) sInst tInst → STExpIntConcl sz0 ∅ STSigAll (STflowE z0) sInst tInst
L669: theorem inst_expIntIV_concl : STExpDriftLoConcl szG (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4) → STExpIntConcl szG ∅ STSigAll (STflowE zB) (fun _ => 5 / 8) (fun _ => 3 / 4)
L678: theorem inst_expIntEasy_integral_rpow : ∫ v in (0 : ℝ)..(1 / 16), (1 - v) ^ (-(6 / 5 : ℝ)) ≤ (6 / 5 - 1 : ℝ)⁻¹ * (1 - 1 / 16 : ℝ) ^ (1 - 6 / 5 : ℝ)
L684: theorem inst_expIntIII_rates_le_target : 5 * (2 * sz0.Bctl 0 (1 / 16)) ^ (11 / 5 : ℝ) + 2 * (2 * sz0.Bctl 0 (1 / 16)) ^ (5 / 2 : ℝ) ≤ 64 * STExpTarget sz0 0 (1 / 16)
L691: theorem inst_expIntIV_rate_le_target : ((((szG.size 0 : ℕ) : ℝ) * (1 - 3 / 4))⁻¹) ^ 3 ≤ STExpTarget szG 0 (3 / 4)
```
Further `example`s in the same file (applications at concrete data; `grep -n '^example' ExpIntEasy.lean`): 697,712,724,728,732,737 (lines): target 3a at `sz0`, `n = 0`, `[0,1/16]`, `M = 1`, `F` = the real drift bound itself (nonzero), `(1/64)^2 <= 15/16`; target 3b at `szG`, `n = 0`, `[5/8,3/4]`; target 4 at `(sz0, z0, 0, 1/16)` (the eventual drift bound stays a hypothesis); targets 5a, 5b at the data of 7a (the drift premise stays a hypothesis); target 6 at `(sz0, z0, 0, 1/16)` with `inst_duhEq_holds`.
Hypotheses that stay open in the instances (other gates' pins, CLAUDE.md §4 step 2): `STExpDriftHiConcl` (`inst_expIntIII_concl`), `STExpDriftLoConcl` (`inst_expIntIV_concl`), the stochastic premises inside `InstIng6Concl`, `LWtermEXP 3` (`inst_skeleton6III_Int`); every deterministic hypothesis is discharged (`3 <= 3`, `0 < 1/10`, `flow_z0`, `flow_zG`, `sz0_hs0`, `sz0_hst`, `sz0_ht`, `sz0_reg5III`, `szB_flow_ht`, `1/16 < 1`, `sz0.lam 0 = 1/64 /= 0`, `(1/64)^2 <= 15/16`).

### Hygiene (`grep -cE 'sorry|admit|native_decide|^axiom ' RBM3D/Induction/ExpIntEasy.lean`)
```
hits: 0
```
### Name-clash grep (new public names, non-Probe, `RBM3D/` and `RBM3D.lean`, files other than `ExpIntEasy.lean`)
```
$ grep -rnE "expIntEasy_|expIntIII_|expIntIV_|STExpIntConcl_of_int|STExpIntIIIConcl_of_flow|STExpIntIVConcl_of_flow|stExpIntIII_holds|stExpIntIV_holds|stStep6IV_holds|inst_skeleton6III_Int|inst_skeleton6IV_Int|inst_expIntIII_holds|inst_expIntIV_holds|inst_expIntIII_concl|inst_expIntIV_concl|inst_expIntEasy_integral_rpow|inst_expIntIII_rates_le_target|inst_expIntIV_rate_le_target" RBM3D RBM3D.lean | grep -v "^RBM3D/Induction/ExpIntEasy.lean" | wc -l
hits: 0
```
### Check-file equality (`python3 mkcheck.py` builds the scratch file: check-file imports + `import RBM3D.Induction.ExpIntEasy`, sections 1-2, 14 `example : RBM.Gauss.Sizes.T2235Check.X := @RBM.Gauss.Sizes.X`, section 3 as 9 `example : <statement> := @RBM.Gauss.Step6Inst.<name>`, and `example (d : ℕ) : STExpIntIII d := stExpIntIII_holds d`, same for `STExpIntIV`, `STStep6IV`)
```
$ lake env lean check_eq.lean   (26 `example`s, `grep -c '^example'` = 26)
exit code: 0; lines containing `error`: 0
```
### Registry pre-check (§20 (2)): temporary uncommitted file `import RBM3D` / `import RBM3D.Induction.ExpIntEasy` / `#assert_rbm_axioms`, run `Tue Oct  6 01:04:04 UTC 2026` to `01:04:42 UTC 2026`, root `RBM3D.lean` carrying a temporary uncommitted `import RBM3D.Induction.ExpIntEasy` (removed afterwards: `git checkout RBM3D.lean`)
```
$ lake env lean precheck.lean   -> exit 0
axiom audit: 6877 theorems, 2332 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 130 (borrowed 1, owed 92, structural 31, refuted 6).
registry: 2 borrowed + 142 owed + 88 structural + 7 refuted; 109 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
occurrences of STExpIntIII, STExpIntIV, STStep6IV in the output (owed ledger and 'carry nothing yet' list): 0
owed names in owedProps: base 3a58663 = 145 ; branch = 142
```
### Full `lake build` with the temporary root import (started `Tue Oct  6 01:03:01 UTC 2026` per the task output; end time in the last line)
```
Build completed successfully (4039 jobs).
exit 0
Tue Oct  6 01:03:46 UTC 2026
```
### Scope (`git diff --stat main...t/T2235`; pins unchanged; `Axioms.lean` diff)
```
 RBM3D/Induction/ExpIntEasy.lean | 764 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   3 -
 2 files changed, 764 insertions(+), 3 deletions(-)
git diff main -- RBM3D/Induction/Step6Pins.lean | wc -l  -> 0
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STStep6IV, -- `6:94-96` regime (iv) pin: S6-02; S6-07, S6-08; S6-01 (T2204, DECISIONS §67: owed)
-   `RBM.Gauss.Sizes.STExpIntIII, -- `6:94-96` integrated estimate, regime (iii): S6-08; S6-01 (T2204, DECISIONS §67: owed)
-   `RBM.Gauss.Sizes.STExpIntIV, -- `6:94-96` integrated estimate, regime (iv): S6-08; S6-01 (T2204, DECISIONS §67: owed)
```
Ports from RBM1D/RBM2D: none (no Lean text copied; RBM2D `MLExpVocab_core` was a pattern only), so no `git diff --stat` against a sister commit.

### Narrative
1. All targets 1-9 of the ticket are delivered in `RBM3D/Induction/ExpIntEasy.lean` (764 lines, below the 1500 split line) and committed with the three registry deletions in `RBM3D/Test/Axioms.lean`; no `sorry`/`admit`/`native_decide`/declared `axiom` (grep of the file); all 23 printed axiom lists are `[propext, Classical.choice, Quot.sound]`.
2. No pin text, frozen signature or hypothesis was changed or added: the 14 public theorem statements equal the check-file `def`s (compiled equality above), `Step6Pins.lean` is untouched (`wc -l` of its diff is 0).
3. Route as in the ticket. Target 1: `v ↦ 1-v` (`integral_comp_sub_left`), `integral_rpow`, drop the `(1-s)^{1-r}` term. Target 3a/3b: pointwise bound by a continuous `g` on `[s,u]`, `norm_integral_le_of_norm_le` (no integrability of `F`), `integral_add`, `integral_const_mul`, target 1 at `r-1`; the powers of `1-u` cancel exactly (`expIntEasy_term_integral`). Target 4: `stek_sumNdecay_holds d hd 2 le_rfl` per `σ` on `𝒜 n v _ = D_v^σ`, `st6_prec_det_iff` both ways, `Filter.eventually_all` over `σ`.
4. Constants chosen in the proof of target 2a (not in the ticket text): `2^{1/5} ≤ 6/5` (via `((6/5)^5 > 2)`), `2^{1/2} ≤ 3/2`; `5(2B)^{11/5} ≤ 29 B²G`, `2(2B)^{5/2} ≤ 12 B²(6/5 G + B)`, total `≤ 64 T_u` by `nlinarith`; `B ≤ 2(λ²W^d)⁻¹` is the private `expIntIII_Bctl_le` (uses `N ≥ W^d` from `L ≥ 1`).
5. Targets 5a/5b share one private core `expIntEasy_lift_core` (rate constant `c`: `64` in (iii), `1` in (iv)): per time sequence `u` the kernel bound at `τ/2` (target 4), the one-size integral estimate with `M = N^{τ/2}`, `R_u ≤ c T_u`, `c ≤ N^{τ/2}` eventually (`eventually_le_rpow`), then the single lift `st6_precU_of_forall_seq` (both sides deterministic, §64 (4)). The drift bridges `expIntEasy_drift_pi_hi/lo` use the same `τ` (no halving), the triangle inequality `D = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` and `pi_norm_le_iff_of_nonneg`.
6. `λ_n ≠ 0` is used only in regime (iii) and only eventually (`st6_lam_pos sz hflow.1.2.2.2.2`); regime (iv) uses neither a regime hypothesis nor `λ`.
7. `STExpIntConcl_of_int` carries the pinned hypothesis `∀ n, t n < 1`, which its proof does not use (binder `_ht1`); kept so that the statement equals the check file's. `STExpIntConcl_of_int` uses the same `τ` for the initial term and the drift integral.
8. `stExpIntIII_holds`, `stExpIntIV_holds` take `𝔠_d = 1/100` and ignore the eight stochastic premises of `STIngR6`, `ε` and `𝔡`; `stStep6IV_holds` is the one-line merged skeleton `ST_step6_caseIV_of_pins` with `stImproveExpAver_holds`, `stExpDuhamelZ_holds`, `stExpDriftLo_holds`, `stExpIntIV_holds`; `inst_skeleton6IV_Int` has no open pin. `STStep6III` stays owed: it still needs `LWtermEXP` (`inst_skeleton6III_Int` takes `LWtermEXP 3`).
9. `main` moved from the branch base `3a58663` to `f6650b2` (T2233 merge, one deletion in the same `Axioms.lean` region): not rebased here; merge note below.

## (c) Verified Mathlib names used (module of each, by `env.getModuleIdxFor?`, script `modnames.lean`; the file compiles with them)
```
intervalIntegral.integral_comp_sub_left : Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
intervalIntegral.norm_integral_le_of_norm_le : Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
intervalIntegral.integral_add : Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
intervalIntegral.integral_const_mul : Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
integral_rpow : Mathlib.Analysis.SpecialFunctions.Integrals.Basic
ContinuousOn.intervalIntegrable : Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
ContinuousOn.rpow_const : Mathlib.Analysis.SpecialFunctions.Pow.Continuity
Real.rpow_le_rpow : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.mul_rpow : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_add : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_neg : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_sub : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_two : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_natCast : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.inv_rpow : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_le_rpow_of_exponent_ge : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_le_rpow_of_exponent_le : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_pos_of_pos : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_nonneg : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_one : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_zero : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_neg_one : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.sqrt_eq_rpow : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.sqrt_le_left : Mathlib.Analysis.Real.Sqrt
pi_norm_le_iff_of_nonneg : Mathlib.Analysis.Normed.Group.Constructions
norm_le_pi_norm : Mathlib.Analysis.Normed.Group.Constructions
Filter.eventually_all : Mathlib.Order.Filter.Finite
inv_anti₀ : Mathlib.Algebra.Order.GroupWithZero.Basic
pow_lt_pow_left₀ : Mathlib.Algebra.Order.GroupWithZero.Basic
pow_le_pow_left₀ : Mathlib.Algebra.Order.GroupWithZero.Basic
one_le_pow₀ : Mathlib.Algebra.Order.GroupWithZero.Basic
Complex.norm_real : Mathlib.Analysis.Complex.Norm
Real.norm_eq_abs : Mathlib.Analysis.Normed.Group.Real
norm_add_le : Mathlib.Analysis.Normed.Group.Basic
div_neg : Mathlib.Algebra.Ring.Basic
div_eq_inv_mul : Mathlib.Algebra.Group.Basic
Set.uIcc_of_le : Mathlib.Order.Interval.Set.UnorderedInterval
```
Listed by the ticket and not used: `intervalIntegral.integral_mono_on`, `Real.div_rpow`, `intervalIntegral.intervalIntegrable_rpow` (present, modules `...IntervalIntegral.Basic`, `...Pow.Real`, `...Integrability.Basic`). Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- T2235a (`6:94-96`, regime (iii), "integrating over `u`"): made explicit as `(1-v)B_v ≤ 2(1-u)B_u` (needs `1-u ≥ ilambda²`), `∫_s^u x_v^{-6/5}, x_v^{-3/2}`, powers of `1-u` cancel, `5(2B)^{11/5} + 2(2B)^{5/2} ≤ 64 T_u` from `B ≤ 2(ilambda²W^d)⁻¹`; the paper's `B_{u,0} ≍ |1-u|^{-1}` is used only one-sidedly.
- T2235b (`6:94-96`, regime (iv)): the integrated bound needs no regime (`∫ x_v^{-2} ≤ x_u⁻¹`, `(N x_u)^{-3} ≤ B_u³ ≤ T_u`, constant `1`); the regime enters only through `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` (the premise `STExpDriftLoConcl`).
- T2235c (regime (iii)): uses `ilambda > 0` (eventual, `(eq:WO)`) because the target's `(ilambda²W^d)^{-1/5}` is `0` at `ilambda = 0` in Mathlib.
- No primed successor (`STExpIntIII'`, `STExpIntIV'`) and no new hypothesis was forced: the merged pins are proved as stated.
- Merge note for the hub (§20 (3)): this commit deletes the owed lines of `STStep6IV`, `STExpIntIII`, `STExpIntIV` in `Test/Axioms.lean`; T2233 (merged at `f6650b2`, `git diff 3a58663 main -- RBM3D/Test/Axioms.lean`: one deleted line, `STExpIntII`) edited the same region: keep every deleted line deleted, keep `STStep6III`, `STStep6`, `STExpIntI`. Root import `RBM3D.Induction.ExpIntEasy` is added by the hub (the full build above needed it temporarily).
- `STStep6III` remains open on `LWtermEXP` (LW-14): `ST_step6_caseIII_of_pins (stExpLKLKHi_holds d) <LW-14 proof> (stExpDuhamelZ_holds d) (stExpIntIII_holds d)` is the one-line closure once it is merged.
