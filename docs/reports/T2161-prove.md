Prover model: claude-sonnet-5-5

## Top notices (stage 1b, Sun Oct  4 23:20:59 UTC 2026; section (a) below is unchanged)
1. **Bulk condition (T2001d/l): the decided form changes what Thm 2.7 claims; the dispatcher asks Jun.** Decided: `B_κ = {E : ρ_N(E) ≥ κ}` (`BAbulk`, `ρ_N = π⁻¹ Im m(E+i0, g)`; no `e_λ`, no `supp μ_N`) and the chain domain `Im m(z,g) ≥ κ` with the bridge pin `BAImmLower`. Against the paper's `|E| ≤ e_λ − κ` the energy set of Thm 2.7 (i) is defined for odd `L`, (ii) is non-empty at gap couplings, (iii) loses the cusp points `ρ_N = 0` (`L=4`, `g=g_c=0.3542`: `E*=2.508`) where `lem:propM`(2) fails. Evidence: (a), b.3, b.5.
2. **BA count over 50 (DECISIONS §9 O2): the dispatcher asks Jun before any BA proof ticket starts.** b.9: 57 tickets (53 new + the 4 graph-layer rows BA-L1..L4 of T2040), lines/1000 = 48.8 / 67.1 / 95.6 (lo / central / hi). Not priced: making the merged chain files carrier-generic instead of re-proving the twins (b.8: 258 of 267 chain pins depend on band objects).
3. Paper findings (d): T2161a `GGGamma` (B:398) is false as printed; T2161b `lem:propM`(2) `Im m ≳ 1` fails at cusps; the TeX cites [RBSO1D] Lemma 3.9 only in comments (7_8:1844, 1846).


## (a) Math preflight — Sun Oct  4 20:50:47 UTC 2026

Notation: `g` = paper's `\ilambda` (1_2:256, DECISIONS §12 T2002a) = the ticket's "λ"; `d=3`; `Ψ^(B)` = adjacency of `Z_L^d` (1_2:278); `ν_L` = its spectral measure; `K_ab=|M^(B)_ab|²` (`M^(+,-)`, `S^(B)=I`); `ρ_N=π⁻¹ Im m(E+i0)`. Scripts (python3, numpy/scipy, no Lean) in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161/`; the support is computed exactly: with `u=z+m`, `m=G_{gν}(u)`, `z(u)=u−G(u)`, a real `u` off the atoms with `f(u)=∫dν/(gx−u)²<1` maps into `ℝ∖supp μ_N` (gap = `(z(u1),z(u2))`; outer edges from `f=1`); cross-checked by direct iteration of (self_m) below.

**Finding for the dispatcher (T2001d/l decision; may change what Thm 2.7 claims).** The paper's bulk condition `|E| ≤ e_g−κ` (7_8:1817-1819, `lem:propM` 7_8:1847-1849) is wrong in three ways at admissible `(L,g)`: (1) `L` odd: `e_+≠e_-`; (2) `L=4,g=1/2` already has interior gaps, so `g ≤ 1` does not give an interval (ticket option 2 "or λ≤1" fails); (3) at the gap-opening value `g_c(4)=0.3542` the support is the symmetric interval `[−e,e]`, `e=2.883`, yet `ρ_N(E*)=0` at `E*=2.508`, `|E*|≤e−0.1` (cusp, `ρ∝η^{1/3}`), so even "L even, g small" does not make `|E|≤e_g−κ` imply `Im m ≳ 1`. Literal option 1 (`dist(E,ℝ∖supp)≥κ`) contains `E*` too, and the §11 normalisation `ρ_N(E)^{-n}` is undefined there. Option 2 cannot remove cusps (a `g_c(L)` was found for each `L∈{3,…,8,10,12}`; the sequence `g_n=g_c(L_n)` is admissible). **Recommended form: bulk set `{E : ρ_N(E) ≥ κ}`** (expected equivalent to the paper's form, with `κ` renamed, wherever the paper's `e_g` is defined and `ρ_N≍√(e−|E|)` uniformly (not checked here); extends it to odd `L`, gaps; gives `Im m ≳ 1`, which `lem:propM`(2) needs). It changes the set of `E` of Thm 2.7 (strictly extends, never shrinks) → dispatcher asks Jun.

### (i) Exponent / constant table (d=3; 𝔠=1/20, 𝔡=1/10, κ=0.1)

| item | value | constraint | slack |
|---|---|---|---|
| `𝔠` | 1/20 | `W ≥ N^𝔠`, `N=(WL)³` ⇔ `L ≤ W^{(1−3𝔠)/(3𝔠)}=W^{17/3}` | `L∈{4,6}` fixed: `W^{17/3}` vs `L` |
| `𝔡`, `g` range | 1/10 | `W^{-3/2+𝔡}=W^{-1.4} ≤ g ≤ 𝔡^{-1}=10` | `g=0.3`: upper factor 33; `g=W^{-1.3}`: lower factor `W^{0.1}` |
| `g_c(L)` (first interior gap, cusp) | 0.3389 (L=3), 0.3542 (4), 0.3771 (5), 0.4015 (6), 0.5371 (12) | gap-free iff `g<g_c(L)` (numerics `L≤12`, bisection) | `g=0.3` vs `g_c(3)=0.3389`: 0.039. Option "`g≤g_0<inf_L g_c(L)`" unproved for `L>12` |
| `e_±(g)` | `(L,g)=(6,.2)`: 2.2540/2.2540; `(5,.2)`: 2.2478/2.2575; `(4,.3)`: 2.6381 | paper: `e_+=e_-` | `L=5`: `e_+−e_-=9.7e-3 ≠ 0` |
| bulk lower bound: `min ρ_N` on `[−e_-+κ,e_+−κ]` | min `ρ_N` = 0.0762, 0.0742, 0.0466, 0.0994 at `(6,.2),(5,.2),(4,.3),(6,.001)` | `lem:propM`(2) `Im m≳1`; ρ-form `ρ_N≥κ_ρ` | `κ_ρ=0.04` closes at all four (slack ≥0.0066); constant → 0 as `κ→0` |
| Ward `Σ_b|M_0b|²` | `1` to 1e-9 at `η=1e-10` (all instances) | `=1` at `η=0` (7_8:1869); residual `η/(Im m+η)` | `|m|<1`: `1−|m|²=0.18…0.56` |
| gap of `1−K` (+,−) | `λ_1`: 4.16e-2 (6,.2), 1.835e-1 (4,.3), 5.66e-2 (5,.2); `λ_1/g²=1.000` at `g=1e-3`, `L=6` | `λ_0=0`; `λ_1≳g²L^{-2}` expected (diffusion `2(1−cos 2π/L)g²|m|⁴`) | not uniform in `L` in this table (fixed `L`); L-uniform bound is a 1b/PT obligation |
| gap of `1−M^(+,+)`: `min_k|1−M^(++)_k|` | 1.71 (E=0), 0.506 at `E=e−κ` (6,.2); 0.606 (4,.3); 0.50 (5,.2); 0.62 (6,.001) | `≳1`-type, `Θ^(+,+)` bounded | ≥0.50 |
| `r=(1−|m|²)/min_{t∈[0,1]}|1−tm²|` (A_det:32, `‖M'‖_{∞→∞}≤(1−ε)|1−tm²|`) | 0.4536 (6,.2), 0.8848 (4,.3), 0.4746 (5,.2) at `E=e−κ` | `r ≤ 1−ε` | `ε=0.115` at `(4,.3)`: `ε` shrinks as `g` grows (dependence on `𝔡`, §18) |
| Combes–Thomas (`lem:propM`(3)) | `C_eff=max_{|b|≤3}(|M_0b|/g^|b|)^{1/|b|}` ≤ 1.82 (g≤.3); `min_{b∼0}|M_0b|/g` ≥ 0.57 | `C⁻¹g≤|M_ab|≤(Cg)^{|a−b|}`, `g<(2C)⁻¹` | `C=2`: (3) covers `g<1/4`; `g=0.3` falls under (3') exponential bound |
| flow `zztE_BA`: `t0,E,g0=√t0 g` | `√t0 m(E,g0)=m(z,g)` to 1e-13 (3 points below) | `Im m0>0` at real `E` | `ρ_{g0}(E)=Im m(z,g)/(π√t0) ≥ Im m(z,g)/π` exactly (`t0≤1`): ρ-form passes from `(z,g)` to `(E,g0)`; edge form needs `e_{g0}` not `e_g` (paper writes `e_g`) |
| `zztE_BA` hypothesis `|Re z|≤2−κ` (7_8:1797) | typo for `e_g−κ` (DECISIONS §10, T2001g) | — | — |

### (ii) Concrete nondegenerate instance

Admissible sequences (`𝔠=1/20`, `𝔡=1/10`, `d=3`, `W_n=10^n`) and every deterministic quantity above computed at `d=3`, `L∈{4,5,6}` (rows of `ba_supp`, `ba_det`); non-vacuity of the ρ-form `B_κ={ρ_N≥0.05}` in each vacuity class (`ba_vac`): gaps (`L=4,g=10`), odd `L`, cusp, interval. `T2001` sequence `L_n=4,g_n=10` is admissible (T2001 report) and has `ρ_N(0)=0.178`.
```
$ python3 ba_supp.py ; ba_check.py ; ba_gcL.py ; ba_cusp.py ; ba_vac.py ; ba_det.py ; ba_flow.py ; ba_adm.py   (outputs concatenated)
d=3: exact support of mu_N: left edge -e_-, right edge e_+, interior gaps of supp mu (z(u1),z(u2))
L=4 g=0.5  e_-=3.6202 e_+=3.6202 #gaps=2 first gap=(-3.175,-2.995)
L=4 g=1    e_-=6.4413 e_+=6.4413 #gaps=6 first gap=(-5.954,-4.827)
L=4 g=10   e_-=60.2697 e_+=60.2697 #gaps=6 first gap=(-59.770,-40.636)
L=5 g=0.5  e_-=3.3182 e_+=3.5732 #gaps=2 first gap=(-2.461,-2.449)
L=5 g=1    e_-=5.5666 e_+=6.3815 #gaps=6 first gap=(-4.589,-3.674)
L=5 g=10   e_-=49.0690 e_+=60.1996 #gaps=9 first gap=(-48.057,-27.079)
L=6 g=0.5  e_-=3.5470 e_+=3.5470 #gaps=2 first gap=(-3.319,-3.266)
L=6 g=1    e_-=6.3466 e_+=6.3466 #gaps=8 first gap=(-6.085,-5.568)
L=6 g=10   e_-=60.1576 e_+=60.1576 #gaps=12 first gap=(-59.886,-50.358)
cross-check by direct (self_m) iteration, eta=1e-7: rho_N=Im m/pi at E inside/outside the exact gap
L=4 g=0.5 gap=(-3.175,-2.995) E=(2.5, 3.085, 3.4) rho_N=['1.17e-01', '3.28e-08', '4.45e-02']
L=5 g=1 gap=(0.333,0.346) E=(0.2, 0.3395, 0.5) rho_N=['1.04e-01', '3.73e-07', '1.09e-01']
d=3 g_c(L) (first interior gap opens; cusp there): {3: 0.3389, 4: 0.3542, 5: 0.3771, 6: 0.4015, 7: 0.4259, 8: 0.4497, 10: 0.4949, 12: 0.5371}
g_c(L=4)=0.354226297  gap just above g_c: (2.507922,2.507922) -> cusp E*=2.50792 ; e_g=2.88314 ; E* in [-e+kappa,e-kappa] for kappa=0.1: True
  g=g_c-: eta=0.001 rho_N(E*)=1.6635e-02  rho/eta^(1/3)=0.1663
  g=g_c-: eta=1e-05 rho_N(E*)=3.6224e-03  rho/eta^(1/3)=0.1681
  g=g_c-: eta=1e-07 rho_N(E*)=7.8082e-04  rho/eta^(1/3)=0.1682
gaps: L=4,g=10       e_-=60.2697 e_+=60.2697 #gaps=6 |B_k|/(e_-+e_+)=0.064 nonempty=True rho(0)=0.1781
odd L: L=5,g=0.2     e_-=2.2478 e_+=2.2575 #gaps=0 |B_k|/(e_-+e_+)=0.980 nonempty=True rho(0)=0.2881
cusp: L=4,g=g_c-     e_-=2.8831 e_+=2.8831 #gaps=0 |B_k|/(e_-+e_+)=0.895 nonempty=True rho(0)=0.2505
interval: L=4,g=0.3  e_-=2.6381 e_+=2.6381 #gaps=0 |B_k|/(e_-+e_+)=0.953 nonempty=True rho(0)=0.2636
L=6 g=0.2: e_-=2.2540 e_+=2.2540 #gaps=0  min rho_N on [-e_-+0.1,e_+-0.1]=0.0762
   E=0.0000 |m|=0.9049 Im m=0.9049 Ward=1.000000000 lam1(1-K)=4.163e-02 lam1/g^2=1.041 min_k|1-M++_k|=1.708 C_eff=1.51 min_{b~0}|M_0b|/g=0.755
   E=2.1540 |m|=0.8697 Im m=0.2394 Ward=1.000000000 lam1(1-K)=6.786e-02 lam1/g^2=1.696 min_k|1-M++_k|=0.506 C_eff=1.59 min_{b~0}|M_0b|/g=0.819
L=4 g=0.3: e_-=2.6381 e_+=2.6381 #gaps=0  min rho_N on [-e_-+0.1,e_+-0.1]=0.0466
   E=0.0000 |m|=0.8282 Im m=0.8282 Ward=1.000000000 lam1(1-K)=1.835e-01 lam1/g^2=2.039 min_k|1-M++_k|=1.559 C_eff=1.13 min_{b~0}|M_0b|/g=0.582
   E=2.5381 |m|=0.6663 Im m=0.1464 Ward=0.999999999 lam1(1-K)=4.356e-01 lam1/g^2=4.840 min_k|1-M++_k|=0.606 C_eff=1.43 min_{b~0}|M_0b|/g=0.570
L=5 g=0.2: e_-=2.2478 e_+=2.2575 #gaps=0  min rho_N on [-e_-+0.1,e_+-0.1]=0.0742
   E=0.0000 |m|=0.9050 Im m=0.9050 Ward=1.000000000 lam1(1-K)=5.661e-02 lam1/g^2=1.415 min_k|1-M++_k|=1.708 C_eff=1.50 min_{b~0}|M_0b|/g=0.754
   E=2.1575 |m|=0.8652 Im m=0.2331 Ward=1.000000000 lam1(1-K)=9.889e-02 lam1/g^2=2.472 min_k|1-M++_k|=0.502 C_eff=1.61 min_{b~0}|M_0b|/g=0.812
L=6 g=0.001: e_-=2.0000 e_+=2.0000 #gaps=0  min rho_N on [-e_-+0.1,e_+-0.1]=0.0994
   E=0.0000 |m|=1.0000 Im m=1.0000 Ward=1.000000000 lam1(1-K)=1.000e-06 lam1/g^2=1.000 min_k|1-M++_k|=2.000 C_eff=1.82 min_{b~0}|M_0b|/g=1.000
   E=1.9000 |m|=1.0000 Im m=0.3122 Ward=1.000000000 lam1(1-K)=1.000e-06 lam1/g^2=1.000 min_k|1-M++_k|=0.624 C_eff=1.82 min_{b~0}|M_0b|/g=1.000
g=0.2: e_g=2.25402 ; target window |Re z|<=e_g-kappa=2.15402   (zztE_BA at L=6)
z=+0.0+1i t0=0.3680 E=-0.0000 g0=0.1213 |sqrt(t0)m0-m|=3e-14 rho_g0(E)=0.3056 >= Im m(z)/pi=0.1854 ; e_g0-|E|=2.0903
z=+2.1+0.1i t0=0.7392 E=+2.0258 g0=0.1720 |sqrt(t0)m0-m|=9e-14 rho_g0(E)=0.1049 >= Im m(z)/pi=0.0902 ; e_g0-|E|=0.1593
z=+2.1+0.001i t0=0.9967 E=+2.0992 g0=0.1997 |sqrt(t0)m0-m|=1e-13 rho_g0(E)=0.0953 >= Im m(z)/pi=0.0952 ; e_g0-|E|=0.1539
L=4,g=0.3 (fixed) n=2 N=6.4e+07: W>=N^c True; W^{-d/2+dd}=1.6e-03 <= g=3.0e-01 <= 1/dd=10: True
L=4,g=0.3 (fixed) n=8 N=6.4e+25: W>=N^c True; W^{-d/2+dd}=6.3e-12 <= g=3.0e-01 <= 1/dd=10: True
L=6,g=W^-1.3   n=2 N=2.2e+08: W>=N^c True; W^{-d/2+dd}=1.6e-03 <= g=2.5e-03 <= 1/dd=10: True
L=6,g=W^-1.3   n=8 N=2.2e+26: W>=N^c True; W^{-d/2+dd}=6.3e-12 <= g=4.0e-11 <= 1/dd=10: True
L=6 g=0.2 E=0.0000: 1-|m|^2=0.1812 min_t|1-t m^2|=1.0000 r=0.1812
L=6 g=0.2 E=2.1540: 1-|m|^2=0.2437 min_t|1-t m^2|=0.5372 r=0.4536
L=4 g=0.3 E=0.0000: 1-|m|^2=0.3142 min_t|1-t m^2|=1.0000 r=0.3142
L=4 g=0.3 E=2.5381: 1-|m|^2=0.5560 min_t|1-t m^2|=0.6284 r=0.8848
L=5 g=0.2 E=0.0000: 1-|m|^2=0.1811 min_t|1-t m^2|=1.0000 r=0.1812
L=5 g=0.2 E=2.1575: 1-|m|^2=0.2514 min_t|1-t m^2|=0.5297 r=0.4746
```

**External citations of the BA part** (internal route per DECISIONS §5; the `\cite` list from `1_2:599-675`, `7_8:1792-2108`, `B:286-525`, `A_det`):
- [Biane] (1_2:624, `ρ_N` continuous): route: bulk set `{ρ_N ≥ κ}` with `m` the `Im m>0` solution of (self_m) (iteration converged to residual ≤1e-15 in `ba_det`); existence/uniqueness of `m` to be proved in 1b.
- [RBSO1D] Lemma 3.3 (`zztE_BA`): algebra: `m0=m/√t0` solves (self_m) at `(E,g0)` iff `E=(t0 z−(1−t0)m)/√t0` and `t0 Im z=(1−t0)Im m`; numerics 1e-13 above.
- [LeeSchSteYau2015] Lemma 3.5 (`Im m ≳ 1`): with the ρ-form this is the hypothesis, not a result.
- [Aizenman_book] Thm 10.5 (Combes–Thomas, `Mbound_AO2`): RBM2D has `Propagator/CombesThomas*.lean`; port for `M=(gΨ−u)⁻¹`, `Im u≥Im m>0`.
- [RBSO1D] Lemma 6.1, 7.1, §7.1, §7.3 (`lem_GbEXP_BA`, `lem_ConArg_BA`): paper says "verbatim"; owed, DECISIONS §19.
- [yang2024Del] B.9–B.11 (`GGGamma` expansions), Lemma 3.1/(E.19) (Θ^(+,−) decay), [DYYY25] 2.14: internal (BA-L1…L4 / PT).
- [bourgade2019random] Lemma 4.2 (band case only); LSY Thm 2.2 (§5, authorized). LSY limit computation: its text is not in the repository (T2001 report, same point); for BA at fixed `(L,g)` `μ_N` does not depend on `N`, so `ρ_N(E)≥κ_ρ>0` is a fixed number (table); the LSY hypothesis check is left to UN-D1/1b.

### Verdicts
- Deterministic layer of BA (`(self_m)`, `(def_G0)`, Ward, `Θ_BA` gaps, `lem:propM`, `zztE_BA`) at `d=3` nondegenerate data: **PASS** (instances above; all hypotheses hold at once at `L=4,g=0.3` and `L=6,g=W^{-1.3}`, `n=2,8`).
- Paper's literal bulk condition `|E|≤e_g−κ` as a premise of the BA pins: **FAIL** (vacuous at gap sequences, ill-defined for odd `L`, false at cusps); recommended replacement `ρ_N(E)≥κ`: **PASS** at all four vacuity classes.
- Overall BA-D1 preflight: **PASS** (stage 1b may proceed with the ρ-form pending Jun's answer; the dispatcher decides whether to ask).

## (a′) Preflight corrections — Sun Oct  4 23:20:59 UTC 2026
Two phrases of (a) are imprecise; the verdict PASS is unchanged. (1) "strictly extends, never shrinks": the ρ-form removes the cusp points (`ρ_N=0` inside `|E| ≤ e_g−κ`, `L=4`, `g=g_c`), and its constant `κ_ρ(κ)` degrades as `g ↑ g_c(L)` (b.3: `min ρ_N` on `|E| ≤ e−0.1`, `L=4`, is 0.0994 at `g=0.01` and 0.0468 at `g=0.3`; `ρ_N(E*)=0` at `g_c`). (2) "false at cusp" is the claim `Im m ≳ 1` of `lem:propM`(2), not Thm 2.7. The notices above were inserted below line 1; (a) itself is byte-identical.

## (b) Script output
`W`=/Users/junyin/Lean_proof/RBM3D-wt/T2161 (branch `t/T2161`, base 275e275, HEAD 82e72b3, `RBM3D/Probe/T2161Pins.lean`, 2730 lines); `S`=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161 (scripts; `$S/final_run.sh` regenerates every output). Full outputs, tables and scripts: `docs/reports/T2161-portmap.md` (P.1-P.12).
### b.1 Build, axioms, hygiene
    $ git diff --name-only main...t/T2161; lake env lean RBM3D/Probe/T2161Pins.lean > $S/final_lean.out; echo "lean exit=$?"; tail -1 $S/final_lean.out; lake build RBM3D.Probe.T2161Pins > $S/final_build.out 2>&1; tail -2 $S/final_build.out; echo "probe warnings $(grep -c "warning: RBM3D/Probe/T2161Pins" $S/final_build.out)"
    RBM3D/Probe/T2161Pins.lean
    lean exit=0
    'RBM.BA.Inst.inst_cls_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
    info: RBM3D/Probe/T2161Pins.lean:2730:0: 'RBM.BA.Inst.inst_cls_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
    Build completed successfully (3749 jobs).
    probe warnings 0
    $ echo "std-axiom theorems $(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' $S/final_lean.out); other axiom lines $(grep 'depends on axioms' $S/final_lean.out | grep -vc '\[propext, Classical.choice, Quot.sound\]'); forbidden tokens $(grep -cE 'sorry|admit|native_decide|^axiom' $W/RBM3D/Probe/T2161Pins.lean)"
    std-axiom theorems 125; other axiom lines 0; forbidden tokens 0
    $ python3 $S/name_clash.py | sed -n "1,2p;5p"   # new public names vs RBM3D and RBM2D@c9a24cf (RBM1D, main: portmap P.10)
    declarations in the probe: 269 (public 269, private 0); namespaces used: ['RBM.BA', 'RBM.BA.Inst']
    exact full-name clashes with other RBM3D files (worktree, base 275e275): 0 []
    RBM2D @c9a24cf: files declaring one of them: []
### b.2 Pins (item 2): registry class of every Prop-valued definition (DECISIONS §16, §20); statements of the targets, extracted by script
    $ python3 $S/registry.py | sed -n "1,6p" | cut -c1-250
    Prop-valued definitions of the probe: 74; classified: 74; unclassified: []; classified but absent: []
    owed       36: BAmExists BAmUniqReal BAmBoundary BAWard BAPropM BAoffDiag BAImmLower BAProp5 BAProp5s BAProp6 BAProp7 BAProp8 BAProp5to8 BAMainInd BAGbEXP BAConArg BAStep1 BAStep2 BAEMn2Exp BAKsolve BAKbound BAlanlw BAlweight BAGGGamma BAEnd_locSC BA
    structural 13: BASelf BAedgeBulk BAdistBulk BAbulk BAReal BAdom BAFlow BAGbEXPpre BAendDom BAIsOrthoEigenbasis BAqueWindow BAqueBad BAque2Bad
    shape       9: BAGbEXPconcl BAConArgLoop BAConArgVec BAlocSCConcl BAqdConcl BAdecolConcl BAqueConcl BAunivConcl Thm27At
    carrier    16: STLKg STLmaxg STDecayg STDecayStrongg STLocalMaxg STLocalEntryg STExp2g STInitialGT2g STKboundg STStep1Loopg STStep1Weakg STLWassmExpg STMainIndG STStep2Localg STStep2Avgg STStep2Decayg
    borrowed    0: -
    $ python3 $S/statements.py BAMainInd BAEnd_BUniv BAThm27
    -- RBM3D/Probe/T2161Pins.lean:1071
    def BAMainInd (d : ℕ) : Prop :=
      STMainIndG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        (fun sz z n => BAflowT0 sz z n)
    -- RBM3D/Probe/T2161Pins.lean:1652
    def BAEnd_BUniv (d : ℕ) : Prop :=
      3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (k : ℕ), 1 ≤ k → ∀ κ : ℝ, 0 < κ →
        ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ E' : ℝ, |E'| < 2 →
          ∀ O : (Fin k → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
            BAunivConcl sz k E E' O
    -- RBM3D/Probe/T2161Pins.lean:1659
    def BAThm27 (d : ℕ) : Prop :=
      BAEnd_decol d ∧ BAEnd_locSC d ∧ BAEnd_QUE d ∧ BAEnd_BUniv d ∧ BAEnd_QDiff d
### b.3 Bulk condition (T2001d/l): forms and the bridge `BAImmLower` at the vacuity classes
    $ sed -n "442p;448p;451p" $W/RBM3D/Probe/T2161Pins.lean   # forms 0, 1, 3 (the chain domain `BAdom` and `BAReal` are at :455, :459)
    def BAedgeBulk (e κ E : ℝ) : Prop := |E| ≤ e - κ
    def BAdistBulk (g κ E : ℝ) : Prop := ∀ x : ℝ, x ∉ BAsuppSet d L g → κ ≤ |E - x|
    def BAbulk (g κ E : ℝ) : Prop := κ ≤ BArho d L g E
    $ python3 $S/n1_immlower.py   # min Im m(E+iη) over B_κ (κ=0.05), η∈(0,1], vs πκ
    d=3 rho-bulk B_k (k=0.05): min over E in B_k, eta in (0,1] of Im m(E+i eta)  [pi*k=0.1571]
    gaps  L=4 g=10         |B_k| pts= 15/241  min Im m = 0.0858 at (E,eta)=(-40.180,1)  ratio to pi*k = 0.55
    odd   L=5 g=0.2        |B_k| pts=235/241  min Im m = 0.1852 at (E,eta)=(-2.191,0.03)  ratio to pi*k = 1.18
    cusp- L=4 g=0.35422    |B_k| pts=215/241  min Im m = 0.1525 at (E,eta)=(-2.691,0.1)  ratio to pi*k = 0.97
    intvl L=4 g=0.3        |B_k| pts=229/241  min Im m = 0.1598 at (E,eta)=(-2.506,0.03)  ratio to pi*k = 1.02
    small L=6 g=0.001      |B_k| pts=237/241  min Im m = 0.1788 at (E,eta)=(1.967,0.01)  ratio to pi*k = 1.14
    large g L=6 g=3        |B_k| pts= 65/241  min Im m = 0.0385 at (E,eta)=(-15.173,1)  ratio to pi*k = 0.25
    $ sed -n "1p;2p;4p" $S/n1_equiv.out | cut -c1-175   # output of `python3 $S/n1_equiv.py`: c1(κ)=min ρ_N on |E| ≤ e−κ, even L, no gaps
    d=3, L even, no gaps.   kappa:  c1(kappa)=min rho on |E|<=e-kappa ; sqrt(kappa)/pi (semicircle edge) ; then k'=0.05: c2(k')=min{e-|E|: rho>=k'}
    L=4 g=0.01  e=2.0006  k=0.30: 0.1676 (sc 0.1743) | k=0.10: 0.0994 (sc 0.1007) | k=0.03: 0.0549 (sc 0.0551) | k=0.01: 0.0318 (sc 0.0318) | k'=0.05: c2=0.0250
    L=4 g=0.3   e=2.6381  k=0.30: 0.0639 (sc 0.1743) | k=0.10: 0.0468 (sc 0.1007) | k=0.03: 0.0275 (sc 0.0551) | k=0.01: 0.0167 (sc 0.0318) | k'=0.05: c2=0.1209
### b.4 Constants where `M ≠ mI` (item 4; DECISIONS §18: constants may depend on Λ = 𝔡⁻¹)
    $ python3 $S/n2_table.py | sed -n "2p;3p;5p;7p;22p;23p" | cut -c1-175
    L   g      E       Im m    |m|     sum|M_0b|^2  r      Dk/g^2    lam1/(g^2 2(1-cos)) |M_0e|/min(g,1) ct
    5   0.05   0.000   0.9926  0.9926  0.999999999  0.015  1.005     1.002          0.978        ['3.02', '3.02', '2.01']  chk=0.0e+00
    5   0.3    0.000   0.8243  0.8243  0.999999999  0.321  1.156     1.040          0.594        ['1.73', '1.67', '1.11']  chk=4.4e-16
    5   1      0.000   0.4382  0.4538  0.999999997  0.794  0.773     0.555          0.138        ['1.98', '1.01', '0.67']  chk=0.0e+00
    9   3      0.000   0.3028  0.3031  0.999999997  0.908  0.308     0.198          0.050        ['2.99', '1.78', '0.97']  chk=0.0e+00
    9   10     0.000   0.2883  0.2883  0.999999997  0.917  0.029     0.018          0.015        ['4.18', '2.37', '0.95']  chk=2.2e-16
### b.5 Instances (item 7): compiled; the three class sequences of 13.9 and the sequence `sz0`
    $ python3 $S/instances_index.py | grep -E "^13\.(2|5|6|9) "
    13.2   8 theorems: P4_g0_le:1985 inst_BAmExists:1988 inst_BAmUniqReal:1992 inst_BAmBoundary:1996 inst_BAWard:2001 inst_BAPropM:2006 inst_BAoffDiag:2013 inst_BAImmLower:2022
    13.5   7 theorems: inst_BAMainInd:2209 inst_BAGbEXP:2226 inst_BAConArg:2247 inst_BAStep1:2257 inst_BAStep2:2267 inst_BAEMn2Exp:2279 inst_BAKbound:2309
    13.6  10 theorems: inst_BAEnd_locSC:2314 inst_BAEnd_QDiff:2317 inst_BAEnd_decol:2320 inst_BAEnd_QUE:2324 bump1_smooth:2334 bump1_supp:2337 bump1_zero:2340 inst_BAEnd_BUniv:2349 inst_BAThm27:2357 inst_BAThm27_skeleton:2366
    13.9  15 theorems: clsSz_L_le_W:2452 clsSz_tendsto:2458 clsSz_bandwidth:2468 clsSz_WO:2486 clsSz_admissible:2510 clsκ_pos:2521 cls_bulk:2525 cls_domain:2534 inst_cls_Thm27:2554 inst_cls_Thm27_chain:2574 hg_fifth:2583 hg_3_10:2585 inst_cls_gaps:2588 inst_cls_odd:2593 inst_cls_interval:2598
    $ python3 $S/cls_numerics.py | cut -c1-250   # class of `g_0` (same formulas as `fp`; `E_*≈0` at even `L`)
    subordination point w = 6i/5, d = 3: flow point (g0 = sqrt(t0) g_raw, E_*, m0 = m_w/sqrt(t0)); lower bound of the probe: t0 >= 1/(|w|^2+g_raw^2 L^3)
    L   g_raw    t0        t0 bound  g0        E_*        Im m0     residual  Re m0         | support at g0: e_-, e_+, #gaps, rho_N(E_*), pi*kappa=Im m0 | class
    4   10       0.2183    0.000156  4.6723    -0.00000   0.56068   1.1e-16   2.20e-18      | 28.3260 28.3260 6 0.17847 0.56068 | gaps (6 interior gaps, first (-27.827,-19.352))
    5   0.2      0.6101    0.155     0.1562    -0.00015   0.93728   3.1e-17   1.51e-04      | 2.1503 2.1527 0 0.29835 0.93728 | odd L (e_+ != e_-: 2.1527 vs 2.1503)
    4   0.3      0.5492    0.139     0.2223    0.00000    0.88931   2.2e-16   -9.36e-18     | 2.3389 2.3389 0 0.28307 0.88931 | interval (g0 < g_c(4)=0.3542)
### b.6 Extremes of the PT-BA pins and of `BAKsolve`
    $ python3 $S/n3_pt.py | sed -n "1p;2p;3p;33p;38p;40p"
    d=3 BA (+,-): P5=max|Th|/(B e^{-0.3|a|/l}); P8=max|Th0|(g^2+e)(|a|+1); U1,U2s unit differences (|x|>=2); (+,+): P5s=max|Th++|/(1_{a=0}+g^2 e^{-|a|/2})
    L   g     E      e         Im m    | P5     P8     U1     U2s    P5s   
    15  0.05  0.000  1.00e-09  0.9926  | 0.76   0.24   0.39   1.05   0.50  
    15  3     0.000  1.00e-09  0.2093  | 0.26   9.42   7.90   177.51 1.31  
    15  10    0.000  1.00e-09  0.1813  | 0.23   103.57 148.23 3323.06 0.04  
    15  10    0.000  9.99e-01  0.1813  | 98.06  100.97 0.12   2.68   0.01  
    $ python3 $S/n4_kn2.py | sed -n "1p;3p;5p"
    d=3 L=5 g=0.3 E=0 (+,-): max |d/dt K2 - (K2*K2)| / max|d/dt K2|  (central difference, h=1e-6(1-t))
      t=0.5        rel residual 2.99e-10   (|K2| max 1.041e+00)
      t=0.999999   rel residual 2.21e-05   (|K2| max 7.992e+03)
### b.7 The graph-layer expansions (BA-L2) at an extreme input
    $ python3 $S/n6_lw.py | sed -n "2p;4p;6p;8p" | cut -c1-175
    GGGamma first two sums with coefficient S^+_{x be} (as printed, B:398)
      f#0:  lanlw 3.06e-07 (|LHS|=0.011)   lweight 8.17e-07 (|LHS|=0.014)   GGGamma 1.24e-02 (|LHS|=0.004)
    GGGamma first two sums with coefficient (M^+ S^+)_{x be}
      f#0:  lanlw 3.06e-07 (|LHS|=0.011)   lweight 8.17e-07 (|LHS|=0.014)   GGGamma 1.20e-06 (|LHS|=0.004)
    $ python3 $S/n6_lw_mc.py | sed -n "1p;4p"; python3 $S/n6_lw_mc_printed.py | sed -n "2p"   # W=2, N=6, 4e5 samples
    W=2, N=6, L=3, n=400000 samples; f = |G_01|^2; lanlw (x,y)=(0,0); lweight x=2; GGGamma (x,y,y')=(0,2,2)
      GGGamma (M^+S^+ coefficient)   LHS=-0.00057-0.00010i  RHS=-0.00057-0.00010i  |LHS-RHS|=6.5e-06  (MC s.e. ~ 5.3e-06)
      GGGamma with S^+ as printed    LHS=-0.00057-0.00010i  RHS=+0.00072-0.00036i  |LHS-RHS|=1.3e-03  (MC s.e. ~ 5.3e-06)
### b.8 Inventory (item 1): paper statements, merged declarations, RBM2D port candidates (file:line at `c9a24cf`), cost structure
    $ python3 $S/inv_paper_summary.py
    statement environments naming the BA model: 18 (each with its proof; `$S/inv_paper.out` has cites and pins)
      new    (3): MR:decol_BA 1_2:644-669; lem:main_ind_BA 7_8:1825-1828; def scalingBA B:345-356
      shared (5): def_flow 1_2:714-734; lem:SE_basic 1_2:949-979; def_Theta 1_2:1068-1090; lem_propTH 1_2:1119-1170; lem_pureloop A:643-648
      cited  (9): lem_WI_K 1_2:1034-1044; zztE_BA 7_8:1796-1808; lem:propM 7_8:1846-1906; lem_GbEXP_BA 7_8:1916-1946; lem_ConArg_BA 7_8:1956-1985; tree-representation_BA A:592-598; lanlw B:359-372; lem_lweight B:376-387; GGGamma B:393-405
      band   (1): lem_GbEXP 3_5:14-35
    $ python3 $S/inv_merged_summary.py | sed -n "1p"; tail -2 $S/inv_merged_ba.out
    33 merged declarations found: covers 24, shape 5, band 4; by file: BlockAnderson 7, GLoopFlow 6, Pins 2, Resolvent 2, KLTree 4, LWPins 2, LWVocab 1, StochDomAt 2, Sizes 1, Params 2, Defs 3, Prop6Hold 1
    files read from the worktree of t/T2161, base (merge-base with main) 275e275; main is now 04aedec; .lean files changed on main since the base: ['RBM3D.lean', 'RBM3D/Evolution/MeanFar.lean', 'RBM3D/Induction/AzumaProxyN.lean', 'RBM3D/Induction/AzumaProxyN2.lean', 'RBM3D/Induction/IniTermII.lean', 'RBM3D/Path/LemDecCalE.lean', 'RBM3D/Test/Axioms.lean']
    inventory declarations among them: []
    $ sed -n "/^group totals/,/^files mentioning/p" $S/inv_rbm2d.out; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Endpoints.lean   # port: `BAIsOrthoEigenbasis` = RBM2D/Endpoints.lean:56-59 (c9a24cf); per-file rows: portmap P.1d
    group totals (files, lines at c9a24cf, kept lines at 0c1330a (0 = deleted by RBM2D T2274), d=2 tokens):
      CombesThomas* (BA-D4)                            8 files   669 lines     0 kept   0 tokens
      FreeConv* (BA-D2, D6)                            2 files  1554 lines  1455 kept   0 tokens
      Step1Band + BUnivHolds (UN-D1/T2162)             2 files  1335 lines  1225 kept   2 tokens
      Main/{Decol,QUE,RegionUnif,Endpoints} (MA-BA)    4 files  2466 lines  1472 kept  56 tokens
      Endpoints.lean (probe 11, ported pins)           1 files   268 lines   268 kept   2 tokens
    files mentioning "anderson" at c9a24cf (git grep -il): 0
     RBM2D/Endpoints.lean | 66 ++++++++++++++++++++++++++--------------------------
     1 file changed, 33 insertions(+), 33 deletions(-)
    $ sed -n "/^TOTAL/p" $S/decl_inv.out; sed -n "1p;\$p" $S/pin_subst2.out   # merged Lean: lines whose signature mentions a band token; chain pins that depend on band objects
    TOTAL         10918  161863 |   1715   37383 |    961   22582
    transitive closure over all 1326 merged defs: 1272 band-dependent
    total                                                                      267       258
### b.9 External citations (item 3) and the split (item 6): count against DECISIONS §9 O2
    $ python3 $S/cites_grouped.py
    #  source                                                       | cited at                   | statement                                                                | used in                | internal route                                                                                                         | items (BA-)        lines c
    1  [Biane]                                                      | 1_2:624                    | mu_N=semicircle(x)nu_L, density, m solves (self_m)                       | (self_m), rho_N        | Schwarz-Pick fixed point; RBM2D FreeConv port (719 l.); boundary values                                                | D2,D6              2100
    2  [RBSO1D] L3.3 (zztE_BA)                                      | 7_8:1796                   | sqrt(t0) m(E,g0)=m(z,g), sqrt(t0) M(E,g0)=M(z,g), G =_d sqrt(t0) G_t0    | flow, all steps        | algebra, proved in the probe (BAzztE_data/_Mres) + merged Gt_BA                                                        | D1                 1300
    3  lem:propM: [RBSO1D L3.9] (commented out), [LSY15 L3.5], [Aizenman Thm 10.5] | 7_8:1844,1846,1908,1911    | translation inv., Ward, Im m >~ 1, Mbound_AO(2)                          | Theta, Steps 1-6       | Ward proved (BAward_avg); Taylor; Combes-Thomas (RBM2D CT*, 669 l.); Im m bridge BAImmLower (Holder-1/3 + Poisson)     | D3,D4,D7           3250
    4  [RBSO1D] L6.1                                                | 7_8:1948                   | lem_GbEXP_BA: GiiGEX, GijGEX, GavLGEX (g <= W^-eps there)                | Step 1, Step 5(iii)    | RBSO1D text not in the repo; Schur/LDE rebuild, merged Green/* as the band model                                       | G1,G2,G3,G4,G5,G6  7800
    5  [RBSO1D] L7.1, S7.1, S7.3; [YY_25] S5.3                      | 7_8:1987,1990,2101         | lem_ConArg_BA; Step 1 (lRB1, Gtmwc); Step 5 large t                      | Steps 1, 5             | same arguments with (W^d l^d eta)^-1 for W^-d B; merged S1-32.., Step5*                                                | S1,S2,S3,U5        4500
    6  [RBSO1D] L3.17                                               | 1_2:1046                   | Ward identity for K-loops (lem_WI_K)                                     | Steps 2-5, Kbound      | merged KLWard.lean/KLWardIneq.lean as the model                                                                        | K5                 800
    7  [RBSO1D] L4.16, S4, L4.29, Claim 4.30; [YY_25] L3.10         | A:376,592,734              | tree representation with M-entries; molecule sum-zero                    | ML:Kbound, Kn2sol      | ODE d/dt Theta = Theta M Theta; merged KLtreeValW, KLPure                                                              | K2,K3              2800
    8  [RBSO1D] L3.10, [yang2024Del] L3.1, (E.19); [DYYY25] L2.14, S8; [Lawler] S2 | A:50-67                    | Theta(+,-) bounds by summation by parts; Gaussian tail of K^n, local CLT | lem_propTH 5-8 for K=|M|^2 | Fourier symbol of K, Esscher tilt; merged PropUnit/HeatProduct as models                                               | P4,P5,P6           3800
    9  [RBSO1D] A.10, (A.112); [DYYY25] S7                          | 3_5:2213,2248              | CLT cancellation of the far term ("does not depend on d")                | Step 5                 | merged Evolution/Clt* (S5-17..24) over the carrier                                                                     | U4                 1200
    10 [yang2024Del] L B.9-B.11, App. B                             | B:357-407                  | lanlw, lem_lweight, GGGamma; reduction to locally standard graphs        | LWterm_EXP (Step 6)    | checked numerically (b.7; delta T2161a); BAlanlw/BAlweight/BAGGGamma; BA-L2, L3                                        | L2,L3              3990
    11 LSY Thm 2.2 (authorized, DECISIONS 5)                        | 1_2 Thm B_Univ             | bulk universality of Gaussian-divisible matrices                         | UN                     | external, no proof lines; BA wrappers only                                                                             | N1,N2              2000
    12 [bourgade2019random] L4.2; [PelSchShaSod]; [LSY15, knowles20] | A:25; 1_2:39,634,672       | band properties of S^(B)(g); localization; background                    | band / remarks         | not used for BA                                                                                                        | -                  0
    $ python3 $S/ba_split2.py | sed -n "1,15p;17p;19p;20p"   # items = tickets of 600-1500 lines (rows: `$S/ba_split2.py full`, portmap P.9)
        group                        items | lines lo / central / hi 
    D   deterministic layer              6 |   4650   6650   9600
    P   propagator (PT-BA)               8 |   5500   7600  10800
    K   K-loops (KL-BA)                  5 |   4600   6100   8400
    E   evolution kernels (EK-BA)        3 |   2200   3200   4500
    G   lem_GbEXP_BA chain               6 |   5600   7800  11100
    S   Step 1                           3 |   2300   3200   4600
    T   Step 2                           8 |   7800  10900  15400
    U   Steps 3-5                        6 |   4600   6800   9800
    V   Step 6 and chain                 3 |   2200   3200   4700
    L   graph layer (T2040 rows)         4 |   5833   6363   8296
    M   MA-BA                            3 |   2300   3300   4900
    N   UN-BA                            2 |   1200   2000   3500
        TOTAL                           57 |  48783  67113  95596
    lines/1000 (all groups): lo 48.8  central 67.1  hi 95.6 ; items 57
    items with central > 1500 lines (600-1500 rule): [('BA-K2', 1600), ('BA-K4', 1600), ('BA-T2', 1700), ('BA-L2', 2400), ('BA-L3', 1590)] ; tickets if every item is cut at 1500 central lines: 62
    DECISIONS 9 O2 (25/40/50): items 57, lines/1000 central 67.1 -> OVER 50
    owed pins to discharge: 36; discharged by some item: 36; missing: []; discharged twice: []
### Reading (narrative)
1. The probe has 2730 lines, 269 declarations, 125 theorems with the three standard axioms only; sections: 0-2 resolvent identities and bulk forms, 3 deterministic pins, 4 PT pins, 5-9 chain pins over a flow carrier, 10 graph layer, 11 endpoints, 12-12.1 skeletons with six glue pins, 13 instances (82 theorems).
2. Proved here, not pinned: subordination (`BASelf_subord`: explicit `(self_m)` data at `z = w − m_w`, `Im w > 1`); `zztE_BA` (clauses 1-3 by `BAzztE_data`, `BAzztE_Mres` for any Hermitian `Ψ`, clause 4 is the merged `Gt_BA`; the hypothesis `|Re z| ≤ 2−κ` of 7_8:1797 is dropped, T2001g); averaged Ward `BAward_avg`; `BAbulk_iff`; `BAdom_real` (chain domain ⇒ real-axis datum `(g_0, E, m_0)`, `g_0 = √t_0 g ≤ g`); `BAlocalEntry_of_flow`; `BAendDom_to_dom`.
3. Steps that reuse the ST pins with `M` for `m`: 3, 4, 5 except `sec:Step5_larget` (`1−t ≥ g²`, case (iii)) and 6 except `lem:LWterm_EXP` "extend verbatim" (7_8:2100-2105), so they get no BA statement. The 16 `ST*g` forms restate the merged band pins over `FlowFM`: at `bandFM` they are the merged pins (`Iff.rfl`), at `baFM` the BA pins. BA statements exist only where the paper changes: Step 1 (`BAGbEXP`, `BAConArg`, `BAStep1`), Step 2 (`BAStep2`, `BAEMn2Exp`: deterministic `𝒥`), 5(iii) (consumes `BAGbEXP`), Step 6 (`BAlanlw`, `BAlweight`, `BAGGGamma`; BA-L1..L4), K-loops (`BAKsolve`, `BAKbound`), PT 5-8 for `K=|M|²` (`BAProp5..8`). Every chain pin quantifies its constants (`κ, ε, 𝔡`, then `c`, `𝔠_d` or `C_d`) before `∀ sz z` (`BAMainInd`, `BAGbEXP`, `BAConArg`, `BAStep1`, `BAStep2`).
4. This does not make the merged proofs generic: 258 of 267 chain pins depend on band objects and 37383 signature lines hardwire a band token (b.8): the twins are re-proved (priced in b.9) or the merged files are refactored (not priced).
5. Endpoints are in the form of DECISIONS §11 with the ρ-bulk (`BAEnd_*`, `BAThm27`); six glue pins (BA-V2, MA-BA, UN-BA) make `BAThm27_skeleton_chain` a compiled implication graph: the deterministic pins, `BAKsolve`, the Step 1-2 pins, `BAKbound` and the three graph expansions ⇒ `BAThm27`; `inst_cls_Thm27_chain` applies it at the class sequences. Scales as in the ST pins: `≺` is `Prec` at `N` (`W^τ`, `W^{-D}` read as `N^τ`, `N^{-D}`, T2002i; `|x−y|` is `W|[x]−[y]|`, T2001e).
6. Instances (b.5): at `sz0` every chain pin is applied with all deterministic hypotheses discharged (the pin hypothesis is `BAmExists`); at three class sequences (gaps, odd, interval; 13.9) the ρ-bulk contains `E_*` with `ρ_N(E_*) ≥ κ_*` and `𝐃^{BA}` is nonempty for every `n` (compiled); `BAThm27 3` and `BAmUniqReal 3` are the only hypotheses.
7. Not compiled: the ρ-bulk at a prescribed coupling such as `g=10` (needs the spectral form of `(self_m)`, BA-D2); the regime of `g_0` (numerics, b.5); the carrier forms of the Steps 3-6 pins as named pins (BA-U1..V3 name them).
8. Findings: `GGGamma` (B:398) needs `(M⁺S⁺)_{xβ}` in its first two sums (b.7: 1.2e-6 against 1.2e-2 exact; Monte Carlo 6.5e-6 against 1.3e-3); the constants of `BAPropM`, `BAoffDiag`, `BAProp5` depend on `Λ` (b.4, b.6: `r` rises from 0.015 to 0.917 in the rows shown and reaches 0.982 at `L=7, g=3` (P.4); `P5` reaches 98 at `g=10`); RBM2D has no BA chain (0 files mention "anderson", b.8), so only CT, FreeConv and the Main files port; the [RBSO1D] text is not in the repository, so the G group is priced from the band chain (widest spread, b.9).

## (c) Verified Mathlib names (`#check`, exit 0; absent = `#check_failure` "Unknown constant"; `$S/names_check.lean`)
    $ python3 $S/oneline.py $S/names_check.out
    present Real.sqrt_le_one                   : ∀ , √x ≤ 1 ↔ x ≤ 1
    present Real.rpow_le_rpow_of_nonpos        : ∀ , 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
    present Matrix.nonsing_inv_eq_ringInverse  : ∀ (A : Matrix n n α), A⁻¹ = Ring.inverse A
    present Matrix.inv_smul                    : ∀ (A : Matrix n n α) (k : α) , IsUnit A.det → (k • A)⁻¹ = ⅟k • A⁻¹
    present Matrix.trace_smul                  : ∀ (r : α) (A : Matrix n n R), (r • A).trace = r • A.trace
    present Finset.sum_mul_sq_le_sq_mul_sq     : ∀ (s : Finset ι) (f g : ι → R), (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2
    present EuclideanSpace.inner_single_right  : ∀ (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι), inner 𝕜 v (EuclideanSpace.single i a) = a * (starRingEnd ((fun x => 𝕜) i)) (
    present EuclideanSpace.norm_sq_eq          : ∀ (x : EuclideanSpace 𝕜 n), ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2
    present Matrix.toEuclideanLin              : → → → → → → Matrix m n 𝕜 ≃ₗ EuclideanSpace 𝕜 n →ₗ EuclideanSpace 𝕜 m
    present ContDiffBump.contDiff              : ∀ (f : ContDiffBump c) , ContDiff ℝ ↑n ↑f
    present ContDiffBump.hasCompactSupport     : ∀ (f : ContDiffBump c) , HasCompactSupport ↑f
    present ContDiffBump.one_of_mem_closedBall : ∀ (f : ContDiffBump c) , x ∈ Metric.closedBall c f.rIn → ↑f x = 1
    present HasCompactSupport.comp_homeomorph  : ∀ , HasCompactSupport f → ∀ (φ : X ≃ₜ Y), HasCompactSupport (f ∘ ⇑φ)
    present EuclideanSpace.equiv               : (ι : Type u_1) → (𝕜 : Type u_2) → → EuclideanSpace 𝕜 ι ≃L ι → 𝕜
    ABSENT  Finset.inner_mul_le_norm_mul_norm
    ABSENT  Real.sqrt_lt_one
    ABSENT  Real.rpow_le_rpow_of_exponent_nonpos
    ABSENT  Nat.pos_pow_of_pos
    ABSENT  Real.sqrt_le_one_iff_le_one_of_nonneg

## (d) Open issues and paper-delta candidates
Paper-delta candidates (the dispatcher numbers them):
- **T2161a** `GGGamma` (B:393-405): in the first two sums the coefficient `S^+_{xβ}` must be `(M^+S^+)_{xβ} = (1+M^+S^+)_{xβ} − δ_{xβ}` (b.7; `BAGGGamma` uses the corrected form; the third sum, `lanlw` and `lem_lweight` hold as printed).
- **T2161b** bulk condition: `|E| ≤ e_λ − κ` (1_2:649, 7_8:1817) and `lem:propM`(2) `Im m ≳ 1` (7_8:1908) are undefined for odd `L`, empty at gaps, and `Im m = 0` at cusps; the probe uses `ρ_N ≥ κ` (top notice 1, b.3). Related: [RBSO1D] L3.9 appears only in comments (7_8:1844, 1846).
- **T2161c** (convention) `B_{t,K}` (1_2:1107-1108) and `ℓ_t` (1_2:1121-1123) carry `ilambda`; in the BA flow the coupling is `g_0 = √t_0 g`; the probe keeps the model `g_n` (merged `Bparam`); the two agree up to the constant `t_0 ≥ κ/(κ+1)` (`Im m ≥ κ`, `Im z ≤ 1`); the paper does not say which.
Open issues for the dispatcher: (1) Jun: the bulk form and the BA count (top notices); the ρ-bulk at a prescribed coupling stays uncompiled until BA-D2. (2) The Steps 3-6 carrier pins are not named here (BA-U1..V3); `BAMainInd` as the end of the chain is BA-V2 (priced, not designed). (3) LSY Thm 2.2 for the BA initial data is UN-D1 (T2162) and BA-N1; the [RBSO1D] text is unavailable, so the G group (7800 lines central) has the widest spread. (4) `BAmUniqReal`, `BAmBoundary`, `BAImmLower` are owed pins of BA-D2, D6, D7: the audit should try them at `g → 0` and at a gap coupling (b.3, b.5).
