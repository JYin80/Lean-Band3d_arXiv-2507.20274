Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 06:53:26 UTC 2026

Notation: `N = sz.size n = (WL)^d`, `Δ = (t−s)/K ≤ N^{-CK}` (`gridStep`, `Walk.lean:67`), `u_j = s + jΔ`, `k = m` the loop length of the target, `η_u = etaT E u = (1−u) Im m_E`.

### (i) Exponent table  (`CK := 2m + 2D + 16`; `c_P = 2000 m²(m+1)² 16^{2m+4}`; `c_2 = m(2m+2) 16^{2m+3}`)
| # | quantity | value / bound | constraint | slack |
|---|---|---|---|---|
| 1 | `η_u`, `u ≤ t ≤ lemT(z_n)` | `η_u ≥ N^{-1+ε}/16 ≥ 1/(16N)` (`difRep_flow_bounds`, `DifREP1.lean:600`) | `N ≥ 1`, `ε > 0` | `N^{ε}` (flow.py: `η(lemT) ≥ N^{-0.9}/16` at all `n ≤ 6`) |
| 2 | `‖STeeM_u(M)_{σ,a,a'}‖`, `M` Hermitian | `≤ W^d m L^d η^{-(2m+2)} (W^{-d})^{2m+1} ≤ m N (16N)^{2m+2} = m 16^{2m+2} N^{2m+3}` (`STeeLoop` length `2(m−k+1)+2k = 2m+2`; `norm_gloop_le_of_le_abs_im` `Split.lean:757`; `Σ_{b,b'}‖SB‖ = L^d`, `W^dL^d = N`) | `hL: 3 ≤ L`, `Im z = η_u ≥ η`, `\|E\|<2`, `u<1` | `W^{-d(2m+1)} ≤ 1` dropped (`W ≥ N^𝔠`) |
| 3 | `V_k = Σ_{j<k} Δ‖STeeM_{u_j}(H_j)_{σ,a,a}‖`, `V_max` | `V_k ≤ KΔ·row 2 ≤ V_max := m 16^{2m+2} N^{2m+3}`; `t−s ≤ 1` | `V_{ℓ=L_n} := 2^{L_n}N^{-D} ≥ V_max`: `L_n = ⌈log₂(V_max N^D)⌉ ≤ (2m+3+D)log₂N + log₂(m16^{2m+2}) + 1` | none needed (`L_n` is defined by it) |
| 4 | shift sum `Σ_{j<K} Δ·eeShiftErrN(u_j,u_{j+1})` | `eeShiftErrN = W^d m L^d (2m+2) η_{u_{j+1}}^{-(2m+3)}(W^{-d})^{2m+1}Δ ≤ m(2m+2)N(16N)^{2m+3}Δ`; sum `≤ (KΔ)Δ·… ≤ c_2 N^{2m+4−CK}` | `≤ N^{-D}`: `CK ≥ 2m+D+4+log_N c_2` | at `CK=2m+2D+16`: `c_2 N^{-D-12}≤1`, slack `N^{D+12}/c_2` (`N ≥ 7` for `m=2`) |
| 5 | `Y` proxy `P` (`AzumaProxyN_YfieldsW`, `AzumaProxyN2.lean:1025`) | `S=Σ‖δ_a‖=1`, `C_2 = m(m+1)Nη^{-(m+2)} ≤ m(m+1)16^{m+2}N^{m+3}`, `P = 2000C_2²N⁸ ≤ c_P N^{2m+14}`; `E(Re Y_j)² ≤ Δ²P` | — | `c_P = 3.09e14 (m=2), 3.17e17 (m=3)` |
| 6 | `Y` tail (Doob `doob_L2_max`: `μ(x ≤ max\|M_k\|) ≤ E M_K²/x²`, no factor 4) | `x = x_Y/√2 = ¼N^{ε'−D/2}`; `E M_K² = Σ E(ΔM_j)² ≤ KΔ²P ≤ ΔP`; Re and Im: `≤ 32 c_P N^{2m+14+D−CK−2ε'}` | `≤ N^{-D}/2`: `CK > 2m+2D+14` (ε'-gain dropped, so `CK` is free of `ε'`) | at `CK=2m+2D+16` need `64c_P ≤ N^{2+2ε'}`; at `+15` need `N^{1+2ε'}`: slack one power of `N` |
| 7 | `Z` levels `V_ℓ = 2^ℓN^{-D}`, `ℓ ≤ L_n`; `y_ℓ = ½N^{ε'}(V_ℓ/2)^{1/2}` | switched proxy sum `≤ m(V_ℓ + N^{-D}) ≤ 2mV_ℓ` (row 4; `V_ℓ ≥ N^{-D}`); `x = y_ℓ/√2`: `x²/(2·2mV_ℓ) = N^{2ε'}/(64m)` | `(L_n+1)·4e^{-N^{2ε'}/(64m)} ≤ N^{-D}/2` ⇔ `N^{2ε'} ≥ 64m ln(8(L_n+1)N^D)` | threshold `N_0(m,D,ε')` below; no polynomial slack (`ε'>0` arbitrary) |
| 8 | level inclusion (e) | least `ℓ` with `V_k ≤ V_ℓ`: `V_ℓ = N^{-D}` if `ℓ=0`, `V_ℓ < 2V_k` else, so `V_ℓ/2 ≤ V_k + N^{-D}`, i.e. `N^{ε'}(V_k+N^{-D})^{1/2} ≥ 2y_ℓ`; `y_ℓ ≥ y_0 = x_Y` exactly; `\|Mart_k\|>2y_ℓ ≥ y_ℓ+x_Y` ⇒ `\|S^Z\|>y_ℓ` or `\|S^Y\|>x_Y` | `V_k ≤ V_max ≤ V_{L_n}`; `G^ℓ_j={V_{j+1}≤V_ℓ}` nested, `j<k` all in `G^ℓ` when `V_k ≤ V_ℓ` | factor 2 at `ℓ=0`; none lost in `x_Y/√2` (equality) |
| 9 | target 1 | `X_k = exp(rS_k − r²W_k/2)`, `E X_K ≤ 1`; switch `G'_j = G_j ∩ {S_i<x ∀i≤j}` (`ℱ_j`): `{∃k≤K, x≤S_k} ⊆ {x ≤ S'_K}`, `ΣG'v ≤ V`; Markov at `r=x/V`: `e^{-rx+r²V/2} = e^{-x²/(2V)}` | `0<V`, `0≤x`; `x=0`: event is `Ω` (k=0), bound `=1`; `K=0` trivial | exact (optimal `r`); four events `±Re,±Im` give factor 4 |
| 10 | target 2 | `Re/Im Σκ_bZ_b = √Δ linTr(A_j,X_{j+1})`, cond. mgf `= exp(r²Δ linTrVar(A_j)/2)` (`condExp_freeze`, `mgf_linTr_seqXmat`); `linTrVar ≤ Σ_c gvar‖D_c‖² ≤ k Re Σκκ̄ STeeM_{u_{j+1}}(H_j)` (`qvPropagatedN`, `QVN.lean:813`, `u_{j+1} ∈ [0,1)`, `\|E_n\|<2`, `H_j` Hermitian) | integrability: `Δ linTrVar ≤ c := Δ k(Σ\|κ\|)² sup‖STeeM_{u_{j+1}}‖` (row 2 at length `2k+2`, deterministic) | `s=t`: `Δ=0`, `Z=0`, both sides `1`; `0 ≤` proxy since `≥ linTrVar ≥ 0` |
| 11 | `CK` | `max(2m+D+4, 2m+2D+14)+ = 2m+2D+14+` (row 6 binds, `D>0`); chosen `2m+2D+16` | `CK` depends on `m,D` only; `K n ≥ N^{CK}` ⇒ `Δ ≤ N^{-CK}`, `KΔ=t−s ≤ 1` | `N^{2+2ε'}/(64c_P)` and `N^{D+12}/c_2` |
| 12 | order, `d` | `m → D → CK → K → ε' → n≫1` (pin: `∃CK` before `K`, `ε'` after; threshold of `∀ᶠn` depends on `K` only through `N^{CK} ≤ K n`) | no input has `3 ≤ d` (`difRep_flow_bounds`, `qvPropagatedN`, `norm_STeeM_shiftN_le`, `hermTestFunLoopN`, `AzumaProxyN_YfieldsW`, `pathH_isHermitian` all `∀ d`) | `3 ≤ d` only in target 4 (`stGridMart_of_tail`, `gridRepRemN_holds`) |

### (ii) One concrete nondegenerate instance
Data: `d=3`, `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `N_0 = 2097152`), `z0 = 1/2 + iN^{-4/5}`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `s≡0`, `t≡1/16 ≤ lemT(z0 n)`, `D=1`, `ε'=1/10`, `m ∈ {2,3}`, `CK = 2m+2D+16 ∈ {22, 24}`, `K_n = N_n^{CK}+1`.
Command: `python3 flow.py` (mpmath; `msc` = root of `m²+zm+1` with `Im>0`, `lemE = −2Re m/|m|`, `lemT = |m|²`)
```
n=0 N=2.10e+06 E=0.5000 lemT=0.9999909488 1/16<=lemT:True |E|<2:True eta(lemT)=8.76e-06>=N^-0.9/16=1.28e-07:True
n=1 N=5.50e+11 E=0.5000 lemT=0.9999999996 1/16<=lemT:True |E|<2:True eta(lemT)=4.05e-10>=N^-0.9/16=1.70e-12:True
n=2 N=8.12e+14 E=0.5000 lemT=1.0000000000 1/16<=lemT:True |E|<2:True eta(lemT)=1.18e-12>=N^-0.9/16=2.38e-15:True
n=3 N=1.44e+17 E=0.5000 lemT=1.0000000000 1/16<=lemT:True |E|<2:True eta(lemT)=1.88e-14>=N^-0.9/16=2.25e-17:True
n=4 N=8.00e+18 E=0.5000 lemT=1.0000000000 1/16<=lemT:True |E|<2:True eta(lemT)=7.54e-16>=N^-0.9/16=6.07e-19:True
n=5 N=2.13e+20 E=0.5000 lemT=1.0000000000 1/16<=lemT:True |E|<2:True eta(lemT)=5.46e-17>=N^-0.9/16=3.16e-20:True
n=6 N=3.42e+21 E=0.5000 lemT=1.0000000000 1/16<=lemT:True |E|<2:True eta(lemT)=5.93e-18>=N^-0.9/16=2.61e-21:True
```
Command: `python3 inst.py` (targets 1–2 at `n=0, E≡1/2, K≡4, j=0, k=3, κ=δ_0, G_j=univ, x=1`; `Re STeeM ≤ ‖STeeM‖ ≤ k N η^{-(2k+2)}(W^{-d})^{2k+1}` for `B`)
```
T2 hyps: |E|<2: True  0<=s<=t<1: True  j+1<=K: True  2<=k: True  Delta = 1/64  u_1 = 1/64  Delta>0: True
  u_0=0 eta=0.96825 (>= 1/(16 N0) = 2.98e-08: True)
  u_1=1/64 eta=0.95312 (>= 1/(16 N0) = 2.98e-08: True)
  u_2=1/32 eta=0.93799 (>= 1/(16 N0) = 2.98e-08: True)
  u_3=3/64 eta=0.92286 (>= 1/(16 N0) = 2.98e-08: True)
  u_4=1/16 eta=0.90773 (>= 1/(16 N0) = 2.98e-08: True)
T1 data [B from eta^-1 <= 1/eta_min (W^-d kept)]: B=10^-25.8  V=4B=10^-25.2  0<V:True  x=1>=0  K=4, G_j=univ, sum_(j<4) v_j<=4B=V  ->  bound exp(-x^2/(2V)) = 10^-3.44e+24
T1 data [B from crude (16N)^(2m+2)]: B=10^65.7  V=4B=10^66.3  0<V:True  x=1>=0  K=4, G_j=univ, sum_(j<4) v_j<=4B=V  ->  bound exp(-x^2/(2V)) = 10^-1.15e-67
T3 m=2 D=1 CK=22: K_n=N_n^CK+1 >= N_n^CK for n=0..6: True; K_n != 0: True
T3 m=3 D=1 CK=24: K_n=N_n^CK+1 >= N_n^CK for n=0..6: True; K_n != 0: True
```
Command: `python3 budgets.py` (budgets (4),(6),(7) of rows 4/6/7 with the worst-case crude bounds, `K_n = N_n^{CK}+1`, `Δ = (1/16)/K_n`, exact `Δ ≤ N^{-CK}` and `KΔ = 1/16` asserted; columns are `log10(budget/target)`)
```
c_P(m=2)=3.092e+14 c_P(m=3)=3.167e+17  c_2:=m(2m+2)16^(2m+3): m=2 3.221e+09 m=3 1.649e+12  V_max(m=2,N_0)=10^51.8
table m=2 D=1 eps'=1/10, CK=22 (shift/Y/Z = log10(budget/target), <=0 holds):
  n=0 log10N=6.32 L_n=193 log10K_n=139 shift=-72.7 Y=3.7 Z=9.5 all=False
  n=1 log10N=11.74 L_n=337 log10K_n=258 shift=-143.1 Y=-7.2 Z=14.4 all=False
  n=2 log10N=14.91 L_n=422 log10K_n=328 shift=-184.3 Y=-13.5 Z=15.2 all=False
  n=3 log10N=17.16 L_n=481 log10K_n=377 shift=-213.6 Y=-18.0 Z=11.6 all=False
  n=4 log10N=18.90 L_n=528 log10K_n=415 shift=-236.2 Y=-21.5 Z=2.1 all=False
  n=5 log10N=20.33 L_n=566 log10K_n=447 shift=-254.8 Y=-24.4 Z=-15.5 all=True
  n=6 log10N=21.53 L_n=598 log10K_n=473 shift=-270.4 Y=-26.8 Z=-43.5 all=True
m=2 D=1 eps'=1/10 CK=22: first sz0 index n=5 (N_n=10^20.33); real threshold N_0=10^19.13
m=2 D=1 eps'=1/2 CK=22: first sz0 index n=1 (N_n=10^11.74); real threshold N_0=10^8.15
m=2 D=3 eps'=1/10 CK=26: first sz0 index n=6 (N_n=10^21.53); real threshold N_0=10^21.52
m=2 D=3 eps'=1/2 CK=26: first sz0 index n=1 (N_n=10^11.74); real threshold N_0=10^8.15
m=3 D=1 eps'=1/10 CK=24: first sz0 index n=5 (N_n=10^20.33); real threshold N_0=10^20.12
m=3 D=1 eps'=1/2 CK=24: first sz0 index n=1 (N_n=10^11.74); real threshold N_0=10^9.65
m=3 D=3 eps'=1/10 CK=28: first sz0 index n=7 (N_n=10^22.58); real threshold N_0=10^22.49
m=3 D=3 eps'=1/2 CK=28: first sz0 index n=1 (N_n=10^11.74); real threshold N_0=10^9.65
```
Target-2 extreme-input test (lesson 25), `python3 qv.py` (`d=3, L=3, W=1, g=1/2, N=27`; `Σ_c gvar_c|D_c|²` is `≥ linTrVar(A), linTrVar((−I)A)`; `STeeM` and `STeeLoop` transcribed from `Step2Defs.lean:757`, `Step34Pins.lean:152`; first line validates the gradient by finite differences):
```
grad check |fd - tr(BX)| = 3.08851024729078e-11
H=0 E=0.5 u=0.3 sig=+- kappa=d00: VarRe=1.6584e+00 VarIm=0.0000e+00 sum_c gvar|D_c|^2=1.6584e+00 <= m*Re(ee)=8.8710e+00
H=0 E=0.5 u=0.3 sig=+- kappa=d01: VarRe=0.0000e+00 VarIm=0.0000e+00 sum_c gvar|D_c|^2=0.0000e+00 <= m*Re(ee)=0.0000e+00
H=0 E=0.5 u=0.3 sig=+- kappa=k=1: VarRe=4.4777e+01 VarIm=0.0000e+00 sum_c gvar|D_c|^2=4.4777e+01 <= m*Re(ee)=2.3952e+02
H=0 E=0.5 u=0.3 sig=++ kappa=d00: VarRe=8.4122e+00 VarIm=4.5880e-01 sum_c gvar|D_c|^2=8.8710e+00 <= m*Re(ee)=8.8710e+00
H=0 E=0.5 u=0.3 sig=++ kappa=d01: VarRe=0.0000e+00 VarIm=0.0000e+00 sum_c gvar|D_c|^2=0.0000e+00 <= m*Re(ee)=0.0000e+00
H=0 E=0.5 u=0.3 sig=++ kappa=k=1: VarRe=2.2713e+02 VarIm=1.2388e+01 sum_c gvar|D_c|^2=2.3952e+02 <= m*Re(ee)=2.3952e+02
H=0 E=0.5 u=0.3 sig=+-+ kappa=d00: VarRe=2.4969e-01 VarIm=9.5460e+00 sum_c gvar|D_c|^2=9.7957e+00 <= m*Re(ee)=3.5327e+01
H=0 E=0.5 u=0.3 sig=+-+ kappa=d01: VarRe=0.0000e+00 VarIm=0.0000e+00 sum_c gvar|D_c|^2=0.0000e+00 <= m*Re(ee)=0.0000e+00
32 cases (H in {0, random Hermitian}, (E,u) in {(.5,.3),(0,.9)}): LHS<=RHS: True | max LHS/RHS = 1.0 | |ee|<=m N eta^-(2m+2) (kappa=delta cases): True
```
Reading: every hypothesis of targets 1, 2 holds at the data above (`|E|<2`, `0≤s≤t<1`, `j+1≤K`, `2≤k`, `0<V`, `0≤x`, `v_j ≤ B`; `G_j=univ`). The target-1 instance with the crude `B` gives the bound `1−10^{-67}` (formally nondegenerate, uninformative); keeping `(W^{-d})^{2k+1}` gives `10^{-3.4e24}`. Targets 3 and 4 are eventual statements: for `ε'=1/10` all budgets hold from `sz0` index `n=5` (`m=2,3`, `D=1`) to `n=7` (`m=3, D=3`), i.e. `N_n ≈ 10^{20.3}–10^{22.6}` (threshold `N_0 ≈ 10^{19.1}–10^{22.5}`); `K_n ≥ 10^{139}` is forced by the pin `N^{CK} ≤ K`, not by a hypothesis of the proof. All flow hypotheses (`t ≤ lemT`, `|E|<2`, `η` lower bound) hold at every `n ≤ 6`, including the boundary `t = lemT(z0 n)` (flow.py) and `s=t` (`Δ=0`, `Mart ≡ 0`, event empty).

### Verdict
- Target 1 `azumaRandProxy_max`: PASS (row 9; no hypothesis set is empty; the maximal form needs no bound on `K`).
- Target 2 `difRepTail_condMGF_Z`: PASS (row 10; `k·Re(𝓔⊗𝓔)_{u_{j+1}}` proxy checked numerically, `LHS ≤ RHS` with equality at `σ=(+,+)`).
- Target 3 `gridRepTailN_holds` (every `d`, `CK = 2m+2D+16` free of `ε'`): PASS (rows 1–8, 11–12; binding constraint: row 6 `CK > 2m+2D+14`).
- Target 4 `stGridMart_holds`, `stGridMartAt_holds`: PASS (composition of merged `stGridMart_of_tail`, `stGridMartAt_of_parts2`, `gridRepRemN_holds` `C₀ = 2+9 = 11` with target 3 at `m=2`; `3 ≤ d` from those).
Overall: PASS.

## (b) Script output — Mon Oct  5 15:30:36 UTC 2026
Branch `t/T2180`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2180` (no `../RBM2D` there: RBM2D read by absolute `git -C`).
```
$ git log --format='%h %s' main..t/T2180 | cut -c1-110; git diff --stat main...t/T2180
a5491d5 T2180: DifREP2: exact source ranges in the copy docstrings
93503bc T2180: DifREP2: difRep2_* docstrings cite Amend 2
8b20b70 T2180: DifREP2: literal peeling form difRep2_peel_N with instance, docstring fixes
1ffdf13 T2180: registry: GridRepTailNAt and STGridMartAt proved (owed lines removed)
4ba62bc T2180: DifREP2 (ST2-13a): maximal Azuma bound with a random proxy, GridRepTailNAt at every m, STGridMa
main: 0818c49, merge-base: 4c52041
 RBM3D/Path/DifREP2.lean | 2623 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    2 -
 2 files changed, 2623 insertions(+), 2 deletions(-)
```

### b.1 Builds, axioms, registry
```
$ lake build RBM3D.Path.DifREP2 2>&1 | tail -2        # exit 0; no warning is reported for DifREP2.lean
✔ [3852/3852] Built RBM3D.Path.DifREP2 (13s)
Build completed successfully (3852 jobs).
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Path/DifREP2.lean
0
$ #print axioms of the 11 public declarations and 4 instances (tmp file `import RBM3D.Path.DifREP2`), grouped by script:
15 declarations, axioms [propext, Classical.choice, Quot.sound]:
  azumaRandProxy_max, difRepTail_condMGF_Z, gridRepTailN_holds, stGridMart_holds, stGridMartAt_holds, difRep2_norm_STeeM_le,
  difRep2_norm_STeeM_le_N, difRep2_eeShiftErrN_le, difRep2_eeShift_sum_le, difRep2_peel, difRep2_peel_N, DifREP2Inst.inst_peel_N,
  DifREP2Inst.inst_azumaRandProxy_max, DifREP2Inst.inst_peel, DifREP2Inst.inst_gridRepTailN
$ registry pre-check (tmp file: `import RBM3D`, `import RBM3D.Path.DifREP2`, `#assert_rbm_axioms`), after deleting the owed lines `GridRepTailNAt` (:121), `STGridMartAt` (:163):
exit=0; first line:  axiom audit: 5382 theorems, 1904 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
last line:  non-vacuity certificates: 0 of 113 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
(same check before the deletion: `0 of 115 premises`)
$ lake build   # root without the new import, before the registry edit: exit 0, `Build completed successfully (3986 jobs).`
$ lake build RBM3D   # root without the new import, after the registry edit: exit 1
error: RBM3D.lean:228:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:  [RBM.Ind.GridRepTailNAt]
$ lake build   # hub merge step 4 simulated: `import RBM3D.Path.DifREP2` after the last import of RBM3D.lean; the file was restored afterwards (md5 unchanged): exit 0, 0 `error` lines
Build completed successfully (3987 jobs).
```
### b.2 Target statements extracted by script (`extract.py`: text from `theorem NAME` to `:=`, whitespace squeezed; line numbers of the file)
```
L283 theorem azumaRandProxy_max : ∀ {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω') [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (ζ v : ℕ → Ω' → ℝ) (G : ℕ → Set Ω') (K : ℕ) (B V x : ℝ), (∀ j <
    K, StronglyMeasurable[ℱ (j + 1)] (ζ j)) → (∀ j < K, StronglyMeasurable[ℱ j] (v j)) → (∀ j < K, MeasurableSet[ℱ j] (G j)) → (∀ j < K, ∀ ω, 0 ≤ v j ω ∧ v j ω ≤ B) → (∀ j < K, ∀ r : ℝ, Integrable
    (fun ω => Real.exp (r * ζ j ω)) μ) → (∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * ζ j ω) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v j ω / 2)) → (∀ ω, ∑ j ∈ Finset.range K, (G j).indicator (v j) ω ≤
    V) → 0 < V → 0 ≤ x → μ.real {ω | ∃ k, k ≤ K ∧ x ≤ ∑ j ∈ Finset.range k, (G j).indicator (ζ j) ω} ≤ Real.exp (-x ^ 2 / (2 * V))
L1404 theorem difRepTail_condMGF_Z : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ), |E n| < 2 → 0 ≤ s n → s n ≤ t n → t n < 1 → j + 1 ≤ K n → ∀ {k : ℕ}, 2 ≤ k → ∀ (σ : Fin k → Bool) (κ :
    (Fin k → Zd d (sz.L n)) → ℂ) (r : ℝ), Integrable (fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re)) (pathP sz) ∧ Integrable (fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n
    j σ ω b).im)) (pathP sz) ∧ (pathP sz)[fun ω => Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).re) | filt sz j] ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * ((k : ℝ) * (∑ b :
    Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n), κ b * (starRingEnd ℂ) (κ b') * sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re)) / 2)) ∧ (pathP sz)[fun ω =>
    Real.exp (r * (∑ b, κ b * ZvecN sz E s t K n j σ ω b).im) | filt sz j] ≤ᵐ[pathP sz] (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * ((k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d
    (sz.L n), κ b * (starRingEnd ℂ) (κ b') * sz.STeeM n (E n) (gridTime s t K n (j + 1)) (pathH sz s t K n j ω) σ b b').re)) / 2))
L2180 theorem gridRepTailN_holds : ∀ d m : ℕ, 2 ≤ m → GridRepTailNAt d m
L2283 theorem stGridMart_holds : ∀ d : ℕ, 3 ≤ d → STGridMart d
L2288 theorem stGridMartAt_holds : ∀ d : ℕ, 3 ≤ d → STGridMartAt d 11
```
Conformance with the check file (tmp file: `import RBM3D.Path.DifREP2` + section 2 of `docs/tickets/checks/T2180-check.lean` + `example : XStmt := @x` for the five targets): `lake env lean` exit 0, 0 output lines.
Amend 2 pieces (public, prefix `difRep2_`, docstrings cite `docs/tickets/T2180-amend-2.md`), same script:
```
L1216 theorem difRep2_norm_STeeM_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {m : ℕ} (σ :
    Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) : ‖sz.STeeM n E u M σ a a'‖ ≤ ((sz.W n : ℝ) ^ d) * ((m : ℝ) * (((sz.L n : ℝ) ^ d) * ((etaT E u)⁻¹ ^ (2 * m + 2) * (((sz.W n : ℝ) ^ d)⁻¹) ^ (2 * m +
    1))))
L1277 theorem difRep2_norm_STeeM_le_N {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) (hη : 1 /
    (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT E u) {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) : ‖sz.STeeM n E u M σ a a'‖ ≤ (m : ℝ) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2
    * m + 2)
L1316 theorem difRep2_eeShiftErrN_le {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) {u u' : ℝ} (huu' : u ≤ u') (hη : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT E u') (m : ℕ) : eeShiftErrN d (sz.L n) (sz.W n) E m u u'
    ≤ (m : ℝ) * (2 * m + 2) * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ (2 * m + 3) * (u' - u)
L1353 theorem difRep2_eeShift_sum_le {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (hst : s n ≤ t n) (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1) (hη : ∀ j, j + 1 ≤ K n → 1 / (16 * ((sz.size n :
    ℕ) : ℝ)) ≤ etaT (E n) (gridTime s t K n (j + 1))) : ∑ j ∈ Finset.range (K n), gridStep s t K n * eeShiftErrN d (sz.L n) (sz.W n) (E n) m (gridTime s t K n j) (gridTime s t K n (j + 1)) ≤ ((m : ℝ)
    * (2 * m + 2) * 16 ^ (2 * m + 3) * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4)) * gridStep s t K n
L478 theorem difRep2_peel {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω') [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (ζ : ℕ → Ω' → ℂ) (a v : ℕ → Ω' → ℝ) (e : ℕ → ℝ) (K Lmax : ℕ) (c δ ρ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hζre : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).re)) (hζim : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).im)) (ha : ∀ j < K,
    StronglyMeasurable[ℱ j] (a j)) (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j)) (ha0 : ∀ j < K, ∀ ω, 0 ≤ a j ω) (hv0 : ∀ j < K, ∀ ω, 0 ≤ v j ω) (he0 : ∀ j < K, 0 ≤ e j) (hve : ∀ j < K, ∀ ω, v j ω ≤ c
    * (a j ω + e j)) (hesum : ∑ j ∈ Finset.range K, e j ≤ δ) (haL : ∀ ω, ∑ j ∈ Finset.range K, a j ω ≤ 2 ^ Lmax * δ) (hintRe : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * (ζ j ω).re)) μ)
    (hintIm : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * (ζ j ω).im)) μ) (hmgfRe : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).re) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v j ω / 2))
    (hmgfIm : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).im) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v j ω / 2)) : μ.real {ω | ∃ k, k ≤ K ∧ ρ * (∑ j ∈ Finset.range k, a j ω + δ) ^ (1 / 2 : ℝ)
    < ‖∑ j ∈ Finset.range k, ζ j ω‖} ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * c)))
L757 theorem difRep2_peel_N {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω') [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ') (ζ : ℕ → Ω' → ℂ) (a v : ℕ → Ω' → ℝ) (e : ℕ → ℝ) (K Lmax m : ℕ) (N D ε' :
    ℝ) (hm : 1 ≤ m) (hN : 1 ≤ N) (hζre : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).re)) (hζim : ∀ j < K, StronglyMeasurable[ℱ (j + 1)] (fun ω => (ζ j ω).im)) (ha : ∀ j < K,
    StronglyMeasurable[ℱ j] (a j)) (hv : ∀ j < K, StronglyMeasurable[ℱ j] (v j)) (ha0 : ∀ j < K, ∀ ω, 0 ≤ a j ω) (hv0 : ∀ j < K, ∀ ω, 0 ≤ v j ω) (he0 : ∀ j < K, 0 ≤ e j) (hve : ∀ j < K, ∀ ω, v j ω ≤
    (m : ℝ) * (a j ω + e j)) (hesum : ∑ j ∈ Finset.range K, e j ≤ N ^ (-D)) (haL : ∀ ω, ∑ j ∈ Finset.range K, a j ω ≤ 2 ^ Lmax * N ^ (-D)) (hintRe : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r
    * (ζ j ω).re)) μ) (hintIm : ∀ j < K, ∀ r : ℝ, Integrable (fun ω => Real.exp (r * (ζ j ω).im)) μ) (hmgfRe : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).re) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r
    ^ 2 * v j ω / 2)) (hmgfIm : ∀ j < K, ∀ r : ℝ, μ[fun ω => Real.exp (r * (ζ j ω).im) | ℱ j] ≤ᵐ[μ] fun ω => Real.exp (r ^ 2 * v j ω / 2)) : μ.real {ω | ∃ k, k ≤ K ∧ N ^ ε' * (∑ j ∈ Finset.range k, a
    j ω + N ^ (-D)) ^ (1 / 2 : ℝ) < ‖∑ j ∈ Finset.range k, ζ j ω‖} ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-N ^ (2 * ε') / (64 * (m : ℝ))))
```
### b.3 Compiled nonempty instances in the same file (namespace `RBM.Ind.DifREP2Inst`)
Data: `sz0` (d = 3, N_0 = 2097152), `s ≡ 0`, `t ≡ 1/16`, `K ≡ 4` (`gridStep_inst : gridStep sInst tInst (fun _ => 4) 0 = 1 / 64`), `n = 0`, `E ≡ 1/2` (`E12`), σ = (+,-,+), a = 0, κ = δ_0.
```
$ grep -nE '^example|^theorem inst_' RBM3D/Path/DifREP2.lean | cut -c1-150
2375:example := difRepTail_condMGF_Z sz0 E12 sInst tInst (fun _ => 4) 0 0 hE12 (hs0 0) (hst 0) ht0
2385:example := difRep2_norm_STeeM_le sz0 0 (E := E12 0) (u := 1 / 16) hE12 (by norm_num) herm0 σ3 a0 a0
2388:example := difRep2_norm_STeeM_le_N sz0 0 (E := E12 0) (u := 1 / 16) hE12 (by norm_num) herm0
2392:example := difRep2_eeShiftErrN_le sz0 0 (E12 0) (u := 0) (u' := 1 / 64) (by norm_num)
2397:example := difRep2_eeShift_sum_le sz0 E12 sInst tInst (fun _ => 4) 0 3 (hst 0)
2413:theorem inst_azumaRandProxy_max :
2440:example := inst_azumaRandProxy_max
2460:theorem inst_peel :
2501:example := inst_peel
2513:theorem inst_peel_N :
2572:example := inst_peel_N
2577:theorem inst_gridRepTailN (m : ℕ) (hm : 2 ≤ m) :
2600:example := inst_gridRepTailN 2 le_rfl
2601:example := inst_gridRepTailN 3 (by norm_num)
2604:example : STGridMart 3 := stGridMart_holds 3 (by norm_num)
2607:example : STGridMartAt 3 11 := stGridMartAt_holds 3 (by norm_num)
2611:example (hLWB : STLWB 3) : STOptL2 3 :=
2617:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hOpt : STOptL2 3)
$ sed -n '2375,2376p' RBM3D/Path/DifREP2.lean
example := difRepTail_condMGF_Z sz0 E12 sInst tInst (fun _ => 4) 0 0 hE12 (hs0 0) (hst 0) ht0
  (by norm_num) (k := 3) (by norm_num) σ3 κ0 1
```
Notes: `inst_azumaRandProxy_max` is target 1 on `(PathΩ sz0, pathP sz0, filt sz0)` with `ζ_j = Re Z_{j,0}`, `v_j` the proxy of target 2, `G_j = univ`, `K = 4`, `B = B3` (`B3_pos`), `V = 4 B3`, `x = 1`;
`inst_peel`/`inst_peel_N` apply `difRep2_peel`/`difRep2_peel_N` to `Z_{j,0}` (`δ3_pos`; `m = 3`, `N = N_0`, `D = 1`, `ε' = 1/10`); `inst_gridRepTailN` takes `D = 1`, `ε' = 1/10`, `K n = ⌈N_n^{CK}⌉₊ + 1`;
`STLWB`, `STNewKLK`, `STLWT`, `STEMn2Exp`, `STOptL2`, `STLocalAvgOfL2` stay hypotheses of the two chain examples (other gates' pins, CLAUDE.md §4 step 2).
### b.4 Name-clash grep and ports
```
$ grep -rn NAME RBM3D RBM3D.lean --include='*.lean' | grep -v 'RBM3D/Path/DifREP2.lean' | wc -l    (worktree; also `git grep` on main 0818c49: 0)
azumaRandProxy_max:0 difRepTail_condMGF_Z:0 gridRepTailN_holds:0 stGridMart_holds:0 stGridMartAt_holds:0 difRep2_norm_STeeM_le:0 difRep2_norm_STeeM_le_N:0
difRep2_eeShiftErrN_le:0 difRep2_eeShift_sum_le:0 difRep2_peel:0 difRep2_peel_N:0 DifREP2Inst:0 difRepTail_:0
$ cd /Users/junyin/Lean_proof && grep -rn -i 'supermartingale\|random.proxy\|Freedman' RBM1D RBM2D --include='*.lean' | grep -v /.lake/ | wc -l   -> 0   (no random-proxy Azuma bound in the sister projects)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h   -> 9e0f275   (the ports cite c9a24cf; checked there: Path/Markov.lean:417 mgf_linTr_seqXmat, :564 condMGF_le; Induction/AzumaProxyN.lean:198-247)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/Markov.lean RBM2D/Induction/AzumaProxyN.lean
 RBM2D/Induction/AzumaProxyN.lean | 1140 +++-----    RBM2D/Path/Markov.lean | 151 +----    2 files changed, 96 insertions(+), 1195 deletions(-)
```
Copies (private, prefix `difRepTail_`; sources are the merged RBM3D files, RBM2D lines for provenance): `Induction/AzumaProxyN.lean:122-232` (`43ab861`; RBM2D `AzumaProxyN:200-260`, `c9a24cf`),
`Path/Markov.lean:263-305, 319-321, 393-435, 572-604` (`58bedae`; RBM2D `Markov:417-620`, `c9a24cf`), `Induction/NQGood1.lean` `nqGood1_sum_sum_norm_SB` (`691566a`). RBM1D (`de0de42`): no counterpart, nothing ported.
### Narrative
1. Layout of `DifREP2.lean`: §1-§1c model-free (lintegral step `difRepTail_lintegral_mul_le`, one step `difRepTail_step_cond`, induction `difRepTail_lintegral_X_le`, target 1, `difRepTail_max_abs`, `difRepTail_switch_sum`,
   `difRep2_peel`, `difRep2_peel_N`, `difRepTail_doob_tail`); §2-§5 copies and the random-variance conditional moment; §6 crude bounds; §7 target 2; §8-§11 `Z`/`Y` parts, `difRepTail_core`, asymptotics;
   §12 target 3; §13 target 4; §14 instances.
2. Target 1: `X_k = exp(r S_k - r²/2 W_k)` has `∫⁻ ofReal X_k ≤ 1` by induction with `difRepTail_lintegral_mul_le` (truncation `min X n`, `condExp_mul_of_stronglyMeasurable_left`, `lintegral_iSup'`), so no
   integrability of products and no bound on `K` are needed; the pinned hypothesis `v_j ≤ B` is not used by the proof.  The maximum is handled by the second switch `G'_j = G_j ∩ {S_i < x ∀ i ≤ j}`
   (least `k₀` with `x ≤ S_{k₀}`: `S'_K = S_{k₀}`), then Markov at `r = x/V`; `x = 0` is trivial.
3. Target 2: `Σ_b κ_b Z_b = stepZCN` of the loop family with kernel `(·, a) ↦ κ_a`; `A_j` is `F_j`-measurable by `stepDecompCN`; the conditional mgf is `exp(linTrVar(A_j)(r√Δ)²/2)` by the copied
   `condExp_freeze` argument (`difRepTail_condExp_exp`), then `linTrVar ≤ k Re Σ κ κ̄ 𝓔⊗𝓔` (`qvPropagatedN`).  Integrability: `stepDecompCN_Z_subG` at `E = univ` with the deterministic bound of
   `difRep2_norm_STeeM_le`, then `HasCondSubgaussianMGF.integrable_exp_mul`.
4. Target 3, `CK = 2m + 2D + 16` (literal): `difRepTail_core` proves the pin at one `n` from three numerical budgets (shift sum, `Y`, `Z`) and `η_{u_j} ≥ 1/(16 N)` (`difRep_flow_bounds`); pathwise `Mart = S^Z + S^Y`;
   `Z` by `difRep2_peel` with `ρ = N^{ε'}/2`; `Y` by `difRepTail_Y_tail` (`AzumaProxyN_YfieldsW` at `κ = δ_a`, `τ ≡ K n`; Doob via `doob_L2_max`, `martingale_sq_eq_sum`).  The assembly makes the budgets hold eventually:
   `N ≥ max(c₂, 32 c_P)` and `difRepTail_eventually_Z` (polynomially many levels `L = ⌈m N (16N)^{2m+2} N^D⌉₊` against `e^{-N^{2ε'}/(64m)}`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`).
5. Differences from the ticket's route (no statement changes): (i) `x_Y = (N^{ε'}/2) N^{-D/2}`, `Y` budget `32 c_P ≤ N²` (ε'-gain dropped; (a) rows 6, 8 use another split); (ii) the number of levels is polynomial, not `O(log N)`;
   (iii) `difRep2_peel` has separate threshold increments `a_j`, slack `e_j`, constant `c`; `difRep2_peel_N` is the amend's form (`ρ = N^{ε'}`, `δ = N^{-D}`, exponent `64 m`; the proof gives `16 m`);
   (iv) the crude-bound and peeling instances use `E ≡ 1/2` (`eta12`: `η_u ≥ 1/2` for `u ≤ 1/16`), target 3 uses the flow data.
6. `3 ≤ d` only in target 4 (`stGridMart_of_tail`, `gridRepRemN_holds`); targets 1-3 and the `difRep2_*` pieces are for every `d` (`gridRepTailN_holds : ∀ d m` compiles).  Section (a) stands, no (a′).
7. §29 checklist: (1) `0 ≤ s n ≤ t n < 1`, `j + 1 ≤ K n` are hypotheses of target 2; (5) the union over `k ≤ K` is inside `μ` in target 1; (6) `N → ∞` is `hz.1.2.2.1 : sz.SizeTendsto` (from `STFlow`), never a premise;
   (7) `CK` is the literal `2m + 2D + 16`, free of `ε'`, `κ`, `ε`.  Registry: only the two owed lines were deleted (pre-check exit 0); `STGridRepN` (:120) and `GridRepWTailNAt` (:122) stay.

## (c) Verified Mathlib names (all compiled; Mathlib at the project's `v4.34.0`)
- `MeasureTheory`: `condExp_mul_of_stronglyMeasurable_left`, `condExp_add`, `condExp_of_stronglyMeasurable`, `condExp_zero`, `integral_condExp`, `integrable_condExp`, `Integrable.bdd_mul`, `Integrable.of_bound`,
  `ofReal_integral_eq_lintegral_ofReal`, `lintegral_iSup'`, `mul_meas_ge_le_lintegral`, `ofReal_measureReal`, `measureReal_mono`, `measureReal_union_le`, `measureReal_biUnion_finset_le`, `measureReal_le_one`
- measurability: `StronglyMeasurable.mono`, `.indicator`, `.const_mul`, `Finset.stronglyMeasurable_fun_sum`, `Continuous.comp_stronglyMeasurable`, `measurableSet_le`, `measurableSet_lt`, `Finset.measurableSet_biInter`
- martingale / `L^p`: `martingale_of_condExp_sub_eq_zero_nat`, `memLp_finsetSum`, `memLp_two_iff_integrable_sq`, `memLp_one_iff_integrable`, `MemLp.mono_exponent`, `MemLp.zero'`;  `ProbabilityTheory.HasCondSubgaussianMGF.integrable_exp_mul`
- analysis: `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_rpow_atTop`, `Real.rpow_add` (explicit exponents), `Real.rpow_natCast`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.one_le_rpow`, `Real.sqrt_eq_rpow`,
  `inv_anti₀`, `Nat.lt_two_pow_self`, `Nat.ceil_lt_add_one`, `Complex.norm_le_sqrt_two_mul_max`, `Finset.le_sup'_iff`
- verified absent or changed (tool log): `MeasureTheory.Integrable.bdd_mul'`, `MeasureTheory.Integrable.condExp` (unknown constants); `one_div_le_one_div_iff`, `mul_le_mul_left'` (unknown identifiers in this scope); `StronglyMeasurable.div_const` (no such field);
  `Finset.stronglyMeasurable_sum` is the `∑ i ∈ s, f i` form (the `fun ω => ∑` form is `Finset.stronglyMeasurable_fun_sum`); deprecated here: `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`), `push_neg` (use `push Not`), `if_pos`/`if_neg`;
  `import Mathlib` fails in the worktree (no root olean), import the modules.

## (d) Open issues and paper-delta candidates
Open: (1) `STGridRepN` stays owed (clause (iv), ST2-13b); `GridRepTailNAt` remains a hypothesis of the merged `stGridRepNAt_of_parts`, `stGridRepN_of_tails`, `stGridMartAt_of_parts2`, `stGridMart_of_tail` (`DifREP1.lean:1243-1305`).
(2) Hub: add `import RBM3D.Path.DifREP2` after the last `import` of `RBM3D.lean` at merge (b.1: the root build fails after the registry edit without it, exit 0 with it).
(3) Dispatcher: the comment of `STOptL2` in `Test/Axioms.lean` (`:127` on main, `:126` on the branch; "stays owed through `STLWB` and `STGridMart`") is stale once `STGridMart` is proved for `3 ≤ d`; left unchanged as the ticket says.
(4) For ST2-13b the interface is `azumaRandProxy_max` (any `K`), `difRepTail_condMGF_Z` (general `κ`), `difRep2_peel` / `difRep2_peel_N` (one time grid, `ζ_j` adapted, proxy `v_j ≤ c (a_j + e_j)`), `difRepMartN_succ_sub`; the `k`-dependent
kernel `𝒰_{u_j,u_k}` of the weighted tail is not covered by the peeling lemma.  (5) Process: RBM2D HEAD is `9e0f275`, not `c9a24cf`; the cited lines were checked at `c9a24cf` (b.4).  (6) `Test/Axioms.lean` and `RBM3D.lean` changed on main since the base (`git diff --stat 4c52041 main`: 21 and 9 lines); `git merge-tree --write-tree main t/T2180` (main `0818c49`): one line, tree `f1c33f9`, no conflict.
Paper-delta candidates (tags `T2180a`...; the dispatcher numbers them):
- T2180a: BDG `(aaswtghh)` + Markov replaced by a maximal exponential bound with the predictable proxy, uniform in `K` (D90): `μ(max ≥ x) ≤ e^{-x²/(2V)}`; levels `V_ℓ = 2^ℓ N^{-D}`, union over `ℓ`, factor `4` for `±Re, ±Im`.
- T2180b: the first-chaos proxy is `k Re(𝓔⊗𝓔)` at `u_{j+1}` (`ZvecN` differentiates `𝓛_{u_{j+1}}` at `H_j`), moved to the paper's `u_j` at cost `m(2m+2)16^{2m+3} N^{2m+4} Δ` (`difRep2_eeShift_sum_le`), absorbed in the `N^{-D}` floor.
- T2180c: the second-order part `Y` by Doob's `L²` inequality inside the same `N^{-D}` floor; the `L⁴` field of `AzumaProxyN_YfieldsW` is used only for square integrability.
- T2180d: `CK = 2m + 2D + 16` depends on `m, D` only (free of `ε'`); the tail `GridRepTailNAt d m` holds for every `d`, `3 ≤ d` only in the assembly.
- T2180e: `STGridMart d` and `STGridMartAt d 11` unconditional for `3 ≤ d`; `C₀ = 2 + 9 = 11` explicit (paper `C₀(d)`).  T2180f (Lean device): `Mart = Σ ZvecN + Σ YvecN`, `YvecN := martIncN - ZvecN` by definition.
