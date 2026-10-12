Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 04:12:12 UTC 2026

Target: `baTwistGridWTail_holds d : BATwistGridWTail d`, every `d` (`BA/TwistGrid2.lean:248`). Notation: `N = sz.size n = (WL)^d`, `Δ = (t-s)/K`, `δ = N^{-D}/2`, `η_u = Im z_u = (1-u) Im m_F`, `S` = row-sum bound of the weights, `P = ⌈N^{C'}⌉`, `ρ = N^{ε'}/4` (the band's `ρ`: the pathwise bound is `ρ(·)^{1/2} + 2ρ√δ`, `DifREP3:1457-1480`, against the pin's `N^{ε'} = 4ρ`). Scripts (mathematics only): scratchpad `T2439/{conj,var,budget}.py`.

### (i) Exponent table
| # | quantity | value | constraint / merged source | slack |
|---|---|---|---|---|
| 1 | labels, union | `#Zd = L^d ≤ N` (`W ≥ 1`); union over `p ≤ P`, `a'` ∈ `Zd`: `(P+1)L^d ≤ 3N^{C'+1}`; `i = (σ,a,c₁,c₂)` is outside the probability (the pin's `∀ i`) | one index (band: `N^m`) | at `C' = D+14`: `3N^{D+15}` |
| 2 | `η_u⁻¹`, `u ≤ t ≤ T0` | `η_u ≥ (κ/2)N^{-1+ε}` (`GreenCond2_eta_lower`, `BA/GreenCond2:321`); so `η⁻¹ ≤ (2/κ)N^{1-ε} ≤ 16N` iff `N^ε ≥ 1/(8κ)` | eventual: `BAFlow.1 = Admissible ⊇ SizeTendsto` (`Defs/Sizes:173-178`); at `κ = 1/2` all `N ≥ 1` | datum `1/η_{T0} = 3.2669` vs `16N = 3.4e7` (budget.py) |
| 3 | `(1-u)⁻¹ ≤ (1-T0)⁻¹` on `[s,t]` | `1-T0 ≥ Im z/2 ≥ N^{-1+ε}/2` (`EMn2BA_one_sub_T0`, `BA/EMn2BA:111`; `T0 < 1`: `:106`; `Im z ≥ N^{-1+ε}`: `BAdom`, `BA/MFixedPoint:435`), so `(1-u)⁻¹ ≤ 2N^{1-ε} ≤ 16N`, **no eventual condition** | `S := 16N`: `Σ_b|Ũ_{u_j,v}(a',b)| = ‖row‖ ≤ (1-u_j)/(1-v) ≤ (1-v)⁻¹` (`EKPins_norm_uKer_le`, `BA/EKPins:185`, `u_j ≤ v < 1`) | `(1-T0)⁻¹ = 3.2652` vs `2N^{0.9} = 9.8e5` (n=0) |
| 4 | kernel transfer | `‖Ũ_{w,v}-1‖ ≤ (v-w)(1-v)⁻¹` (`BAuKer_eq_one_add :62`, `EKPins_norm_Q_le :151`, `EKPins_norm_Theta_le :161`); `Ũ_{v,w}Ũ_{u,v} = Ũ_{u,w}` (`BAuKer_comp`, `BA/TwistGrid:188`); `‖Ũ_{u,v}-Ũ_{u,w}‖ = ‖(Ũ_{w,v}-1)Ũ_{u,w}‖ ≤ 256N²(v-w)` | `0 ≤ w,v < 1` | conj.py: bounds attained (ratio 1.0000), not exceeded |
| 5 | crude `‖twEEM(b,b')‖` | `|twDerM| ≤ 2η⁻³` (two terms of (D.2), `W^{-2d}` against `W^{2d}` index pairs); `S^{(B)}(0) = I` (`baFM.S = 1`, `BA/FlowPins:327`) so `Σ_{xy}W^{-d}S_{[x][y]} = N`: `‖twEEM‖ ≤ 4Nη⁻⁶ ≤ c'N⁷`, `c' = 4·16⁶ = 6.71e7`; `V_Q := S²c'N⁷ = c_V N⁹`, `c_V = 4·16⁸ = 1.72e10` | `a_j := Δ‖twEEUM_{u_j,v_p}‖ ≤ ΔV_Q`, `KΔ = t-s ≤ 1` | var.py: `max|D|/(2η⁻³) = 0.061` |
| 6 | `C₂` of `Φ_b(M) = L̃_{u_{j+1}}(g₀Ψ+M)` | `C₂ = 6Nη⁻⁴ ≤ 6·16⁴N⁵` (Leibniz `2+2+2` terms; the entrywise count gives `6η⁻⁴`, looser kept = band `m(m+1)N(16N)^{m+2}` at `m = 2`); `P_Y = 2000(S C₂)²N⁸ = c_P N²⁰`, `c_P = 2000(6·16⁵)² = 7.92e16` | `AzumaProxyN_YfieldsW` hypothesis `hP` (`AzumaProxyN2:1025`), `stepDecompCN_Y_sq` (`StepDecompN:965`) | var.py: `max|d²L[y,y]|/(6Nη⁻⁴‖y‖²) = 0.0038` |
| 7 | shift `u_{j+1} → u_j` | `|twEEM_{u'}-twEEM_u| ≤ 24N|z'-z|η⁻⁷`, `|z'-z| = (u'-u)|m_F| ≤ (u'-u)` (`‖m_F‖ ≤ 1`: `BAm_norm_le_one`, `BA/Ward:136`, at `BAflow_real`, `BA/GreenSchur:59`); `Σ_j e_j ≤ S²·24·16⁷N⁸Δ = 256·c_sh N¹⁰Δ`, `c_sh = 24·16⁷ = 6.44e9` | `Σe ≤ δ` ⇔ `512c_sh ≤ N^{CK-10-D}` | `‖m_F‖ = 0.999493` (n=0), `1.000000` (n ≥ 1) |
| 8 | **`C'`** (coarse grid, indep. of `K`) | **`D + 14`** (band `4m+D+6`, `m = 2`) | proxy transfer `c₃N¹⁰/P ≤ N^{-D}/4`, `c₃ = 8192c' = 2³⁹`: `N^{C'-10-D} ≥ 4c₃ = 2.20e12`; kernel transfer `A = 16N/P ≤ 1/4`, `A V_Q ≤ δ/4`: `N^{C'-10-D} ≥ 128c_V = 2.20e12` | exponent `4`, `N ≥ 1218`; (`C' = D+11` closes only for `N ≥ 2.2e12`) |
| 9 | **`CK(D)`** | **`3D + 40`** (T2428 row 8; band `9m+3D+22`) | `Δ ≤ N^{-CK}`. `Y`: `(P+1)·N·4ΔP_Y/(ρ√δ)² ≤ N^{-D}/4` ⇔ `1536c_P ≤ N^{CK-C'-2D-21+2ε'}`; shift: row 7 | `Y`: exponent `5.2` (`ε' = 1/10`; `≥ 5` for all `ε' > 0`), `N ≥ 7286`; shift: exponent `32` |
| 10 | `Z` budget | levels `L = ⌈V_Q/δ⌉ ≤ 2c_V N^{9+D}+1`; `(P+1)N(L+1)·4·exp(-ρ²/(16c)) ≤ N^{-D}/2`, `ρ²/(16c) = N^{2ε'}/(256c)`; proxy factor `c = 1` (part (ii)); `difRep2_peel` (`DifREP2:478`) takes real `c > 0` | polynomial `N^{2D+24}` against stretched exponential: eventual for all `D, ε' > 0` | binding; thresholds in (ii) |
| 11 | `ε'`, `D`, exponent `1/2` | free `> 0`; `ρ ≥ 1/4` for every `ε' > 0` | — | — |
| 12 | `d`, `E` | no `3 ≤ d`; no `|E| < 2` (only `Im z_u > 0` enters `‖G‖ ≤ η⁻¹`) | the cited lemmas carry only `BAReal`/`BAFlow`; all `3 ≤ d` in `EKPins`, `EMn2BA`, `FlowPins` are inside pin definitions | `grep` in (iv) |

### (ii) One concrete nondegenerate instance; conjugation and variance identities
`d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))⁵`, `lam = (2(n+1))⁻⁶`, `Defs/Sizes:260`), `zSeq`, `flow_sz0` at `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `s ≡ 1/2 < t ≡ 2/3 ≤ T0` (`t0_sz0`, `BA/FlowPins:1227`; `T0 = 0.6937..0.6944`), `D = 1`, `ε' = 1/10`, `C' = 15`, `CK = 43`, `K_n = ⌈N_n^{43}⌉ + 1`. No external hypothesis occurs (the pin is eventual in `n`; `BAFlow` is discharged by `flow_sz0`), so the limit computation owed is the budget limit of rows 8-10, evaluated below at `n = 0..59`.
```
$ python3 budget.py | grep -E '^constants|n= 0 |n= 7 |first n|^C.=|shift:|f2:|f1:|Y:'      (budget.py: sz0 datum by Fourier modes of Ψ^B; logs of the five budgets)
constants: c' = 4*16^6 = 67108864 ; c_V = 4*16^8 = 17179869184 ; C2 = 6*16^4 N^5 = 393216 N^5 ; c_P = 2000*(16*C2c)^2 = 7.9165e+16 ; c3 = 2^39 = 5.4976e+11 (1) ; c_sh = 24*16^7 = 6442450944
  n= 0 N=2.0972e+06 Im m=0.832488 Im z=0.367512 T0=0.693740 (1-T0)^-1=3.2652 2N^(1-eps)=9.784e+05 |mF|=0.999493 eta_T0^-1=3.2669 16N=3.355e+07 | Im z/2<=1-T0:True bound:True dom+|mF|<=1:True
  n= 7 N=3.7779e+22 Im m=0.833333 Im z=0.366667 T0=0.694444 (1-T0)^-1=3.2727 2N^(1-eps)=4.174e+20 |mF|=1.000000 eta_T0^-1=3.2727 16N=6.045e+23 | Im z/2<=1-T0:True bound:True dom+|mF|<=1:True
C'=15 CK=43 proxy factor c=1: first n<60 with all five budgets true: n*=16, N*=2.9492e+28
C'=15 CK=43 proxy factor c=4: first n<60 with all five budgets true: n*=25, N*=6.1823e+31
C'=15 CK=43:
    shift: 512 c_sh <= N^(CK-10-D): const=3.2985e+12, exponent=32, N >= 2.461
    f2: 4 c3 <= N^(C'-10-D): const=2.1990e+12, exponent=4, N >= 1218
    f1: 128 c_V <= N^(C'-10-D): const=2.1990e+12, exponent=4, N >= 1218
    Y: 1536 c_P <= N^(CK-C'-2D-21+2eps'): const=1.2160e+20, exponent=5.2, N >= 7286
$ python3 -c "...n=16..."      ->  n*=16  N=2.9492e+28  log10 K=ceil(N^43)+1 = 1224.2  ; P+1<=3N^15: log10 = 427.5
```
Only the `Z` budget (stretched exponential `exp(-N^{2ε'}/(256c))` against `N^{2D+24}`) is binding: at `n = 0..15` the other four hold (verified by `budget.budgets` for `n = 0..15`: `shift, f2, f1, Y` true, `Z` false; `n = 16, 17`: all true); `K_{n*}` has `log10 = 1224.2`: it is the pin's own hypothesis `N^{CK} ≤ K n`, passed as a function and never evaluated (as in `TwistGrid2:333-343`). `c = 4` (a per-coordinate Lean route) closes from `n = 25`.

**Conjugation identity** `Ũ^{(σ̄)} = conj Ũ^{(σ)}`, `σ̄ = (!σ₀,!σ₁)`, `Ũ = (1-sM)Θ_t`, `0 ≤ s,t < 1` real (needed by `twEEUM = Σ_{b,b'}κ_bκ̄_{b'}twEEM(b,b')` with `κ = Ũ_{u_j,v_p}(a',·)`):
- `(+,+)↔(-,-)`: `BATheta_conj` (`BA/KBase:362`) and `M^{(--)} = conj M^{(++)}` entrywise (inline in its proof: `M(-) = M^*`, `M^{(B)}` symmetric, `BAMB_symm`): private lemma, then `(1-sM)` conjugates too.
- `(+,-)↔(-,+)`: `BAMss_pm_eq`, `BAMss_mp_eq` (`BA/KKernel:84,93`): both `= Matrix.map BAK ofReal`, so `M^{(+-)} = M^{(-+)}` is real, `Θ^{(+-)} = Θ^{(-+)}` (`BATheta_pm_eq :107`, `BATheta_swap :350`) is the inverse of a real matrix, hence real; `Ũ^{(σ̄)} = Ũ^{(σ)} = conj Ũ^{(σ)}`.
```
$ python3 conj.py | grep -E '^d=|max \|U|\|\|M\|\|'      (self-consistent m from m = L^-d tr(gΨ-E-m)^-1, torus L=3, g=0.05, E=0.3, s=.3, t=.55, all four σ)
d=1 L=3 n=3 g=0.05 E=0.3 Im m=0.986219 resid=2.0e-16 MB symmetric: 7.8e-18
   max |U^(sbar)-conj U^(s)| over the 4 pairs = 8.73e-19;  semigroup residual = 2.22e-16
d=3 L=3 n=27 g=0.05 E=0.3 Im m=0.981413 resid=6.0e-16 MB symmetric: 5.0e-17
   max |U^(sbar)-conj U^(s)| over the 4 pairs = 5.64e-18;  semigroup residual = 4.66e-15
   ||M||_inf max = 1.000000 (<=1);  ||U_(s,t)||/((1-s)/(1-t)) max = 1.0000 (<=1);  ||U_(t,w)-1||/(|w-t|/(1-w)) max = 1.0000 (<=1)
```
(`U^{(++)}` is genuinely complex: `max|Im U| = 3.1e-2`; the mixed pairs are real, `1.5e-17`; same output at `d = 2`.)

**Weighted variance identity** (constant `1`): for `f = Σ_b Ũ^{(σ)}(a,b)L̃_b`, with the Gaussian law of `pathH` (`E|X_xy|² = S_xy = W^{-d}1[[x]=[y]]`, `gvarF`, `Gauss/FineModel:89`: `S_ii` on the diagonal, `S_ij/2` per real coordinate `E_ij+E_ji`, `iE_ij-iE_ji`), `Σ_c gvar_c|df(X_c)|² = Σ_{xy}S_xy|Σ_bŨ(a,b)∂_{xy}L̃_b|² = Re twEEUM(a)` exactly: `df` is complex-linear in the Hermitian direction, `|f_ij+f_ji|²+|f_ij-f_ji|² = 2(|f_ij|²+|f_ji|²)`, and `linTrVar` of `A` and `-iA` are each `≤ Σ_c gvar_c|tr(AX_c)|²` (`Re²,Im² ≤ |·|²`), so the proxy factor is `c = 1` (the band's factor `m` came from `m` gradient terms; the two terms of (D.2) sit inside `twDerM`).
```
$ python3 var.py | grep -E '^toy|\(c1,c2\)=\(0,1\)|^max'      (d=1, L=3, W=2, N=6, random Hermitian H, u=.43, all 4 σ x 3 (c1,c2); finite differences h=1e-5)
toy d=1 L=3 W=2 N=6  u=0.43  eta=Im z_u=0.5621  eta^-1=1.779  16N=96
  sigma=++ (c1,c2)=(0,1):  sum_c gvar|df|^2=6.44883404e-02  Re twEEUM=6.44883404e-02  ratio=1.000000000
  sigma=+- (c1,c2)=(0,1):  sum_c gvar|df|^2=9.23506778e-02  Re twEEUM=9.23506778e-02  ratio=1.000000000
  sigma=-+ (c1,c2)=(0,1):  sum_c gvar|df|^2=7.16607648e-02  Re twEEUM=7.16607648e-02  ratio=1.000000000
  sigma=-- (c1,c2)=(0,1):  sum_c gvar|df|^2=9.46248434e-02  Re twEEUM=9.46248434e-02  ratio=1.000000000
max rel err (D.2 vs finite difference)          : 1.05e-09
max rel err (variance identity, constant 1)     : 3.24e-10  (includes |twEEUM(sigma-bar weights) - twEEUM(conj weights)|)
max |Im twEEUM| / Re twEEUM                      : 1.51e-17
max |U^(sbar) - conj U^(s)| at the weights used  : 8.73e-19
```

### (iii) Reuse table (`Path/DifREP3.lean`, 2567 lines; section line counts by `awk`)
| band | lines | twist |
|---|---|---|
| §3 kernel algebra `:187-717` (531) | `uKerQ`, `zeroModeSet`, `tensorKer`, `difRep3_sum_prod_sub_prod`, `difRep3_norm_UN_sub_le`, `difRep3_UN_transfer :163` (`UN`, `Q`): **dropped**; replaced by row 3-4 facts (imported `EKPins`, `BAuKer_comp`) and the private conjugation lemma | twins of `difRep3_STeeUQM_eq :607`, `_norm_STeeUQM_le :627`, `_sub_le :645`: new, one slot |
| §4 grid `:718-835` (118) | copy (generic in `s,t,K,n`); `difRep3_card_label_le :767` at one label | copy |
| §5 `:836-1087` (252) | `difRep3_doob_tail :859`, `memLp_two_of_pow4 :845`: copy; `difRep3_Y_tail :959`: copy with `AzumaProxyN_YfieldsW :1025` (loop: `loopFamN`, `hermTestFunLoopN`) replaced by a `Φ`-generic twin through public `stepDecompCN_Y_sq`, `integrable_stepZCN_re/im_of_hermTestFun` | new moment twin (`AzumaProxyN2:385-538` private) |
| §6 `:1088-1429` (342) | defs `kap, zeta, yinc, aSeq, qv, vSeq, eSeq` at one slot; `difRep3_zeta_mgf :1354` from the twisted `κ`-weighted `condMGF_Z` (twin of `difRepTail_condMGF_Z`, `DifREP2:1404`, loops) and the proxy shift (twin of `difRep2_eeShift_sum_le :1353`), crude bound (twin of `difRep2_norm_STeeM_le_N :1277`) | **copy** with stem `TwistGridWTail_`: `RBM3D/BA/TwistGridTail.lean` is not on `main` (`git ls-tree main` count 0); import `difRep2_peel :478`, `stepDecompCN :844` |
| §7 `:1430-1911` (482) | `difRep3_pathwise :1457`, `difRep3_core :1678`: rewrite at one slot (no `Q`, no `(1+ε₀)^{m-1}`) | rewrite |
| §8 budgets `:1912-2172` (261) | pure arithmetic with `m`-exponents | recomputed constants of rows 5-10 |
| §9 `:2173-2332` (160) | `difRep3_eventually_Z :2193`, `rpow_CK`, `tail_at :2245` | copy, `m → c` |
| §10 `:2333-2390` (58) | `gridRepWTailQN_holds :2343` → target 1; `stGridRepN_holds` (`3 ≤ d`) dropped | |
| §11 `:2391-2567` | dropped | instance pattern `TwistGrid2:284-343` |

(iv) `3 ≤ d` occurs in no cited lemma: `grep -c '3 ≤ d'` is 0 for `KBase`, `KKernel`, `GreenCond2`; the hits in `EKPins` (`:98-135, 241-262`), `EMn2BA` (`:452, 458, 633+`), `FlowPins` (`:174-218, 411`) are pin definitions, not the lemmas of rows 2-7 (`EKPins:62,151,161,185`, `EMn2BA:106,111`); `BATwKerA` (`TwistPins:193`) is not used. (v) The ticket asks for predicted lines per file; CLAUDE.md §4 and the stage prompt bar size estimates in (a), so none is given. Inputs: the band lines above (§3-§6 `:187-1429` = 1243 and §7-§10 `:1430-2390` = 961, the two files of the ticket) and the ticket's own 805 / 1,150 / 1,552 with stop line 2,000 per file.

### Verdicts
- Target 1 `baTwistGridWTail_holds d` (every `d`): **PASS**. `C' = D+14`, `CK = 3D+40` close (rows 8-9, slack exponents `4`, `5.2`); the conjugation identity and the variance identity (constant 1) hold; the pin carries no `3 ≤ d` and the route no `|E| < 2`; the `Z` budget is eventual for all `D, ε' > 0`.
- Target 2 (shared helpers with T2438): **PASS**, copy with the stem `TwistGridWTail_` (`TwistGridTail.lean` absent on `main` at this time); the twisted `YfieldsW` moment twin is a new piece (row 6).
- Target 3 (instance at `sz0`, `D = 1`, `ε' = 1/10`): **PASS**; every deterministic hypothesis is discharged at `flow_sz0`, `t0_sz0`; `BATwistGridRem 3 C₀`, `BATwistGridTail 3` stay hypotheses (T2437, T2438); the budgets close from `n* = 16`.
- Target 4 (registry): none.

## (b) Script output — written Mon Oct 12 05:10:45 UTC 2026 (`date -u`); branch `t/T2439`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2439`

**Ticket header.** `C' = D + 14` (`P = ⌈N^{14} · N^D⌉`, `TwistGridWTail2_tail_at`); `CK(D) = 3D + 40` (`baTwistGridWTail_holds` returns `CK := 3 * D + 40`; `TwistGridWTail2_rpow_CK`).
Conjugation identity `Ũ^{(σ̄)} = conj Ũ^{(σ)}`, all four charge pairs: `TwistGridWTail_twU_conj` (TwistGridWTail.lean:83), from `TwistGridWTail_BAMss_conj` (:50, `BAMB_symm`, `BA/Ward:83`) and `TwistGridWTail_BATheta_conj` (:63: `BATheta_isUnit`, `BA/KBase:324`, and the ring map `(starRingEnd ℂ).mapMatrix`, the argument of the private `BAKBase_conj`, `KBase:276`). `BATheta_conj`, `BAMss_pm_eq`, `BATheta_pm_eq` of the ticket list are not used.
**T2438 helpers: copied** (stem `TwistGridWTail_`): `RBM3D/BA/TwistGridTail.lean` was not on `main` at 1b start (about 04:14 UTC: `git ls-tree main --name-only RBM3D/BA/` listed `Twist{AvgA,AvgA2,AvgB,Chain,Grid,Grid2,Ker,Ker2,Pins,QV}` only); `0b55de5` (T2438 merge) is dated 2026-10-11T21:56:42-07:00 = 04:56:42 UTC; `main` at 05:06 UTC also lists `TwistGridRem{,2}`, `TwistGridTail{,2}`.
**Lines per file against the stop line 2,000** (`wc -l`): 1822 (`TwistGridWTail.lean`), 1334 (`TwistGridWTail2.lean`).

```
$ lake build RBM3D.BA.TwistGridWTail RBM3D.BA.TwistGridWTail2 2>&1 | tail -n 1
Build completed successfully (4039 jobs).                (warnings: 12, all `longLine` in the two module docstrings)
$ lake env lean docs/tickets/checks/T2439-check.lean       (run in the branch worktree)   -> exit 0
$ example : ∀ d, BATwistGridWTail d := baTwistGridWTail_holds   (scratch file, import RBM3D.BA.TwistGridWTail2)  -> compiles
$ full `lake build`, with the two `import` lines added to RBM3D.lean temporarily (reverted, not committed: the hub writes root imports):
  Build completed successfully (4257 jobs).
  info: RBM3D.lean:489:0: axiom audit: 12815 theorems, 4025 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c "sorry\|admit\|native_decide" TwistGridWTail.lean TwistGridWTail2.lean       -> 0 and 0 (no `axiom` declaration either)
$ axioms of the 100 public declarations (scratchpad axsum.lean, Lean.collectAxioms):
  public declarations checked: 100; union of axioms: [Quot.sound, Classical.choice, propext]; declarations with a non-standard axiom: []
$ #print axioms RBM.BA.baTwistGridWTail_holds
  'RBM.BA.baTwistGridWTail_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Target.** The merged pin (`BA/TwistGrid2.lean:248-257`, `sed`), and the theorem (`TwistGridWTail2.lean:1234`); no hypothesis added, the pin unchanged:
```
def BATwistGridWTail (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
          ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
            ‖twEEUk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
          ‖(∑ j ∈ Finset.range k, twU sz (BAflowLam0 sz z) (BAflowEs sz z) n i.1 (gridTime s t K n j) (gridTime s t K n k) *ᵥ
            (fun b => twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 b i.2.2.1 i.2.2.2 (j + 1) ω -
              twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 b i.2.2.1 i.2.2.2 j ω)) i.2.1‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
theorem baTwistGridWTail_holds (d : ℕ) : BATwistGridWTail d := by
```

**Compiled nonempty instance** (`TwistGridWTail2.lean:1287-1332`, section `Inst`): `d = 3`, `sz0`, `zSeq`, `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/2`, `t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`), `D = 1`, `ε' = 1/10`, `K_n = ⌈N_n^{CK}⌉ + 1`; every deterministic hypothesis discharged. The second `example` (`:1302`) states the full conclusion (`∃ CK n, 0 ≤ CK ∧ ∀ i, Pp {…} ≤ ofReal (N^{-1})`). `BATwistGridRem 3 11`, `BATwistGridTail 3` are the hypotheses of the assembly examples (`:1320`, `:1324`; TL2a2, TL2a3):
```
example : ∃ n : ℕ, True := by
  obtain ⟨CK, hCK, H⟩ := baTwistGridWTail_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) 1 one_pos
  have H2 := H (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)) (1 / 10) (by norm_num)
  obtain ⟨n, hn⟩ := H2.exists
  exact ⟨n, trivial⟩

/-- The same instance, the conclusion kept: some size index `n` with the pinned bound at every label, at the window `[1/2, 2/3]`. -/
example (hRem : BATwistGridRem 3 11) (hTail : BATwistGridTail 3) : BATwistGridMartAt 3 11 :=
  baTwistGridAssemble_holds 3 11 (by norm_num) hRem hTail (baTwistGridWTail_holds 3)
```

**Name-clash grep** (script, 100 public names, `git grep -l -w NAME main`, `main = 98aab64`; then `git log --all`):
```
public names: 100 ; names occurring in main: 0
$ git log --all --format=%h -- 'RBM3D/BA/TwistGridWTail*'     -> 3ef3862 4dda3d6 6c0148f ee9b041 b76b78b   (all on t/T2439)
```
**Ports.** No file under `../RBM1D` or `../RBM2D` was read or copied: no RBM1D/RBM2D `diff --stat`. Copies are of merged RBM3D files (commit = `git log -1 --format=%h main -- file`): `Path/DifREP2.lean:805-917, 1051-1187` (`76b840e`: `_hasDerivAt_dir`, `_linTr_neg_I_smul`, `_seqXmat_single`, `_linTrVar_eq/_le`, section `Frozen`); `Path/DifREP3.lean:316, 726-757, 786-834, 857-934, 1985, 2179` (`b3c37aa`: `norm_double_sum_le`, grid arithmetic, coarse grid, Doob, `f1_arith`, `tendsto_rpow_exp`), whose §6-§10 (`:1088-2390`) is the template of `TwistGridWTail2`; `Path/QVIdentity.lean:430-585` (`fe32346`: coordinate algebra); `Induction/LoopC2N.lean:238-305` (`14137ce`: line jets, `fderiv2_of_line`); `Induction/GridAssemblyN.lean:872` (`686cf71`: coordinate measurability). New proofs (no twin): the observable `Φ_b` as a Hermitian test function (`TwistGridWTail_Phi_*`, `_hermTestFun`), the gradient bounds (`_der_norm_le`, `_der_sub_le`, `_twEEM_norm_le`, `_twEEM_sub_le`), `TwistGridWTail_deriv_identity`, `TwistGridWTail_linTrVar_le_QV`, `TwistGridWTail_xi_ae`, the kernel facts (§1, `TwistGridWTail2_norm_twEEUM_*`).
`git diff main...t/T2439 --stat`: `RBM3D/BA/TwistGridWTail.lean | 1822 +++`, `RBM3D/BA/TwistGridWTail2.lean | 1334 +++`, 2 files changed.

**Narrative.**
1. Route as the ticket: coarse grid `v_p`; per `(p, a')` the weights `kap_j = Ũ_{u_j,v_p}(a', ·)·1[u_j ≤ v_p]`; the increment splits `Σ_b kap_j(b) ξ_{j+1}(b) = ζ_j + y_j`, `ζ_j = stepZCN` of the family `Φ_b(M) = L̃_{u_{j+1}}(g₀Ψ + M)` at the kernel `(·, a) ↦ kap_j(a)`; `ζ` by `difRep2_peel` (conditional mgf `TwistGridWTail_condMGF_generic`, proxy `Re Σ κ κ̄ twEEM_{u_{j+1}}`), `y` by Doob (`TwistGridWTail_Y_tail`); exact transfer by `BAuKer_comp`.
2. Constants in Lean (at `η⁻¹ = (1−u)⁻¹ = 16N`): `|∂_{xy}L̃| ≤ 2(16N)³`; `|twEEM| ≤ M_ee = 2²⁶N⁷`; `V_Q = 2³⁴N⁹`; `c₃ = 2³⁹N¹⁰`; shift sum `≤ 1649267441664·N¹⁰Δ`; `C₂ = 6η⁻⁴` (section (a) row 6 kept the looser `6Nη⁻⁴`; the entrywise count is the proved one); `P_Y = 27648·2⁴⁰·N¹⁸` (`Y` second moment from `stepDecompCN_Y_sq` and `integral_normPow4_incr_le`, `768 N⁸`; (a) row 6 used the 2000 of `AzumaProxyN_YfieldsW`).
3. Budgets (`TwistGridWTail2_budget_*`, pure arithmetic) hold for `N ≥ 2⁷⁰`; the `Z` budget `24 (2³⁵+2) N²⁴ (N^D)³ exp(−(N^{ε'}/4)²/16) ≤ 1` is `TwistGridWTail2_eventually_Z`. Eventual conditions of `baTwistGridWTail_holds`: `2⁷⁰ ≤ N`, the `Z` budget, `N^ε ≥ 1/(8κ)`; the last gives `η_u ≥ 1/(16N)` for `u ≤ t` (`EMn2BA_one_sub_T0`, `EMn2BA_mF_data`, `BAdom`) and `(1−u)⁻¹ ≤ 16N` follows from `η_u ≤ 1−u`.
4. File split: file 1 holds the kernel facts, the entry algebra, the observable, the variance identity, the frozen mgf, the `ξ` identification, Doob, grid arithmetic and the `Y` tail; the `Z` vocabulary, the coarse grid, the peeling, pathwise inclusion, core, budgets, target and instances are in file 2 (the ticket put the coarse grid and the `Z` part in file 1; both files stay below 2,000).
5. `condMGF_generic` and `Y_fields` are generic in the label family (`HermTestFun`, `C₂` as hypotheses) through `stepDecompCN`, `stepDecompCN_Y_sq`, `integrable_stepZCN_*`; `Y_fields` takes `ξ =ᵐ stepXiCN` and `filt (j+1)`-measurability of `ξ` (discharged by `xi_ae`, which uses `Φ_b` Borel measurable by `walk_measurable_Gres_apply` and bounded by `η⁻²`).

## (c) Verified Mathlib names (all compile on the final commit)
- `HasDerivAt.fun_sum` (Analysis/Calculus/Deriv/Add:218); `contDiffAt_ringInverse`; `Complex.conjCLE`; `ContDiffAt.sum`, `ContDiffAt.mul`.
- `MemLp.condExp` (ConditionalExpectation/Real:273), `MemLp.mono'` (LpSeminorm/Basic:585), `MemLp.re`, `MemLp.im`, `MemLp.integrable`, `memLp_two_iff_integrable_sq`, `memLp_two_iff_integrable_sq_norm`, `memLp_top_of_bound`.
- `condExp_finsetSum` (ConditionalExpectation/Basic:304), `condExp_smul` (:318), `condExp_sub` (:336), `condExp_const` (:148), `ContinuousLinearMap.comp_condExp_comm`; `doob_L2_max`, `martingale_sq_eq_sum`, `martingale_of_condExp_sub_eq_zero_nat`.
- `Matrix.mulVec_sum`, `Matrix.mulVec_mulVec`, `Matrix.one_mulVec`, `Matrix.sub_mulVec`; `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`; `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_rpow_atTop`; `Real.one_le_rpow`, `Nat.lt_two_pow_self`, `Nat.ceil_lt_add_one`.
- Verified absent: none claimed.

## (d) Open issues and paper-delta candidates
- `T2439a` (proof device, no statement change): clause (iv) is proved by Azuma/Doob steps in place of the BDG step of `(alu9_STime)` (the existing D90/§7 delta), with explicit constants `C' = D + 14`, `CK = 3D + 40`.
- The mismatch of the pin's weights `Ũ_{u_j,u_k}` with the exact 4 (a) weights `Ũ_{u_{i+1},·}` stays TL2d's (T2428 (a″) decision 4); not touched here.
- Section (a) needed no correction (no (a′)); two constants of (a) are looser than the proved ones (row 6: `C₂`, `P_Y`; narrative item 2).
- The hub adds `import RBM3D.BA.TwistGridWTail`, `import RBM3D.BA.TwistGridWTail2` at merge (not committed here). `main` moved after 1b started (T2438 `0b55de5`; `TwistGridRem*` on main); the name check above ran against `main = 98aab64`; the branch is based on `b16ad61`.

