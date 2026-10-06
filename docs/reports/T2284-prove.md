Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 10:50:43 UTC 2026

Notation: `N = sz.size n = (WL)^d`, `x = ln N`, `W ≥ N^𝔠` (Bandwidth), `W ≤ N`, `g = lam n ≤ Λg = 𝔡⁻¹` (WO), `κ' = min κ (4/5) ≤ Im m(E n)` (`nqGood1_mE_im_ge`, `NQGood1.lean:404`), `ε₀' = min ε₀ 1`, `τ_R = min τ 1`, `Ls = Im⁻¹ ln N`. Scripts (Python, no Lean) in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2284/`: `g1.py g2.py inst.py g3.py`.

### (i) Exponent table (order `(d,k,Λg,κ') → C → ε₀' → ε₁=εq → D'' → D' → τ',τ_R → C_P* → C_P' → C_K`, as in the ticket's 0)
| name | value | constraint (source) | slack |
|---|---|---|---|
| `C` | `nzUgen_holds d k Λg κ'` (`QtNonzero.lean:299`), `C>0`, abstract | row sum / operator bound of `Q^{(A)}∘𝒰`; H1–H3 need it only through `log(6C)` | none needed; log10 crossovers below at `C ∈ {1, 10³, 3380}` |
| `ε₀'` | `min ε₀ 1` (`1/10`) | `ε₀' ≤ ε₀` (last step `N^{ε₀'} ≤ N^{ε₀}`) | `0` at `ε₀ ≤ 1` |
| `ε₁ = εq` | `ε₀'/8` (`1/80`) | `>0`; H1 `ε₁<ε₀'`, H2 `2ε₁<ε₀'`, H3 `εq+ε₁<ε₀'` | `7ε₀'/8`, `3ε₀'/4`, `3ε₀'/4` (in the exponent of `N`) |
| `D''` | `2(k+2)/𝔠 + 1` (`61` at `𝔠=1/6,k=3`) | H4: `εq + k − 𝔠D''/2 − ε₀' < 0` | `2 + 𝔠/2 + 7ε₀'/8` (`2.1708` at `𝔠=1/6,ε₀'=1/10`); superseded `2k+4d+10`: coefficient `+0.5792` there, H4 false (G1) |
| `D' = D''+1` | `62` | `W^{-D'} ≤ W^{-D''}/2` needs `W ≥ 2` | crossover `log10 N = 1.80` (`𝔠=1/6`) |
| `τ'` (GoodSetN) | `1` | only `0 < τ'` (GridGoodNConcl takes every `ε,τ',D'>0`, `GridGoodN.lean:505-518`) | free |
| `τ_R` | `min τ 1` (`1/2`) | `RangeCond τ t ⇒ RangeCond τ_R v` (`N≥1`, `v ≤ t`, `τ_R ≤ τ`); `0<τ_R≤1` (`nqBudget_merged_inputs`) | `1/2` |
| `hη` | `η_v⁻¹ ≤ κ'⁻¹ N^{1−τ_R} ≤ N` | `N^{τ_R} ≥ κ'⁻¹` | crossover `log10 N = 1.99` |
| `τK`, `D_Y = D_t` | `1`, `k+2` | H5 `k−D_Y < ε₀'`, H6 `k−D_t+log_N cA < ε₀'` | `2+ε₀'` (H6 minus `k log 2/ln N`) |
| `cA` and the `Y` levels | `2^k`; `4^{|A|+1} ≤ 4^{k+1}`, `16^{|A|+1} ≤ 16^{k+1}` | `|A| ≤ k`; `Σ|q| ≤ 2^{|A|}` (`norm_zeroModeSet_le`) | all `A` at once |
| `C_P*`, `C_P'` | `11+(4k+4)max 0 (1−τ_R)` (`AzumaProxyN2.lean:921`, witness inside `yMomentsUnifN`) → `19`; `C_P' = C_P*+2k+2 = 27` | `4^{k+1} P ≤ N^{C_P'}` iff `4^{k+1} ≤ N^{2k+2}` | crossover `log10 N = 0.30` |
| `C_K` | `D₁+2C_P'+D''+16k+40 = 204` (`k=3,D₁=1`) | `AssembledN`: `D₁+1+4D_Y+k+2C_P'+8 = 87`; merged `h1..h4`: `28, 19.5, 10, 0.5`; shift `D''+2k+5 = 72`; `C_K ≥ 1` | `117`; `≥ 176`; `132` |
| `hδ` | `ee ≤ k(2k+2)N^{2k+4−C_K}` (`NQEndLin.lean:533`-pattern, `W^dL^d=N`, `η⁻¹ ≤ N`) | `≤ W^{-D''}/2`, `W^{-D''} ≥ N^{-D''}` | exponent `2k+4−C_K+D'' = −133` (`W≤N`); `−126.3` at `log10 N=1` (W=N^{1/3}) |
| grid | `Δ ≤ N^{-C_K}`, `KΔ = v−s ≤ 1`, `Δη_v⁻¹ ≤ N^{1−C_K} ≤ 1` | union `4^k N^{-(D₁+1)} ≤ N^{-D₁}` (pairs `(σ,A)`, `≤ 2^k·2^k`) | `N ≥ 4^k`: crossover `log10 N = 3.61` (`k=6`) |
| window | `0 ≤ s`, `1−g²/L² ≤ s ≤ u_i ≤ u_m ≤ v ≤ t < 1`, `0<g≤Λg`, `κ'≤Im m`, `|E|<2`, `3≤L`, `A ⊇ I_diff σ` | hypotheses of `nzUgen_holds`; `1−s ≤ g²/L²` is `STCaseII` (`Step34Pins.lean:241`) | equality at `szB` (`1−s = 1/16 = g²/L²`) |
| `κ'` | `min κ (4/5)` | `κ' ≤ Im m(E n)` for `|E| ≤ 2−κ` | min over `κ∈(0,2]` of `Im m − κ'` on 20000 points `≥ −1e-30`, equality at `κ = 4/5` |

H1–H6 and the other rows over the grid (`g2.py`: `𝔠∈{1/6,1/3}`, `ε₀∈{1/10,1/100}`, `C∈{1,10³,3380}`, `k∈{2,3,6}`, `Im m∈{1/10,1/2,0.968}`, `τ_R=1/2`, `W=N^𝔠` or `N^{1/3}`; `log10(LHS/RHS)`, `>0` = not yet absorbed). Command: `python3 g2.py`
```
row                                          | at log10N=1,2,3,6              | crossover log10N (last >0) | attained at (c,eps0,C,k,Im)
H1  C N^e1 <= N^e0/6                         |     +4.30     +4.29     +4.28     +4.25 | 492.23                     | (0.1667, 0.01, 3380.0, 2, 0.1)
H2  C cA k N^2e1 Ls <= N^e0/6                |     +8.25     +8.54     +8.71     +8.99 | 1524.91                    | (0.1667, 0.01, 3380.0, 6, 0.1)
H3  N^eq C N^e1 sqrt(k Ls) <= N^e0/12        |     +5.67     +5.81     +5.89     +6.02 | 955.79                     | (0.1667, 0.01, 3380.0, 6, 0.1)
H4  N^eq N^k C sqrt(k W^-D'') <= N^e0/12     |     +2.91     +0.81     -1.28     -7.56 | 2.38                       | (0.1667, 0.01, 3380.0, 6, 0.1)
H5  N^k N^-DY <= N^e0/6                      |     -1.23     -3.24     -5.25    -11.28 | 0.38                       | (0.1667, 0.01, 1.0, 2, 0.1)
H6  cA N^k N^-Dt <= N^e0/6                   |     +0.57     -1.44     -3.45     -9.48 | 1.28                       | (0.1667, 0.01, 1.0, 6, 0.1)
hdelta ee<=W^-D''/2 (W=N^(1/3))              |   -126.29   -253.95   -381.62   -764.62 | none (<=0 from 0.3)        | None
hdelta, crude W<=N                           |   -109.62   -220.62   -331.62   -664.62 | none (<=0 from 0.3)        | None
hdelta W^-D' <= W^-D''/2 (W=N^c): W>=2       |     +0.13     -0.03     -0.20     -0.70 | 1.80                       | (0.1667, 0.1, 1.0, 2, 0.1)
heta  kappa'^-1 N^(1-tauR) <= N              |     +0.50     +0.00     -0.50     -2.00 | 1.99                       | (0.1667, 0.1, 1.0, 2, 0.1)
hDeta N^(1-CK) <= 1                          |   -143.00   -286.00   -429.00   -858.00 | none (<=0 from 0.3)        | None
union 4^k N^-(D1+1) <= N^-D1                 |     +2.61     +1.61     +0.61     -2.39 | 3.61                       | (0.1667, 0.1, 1.0, 6, 0.1)
4^(k+1)<=N^(2k+2) (C_P')                     |     -4.19    -10.19    -16.19    -34.19 | 0.30                       | (0.1667, 0.1, 1.0, 2, 0.1)
closed form (log10 N*): H1 = log10(6C)/(7e0'/8): C=1: 8.89  C=1e3: 43.18  C=3380: 49.22 (e0'=1/10);  e0'=1/100: 88.9 / 431.8 / 492.2
```
Every row is `≤ 0` eventually (scan range `log10 N ≤ 3000`). The binding thresholds are H1–H3 (the polylog rows), none inside `W^{Cε}`; every one is a `∀ᶠ n` threshold, not a hypothesis. G1 (O4), `ε₀=1/10` rows (`python3 g1.py | grep -E "^c |1/10 +\|"`):
```
c      k  eps0 | D''=2(k+2)/c+1  D_old=2k+4d+10 | e(D'')       e(2(k+2)/c)  e(D_old)    | H4 true? (D'' / D_old) | C_K>=D''+2k+5  C_K (C_P*=11+(4k+4)(1-tauR))
1/100  2  1/10 | 801             26              | -2.0925      -2.0875      1.7825      | True / False | 810 920
1/100  3  1/10 | 1001            28              | -2.0925      -2.0875      2.7725      | True / False | 1012 1144
1/100  6  1/10 | 1601            34              | -2.0925      -2.0875      5.7425      | True / False | 1618 1816
1/6    2  1/10 | 49              26              | -2.1708      -2.0875      -0.2542     | True / True | 58 168
1/6    3  1/10 | 61              28              | -2.1708      -2.0875      0.5792      | True / False | 72 204
1/6    6  1/10 | 97              34              | -2.1708      -2.0875      3.0792      | True / False | 114 312
1/3    2  1/10 | 25              26              | -2.2542      -2.0875      -2.4208     | True / True | 34 144
1/3    3  1/10 | 31              28              | -2.2542      -2.0875      -1.7542     | True / True | 42 174
1/3    6  1/10 | 49              34              | -2.2542      -2.0875      0.2458      | True / False | 66 264
```

### (ii) One concrete nondegenerate instance
Data: `szB` (`d=3, L=4, W=n+4, lam=1`, so `N=64(n+4)³`), `𝔠=1/6, 𝔡=1/10 (Λg=10), κ=1 (κ'=4/5), τ=1/2`, `E ≡ 1/2` (`Im m = √15/4 = 0.9682`), `s ≡ 15/16`, `t ≡ 31/32`, `v ≡ 31/32` (non-collapsed) or `15/16` (collapsed), `k=3`, `σ = sig3` (`STIdiff = {0,1}`), `Λ=Φ₁=Φ₂=Φ₃=1`, `ε₀=1/10`, `D₁=1`. Command: `cd <scratch>/T2284 && python3 inst.py`
```
3<=d,k>=2,kappa,c,tau,dd,eps0,D1>0                                       True
|E|=1/2<=2-kappa=1; 0<=s<=t<1, s<=v<=t (both v)                          True
STCaseII: 1-s <= lam^2/L^2 (1/16<=1/16, equality)                        True
SizeTendsto: N(n)>=n (n<20000)                                           True
Bandwidth 1/6: N<=W^6 (n<20000)                                          True
WO 1/10: W^(-3/2+1/10)<=1=lam<=1/dd=10 (W>=1)                            True
RangeCond(1/2) t: N^(-1/2)<=1-t=1/32 iff N>=1024 (n<20000)               True
Lambda=1>=0 (and >=1), Phi_i=1>=0                                        True
kappa'=4/5 ; (kappa')^2=16/25 <= (Im m)^2=15/16 : True ; Im m=0.968246
nzUgen window: 1-g^2/L^2 = 15/16 <= s = 15/16 <= u_i <= v <= 31/32 < 1 ; 0 < g=1 <= Lambda_g=1/dd=10
constants k=3: eps0'=1/10 eps1=eq=1/80 D''=61 D'=62 tau_R=1/2 tauK=1 D_Y=D_t=5 cA=2^k=8 C_P*(witness 11+(4k+4)max(0,1-tau_R))=19 C_P'=27 C_K=204
AssembledN: D1'+4D_Y+k+2C_P'+8 = 87 <= C_K=204 (slack 117)
nqBudget_merged_inputs h1..h4 thresholds 28 39/2 10 1/2 all < C_K=204 : True ; shift C_K>=D''+2k+5=72: True ; C_K>=1: True
n=0 (N=4096,W=4): W^-D'+ee(u_{K-1},u_K) = 4.70198e-38 <= W^-D'' = 1.88079e-37 : True
n=0: eta_v^-1=33.0495 <= N: True ; Delta*eta_v^-1=1.238e-737 <= 1 ; K*Delta=0.03125 <= 1 ; 4^k=64 <= N: True ; 4^(k+1)=256 <= N^(2k+2) : True ; log10 K=736.92
hlog n=0: (1/Im)(ln 2 + Dl/(1-v)) = 0.715879 <= Im^-1 ln N = 8.59055
eventual thresholds at szB (W=n+4, N=64W^3, Im m=0.968, k=3, eps0=1/10): last log10 N where a row of H1..H6 fails, scanning log10 W step 0.05
  C=1        H1:8.9 H2:57.2 H3:29.9 H4:2.7 H5:none H6:none
  C=3380     H1:49.2 H2:107.9 H3:79.8 H4:3.2 H5:none H6:none
  C=1000000  H1:77.4 H2:142.5 H3:113.7 H4:3.5 H5:none H6:none
  all six hold at W=10^130 (N=64e390, log10 N=391.806) for C=1,3380,1e6: [True, True, True]
assembledRHSNZN=4.52797883086e+47 ; AssembledN RHS (kappa=C, epsK=0, delta0=deltaD=0)=4.52797883086e+47 ; |diff|=0.0 ; sum_j cQVNZN=4.02867e-9 > 0
```
Reading: the pin's own hypotheses hold at `szB` for every `n` (exact integer/`Fraction` checks, `n<20000`; closed forms: `N ≤ W⁶` iff `64 ≤ (n+4)³`, `N ≥ 1024`). The grid is `K n = max 1 ⌈N^{C_K}⌉` with `C_K = 204`: `K ≈ N^{204}` (`log10 K = 736.9` at `n=0`), a function value never summed; the conclusion needs `n ≥ n₀`, with `log10 N₀ = 57.2 / 107.9 / 142.5` at `C = 1 / 3380 / 10⁶` (H2 binding), and Lean takes `n` by `Filter.Eventually.exists`. Finite-size rows at `n=0` (`hδ`, `hη`, `hΔη`, `KΔ`, union, `C_P'`) hold with the actual `K = N^{204}`; H1–H3 are false at `n=0` (need `log10 N ≥ 8.9`), true at `W = 10^{130}`. The last line (`n=0`, `K=4`, `s=15/16`, `v=31/32`, `C=5`, `cA=8`, `Λ=Φ_i=1`, `D''=61`, `D_Y=5`, `τK=1`, `εq=1/80`; two separate transcriptions) confirms that `assembledRHSNZN` is the right side of `AssembledN` at `m = K` with `κ ≡ C`, `εK ≡ 0`, `δ0 = δD = 0`, `dDrift = cA·dDriftLinN`, `c = cQVNZN`, `stepErr = cA·stepErrN`, `ε = εq`, `D = D_Y`; `K=4` is not a grid of the pin, it only checks the identification (`hc_pos`: the sum is `> 0`).

External hypotheses: none (`prop5Short_holds`, `prop8ZeroMode_holds` are unconditional inside the merged `nzUgen_holds`), so no limit computation. `hexp` (G3), `k=2, d=3, L=4, g=1, E=0.3, K=4, s=15/16, v=31/32`, random complex tensors `A0, Dr_j, Z_j, Y_j, R_j`; `A_K = 𝒰(u₀,u_K)A0 + Σ_j 𝒰(u_{j+1},u_K)(ΔDr_j+R_j+Z_j+Y_j)`, `Af(K)` the ticket's formula with every tensor replaced by its `Q^{(A)}`: `python3 g3.py | head -2`
```
sigma=(True, False) A=(0, 1): max|Af(K)-Q(A_K)|=6.5e-15 (max|A_K|=15.7); max|Q Ugen - Ugen Q|=2.2e-15; max|QQ-Q|=2.5e-16
sigma=(True, True) A=(0,): max|Af(K)-Q(A_K)|=8.0e-15 (max|A_K|=16.2); max|Q Ugen - Ugen Q|=1.8e-15; max|QQ-Q|=2.5e-16
```
Pin text (`awk '/^def T2284_nzGridEndN/{f=1} /^\/-! ## 3/{f=0} f' docs/tickets/checks/T2284-check.lean > pin.txt`; `grep -c -F`): `Φc` 2 (its `∀` binder, line 13, and the `GoodSetN` argument, line 21), ` ^ 2` 0, `C₀` 0, `STKbound` 0, `Prec` 0, `STCaseII` 1; right side line 35 `N^ε₀ * (Λ n ^ ((1:ℝ)/2) + Φ₁ n + Φ₂ n + Φ₃ n) * B_v^k`; `GoodLinN` takes `N^ε₁, Φ₁ n, Φ₂ n, Φ₃ n`, the same `N^ε₁` as `GoodSetN`; initial and terminal objects are `zeroModeSet d (sz.L n) A (fun b => sz.STLKM n (E n) (s n | v n) (pathH … 0 | K n …) σ b)`; the pin has no `W⁻¹ ≤ (1−t)/(1−s)` premise.

### Verdicts
- Target 0 (constants, order, `C_K`): PASS (every constraint row of (i) closes, slacks above). Target 1 (absorption H1–H6, `hδ`, `hη`, `hΔη`, union, range monotonicity, EK-5 window): PASS (G2: all rows `≤ 0` eventually; `RangeCond τ_R v` and `nqBudget_merged_inputs h1–h4` at `τ'=τ_R` closed by `C_K`). Target 2 (assembly per `(σ,A)` at `nqLinExitTauN`): PASS (`hexp` identity 1e-14 above, `AssembledN` right side = `assembledRHSNZN`, `hc_pos` positive, `Y` levels `4^{k+1}P ≤ N^{C_P'}`; each `GridAssemblyHypN` field has a merged source or is new as listed in the ticket: `hdDrift0`, `hc_pos`, `hstepErr0`). Target 3 (`nzGridEndN`, collapsed window `Δ=0 ⇒ pathH j = pathH 0` by `√0 = 0` in `pathH`, `Walk.lean:75`; `N^{ε₁} ≤ N^{ε₀}`, `Λ ≥ 1`): PASS.
- G1 PASS (the `D''` of 0 gives `−2.09 … −2.25` at `ε₀=1/10`, the superseded value is positive at `(1/6,3)`, `(1/6,6)`, `(1/3,6)`, `(1/100,·)`). G2 PASS. G3 PASS (`hexp` identity, `Q Ugen = Ugen Q`, `Q²=Q`).
- §29/§45: (1) `0≤s`, `s≤t`, `t<1`, `s≤v≤t` are premises of the pin; (2) case (ii) boundary `1−g²/L² ≤ s ≤ u_i` with `0 ≤ u_i`, equality at `szB`; (3) no `L^d ≤ W^K`, no `W⁻¹` window; (4) all numerical conditions are `∀ᶠ n` from `SizeTendsto`, `Bandwidth`, `WO`, `RangeCond`; (5) per-path statement, no `Prec`; (6) `0<g≤Λg` from `WO`, `κ' ≤ Im m` from `nqGood1_mE_im_ge` (row `κ'`); (7) scale `N = sz.size n`. `stKbound_holds sz hd hκ hΛg hsize (Eventually.of_forall hE) hlam` is the call used at `NQEndLin.lean` (`nqGridEndLinN`), so `STKbound` is not a premise.
- Consumer fit (S3-22b): `GridGoodNConcl` (`GridGoodN.lean:505`) takes every `ε,τ',D'>0`, `1 ≤ Φ`, `∀ C, K+1 ≤ N^C`; `NQLinConcl` (`NQLin.lean:102`) takes `ε>0`, the same `K` bound; both events are spelled `pathH sz s v K n j ω ∈ … (gridTime s v K n j) k ((N:ℝ)^ε) …`, as in the pin. Caveat, not a FAIL: the thresholds in `n` (`log10 N₀` up to `1525` at the worst grid corner of G2, `57–143` at `szB`) are large and only eventual; `C` of `nzUgen_holds` is abstract, so only its `log(6C)` enters.

## (b) Script output — Tue Oct  6 11:26:12 UTC 2026
Commit `40fc59f` on `t/T2284` (`git status --short` empty); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2284`; scratch scripts in the scratchpad `T2284/`.

### Build, statement script, axioms
```
Tue Oct  6 11:22:16 UTC 2026
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2284 && git status --short && lake build RBM3D.Induction.QtNonzeroEnd 2>&1 | grep -E "QtNonzeroEnd|error|sorry|Build completed"
Build completed successfully (3846 jobs).
tool log of the genuine build (11:19:23 UTC, same file content as commit 40fc59f): `✔ [3846/3846] Built RBM3D.Induction.QtNonzeroEnd (7.9s)`, no warning of this file
```
```
$ lake env lean stmt.lean  # = check-file §2 (T2284Check.T2284_nzGridEndN) + `example : RBM.Ind.T2284Check.T2284_nzGridEndN := @RBM.Ind.nzGridEndN` + `#print axioms`
'RBM.Ind.nzGridEndN' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean axioms.lean  # #axioms_of_module RBM3D.Induction.QtNonzeroEnd (all public decls) + #print axioms of the targets
RBM3D.Induction.QtNonzeroEnd: 50 public theorems/definitions (private and internal excluded)
  50 with axioms #[Classical.choice, Quot.sound, propext]
  declarations using sorryAx: []
'RBM.Ind.nzGridEndN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.nzEnd_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.nzEnd_instance_collapsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroEndInst.assembly_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Target statement (`nzGridEndN`, extracted by `sed -n 979,1014p`) and the pin diff
```
theorem nzGridEndN :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseII s t → sz.RangeCond τ t →
    ∀ k : ℕ, 2 ≤ k →
    ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                  (sz.Bctl n (v n)) ^ k := by
$ pin_diff.sh   # statement lines of the file vs the pin in docs/tickets/checks/T2284-check.lean
Lean statement: RBM3D/Induction/QtNonzeroEnd.lean:980-1014 (header line 979, trailing ' := by' stripped); pin: T2284-check.lean:206-240
diff exit 0: the 35 statement lines are identical
```

### The compiled nonempty instances (`nzEnd_instance`, `sed -n 1501,1522p`; `grep -n ^example`)
```
theorem nzEnd_instance (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ szB), (pathP szB).real Gᶜ ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KB C_K n, pathH szB sB vB (KB C_K) n j ω ∈
            szB.GoodSetN n (Einst n) (gridTime sB vB (KB C_K) n j) k
                (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 τ' D' ∩
              GoodLinN szB n (Einst n) (gridTime sB vB (KB C_K) n j) k
                (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 1) →
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd 3 (szB.L n),
              ‖zeroModeSet 3 (szB.L n) A
                  (fun b : Fin k → Zd 3 (szB.L n) =>
                    szB.STLKM n (Einst n) (sB n) (pathH szB sB vB (KB C_K) n 0 ω) σ b) a‖ ≤
                ((szB.size n : ℕ) : ℝ) ^ ε₁ * (szB.Bctl n (sB n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd 3 (szB.L n),
              ‖zeroModeSet 3 (szB.L n) A
                  (fun b : Fin k → Zd 3 (szB.L n) =>
                    szB.STLKM n (Einst n) (vB n) (pathH szB sB vB (KB C_K) n (KB C_K n) ω) σ b) a‖ ≤
                ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ((1 : ℝ) ^ ((1 : ℝ) / 2) + 1 + 1 + 1) *
                  (szB.Bctl n (vB n)) ^ k := by
1487:example := assembly_instance (STIdiff sig3) (Finset.Subset.refl _)
1490:example := assembly_instance Finset.univ (Finset.subset_univ _)
1570:example := nzEnd_instance 2 le_rfl
1573:example := nzEnd_instance 3 (by norm_num)
1576:example := nzEnd_instance 4 (by norm_num)
1579:example := nzEnd_instance_collapsed 3 (by norm_num)
```

### Name clash, forbidden tokens, registry pre-check, branch diff
```
grep -rn -F 'nzGridEndN' RBM3D RBM3D.lean (excluding the new file): 0 hits
grep -rn -F 'RBM.Ind.QtNonzeroEndInst' RBM3D RBM3D.lean (excluding the new file): 0 hits
grep -rn -F 'QtNonzeroEndInst' RBM3D RBM3D.lean (excluding the new file): 0 hits
grep -rn -F 'nzEnd_' RBM3D RBM3D.lean (excluding the new file): 0 hits
grep -rn -F 'QtNonzeroEnd' RBM3D RBM3D.lean (excluding the new file): 0 hits
public declarations checked: 50
Tue Oct  6 11:23:31 UTC 2026
$ grep -n -w -E "sorry|admit|axiom|native_decide|maxHeartbeats" RBM3D/Induction/QtNonzeroEnd.lean | wc -l
0
$ git diff --stat main...t/T2284
 RBM3D/Induction/QtNonzeroEnd.lean | 1584 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1584 insertions(+)
$ lake env lean reg_before.lean / reg_after.lean   # `import RBM3D` [+ `import RBM3D.Induction.QtNonzeroEnd`] + `#assert_rbm_axioms`
before: exit 0; axiom audit: 8174 theorems, 2650 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
after:  exit 0; axiom audit: 8214 theorems, 2660 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ diff <(tail -n +2 reg_before.out) <(tail -n +2 reg_after.out)   -> empty (all ledger lines after line 1 identical)
```


**Narrative** (facts from the files and the tool log above)
1. Scope: new file `RBM3D/Induction/QtNonzeroEnd.lean`, 1584 lines; 50 public declarations (`RBM.Ind.nzGridEndN` and 49 in `RBM.Ind.QtNonzeroEndInst`), 29 private helpers (prefix `nzEnd_`); no `set_option maxHeartbeats`; `Test/Axioms.lean` and `RBM3D.lean` untouched. `nzGridEndN` has exactly the pinned type (empty diff, compiled `example`); no hypothesis added or weakened.
2. Route (shape of `nqGridEndLinN`, `NQEndLin.lean:1067`): private `nzEnd_assembly` applies the merged `assembledN` (`GridAssemblyN.lean:1605`) per pair `(σ, A)`, `STIdiff σ ⊆ A`, at `τ = nqLinExitTauN` (`NQLin.lean:716`) with `Cls X := (Q^{(A)} X = X)`, `κ ≡ C`, `εK ≡ 0`, `δ0 = 0`, `δD ≡ 0`, `A0 = Q A_0`, `Dr = Q driftTensorN`, `Z = Q ZvecN`, `Y = Q YvecN`, `R = Q (predIncN − Δ driftTensorN)`, `dDrift = 2^k dDriftLinN`, `c = cQVNZN`, `v = 4^{|A|+1} Δ² P`, `w = 16^{|A|+1} Δ⁴ P²`, `stepErr = 2^k stepErrN`, `P' = 4^{k+1} P ≤ N^{C_P'}`.
3. Field sources: `hexp` is `rfl` (`Af` is the Duhamel formula; on the good walk it equals `Q A_K` by `zeroModeCalc_duhamel_inside_at`, `ZeroModeCalc.lean:522`, `GridDuhamelN_Ugen_add`, `zeroModeSet_add`, `zeroModeSet_smul`); `hker = nz_hker` (`QtNonzero.lean:327`) with the operator half of `nzUgen_holds` (`:299`) at `(u_i, u_m)`; `hA0cls`, `hDcls` = `zeroModeSet_idem` (`:97`); `hdrift = nz_hdriftN` (`:358`) and `2^{|A|} ≤ 2^k`; `hY = yMomentBounds_nzN` (`:731`) on the moments of `yMomentsUnifN`; `hR` = `gridDriftN_envelope` (`GridEnvelopeN.lean:111`) + `norm_zeroModeSet_le`; Azuma input = `subGaussStop_nzN` (`:417`) with the row half of `nzUgen_holds` at `(u_{j+1}, u_m)`; new here: `hdDrift0`, `hc_pos` (`Δ > 0`, `C > 0`, `W^{-D''} > 0`), `Zmeas` (`gridAsm_stronglyMeasurable_ZvecN` composed with the continuous `zeroModeSetLin`).
4. Case-(ii) window: `1 − g²/L² ≤ s ≤ u_i` from `STCaseII` (`Step34Pins.lean:241`), `0 ≤ u_i`, `u_i ≤ u_m < 1`; `0 < g ≤ 𝔡⁻¹` from `WO`; `κ' = min κ (4/5) ≤ Im m` by `nqGood1_mE_im_ge`; no `W⁻¹ ≤ (1−t)/(1−s)`; `STKbound` is internal (`stKbound_holds`, `KLFinal.lean:243`); `Φc` occurs only in the good-walk hypothesis (`GoodSetN`, only its `STeeM` clause is used), never on the right side.
5. Constants as in the ticket's 0: `D'' = 2(k+2)/𝔠 + 1` (H4: `𝔠 D''/2 = k + 2 + 𝔠/2`), `D' = D'' + 1`, `τ' = 1`, `ε₁ = εq = ε₀'/8`, `C_K = D₁ + 2C_P' + D'' + 16k + 40`; the `AssembledN` exponent condition, `nqBudget_merged_inputs` h1–h4 (`NQBudget.lean:834`) and the shift `D'' + 2k + 5 ≤ C_K` close by `linarith` (`hC1`–`hC6` in §5).
6. Union over the pairs `{(σ, A) | STIdiff σ ⊆ A}` (`Fintype.card ≤ 2^k · 2^k`), per-pair failure exponent `D₁ + 1`, `4^k N^{-(D₁+1)} ≤ N^{-D₁}` (`nzEnd_ev_union`); collapsed window `s n = v n`: `G = univ` (`nzEnd_collapse`).
7. Deviations from the ticket's list 1(b): `hΔη` is not proved, because `budgetNZN` (`QtNonzero.lean:872`) has no `Δη` premise; `nzEnd_ev_union` takes the constant `4^k` as a parameter.
8. Instances (§6): `szB` (`d = 3, L = 4, W = n + 4, ilambda = 1`), `s ≡ 15/16`, `t ≡ 31/32`, `v ≡ 31/32` (`s < v`, `Δ > 0`: `window_nondegenerate`) resp. `v ≡ 15/16` (`window_collapsed`), `E ≡ 1/2`, `κ = 1`, `τ = 1/2` (`rangeCond_tB`, new: `N^{-1/2} ≤ 1/64` from `szB_size_ge`), `k = 3`, `σ = sig3`, `Λ = Φ_i = Φc ≡ 1`, `ε₀ = 1/10`, `D₁ = 1`, grid `KB C_K`. (1) `asymp_instance`; (2) instances of H1–H6, union, range monotonicity, `hη`, `hδ`, `Δ ≤ N^{-C_K}` and `KΔ ≤ 1` (`grid_instance`), the per-`n` operator bound of `nzUgen_holds` (`hop_instance`), at the endpoint's exponents (`ε₁ = 1/80`, `D'' = 61`, `D_Y = 5`, `cA = 8`); (3) `assembly_instance` at `A = {0, 1}` and `A = univ`; (4) `nzEnd_instance` (`k = 3`, examples at `k = 2, 4`) and `nzEnd_instance_collapsed` apply `nzGridEndN` with every premise discharged; (5) the statement script above. `C` of `nzUgen_holds` stays abstract (`Classical.choose`); every `n` comes from `Filter.Eventually.exists`; the good-walk and projected-initial hypotheses stay in the conclusion (S3-22b's).
9. No RBM1D/RBM2D file was read, built or diffed; §0, §1, §3 hold copies of private helpers of the merged `NQEndLin.lean` (last commit `cef761a`; the source line is in each docstring).

## (c) Verified Mathlib names used (one `#check`-based line each, `mathlib3.lean`: explicit binder types joined by →, implicit and instance binders omitted; none was found absent)
```
Real.rpow_le_rpow_of_nonpos : 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_le_rpow_of_exponent_le : 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.log_le_rpow_div : 0 ≤ x → 0 < ε → Real.log x ≤ x ^ ε / ε
Real.sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
Real.toNNReal_pos : 0 < r.toNNReal ↔ 0 < r
NNReal.coe_pos : 0 < ↑r ↔ 0 < r
tendsto_rpow_atTop : 0 < y → Filter.Tendsto (fun x => x ^ y) Filter.atTop Filter.atTop
Finset.sum_pos : ∀ i ∈ s, 0 < f i → s.Nonempty → 0 < ∑ i ∈ s, f i
Finset.sup'_le : s.Nonempty → β → α → ∀ b ∈ s, f b ≤ a → s.sup' H f ≤ a
Finset.card_le_univ : Finset α → s.card ≤ Fintype.card α
Fintype.card_subtype_le : α → Prop → Fintype.card { x // p x } ≤ Fintype.card α
Fintype.card_finset : Fintype.card (Finset α) = 2 ^ Fintype.card α
MeasureTheory.measureReal_iUnion_fintype_le : β → Set α → μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p)
MeasureTheory.measureReal_empty : μ.real ∅ = 0
Set.compl_iInter : ι → Set β → (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ
Filter.eventually_all : (∀ᶠ (x : α) in l, ∀ (i : ι), p i x) ↔ ∀ (i : ι), ∀ᶠ (x : α) in l, p i x
LinearMap.continuous_of_finiteDimensional : E →ₗ[𝕜] F' → Continuous ⇑f
Continuous.comp_stronglyMeasurable : Continuous g → MeasureTheory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun x => g (f x)
pi_norm_le_iff_of_nonneg : 0 ≤ r → ‖x‖ ≤ r ↔ ∀ (i : ι), ‖x i‖ ≤ r
pow_le_pow_right₀ : 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n
sub_le_comm : a - b ≤ c ↔ a - c ≤ b
inv_anti₀ : 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹
Nat.le_ceil : R → a ≤ ↑⌈a⌉₊
mul_le_of_le_one_right : 0 ≤ a → b ≤ 1 → a * b ≤ a
Filter.Eventually.exists : ∀ᶠ (x : α) in f, p x → ∃ x, p x
```

## (d) Open issues and paper-delta candidates
- Thresholds: every `∀ᶠ n` threshold is existential; at `szB` the binding row is H2 (section (a): `log10 N₀ = 57.2 / 107.9 / 142.5` at `C = 1 / 3380 / 10⁶`); the instances take `n` from `Filter.Eventually.exists`. `C_K = 204` at `k = 3` (section (a)): the grid size `K ≈ N^{204}` is a function value, never summed.
- `hΔη` of the ticket's list 1(b) is not needed (`budgetNZN` has no `Δη` premise); not proved.
- S3-22b's obligations: the good-walk event (`GridGoodNConcl` at `Φ := Φc`, `Γ = N^{ε₁}`, `τ' = 1`, `D' = D'' + 1`, intersected with `NQLinConcl` at `ε := ε₁`), the projected initial hypothesis from `STLK s` at `ε₁/2` (`norm_zeroModeSet_le`, `2^k ≤ N^{ε₁/2}`), the per-time transfer and the lift; `STCaseII s t` is the regime of every section `[s, v]`. `STOeqQtNZ'` stays owed (`Test/Axioms.lean:126`) until S3-22c.
- `T2284a` (statement): the case-(ii) endpoint (`3_5:1903-1916`) is proved on the grid for `Q^{(A)}(𝓛−𝒦)^{(k)}`, every `σ` and every `A ⊇ I_diff(σ)`, with the loss-free EK-5 kernel (`κ ≡ C`, `εK ≡ 0`), the class "fixed points of `Q^{(A)}`", `GoodSetN` at a free crude level `Φc` (only its `STeeM` clause) and `GoodLinN` at `Φ₁ Φ₂ Φ₃`; right side `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`, degree 1 in the levels, no `Φ²`, no `Φc`.
- `T2284b` (exponents): `D'' = 2(k+2)/𝔠 + 1` (O4; `2k + 4d + 10` makes H4 false), `D' = D'' + 1`, `ε₁ = εq = ε₀'/8`, `ε₀' = min ε₀ 1`, `τ' = 1`, `C_K = D₁ + 2(C_P^* + 2k + 2) + D'' + 16k + 40`; "`N` large enough" is the eventual statement `∀ᶠ n`, thresholds not computed.
- `T2284c` (initial assumption): taken on the projected loops `‖(Q^{(A)}(𝓛−𝒦))_{s,σ,a}‖ ≤ N^{ε₁} B_s^k` for all `σ`, `A ⊇ I_diff(σ)` (the paper's `(Eq:L-KGt+IND)` at `s` with `(normQA2)` implicit, `3_5:1902`).
- `T2284d` (window): the collapsed window `v_n = s_n` is a separate case (`G = univ`, `H_K = H_0`), where `hc_pos` of the assembly fails.
- `T2284e` (statement): one event `G`, `P(Gᶜ) ≤ N^{-D₁}`, serves all `σ` and all `A ⊇ I_diff(σ)` simultaneously (union over `≤ 4^k` pairs, per-pair exponent `D₁ + 1`); the per-time statement is S3-22b's.
