Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 09:12:18 UTC 2026

### (i) Exponent table
Targets as in the ticket: 3 `zeroModeSet_idem`, 4 `nzUgen`, 5 `nz_hker`, 6 drift, 7 Azuma proxy, 8 `Y`-moments, 9 budget. `N = sz.size n`, `x = ln N`, `𝔠`: `W ≥ N^𝔠`.

| quantity | value | constraint | slack |
|---|---|---|---|
| `C` (T4,5,7,9) | EK-5 `Ci^k`, `∃` after `(d,k,Λg,κ')`; scan: `C ≤ 4.45 / 8.90 / 88.1` (`k=2/3/6`, `g ≤ 1`, `L ≤ 24`), `≤ 15.0 / 25.8 / 3380` (`g=2`) | `‖Q^{(A)}𝒰X‖ ≤ C‖X‖`, `Σ_b|κ_b| ≤ C` | no loss in `L`, `N`, `(1-w)/(1-v)`; instance needs `C ≥ 4.2568` |
| window (T4) | `0≤v`, `1-g²/L² ≤ v ≤ w < 1`, `0<g≤Λg`, `κ'≤Im mE E`, `|E|<2`, `3≤L`, `A ⊇ I_diff` | the EK-5 hypotheses at `m = mE E` (`‖m‖=1`, `norm_mE`) | `g ≥ L`: window starts at `v=0` (scan rows `g=L,2L`) |
| `Σ_{b'}|q_{bb'}|` of `Q^{(A)}` | `≤ 2^{|A|}`; observed `1.9688` (`|A|=1`), `3.8760` (`|A|=2`) | T6 level `2^{|A|}`, T9 `cA`, T8 | `1.016`, `1.032` |
| `Y` levels (T8) | `4^{|A|+1}v`, `16^{|A|+1}w`; sharp `4^{|A|}`, `16^{|A|}` | `(Σ|q|)² ≤ 4^{|A|}`, `(Σ|q|)⁴ ≤ 16^{|A|}` | factors 4, 16 (`v,w ≥ 0` is forced by `YMomentBoundsN` once some `j<m≤K` exists); observed `15.02 ≤ 16 ≤ 64`, `225.7 ≤ 256 ≤ 4096` |
| proxy (T7) | `cQVNZN = Δ·k·C²(Γ(ΓΛ)B_{u_j}^{2k}/η_{u_j} + W^{-D''})` | `hδ: W^{-D'} + eeShiftErrN(u_j,u_{j+1}) ≤ W^{-D''}`; `STeeM` clause at `u_j`, shift to `u_{j+1}` (any `σ`, Hermitian) | no ratio factor, no far part; `k` from `QVPropagatedN` |
| drift (T6) | `2^{|A|}·Γ²((k-2)Φ₁+Φ₂+Φ₃)B_{u_j}^k/η_{u_j}` | `(normQA2)` × `dDriftLinN` | none lost |
| `ε₁ = ε_q = ε₀/8`, `ε₀ ∈ {1/10,1/100}` | `Γ = N^{ε₁}` | H1 `C N^{ε₁} ≤ N^{ε₀}/6`; H2 `C cA k Γ² Im^{-1} ln N ≤ N^{ε₀}/6`; H3 `N^{ε_q} C Γ √(k Im^{-1} ln N) ≤ N^{ε₀}/12` | exponents `7ε₀/8`, `3ε₀/4` (vs `ln N`), `3ε₀/4` (vs `√ln N`); crossovers in (ii) |
| `D''` (free real) | `D'' = 2(k+2)/𝔠` | H4 `N^{ε_q} N^k C √(k W^{-D''}) ≤ N^{ε₀}/12`: coefficient of `x` is `ε_q + k - 𝔠D''/2 - ε₀` | `-(2 + 7ε₀/8)`. The ticket's `2k+4d+10` gives (at `ε₀=1/10`) `+0.246` (`𝔠=1/3,k=6`), `+0.579` (`𝔠=1/6,k=3`): H4 false |
| `D_Y = D_t = k+2` | | H5 `N^k N^{-D_Y} ≤ N^{ε₀}/6`; H6 `cA N^k N^{-D_t} ≤ N^{ε₀}/6` | `2 + ε₀` (H6: `- log_N cA`) |
| `C_K` | `K ≤ ⌈N^{C_K}⌉`, `Δ ≤ N^{-C_K}`, `AssembledN`: `D₁+4D+k+2C_P+8 ≤ C_K` | `hstep Σ(1+(1-u_K)^{-1})^k stepErrN ≤ N^{-D_t}`: `C_K ≥ 4k+18+2D_t` (worst `1-v = 1/N`) | `-0.83..-0.87` there, `+0.13..+0.17` at `4k+16+2D_t`; upper side free |
| `B_v ≥ N^{-1}`, `B_s ≤ B_v` | `Bparam` zero-mode term `(L^d(1-t))^{-1} ≥ L^{-d}` times `W^{-d}`, `0≤t<1`; `STBctl_mono` | absorbs `N^{-D_Y}`, `N^{-D_t}`, `√(kW^{-D''})` and `X0` | exact; instance `B_v = 0.022964 ≥ 1/N` |
| budget split | `1/6 (X0) + 1/6 (drift) + 1/12+1/12 (QV) + 1/6 (D_Y) + 1/6 (step) = 5/6` | `≤ 1` on `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k`; uses `Λ≥1`, `Φ_i≥0`, `cA≥0`, `v-s ≤ 1` | `1/6` |
| `hlog` | `Σ_j Δ/η_{u_j} ≤ Im^{-1} ln N` | window fact `(1-s)/(1-v) ≲ N/e` (a premise of T9; owed to S3-22a) | instance `0.6345 ≤ 8.318` |
| R2* | `Λ = nqFlowLam XL B_s k p`; `Λ^{1/2}` = first summand of `STbootRHS … B_s` | identity | none lost; `max 1 Λ` is dominated by `Σ XL ≥ 1` |

### (ii) Concrete nondegenerate instance
Scripts (no Lean) in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2274/`; command: `python3 t2274_preflight.py; python3 g2b.py; python3 g3c.py; python3 dpp.py | grep -E "c=0.333 k=6 eps0=0.1 |c=0.167 k=3 eps0=0.1 |c=0.167 k=6 eps0=0.1 "`.
- T3, T4, T5: `d=3, L=4, g=1 (Λg=1, κ'=1/2 ≤ Im mE 0 = 1), E=0, v=15/16=1-g²/L², w=31/32, k=3, σ=(+,-,+), A=I_diff={0,1}, X=δ_0`. External hypotheses (`Prop5Short`, `Prop8ZeroMode`): none open (`prop5Short_holds`, `prop8ZeroMode_holds` unconditional), so no limit computation. T5 at `K=1`, `u_0=15/16`, `u_1=31/32` (the ticket's `u ≡ 15/16` collapses the window to `𝒰 = id`), `X = Q^{(A)}δ_0`.
- T6, T7: the `NQLinInst` data of the ticket. Its `∃κ` row at `sz0` (`L=4, g=1/64, E=1/2, u_1=1/128, u_4=1/32`) cannot come from T4 (`1-g²/L² = 0.999985 > u_1`); it comes from `‖𝒰‖ ≤ ((1-s)/(1-t))^k` and `‖Q^{(A)}‖ ≤ 2^{|A|}`: `Σ|κ| = 3.9842 ≤ 4.2974`.
- T8: `Y_j = ζ_j δ_0`, `ζ_j ~ N(0,1)` independent of `F_j` (mean 0, `Eζ²=1`, `Eζ⁴=3`), `(u_{j+1},u_m) = (121/128, 124/128)`; levels `v=c0²`, `w=3c0⁴` (`Y ≡ 0` also admissible).
- T9: `szB, n=0` (`L=4, W=4, lam=1, N=4096`), `E=0`, `K=4, s=15/16, v=31/32`, `k=3`, `C=5`, `cA=4`, `Λ=1`, `Φ_i=1`. `K=4` forces `D_t<0`, `ε₀=14` (finite-`N` witness as the merged `budgetNonAltLinN_instance`); the asymptotic rows are the H1-H6 table.

```
== G1 (d=3; exact Fourier diagonalisation; ||.|| = infty->infty = sum_x |kernel(x)|; tensor norm = product of one-index norms)
 max over E in{0,1.5}, w in{v,(1+v)/2,1-1e-2(1-v),1-1e-4(1-v)}, v=max(0,1-g^2/L^2), all sigma, all A>=I_diff
  [B] fixed g<=Lambda_g:   L     g | max|PU(1)| max|U(m^2)| |  C(k=2)   C(k=3)   C(k=6)
                         4  0.50 |    1.9997     1.0109 |    3.999    7.858     63.94
                         8  0.50 |    2.0098     1.0028 |    4.039    8.059     65.91
                        24  0.50 |    2.0130     1.0003 |    4.052    8.103     66.54
                         4  1.00 |    2.0185     1.1562 |    4.074    8.022     67.64
                         8  1.00 |    2.0940     1.0391 |    4.385    8.755     84.30
                        24  1.00 |    2.1095     1.0043 |    4.450    8.902     88.13
                         4  2.00 |    2.5805     3.8739 |   15.007   25.797   3379.72
                         8  2.00 |    2.7474     1.7186 |    7.548   16.665    430.05
                        24  2.00 |    2.7992     1.0799 |    7.836   15.971    481.10
  [A] ticket grid g=cL (g unbounded, so Lambda_g unbounded):
                         4  1.00 |    2.0185     1.1562 |     4.07     8.02      67.6
                        12  3.00 |    4.1048     2.6558 |     16.8     48.2  4.78e+03
                         4  4.00 |    5.5150    48.2707 | 2.33e+03 1.47e+03  1.27e+10
                        12 12.00 |   41.7919   414.6096 | 1.72e+05 7.24e+05  5.08e+15
  single index L=8,g=1,mu=1:  (1-v)/(1-w)=1: |U(1)|=1.00 |PU(1)|=1.996 ; (1-v)/(1-w)=2: |U(1)|=2.00 |PU(1)|=2.018 ; (1-v)/(1-w)=100: |U(1)|=100.00 |PU(1)|=2.092 ; (1-v)/(1-w)=10000: |U(1)|=10000.00 |PU(1)|=2.094
  check FFT kernel = (1-v mu S)(1-w mu S)^-1 built from SB definition (l1 distance 1): max|diff|=1.7e-15
  sigma=(+-),A={0,1}: |Q^A U - tensor(PU)|=3e-14; ||Q^A U||=3.9692; duality |(Q^A U X)(0)|=3.9692 = sum|kappa|=3.9692 (|X|<=1.000); |QQ-Q|=0e+00, |QU-UQ|=2e-15
  sigma=(++),A={0}   : |Q^A U - tensor(PU)|=6e-16; ||Q^A U||=2.1110; duality |(Q^A U X)(0)|=2.1110 = sum|kappa|=2.1110 (|X|<=1.000); |QQ-Q|=0e+00, |QU-UQ|=1e-17
  INSTANCE d=3 L=4 g=1 E=0 v=15/16 w=31/32 sigma=(+,-,+): I_diff=[0, 1] (card 2), A=I_diff, mu=(1,1,(-1+0j))
     one-index norms |PU(1)|,|PU(1)|,|U(m^2)| = 1.9923 1.9923 1.0725 ; ||Q^A U||=4.2568 ; ||Q^A U delta_0||_inf=0.9919 (||delta_0||=1)
  T7 row premise at sz0 (L=4,g=1/64,E=1/2,u_1=1/128,u_4=1/32,A=I_diff): sum|kappa|=3.9842 <= 2^|A| ((1-u1)/(1-u4))^k = 4.2974 ; EK-5 window 1-g^2/L^2=0.999985 > u_1: target 4 not applicable there
  T8 instance Y_j=zeta_j delta_0: v=c0^2=1.0840, w=3c0^4=3.5254 ; Q^A-edge max_b|(Q^A U delta_0)_b|^2=0.9724 <= 4^(|A|+1) v=69.38 ; 3 max^4=2.8369 <= 16^(|A|+1) w=14440.1
== G2 asymptotic rows (x=ln N): eps1=eq=eps0/8, W=N^(1/6), D''=12(k+2), D_Y=D_t=k+2, cA=2^k; Im mE >= sqrt(kappa/2)/2
   worst log10 N0 (row true for all N>=N0) over C in{1,1e3},k in{2,3,6},kappa in{1/10,1/100}:   eps0=1/10   eps0=1/100
   H1  C N^e1 <= N^e0/6                                  43.1        431.0
   H2  C cA k N^2e1 Im^-1 lnN <= N^e0/6                 144.0      1.53e+3
   H3  N^eq C N^e1 sqrt(k Im^-1 lnN) <= N^e0/12          85.9        910.0
   H4  N^eq N^k C sqrt(k W^-D'') <= N^e0/12              2.16         2.29
   H5  N^k N^-D_Y <= N^e0/6                             0.456        0.456
   H6  cA N^k N^-D_t <= N^e0/6                           1.29         1.29
   truth H1..H6 at log10N=1,2,3,6 (C=1e3,k=6,kappa=1/100; same string for eps0=1/10 and 1/100): FFFFTF  FFFFTT  FFFTTT  FFFTTT
   hstep, worst 1-v=1/N, N=1e30, D_t=k+2: log_N(sum)+D_t at C_K=4k+16+2D_t / +2 (<=0 closes): k=2: 0.133 / -0.867; k=3: 0.144 / -0.856; k=6: 0.167 / -0.833
== G2 concrete: d=3 L=4 W=4 lam=1 (szB n=0) N=4096 E=0 k=3 K=4 s=15/16 v=31/32 (Delta=1/128); C=5 cA=4 Lambda=1 Phi_i=1 tauK=0 D''=13 D_Y=5
   free: eps0=14.0 eps1=epsq=eps0/8 D_t=-9.0 Gamma=N^eps1 X0=N^eps1 B_s^3; B_s=0.0186121 B_v=0.022964 >= 1/N=0.000244141
   hlog  sum_j Delta/eta_j <= Im^-1 ln N        0.6345     <= 8.318      OK
   hX0   X0 <= N^e1 B_s^k                       13.52      <= 13.52      OK
   hstep sum fac*stepErr <= N^-Dt               1.446e+32  <= 3.245e+32  OK
   H1 C N^e1 <= N^e0/6                          1.049e+7   <= 6.236e+49  OK
   H2 C cA k Gam^2 Im^-1 lnN <= N^e0/6          2.195e+15  <= 6.236e+49  OK
   H3 N^eq C Gam sqrt(k Im^-1 lnN) <= N^e0/12   1.098e+14  <= 3.118e+49  OK
   H4 N^eq N^k C sqrt(k W^-D'') <= N^e0/12      1.524e+14  <= 3.118e+49  OK
   H5 N^k N^-D_Y <= N^e0/6                      5.96e-8    <= 6.236e+49  OK
   H6 cA N^k N^-D_t <= N^e0/6                   8.92e+43   <= 6.236e+49  OK
   assembledRHSNZN = 5.7842e+32 <= N^e0 (Lam^(1/2)+Phi1+Phi2+Phi3) B_v^3 = 1.8124e+46 : True
   five pieces / (N^e0 B_v^k): 1.49e-44 2.98e-37 5.46e-38 1.91e-64 1.28e-13   (proof budget 1/6,1/6,1/6,1/6,1/6; total 5/6)
== (iii) R2*: Lambda=XL(2k-1)(XL(4p)/B_s)^(1/2p): max rel.err of Lambda^(1/2) vs first summand B_s^(-1/4p) XL(2k-1)^(1/2) XL(4p)^(1/4p) of STbootRHS over 1000 random draws = 3.1e-61
== G3 (q = matrix of Q^(A) on k=2 tensors; heavy-tailed and sign-aligned real y)
  d=1 L=4 k=2 A=(0,)   samples=100000: max_b sum|q|=1.5000 (2^|A|=2); max ratio-1 of (ReQy)^2/[sum|q| sum|q|(Re y)^2]=6.7e-16, of (ReQy)^4/[(sum|q|)^3 sum|q|(Re y)^4]=8.9e-16; (sum|q|)^2=2.250<=4^|A|=4, (sum|q|)^4=5.06<=16^|A|=16
  d=1 L=4 k=2 A=(0, 1) samples=100000: max_b sum|q|=2.2500 (2^|A|=4); max ratio-1 of (ReQy)^2/[sum|q| sum|q|(Re y)^2]=1.8e-15, of (ReQy)^4/[(sum|q|)^3 sum|q|(Re y)^4]=2.9e-15; (sum|q|)^2=5.062<=4^|A|=16, (sum|q|)^4=25.63<=16^|A|=256
  d=3 L=4 k=2 A=(0,)   samples=4000: max_b sum|q|=1.9688 (2^|A|=2); max ratio-1 of (ReQy)^2/[sum|q| sum|q|(Re y)^2]=8.4e-15, of (ReQy)^4/[(sum|q|)^3 sum|q|(Re y)^4]=1.5e-14; (sum|q|)^2=3.876<=4^|A|=4, (sum|q|)^4=15.02<=16^|A|=16
  d=3 L=4 k=2 A=(0, 1) samples=4000: max_b sum|q|=3.8760 (2^|A|=4); max ratio-1 of (ReQy)^2/[sum|q| sum|q|(Re y)^2]=5.8e-13, of (ReQy)^4/[(sum|q|)^3 sum|q|(Re y)^4]=9.5e-13; (sum|q|)^2=15.023<=4^|A|=16, (sum|q|)^4=225.70<=16^|A|=256
 == H4 coefficient e of ln N (>0: row false): ticket D''=2k+4d+10 vs D''=2(k+2)/c, W=N^c
 c=0.333 k=6 eps0=0.1   e(ticket)=+0.246  e(D2=48)=-2.087
 c=0.167 k=3 eps0=0.1   e(ticket)=+0.579  e(D2=60)=-2.087
 c=0.167 k=6 eps0=0.1   e(ticket)=+3.079  e(D2=96)=-2.087
```

### Verdicts
- T1 `cQVNZN`, T2 `assembledRHSNZN`: PASS (vocabulary; T2's five terms are the five pieces evaluated in G2).
- T3: PASS (`P^{(i)}` averaging projections that commute; brute force `|Q^AQ^A - Q^A| = 0`).
- T4: PASS (EK-5 hypotheses are exactly T4's at `m=mE E`; row-sum form by `∞→∞` duality, verified `Σ|κ| = ‖Q^AU‖ = 3.9692 / 2.1110`; `‖Q^AU‖` bounded in `L` at fixed `g`, grows with `g`: `C = C(Λg)`).
- T5: PASS (`𝒰X = 𝒰Q^AX = Q^A𝒰X` for `w ∈ [0,1)`). T6: PASS. T7: PASS (needs `Σ|κ| ≤ C`, `0≤C`, `Γ,Λ ≥ 0`; no `hwL`, `hWt`, `hσ`). T8: PASS. T9: PASS (all 9 hypotheses and the conclusion hold at the instance; H1-H6 eventually true).
- G1 PASS, read at fixed `g ≤ Λg`: `C` saturates in `L` (`k=6`, `g=1`: `67.6 → 88.1`; `g=2`: `3380 → 481`). The ticket's stop rule "growth in `L` at fixed `g/L`" fires only in scan [A], where `g = cL` is unbounded, outside `g ≤ Λg`; this is not a defect of T4. G2 PASS with `D'' = 2(k+2)/𝔠`. G3 PASS: `(Re Σ q y)² ≤ (Σ|q|) Σ|q|(Re y)²` and the fourth-power Hölder form hold with ratio `-1 ≤ 1e-12` (`q` real, so `Re` passes through; `Σ|q| ≤ 2^{|A|}` from `Q^{(A)} = Σ_{B⊆A}(-1)^{|B|}P^{(B)}`); samples: `10^5` at `d=1`, `4000` at `d=3` (not `10^5`).
- Consumer fit (iv): T5-T8 are the fields of `AssembledN` (`hker`, `hdrift`, `hDcls` by T3, `hY`, `SubGaussStopN`); T9 is its right side at `m = K n`. R2* (iii): PASS (row R2*). §29/§45: windows are explicit per-`n` premises; `0 ≤ v` carried; no `L^d ≤ W^K`; no `Prec`.

## (b) Script output (stage 1b; report assembled Tue Oct  6 10:01:12 UTC 2026)
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2274`, branch `t/T2274`, commits after `b2529ba`: `d60acad a4e1cde 01f571f 67f6489`. Scratch scripts: `<scratchpad>/T2274/`.
```
### date / commit
Tue Oct  6 09:56:45 UTC 2026
67f6489 T2274: rename nz_hker_instance (short-name clash with NQGood1Inst.hker_instance)
uncommitted files: 0
### build
$ lake build RBM3D.Induction.QtNonzero 2>&1 | tail -3
info: RBM3D/Induction/QtNonzero.lean:1725:0: 'RBM.Ind.QtNonzeroInst.yMoment_random_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzero.lean:1726:0: 'RBM.Ind.QtNonzeroInst.budgetNZN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3845 jobs).
### axioms (script `axioms2.lean`: `collectAxioms` of every non-private, non-internal constant of the module)
$ lake env lean axioms2.lean
20 public declarations: 9 targets (`RBM.zeroModeSet_idem`, `RBM.Ind.{cQVNZN, assembledRHSNZN, nzUgen_holds, nz_hker, nz_hdriftN, subGaussStop_nzN, yMomentBounds_nzN, budgetNZN}`),
  10 instance theorems `RBM.Ind.QtNonzeroInst.*`, 1 compiler matcher `subGaussStop_nzN.match_1_1`
declarations whose axioms are not within [propext, Classical.choice, Quot.sound]: 0
### statement script `stmt.lean` = `docs/tickets/checks/T2274-check.lean` + `import RBM3D.Induction.QtNonzero` + these examples (inside `namespace RBM.Ind.T2274Check`):
example : T2274_zeroModeSet_idem := @RBM.zeroModeSet_idem
example : T2274_nzUgen := @RBM.Ind.nzUgen_holds
example : T2274_nz_hker := @RBM.Ind.nz_hker
example : T2274_nz_hdriftN := @RBM.Ind.nz_hdriftN
example : T2274_subGaussStop_nzN := @RBM.Ind.subGaussStop_nzN
example : T2274_yMomentBounds_nzN := @RBM.Ind.yMomentBounds_nzN
example : T2274_budgetNZN := @RBM.Ind.budgetNZN
example : @RBM.Ind.cQVNZN = @RBM.Ind.T2274Check.cQVNZN := rfl
example : @RBM.Ind.assembledRHSNZN = @RBM.Ind.T2274Check.assembledRHSNZN := rfl
$ lake env lean stmt.lean; echo exit=$?
exit=0 (output lines containing error: 0)
### registry pre-check
$ lake env lean pre_after.lean  (import RBM3D; import RBM3D.Induction.QtNonzero; #assert_rbm_axioms)
exit=0
before: axiom audit: 7934 theorems, 2615 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
after:  axiom audit: 7951 theorems, 2617 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
all other lines (ledgers, premises, certificates) identical: yes
### target statements, extracted from the file by `extract.py` (text up to the first `:=`, whitespace-normalised)
[1 cQVNZN] (line 224)
def cQVNZN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (C Γ Λ D'' : ℝ) (j : ℕ) : ℝ≥0
[2 assembledRHSNZN] (line 233)
def assembledRHSNZN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (C cA : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y τK εq X0 : ℝ) : ℝ
[3 zeroModeSet_idem] (line 97)
theorem zeroModeSet_idem (d L : ℕ) [NeZero L] (n : ℕ) (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) : zeroModeSet d L A (zeroModeSet d L A T) = zeroModeSet d L A T
[4 nzUgen_holds] (line 299)
theorem nzUgen_holds : ∀ (d k : ℕ), 3 ≤ d → 2 ≤ k → ∀ Λg κ' : ℝ, 0 < Λg → 0 < κ' → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g E : ℝ, 0 < g → g ≤ Λg → |E| < 2 → κ' ≤ (mE E).im → ∀ v w : ℝ, 0 ≤
    v → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ v → v ≤ w → w < 1 → ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A → (∀ X : (Fin k → Zd d L) → ℂ, ‖zeroModeSet d L A (Ugen d L g E σ v w X)‖ ≤ C * ‖X‖) ∧ ∀
    a : Fin k → Zd d L, ∃ κ : (Fin k → Zd d L) → ℂ, (∀ X : (Fin k → Zd d L) → ℂ, zeroModeSet d L A (Ugen d L g E σ v w X) a = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C
[5 nz_hker] (line 327)
theorem nz_hker : ∀ {d k : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ) (K : ℕ) (C : ℝ), 0 ≤ C → |E| ≤ 2 → (∀ i ≤ K, 0 ≤ u i) → (∀ i ≤ K, u i < 1) → (∀ i m, i
    ≤ m → m ≤ K → ∀ X : (Fin k → Zd d (sz.L n)) → ℂ, ‖zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X)‖ ≤ C * ‖X‖) → ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ)
    (M δ : ℝ), 0 ≤ M → 0 ≤ δ → (∀ b, ‖X b‖ ≤ M) → zeroModeSet d (sz.L n) A X = X → ∀ a, ‖Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X a‖ ≤ C * M + 0 * δ
[6 nz_hdriftN] (line 358)
theorem nz_hdriftN : ∀ {d : ℕ} (sz : Sizes d) {n k : ℕ}, 2 ≤ k → ∀ (σ : Fin k → Bool) (A : Finset (Fin k)) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ), (∀ ω j, j < τ ω → pathH
    sz s v K n j ω ∈ GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) → ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n), ‖zeroModeSet d (sz.L n) A (driftTensorN sz n (E n)
    (gridTime s v K n j) (pathH sz s v K n j ω) σ) b‖ ≤ 2 ^ A.card * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
[7 subGaussStop_nzN] (line 417)
theorem subGaussStop_nzN : ∀ {d k : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin k → Bool) (A : Finset (Fin k)) (C Γ Λ Φ τ' D' D'' : ℝ) (τ : PathΩ sz → ℕ), 2 ≤ k → (∀ n, |E n| < 2) →
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) → 0 ≤ C → 0 ≤ Γ → 0 ≤ Λ → (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) → (∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime
    s v K n j) k Γ Λ Φ τ' D') → ∀ m, m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m → (∃ κ : (Fin k → Zd d (sz.L n)) → ℂ, (∀ X : (Fin k → Zd d (sz.L n)) → ℂ, zeroModeSet d (sz.L n) A (Ugen d
    (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n m) X) a = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C) → ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k
    (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') → SubGaussStopN sz (E n) σ (gridTime s v K n) τ (fun j ω => zeroModeSet d (sz.L n) A (ZvecN sz E s v K n j σ ω)) m a j
    (cQVNZN sz E s v K n k C Γ Λ D'' j)
[8 yMomentBounds_nzN] (line 731)
theorem yMomentBounds_nzN : ∀ {d : ℕ} (sz : Sizes d) {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (K : ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (v w : ℕ → ℝ), |E| ≤ 2 → (∀ i ≤ K, 0 ≤ u i) → (∀ i ≤ K, u i < 1) → YMomentBoundsN sz E σ u τ K Y v w → YMomentBoundsN sz E σ u τ K (fun j ω => zeroModeSet d (sz.L n) A (Y j ω)) (fun j => 4 ^
    (A.card + 1) * v j) (fun j => 16 ^ (A.card + 1) * w j)
[9 budgetNZN] (line 872)
theorem budgetNZN : ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (C cA : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ), 2 ≤ k → 0 < C → 0 ≤ cA → 0 ≤ ε₁ → |E n| < 2 → 0 ≤
    s n → s n ≤ v n → v n < 1 → K n ≠ 0 → Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁ → 1 ≤ Λ n → 0 ≤ Φ₁ n → 0 ≤ Φ₂ n → 0 ≤ Φ₃ n → ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
    (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) → X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k → ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * stepErrN d (sz.L
    n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) (gridStep s v K n) (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t)
    → C * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 → C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ)
    ^ ε₀ / 6 → ((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ * Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 → ((sz.size n
    : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k * (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 → ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^
    (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 → cA * ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 → assembledRHSNZN sz E s v K n k C cA Γ Λ Φ₁ Φ₂ Φ₃ D''
    D_Y τK εq X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k
### vocabulary against check §2 (`vocabdiff.py`, `difflib.unified_diff` of the definition text)
def cQVNZN: 5 lines in the file, 5 in the check; diff lines: 0
def assembledRHSNZN: 12 lines in the file, 12 in the check; diff lines: 0
### compiled nonempty instances (statements by `inst_extract.py`; all proved in the file; data in the narrative, point 9)
[line 1193]
theorem idem_instance : zeroModeSet 3 4 (STIdiff sig3) (zeroModeSet 3 4 (STIdiff sig3) qnDelta) = zeroModeSet 3 4 (STIdiff sig3) qnDelta ∧ qnDelta ≠ 0 ∧ zeroModeSet 3 4 (STIdiff sig3) qnDelta ≠
    qnDelta ∧ zeroModeSet 3 4 (STIdiff sig3) qnDelta ≠ 0
[line 1217]
theorem nzUgen_instance : ∃ C : ℝ, 0 < C ∧ qnDelta ≠ 0 ∧ ‖zeroModeSet 3 4 (STIdiff sig3) (Ugen 3 4 1 0 sig3 (15 / 16) (31 / 32) qnDelta)‖ ≤ C * ‖qnDelta‖ ∧ ∃ κ : (Fin 3 → Zd 3 4) → ℂ, (∀ X : (Fin 3 →
    Zd 3 4) → ℂ, zeroModeSet 3 4 (STIdiff sig3) (Ugen 3 4 1 0 sig3 (15 / 16) (31 / 32) X) 0 = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C
[line 1260]
theorem nz_hker_instance : ∃ C : ℝ, 0 < C ∧ zeroModeSet 3 (szB.L 0) (STIdiff sig3) qnDelta ≠ 0 ∧ ∀ i m, i ≤ m → m ≤ 1 → ∀ a : Fin 3 → Zd 3 (szB.L 0), ‖Ugen 3 (szB.L 0) (szB.lam 0) 0 sig3 (qnU i) (qnU
    m) (zeroModeSet 3 (szB.L 0) (STIdiff sig3) qnDelta) a‖ ≤ C * ‖zeroModeSet 3 (szB.L 0) (STIdiff sig3) qnDelta‖ + 0 * 0
[line 1289]
theorem nz_hdrift_instance (A : Finset (Fin 3)) : ∀ ω j, j < Kg 0 → j < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 ω → ∀ b : Fin 3 → Zd 3 (sz0.L 0), ‖zeroModeSet 3
    (sz0.L 0) A (driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) (pathH sz0 sInst vg Kg 0 j ω) sig3) b‖ ≤ 2 ^ A.card * dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0)
    ((fun _ : ℕ => (12 : ℝ)) 0) (Φ1 0)
[line 1319]
theorem nz_hdrift_level_pos (A : Finset (Fin 3)) : 0 < 2 ^ A.card * dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0) (Φ1 0) ((fun _ : ℕ => (12 : ℝ)) 0) (Φ1 0)
[line 1345]
theorem subGaussStop_nz_instance (A : Finset (Fin 3)) (m : ℕ) (hm : m ≤ Kg 0) (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < m) : SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0 (fun j
    ω => zeroModeSet 3 (sz0.L 0) A (ZvecN sz0 Einst sInst vg Kg 0 j sig3 ω)) m a j (cQVNZN sz0 Einst sInst vg Kg 0 3 (2 ^ A.card * (32 / 31) ^ 3) (Γ4 0) (Λ3 0) 5 j)
[line 1372]
theorem cQVNZN_inst_pos (A : Finset (Fin 3)) {j : ℕ} (hj : j < Kg 0) : 0 < cQVNZN sz0 Einst sInst vg Kg 0 3 (2 ^ A.card * (32 / 31) ^ 3) (Γ4 0) (Λ3 0) 5 j
[line 1412]
theorem yMoment_zero_instance (A : Finset (Fin 3)) : YMomentBoundsN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0 (Kg 0) (fun j ω => zeroModeSet 3 (sz0.L 0) A ((fun (_ : ℕ) (_ : PathΩ sz0) (_ : Fin
    3 → Zd 3 (sz0.L 0)) => (0 : ℂ)) j ω)) (fun _ => 4 ^ (A.card + 1) * 0) (fun _ => 16 ^ (A.card + 1) * 0)
[line 1515]
theorem yMoment_random_instance : ∃ v w : ℕ → ℝ, (∀ j, 0 ≤ v j) ∧ (∀ j, 0 ≤ w j) ∧ YMomentBoundsN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) (fun _ => Kg 0) (Kg 0) qnY v w ∧ YMomentBoundsN sz0 (Einst
    0) sig3 (gridTime sInst vg Kg 0) (fun _ => Kg 0) (Kg 0) (fun j ω => zeroModeSet 3 (sz0.L 0) (STIdiff sig3) (qnY j ω)) (fun j => 4 ^ ((STIdiff sig3).card + 1) * v j) (fun j => 16 ^ ((STIdiff
    sig3).card + 1) * w j) ∧ (∃ ω, qnY 0 ω ≠ 0) ∧ (∃ ω, zeroModeSet 3 (sz0.L 0) (STIdiff sig3) (qnY 0 ω) ≠ 0)
[line 1660]
theorem budgetNZN_instance : assembledRHSNZN sz0 Einst sInst vg Kg 0 3 5 4 Γ4 Λ3 Φ1 (fun _ => 12) Φ1 5 1 (1 / 21) 1 (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) ≤ ((sz0.size 0 : ℕ) : ℝ) ^ (9 : ℝ) * (Λ3 0 ^ ((1 :
    ℝ) / 2) + Φ1 0 + (fun _ : ℕ => (12 : ℝ)) 0 + Φ1 0) * (sz0.Bctl 0 (vg 0)) ^ 3
### name-clash grep (`grep -rn -F <name> RBM3D RBM3D.lean`, hits outside `QtNonzero.lean`)
zeroModeSet_idem:0 cQVNZN:0 assembledRHSNZN:0 nzUgen_holds:0 nz_hker:0 nz_hdriftN:0 subGaussStop_nzN:0 yMomentBounds_nzN:0 budgetNZN:0 QtNonzeroInst:0 idem_instance:0 nzUgen_instance:0 nz_hker_instance:0 nz_hdrift_instance:0 nz_hdrift_level_pos:0 subGaussStop_nz_instance:0 cQVNZN_inst_pos:0 yMoment_zero_instance:0 yMoment_random_instance:0 budgetNZN_instance:0 
### hygiene
sorry/admit/native_decide/axiom/maxHeartbeats hits in the file: 0
files changed vs main: RBM3D/Induction/QtNonzero.lean 
lines in the file:     1726; commits on t/T2274 after b2529ba:        4
set_option lines in the file: 48:set_option linter.style.longLine false 49:set_option linter.unusedSectionVars false 50:set_option linter.unusedVariables false 1387:set_option linter.flexible false in 
ports: none (no RBM1D/RBM2D source; ticket); RBM1D/RBM2D untouched, no diff-stat. Patterns copied from merged RBM3D files (`git log -1`: GridAssemblyN `686cf71`, AzumaProxyN `43ab861`, NQGood2 `cc96b69`, NQLin `d783ee3`, Kernel/Evolution `ff8d36d`):
  `GridAssemblyN.lean:2051` (`hY` at `Y = 0`), `AzumaProxyN.lean:980`, `NQGood2.lean:519`, `NQLin.lean:943,966,1376,1403,1724`, `Kernel/Evolution.lean:131` (`norm_UN_apply_le`).
```

Narrative (every figure from the blocks above or the files).
1. One new file, `RBM3D/Induction/QtNonzero.lean` (1726 lines); `git diff --name-only main...t/T2274` lists only it. No merged file, registry line or `RBM3D.lean` line changed (the root import is the hub's).
2. Targets 1-2 are verbatim (0 diff lines). Targets 3-9 satisfy the seven pinned statements (statement script exit 0). Registry pre-check exit 0: +17 theorems, +2 definitions, all ledger and premise lines unchanged.
3. T3: `Q^{(A)}` is the tensor kernel `(i ∈ A ? projMat : 1)` (merged `zeroModeSet_tensorKer` at the identity kernel), idempotent by `projMat_mul_self`.
4. T4: merged `ekSumDecayNonzero_holds` with the unconditional `prop5Short_holds`, `prop8ZeroMode_holds` (no open hypothesis, hence no limit check); operator form directly; row form: `Q^{(A)}𝒰` is a tensor kernel,
   `κ_b = ∏_i K_i(a_i,b_i)`, `Σ|κ_b| ≤ C` by the `∞→∞` duality (`qtNZ_sum_norm_le_of_bound`, test vector `κ_b⁻¹|κ_b|`).
5. T5 is `zeroModeSet_Ugen` plus the operator bound; T6 is `nqLin_hdriftN` plus `norm_zeroModeSet_le` (`0 ≤ dDriftLinN` is read off the sup bound).
6. T7: `azumaSubGN` with the weights `κ` (`𝒰 Q^{(A)} Z = Σ κ_b Z_b`, `zeroModeSet_Ugen`), `qvPropagatedN`, `Re Σκκ̄ee ≤ (Σ‖κ‖)² max‖ee‖` with `ee(u_{j+1})` from the (D4) clause at `u_j`
   and `norm_STeeM_shiftN_le` + `hδ`; no `hwL`, `hWt`, `hσ`, no ratio weight, no far part.
7. T8: real kernel `qtNZ_q` of `Q^{(A)}`, `Σ|q| ≤ 2^{|A|}`, `qtNZ_comb` (Cauchy-Schwarz twice, linearity and monotonicity of `condExp`); proved `(Σ|q|)²v`, `(Σ|q|)⁴w`, weakened to the pinned `4^{|A|+1}`, `16^{|A|+1}`;
   `v j, w j ≥ 0` are derived from the hypothesis. The pin has no hypothesis on `{j < τ}`; a.e.-measurability of the stopped edges comes from `f = f⁴/g³` (`qtNZ_aesm_of_pow4`).
8. T9: five terms bounded separately, coefficients of `N^{ε₀}B_v^k`: `X0` 1/6, drift 1/6·ΣΦ, QV 1/12·Λ^{1/2} + 1/12, `D_Y` 1/6, step 1/6 (total on `Λ^{1/2}` ≤ 2/3); no `set_option maxHeartbeats` is used.
9. Instances. (1)-(3) at `L = 4`, `g = 1`, `E = 0`, window `(15/16, 31/32)`, `σ = (+,-,+)`, `A = I_diff = {0,1}`, `δ₀` (`(Q^{(A)}δ₀)(0) = (63/64)²`); (3) at `szB`, `K = 1`, `u_i = 15/16 + i/32`, `X = Q^{(A)}δ₀ ≠ 0`.
   (4)-(7) at the merged `sz0` data of `NQLinInst`/`NQGood2Inst` (`L = 4`, `W = 32`, `N = 2^21`, `E = 1/2`, grid `(0, 1/32, 4)`) with the exit time `tau0` (positive at every sample).
   (4) `A = ∅` and `A = I_diff`, plus `2^{|A|}·dDriftLinN > 0`. (5) the `∃κ` premise comes from `qtNZ_row_coarse` (`Σ|κ| ≤ 2^{|A|}((1-u_{j+1})/(1-u_m))³ ≤ 2^{|A|}(32/31)³`), not from (2): as (a) says, the EK-5 window
   `1 - g²/L² = 0.999985` does not contain `u_{j+1} ≤ 1/32`; the proxy is positive (`cQVNZN_inst_pos`). (6) `Y ≡ 0` (the `Y` of the merged `gridAsm_bundle`) and a random `Y_j = ζ_j δ₀`, `ζ_j` the Gaussian increment
   `gridAsm_witZ` (independent increments by `condExp_indep_eq`; levels `R²Eζ_j²`, `R⁴Eζ_j⁴`, `R = (32/31)³`), `Y_0` and `Q^{(A)}Y_0` nonzero at some sample. (7) the `sz0` data of `budgetNonAltLinN_instance`
   (not the `szB` data of (a)(ii)): `C = 5`, `cA = 4`, `ε₀ = 9`, `ε₁ = 2/21`, `D'' = 5`, `D_Y = 1`, `D_t = -5`; `hlog`, `hR` are `NQBudgetInst.hlog_instance`, `hR_instance`.
10. Registry: no line added or removed; `STOeqQtNZ'` stays owed (not concluded here).

## (c) Verified Mathlib names used (script `names.lean`: `Environment.contains`, 63 names, missing: none; one line per group of the non-routine ones)
- `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` weighted Cauchy-Schwarz (T8); the `_eq_mul` form is a deprecated alias
- `Finset.prod_univ_sum`, `Fintype.piFinset_univ` row sum of a tensor kernel as a product (T8, `qtNZ_sum_abs_q_le`)
- `Finset.prod_ite_mem`, `Finset.abs_prod`, `Finset.univ_unique`, `Fin.prod_univ_three` products over `A`, `Unit`, `Fin 3`
- `Complex.re_ofReal_mul`, `Complex.im_ofReal_mul`, `Complex.re_le_norm`, `Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`
- `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm` sup norm on tensors; `LinearMap.continuous_of_finiteDimensional` for `zeroModeSetLin`
- `MeasureTheory.condExp_finsetSum`, `condExp_smul`, `condExp_mono`, `condExp_nonneg` linearity, monotonicity, positivity (T8)
- `MeasureTheory.condExp_indep_eq` conditional expectation of an independent increment (instance (6))
- `MeasureTheory.integrable_finsetSum`, `integral_finsetSum`, `integral_const_mul`, `integral_mono`, `integral_map`, `Integrable.mono'`
- `Continuous.comp_aestronglyMeasurable`, `Continuous.comp_stronglyMeasurable`, `Finset.aestronglyMeasurable_fun_sum`, `AEMeasurable.div`
- `MeasureTheory.ae_all_iff`, `Filter.Eventually.exists` finite families of a.e. statements; `Even.pow_abs`; `RCLike.norm_conj`
- `MeasureTheory.memLp_map_measure_iff`, `MemLp.const_mul`, `MemLp.integrable_norm_pow'`, `ProbabilityTheory.memLp_id_gaussianReal`, `comap_measurable` (instance (6))
- `Real.le_coe_toNNReal`, `Real.coe_toNNReal`, `Real.toNNReal_pos`, `Real.sqrt_le_iff`, `Real.sqrt_mul`, `Real.sqrt_sq`, `Real.sqrt_eq_rpow`, `Real.log_two_lt_d9`, `Real.log_pow`
- verified absent (tool log): `RBM.mE_zero`, `MeasureTheory.MemLp.integrable_pow`; deprecated, not used: `condExp_finset_sum`, `integrable_finset_sum`, `integral_finset_sum`, `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`

## (d) Open issues and paper-delta candidates
Open issues (none blocks this ticket):
1. T9's `hlog`, `hX0`, `hR` and H1-H6 are numerical premises owed `∀ᶠ n` to S3-22a; instance (7) discharges them at one `n`. (a) row 16 and its `dpp.py` lines show that the ticket's `D'' = 2k+4d+10` makes H4 false (`W = N^𝔠`, e.g. `𝔠 = 1/3`, `k = 6`) while `D'' = 2(k+2)/𝔠` makes it true; `D''` is a free real here.
2. `hlog` needs the window fact `(1-s)/(1-v) ≲ N/e` ((a) row `hlog`), owed to S3-22a. T7's row premise: on the case-(ii) window S3-22a takes it from `nzUgen_holds`; `qtNZ_row_coarse` is private.
3. The random `Y` of instance (6) is a Gaussian multiple of `δ₀`, not a loop remainder `YvecN`; `YMomentsN` (the pin that gives `YvecN` its levels) is not instantiated here.
Paper-delta candidates (temporary tags):
T2274a: `lem:sum_decay_nonzero` (`3_5:1666`, proof `A:204-232`) is used as the loss-free `‖Q^{(A)}𝒰𝒜‖_∞ ≤ C‖𝒜‖_∞` on every tensor (merged EK-5), so the case-(ii) grid argument has no decay class, far part or ratio weight (`nz_hker`, `budgetNZN`); the paper states `≺`.
T2274b: the quadratic variation of `Q^{(A)}Z_j` is bounded through the row sum of `Q^{(A)}∘𝒰` (`∞→∞` duality) and the pointwise `(ℰ⊗ℰ)` bound, with Azuma, instead of BDG with the kernel bound `(sahwNQ2)` (`3_5:1910`).
T2274c: the `Y` part of `Q^{(A)}Y` (target 8): `Q^{(A)}` acts through a real kernel with row sum `≤ 2^{|A|}`; the levels `4^{|A|+1}v`, `16^{|A|+1}w` are weaker than the proved `(Σ|q|)²v`, `(Σ|q|)⁴w`; the paper has no separate `Y` part (Lean device, DECISIONS §10).
T2274d: `budgetNZN` makes the paper's `W^{-D}` of `(sahwNQ_smalleta)` explicit free reals `D''`, `D_Y`, `D_t`, and `≺` explicit constants `C` (row sum) and `cA = 2^{|A|}`.
