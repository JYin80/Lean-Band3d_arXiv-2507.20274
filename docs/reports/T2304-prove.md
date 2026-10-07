Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 14:40:39 UTC 2026

### (i) Exponent table (d = 3, kappa = eps = dd = 1/10; cc = bandwidth exponent; N = sz.size n = (WL)^d)

Sources: `Bctl n u = W^-d((lam^2+1-u)^-1 + (L^d(1-u))^-1)` (`cont_Bctl_eq`, ContinuityNet:691); `W^{2dd} <= lam^2 W^d` (`lam_sq_mul_pow_ge`, Sizes:193); `Bandwidth cc`, `WO dd` (Sizes:164-168); `RangeCond (eps/2) t` (Pins:55); `|E|<2-kap/2`, `t<1` (`v3_premises_of_stFlow`, Pins:1049).

| quantity | value (cc=1/6 ; cc=1/4) | constraint | slack |
|---|---|---|---|
| c1 = min(2 dd cc, eps/2) | 1/30 ; 1/20 | > 0 (dd, cc, eps > 0 from `Admissible`, hyp.). `Bctl(u) <= W^-2dd + N^-eps/2 <= 2 N^-c1` for u <= t | cc=1/6: 2dd cc = 1/30 < eps/2 = 1/20 (gap 1/60); cc=1/4: equal (1/20) |
| c = c1/12 (contraction) | 1/360 ; 1/240 | `B_u^(1/6) <= N^-c` for all u in [0,t_n], n >= n0; sufficient: `2 <= N^(c1/2)` (since 2^(1/6) <= N^(c1/12)) | sufficient crossover log10N = 18.06 ; 12.04; exact last violation (worst g=W^-1.4, 1-t=N^(-1+eps/2)) log10N = 12.53 ; 12.03 (script B). Same c in both regimes (no regime predicate used), `n`-free |
| `Bctl(u) <= 1` (needed by `STXiLKM_crudeN`) | | `2 <= N^c1` | log10N >= 9.03 ; 6.02 (weaker than the line above) |
| C0 = 2 n_+1 (crude start) | 5, 7, 13 at n_=2,3,6 | `1+(eta^-n_+N)B^-n_ <= N^(2n_+1)`: needs `eta^-1 <= N`, `B^-1 <= N` (`cont_inv_size_le_Bctl`, no threshold), `N >= 3` | generic `eta^-1 <= N` iff `N^(eps/2) sqrt(kap/2)/2 >= 1`: log10N >= 19.03 (uses only `Im m >= sqrt(kap/2)/2 = 0.1118`, `ST_mE_im_ge`); at szB actual `Im m = 0.968`, `eta^-1 = 33.05 <= N` for all n; log10 lhs 10.94 vs 18.06 (n_=2, n=0) |
| r = ceil(C0/c)+1 (rounds) | cc=1/6: 1801, 2521, 4681; cc=1/4: 1201, 1681, 3121 (n_=2,3,6) | `N^(C0-rc) <= 1`, i.e. `C0 - rc <= -c` | slack exactly c (ceil); no threshold on N (N >= 1). r depends on (C0, c) only, never on n or the round index |
| `N^-c <= 1` (step (c) of `stBoot_rounds`) | | N >= 1 (`one_le_size`) | automatic |
| per-round tau, constant r+1 | tau free | each round is a full `Prec` statement (every tau > 0, D > 0, eventually in n); `r+1 <= N^tau` eventually, for each tau | no accumulation of tau across rounds (hypothesis `hround` is for every deterministic `Y >= 1`); threshold `N >= (r+1)^(1/tau)` |
| `STbootRHS 1` XLK-indices | `[1, n_-1]` | `qtBoot_bootRHS_update` needs XLK read only at `m <= n_-1`, `n_>=2` | script C: n_ = 2..12 all in `[1,n_-1]`; for m >= (n_+1)/2+1 index `n_+2-m <= n_-1` iff `(n_+1)/2 >= 2` (n_ >= 3), empty sum for n_=2 |
| lower terms of `(eq:expandQAempty)` | C_{n_} = max_sigma sum_alpha abs(xi_alpha) 2^k_alpha (kappa/2)^(-(n_-k_alpha)/2) | `STNewPQ` quantifies `(l,k,xi,sigma',iota,A')` before `sz, n` (Step34Pins:330), `1 <= k_alpha <= n_-1`: finite, n-free | factor per term `<= (max(2, (kappa/2)^(-1/2)))^n_` = 4.4721^n_; B-exponent cancels exactly: `(N eta)^-(n_-k) B^k / B^n_ <= ((Im m)^-1)^(n_-k)`, no loss |
| RangeCond delta, t, s | eps/2 = 1/20; `1-t >= N^-0.95` | `v3_premises_of_stFlow` | szB: `1-t = 1/32` vs `N^-0.95 <= 3.7e-4` at N=4096 (factor ~84) |
| `\|E\| < 2-kap/2`, `Im m` | `\|lemE\| = 0.49998` vs 1.95 | `ST_mE_im_ge` at kap/2 | large |
| `STConStInd 𝔠d` (hypothesis of `STIngR`, not used in the contraction) | 𝔠d <= 1/100 (chosen by the pin) | `(Bctl t)^𝔠d <= (1-t)/(1-s) = 1/2 < 1` eventually | holds for every 𝔠d>0 (`conStInd_const`): W >= 1.23e10 at 𝔠d=1/100, W >= 2.5e100 at 𝔠d=1/1000 (script D) |

### (ii) Concrete nondegenerate instance (merged `szB`, Step34Pins:710; case (ii) with 1-s = lam^2/L^2 = 1/16 exactly)

Data: d=3, L=4, W_n=n+4, lam=1, N=(4W)^3 >= 4096, z_n=1/2+i/64, kappa=eps=dd=1/10, cc=1/6, s=15/16, t=31/32 (`lemT zB >= 31/32`), n_ in {2,3,6}, c=1/360, C0=2n_+1. Stochastic premises (`STKbound`, `STKward`, `STLK s`, `STStep2Concl`, round `STXiRound'`) stay hypotheses of the instances (other gates' pins). Command and verbatim output:

`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2304/final.py` (mpmath, 40 digits; the rounds block 1200 digits)

```
A. exponents (d=3, kappa=eps=dd=1/10): c1=min(2*dd*cc,eps/2), c=c1/12, C0=2n_+1, r=ceil(C0/c)+1
 cc=0.1667 c1=0.033333 c=0.0027778 | log10N thresholds: 2<=N^(c1/2) 18.0618; Bctl<=1 9.0309; eta^-1<=N (generic) 19.031 | r(n_=2,3,6)=[1801, 2521, 4681]; N^(C0-rc)<=1 slack c: C0-rc<=-c
 cc=0.25 c1=0.05 c=0.0041667 | log10N thresholds: 2<=N^(c1/2) 12.0412; Bctl<=1 6.0206; eta^-1<=N (generic) 19.031 | r(n_=2,3,6)=[1201, 1681, 3121]; N^(C0-rc)<=1 slack c: C0-rc<=-c
B. log_N Bctl at worst u (B increasing in u); boundary: 1-u=g^2/L^2; edge: 1-t=N^(-1+eps/2); src=log_N(W^(-2dd)+N^(-eps/2)); N=10^{3,6,12,18,24}
 cc=0.167 g=1: bdry -0.471 -0.494 -0.5 -0.5 -0.5 | edge -0.0437 -0.0499 -0.05 -0.05 -0.05 | src 0.0589 0.00898 -0.0156 -0.0235 -0.0273
 cc=0.167 g=W^-1.4: bdry -0.00392 -0.0271 -0.033 -0.0333 -0.0333 | edge 0.0563 0.00893 -0.0156 -0.0235 -0.0273 | src 0.0589 0.00898 -0.0156 -0.0235 -0.0273
 cc=0.25 g=1: bdry -0.71 -0.735 -0.747 -0.749 -0.75 | edge -0.0489 -0.05 -0.05 -0.05 -0.05 | src 0.0503 0.000172 -0.0249 -0.0333 -0.0375
 cc=0.25 g=W^-1.4: bdry -0.00958 -0.0353 -0.0469 -0.0493 -0.0498 | edge 0.039 -0.000946 -0.0249 -0.0333 -0.0375 | src 0.0503 0.000172 -0.0249 -0.0333 -0.0375
 cc=0.167: last log10N (grid .01) with B_t^(1/6)>N^-c at g=W^-1.4, edge: 12.53; sufficient crossover 18.0618
 cc=0.25: last log10N (grid .01) with B_t^(1/6)>N^-c at g=W^-1.4, edge: 12.03; sufficient crossover 12.0412
C. STbootRHS 1 XLK-indices (Icc 1 (n_-1) and n_+2-m, m in Icc ((n_+1)/2+1) (n_-1)) all in [1,n_-1] for n_=2..12: True
D. checks = Bandwidth,WO,locDomain,RangeCond,CaseII,B_t<=1,contraction,B_s<=B_t,1/N<=B_s (9)
 instance szB: d=3,L=4,W_n=n+4,lam=1,N=(4W)^3,z=1/2+i/64,kap=eps=dd=1/10,cc=1/6,s=15/16,t=31/32
 msc(z)=(-0.24798289 + 0.96046696j) lemT=0.98399229>=31/32:True lemE=0.499984 |lemE|<2-kap/2:True Im m(lemE)=0.968248>=sqrt(kap/2)/2=0.1118:True
 n=0                     log10N=3.6124  B_t^(1/6)=0.5331   N^-c=0.9772  checks=9/9
 n=1                     log10N=3.9031  B_t^(1/6)=0.4769   N^-c=0.9753  checks=9/9
 n=10                    log10N=5.2446  B_t^(1/6)=0.285    N^-c=0.967   checks=9/9
 n=1000                  log10N=10.811  B_t^(1/6)=0.03365  N^-c=0.9332  checks=9/9
 n=1000000               log10N=19.806  B_t^(1/6)=0.001066 N^-c=0.881   checks=9/9
 n=1000000000000         log10N=37.806  B_t^(1/6)=1.066e-6 N^-c=0.7852  checks=9/9
 n=100000000000000000000 log10N=61.806  B_t^(1/6)=1.066e-10 N^-c=0.6735  checks=9/9
 all sampled deterministic hypotheses hold: True
 contraction for ALL n of szB: needs N>=(64k)^(60/59)=101.59; min N of szB = 4096
 crude start 1+(eta^-n_+N)N^n_ <= N^(2n_+1), eta^-1=1/((1-t)Im m)=33.049 <= N:
  n=0: n_=2: log10 lhs=10.94 <= 18.062; n_=3: log10 lhs=15.441 <= 25.287; n_=6: log10 lhs=30.789 <= 46.961
  n=1000: n_=2: log10 lhs=32.434 <= 54.057; n_=3: log10 lhs=43.246 <= 75.68; n_=6: log10 lhs=75.688 <= 140.55
 STConStInd (Bctl(t))^cd <= (1-t)/(1-s)=1/2 < 1; B_t<=k W^-3 -> 0 (k=1.4697), so holds eventually for every cd>0:
  cd=0.01: W>=1.2305e+10 (log10 W=10.0901)
  cd=0.001: W>=2.5065e+100 (log10 W=100.399)
 stBoot_rounds (R=10,c=1/360,C0=2n_+1), Y_{j+1}=N^-c Y_j+R:
  n=0,n_=2: r=1801 viol=0 Y_r=438.805<=(r+1)R=18020:True N^(C0-rc)<=1:True
  n=0,n_=3: r=2521 viol=0 Y_r=438.805<=(r+1)R=25220:True N^(C0-rc)<=1:True
  n=0,n_=6: r=4681 viol=0 Y_r=438.805<=(r+1)R=46820:True N^(C0-rc)<=1:True
  n=100000000000000000000,n_=2: r=1801 viol=0 Y_r=31.2982<=(r+1)R=18020:True N^(C0-rc)<=1:True
  n=100000000000000000000,n_=3: r=2521 viol=0 Y_r=31.2982<=(r+1)R=25220:True N^(C0-rc)<=1:True
  n=100000000000000000000,n_=6: r=4681 viol=0 Y_r=31.2982<=(r+1)R=46820:True N^(C0-rc)<=1:True
 instance (3) stBoot_rounds: xi=1,R=1,c=1,C0=0: r=1; Prec xi N^0, round 1<=N^-1 Y+1 (Y>=1): ok
```

External-hypothesis limit computations: `Bandwidth 1/6` at szB: `W >= N^(1/6) = 2 W^(1/2)`, true for W >= 4. `WO 1/10`: `W^-1.4 <= 1 = lam <= 10`. `RangeCond 1/20`: `N^-0.95 <= 1/32` for N >= 4096. `STConStInd`: `B_t = 1.4697 W^-3 -> 0`, so `B_t^𝔠d -> 0 < 1/2 = (1-t)/(1-s)` for every 𝔠d > 0; the pin picks 𝔠d <= 1/100, threshold W >= 1.23e10 at 𝔠d = 1/100 (an eventual, not a vacuous, hypothesis).

### Verdicts

- Pin `STXiRound'` (check §2): PASS. Differs from `STXiBoot'` (NQEndFlow:95-104) only by `m+1 <= n_` to `m <= n_` and the extra summand `B_u^(1/6) XLK n_`; its right side is the case-(ii) output `STNZConcl''` (QtNonzeroFlowLift:68) plus lower terms with `lo=1`.
- `stBoot_rounds`: PASS. Y_j >= 1; `Y_j <= N^(C0-jc) + jR` (script, 0 violations); `Y_r <= (r+1)R` and the constant `r+1` is absorbed by `N^tau` for every tau; r is independent of n.
- `stXiBoot'_of_round`, `stXiBootR_of_round`: PASS. Contraction constant `c = min(2dd cc, eps/2)/12` is `n`-free, the same for every u in [s_n,t_n], valid for n >= n0; regime-free (no regime predicate, no `STConStInd`, no `L^d <= W^K`). Crude start `C0 = 2n_+1` from `STXiLKM_crudeN` with `MK = N`, `eta^-1 <= N`, `B^-1 <= N`. `STbootRHS 1` reads `XLK` at `[1,n_-1]` only (script C).
- `stXiRoundNZ_holds`: PASS. Lower terms `k_alpha = 1..n_-1` bounded by hypotheses only: `(normQA2)` `||Q^(A')T|| <= 2^|A'| ||T||`, `|A'| <= k_alpha`, `Xi^_{v,k_alpha} <~ XLK k_alpha` (hypothesis range `m <= n_`), `(N eta)^-1 <= (Im m)^-1 B_v` (`expWII_inv_Neta_le`); the B-exponent cancels exactly, constant `C_{n_}` finite and n-free (`STNewPQ` quantifier order). Envelope `XL#`,`XLK#` gives `XLK#(v) <= XLK(u)` for v <= u <= t and `B_v <= B_u`.
- `stOeqQtNZ'_holds`: PASS (one term from the above).
- O2 verdict: PASS: `c` is a fixed positive number of (dd, cc, eps), uniform in n in both regimes; the small-N failure of `B_t <= 1` (`edge +0.0563`, `+0.039` at log10N = 3 for g = W^-1.4) is harmless: only `forall^f n` is used and r does not depend on n.
- §95 (3) level check: no drift or good-set level is added by this ticket; the current length enters only through the self-absorbing summand removed by deterministic rounds.

## (a′) Preflight corrections and additions — Tue Oct  6 15:21:13 UTC 2026

No verdict of (a) changes.  Below: one route difference (not a mistake) and the lines the ticket's gates ask for that (a) does not contain: the §29/§45 one-liners, the G3 table, the `STNZConcl''`/`STOeqQtNZ'` part of G2, the §95 (3) grep ((a) has the O2 and §95 (3) verdicts and the `STXiRound'`-vs-`STXiBoot'` comparison).
Route note; `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2304/corr.py` (mpmath, 40 digits):
```
mu = (sqrt(kappa/2)/2)^-1 = 8.94427191
n_=2: Lean-route threshold 2+mu^n_ = 82.0  (log10 N >= 1.91381)
n_=3: Lean-route threshold 2+mu^n_ = 717.5417528  (log10 N >= 2.85585)
n_=6: Lean-route threshold 2+mu^n_ = 512002.0  (log10 N >= 5.70927)
cc=0.166667: c1=0.033333333, contraction threshold 2<=N^(c1/2): log10 N >= 18.0618
cc=0.25: c1=0.05, contraction threshold 2<=N^(c1/2): log10 N >= 12.0412
```
(a) row "C0 = 2 n_+1" gets the crude start from `eta^-1 <= N` (log10N >= 19.03).  Lean (`qtBoot_crude`, QtNonzeroBoot.lean:337) uses `eta^-1 <= mu N`, `mu = (sqrt(kappa/2)/2)^-1` (`expWII_inv_Neta_le`, `ST_mE_im_ge`, `B <= 1`); its own threshold is `2 + mu^n_ <= N` (above).  `C0 = 2 n_+1` and the contraction crossover 18.0618 / 12.0412 (the binding one) are those of (a).
Gate lines (file at commit `8e4bfe8`; evidence: (b) blocks "gates" and "pin", `where.sh` for producer lines):
- §29/§45 (1) PASS: `0 ≤ s`, `s < t ≤ lemT z` are `STIngR` binders (Step34Pins.lean:445); `t < 1`, `RangeCond (ε/2) t`, `|E| < 2 − κ/2`, `Admissible 𝔠 𝔡` come from `v3_premises_of_stFlow` (code lines 342, 526, 1065).
- §29/§45 (2) PASS: §2-§4 use no regime predicate; `STCaseI/STCaseII` occur in code only from line 1059 on (`stXiRoundNZ_holds`, `stOeqQtNZ'_holds`, §7).   (3) PASS: `STConStInd`, `st_window`, `L^d ≤ W^K`: no code line.
- §29/§45 (4) PASS: every numerical condition is `∀ᶠ n`: `filter_upwards` at 254 (`Bandwidth`, `WO`, `RangeCond`, `2 ≤ N^{c₁/2}`), 355 (`B ≤ 1`, `‖𝒦‖ ≤ N B^{n_-1}`, `2 + μ^{n_} ≤ N`), 562 (`B^{1/6} ≤ N^{-c}`), 712 (`3 ≤ N^{τ/2}`).
- §29/§45 (5) PASS: every statement is `Prec` over `STPair s t` (or its product with a finite inner index, reduced by `qtBoot_prec_sup`).   (6) PASS: `stXiBootR_of_round` keeps the `𝔠d` of its hypothesis, `stXiRoundNZ_holds` that of `stOeqNZ''_holds d`.   (7) PASS: scale `N = sz.size n` in every `Prec sz`.
- §95 (3) PASS: the ticket's level grep has 0 matches; `STbootRHS` reads `XLK` at lengths ≤ n_−1 only (`qtBoot_bootRHS_update`, :452, compiled).
- G2 PASS: `STNZConcl''` is used at `A = STIdiff σ` with `Finset.Subset.refl` (`precomp_param` in `qtBoot_round_of_NZ`, :845); its quantity is defeq to the first summand of `zeroModeCalc_LK_expansion_empty` (`exact` in `hpt`); `STOeqQtNZ' 3 = STIngR 3 STCaseII (fun … => STXiBoot' …)` by `rfl` (:1245); case-(i) shape compiled (:1233).
- G3 (premise ← producer; every row PASS; no premise without producer or "new"):
  `STXiRound'` ← case (ii) `stXiRoundNZ_holds` (new, :1059), case (i) S3-18b2 (new there) · flow, `0≤s<t≤lemT` ← `STIngR` binders, `v3_premises_of_stFlow` Green/Pins:1049 · crude `Ξ̂_{n_} ≺ N^{2n_+1}` ← new `qtBoot_crude` (:337) ← `STXiLKM_crudeN` NQGood1:959, `stKbound_timeIcc` KDecay:1062, `st6_prec_det_iff` Step6Kit:81, `cont_inv_size_le_Bctl` ContinuityNet:701, `expWII_inv_Neta_le` ExpWardII:303, `ST_mE_im_ge` Step2Events:555, `seqHflow_isHermitian` FineModel:531, `gridGood_STXiLKM_seqHflow` GridGoodN:95 ·
  contraction ← new `qtBoot_contraction` (:246) ← `cont_Bctl_eq` ContinuityNet:691, `lam_sq_mul_pow_ge` Sizes:193, `Bandwidth`/`WO` Sizes:168/164, `RangeCond` Green/Pins:55 · pair hypotheses `XL`, `XLK` (`m ≤ n_−1`) ← the consumer's (S3-25 via `STIterR'`) · `XLK n_ := Y_j` ← new (round state in `stXiBoot'_of_round`) · `STNZConcl''` at envelope controls ← `stOeqNZ''_holds` QtNonzeroFlowLift:763, copies of `nzLift_sharp_*` (:99-152) as `qtBoot_sharp_*`, `nqFlowSharp` NQEndFlowLift:68 ·
  expansion ← `zeroModeCalc_LK_expansion_empty` ZeroModeCalc:595 ← `stNewPQ_holds` NewPQ:584 · `(normQA2)` ← `norm_zeroModeSet_le` ZeroModeCalc:163 · `(Nη)^{-1} ≤ (Im m)^{-1} B`, `Im m ≥ √(κ/2)/2` ← `expWII_inv_Neta_le`, `ST_mE_im_ge` · `Ξ̂_{k_α} ≺ XLK k_α` ← the round's hypothesis (`k_α ≤ n_−1`) · `B_v ≤ B_u` ← `STBctl_mono` ScaleFacts:74 · `STbootRHS` monotone / `lo` ← copy of `nzLift_bootRHS_mono` :158 as `qtBoot_bootRHS_mono` (:651), new `qtBoot_bootRHS_two_le_one` (:489) · finite max ← new `qtBoot_prec_sup` (:688) · `stOeqQtNZ'_holds`: no premise.


## (b) Script output — Tue Oct  6 15:21:13 UTC 2026

Scripts and outputs: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2304/` (`evidence.sh` → `evidence.out`, `stmt.lean`, `reg_before.out`, `reg_after2.out`, `gates.py`, `clash.sh`, `where.sh`, `names.lean`).  Commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2304`; lines as the scripts print them (long lines cut by the scripts).
```
$ date -u; git branch --show-current; git log --oneline -1; lake build RBM3D.Induction.QtNonzeroBoot; grep …; git diff --stat main...t/T2304
Tue Oct  6 15:19:56 UTC 2026
t/T2304
8e4bfe8 T2304: obsB helpers of the instance section private
exit: 0
1029:Build completed successfully (3890 jobs).
warnings/errors in RBM3D/Induction/QtNonzeroBoot.lean: 0
1257:0: 'RBM.Gauss.Sizes.STXiRound'' depends on axioms: [propext, Classical.choice, Quot.sound]
1258:0: 'RBM.Ind.stBoot_rounds' depends on axioms: [propext, Classical.choice, Quot.sound]
1259:0: 'RBM.Ind.stXiBoot'_of_round' depends on axioms: [propext, Classical.choice, Quot.sound]
1260:0: 'RBM.Ind.stXiBootR_of_round' depends on axioms: [propext, Classical.choice, Quot.sound]
1261:0: 'RBM.Ind.stXiRoundNZ_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1262:0: 'RBM.Ind.stOeqQtNZ'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1263:0: 'RBM.Ind.QtNonzeroBootInst.inst_OeqQtNZ'' depends on axioms: [propext, Classical.choice, Quot.sound]
1264:0: 'RBM.Ind.QtNonzeroBootInst.inst_RoundNZ' depends on axioms: [propext, Classical.choice, Quot.sound]
lines:     1264   sorry|admit|native_decide|axiom|maxHeartbeats|open private|_private: 0
git diff --stat main...t/T2304:
 RBM3D/Induction/QtNonzeroBoot.lean | 1264 ++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean             |    6 +-
 2 files changed, 1267 insertions(+), 3 deletions(-)
```
Targets, statements extracted from the file by script (`awk`):
```
92: def STXiRound' (E s t : ℕ → ℝ) : Prop :=
93:   ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
94:     (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
95:     (∀ m, 1 ≤ m → STlenL n_ p m →
96:       Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
97:     (∀ m, 1 ≤ m → m ≤ n_ →
98:       Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
99:     Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
100:       (fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
101:         STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
136: theorem stBoot_rounds {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {U : ℕ → Type} (π : ∀ n, U n → ℝ)
137:     (ξ : ∀ n, U n → sz.SeqΩ → ℝ) (R : ℕ → ℝ → ℝ) (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
138:     (hR : ∀ n u, 1 ≤ R n u)
139:     (h0 : Prec sz (U := U) ξ (fun n _ _ => ((sz.size n : ℕ) : ℝ) ^ C₀))
140:     (hround : ∀ Y : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ Y n u) →
141:       Prec sz (U := U) ξ (fun n q _ => Y n (π n q)) →
142:       Prec sz (U := U) ξ (fun n q _ => ((sz.size n : ℕ) : ℝ) ^ (-c) * Y n (π n q) + R n (π n q))) :
143:     Prec sz (U := U) ξ (fun n q _ => R n (π n q)) := by
522: theorem stXiBoot'_of_round {d : ℕ} (hd : 3 ≤ d) (κ ε 𝔠 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (sz : Sizes d)
523:     (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
524:     (ht : ∀ n, t n ≤ lemT (z n)) (hround : STXiRound' sz (STflowE z) s t) :
525:     STXiBoot' sz (STflowE z) s t := by
581: theorem stXiBootR_of_round (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
582:     (h : STIngR d R (fun sz E s t => STXiRound' sz E s t)) :
583:     STIngR d R (fun sz E s t => STXiBoot' sz E s t) := by
1059: theorem stXiRoundNZ_holds : ∀ d : ℕ, STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t) := by
1074: theorem stOeqQtNZ'_holds : ∀ d : ℕ, STOeqQtNZ' d := fun d => stXiBootR_of_round d STCaseII (stXiRoundNZ_holds d)
```
Compiled nonempty instances (declarations of namespace `RBM.Ind.QtNonzeroBootInst`, with file lines) and the pinned-statement script (the check file's section 3 `T2304_*` Props over the library `STXiRound'` + 7 `example`s; exit 0, no output):
```
1092: theorem inst_OeqQtNZ' :
1100: theorem inst_RoundNZ :
1111: example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
1129: example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
1148: example : Prec szB (U := fun _ => Unit) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
1160: example : Prec szB (U := fun _ => Unit) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => (2 : ℝ)) :=
1188: example : Prec szB (U := fun _ => Unit) (fun n _ ω => 1 + obsB n ω) (fun _ _ _ => (3 : ℝ)) :=
1209: example : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ u : ℝ, 0 ≤ u → u ≤ 31 / 32 →
1220: example : Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
1226: example (hround : STXiRound' szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
1233: example : ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t) → STOeqQt' d :=
1236: example : ∀ d : ℕ, STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t) → STOeqQtNZ' d :=
1241: example : ∀ d : ℕ, STOeqQtNZ' d := @stOeqQtNZ'_holds
1243: example : STOeqQtNZ' 3 := stOeqQtNZ'_holds 3
1245: example : STOeqQtNZ' 3 = STIngR 3 STCaseII (fun sz E s t => STXiBoot' sz E s t) := rfl
1248: example : STIngR 3 STCaseII (fun sz E s t => STXiBoot' sz E s t) :=
exit: 0   output lines:        0
64:example : T2304_stBoot_rounds := @RBM.Ind.stBoot_rounds
65:example : T2304_stXiBoot'_of_round := @RBM.Ind.stXiBoot'_of_round
66:example : T2304_stXiBootR_of_round := @RBM.Ind.stXiBootR_of_round
67:example : T2304_stXiRoundNZ_holds := @RBM.Ind.stXiRoundNZ_holds
68:example : T2304_stOeqQtNZ'_holds := @RBM.Ind.stOeqQtNZ'_holds
69:example : T2304_consumer_II := fun d h => RBM.Ind.stXiBootR_of_round d STCaseII h
70:example : T2304_consumer_I := fun d h => RBM.Ind.stXiBootR_of_round d STCaseI h
```
Pin (script diff of the body against the check file's section 2; and against `STXiBoot'`, NQEndFlow.lean:96-103):
```
pin body vs check section 2: IDENTICAL (diff exit 0)
--- STXiBoot' (NQEndFlow.lean:96-103) vs STXiRound' body:
5c5
<     (∀ m, 1 ≤ m → m + 1 ≤ n_ →
---
>     (∀ m, 1 ≤ m → m ≤ n_ →
8c8,9
<       (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
---
>       (fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
>         STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
```
Registry (`Test/Axioms.lean` hunks; then `import RBM3D` + `import RBM3D.Induction.QtNonzeroBoot` + `#assert_rbm_axioms` by `lake env lean`; `reg_before.out` was produced before the registry edit, i.e. for the library without the new module; the `exit: 0` line is that of the run with the new module):
```
 RBM3D/Test/Axioms.lean | 6 +++---
 1 file changed, 3 insertions(+), 3 deletions(-)
-   `RBM.Gauss.Sizes.STXiBoot', -- `(am;asoi222)` at `B_s` (DECISIONS §80): S3-18b, S3-22; hypothesis of `STIterR'`; hypothesis of `iterationsB_step` (T2259)
-   `RBM.Gauss.Sizes.STOeqQt', -- `lem:STOeq_Qt`, R2* (DECISIONS §80): S3-18b
-   `RBM.Gauss.Sizes.STOeqQtNZ', -- `lem:STOeq_Qt_nonzero`, R2* (DECISIONS §80): S3-22
+   `RBM.Gauss.Sizes.STXiBoot', -- `(am;asoi222)` at `B_s` (DECISIONS §80): S3-18b, S3-22; hypothesis of `STIterR'`; hypothesis of `iterationsB_step` (T2259); concluded from `
+   `RBM.Gauss.Sizes.STOeqQt', -- `lem:STOeq_Qt`, R2* (DECISIONS §80): S3-18b; S3-18b2 via `stXiBootR_of_round d STCaseI` (T2304)
+   `RBM.Gauss.Sizes.STXiRound', -- one round of `(am;asoi222)` with the current-length control (T2304); premise of `stXiBoot'_of_round`, `stXiBootR_of_round`; case (ii) prove
exit: 0
--- reg_before.out
1:axiom audit: 8646 theorems, 2828 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
27:  RBM.Gauss.Sizes.STIngR: 1 [no certificate]
31:  RBM.Gauss.Sizes.STXiBoot': 4 [no certificate]
33:  RBM.Gauss.Sizes.STOeqQtNZ': 1 [no certificate]
153:premises found by scanning: 152 (borrowed 1, owed 93, structural 41, refuted 6, superseded 11).
154:registry: 2 borrowed + 144 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
--- reg_after2.out
1:axiom audit: 8653 theorems, 2829 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
27:  RBM.Gauss.Sizes.STIngR: 3 [no certificate]
31:  RBM.Gauss.Sizes.STXiBoot': 7 [no certificate]
33:  RBM.Gauss.Sizes.STXiRound': 4 [no certificate]
153:premises found by scanning: 152 (borrowed 1, owed 93, structural 41, refuted 6, superseded 11).
154:registry: 2 borrowed + 144 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```
Gates (`gates.py`: comments stripped before grepping):
```
code-only lines mentioning STCaseI/STCaseII      : 1059 1074 1094 1102 1233 1234 1236 1237 1245 1248 1249
code-only lines mentioning STConStInd / st_window : none
code-only lines mentioning v3_premises_of_stFlow  : 342 526 1065 1211
code-only lines with filter_upwards               : 239 254 355 562 694 712
ticket 95(3) level grep (whole file incl. comments): 0 matches
```
Name clashes (the same script run in the main worktree gave 0 hits for the 9 names; those lines are omitted):
```
STXiRound': 2 hits outside RBM3D/Induction/QtNonzeroBoot.lean
stBoot_rounds: 0 hits outside RBM3D/Induction/QtNonzeroBoot.lean
stXiBoot'_of_round: 1 hits outside RBM3D/Induction/QtNonzeroBoot.lean
stXiBootR_of_round: 3 hits outside RBM3D/Induction/QtNonzeroBoot.lean
stXiRoundNZ_holds: 1 hits outside RBM3D/Induction/QtNonzeroBoot.lean
stOeqQtNZ'_holds: 1 hits outside RBM3D/Induction/QtNonzeroBoot.lean
QtNonzeroBootInst: 0 hits outside RBM3D/Induction/QtNonzeroBoot.lean
inst_OeqQtNZ': 0 hits outside RBM3D/Induction/QtNonzeroBoot.lean
inst_RoundNZ: 0 hits outside RBM3D/Induction/QtNonzeroBoot.lean
qtBoot_: 0 hits outside RBM3D/Induction/QtNonzeroBoot.lean
--- the hits (file:line):
RBM3D/Test/Axioms.lean:124:   `RBM.Gauss.Sizes.STXiBoot', -- `(am;asoi222)` at `B_s` (DECISIONS §80): S3-18b, S3-22; hyp
RBM3D/Test/Axioms.lean:125:   `RBM.Gauss.Sizes.STOeqQt', -- `lem:STOeq_Qt`, R2* (DECISIONS §80): S3-18b; S3-18b2 via `st
RBM3D/Test/Axioms.lean:126:   `RBM.Gauss.Sizes.STXiRound', -- one round of `(am;asoi222)` with the current-length contro
RBM3D/Induction/QtNonzeroFlowLift.lean:87:S3-22c (`newPQ` combination and self-absorption bootstrap, `stOeqQtNZ'_holds`)
```
Ports: none from RBM1D/RBM2D (nothing was run there).  Copies inside RBM3D (private, prefix `qtBoot_`): `nzLift_sharp_{one_le,le,mono,prec}` (QtNonzeroFlowLift.lean:99-152), `nzLift_bootRHS_mono` (:158), `nzLift_bootRHS_one_le` (:193), `nzLift_flowLam` (:659), the pattern of `nqFlow_prec_of_le_right` (NQEndFlow.lean:206).  No `set_option maxHeartbeats` in the file.
Narrative.
- `RBM3D/Induction/QtNonzeroBoot.lean`, 1264 lines (below the ticket's 1500 cut: no T2304a/b split), commits `5b22d3f`, `0bfcdc9`, `8e4bfe8`; registry hunks as in the ticket (3 lines changed); module build exit 0, 0 warnings in the file.
- §2 `stBoot_rounds`: `Y_0 = N^{C₀}`, `Y_{j+1} = N^{-c} Y_j + R`; `Y_j ≥ 1`; `ξ ≺ Y_j` by induction; `Y_j ≤ N^{C₀−jc} + jR` for every `n` (`N^{-c} ≤ 1` needs only `N ≥ 1`); at `r = ⌈C₀/c⌉₊+1`, `N^{C₀−rc} ≤ 1 ≤ R`, so `Y_r ≤ (r+1)R`; the constant is absorbed by `StochDomAt.const_mul_right` with `(r+1)⁻¹`.
- §3 `qtBoot_contraction` (:246): `B_u ≤ N^{-2𝔡𝔠} + N^{-ε/2} ≤ 2N^{-c₁} ≤ N^{-c₁/2}` once `2 ≤ N^{c₁/2}`, `c₁ = min(2𝔡𝔠, ε/2)`; then `B ≤ 1`, `B^{1/6} ≤ N^{-c₁/12}`, `c = c₁/12 = qtBoot_c`; only `Admissible`, `RangeCond`.  `qtBoot_crude` (:337): `Ξ̂ ≤ N^{2n_+1}` for every sample.
- §4 `stXiBoot'_of_round`: the round at `XLK' = Y` in the slot `n_` (`STbootRHS` unchanged, `qtBoot_bootRHS_update`), then `B_u^{1/6} Y ≤ N^{-c} Y` eventually (pairs have `u ∈ [s_n, t_n]`); `stXiBootR_of_round` unfolds `STIngR`, keeps `𝔠d`.
- §5 `qtBoot_round_of_NZ` (:845): data `(ℓ, k, ξ, σ', ι, A')` per `σ` by `choose` from `zeroModeCalc_LK_expansion_empty`; first term = `STNZConcl''` at the envelope controls, reindexed by `precomp_param`, compared pointwise on pairs; lower terms by `qtBoot_term_le` (:767), constants `|ξ_α| 2^{k_α} (√(κ/2))^{-(n_−k_α)}`; `max_σ` is replaced by `Σ_σ Σ_α` (`max ≤ Σ`, non-negative terms); `qtBoot_prec_sup` is a direct measure-monotonicity proof, `qtBoot_prec_of_add_le` uses `StochDomAt.of_subset_union`, `qtBoot_prec_sum` is its induction.
- Differences from the ticket text, none in a pin: contraction routed through `B ≤ N^{-c₁/2}`; crude start via `η⁻¹ ≤ μN` ((a′)); `Σ_σ` for `max_σ`; extra instances (1'), (2'), (3'), (3''), (4'), (6').

## (c) Verified Mathlib names — Tue Oct  6 15:21:13 UTC 2026

`lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2304/names.lean` (`import RBM3D.Induction.QtNonzeroBoot`, one `#check @name` each): 88 names, exit 0, no error.  Real.: rpow_le_one_of_one_le_of_nonpos, one_le_rpow, rpow_nonneg, rpow_add, rpow_mul, rpow_neg, rpow_one, rpow_natCast, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_pos_of_pos, sqrt_pos, sqrt_le_sqrt, norm_of_nonneg, abs_sin_le_one, sInf_empty.  Complex.: norm_I, norm_natCast, norm_real, norm_two, norm_intCast.  Finset.: exists_mem_eq_sup', le_sup', sup'_le, le_sup'_of_le, sum_le_sum_of_subset_of_nonneg, Icc_subset_Icc_left, single_le_sum, card_le_univ, sum_div, sum_insert, sum_nonneg, sum_congr, sum_le_sum, induction_on, mem_Icc, mem_univ, univ_nonempty.
Root: Nat.le_ceil, Nat.cast_nonneg, div_le_iff₀, lt_div_iff₀, inv_anti₀, inv_inv, mul_inv, mul_inv_cancel_left₀, mul_inv_cancel₀, inv_pos, inv_nonneg, inv_div, one_div, add_div, div_le_div_of_nonneg_right, pow_le_one₀, pow_le_pow_left₀, pow_le_pow_right₀, one_le_pow₀, pow_pos, pow_nonneg, pow_add, pow_succ, mul_pow, mul_le_mul, mul_le_mul_of_nonneg_left/right, add_le_add_left/right, abs_nonneg, lt_min, min_le_left/right, lt_of_le_of_lt, norm_sum_le, norm_add_le, norm_div, norm_pow, norm_mul, pi_norm_le_iff_of_nonneg, norm_le_pi_norm, csInf_le, csInf_le_csInf, exists_lt_of_csInf_lt, max_le_max, Set.Icc_eq_empty, Set.image_mono, measure_mono, Filter.eventually_atTop, Filter.Eventually.of_forall.
Verified absent (unknown identifier, `names_absent.lean`): root-namespace `norm_I`, `norm_intCast` (the `Complex.` forms exist).  Deprecated here (tool-log warnings; replaced by `simp`): `if_pos`, `if_neg`.

## (d) Open issues and paper-delta candidates

- `T2304a` ("solving which yields `(am;asoi222)`", `3_5:1929-1930`): the paper states no a priori bound (read `3_5:1885-1935`); Lean implements it as a finite deterministic bootstrap: crude start `Ξ̂^{(𝓛-𝒦)}_{v,n} ≺ N^{2n+1}` (`qtBoot_crude`), contraction `(W^{-d}B_{u,0})^{1/6} ≤ N^{-c}`, `c = min(2𝔡𝔠, ε/2)/12` from `(eq:WO)`, `(Main_DEL_COND)` and `1 − t ≥ N^{-1+ε/2}` (`RangeCond`), `⌈C₀/c⌉+1` rounds, `C₀ = 2n+1`; regime-free, so the same argument closes `lem:STOeq_Qt` (case (i), S3-18b2).
- `T2304b` (the lower terms of `(eq:expandQAempty)`, `k_α = 1` included): bounded by the hypotheses `Ξ̂_{k_α} ≺ Ξ_{k_α}` (`1 ≤ k_α ≤ n−1`) with `(normQA2)` and `(Nη_t)^{-1} ≤ (√(κ/2))^{-1} W^{-d}B_{t,0}`; factor `|ξ_α| 2^{k_α} (√(κ/2))^{-(n−k_α)}`, the powers of `B` cancel exactly; neither `(eq:kalpha1)` (averaged law) nor `(am;asoiuw_smalleta)` at length `k_α` (`3_5:1925`) is used.
- Open: `STXiRound'` stays in `owedProps` (case (i) is S3-18b2's; per the ticket's design `stOeqQt'_holds d := stXiBootR_of_round d STCaseI H`, `H` from `stOeqNQ''_holds` and the alternating pin at the minimum of the two `𝔠d`); `STOeqQtNZ'` left `owedProps` (registry: 144 owed before and after).  The contraction holds for `n ≥ n₀(𝔠, 𝔡, ε)`; at `κ = ε = 𝔡 = 1/10` the sufficient threshold `2 ≤ N^{c₁/2}` used in the proof is log10N ≥ 18.06 (𝔠 = 1/6) / 12.04 (𝔠 = 1/4) (`corr.py`).
- The full `lake build` is the hub's merge step (CLAUDE.md §3 (A)); the substitute run here is the registry pre-check above (library + new module + `#assert_rbm_axioms`, exit 0).
