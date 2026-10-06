Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 12:13:39 UTC 2026
Notation: `N = sz.size n`, `B_u = Bctl n u`, `k = n_`, `τ` = stochastic-domination exponent (`ε₀ = τ/2`, `D₁ = D+2` for `nzGridEndN`), `𝔠` = flow bandwidth, `ε` = flow `locDomain` exponent (`RangeCond (ε/2)`). Scripts (Python, no Lean; mpmath 40 digits) in `$SCR` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2292` (`defs.py` = transcription of `STbootRHS`, `STn12(E)`, `nqLinPhi1-3`, `nqFlowLam/PhiC`, `Bparam`, `Bctl` from the merged files, as for T2246). `main` = fbec579 (`git log -1`; the worktree is at it).
### (i) Exponent table
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | `𝔠d := min 𝔠d_G 𝔠d_L` (`gridGoodN_holds d`, `nqLinGood_holds d` at the same `(κ,ε,𝔡,C_d)`) | `0<𝔠d ≤ 𝔠d_G ≤ 1/100`; no `1/(2d)`: the `nzGridEndN` statement has no `W⁻¹ ≤ (1−t)/(1−s)` premise (count 0, below) | none needed |
| 2 | `STConStInd 𝔠d s t ⇒ STConStInd 𝔠d_* s t`, `𝔠d_* ∈ {𝔠d_G,𝔠d_L}` | `B_t^{𝔠d} ≤ (1−t)/(1−s) < 1`, `B_t>0` ⇒ `B_t<1` ⇒ `B_t^{𝔠d_*} ≤ B_t^{𝔠d}` as `𝔠d ≤ 𝔠d_*` | exact |
| 3 | windows | `v n := u_n` if `s n < u_n`, else `t n`: `s<v≤t` (GridGoodN needs `s<v`); `STConStInd` on `[s,v]` by `st_conStInd_sub` (`s≤s, s<v, v≤t, t<1`); `STStep2Concl` restricts (`precomp_param`); `NQLinConcl` on `[s,t]` has `v` as binder; `STCaseII s t` concerns `s` only, so it holds on every `[s,v]` | none lost |
| 4 | premises of `nzGridEndN` at `κ/2`, `τ_R = ε/2` | `|E n| < 2−κ/2`, `t<1`, `RangeCond (ε/2) t`, `Admissible` (`𝔠>0`, `SizeTendsto`, `Bandwidth 𝔠`, `WO 𝔡`) from `v3_premises_of_stFlow` (`Green/Pins.lean:1049`); `Λ=max 1 (nqFlowLam …)≥1`, `Φ₁,Φ₂,Φ₃≥0` | instance (ii) |
| 5 | `e0=min(τ/2,1)`, `ε₁=e0/8`, `τ'=1`, `D''=2(k+2)/𝔠+1`, `D'=D''+1`, `C_K=D₁+2(Cmax+2k+2)+D''+16k+40` (`QtNonzeroEnd.lean:1046-1057`; `Cmax≥0` abstract from `nzEnd_yMomentsMax`, depends on `(κ,E,s,v,k)` only) | `ε₁,τ',D'>0`, `C_K≥0`; `nzGridEndN` quantifies every `ε₀>0`, `D₁>0`, so no absorption row is re-derived here | `ε₁ = τ/16 < ε₀ = τ/2`; `C_K ≥ 136` (`𝔠=1/6`, `Cmax=0`) |
| 6 | order | `(τ,D)` → section `(u_n,σ_n,A_n,a_n)` → `v` → `Λ,Φ₁,Φ₂,Φ₃` → `nzGridEndN` (`∀Λ Φ v ε₀ D₁ ∃ε₁ τ' D' C_K ∀Φc K`) → `Φc, K` → `GridGoodNConcl`, `NQLinConcl` at `(C_K+2, ε₁, τ', D')` → `STLK s` at `(k, ε₁/2, D+2)`; `ε₁` depends on `τ` only | each object after all it depends on |
| 7 | grid `K=max 1 ⌈N^{C_K}⌉` | `K≠0`, `N^{C_K}≤K≤⌈N^{C_K}⌉`, `K+1 ≤ N^{C_K+2}` for `N≥2` (`N^{C_K}(N²−1)≥2`) | crossover `log₁₀N=0.301`, 0 violations |
| 8 | failure | four events `≤N^{-(D+2)}` (`Gᶜ`, `GoodSetN` walk, `GoodLinN` walk, projected initial): `4N^{-(D+2)} ≤ N^{-D}` iff `N≥2` | `−1.4` at `N=10` |
| 9 | projected initial event (new) | `‖Q^{(A)}(𝓛−𝒦)_{s,σ,·}(a)‖ ≤ 2^{|A|} sup_b‖(𝓛−𝒦)_{s,σ,b}‖ ≤ 2^k N^{ε₁/2}B_s^k ≤ N^{ε₁}B_s^k` iff `2^k ≤ N^{ε₁/2}` (`|A|≤k`; `STLK s` at length `k≥2`, all `(σ,b)`) | eventual: `log₁₀N ≥ 192.7…5779.8` |
| 10 | collapsed `u_n=s_n` | `2^k N^{τ/2} ≤ N^τ ≤ N^τ ζ` iff `2^k ≤ N^{τ/2}`; `ζ ≥ S2 ≥ 3` | eventual: `log₁₀N ≥ 12.0…361.2` |
| 11 | terminal level | `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃) ≤ N^{τ/2}ζ ≤ N^τζ`, `sum ≤ ζ` exactly (no factor 3; `3N^{τ/2}≤N^τ` is not needed) | ratio max `1.000000000000`, 0 violations |
| 12 | `Λ` (R2*) | `Λ^{1/2}` = first summand of `STbootRHS 2 … B_s` exactly (row ratio `1.000000000000`); if `nqFlowLam<1`: `1+Φ₃ ≤ S2` | exact |
| 13 | `B` ratios (G1) | `B_s ≤ B_u ≤ B_t` (`STBctl_mono`), `B_s>0`, `log_N B_u ≥ −1` (`N⁻¹ ≤ B_u`); `log_N(B_t/B_s)∈[0.004, 0.70]` | table below |
| 14 | `Φc = Σ_{m≤k+1}(X_m+Y_m)` | `Φc ≥ 1`, `≥ X_m (m≤k+1)`, `≥ Y_m (m≤k)`; only the exit-time level of `GoodSetN` (statement has `Φc` twice: binder, `GoodSetN` argument) | 0 violations |
Constants and crossovers (`python3 consts.py`, rows for `𝔠=1/6`; `Cmax=0`; `log₁₀N*` = last positive `log₁₀(LHS/RHS)`):
```
$ python3 consts.py | grep -E "^(tau  |1/10 +1 +3 |1/100 +3 +6 |tau=1/10 .*(4N|2\^n_<=N\^\(eps1)|tau=1/100.*(4N|2\^n_<=N\^\(eps1)|K\+1)"
tau   D  n_ | eps0   e0     eps1   eps1/2   | D''   D'    C_K(Cmax=0) | crossover log10N: [4N^-(D+2)<=N^-D] [2^n_<=N^(eps1/2)] [2^n_<=N^(tau/2)] [3N^(tau/2)<=N^tau]
1/10  1  3  | 1/20   1/20   1/160   1/320    | 61    62    168      | 0.301  289.0  18.1  9.5
1/100 3  6  | 1/200  1/200  1/1600  1/3200   | 97    98    266      | 0.301  5779.8  361.2  95.4
tau=1/10  D=1 n_=3 4N^-(D+2)<=N^-D                                             -1.398     -3.398     -5.398    -11.398
tau=1/10  D=1 n_=3 2^n_<=N^(eps1/2)                                            +0.900     +0.897     +0.894     +0.884
tau=1/100 D=3 n_=6 4N^-(D+2)<=N^-D                                             -1.398     -3.398     -5.398    -11.398
tau=1/100 D=3 n_=6 2^n_<=N^(eps1/2)                                            +1.806     +1.806     +1.805     +1.804
K+1<=N^(C+2) violations on N in [2,200), C in {0,1/2,1,7/3,17}: 0
```
G1 (`python3 g1.py`, `d=3`, `N=(LW)^3`, `W=N^𝔠`, `g∈{1,W^{-1.4}}`, boundary `1−s=g²/L²`, `1−t=N^{-0.95}`, `1−u=√((1−s)(1−t))`; rows `log₁₀N=30` shown; the full run has 16 rows (`log₁₀N=3,6,12,30`)):
```
$ python3 g1.py | grep -E "^(c |0.167 .* 30 \||0.25 .* 30 \||all rows)"
c    g          log10N | L>=3 s<t s>=0 | log_N B_s  log_N B_u  log_N B_t | log_N(B_t/B_s)  B_s<=B_u<=B_t  log_N B_u>=-1 | B_s^(-1/4)>=1
0.167 1          30 | True True True | -0.5000   -0.3583   -0.0500 | +0.4500   True  True | True
0.167 W^-1.4     30 | True True True | -0.0333   -0.0333   -0.0294 | +0.0040   True  True | True
0.25 1          30 | True True True | -0.7500   -0.4417   -0.0500 | +0.7000   True  True | True
0.25 W^-1.4     30 | True True True | -0.0500   -0.0492   -0.0400 | +0.0100   True  True | True
all rows: B_s<=B_u<=B_t, log_N B_u>=-1, s<t, s>=0: True ; min log_N(B_t/B_s) = 0.003977556839547341 ; log_N B_s in [-0.7500, -0.0039]
```
Degree-1 / `Φc` / `S2` checks (`python3 deg1.py`, 40000 random `k∈[2,9], p∈[1,6], XL,XLK∈[1,10^8], B_s≤B_v≤1`, `Λ=max(1,·)`):
```
$ python3 deg1.py | sed -n '1,3p;6p'
cases 40000  max (Lam^1/2+Phi1+Phi2+Phi3)/zeta = 1.000000000000  violations(>1): 0
bridge: STbootRHS(B_v) <= STbootRHS(B_s) for B_s<=B_v: violations 0
Phi_c >= X_m (m<=k+1), >= Y_m (m<=k), >= 1: violations 0
S2=sum_{m=k-1}^{k+1} XL_m >= 3 and 1 + Phi3 <= S2: violations 0
```
`(normQA2)` (`3_5:1466`, `norm_zeroModeSet_le`), `d=3`, three indices over `M=L^d` points (`python3 qa2.py`):
```
$ python3 qa2.py
M=L^d=8: max ||Q^A T||/(2^|A| ||T||) over 40 random T, all 8 A: 1.0000 (<=1); idempotence defect 4.7e-16; Q^(0) on delta: 0.8750; on sign pattern: 1.7500 (<= 2-2/M = 1.7500)
M=L^d=64: max ||Q^A T||/(2^|A| ||T||) over 40 random T, all 8 A: 1.0000 (<=1); idempotence defect 7.0e-16; Q^(0) on delta: 0.9844; on sign pattern: 1.9688 (<= 2-2/M = 1.9688)
```
### (ii) One concrete nondegenerate instance
Data = merged `inst_OeqQtNZ` (`Step34Pins.lean:710-837`): `szB` (`d=3, L=4, W_n=n+4, lam=1`), `z_n=1/2+i/64`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `C_d=1`, `s≡15/16`, `t≡31/32`; pin data `k=3`, `p=1`, `XL≡XLK≡1`, `τ=1/10`, `D=1`; sections `u=t` and `u=61/64` (`s<u`, `v=u`) and `u=s` (collapsed); `σ=sig3=(+,−,+)`, `A={0,1}`. Command `python3 inst.py` (hypothesis checks at `n=0`, `N=4096`; sections at `n=0,10,10^6`; the `grep -v` drops the `n=10` and `u=mid` rows; `cut` truncates the long section lines at 300 characters):
```
$ python3 inst.py | grep -v -E "^(non-collapsed u=mid|collapsed u=s +n=10 |non-collapsed u=t +n=10 |   collapsed: zeta\(s\)=(1|3)|STbootRHS|$)" | cut -c1-300
z=1/2+i/64: msc= (-0.247982891211 + 0.960466955469j)  lemE=0.499983724824 lemT=0.983992286882 | |msc|<1: True
lemma28 identity (1-lemT)*Im mE(lemE) - sqrt(lemT)*Im z = -3.95e-42
3<=d, kappa,eps,fd,C_d>0                                                                     True
locDomain: |Re z|=1/2<=2-kappa=1.9 ; N^(-1+eps)=5.609e-04<=Im z=1/64 ; Im z<=1 (N=4096)      True
Admissible: Bandwidth 1/6: N^(1/6)=4.000000<=W=4 (n=0, equality: 4096^(1/6)=4) ; WO: W^(-1.4)=0.1436<=lam=1<=1/fd=10 True
0<=s=15/16<t=31/32<=lemT=0.983992287                                                         True
STCaseII: 1-s=1/16 <= lam^2/L^2=1/16 (equality)                                              True
v3_premises: |E|<=2-kappa/2=1.95 (|lemE|=0.5000<=|Re z|); t<1; RangeCond(eps/2): N^(-0.95)=3.700e-04<=1-t=1/32 True
n=0: B_s=1.861213e-02 B_t=2.296402e-02 (W^-3*(16/17+1/4), W^-3*(32/33+1/2)); B_s<=B_u<=B_t, B_s>0
n_=3: sig3=(T,F,T): Idiff= [0, 1]  ; #{(sigma,A): Idiff(sigma)<=A}=28 <= 4^n_=64 ; A=emptyset allowed for const sigma: True
non-collapsed u=t  n=0 u=0.96875: B_s=1.8612e-02 B_u=2.2964e-02 | Lam=7.3300e+00 Lam^1/2=2.7074e+00 first=2.7074e+00 (=,ratio 1.000000000000) | Phi1=1.0 Phi2=0.5331 Phi3=1.0 Phi_c=8.0 | S1=1.0 S2=3.0 S3=0.0 | zeta=7.2405e+00 sum=5.2405e+00<=zeta:True | N^(tau/2)*sum=7.9432e+00 <= N^tau*zeta=1.6634e+
collapsed u=s      n=0 u=0.9375: B_s=1.8612e-02 B_u=1.8612e-02 | Lam=7.3300e+00 Lam^1/2=2.7074e+00 first=2.7074e+00 (=,ratio 1.000000000000) | Phi1=1.0 Phi2=0.5148 Phi3=1.0 Phi_c=8.0 | S1=1.0 S2=3.0 S3=0.0 | zeta=7.2222e+00 sum=5.2222e+00<=zeta:True | N^(tau/2)*sum=7.9154e+00 <= N^tau*zeta=1.6592e+0
   collapsed: zeta(s)=7.2222e+00 >= 3 (S2>=3): True ; STLK s at tau/2: ||Q^A(L-K)_s||/B_s^3 <= 2^3 N^(tau/2) <= N^tau <= N^tau*zeta  needs 2^3<=N^(tau/2) i.e. log10 N>=18.06
non-collapsed u=t  n=1000000 u=0.96875: B_s=1.1912e-18 B_u=1.4697e-18 | Lam=9.1625e+08 Lam^1/2=3.0270e+04 first=3.0270e+04 (=,ratio 1.000000000000) | Phi1=1.0 Phi2=0.0011 Phi3=1.0 Phi_c=8.0 | S1=1.0 S2=3.0 S3=0.0 | zeta=3.0274e+04 sum=3.0272e+04<=zeta:True | N^(tau/2)*sum=2.9604e+05 <= N^tau*zeta=2.
collapsed u=s      n=1000000 u=0.9375: B_s=1.1912e-18 B_u=1.1912e-18 | Lam=9.1625e+08 Lam^1/2=3.0270e+04 first=3.0270e+04 (=,ratio 1.000000000000) | Phi1=1.0 Phi2=0.0010 Phi3=1.0 Phi_c=8.0 | S1=1.0 S2=3.0 S3=0.0 | zeta=3.0274e+04 sum=3.0272e+04<=zeta:True | N^(tau/2)*sum=2.9604e+05 <= N^tau*zeta=2.8
eventual thresholds at szB (N=64 W^3, W=n+4; tau=1/10, n_=3, D=1; eps0=tau/2=1/20, e0=1/20, eps1=1/160):
  2^n_ <= N^(eps1/2)  [initial event]      log10 N >= 288.99  <=> n >= ~10^95.73 (W=(N/64)^(1/3))
  2^n_ <= N^(tau/2)    [collapsed]         log10 N >= 18.06  <=> n >= ~10^5.42 (W=(N/64)^(1/3))
  N>=2: 4N^-(D+2)<=N^-D                    log10 N >= 0.30  <=> n >= ~10^-0.50 (W=(N/64)^(1/3))
STConStInd cd (eventual; 1-t)/(1-s)=1/2: B_t(n)^cd<=1/2 iff log10 W >= (ln2/cd + ln(32/33+1/2))/(3 ln10):
  cd=1/100: log10 n0 ~ 10.09
  cd=1/1000: log10 n0 ~ 100.40
  cd=1/1000000: log10 n0 ~ 100343.39
limit computation (szB, n->inf): log_N B_s, log_N of first summand B_s^(-1/4), log_N zeta(u=t) -> exact limits -1, +1/4, +1/4
  n=1e1    log_N B_s=-0.641122  log_N first=0.160281  log_N zeta=0.200153  log_N (B_t/B_s)=0.017399
  n=1e6    log_N B_s=-0.904971  log_N first=0.226243  log_N zeta=0.226246  log_N (B_t/B_s)=0.004607
  n=1e12   log_N B_s=-0.950216  log_N first=0.237554  log_N zeta=0.237554  log_N (B_t/B_s)=0.002414
  n=1e30   log_N B_s=-0.979499  log_N first=0.244875  log_N zeta=0.244875  log_N (B_t/B_s)=0.000994
```
Reading: every deterministic hypothesis of `stOeqNZPT''_holds` at these data holds at `n=0` (no `N=0`, `L=4`, window `[15/16,31/32]` nondegenerate, equality `1−s=lam²/L²` = `STCaseII` boundary, `v>s`, index set of 28 pairs `(σ,A)` with `Idiff σ ⊆ A`, `A=∅` allowed for constant `σ`). `STConStInd 𝔠d` (`𝔠d` abstract from the merged theorems), `STLK`, `STKbound`, `STKward`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` are hypotheses of the instance (other gates' pins); all `∀ᶠ n` conclusions are never evaluated at `n=0` (thresholds above: `log₁₀N ≥ 289` for the initial event, `n ≥ 10^{10.09}/10^{100.4}/10^{100343}` for `STConStInd` at `𝔠d=10^{-2}/10^{-3}/10^{-6}`). **External hypotheses:** none new (`nzGridEndN`, `gridGoodN_holds`, `nqLinGood_holds` are merged theorems, no declared axiom); limit computation for the quantity entering the right side: `log_N B_s → −1`, `log_N(first summand `B_s^{-1/4}`) → 1/4`, `log_N ζ → 1/4` along `szB` (rows `n=10…10^{30}` above), `Λ_s ≥ 1`, `ζ ≥ 3` throughout.
Pin/consumer text checks (`sh pin.sh`; `QtNonzeroFlow.lean` does not exist yet, so the ticket's `grep … QtNonzeroFlow.lean` is a stage-1b check):
```
$ sh pin.sh
diff hunks, merged STNQConclPT'' (NQEndFlow.lean) vs check-file STNZConclPT'':
1c1
8c8
10c10,12
pin text counts: ' ^ 2'=0 'Φc'=0 STKbound=0 finRotate=0 STIdiff=1
nzGridEndN statement (QtNonzeroEnd.lean:979-1023) counts: Φc=2 ' ^ 2'=0 STKbound=0 W^-1-window=0 STCaseII=1 RangeCond=1
QtNonzeroEnd.lean: dDriftLinN=4 ; dDriftNonAltN|budgetNonAltN|dDriftAltQN|alt_hdriftQN|dFlowQN_levelM=0
STNewPQ (Step34Pins.lean:330-345): '1 ≤ k α ∧ k α + 1 ≤ m' x1, 'STIdiff (σ' α) ⊆ A' α' x2 ; STXiBoot' (NQEndFlow.lean:95-100) XLK pair hyp 'm + 1 ≤ n_' x1
```
### Verdicts
- **Target 1 (pins `STNZConclPT''`, `STOeqNZPT''`): PASS.** Diff against the merged `STNQConclPT''` = the header (binders `{d} (sz)`, from `variable`), the index set `{σA // STIdiff σA.1 ⊆ σA.2}`, the quantity `‖zeroModeSet …‖` (hunks `1c1, 8c8, 10c10,12`); hypotheses, `/B_u^{n_}` and right side (`B_u^{1/6}XLK n_ + STbootRHS 2 … B_s`, no `^2`, no `Φc`) unchanged.
- **Targets 2–5 (window facts, levels, `Q^{(A)}` facts, core and section): PASS** (rows 1–14). The initial event (row 9) and the collapsed bound (row 10) need only eventual `2^k ≤ N^{ε₁/2}`, `2^k ≤ N^{τ/2}`; the large crossovers (`192.7…5779.8`) are `∀ᶠ n` thresholds, never hypotheses.
- **Target 6 (`stOeqNZPT''_holds`): PASS.** `perTimeDomAt_iff_forall_section` needs `U n` nonempty: `(s n, ⟨(fun _ => true, univ), subset_univ⟩, fun _ => 0)`.
- **§29/§45 O2:** (1) `0≤s`, `s<t≤lemT z` are `STIngR`'s; `t<1`, `RangeCond (ε/2) t`, `|E|<2−κ/2` from `v3_premises_of_stFlow`. (2) case-(ii) boundary: `STCaseII s t` passes to `nzGridEndN` unchanged on every `[s,v]`, `s≤v≤t`; the EK-5 window is internal to `nzGridEndN`. (3) no `L^d ≤ W^K`, no `W⁻¹ ≤ (1−t)/(1−s)` (count 0). (4) every numerical condition is `∀ᶠ n` (rows 7–10). (5) per-time `PrecPT`, union over `u` outside `P`. (6) `GridGoodNConcl`, `NQLinConcl` from `STAny` pins at `trivial`. (7) scale `N=sz.size n`. All PASS.
- **§95 (3) level check: PASS.** `Λ,Φ₁,Φ₂,Φ₃,Φc` are deterministic functions of the controls; the current length enters only as `B_v^{1/6}·XLK n_` inside `Φ₂` (degree 1, self-absorbing) and `Y n_` inside `Φc` (exit time only); the `nzGridEndN` statement has no `^2` and no `STKbound`; the drift level is `dDriftLinN` (4 uses in `QtNonzeroEnd.lean`), the five non-alternating/`Q`-budget names have count 0.
- **G1: PASS** (rows 12–13: `Λ^{1/2}`/first summand `=1.000000000000`; `log_N(B_t/B_s) ≥ 0.004` on all 16 rows, `B_s≤B_u≤B_t`, `log_N B_u ≥ −1`; `ζ♯` of T2292b non-decreasing needs only `STBctl_mono`). **G2: PASS** (every binder of `nzGridEndN` discharged as in Design; the good-walk hypothesis is the intersection of the `GoodSetN` and `GoodLinN` events with the spelling `gridTime s v K n j`, `N^{ε₁}`; initial hypothesis = row 9 after the `j=0` transfer; conclusion at `j=K n` is the section's quantity by `rfl`).
- **Consumer fit for S3-22c (iv): PASS (text).** `STNewPQ` carries `1 ≤ k α ∧ k α+1 ≤ m` and `STIdiff (σ' α) ⊆ A' α`, so every term of `(eq:expandQAempty)` (`3_5:1893`) with `k_α≥2` lies in the pin's index set; the main term `A∪Idiff σ ⊇ Idiff σ`; `k_α=1` by `(normQA2)`. `STXiBoot'` has the `XLK` pair hypothesis only for `m+1≤n_`, the pin for `m≤n_` (the self-absorption step of S3-22c, as for `STNQConclPT''` vs `STXiBoot'`); `STbootRHS 2 ≤ STbootRHS 1` (5000 random cases, 0 violations).
- Findings (no verdict change): (1) the initial event needs `STLK s` at `ε₁/2 = τ/32`, so its threshold `2^k ≤ N^{τ/32}` is `log₁₀N ≥ 192.7…5779.8`, eventual only; (2) `3N^{τ/2} ≤ N^τ` of the ticket is not needed (sum `≤ ζ`); (3) the G1 data of the ticket at `𝔠=1/4, log₁₀N=3` has `L<3` (not an admissible `Sizes`); the formulas are unaffected.
## (b) Script output — Tue Oct  6 12:42:35 UTC 2026
```
$ date -u; git log -1 --format="%h %an %s"; git diff --stat main...t/T2292; git status --short | wc -l
Tue Oct  6 12:42:35 UTC 2026
edf0117 Jun Yin T2292: S3-22b Induction/QtNonzeroFlow, per-time case-(ii) projected endpoint (stOeqNZPT''_holds; pins STNZConclPT'', STOeqNZPT'')
 RBM3D/Induction/QtNonzeroFlow.lean | 989 +++++++++++++++++++++++++++++++++++++
 1 file changed, 989 insertions(+)
worktree changes after the commit:        0
$ lake build RBM3D.Induction.QtNonzeroFlow 2>&1 | tail -6
ℹ [3851/3851] Replayed RBM3D.Induction.QtNonzeroFlow
info: RBM3D/Induction/QtNonzeroFlow.lean:986:0: 'RBM.Gauss.Sizes.STNZConclPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroFlow.lean:987:0: 'RBM.Gauss.Sizes.STOeqNZPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroFlow.lean:988:0: 'RBM.Ind.stOeqNZPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroFlow.lean:989:0: 'RBM.Ind.QtNonzeroFlowInst.inst_OeqNZPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3851 jobs).
$ grep/wc checks on the file
lines:      989; public decls: 4; private decls: 30; examples: 10
imports: Induction.QtNonzeroEnd Induction.NQEndFlow Induction.GridGoodN Induction.NQLin Induction.ScaleFacts3 Induction.ZeroModeCalc Induction.Step2Events Green.Pins 
sorry|admit|axiom|native_decide|maxHeartbeats: 0 hits; §95(3) names dDriftNonAltN|budgetNonAltN|dDriftAltQN|alt_hdriftQN|dFlowQN_levelM: 0 hits
' ^ 2' / 'Φc' / 'STKbound' in the pin text: 0 hits; st_window: 1 hit(s), the docstring line: 833:`1/(2d)` in `𝔠_d`: case (ii) uses no `st_window` and `nz
$ target statements, extracted from the file by script (awk from the `def` line to the first blank line)
def STNZConclPT'' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

def STOeqNZPT'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E s t)
theorem stOeqNZPT''_holds : ∀ d : ℕ, STOeqNZPT'' d := by
$ the compiled nonempty instances (namespace RBM.Ind.QtNonzeroFlowInst): (1) and (2) in full, then the first line of every other example
theorem inst_OeqNZPT'' :
    InstIngConcl (fun sz E s t => STNZConclPT'' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STNZConclPT'' sz E s t) (stOeqNZPT''_holds 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
    (hStep2 : STStep2Concl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiL szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ))) :
    PrecPT szB (U := fun n => TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
        {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} × (Fin 3 → Zd 3 (szB.L n)))
      (fun n q ω => ‖zeroModeSet 3 (szB.L n) q.2.1.1.2
          (fun b : Fin 3 → Zd 3 (szB.L n) =>
            Lloop szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1.1 b ω -
              STKloop szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (szB.Bctl n (q.1 : ℝ)) ^ 3)
      (fun n q _ => (szB.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 2 (fun _ => 1) (fun _ => 1) (szB.Bctl n (15 / 16)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqNZPT''
  exact hC (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp
919:example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16)) :
929:example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16)) :
941:example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16)) :
952:example (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 4) :
958:example (a : Fin 3 → Zd 3 (szB.L 0)) :
966:example (n : ℕ) : Nonempty (TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
970:example : ∃ x : {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2},
974:example : STIdiff sig3 = ({0, 1} : Finset (Fin 3)) := σ3_idiff
978:example : ∀ d : ℕ, STOeqNZPT'' d := @stOeqNZPT''_holds
$ statement script: docs/tickets/checks/T2292-check.lean + `import RBM3D.Induction.QtNonzeroFlow` + the two examples; lake env lean
example : RBM.Gauss.Sizes.T2292Check.T2292_stOeqNZPT''_holds := @RBM.Ind.stOeqNZPT''_holds
example : ∀ d : ℕ, RBM.Gauss.Sizes.T2292Check.STOeqNZPT'' d := @RBM.Ind.stOeqNZPT''_holds
exit: 0; lines containing 'error': 0; last line: 'RBM.Ind.stOeqNZPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ pin text diffs (scripts: pindiff.py extracts each def from its file; diff)
body lines (check, file): 14 14
body identical (check lines 2.. vs file lines 2..): True
STOeqNZPT'' file  : ["def STOeqNZPT'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E 
STOeqNZPT'' identical: True
merged STNQConclPT'' (NQEndFlow.lean:107) vs STNZConclPT'': hunks 1c1 8c8 10c10,12 
$ name clash: grep -rn -F <name> RBM3D RBM3D.lean (new file excluded): worktree / main worktree
 STNZConclPT'':0/0 STOeqNZPT'':0/0 stOeqNZPT''_holds:0/0 inst_OeqNZPT'':0/0 QtNonzeroFlowInst:0/0 nzFlow_:0/0
main worktree HEAD: 1ba63a2; branch base: fbec579
$ registry pre-check: lake env lean reg_before.lean / reg_after.lean   # `import RBM3D` [+ `import RBM3D.Induction.QtNonzeroFlow`] + `#assert_rbm_axioms`
before: exit 0; axiom audit: 8371 theorems, 2784 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
after:  exit 0; axiom audit: 8373 theorems, 2786 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff of the ledger lines after line 1: empty
premises found by scanning: 152 (borrowed 1, owed 94, structural 40, refuted 6, superseded 11).
$ lake build   # whole library in the worktree after the commit; `RBM3D.lean` does not import the new module (the hub adds the root import at merge)
Build completed successfully (4098 jobs).
full build exit: 0
$ ports: last commits of the merged files the private copies come from; RBM1D/RBM2D
NQEndFlow.lean 0f60da2; QtNonzeroEnd.lean 9664e13; no RBM1D/RBM2D file was read, built or diffed in this stage
git status after all runs:        0 changes
```

**Narrative** (facts from the files and the tool log above)
1. Scope: new file `RBM3D/Induction/QtNonzeroFlow.lean`, 989 lines, commit `edf0117` on `t/T2292`; `git diff --stat main...t/T2292` lists only this file. 4 public declarations (`STNZConclPT''`, `STOeqNZPT''`, `stOeqNZPT''_holds`, `QtNonzeroFlowInst.inst_OeqNZPT''`), 30 private helpers (prefix `nzFlow_`), 10 `example`s. Imports: the ticket's list plus `Induction.Step2Events` (`ST_gridTime_zero`); neither `RBM3D` nor `NQEndFlowLift`. No `set_option maxHeartbeats`; the three linter options of `NQEndFlow.lean` are set. No hypothesis added, no target weakened, no pinned signature or merged file changed; `Test/Axioms.lean` and `RBM3D.lean` untouched; the registry ledger is identical before and after (the +2 theorems, +2 definitions are the four public declarations).
2. Pins: `STNZConclPT''` (`:75`) and `STOeqNZPT''` (`:95`) are identical to the check file (14 body lines; one line); against the merged `STNQConclPT''` the diff has exactly the three hunks (name, index set `{σA // STIdiff σA.1 ⊆ σA.2}`, quantity `‖zeroModeSet …‖`). `stOeqNZPT''_holds` (`:837`) has the pinned type: the statement script exits 0.
3. Copies: 330 lines are private copies of `NQEndFlow.lean` (ranges `205-211`, `293-331`, `347-355`, `359-421`, `427-503`, `505-583`, `593-630`, `802-819`, renamed `nqFlow_ ↦ nzFlow_`); `nqFlowLam`, `nqFlowPhiC` are reused, not redefined.
4. `stOeqNZPT''_holds`: `𝔠d := min 𝔠G 𝔠L` (no `1/(2d)`, no `st_window`); `v3_premises_of_stFlow` at `(κ/2, ε/2)`; `STConStInd` passes to `𝔠G`, `𝔠L` (`nzFlow_conStInd_exp_mono`); `gridGoodN_holds` is applied on every window `[s, v]`, `s < v ≤ t` (`st_conStInd_sub`, `nzFlow_step2_restrict`), `nqLinGood_holds` on `[s, t]`; `perTimeDomAt_iff_forall_section` (`U n` nonempty by `(s n, ⟨(fun _ => true, univ), subset_univ⟩, 0)`) reduces to `nzFlow_section` (`:747`) at a section `q n = (u_n, ⟨(σ_n, A_n), h_n⟩, a_n)`: `v n := u_n` if `s n < u_n`, else `t n`; controls `XL m n (v n)`, `XLK m n (v n)` on `[s, v]` (`nzFlow_restrict_pair`).
5. `nzFlow_core` (`:577`; the shape of `nqFlow_core`, `NQEndFlow.lean:642`, without `hσ`, `hWt`; `STCaseII`; `A n ⊇ STIdiff (σ n)`): levels `Λ = max 1 (nqFlowLam X B_s n_ p)`, `Φ₁ = nqLinPhi1`, `Φ₂ = nqLinPhi2 … B_v … (Y n_ n)`, `Φ₃ = nqLinPhi3`, `Φc = nqFlowPhiC` (deterministic functions of the controls); `nzGridEndN` at `ε₀ = τ/2`, `D₁ = D+2`; grid `K = max 1 ⌈N^{C_K}⌉`. The failure event lies in the union of four events of probability `≤ N^{-(D+2)}` (`GoodSetN` walk by `hGrid`, `GoodLinN` walk by `hLin`, projected initial event, `Gᶜ`), and `4N^{-(D+2)} ≤ N^{-D}` for `N ≥ 2`; outside it the terminal projected loop is `≤ N^{τ/2}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^{n_} ≤ N^τ ζ B_v^{n_}` (`nzFlow_level_le`: the sum is `≤ ζ`, so the factor 3 of the ticket's Design is not needed, as in (a) finding (2)). Transfers: `map_pathH_eq` at `j = K n` (`gridTime_last`) and `j = 0` (`ST_gridTime_zero`); `STLKM … (seqHflow …) = Lloop … - STKloop …` holds by `rfl`.
6. New here: `nzFlow_proj_le` (`:467`, `(normQA2)`: `‖(Q^{(A)}T)_a‖ ≤ 2^k x` if every `‖T_b‖ ≤ x`); `nzFlow_meas_proj` (`:481`, measurability of `H ↦ ‖(Q^{(A)}(𝓛-𝒦)_{u,σ,·}(H))_a‖`: `Measurable.of_eval`, `zeroModeSetLin`, `LinearMap.continuous_of_finiteDimensional`); `nzFlow_initQ` (`:497`): `P(∃ σ A a, N^ε B_s^k < ‖(Q^{(A)}(𝓛-𝒦)_{s,σ,·})_a‖) ≤ N^{-D}` eventually, from `STLK s` at `ε/2` and `2^k ≤ N^{ε/2}`; used at `(ε₁, D+2)` for the initial hypothesis of `nzGridEndN` (through the measurable matrix event `Sinit`) and at `ε = τ` for the collapsed sections; `nzFlow_collapsed` (`:534`): sections `u_n = s_n` are `≺ ζ` for every `ζ ≥ 1` (here `ζ` is the pin's right side at `u = s`, `≥ 1` by `nzFlow_bootRHS_one_le`). `STIngR` needs `s < t`, so the good-event lemmas have no window `[s, s]`; collapsed indices take `v n := t n` and are bounded by `nzFlow_collapsed`.
7. Instances (§7; data of `inst_OeqQtNZ`: `szB` with `d=3, L=4, W=n+4, ilambda=1`, `zB`, `s ≡ 15/16`, `t ≡ 31/32`, `𝔠 = 1/6`, `κ=ε=𝔡=1/10`, `C_d=1`): (1) `inst_OeqNZPT''` by `inst_ing` with every deterministic hypothesis discharged (`szB_caseII`: `1-s = 1/16 = lam²/L²`; `(con_st_ind)` for every `𝔠d` by `conStInd_const`); (2) its conclusion at `n_=3`, `p=1`, `XL ≡ XLK ≡ 1`, with `STKbound`, `STKward` from `stKbound_of_flow`, `stKward_of_flow`; the hypotheses left are `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` (other gates' pins); (3) `nzFlow_initQ` (`k=3`, `ε=1/160`, `D=3`; also at one size index), `nzFlow_collapsed` (`σ = sig3`, `A = {0,1}`, `ζ ≡ 1`), `nzFlow_proj_le`, `nzFlow_meas_proj`; (4) the parameter type of the pin is nonempty, with members `(sig3, {0,1})` (`σ3_idiff`) and `(const +, ∅)`; (5) `example : ∀ d, STOeqNZPT'' d := @stOeqNZPT''_holds`.
8. (a′): none. The constants of rows 5 and 7 of (a) are those of `nzGridEndN`'s proof (`QtNonzeroEnd.lean:1046-1057`) and `nzFlow_K_card`; rows 11-12 are `nzFlow_level_le`.

## (c) Verified Mathlib names used (new in this file; `#check`s run by `lake env lean`, exit 0; none was found absent; names inside the private copies are those of the merged `NQEndFlow.lean`)
```
Measurable.of_eval : (∀ a, Measurable fun c => f c a) → Measurable f   [`measurable_pi_lambda` is a deprecated alias since 2026-08-20; not used]
LinearMap.continuous_of_finiteDimensional : (f : E →ₗ[𝕜] F') → Continuous ⇑f   [T2Space E, FiniteDimensional 𝕜 E]
LinearMap.proj : (i : ι) → ((i : ι) → φ i) →ₗ[R] φ i
pi_norm_le_iff_of_nonneg : 0 ≤ r → (‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r)
norm_le_pi_norm : (f : (i : ι) → G i) → (i : ι) → ‖f i‖ ≤ ‖f‖
Finset.card_le_univ : (s : Finset α) → s.card ≤ Fintype.card α
Fintype.card_fin : (n : ℕ) → Fintype.card (Fin n) = n
pow_le_pow_right₀ : 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n
tendsto_rpow_atTop : 0 < y → Tendsto (fun x => x ^ y) atTop atTop
Filter.Tendsto.eventually_ge_atTop : Tendsto f l atTop → (c : β) → ∀ᶠ x in l, c ≤ f x
MeasurableSet.iUnion : (∀ b, MeasurableSet (f b)) → MeasurableSet (⋃ b, f b)   [Countable ι]
measurableSet_lt : Measurable f → Measurable g → MeasurableSet {a | f a < g a}
Measurable.div_const : Measurable f → (c : G) → Measurable fun x => f x / c
Continuous.measurable : Continuous f → Measurable f
Measurable.comp : Measurable g → Measurable f → Measurable (g ∘ f)
Measurable.norm : Measurable f → Measurable fun a => ‖f a‖
lt_div_iff₀ : 0 < c → (a < b / c ↔ a * c < b);   div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)
```

## (d) Open issues and paper-delta candidates
- `T2292a`: Lean states the per-time case-(ii) endpoint at the flow for `Q^{(A)}(𝓛-𝒦)^{(n_)}`, every `σ`, every `A ⊇ I_diff(σ)` (`STNZConclPT''`), with the first summand of `STbootRHS` at `B_s` (R2*, DECISIONS §80 (1)) and the controls `XL m n u`, `XLK m n u` taken at the endpoint `u`; the paper states `(am;asoiuw_smalleta)` (`3_5:1914-1919`) at `u = t`, with `sup_{u∈[s,t]}` of the controls on the right, and says "the same argument applies to each fixed `u`" (`3_5:1931`). The uniform-in-`u` form is T2292b.
- `T2292c`: the projected initial assumption `‖(Q^{(A)}(𝓛-𝒦))_{s,σ,a}‖ ≤ N^{ε₁}B_s^k` is derived from `(Eq:L-KGt+IND)` at `s` (`STLK s`) with `(normQA2)` (`3_5:1466`, `:1902`) at the half exponent `ε₁/2`; it needs `2^{n_} ≤ N^{ε₁/2}` eventually (thresholds in (a) row 9).
- `T2292d`: the collapsed sections `u_n = s_n` are bounded directly by `STLK s` and `(normQA2)` (`nzFlow_collapsed`), because `STIngR` has `s < t` and no good-event lemma exists on `[s, s]` (D597's separate case).
- `T2292e`: `STStep2Concl` and the pair hypotheses are restricted from `[s,t]` to `[s,v]`, `v = u_n`, per section (`nzFlow_step2_restrict`, `nzFlow_restrict_pair`), as T2246b for case (i); the paper does not state this restriction.
- `T2292f`: the crude level `Φc` of `GoodSetN` is the sum `nqFlowPhiC` of the controls of lengths `1…n_+1` (`nzGridEndN` reads only the `STeeM` clause of `GoodSetN`), as T2246c.
- Observations (no statement affected): (i) the pin's `XLK` hypothesis is for `m ≤ n_`, `STXiBoot'` has `m + 1 ≤ n_` ((a) (iv)): S3-22c's self-absorption step; (ii) `STOeqQtNZ'` stays owed (`Test/Axioms.lean:126`), S3-22c deletes it; (iii) S3-22c needs `STNZConcl''` from T2292b (`stOeqNZ''_holds`), not this file.
