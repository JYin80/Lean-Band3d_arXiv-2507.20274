Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 05:14:12 UTC 2026

### (i) Exponent table (N = sz.size n; every condition eventually in n; `n_ ≥ 2`, `p ≥ 1`, `k ≥ 2`)
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | mesh `A` (core `hclose`: `u−θ ≤ N^{-A}`) | `6n_+20` | term `‖Δ𝓛‖B_u^{-n_} ≤ 3n_N^{3n_+7−A/2} ≤ 1/2`: `A/2 > 3n_+7` | `A/2−(3n_+7)=3`; `A>6n_+14` suffices; larger `A` fine |
| 2 | floor net spacing `1/netSize(A+1,N)` | `≤ N^{-A-1}` | `≤ N^{-A}` (core `hdist`, unchanged) | factor `N` |
| 3 | `‖Δ𝓛‖` (`LemDecCalELip_Lloop_sub`) | `3n_N^{2n_+7}√δ` | needs `\|E\|<2`, `1 ≤ N`, `(etaT E t)⁻¹ ≤ N²` | see 6 |
| 4 | `‖Δ𝒦^{(n_)}‖` (step 4 at `k=n_`) | `N^{2n_+2}δ` | exponent below | see 5 |
| 5 | `𝒦^{(k)}` modulus `‖treeEqRhs‖` | true count `k²C²2^kN^{k+3}`; pin `N^{2k+2}` | `N^{k-1} ≥ k²2^kC²` | `k−1 ≥ 1` (k=2: `N^5` vs `N^6`); `N*` for `C=1,10,100` in the table below |
| 6 | `(etaT E t)⁻¹ ≤ N²` | `(1−t)⁻¹·(Im m)⁻¹` | `(1−t)⁻¹ ≤ N^{1−ε/2} ≤ N` (`RangeCond(ε/2)`), `(Im m)⁻¹ ≤ 1/c₁ ≤ N`, `c₁=√(κ/2)/2` | `N ≥ 9` (κ=1/10), `N ≥ 29` (κ=1/100) |
| 7 | `Bctl` bounds | `N⁻¹ ≤ Bctl(r) ≤ 2W^{-d}(1−t_n)⁻¹ ≤ 2N` (`r ≤ t_n`; `cont_inv_size_le_Bctl`, `cont_Bctl_eq`) | `B_u⁻ⁿ ≤ N^{n_}` | exact |
| 8 | tree-sum factors | `W^dL^{2d} = N·L^d ≤ N²`, `L² ≤ L^d ≤ N`, `#pairs ≤ k²`, `Bctl^k ≤ (2N)^k` | gives `N^{k+3}` | — |
| 9 | `#V ≤ N^{Cv}` | `Cv=2n_` (`#σ ≤ 2^{n_}`, `#a = L^{dn_} ≤ N^{n_}`) | `2^{n_} ≤ N^{n_}`, `N ≥ 2` | `N^{n_}/2^{n_}` |
| 10 | `ε n` | `1` | `ε n ≤ ζ♯`; `ζ♯ ≥ 1` (copy of `nqFlow_bootRHS_one_le`, `lo=2`, `B_s>0`) | none needed |
| 11 | one-sided `hclose` | `ξ(u) ≤ ξ(θ)+1`, `ζ♯(θ) ≤ 2ζ♯(u)` for `θ ≤ u` | `‖𝓛_u−𝒦_u‖ ≤ ‖𝓛_θ−𝒦_θ‖+‖Δ𝓛‖+‖Δ𝒦‖`, `B_u ≥ B_θ` (`STBctl_mono`) so `‖𝓛_θ−𝒦_θ‖B_u^{-n_} ≤ ξ(θ)` | the ticket's ratio terms (`‖𝓛_θ‖,‖𝒦_θ‖` times `(B_θ^{-n_}−B_u^{-n_})`) are not needed in this direction; they are `≤ N^{3n_+2−A}`, kept below |
| 12 | `ζ♯` monotone in `u ≤ t_n` | `B_θ^{1/6}≤B_u^{1/6}`, `XL♯,XLK♯` nondecreasing, first summand's `B_s` fixed, `STbootRHS` monotone in the controls (`B_s>0`, exponents `≥ 0`) | `θ ≤ u ≤ t_n < 1` | exact |
| 13 | constants | `𝔠d` = the one of `stOeqNQPT''_holds d κ ε 𝔡 C_d`; `KLbound_holds` constants depend on `(d,m≤k,κ,gmax=𝔡⁻¹,τ=1)` only (`KLBoundAt`, `KLInduct.lean:89`) | independent of `n` | no new constant |

Bad-set inclusion (envelope): `X♯(u)=max(1,inf_{u'∈[u,t_n]}X(u'))`, `X ≥ 1`, `u ≤ t_n`. If `N^τX♯(u) < Ξ̂_w` for some pair `(w,u)` (`s ≤ w ≤ u ≤ t`), then `inf < Ξ̂_w/N^τ` gives `u' ∈ [u,t_n]` with `N^τX(u') < Ξ̂_w`; `(w,u')` is a pair, so the `X♯`-bad event is inside the `X`-bad event (one `Prec`, `StochDomAt.of_subset`). The left sides of all pair hypotheses of `STNQConclPT''` depend on `q.1.1` only (`NQEndFlow.lean:79-93`: `fun n q ω => STXiL/STXiLK … q.1.1 m ω` against `fun n q _ => X m n q.1.2`).
Cut lengths (`length_cutGlueL/R`): `k+n−l+1`, `l−k+1`, both in [2,n], total `n+2`; `KLK_isKLoop` is on `Ico 0 1`, used on `Icc 0 t_n ⊂ Ico 0 1`.

### (ii) Concrete nondegenerate instance and checks
Instance: `d=3`, `sz0` at `n=0` (`L=4,W=32,N=2^21`, `lam=1/64`), `z0 0 = 1/2+iN^{-4/5}`, `κ=ε=1/10`, `𝔡=1/10` (`gmax=10`), `𝔠=1/6`, `C_d=1`, `s≡0`, `t≡1/16`, `n_=3`, `p=1`; controls with a jump in `u` (`X=3,1.5,4` on `[0,1/32),[1/32,3/64),[3/64,1/16]`, scaled by `1+m/10`, `X=1` beyond `t`). The script also checks the `K^{(3)}` tree equation with the Lean `cutGlue` definitions and computes effective `KLbound` constants. Command (scratch, no Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2258/preflight.py`
```
G2: random step controls, 3000 draws (p in {1,4}, n_ in {2,3,6}), checks: 42000 envelope evaluations
G2 violations (a) 1<=X#, (b) X#<=X, (c) mono, (d) bad-set inclusion, (e) z#(th)<=z#(u), (f) z#<=z, (g) z#>=1: [0, 0, 0, 0, 0, 0, 0]
G6: floor net point (netSize=ceil(N^A)+1, k=floor(x*netSize), 120-digit arithmetic): 20000 random draws, violations: 0
instance sz0,n=0: d=3 L=4 W=32 N=2097152 (=2^21) lam=1/64 z0=1/2+i*8.764e-06  E=lemE(z0)=0.500000000  lemT=0.999990949 >= 1/16: True
  |E|<=2-kappa (kappa=1/10): True; Im m(E)=0.968246 >= sqrt(kappa/2)/2=0.111803: True; etaT(E,t)^-1=1.1016 <= N^2: True; (1-t)^-1=1.0667 <= N: True
  Bctl(0)=3.098697e-05 Bctl(1/16)=3.305223e-05  Bctl(0)<=Bctl(t): True ; Bctl(t) <= 2 W^-d (1-t)^-1 = 6.510417e-05: True ; N^-1=4.768e-07 <= Bctl(0): True
  X#(u) at u=0,1/32,3/64,1/16,1 (X=3,1.5,4 steps; mm=1): [1.65, 1.65, 4.4, 4.4, 1.0]  X(u): [3.3, 1.65, 4.4, 4.4, 1.0]
  zeta#(u) at u= [0, 0.0156, 0.025, 0.0312, 0.0469, 0.0625] = [32.1976, 32.1985, 32.1991, 32.1994, 71.8332, 71.8358]
  zeta# nondecreasing: True ; zeta# <= zeta: True ; zeta# >= 1: True ; zeta(0)=56.6939
  #{non-alternating sigma}: n_=2:2 n_=3:8 n_=6:62 (<= 2^n_);  #V=#sigma*L^(d n_) <= 2^n_ N^n_ <= N^(2 n_): n_=3: 2097152 <= 85070591730234615865843651857942052864: True
  S^(B): row sums in [1.000000000000,1.000000000000], symmetric: True
  empirical Lipschitz of K^(2), K^(3) on [0,1/16] (sup over sigma,a, grid step 1/256): 3.4521e-05, 2.7709e-09;  N^(2k+2) = N^6, N^8 = 8.507e+37, 3.741e+50
  effective constants (tau=0) C_2=sup|K2|/Bctl = 0.9849, C_3=sup|K3|/Bctl^2 = 0.9699
  tree equation (pro_dyncalK) at t0=1/32, sigma=(+,+,-): d/dt K3 (central diff) = -5.790999e-14+2.534938e-13i ; treeEqRhs = -5.790999e-14+2.534938e-13i ; rel.err 4.18e-10
  cut lengths for k=3: (kk,l)->(len cutL,len cutR): (1,2)->(3,2), (1,3)->(2,3), (2,3)->(3,2)
  structural bound W^d*#pairs*L^2d*C2*C3*Bctl^3 (tau=0) = 1.3888e-05 <= N^8 = 3.741e+50: True ; with the ticket's N^(k+3)=N^6 form: k^2 C^2 2^k N^(k+3) with C=max(C2,C3,1)=1.000: 6.125e+39
G3 (i) margin log10[N^(2k+2) / (k^2 C^2 2^k N^(k+3))] = (k-1) log10 N - log10(k^2 2^k C^2); rows log10 N = 1,2,3,6 (C=10); crossover N* = (k^2 2^k C^2)^(1/(k-1)):
  k=2  exponents k+3=5 vs 2k+2=6 (slack k-1=1):  margins ['-2.20', '-1.20', '-0.20', '2.80']   N*(C=1,10,100) = ['16', '1.6e+03', '1.6e+05']
  k=3  exponents k+3=6 vs 2k+2=8 (slack k-1=2):  margins ['-1.86', '0.14', '2.14', '8.14']   N*(C=1,10,100) = ['8.49', '84.9', '849']
  k=6  exponents k+3=9 vs 2k+2=14 (slack k-1=5):  margins ['-0.36', '4.64', '9.64', '24.64']   N*(C=1,10,100) = ['4.7', '11.8', '29.7']
G5: terms of xi(u)-xi(th) <= sum_i c_i N^{e_i}, u-th <= N^-A, B_u^-1 <= N (A=6n_+20; sqrt(delta)=N^-A/2); e_i exact, sum<=1 crossover N0 (mp 40 digits)
  n_=2 A=32: dL*B^-n: 6*N^-3.0; dK*B^-n: 1*N^-24; |L_th|*n N d*B^-n: 2*N^-24; |K_th|*n N d*B^-n: 2*N^-26 | sum at N=10^1,10^2,10^3,10^6: 0.006, 6.0e-6, 6.0e-9, 6.0e-18 | N0=2
  n_=3 A=38: dL*B^-n: 9*N^-3.0; dK*B^-n: 1*N^-27; |L_th|*n N d*B^-n: 3*N^-27; |K_th|*n N d*B^-n: 3*N^-30 | sum at N=10^1,10^2,10^3,10^6: 0.009, 9.0e-6, 9.0e-9, 9.0e-18 | N0=3
  n_=6 A=56: dL*B^-n: 18*N^-3.0; dK*B^-n: 1*N^-36; |L_th|*n N d*B^-n: 6*N^-36; |K_th|*n N d*B^-n: 6*N^-42 | sum at N=10^1,10^2,10^3,10^6: 0.018, 1.8e-5, 1.8e-8, 1.8e-17 | N0=3
  hQ: kappa=0.1: c1=sqrt(kappa/2)/2=0.1118034, 1/c1=8.9442719 <= N needed (and (1-t)^-1 <= N)  => etaT^-1 <= N^2 for N >= 9.0
  hQ: kappa=0.01: c1=sqrt(kappa/2)/2=0.035355339, 1/c1=28.284271 <= N needed (and (1-t)^-1 <= N)  => etaT^-1 <= N^2 for N >= 29.0
  #V<=N^(2n_) needs N>=2 (2^n_ N^n_ <= N^(2n_)); L^2<=L^d<=N; W^d L^(2d)=N L^d<=N^2
limits along sz0: n | N_n=(W L)^3 | lam_n<=10 | (1-t)^-1=16/15<=N | N^(-1+eps/2)<=1-t | 1/c1(kappa/2=1/20)=8.94<=N | |E_n|<=2-kappa | L^2<=N
  n=0        N=2.09715e+6 lam=0.01562 True True True True True
  n=1        N=5.49756e+11 lam=0.0002441 True True True True True
  n=10       N=1.166e+25 lam=8.82e-9 True True True True True
  n=1000     N=2.13522e+60 lam=1.553e-20 True True True True True
  n=1000000  N=2.09719e+114 lam=1.562e-38 True True True True True
  N_n = 128^3 (n+1)^18 -> infinity (SizeTendsto); all rows monotone in n.
```
Hypotheses at the instance: `STFlow sz0 (1/10)(1/10)(1/6)(1/10) z0` is the merged `flow_z0`; `t ≤ lemT(z0 0)=0.99999 (≥ 1/16)`, `s<t`, `STCaseI`, `STConStInd`: merged `sz0_*`; `STKbound`, `STKward` from `stKbound_of_flow`, `stKward_of_flow`; `SizeTendsto` (`N_n=128³(n+1)^18`), `|E_n| ≤ 2−κ`, `0<lam_n≤gmax`, `(1−t)⁻¹=16/15 ≤ N`, `RangeCond(ε/2)`: limit rows above (external hypotheses of `stKloop_lip` / `hQ`). `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ X` stay hypotheses of the instance (other gates' pins), as in `inst_OeqNQPT''`.

### Verdicts
- **G2 (envelope, bad-set inclusion, `ζ♯` monotone/`≤ζ`/`≥1`): PASS** (0 violations in 3000 random step-control draws, `p∈{1,4}`, `n_∈{2,3,6}`, `u>t_n` included; paper-style argument above).
- **G3 (`𝒦^{(k)}` modulus, exponent `2k+2`): PASS** (true count `k+3`, slack `k−1 ≥ 1`; constants uniform over `KLPar κ gmax`; derivative on `Icc 0 t_n`; `k=2` consistent with `LemDecCalELip_STKloop_two_sub` (`N²√x` vs `N⁶x`, incomparable shapes, both hold: empirical Lipschitz `3.45e-5 ≤ N²`). Tree equation verified numerically at the instance (rel. err `4e-10`); cut lengths `(3,2),(2,3),(3,2)` at `k=3`, in `[2,k]`.
- **G5 (mesh `A=6n_+20`, `ξ` modulus, `hlow`, `#V`): PASS** (every row `≤ 1`, `N0 ≤ 3`; `hQ` needs `N ≥ 9`/`29`).
- **G6 (one-sided core): PASS** (floor net point: `0 ≤ netPt ≤ x`, `x−netPt ≤ 1/netSize`, `k ≤ netSize`, 0 violations in 20000 exact draws; `θ=s+netPt ≤ u ≤ t`, the `min (t n)` clamp inactive; the net domination and `N^τ−2N^{τ/2}−1 ≥ 0` absorption of `cont_core` are unchanged since `ζ♯(θ) ≤ ζ♯(u) ≤ 2ζ♯(u)`, `ε=1`).
- Targets 1–7 (`nqFlowSharp`, envelope lemmas, right side, one-sided core, `stKloop_lip`, `ξ` modulus, `stOeqNQ''_holds`): **PASS**; no hypothesis set is unsatisfiable, no pinned shape fails.
- §29/§45 O2: (1) `0 ≤ s`, `t<1`, `t ≤ lemT z` are those of `STIngR`; (2) case (ii) n/a; (3) no `L^d ≤ W^K` (`L² ≤ N` from `L^d ≤ N`, `d ≥ 3`); (4) all new conditions `∀ᶠ n`; (5) conclusion `Prec`, input `PrecPT`; (6) `SizeTendsto`, `|E|≤2−κ`, `0<lam≤gmax` premises of `stKloop_lip`; (7) scale `N=sz.size n`.
- Observation (not a failure): the ticket's step 4 says "`k+4 ≤ 2k+2`"; the count is `k+3` (`W^dL^{2d} ≤ N²`, `L² ≤ N`, `(2N)^k`). At `k=2` the exponent `k+4` would equal `2k+2` with no slack, so the proof must use `k+3` (`N^{k-1} ≥ k²2^kC²` eventually).

## (b) Script output — stage 1b (`prover-max`), branch `t/T2258`, commit `7b379e5` — written Tue Oct  6 05:49:07 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2258`, base `9db01b0`. Section (a) was read and not edited; no `(a′)` section is needed. Files changed (the two sole writable files): `RBM3D/Induction/NQEndFlowLift.lean` (new), `RBM3D/Test/Axioms.lean` (one registry line deleted). Logs and scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2258/`.

### b1. Build, hygiene, diff
```
$ date -u
Tue Oct  6 05:46:49 UTC 2026
$ lake build RBM3D.Induction.NQEndFlowLift 2>&1 | grep -E "NQEndFlowLift|Build completed" | cut -c1-170
ℹ [3854/3854] Replayed RBM3D.Induction.NQEndFlowLift
info: RBM3D/Induction/NQEndFlowLift.lean:1148:0: 'RBM.Ind.nqFlowSharp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlowLift.lean:1149:0: 'RBM.Gauss.Sizes.stKloop_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlowLift.lean:1150:0: 'RBM.Ind.stOeqNQ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlowLift.lean:1151:0: 'RBM.Ind.NQEndFlowLiftInst.inst_OeqNQ''' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3854 jobs).
$ grep -c -E "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/NQEndFlowLift.lean
0
$ wc -l RBM3D/Induction/NQEndFlowLift.lean
    1151 RBM3D/Induction/NQEndFlowLift.lean
$ git diff --stat main...t/T2258
 RBM3D/Induction/NQEndFlowLift.lean | 1151 ++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean             |    1 -
 2 files changed, 1151 insertions(+), 1 deletion(-)
$ git diff main...t/T2258 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]" | cut -c1-120
-   `RBM.Gauss.Sizes.STOeqNQ'', -- `lem:STOeq_NQ`, R2* (DECISIONS §80): per-time form proved by T2246 (`stOeqNQPT''_hold
$ grep -c 'warning: RBM3D/Induction/NQEndFlowLift' build2.log   # `lake build` output of the module (Mathlib linters on)
0
```
### b2. Target statements, extracted from the file by `sed -n` (public: `nqFlowSharp`, `stKloop_lip`, `stOeqNQ''_holds`, `inst_OeqNQ''`)
```
$ sed -n '68,69p;581,589p;939p;974,976p' RBM3D/Induction/NQEndFlowLift.lean
noncomputable def nqFlowSharp (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  max 1 (sInf (X m n '' Set.Icc u (t n)))
theorem stKloop_lip {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hsize : sz.SizeTendsto) (E t : ℕ → ℝ) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) (ht : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ‖STKloop sz n (E n) u σ a - STKloop sz n (E n) u' σ a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) * |u - u'| := by
  -- the constants of `ML:Kbound` (`τ = 1`) for the lengths `0 … k`
theorem stOeqNQ''_holds : ∀ d : ℕ, STOeqNQ'' d := by
theorem inst_OeqNQ'' : InstIngConcl (fun sz E s t => STNQConcl'' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STNQConcl'' sz E s t) (stOeqNQ''_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos
$ sed -n '868,874p' RBM3D/Induction/NQEndFlowLift.lean   # the private lift (binder = the owed per-time pin)
private theorem nqLift_lift (sz : Sizes d) (hd : 3 ≤ d) {E s t : ℕ → ℝ} {κ' gmax : ℝ} (hκ' : 0 < κ')
    (hg : 0 < gmax) (hE : ∀ n, |E n| ≤ 2 - κ') (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) (hPT : STNQConclPT'' sz E s t) :
    STNQConcl'' sz E s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
```
### b3. The vocabulary and the nine pinned statements against the check file (`docs/tickets/checks/T2258-check.lean`)
```
$ python3 pincheck.py   # parses §2–§3 of the check file and the new file, whitespace-normalised text comparison
nqFlowSharp def identical (verbatim): True
noncomputable def nqFlowSharp (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  max 1 (sInf (X m n '' Set.Icc u (t n)))
T2258_sharp_one_le       -> example : <statement> := @nqLift_sharp_one_le    text-identical (whitespace-normalised): True
T2258_sharp_le           -> example : <statement> := @nqLift_sharp_le        text-identical (whitespace-normalised): True
T2258_sharp_mono         -> example : <statement> := @nqLift_sharp_mono      text-identical (whitespace-normalised): True
T2258_sharp_prec         -> example : <statement> := @nqLift_sharp_prec      text-identical (whitespace-normalised): True
T2258_bootRHS_mono       -> example : <statement> := @nqLift_bootRHS_mono    text-identical (whitespace-normalised): True
T2258_netPt_floor        -> example : <statement> := @nqLift_netPt_floor     text-identical (whitespace-normalised): True
T2258_core_below         -> example : <statement> := @nqLift_core_below      text-identical (whitespace-normalised): True
T2258_stKloop_lip        -> example : <statement> := @stKloop_lip            text-identical (whitespace-normalised): True
T2258_stOeqNQ''_holds    -> example : <statement> := @stOeqNQ''_holds        text-identical (whitespace-normalised): True
$ lake env lean statement_script.lean   # the check file + `import RBM3D.Induction.NQEndFlowLift` + the three examples below (05:38:38 UTC)
  example : T2258_stKloop_lip := @RBM.Gauss.Sizes.stKloop_lip
  example : T2258_stOeqNQ''_holds := @RBM.Ind.stOeqNQ''_holds
  example : ∀ t X m n u, RBM.Ind.nqFlowSharp t X m n u = nqFlowSharp t X m n u := fun _ _ _ _ _ => rfl
exit=0; lines containing `error`: 0 (the 214 output lines are the `#check`s of the check file §1)
```
The seven private statements are pinned by in-file `example`s (`RBM3D/Induction/NQEndFlowLift.lean`, text above); `stKloop_lip` and `stOeqNQ''_holds` also by the statement script.
### b4. Compiled nonempty instances (namespace `RBM.Ind.NQEndFlowLiftInst`, section 7 of the file; all compile in the build of b1)
```
$ awk -F: '$1>=966' <(grep -n '^example\|^theorem inst_' RBM3D/Induction/NQEndFlowLift.lean) | cut -c1-110   # section 7
974:theorem inst_OeqNQ'' : InstIngConcl (fun sz E s t => STNQConcl'' sz E s t) sz0 z0 sInst tInst 1 :=
983:example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
1004:example : ∀ (m n : ℕ) (u : ℝ), nqFlowSharp tInst (fun _ _ _ => (1 : ℝ)) m n u = 1 := fun m n u =>
1008:example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + u) 0 0 0 = 2 ∧
1023:example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 0 = 2 ∧
1040:example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 (1 / 32) ≤ (2 : ℝ) + |(1 / 32 : ℝ)| :=
1043:example : nqFlowSharp tInst (fun _ _ u => (2 : ℝ) + |u|) 0 0 0 ≤
1048:example : Prec sz0 (U := STPair sInst tInst) (fun n q ω => (fun (_ : ℕ) (w : ℝ) (_ : sz0.SeqΩ) => w) n q.1.1 ω)
1058:example : ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ tInst n → 0 ≤ u' → u' ≤ tInst n →
1075:example : StochDomAt sz0.seqP sz0.size (U := fun n => TimeIcc sInst tInst n × Fin 2)
1102:example : ∃ k : Fin (netSize 1 4 + 1), netPt 1 1 4 k ≤ (1 / 2 : ℝ) ∧
1106:example : STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) 3 1 ≤
1113:example : ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ gmax : ℝ}, 0 < κ → 0 < gmax → sz.SizeTendsto →
1122:example : ∀ d : ℕ, STOeqNQ'' d := @stOeqNQ''_holds
1128:example : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ), 1 ≤ nqFlowSharp t X m n u :=
1131:example : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
1134:example : ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
1138:example : ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m : ℕ),
```
Map to the ticket: `inst_OeqNQ''` (974) = instance (1), with the conclusion applied at `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1` in `983` (`stKbound_of_flow`, `stKward_of_flow`; `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` stay hypotheses, other gates' pins, as `inst_OeqNQPT''`, `NQEndFlow.lean:984`); (2) = `1004`–`1048` (envelope at `t ≡ 1/16`: `1`, `2`, `1` at `u = 1 > t`; the lemma instances at `X = 2 + |u|`, since `∀ m n u, 1 ≤ X` excludes `2 + u`); (3) = `1058` (`stKloop_lip` at `sz0`, `E = STflowE z0`, `t = tInst`, `k = 3`); (4) = `1075` (`nqLift_core_below`: window `[0, 1/16]`, `V n = Fin 2`, `ξ = u`, `ζ ≡ 1`, `A = Cv = 1`, `Ξ = contGood sz0`, `ε ≡ 1`, per-time input by `precPT_of_le`); (5) = `1102`–`1138` (`nqLift_netPt_floor` at `A = 1`, `N = 4`, `x = 1/2`; `nqLift_bootRHS_mono` at numbers; the pinned statements).
### b5. Registry pre-check (`lake env lean <file>` with `import RBM3D` [+ `import RBM3D.Induction.NQEndFlowLift`] + `#assert_rbm_axioms`; all three exit 0)
```
== precheck_base.log (lake env lean <file>; import RBM3D; #assert_rbm_axioms)
axiom audit: 7576 theorems, 2547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
registry: 2 borrowed + 158 owed + 98 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet: ...
   STOeqNQ'' lines: 2  ->  RBM.Gauss.Sizes.STOeqNQ'': 1 [no certificate]
== precheck_before.log (lake env lean <file>; import RBM3D + import RBM3D.Induction.NQEndFlowLift; #assert_rbm_axioms)
axiom audit: 7579 theorems, 2548 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
registry: 2 borrowed + 158 owed + 98 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet: ...
   STOeqNQ'' lines: 2  ->  RBM.Gauss.Sizes.STOeqNQ'': 2 [no certificate]
== precheck_after.log (lake env lean <file>; import RBM3D + import RBM3D.Induction.NQEndFlowLift; #assert_rbm_axioms)
axiom audit: 7579 theorems, 2548 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
registry: 2 borrowed + 157 owed + 98 structural + 7 refuted + 12 superseded; 123 registered premise(s) carry nothing yet: ...
   STOeqNQ'' lines: 0  ->  
```
Before the registry edit the new module adds 3 theorems and 1 definition (`stKloop_lip`, `stOeqNQ''_holds`, `inst_OeqNQ''`; `nqFlowSharp`) and no premise; after deleting the line (b1, last line) `owed` is 158 → 157 and the scan still finds 153 premises, none unregistered. `STOeqNQ''` (registered; no theorem takes it as a hypothesis: it is in the base run's "carry nothing yet" list, `precheck_base.log:177`) is now concluded by `stOeqNQ''_holds`. `stKloop_lip` has structural/arithmetic binders only (`SizeTendsto`); every helper whose binder mentions `STNQConclPT''`/`STNQConcl''` is `private` (not scanned).
### b6. The hub's merge steps 4–5 simulated (05:45:41–05:46:28 UTC): `import RBM3D.Induction.NQEndFlowLift` inserted after the last `import` of `RBM3D.lean` (backup `cp`, restored afterwards), then the whole library
```
$ lake build > fullbuild.log; echo exit=$?
exit=0
$ grep -n 'axiom audit:\|^Build completed' fullbuild.log | cut -c1-140
3017:info: RBM3D.lean:301:0: axiom audit: 7579 theorems, 2548 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4061 jobs).
$ cp RBM3D.lean.bak RBM3D.lean; git status --short | wc -l
0
```
### b7. Name-clash grep of the new names (BSD `grep -rn -F --include='*.lean'`; `main` worktree and the T2258 worktree outside the new file)
```
main worktree: nqFlowSharp : 0 hits in RBM3D/ and RBM3D.lean
main worktree: stKloop_lip : 0 hits in RBM3D/ and RBM3D.lean
main worktree: stOeqNQ''_holds : 0 hits in RBM3D/ and RBM3D.lean
main worktree: NQEndFlowLift : 0 hits in RBM3D/ and RBM3D.lean
main worktree: nqLift_ : 0 hits in RBM3D/ and RBM3D.lean
main worktree: inst_OeqNQ'' : 0 hits in RBM3D/ and RBM3D.lean
T2258 worktree outside the new file: nqFlowSharp : 0 hits
T2258 worktree outside the new file: stKloop_lip : 0 hits
T2258 worktree outside the new file: stOeqNQ''_holds : 0 hits
T2258 worktree outside the new file: NQEndFlowLift : 0 hits
T2258 worktree outside the new file: inst_OeqNQ'' : 0 hits
```
### b8. Ports
No text of `../RBM1D` or `../RBM2D` was ported in this ticket (no `git -C ../RBM1D` or `../RBM2D` command was run). Copies are from merged RBM3D files (source file:line @ last commit of the file → new name); their own provenance is the one in the docstrings of the merged files (`ContinuityNet.lean`: RBM2D `Induction/Continuity.lean` at `c9a24cf`, RBM1D `Gauss/Step1Hyp.lean:404`, `Gauss/DominationHolder.lean:115` at `86573b9`).
```
ContinuityNet.lean:76  @5b6cbc1 cont_stochDomAt_of_subset -> nqLift_stochDomAt_of_subset (verbatim)
ContinuityNet.lean:106,110 @5b6cbc1 contTime, contTime_mem -> nqLift_time, nqLift_time_mem
ContinuityNet.lean:142-215 @5b6cbc1 cont_core -> nqLift_core_below (hclose one-sided; floor net point)
Gauss/Domination.lean:171  @1c2e756 exists_netPt_close (witness ⌊u·netSize/T⌋₊, T = 1) -> nqLift_netPt_floor
NQEndFlow.lean:804 @0f60da2 nqFlow_bootRHS_one_le -> nqLift_bootRHS_one_le; NQEndFlow.lean:206 nqFlow_prec_of_le_right -> nqLift_prec_of_le_right
KLFinal.lean:294 @471b643 KLFinal_flowLam -> nqLift_flowLam; KLFinal.lean:168 KLoopBound_KLK (list bridge) -> nqLift_loopOf_eq, nqLift_KLK_bound
```
### b9. Narrative
- Architecture (file sections): §1–§3 envelope `nqFlowSharp t X m n u = max 1 (sInf (X m n '' Icc u (t n)))`, `1 ≤ X♯ ≤ X`, monotone on `u ≤ t n`; the pair hypotheses carry over (`nqLift_sharp_prec`: `StochDomAt.of_subset`, bad-set inclusion at `τ' = τ`, the left side depends on `q.1.1` only); `STbootRHS` is monotone in both controls; `ζ♯(θ) ≤ ζ♯(u)`, `ζ♯ ≤ ζ`, `1 ≤ ζ♯` with the first summand at the fixed `B_s` (R2*), so no `B`-ratio step.
- §4 `nqLift_core_below` is the text of `cont_core` with the floor net point `θ = s_n + ⌊(u − s_n) netSize⌋/netSize ≤ u` (`min_eq_right`: the clamp of `contTime` is inactive) and `hclose` asked for `u' ≤ u` only; the net domination and the `N^τ − 2N^{τ/2} − 1 ≥ 0` absorption are unchanged.
- §5 `stKloop_lip` (public): `KLK_isKLoop` (derivative `treeEqRhs` on `[0,1)`) + `KLbound_holds` at `τ = 1` for `m = 1..k` (constants `C_m` from `KLPar κ gmax`, `Cm = Σ_{m ≤ k} C_m`) + `nqLift_treeEq_bound` (cut-loop lengths `i+n−l+1`, `l−i+1 ∈ [2,n]`, `(m₁−1)+(m₂−1) = n`, `‖S^{(B)}_{ab}‖ ≤ 1`, `≤ n²` pairs) + `Bctl ≤ 2N` + `W^d L^{2d} L² ≤ N³`: `‖treeEqRhs‖ ≤ k² Cm² 2^k N^{k+3}`; for `N ≥ max 1 (k² Cm² 2^k)` this is `≤ N^{k+4} ≤ N^{2k+2}` (`k ≥ 2`; equality of exponents at `k = 2`, as noted in (a)); mean value theorem on `Icc 0 (t n)`.
- §6 `nqLift_xi_close`: for `u' ≤ u ≤ t`, `u − u' ≤ N^{-(6n_+20)}`, `N ≥ 3n_+1`, on `contGood`: `ξ(u) ≤ ξ(u') + 1` from `‖Δ𝓛‖ ≤ 3n_N^{2n_+7}√δ` (`LemDecCalELip_Lloop_sub`), `‖Δ𝒦‖ ≤ N^{2n_+2}δ` (`stKloop_lip`), `B_{u'} ≤ B_u` (`STBctl_mono`), `N⁻¹ ≤ B_u` and `nqLift_arith`: `N^{n_}(3n_N^{2n_+7}√δ + N^{2n_+2}δ) ≤ (3n_+1) N^{-3} ≤ 1`. The `B`-ratio term of the two-sided estimate has the favourable sign and is dropped.
- Deviation from the ticket's suggested copies: `|E_n| < 2 − κ/2` is taken from `v3_premises_of_stFlow` and `hQ : (etaT E t)⁻¹ ≤ N²`, `N ≥ 3n_+1`, `|E| < 2` from the public `LemDecCalELip_env`, so no private copy of `KLFinal_flowE` or `nl2_eta_inv_le`; `stKloop_lip` and `LemDecCalELip_env` are applied at `κ/2`, `gmax = 𝔡⁻¹`; `nqLift_flowLam` is the only copy of the three.
- `nqLift_lift` (private) + `stOeqNQ''_holds`: the same `𝔠_d` as `stOeqNQPT''_holds d κ ε 𝔡 C_d` (obtained, not re-chosen); per-time pin at `(XL♯, XLK♯)` → `nqLift_core_below` (`P = seqP`, `size = sz.size`, `V n` = non-alternating `σ` × labels, `#V ≤ N^{2n_}` for `N ≥ 2`, `Ξ = contGood`, `ε ≡ 1`) → `Prec(ξ ≺ ζ♯)` → `Prec(ξ ≺ ζ)` by `ζ♯ ≤ ζ`.
- No hypothesis added, no weakening, no merged/pinned signature changed (`git diff --stat main...t/T2258` above: two files, one registry line deleted); no `set_option maxHeartbeats`; `sorry|admit|native_decide|axiom` count 0; axioms of every public declaration: the three standard ones; the module build has 0 warnings of its own. No obstruction occurred.

## (c) Verified Mathlib names used (all resolved: `#check` script `mathlib_names.lean`, 33 names, `lake env lean` exit 0, 0 errors; names verified absent: none needed)
- `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` — mean value theorem on a convex set, `HasDerivWithinAt` form (`MeanValue.lean:695`)
- `csInf_le` — `sInf s ≤ a` for `a ∈ s`, `s` bounded below
- `csInf_le_csInf` — `sInf` is antitone in the set (`BddBelow`, nonempty, subset)
- `exists_lt_of_csInf_lt` — nonempty `s`, `sInf s < b` gives `a ∈ s` with `a < b`
- `IsLeast.csInf_eq` — `sInf` of a set with a least element (instances)
- `Real.sInf_empty` — `sInf ∅ = 0` on `ℝ`
- `Set.Icc_eq_empty` — `¬ a ≤ b → Icc a b = ∅`
- `Set.Icc_subset_Icc_left` — `a₁ ≤ a₂ → Icc a₂ b ⊆ Icc a₁ b`
- `Set.image_mono` — image is monotone in the set
- `lt_div_iff₀` — `a < b / c ↔ a * c < b` for `0 < c`
- `div_le_div_of_nonneg_left` — `0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c`
- `div_le_div_of_nonneg_right` — `a ≤ b → 0 ≤ c → a / c ≤ b / c`
- `le_self_pow₀` — `1 ≤ a → n ≠ 0 → a ≤ a ^ n`
- `one_le_pow₀` — `1 ≤ a → 1 ≤ a ^ n`
- `pow_le_pow_left₀` — `0 ≤ a → a ≤ b → a ^ n ≤ b ^ n`
- `pow_le_pow_right₀` — `1 ≤ a → n ≤ m → a ^ n ≤ a ^ m`
- `inv_anti₀` — `0 < a → a ≤ b → b⁻¹ ≤ a⁻¹`
- `inv_le_one_of_one_le₀` — `1 ≤ a → a⁻¹ ≤ 1`
- `Real.rpow_le_rpow` — monotone in the base for exponent `≥ 0`
- `Real.rpow_le_rpow_of_exponent_le` — `1 ≤ x → y ≤ z → x ^ y ≤ x ^ z`
- `Real.rpow_neg` — `0 ≤ x → x ^ (-y) = (x ^ y)⁻¹`
- `Real.rpow_natCast` — `x ^ (n : ℝ) = x ^ n`
- `Real.rpow_neg_one` — `x ^ (-1 : ℝ) = x⁻¹`
- `Nat.floor_le` — `0 ≤ a → ↑⌊a⌋₊ ≤ a`
- `Nat.lt_floor_add_one` — `a < ⌊a⌋₊ + 1`
- `Nat.floor_le_of_le` — `a ≤ n → ⌊a⌋₊ ≤ n`
- `Fintype.card_subtype_le` — `card {x // p x} ≤ card α`
- `List.ofFn_get` — `List.ofFn l.get = l`
- `List.ext_getElem` — extensionality of lists by length and entries
- `norm_sum_le` — `‖∑ f‖ ≤ ∑ ‖f‖`
- `Finset.single_le_sum` — a nonneg-term sum dominates a term
- `Nat.card_Icc` — `#Icc a b = b + 1 - a`
- `Nat.card_Ioc` — `#Ioc a b = b - a`

## (d) Open issues and paper-delta candidates
- **`T2258a`** (paper-delta candidate): the uniform-in-`u` form `STNQConcl''` of `(am;asoiuw)` is obtained from the per-time one (`STNQConclPT''`) by a one-sided net on the monotone envelope `X♯` of the controls (`nqFlowSharp`, `stOeqNQ''_holds`); the paper's `N^{-C}`-net remark is commented out (`paper/tex/3_5_Loop_Hierarchy.tex:1182`; the same remark at `:1764`, where a continuity estimate is also invoked). The Lean net is one-sided (floor point) because `ζ♯` is only known to be non-decreasing.
- **`T2258b`** (paper-delta candidate): the Lipschitz time modulus `‖𝒦^{(k)}_u − 𝒦^{(k)}_{u'}‖ ≤ N^{2k+2}|u − u'|` on `[0, t_n]` for every `k ≥ 2` (`stKloop_lip`), deterministic, from the tree equations `(pro_dyncalK)` and `ML:Kbound`; the paper does not state it.
- Hub: add `import RBM3D.Induction.NQEndFlowLift` after the last `import` of `RBM3D.lean` (simulated in b6: full `lake build` exit 0). `main` was at `3a3ed6a` (T2254 merged: `git diff --stat 9db01b0 main` shows `Test/Axioms.lean | 3 -`) when I checked, between 05:38:38 and 05:45:35 UTC; my base is `9db01b0`; my registry change is the single deleted line of `STOeqNQ''` (hub merges registry lines in order, ticket §3).
- Consumers (S3-18b, S3-24b = T2259, S3-26, the Step 3/4 regime pins) state against the merged `STOeqNQ''` (`NQEndFlow.lean:124`, unchanged) and can now cite `RBM.Ind.stOeqNQ''_holds`; `RBM.Gauss.Sizes.stKloop_lip` is public for S5-13.
- Size: the file has 1151 lines against the ticket's 650/850/1100 estimate (stage-1a stop threshold 1500 not reached).
