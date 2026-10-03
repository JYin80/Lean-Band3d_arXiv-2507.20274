Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 05:59:40 UTC 2026

Notation: `ρ = W^ε`, `P = (1−s)/(1−t)`, `r = (g²+|1−s|)/(g²+|1−t|)`, `q = ℓ_t²/ℓ_s²`, `R = ρ ℓ_s`, `ψ_i(c) = |u_i(a_i,c)|` with `u_i = uKer (cycProd (EKsgn m σ) i) s t`. Sources: pins of `RBM3D/Evolution/Pins.lean`; `ekXiBall_holds`, `ekSameRow_holds` (`XiPins.lean:346, 357`); `norm_uKer_le`, `sum_norm_row_le`, `uKer_eq_one_add_XiKer` (merged `Kernel/*`); probe `c961e62:RBM3D/Probe/T2016Pins.lean` (`ek_ratio_le` :477, `ek_arith_claim`, `ekSumDecay1_two` :572–760); RBM2D `RBM2D/Evolution/KernelExpand.lean` at `c9a24cf` (`sum_prod_anchor_le` :93, `KernelExpand_core_bound` :370, `ugenGenExplicit` :472, `ugenCase1Explicit` :507; the ticket's path prefix `Path/` is `Evolution/` at that commit, the line numbers are right).

### (i) Exponent table (general `n ≥ 2`, `d ≥ 3`, constants uniform in `g ∈ (0, Λ]`)

| # | quantity | value | constraint it must satisfy / where it enters | slack |
|---|---|---|---|---|
| 1 | anchored decomposition | `Σ_b ∏ψ_i(b_i)|A_b| ≤ ‖A‖ Σ_{b∈Win} ∏ψ_i + W^{-D} Σ_b ∏ψ_i`, `Win = {∀i,j |b_i−b_j|<R}` | triangle inequality first; `Win ⊆ {∀i |b_i−b_k|<R}` (anchor `k`), complement ⊆ `(deccA0)` far set (`∃ i j |b_i−b_j| ≥ R`) | none needed |
| 2 | window part, anchor `k` | `Σ_{b_k} ψ_k(b_k) ∏_{i≠k} Σ_{b_i: |b_i−b_k|<R} ψ_i(b_i) ≤ Rw_k · S^{n−1}`, `Rw_k` = row-sum bound of the anchor index (`P` or `C_s`), `S = 1 + C_X ρ² r` | RBM2D `sum_prod_anchor_le` (:93, generic in the lattice; port `Z2 L ↦ Zd d L`); window sums from `ekXiBall_holds` with `Λ'=ρ`, `R = Λ'ℓ_s`, `1 ≤ R` (needs `ρ ≥ 1`, `ℓ_s ≥ 1`), `g²/L² ≤ 1−t` | `Λ'=ρ=5 ≥ 1`; `R=5 ≤ 5` (equality) |
| 3 | `C_X` (`ekXiBall_holds`), `d=3` | ball sum `≍ R²`: `S_win ≤ 1 + C_X ρ² r` (`u = 1 + Ξ`) | no `(1+log L)^{n−1}` (that was `d=2`) | empirical `C_X ≥ 0.7729` (script, lower estimate only) |
| 4 | tail part | `Σ_b ∏ψ_i ≤ ∏_i (row sum_i) ≤ P^n` (`norm_uKer_le` + `sum_norm_row_le`) and `P ≤ W` | `W⁻¹ ≤ (1−t)/(1−s)` enters here and only here | instance `1/25` vs `1/5` (5×) |
| 5 | `P ≤ 2 q r` (`ek_ratio_le`) | `(1−s)/(g²+1−s) ≤ 1/ℓ_s²` and `(g²+1−t)/(1−t) ≤ 2 ℓ_t²` | second needs `ℓ_t = g/√(1−t) ≤ L` when `g² ≥ 1−t`, i.e. `t ≤ 1−g²/L²`; first: `ℓ_s ≤ g/√(1−s)` when `g² ≥ 1−s`, else `ℓ_s = 1` | `2qr/P` = 1.85–2.94 in the table below |
| 6 | factors `r`, `q` in `(sum_res_1)` | `P·S^{n−1} ≤ 2qr · ((1+C_X)ρ² r)^{n−1}`: `r^n` (1 from `P`, `n−1` from windows), `q^1` (from `P` only), `ρ^{2(n−1)}` | `S ≤ (1+C_X)ρ² r` needs `ρ² r ≥ 1` (`ρ ≥ 4`, `r ≥ 1`) | `r ≥ 1` since `s ≤ t` |
| 7 | factors in `(sum_res_2_NAL)` | anchor `k` with `σ_k = σ_{k+1}`: `μ_k = m(σ_k)²`, row sum `≤ C_s` (`ekSameRow_holds`, `κ ≤ Im m`) instead of `P`: `C_s·S^{n−1}`: `r^{n−1}`, `q^0`, no `P` | window sums of the other `n−1` indices (any `μ`) as row 2 | empirical `C_s ≥ 1.1229` (`m=i`) |
| 8 | `4 ≤ W^ε` | absorbs constants: `K ≤ 4^m ≤ ρ^m`; also `W ≥ W^ε ≥ 4` (`ε<1`, `W>1`) so `C_s ≤ 4^{m''} ≤ W^{m''}` in the NAL tail | without it `W^{Cε}` has no lower bound (T2016b) | instance `W^ε = 5` vs 4 |
| 9 | `C_res1(n)` (pin 1) | `m'_n = min{m : 4^m > 2(1+C_X)^{n−1}}`, `C = m'_n + 2n`; first term `ρ^{m'_n+2n−2} ≤ W^{Cε}`, tail `W^{-D}P^n ≤ W^{-D+n} ≤ W^{-D+C}` | `C ≥ m'_n+2n−2` and `C ≥ n` | slack 2 and `m'_n+n` |
| 10 | `C_NAL(n)` (pin 2) | `m''_n = min{m : 4^m > C_s(1+C_X)^{n−1}}`, `C = m''_n + 2n−2`; tail `C_s W^{-D} P^{n−1} ≤ W^{-D+m''_n+n−1}` | `C ≥ m''_n+2n−2` and `C ≥ m''_n+n−1` | slack 0 and `n−1` |
| 11 | `n`-dependence of `C` | `m'_n = ⌊log_4(2(1+C_X)^{n−1})⌋+1`: `C_n = O(n)`, linear with slope `2 + log_4(1+C_X)`; depends on `(d, n, Λ)` only, not on `ε, D, L, g, s, t, m, σ, A` | — | empirical `n=2,3`: `C_res1 = 5, 8`; `C_NAL = 3, 5` (below) |
| 12 | `ε, D` | `0<ε<1` (`W>1`⇒`ρ<W`), `D>1` not used by the proof (only `W^{-D}` factored out) | — | instance `ε=1/2`, `D=2` |
| 13 | `g ∈ (0,Λ]` | all constants from `Prop5Decay` (uniform in `g`) via `ekXiBall_holds`, `ekSameRow_holds` | no `L^τ`, no `g`-dependence | tested `g ∈ {0.1, 0.5}`, `Λ=1` |
| 14 | `t ≤ 1−g²/L²` | enters via `ekXiBall_holds` (`g²/L² ≤ 1−t`) and row 5 | — | instance `0.9` vs `0.99` |

Hypothesis check at the compiled-instance data and the endpoint finding (script `pf_all.py`, first block of the output): at `W = 25` the endpoint `t = 1−g²/L²` of the ticket's numeric list violates `W⁻¹ ≤ (1−t)/(1−s)` for all four `(L,g)`; the script therefore uses `W = max(25, P)` and `ε = ln 5 / ln W` (so `ρ = 5` everywhere; `D = 2`). Not a pin defect: the pin has that hypothesis.

### (ii) Concrete nondegenerate instance (and numeric check, exact `Θ`)

Instance (all hypotheses of both pins, `Λ = 1`, `κ = 1/2`): `d=3`, `L=5`, `g=1/2`, `W=25`, `ε=1/2` (`W^ε=5 ≥ 4`), `D=2`, `s=1/2`, `t=9/10` (`≤ 0.99`; `W⁻¹ = 0.04 ≤ 0.2`), `m=i` (`‖m‖=1`, `Im m = 1 ≥ κ`), `σ ∈ {(+,−), (+,−,+)}` for `(sum_res_1)`, `σ = (+,+,−)` (`σ_0=σ_1`) for NAL, `A = δ_0`: `ℓ_s = 1`, far premise `∃ i j |a_i−a_j| ≥ 5` forces `a ≠ 0`, where `A_a = 0 ≤ W^{-D}`; `‖A‖ = 1`. Prop5Decay/Prop5Short are discharged by the proved `prop5Decay_holds` (`Prop5Hold.lean:784`), `prop5Short_holds` (`Prop5Short.lean:400`): no external hypothesis remains; the concrete check of what they feed (window sums of `Ξ`, same-sign row sums, at `g = 0.1, 0.5`, `d = 3`) is the script's pass 1.
Script: exact `Θ` by `d=3` Fourier sum (`S^{(B)}` eigenvalue `(1+2g²Σcos)/(1+6g²)`), `u = (1−sμS)(1−tμS)⁻¹`, `μ = m(σ_i)m(σ_{i+1}) = ±1` for `m=i`; pass 1 measures `C_X`, `C_s` (empirical lower estimates), pass 2 computes `sup_a|UN A|` over all `σ` up to rotation and three `A` (`δ_0`; random; adversarial sign-aligned at `a=0`, all obeying `(deccA0)` with the stated `W, ε=ln5/lnW, D=2`, asserted) and compares with the chain `‖A‖ Rw_k S^{n−1}+W^{-D}·(tail)` and with both right-hand sides at the constants of rows 9–10 (`C_pf`); `C_needed` = least `C` with `LHS ≤ 5^C q r^n ‖A‖ + W^{C−2}` (res_1) resp. `5^C r^{n−1}‖A‖ + W^{C−2}` (NAL).

```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad && python3 pf_all.py
ticket instance L=5 g=1/2 W=25 eps=1/2 D=2 s=1/2 t=9/10 m=i kappa=1/2 Lam=1: {'L_ge3': True, 'g_pos_le_Lam': True, 'W_gt1': True, 'eps01': True, 'D_gt1': True, 'W_eps_ge4': True, 's_le_t': True, 't_le_1_g2_L2': True, 'Winv_le': True, 'kappa_le_Im_m': True, 'Lam_pos': True} | 1-g^2/L^2 = 0.99 W^-1 = 0.04 (1-t)/(1-s) = 0.19999999999999996 W^eps = 5.0
  endpoint t=1-g^2/L^2 at L=5 g=0.1: (1-t)/(1-s)=0.00080 vs W^-1=0.04 at W=25: hypothesis W^-1<=(1-t)/(1-s) FAILS; minimal W=(1-s)/(1-t)=1250.0
  endpoint t=1-g^2/L^2 at L=5 g=0.5: (1-t)/(1-s)=0.02000 vs W^-1=0.04 at W=25: hypothesis W^-1<=(1-t)/(1-s) FAILS; minimal W=(1-s)/(1-t)=50.0
  endpoint t=1-g^2/L^2 at L=7 g=0.1: (1-t)/(1-s)=0.00041 vs W^-1=0.04 at W=25: hypothesis W^-1<=(1-t)/(1-s) FAILS; minimal W=(1-s)/(1-t)=2450.0
  endpoint t=1-g^2/L^2 at L=7 g=0.5: (1-t)/(1-s)=0.01020 vs W^-1=0.04 at W=25: hypothesis W^-1<=(1-t)/(1-s) FAILS; minimal W=(1-s)/(1-t)=98.0
max|direct (1-s mu S)(1-t mu S)^-1 - FFT kernel| at L=5 g=.5 t=.9 mu=-1: 2.4424906541753444e-15
PASS 1 (rho=W^eps=5, R=5 l_s, W=max(25,P)): L g t | P  2qr  W  eps | mu=+1: Swin,(Swin-1)/(rho^2 r) | mu=-1 rowsum
L=5 g=0.1 t=0.9    | P=   5.00 2qr=    9.27 W=    25 eps=0.500 | Swin=   5.00 (Swin-1)/(rho^2 r)=0.0345 | rowsum=0.8027
L=5 g=0.1 t=1-g2/L2| P=1250.00 2qr= 2451.92 W=  1250 eps=0.226 | Swin= 948.45 (Swin-1)/(rho^2 r)=0.7728 | rowsum=0.7651
L=5 g=0.5 t=0.9    | P=   5.00 2qr=   10.71 W=    25 eps=0.500 | Swin=   4.68 (Swin-1)/(rho^2 r)=0.0687 | rowsum=1.0932
L=5 g=0.5 t=1-g2/L2| P=  50.00 2qr=  144.23 W=    50 eps=0.411 | Swin=  38.97 (Swin-1)/(rho^2 r)=0.5265 | rowsum=1.1157
L=7 g=0.1 t=0.9    | P=   5.00 2qr=    9.27 W=    25 eps=0.500 | Swin=   5.00 (Swin-1)/(rho^2 r)=0.0345 | rowsum=0.8027
L=7 g=0.1 t=1-g2/L2| P=2450.00 2qr= 4898.04 W=  2450 eps=0.206 | Swin= 940.74 (Swin-1)/(rho^2 r)=0.7521 | rowsum=0.7651
L=7 g=0.5 t=0.9    | P=   5.00 2qr=   10.71 W=    25 eps=0.500 | Swin=   4.36 (Swin-1)/(rho^2 r)=0.0627 | rowsum=1.0972
L=7 g=0.5 t=1-g2/L2| P=  98.00 2qr=  288.12 W=    98 eps=0.351 | Swin=  41.07 (Swin-1)/(rho^2 r)=0.5452 | rowsum=1.1229
Cb_emp=0.7729 (max (Swin-1)/(rho^2 r)), Cs_emp=1.1229 (max same-sign row sum)
n=2: m'=least with 4^m'>2(1+Cb)^(n-1)=3.546 -> C_res1=m'+2n=5;  m''=least with 4^m''>Cs(1+Cb)^(n-1)=1.991 -> C_NAL=m''+2n-2=3
n=3: m'=least with 4^m'>2(1+Cb)^(n-1)=6.286 -> C_res1=m'+2n=8;  m''=least with 4^m''>Cs(1+Cb)^(n-1)=3.529 -> C_NAL=m''+2n-2=5
PASS 2: sup_a|UN A| (exact Theta), worst over sigma (all up to rotation) x A in {delta_0, random, adversarial at a=0}; A obeys EKFastDecay (asserted)
L=5 g=0.1 t=0.9     n=2 W=    25 far=4000/15625 | res_1: LHS/RHS<=3.0e-04, C_needed<=0.09 (C_pf=5) | NAL: LHS/RHS<=1.1e-03, C_needed<=-1.23 (C_pf=3) | chain ok=True
L=5 g=0.1 t=0.9     n=3 W=    25 far=1122000/1953125 | res_1: LHS/RHS<=7.1e-08, C_needed<=-1.00 (C_pf=8) | NAL: LHS/RHS<=2.4e-04, C_needed<=-0.04 (C_pf=5) | chain ok=True
L=5 g=0.1 t=1-g2/L2 n=2 W=  1250 far=4000/15625 | res_1: LHS/RHS<=5.4e-04, C_needed<=1.84 (C_pf=5) | NAL: LHS/RHS<=7.9e-05, C_needed<=-2.75 (C_pf=3) | chain ok=True
L=5 g=0.1 t=1-g2/L2 n=3 W=  1250 far=1122000/1953125 | res_1: LHS/RHS<=1.4e-13, C_needed<=-1.06 (C_pf=8) | NAL: LHS/RHS<=2.7e-04, C_needed<=3.34 (C_pf=5) | chain ok=True
L=5 g=0.5 t=0.9     n=2 W=    25 far=4000/15625 | res_1: LHS/RHS<=4.2e-04, C_needed<=0.40 (C_pf=5) | NAL: LHS/RHS<=4.1e-03, C_needed<=-0.36 (C_pf=3) | chain ok=True
L=5 g=0.5 t=0.9     n=3 W=    25 far=1122000/1953125 | res_1: LHS/RHS<=8.7e-08, C_needed<=-0.07 (C_pf=8) | NAL: LHS/RHS<=7.4e-04, C_needed<=0.97 (C_pf=5) | chain ok=True
L=5 g=0.5 t=1-g2/L2 n=2 W=    50 far=4000/15625 | res_1: LHS/RHS<=2.4e-03, C_needed<=1.36 (C_pf=5) | NAL: LHS/RHS<=3.0e-03, C_needed<=-0.52 (C_pf=3) | chain ok=True
L=5 g=0.5 t=1-g2/L2 n=3 W=    50 far=1122000/1953125 | res_1: LHS/RHS<=8.5e-08, C_needed<=0.50 (C_pf=8) | NAL: LHS/RHS<=8.9e-03, C_needed<=3.12 (C_pf=5) | chain ok=True
L=7 g=0.1 t=0.9     n=2 W=    25 far=75460/117649 | res_1: LHS/RHS<=3.0e-04, C_needed<=0.09 (C_pf=5) | NAL: LHS/RHS<=1.1e-03, C_needed<=-1.23 (C_pf=3) | chain ok=True
L=7 g=0.1 t=0.9     n=3 W=    25 far=37591428/40353607 | res_1: LHS/RHS<=7.1e-08, C_needed<=-1.00 (C_pf=8) | NAL: LHS/RHS<=2.4e-04, C_needed<=-0.04 (C_pf=5) | chain ok=True
L=7 g=0.1 t=1-g2/L2 n=2 W=  2450 far=75460/117649 | res_1: LHS/RHS<=1.4e-04, C_needed<=1.78 (C_pf=5) | NAL: LHS/RHS<=6.7e-05, C_needed<=-2.76 (C_pf=3) | chain ok=True
L=7 g=0.1 t=1-g2/L2 n=3 W=  2450 far=37591428/40353607 | res_1: LHS/RHS<=1.7e-15, C_needed<=-1.73 (C_pf=8) | NAL: LHS/RHS<=2.6e-05, C_needed<=3.11 (C_pf=5) | chain ok=True
L=7 g=0.5 t=0.9     n=2 W=    25 far=75460/117649 | res_1: LHS/RHS<=3.5e-04, C_needed<=0.29 (C_pf=5) | NAL: LHS/RHS<=4.1e-03, C_needed<=-0.36 (C_pf=3) | chain ok=True
L=7 g=0.5 t=0.9     n=3 W=    25 far=37591428/40353607 | res_1: LHS/RHS<=7.2e-08, C_needed<=-0.19 (C_pf=8) | NAL: LHS/RHS<=6.1e-04, C_needed<=0.86 (C_pf=5) | chain ok=True
L=7 g=0.5 t=1-g2/L2 n=2 W=    98 far=75460/117649 | res_1: LHS/RHS<=1.5e-03, C_needed<=1.31 (C_pf=5) | NAL: LHS/RHS<=2.7e-03, C_needed<=-0.53 (C_pf=3) | chain ok=True
L=7 g=0.5 t=1-g2/L2 n=3 W=    98 far=37591428/40353607 | res_1: LHS/RHS<=1.3e-09, C_needed<=-0.07 (C_pf=8) | NAL: LHS/RHS<=1.1e-03, C_needed<=2.97 (C_pf=5) | chain ok=True
TICKET INSTANCE (L=5 g=1/2 s=1/2 t=9/10 W=25 eps=1/2 D=2 m=i, A=delta_0), exact Theta:
  n=2 sigma=+-: ||UN A||=1.90750; q=2.500 r=2.1429; RHS(sum_res_1,C=5)=51498.7; RHS(NAL,C=3)=292.9; Ndecay bound P^n=25.0
  n=3 sigma=+-+: ||UN A||=1.70065; q=2.500 r=2.1429; RHS(sum_res_1,C=8)=253749658.3; RHS(NAL,C=5)=29974.5; Ndecay bound P^n=125.0
  n=3 sigma=++-: ||UN A||=1.70065; q=2.500 r=2.1429; RHS(sum_res_1,C=8)=253749658.3; RHS(NAL,C=5)=29974.5; Ndecay bound P^n=125.0
```

### Verdicts

- `ekSumDecay1_holds` (`EKSumDecay1 d n Λ`, all `n ≥ 2`): **PASS** — the hypotheses are satisfiable at the instance; rows 1–6, 8–9 close with explicit `C_res1(n)`; numeric chain and both bounds hold in all 16 cases (`LHS/RHS ≤ 2.4e-3`, `C_needed ≤ 1.84 < C_pf`).
- `ekSumDecayNAL_holds` (`EKSumDecayNAL d n Λ κ`, all `n ≥ 2`): **PASS** — rows 7, 10 close with `C_NAL(n)`; one-index factor from `ekSameRow_holds` (EK-2, proved); numeric: `LHS/RHS ≤ 8.9e-3`, `C_needed ≤ 3.34 < C_pf = 5` (n=3).
- No pin change needed, no new paper-delta candidate (`T2016a/b/f` apply, DECISIONS §18). Caution for stage 1b: the empirical `C_X`, `C_s`, `C_pf` are numeric stand-ins; Lean takes `C_X` from `ekXiBall_holds` and `C_s` from `ekSameRow_holds`, and defines `C = m + 2n` resp. `m'' + 2n − 2` from them (rows 9–10).

## (b) Script output (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2034`, branch `t/T2034`, commit `31797d9`; last check run Sat Oct  3 06:14:06 UTC 2026)

```
$ lake build RBM3D.Evolution.SumDecay 2>&1 | grep -c 'Evolution/SumDecay.lean'      # warning lines naming the file
0
$ lake build RBM3D.Evolution.SumDecay 2>&1 | tail -1
Build completed successfully (3418 jobs).
$ lake build 2>&1 | tail -1          # full library, root #assert_rbm_axioms (root does not import SumDecay yet: hub adds it at merge)
Build completed successfully (3731 jobs).
$ git --no-optional-locks diff --stat main...t/T2034
 RBM3D/Evolution/SumDecay.lean | 631 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   3 +-
 2 files changed, 633 insertions(+), 1 deletion(-)
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Evolution/SumDecay.lean
0
```

Axioms (`lake env lean axioms_T2034.lean`, `import RBM3D.Evolution.SumDecay`, exit 0):
```
'RBM.ek_ellT_sq_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_anchor_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_prod_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_core_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_arith_res1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_arith_nal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_UN_anchor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekSumDecay1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekSumDecayNAL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Target statements (extracted by `grep -n "^theorem ekSumDecay..."`) and exact-type check against the pins of `RBM3D/Evolution/Pins.lean` (unchanged: `git diff --stat main...t/T2034 -- RBM3D/Evolution/Pins.lean | wc -l` = 0):
```
SumDecay.lean:325: theorem ekSumDecay1_holds (d n : ℕ) (Λ : ℝ) : EKSumDecay1 d n Λ := by
SumDecay.lean:420: theorem ekSumDecayNAL_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNAL d n Λ κ := by
$ lake env lean types_T2034.lean     # `#check` + example : ∀ d n Λ, EKSumDecay1 d n Λ := ekSumDecay1_holds (and NAL); exit 0
ekSumDecay1_holds : ∀ (d n : ℕ) (Λ : ℝ), EKSumDecay1 d n Λ
ekSumDecayNAL_holds : ∀ (d n : ℕ) (Λ κ : ℝ), EKSumDecayNAL d n Λ κ
```
No unproved `Prop` is a hypothesis of either theorem: `Prop5Decay` / `Prop5Short` are the antecedents inside the pins (`EKSumDecay1 := Prop5Decay d Λ → …`, Pins.lean:76, :92); the instances below discharge them by `prop5Decay_holds`, `prop5Short_holds`.

Compiled instances (`SumDecay.lean:574-627`; `example`s; `d=3, L=5, g=1/2, Λ=1, κ=1/2, W=25, ε=1/2, D=2, s=1/2, t=9/10, m=I`, `A = ekSDdelta0 n = δ_0`; the whole file builds, so each elaborates):
```
574: example (n : ℕ) : ‖ekSDdelta0 n‖ = 1                    -- A is nonzero
583: example (n : ℕ) (hn : 2 ≤ n) : ∃ a : Fin n → Zd 3 5, ∃ i j, (25 : ℝ) ^ ((1 : ℝ) / 2) * ellT 5 (1 / 2 : ℝ) (1 / 2) ≤ (zdistD 3 5 (a i - a j) : ℝ)   -- far premise of (deccA0) non-vacuous (distance 5 = W^ε ℓ_s)
592: example : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) (ekSDdelta0 2)‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) * (ellT 5 (1 / 2 : ℝ) (9 / 10) ^ 2 / ellT 5 (1 / 2 : ℝ) (1 / 2) ^ 2)
          * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2
          * ‖ekSDdelta0 2‖ + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := ekSumDecay1_holds 3 2 1 (prop5Decay_holds 3 1) le_rfl le_rfl one_pos
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ekSD_sqrt25]; norm_num)
    (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
    Complex.norm_I ![true, false] (ekSDdelta0 2) (ekSD_fastDecay 2)⟩
604: example : ∃ C : ℝ, 0 < C ∧ ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false, true]) (1 / 2) (9 / 10) (ekSDdelta0 3)‖ ≤ … ^ 3 * ‖ekSDdelta0 3‖ + (25 : ℝ) ^ (-2 + C)   -- ekSumDecay1_holds 3 3 1 …, same data
616: example : ∃ C : ℝ, 0 < C ∧ ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, true, false]) (1 / 2) (9 / 10) (ekSDdelta0 3)‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ (3 - 1) * ‖ekSDdelta0 3‖ + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := ekSumDecayNAL_holds 3 3 1 (1 / 2) (prop5Decay_holds 3 1)
    (prop5Short_holds 3 1 (1 / 2)) le_rfl (by norm_num) one_pos (by norm_num)
  exact ⟨C, hC, H 5 … 25 (1 / 2) 2 … Complex.I Complex.norm_I (by norm_num [Complex.I_im]) ![true, true, false] ⟨0, by decide⟩ (ekSDdelta0 3) (ekSD_fastDecay 3)⟩
```
(Lines 604 and 616 are shortened above with `…`; the file has the full text, the full text of 592 is the pattern.) Hypotheses discharged at the data: `3 ≤ L`, `0<g≤Λ`, `1<W`, `0<ε<1`, `1<D`, `4 ≤ W^ε` (`W^ε = 5`, `ekSD_sqrt25`), `0≤s≤t`, `t ≤ 1−g²/L²`, `W⁻¹ ≤ (1−t)/(1−s)`, `‖m‖=1`, `κ ≤ Im m`, `σ_0 = σ_1` (NAL), `EKFastDecay` (`ekSD_fastDecay n`, all `n`).

Name-clash grep (`names_T2034.sh`: each new public name against `RBM3D/**.lean` of the worktree, of `main`, and of every other `t/T*` branch head except `Probe/`):
```
new public names: ek_ellT_sq_ge ek_ratio_le ek_anchor_sum_le ek_prod_sum_le ek_core_bound ek_arith_res1 ek_arith_nal ek_UN_anchor_bound ekSumDecay1_holds ekSumDecayNAL_holds
ek_ellT_sq_ge: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ek_ratio_le: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ek_anchor_sum_le: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ek_prod_sum_le: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ek_core_bound: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ek_arith_res1: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ek_arith_nal: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ek_UN_anchor_bound: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ekSumDecay1_holds: worktree-other-files=0 main=0 other-branches(non-Probe)=0
ekSumDecayNAL_holds: worktree-other-files=0 main=0 other-branches(non-Probe)=0
```
The helpers `ekSDdelta0`, `ekSD_sqrt25`, `ekSD_fastDecay`, `ekSD_ellT_s`, `ekSD_zdistD_far` are `private`.

Registry pre-check (DECISIONS §20; scratch file outside the repository `precheck_T2034.lean` = `import RBM3D` / `import RBM3D.Evolution.SumDecay` / `#assert_rbm_axioms`). `ek_UN_anchor_bound` takes `EKFastDecay` as a hypothesis and no theorem proves it, so without a registry line the scan fails; `RBM.EKFastDecay` is therefore appended to `structuralProps` of `RBM3D/Test/Axioms.lean` (a data condition on `A`, class named in Amend 1):
```
$ [Axioms.lean as in 890a89f (branch base), no registry line]  lake build; lake env lean precheck_T2034.lean ; echo exit=$?
precheck_T2034.lean:4:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.EKFastDecay]
exit=1
$ [Axioms.lean with the line `RBM.EKFastDecay]`]  lake build (3731 jobs, success); lake env lean precheck_T2034.lean > out; echo "precheck exit=$?"
precheck exit=0
axiom audit: 1120 theorems, 415 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 13 (borrowed 2, owed 0, structural 11).
$ git --no-optional-locks diff main...t/T2034 -- RBM3D/Test/Axioms.lean   # the only change, one list element appended
-   `RBM.Green.Stable]         -- stability of `1 − ξS` with constant `K`; band profile S1-24
+   `RBM.Green.Stable,         -- stability of `1 − ξS` with constant `K`; band profile S1-24
+   `RBM.EKFastDecay]          -- `(deccA0)`: decay of the tensor `A` beyond the window `W^ε ℓ_s`, a data condition on `A` (EK-3, T2034)
```
Ports: nothing copied from RBM1D/RBM2D. `ek_anchor_sum_le` is the windowed analogue of RBM2D `RBM2D/Evolution/KernelExpand.lean:93 sum_prod_anchor_le` (read at `c9a24cf`; that lemma sums `∏ g i (b j) (b i)` with a diagonal bound, mine sums over the window `∀ i ≠ k, near (b k) (b i)` with window sums; proof written independently); RBM2D `git --no-optional-locks log -1 --format=%h` = `9e0f275`; diff-stat of ported files: none, no file was ported. From the own-project probe (`c961e62:RBM3D/Probe/T2016Pins.lean`): `ek_ellT_sq_ge` (:451), `ek_ratio_le` (:477), copied unchanged; `ek_arith_res1` generalises `ek_arith_claim` (:542-568); the `hwin` step of `ek_UN_anchor_bound` follows `ekSumDecay1_two` (:572-760).

Narrative (≤ 40 lines).
1. Route as in the ticket and section (a): triangle inequality first (`ek_core_bound`), no subset expansion; anchor index `k` (any index for `(sum_res_1)`, the index with `σ_k = σ_{k+1}` for NAL); window `{b : ∀ i ≠ k, |b_k − b_i| < R}`, `R = W^ε ℓ_s`; off the window `|A_b| ≤ W^{-D}` by `EKFastDecay` (pair `(k, i)`); on the window `ek_anchor_sum_le` factorises the sum with `Finset.prod_univ_sum` over `Fintype.piFinset` (`b k = x`, others in the ball around `x`).
2. `ek_UN_anchor_bound` gives `‖UN A a‖ ≤ ‖A‖ Rk (1 + C_X ρ² r)^{n−1} + W^{-D} Rk P^{n−1}` for any anchor row sum `Rk`; row sums of `uKer` from `norm_uKer_le` + `sum_norm_row_le`, window sums from `uKer = 1 + XiKer` and `ekXiBall_holds` at `Λ' = ρ = W^ε`, `R = ρ ℓ_s` (`1 ≤ R` from `ρ ≥ 1`, `ℓ_s ≥ 1`).
3. `(sum_res_1)`: `Rk = P ≤ 2qr` (`ek_ratio_le`, needs `t ≤ 1 − g²/L²`), `P ≤ W` (from `W⁻¹ ≤ (1−t)/(1−s)`); `ek_arith_res1` gives `P S^{n−1} ≤ ρ^{m'+2(n−1)} q r^n` for `2(1+C_X)^{n−1} < 4^{m'}`; constants `C = m' + 2n` (matches row 9 of (a)); tail `W^{-D} P^n ≤ W^{-D+n} ≤ W^{-D+C}`.
4. NAL: `Rk = C_s` from `ekSameRow_holds` (`cycProd (EKsgn m σ) k = PropSpin m (σ k) * PropSpin m (σ k)` by the hypothesis `σ_k = σ_{k+1}`); `ek_arith_nal`: `C_s S^{n−1} ≤ ρ^{m''+2(n−1)} r^{n−1}` for `C_s (1+C_X)^{n−1} < 4^{m''}`; `C = m'' + 2n − 2` (row 10); tail uses `C_s ≤ 4^{m''} ≤ W^{m''}` (`W ≥ W^ε ≥ 4`).
5. Constants depend on `(d, n, Λ, κ)` only (through `C_X`, `C_s`), not on `L, g, W, ε, D, s, t, m, σ, A`; `ε, D` enter only the exponent `W^{Cε}`, `W^{-D+C}`; `1 < D` is not used. No hypothesis was added to a pin, no pin was changed; `4 ≤ W^ε` is the pin's own hypothesis (T2016b).
6. Preflight section (a) needed no correction (no (a′)): C-formulas of rows 9–10 are the ones used; `W⁻¹ ≤ (1−t)/(1−s)` enters only at `P ≤ W` (row 4).
7. Registry: one `structuralProps` line (above), required because `ek_UN_anchor_bound` is a public theorem with `EKFastDecay` as hypothesis; the merge needs it (DECISIONS §20).

## (c) Verified Mathlib names (all elaborate in `#check @name`, script `mathlib_names_T2034.lean`, `import RBM3D.Evolution.SumDecay`, exit 0, 0 errors)
`Finset.sum_fiberwise`, `Finset.prod_univ_sum`, `Fintype.piFinset_univ`, `Fintype.mem_piFinset`, `Finset.mul_prod_erase`, `Finset.card_erase_of_mem`, `Finset.prod_le_prod₀`, `Finset.sum_filter`, `Finset.filter_filter`, `Finset.sum_ite_eq`, `Finset.ne_of_mem_erase`, `pow_unbounded_of_one_lt`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `norm_prod`, `norm_sum_le`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_one`, `inv_le_of_inv_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `Nat.cast_sub`, `ite_false`.
Deprecated names seen in this toolchain (build warnings, replaced): `if_false` → `ite_false`; `push_neg` → `push Not`.

## (d) Open issues and paper-delta candidates
- No new paper-delta candidate. `T2016a`, `T2016b` (`4 ≤ W^ε`), `T2016f` apply (DECISIONS §18) and are not re-proposed.
- The numerics of (a) used `W = max(25, P)` at the endpoint `t = 1 − g²/L²` (preflight finding); the Lean theorems take `W⁻¹ ≤ (1−t)/(1−s)` as the pin states, so no pin issue.
- Hub merge: `RBM3D/Test/Axioms.lean` may conflict on the last element of `structuralProps` with other tickets' Amend-1 registry lines (DECISIONS §20 (3): take the union, keep `]` on the last element). The root import `import RBM3D.Evolution.SumDecay` is added by the hub.
- `ek_core_bound`, `ek_anchor_sum_le`, `ek_UN_anchor_bound` are public (prefix `ek`, any anchor, any row sum `Rk`); nothing is claimed about their use in EK-4.
