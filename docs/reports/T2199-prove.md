Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct  5 18:09:09 UTC 2026

Notation: `N = (WL)^d` so `W ≤ N` (crude) and `W ≤ N^{1/d} ≤ N^{1/3}` (actual); `W ≥ N^𝔠` (Bandwidth); `g = lam n ≤ 𝔡⁻¹ = Λg` (WO); `ε₀' = min ε₀ 1`; `Ls = (Im m)⁻¹ log N`, `Im m ≥ κ' = min κ (4/5)` (`nqGood1_mE_im_ge`, `NQGood1.lean:404`). Scripts (Python, no Lean) are in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2199/` (`exps.py table.py slack2.py cross2.py inst.py`); numerical rows use `ε₀=1/10, 𝔠=1/6, 𝔡=1/10, τ_R=1/2, D₁=1`, `1+g² ≤ 101`.

### (i) Exponent table
**(i.1) Constants** (order `(d,k,Λg,κ') → C=nqGood1C → ε₀' → ε₁,εq → ε → D'' → D' → C_P* → C_K`; `C>0` abstract, `nqGood1C_pos`)

| name | value | constraint (consumer) | slack |
|---|---|---|---|
| `ε₀'` | `min ε₀ 1` | `ε₀' ≤ ε₀` (last step `N^{ε₀'} ≤ N^{ε₀}`, `N ≥ 1`, RHS factor `≥ 0`); `≤ 1` gives `2Cε ≤ 1/4` | `1/10` |
| `ε₁ = εq` | `ε₀'/8` | `>0` (pin, `assembledN`); budget `hε₁ : 0 ≤ ε₁` | `1/80` |
| `ε` | `min(ε₀'/(8C), 1/2)` | `0<ε<1` (`nonAlt_hkerN`); `Cε ≤ ε₀'/8` | `Cε = 1/80` for every `C ≥ 1/40`; `ε = 1/40, 1/80, 1/1600` at `C = 1/2, 1, 20` |
| `τ'` | `ε/2` | `0<τ'<ε` (`hdW`: `d W^{τ'} ≤ W^ε`) | `ε/2` |
| `D''` | `C+k+2+(4k+2)/𝔠` | `> k+1` (`hD''`); `> C+k+2Cε` (he2) | to `k+1`: `C+1+(4k+2)/𝔠`; to `C+k+2Cε`: `2+(4k+2)/𝔠−2Cε ≥ 61.975` (min over grid) |
| `D' = Dc` | `D''+1` | `1<Dc≤D'` (`hker`,`hA0cls`); `W^{-D'} ≤ W^{-D''}/2` (hδ) | `D''=90, D'=91` at `k=3, C=1` |
| `τ_R` | `min τ 1` | `0<τ_R≤1` (`yMomentsUnifN`, `nqBudget_merged_inputs`); `RangeCond τ t ⇒ RangeCond τ_R v` (`N ≥ 1`, `1−v ≥ 1−t`) | `1/2` |
| `τK; D_Y=D_t` | `1; k+1` | `τK>0`, `D_t ≥ 0` | — |
| `C_P*` | `max_σ C_P(σ)` of `yMomentsUnifN … τ_R E s v` | `≥ 0`, before the grid (proof body `AzumaProxyN2.lean:921` has witness `11+(4k+4)max 0 (1−τ')`) | `19` at `k=3, τ_R=1/2` |
| `C_K` | `D₁+2C_P*+6k+20+D''` | (a) `assembledN` (`D=D_Y`, `D₁→D₁+1`): `≥ D₁+1+4(k+1)+k+2C_P*+8`; (b) `nqBudget_merged_inputs` h1 `6k+18` (h2 `6k+8`, h3 `3k+4`, h4 `1` smaller); (c) hδ: `≥ D''+2k+5`; (d) hΔη `≥ 1` | (a) `k+7+D''`; (b) `D₁+2C_P*+2+D''`; (c) `D₁+2C_P*+4k+15`; at `k=3,C=1`: `C_K=167`, slacks `100, 131, 66` |

**(i.2) Absorption exponents** of the seven `budgetNonAltLinN` hypotheses (`W ≤ N` for positive, `W ≥ N^𝔠` for negative powers of `W`; condition: exponent of `N` `< ε₀'`; slack `= ε₀' −` exponent). `python3 slack2.py`:
```
ha1: Ce+e1                         min slack over k in{2,3,6}, C in{1/2,1,5,20}: 3/40 = 0.0750
ha2: Ce+2e1 (+polylog)             min slack over k in{2,3,6}, C in{1/2,1,5,20}: 1/16 = 0.0625
ha3: eq+Ce+e1 (+polylog)           min slack over k in{2,3,6}, C in{1/2,1,5,20}: 1/16 = 0.0625
he1: k-c(D1-C)                     min slack over k in{2,3,6}, C in{1/2,1,5,20}: 134/15 = 8.9333
he2a: eq+2k-1-c(D2-2Ce)/2          min slack over k in{2,3,6}, C in{1/2,1,5,20}: 1181/480 = 2.4604
he2b: eq+k+(k-1)/2-c(D2-Ce-C)/2    min slack over k in{2,3,6}, C in{1/2,1,5,20}: 2803/960 = 2.9198
he2c: eq+k-c(D2-C-k)/2             min slack over k in{2,3,6}, C in{1/2,1,5,20}: 781/240 = 3.2542
he3,he4: k-(k+1)                   min slack over k in{2,3,6}, C in{1/2,1,5,20}: 11/10 = 1.1000
D2-(C+k+2Ce)                       min slack over k in{2,3,6}, C in{1/2,1,5,20}: 2479/40 = 61.9750
```
(`k=4`, same script with `k=4`: slacks `0.075, 0.0625, 0.0625, 15.27, 2.627, 4.087, 5.254, 1.1, 109.975`.) `he2` splits `√(kap²+kap·W^C+W^{C+k})·W^{-D''/2}` with `kapFar = W^{Cε}((1+g²)N)^{k-1}` (`nqBudget_kapFar`, `nqBudget_qvFar`); `ha2`, `ha3` need `C(1+log x)^j x^a ≤ x^b` (`a<b`, `j=1`; `√z ≤ z` for `z ≥ 1`).

**(i.3) Numerical rows**, `log10(LHS/RHS)` (positive = not yet absorbed), worst over `k∈{2,3,6}, C∈{1/2,1,5,20}, Im m∈{1/2,0.968,1/10}, W∈{N^{1/6},N^{1/3}}` (`x*` = last point of the scan `log10 N = 10^{j/40−1}` with value `>0`, so `x*` is within 6% below the true crossover). `python3 table.py`:
```
row | worst log10(LHS/RHS) at log10N = 1,2,3,6,48.6,51.5,56.2,100 | crossover x* (actual W in [N^(1/6),N^(1/3)]) | x* with crude W<=N
ha1                  +0.7 +0.6 +0.5 +0.3 -3.3 -3.5 -3.9 -7.6 | 8.9 | 10.0
ha2                  +3.1 +3.4 +3.5 +3.6 +1.5 +1.3 +1.0 -1.9 | 70.8 | 79.4
ha3                  +2.1 +2.2 +2.2 +2.1 -0.4 -0.6 -1.0 -3.9 | 39.8 | 47.3
he1                  -7.9 -16.8 -25.7 -52.5 -433.1 -459.0 -501.0 -892.3 | 0.1 | 0.1
he2                  +8.7 +5.9 +3.1 -5.3 -116.3 -123.5 -135.0 -242.8 | 4.0 | 4.0
he3=he4              -0.3 -1.4 -2.5 -5.8 -52.7 -55.9 -61.0 -109.2 | 0.7 | 0.7
hdelta               -0.2 -0.3 -0.5 -1.0 -8.1 -8.6 -9.4 -16.7 | none(<=0 at 0.1) | none
heta                 +0.5 +0.0 -0.5 -2.0 -23.3 -24.8 -27.1 -49.0 | 2.0 | 2.0
hDeta                -130.5 -261.0 -391.5 -783.0 -6342.3 -6720.8 -7334.1 -13050.0 | none(<=0 at 0.1) | none
union                +0.8 -0.2 -1.2 -4.2 -46.8 -49.7 -54.4 -98.2 | 1.8 | 1.8
W^eps>=4             +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 +0.6 | 5623.4 | 5623.4
d*W^(eps/2)<=W^eps   +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 +0.5 | 8912.5 | 8912.5
W>=2                 +0.1 -0.0 -0.2 -0.7 -7.8 -8.3 -9.1 -16.4 | 1.8 | 1.8
```
Every row is `≤ 0` eventually. `ha2` at `Im m=0.968, C=1, W=N^{1/3}` (`python3 cross2.py`): `x* = 48.7 / 51.5 / 56.3` for `k=2/3/6` (`53.5` for `k=4`), `Im m=1/2`: `53.3 / 56.1 / 60.8` (T2186 (d) `48.6/51.5/56.2` reproduced); `Im m=1/10` (`κ=1/10`) `64.3 / 67.0 / 71.7`; `ha3` `30.6–36.5`. `he2` includes `(1+g²)^{k-1}, 1+g² ≤ 101` (at the reference row `k=3, C=1, Im m=1/2, W=N^{1/6}`, `x=6`, `he2` is `−10.19` against the drafter's `−13.6`; the other drafter values at `x=6` agree). The two `W^ε` rows are the only astronomical thresholds, inherent in `ε = ε₀'/(8C)` and the premises `4 ≤ W^ε`, `d W^{τ'} ≤ W^ε` of `nonAlt_hkerN`: closed forms `x ≥ log10 4/(𝔠ε)`, `x ≥ 2 log10 d/(𝔠ε)`: `289 / 458` at `C=1`, `5780 / 9161` at `C=20` (`W=N^{1/6}`); they are `∀ᶠ n` thresholds, never hypotheses.

**(i.4) Regime facts** (each at fixed `n`, derivation and premise)
- `hη`: `η_v⁻¹ = ((1−v)Im m)⁻¹ ≤ κ'⁻¹N^{1−τ_R} ≤ N` once `N^{τ_R} ≥ κ'⁻¹` (premises `RangeCond τ t`, `v ≤ t`, `κ' ≤ Im m`); row `heta`. `hΔη`: `Δ=(v−s)/K ≤ N^{−C_K}`, `v−s ≤ 1`, so `Δη_v⁻¹ ≤ N^{1−C_K} ≤ 1`.
- `hwL`: `v ≤ t ≤ 1−g²/L²` (`STCaseI`). `hWt`: `W⁻¹ ≤ (1−t)/(1−s) ≤ (1−v)/(1−s)` (eventual premise, `1−s>0`). `hκm`: `nqGood1_mE_im_ge`. `hg>0`: `lam ≥ W^{−d/2+𝔡}>0` (WO); `hgΛ`: `lam ≤ 𝔡⁻¹ = Λg` (WO). `hW`, `hWε`, `hdW`: `W ≥ N^𝔠 → ∞` (`SizeTendsto`).
- `hδ` (`j<K n`): `eeShiftErrN = N k(2k+2)η_{u_{j+1}}^{−(2k+3)}(W^{−d})^{2k+1}(u_{j+1}−u_j)` (defs, `W^dL^d=N`) `≤ k(2k+2)N^{2k+4}Δ ≤ k(2k+2)N^{2k+4−C_K} ≤ k(2k+2)N^{−D''−1}`; `≤ N^{−D''}/2` for `N ≥ 2k(2k+2)`; `W^{−D'} ≤ W^{−D''}/2` (`W ≥ 2`); `N^{−D''} ≤ W^{−D''}` (`W ≤ N`). Row `hdelta` `< 0` for all scanned `x`.
- Union: `Fintype.card{σ nonalt} ≤ 2^k`, `2^kN^{−(D₁+1)} ≤ N^{−D₁}` for `N ≥ 2^k` (row `union`). `STKbound sz E` (needed by `gridDriftN_envelope`, `GridEnvelopeN.lean:111`): `stKbound_holds sz hd hκ (inv_pos.2 h𝔡) hsize (Eventually.of_forall hE) hlam` (`KLFinal.lean:243`: `3 ≤ d`, `0<κ`, `0<𝔡⁻¹`, `SizeTendsto`, `|E n| ≤ 2−κ`, `0<lam n ≤ 𝔡⁻¹` eventually from WO), no premise.
- Field table of `GridAssemblyHypN` (merged source; "new" = proved in this ticket): `hE` `|E n| ≤ 2−κ`; `hu0 hu1 hΔ0` `ST_gridTime_zero/mono`, `gridTime_last`, `ST_gridStep_nonneg`, `v<1`; `hexp` `rfl` for `Af` + `stoppedDuhamelN_at`; `hκ0 hε0` `nonAlt_hκ0N`, `nonAlt_hε0N`; `hker` `nonAlt_hkerN`; `hδ0 hδD0` `W^{−D'} ≥ 0`; `hA0cls` `nonAlt_hA0clsN`; `hDcls` `nonAlt_hDclsN`; `hdrift` `nqLin_hdriftN`; `hdDrift0` new; `hc_pos` `cQVNonAltN_sum_pos`; `hv0 hw0` `Δ²P, Δ⁴P² ≥ 0` (`P ≥ 0`); `hY` `yMomentsUnifN` at `τ = nqLinExitTauN` (`nqLinExitMeasN`); `hstepErr0` new; `hR` `gridDriftN_envelope` + `stKbound_holds`, with `R = predIncN − Δ•driftTensorN` and `driftTensorN` the sum of the three `ℰ` terms by definition; arguments `hZmeas` `gridAsm_stronglyMeasurable_ZvecN`, `hsubG` `subGaussStop_linN` (needs hδ).
- New fields: `hdDrift0`: `dDriftLinN = Γ²(B^k/η)((k−2)Φ₁+Φ₂+Φ₃) ≥ 0` (`k ≥ 2`, `Φ_i,Γ ≥ 0`, `B>0`, `η>0`, `u_j<1`). `hc_pos`: `cQVNonAltN_sum_pos` needs `s n < v n` (strict window branch). `hstepErr0`: `stepErrN ≥ 0` (RBM2D `NonAltEnd_stepErrN_nonneg` `:817`, `envConst`, `kStepC`, `uStepC ≥ 0` by Bernoulli). `hker` at `u_K = v n`, `u_0 = s n`; `hA0cls`/`hDcls`/`hdrift` from `mem_of_lt_nqLinExitTauN` (components 1, 2); `Φc` enters only `hQ_nonAltN` and the exit time, which take any level (`hΦ` absent from their signatures); `hexp` is `rfl`, `Af (K n) = AvecN … (K n)` by `stoppedDuhamelN_at` since `τ = K n` on the good walk.
- Collapsed window `s n = v n`: `Δ=0`, `u_j = s n`, `pathH j = pathH 0` (`√0 = 0`), conclusion is the initial bound: `N^{ε₁}B_s^k ≤ N^{ε₀'}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k` (`ε₁ ≤ ε₀'`, `Λ ≥ 1`, `Φ_i ≥ 0`, `B ≥ 0`); `G = univ`.

### (ii) One concrete nondegenerate instance
Data: `sz0` (`d=3`, `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{−6}`, `N=(WL)^3`), `𝔠=1/6`, `𝔡=1/10`, `κ=1/10` (`κ'=1/10`), `τ=1/2`, `E ≡ 1/2` (`Im m = √15/4`), `s=0`, `t=1/16`, `v=1/32` (`Δ>0`), `k=3`, `σ=(+,−,+)`, `Λ=3`, `Φ₁=Φ₃=1`, `Φ₂=12`, `ε₀=1/10`, `D₁=1`; grid `K=max 1 ⌈N^{C_K}⌉`, `C_K = C+166` (`C=nqGood1C`, abstract). `python3 inst.py` (premises checked for `n<3000` by exact `Fraction`/integer arithmetic; closed forms: `N^{1/6}=2^{3.5}(n+1)^3 ≤ 2^5(n+1)^5 = W`, `lam=(2(n+1))^{−6} ≥ (2(n+1))^{−7}=W^{−7/5}`, `W ≥ 32`):
```
3<=d, k>=2, kappa,c,tau,dd,eps0,D1>0                                   True
|E|<=2-kappa; 0<=s<=v<=t<1                                             True
Lam>=0 (and >=1), Phi_i>=0                                             True
SizeTendsto: N(n)>=n, n<3000                                           True
Bandwidth 1/6: N <= W^6 (N^(1/6)<=W), n<3000                           True
WO 1/10: W^(-7/5)<=lam<=10, i.e. (2(n+1))^-7<=lam                      True
STCaseI: lam^2/L^2 <= 1-t, n<3000                                      True
RangeCond(1/2) t: N^(-1/2)<=15/16 iff N>=(16/15)^2                     True
W^-1<=(1-t)/(1-s)=15/16                                                True
sigma=(+,-,+) nonalternating: sigma_i=sigma_{i+1 mod 3}                True
n=0: L,W,N,lam = 4 32 2097152 1/64  N=2^21  Im m(1/2)=sqrt(15)/4=0.9682
eventual thresholds on n (sz0, k=3): C -> [row: last n with row>0], log10 N at the largest
C=0.5 {'ha2': '2.36e+02', 'ha3': '2.27e+01', 'hW^eps>=4': '3.16e+04', 'hdW': '1.78e+07'} binding: hdW x*=log10 N=136.8
C=1 {'ha2': '2.36e+02', 'ha3': '2.27e+01', 'hW^eps>=4': '1.78e+09', 'hdW': '7.50e+14'} binding: hdW x*=log10 N=274.1
C=5 {'ha2': '2.36e+02', 'ha3': '2.27e+01', 'hW^eps>=4': '5.62e+47', 'hdW': '1.00e+76'} binding: hdW x*=log10 N=1374.3
C=20 {'ha2': '2.36e+02', 'ha3': '2.27e+01', 'hW^eps>=4': '1.78e+192', 'hdW': '1.00e+305'} binding: hdW x*=log10 N=5496.3
```
All premises of `nqGridEndLinN` hold at `n=0` data (no `N=0`, empty index, collapsed window); the `∀ᶠ n` conclusion needs `n ≥ n₀(C)` (above; `ha1, he1–he4, hδ, hη, hΔη, union` hold from `n=1`), and the instance obtains `n` by `Filter.Eventually.exists` without evaluating it; `K ≈ N^{C_K}` is large by the pin, never evaluated. `RangeCond (1/2) tInst` follows from the merged `rangeCond_half` (`GridEnvelopeN.lean:694`, stated at `t ≡ 1/2`) because `1/2 ≤ 15/16`. Pin text (`python`-free `grep` on the check file): `Φc` occurs in 2 lines (its `∀` binder and the `GoodSetN` argument); `^ 2` and `C₀` occur 0 times; `STKbound` 0 times; right side `N^{ε₀}*(Λ n^(1/2)+Φ₁ n+Φ₂ n+Φ₃ n)*B_v^k` (line 30); `GoodLinN` takes `N^{ε₁}, Φ₁ n, Φ₂ n, Φ₃ n`, the same `N^{ε₁}` as `GoodSetN`.
Consumer fit (S3-12c, text check against `GridGoodNConcl` `GridGoodN.lean:505`, `NQLinConcl` `NQLin.lean:102`): both events use `gridTime s v K n j`, `((sz.size n:ℕ):ℝ)^ε`, the same `v, K`; `GridGoodNConcl` needs `ε,τ',D'>0` (pin gives them), `1 ≤ Φ` (`Φc = N^{C₀}`), `K n+1 ≤ N^C` (from `K ≤ ⌈N^{C_K}⌉ ≤ N^{C_K}+1`); `NQLinConcl` needs `ε>0` and the same `K`-bound; deterministic floor `N^{ε₀}B_v^k ≤` RHS since `Λ ≥ 1`; exponents depend on `v` only through `C_P*`.

**Verdict.** Target 0/1 (constants, absorption, regime, shift, union): PASS. Target 2 (`nqEndLin_assembly` at `nqLinExitTauN`): PASS (every field of `GridAssemblyHypN` is covered above or by a merged theorem; `hdDrift0`, `hstepErr0` are new). Target 3 (`nqGridEndLinN`, pin, collapsed window, union): PASS. Caveats, not FAILs: thresholds in `n` for `4 ≤ W^ε` and `d W^{τ'} ≤ W^ε` are large for large `C` (above) and only eventual; `rangeCond_half` is at `t ≡ 1/2`, not `tInst`.
## (b) Script output — Mon Oct  5 18:53:45 UTC 2026
Scratch scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2199/` (`final_check.sh`, `stmt_diff.py`, `registry.lean`, `axioms_all.lean`, `stmt_check.lean`).
```
$ final_check.sh   (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2199)
Mon Oct  5 18:51:46 UTC 2026
== git: branch t/T2199 vs main
cfafa98 T2199: S3-12b Induction/NQEndLin (nqGridEndLinN, the non-alternating grid endpoint with the linear right side)
70c4283 T2199: WIP NQEndLin (absorption, regime, assembly, endpoint nqGridEndLinN; instances pending)
b43cb93 T2195: merge LW-10c2 Graph/LocalRegular6b
 RBM3D/Induction/NQEndLin.lean | 1592 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1592 insertions(+)
== file size; sorry/admit/native_decide/axiom/maxHeartbeats count
    1592
0
== lake build RBM3D.Induction.NQEndLin | tail -2
info: RBM3D/Induction/NQLin.lean:1775:0: 'RBM.Ind.NQLinInst.budgetNonAltLinN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3842 jobs).
== lake build | tail -1  (whole library; RBM3D.lean does not import the new module yet)
Build completed successfully (4001 jobs).
== registry pre-check: import RBM3D; import RBM3D.Induction.NQEndLin; #assert_rbm_axioms
exit: 0
axiom audit: 5882 theorems, 2072 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 109 (borrowed 1, owed 85, structural 23).
== #print axioms, the 40 public declarations of the file
exit: 0
standard three: 39 of       40; the other:
'RBM.Ind.NQEndLinInst.hσ3_i' depends on axioms: [propext, Quot.sound]
'RBM.Ind.nqGridEndLinN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.assembly_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.nqEndLin_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
== #print axioms, the private declarations (copy of the file; scratch)
standard three: 36 of       36
'_private._stdin.0.RBM.Ind.nqEndLin_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
== stmt_diff.py: theorem statement vs the def body of docs/tickets/checks/T2199-check.lean
check-file def body lines: 30   theorem statement lines: 30
IDENTICAL
== lake env lean stmt_check.lean: check-file section 2 + example : T2199_nqGridEndLinN := @nqGridEndLinN
exit: 0
== name-clash grep (nqGridEndLinN, nqEndLin_assembly, nqEnd_, NQEndLinInst, NQEndArith, NQEndLin): hits in main worktree; in T2199 worktree outside the new file
       0
       0
== RBM2D: git log -1 (HEAD); diff --stat c9a24cf HEAD for the two ported files
9e0f275
 RBM2D/Induction/NonAltEnd.lean      | 490 ++---------------------------
 RBM2D/Induction/StoppedEndDefs.lean | 598 ++++++------------------------------
 2 files changed, 121 insertions(+), 967 deletions(-)
== public nqEndLin_assembly (private removed in a scratch copy, import RBM3D, #assert_rbm_axioms): registry reply
Tpub.lean:1591:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Ind.YMomentBoundsN]
Mon Oct  5 18:52:27 UTC 2026
```
Target statement, extracted by script (`sed -n '1067,1097p' RBM3D/Induction/NQEndLin.lean`):
```
theorem nqGridEndLinN :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
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
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd d (sz.L n),
            ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                (sz.Bctl n (v n)) ^ k := by
```
Compiled nonempty instance (`sed -n '1552,1567p'`, then `grep -n "^example :="`): the data are `sz0` (`d = 3`), `Einst ≡ 1/2`, `sInst ≡ 0`, `tInst ≡ 1/16`, `vg ≡ 1/32`, `Λ3 ≡ 3`, `Φ1 ≡ 1`, `Φ₂ ≡ 12`:
```
theorem nqEndLin_instance (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KC C_K n, pathH sz0 sInst vg (KC C_K) n j ω ∈
            sz0.GoodSetN n (Einst n) (gridTime sInst vg (KC C_K) n j) k
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Λ3 n) (Φ1 n) τ' D' ∩
              GoodLinN sz0 n (Einst n) (gridTime sInst vg (KC C_K) n j) k
                (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Φ1 n) (12 : ℝ) (Φ1 n)) →
          (∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd 3 (sz0.L n),
            ‖sz0.STLKM n (Einst n) (sInst n) (pathH sz0 sInst vg (KC C_K) n 0 ω) σ a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ ε₁ * (sz0.Bctl n (sInst n)) ^ k) →
          ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) → ∀ a : Fin k → Zd 3 (sz0.L n),
            ‖sz0.STLKM n (Einst n) (vg n) (pathH sz0 sInst vg (KC C_K) n (KC C_K n) ω) σ a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (Λ3 n ^ ((1 : ℝ) / 2) + Φ1 n + 12 + Φ1 n) *
                (sz0.Bctl n (vg n)) ^ k := by
1580: example := nqEndLin_instance 2 le_rfl
1583: example := nqEndLin_instance 3 (by norm_num)
1586: example := nqEndLin_instance 4 (by norm_num)
```
Port map (source: RBM2D `RBM2D/Induction/NonAltEnd.lean` at commit `c9a24cf`, line numbers verified by `git show c9a24cf:...`; RBM1D: no file ported directly):
```
NonAltEnd:60 ev_rpow_le, :70 ev_rpow_log_le, :94 ev_polylog_le -> nqEnd_ev_rpow_le, nqEnd_ev_rpow_log_le, nqEnd_ev_polylog_le (verbatim, real x)
:266 Wneg_le -> nqEnd_Wpow_le (any exponent <= 0);  :276 ev_ha1, :295 ev_ha2, :342 ev_ha3 -> nqEnd_ev_ha1/2/3 (re-derived: C*eps, W <= N, kappa')
:416 ev_he1 -> nqEnd_ev_he1;  :573 ev_he4 -> nqEnd_ev_he4 (he3 and he4);  :437 ev_he2, :484 ev_he3 -> nqEnd_he2_bound, nqEnd_he2_final, nqEnd_ev_he2 (new)
:593 etaT_inv_le, :634 ev_hη -> nqEnd_etaT_inv_le, nqEnd_ev_hη (kappa' for c0);  :652 step_le, :667 hΔN, :681 K_mul_step, :689 gridTime_succ_sub -> nqEnd_step_le,
  nqEnd_hΔη, nqEnd_K_mul_step, nqEnd_gridTime_succ_sub;  :694 eeShiftErr_le, :717 ev_hδ -> nqEnd_eeShiftErrN_le, nqEnd_ev_hδ (eta^-1 <= N, C_K >= D''+2k+5)
:817 stepErrN_nonneg, :853 assembly -> nqEnd_stepErrN_nonneg, nqEndLin_assembly (exit time nqLinExitTauN, dDriftLinN, the fields from nonAlt_*N, subGaussStop_linN)
:1014 pathH_collapse, :1025 collapse, :1059 rangeCond_mono, :1068 ev_union, :1092 yMomentsMax -> nqEnd_pathH_collapse, nqEnd_collapse, nqEnd_rangeCond_mono,
  nqEnd_ev_union, nqEnd_yMomentsMax;  :1116 nonAltGridEnd -> nqGridEndLinN;  NonAltEndCheck :1291-1610 (asymp_instance :1297, KC :1469, assembly_instance :1488, nonAltEnd_instance :1535) -> NQEndLinInst
not ported: :123-257 (d = 2 size facts, cCase1/cPair1/cKap/aQv, im_ge: replaced by W^d L^d = N, W <= N, nqGood1_mE_im_ge), :610 ev_hM1 (no scaleM at d >= 3),
  :585 ev_he5 (same as he4), :1083 gridK_le_ceil (K is a parameter)
```
Narrative.
1. Delivered: targets 0-3 and instances (1)-(5) in `RBM3D/Induction/NQEndLin.lean` (1592 lines; the ticket band is 1200 / 1450 / 1700) on t/T2199, commits 70c4283 (WIP) and cfafa98; the diff against main is that one file.
2. Shape: private `nqEnd_*` lemmas (§0-§4), private `nqEndLin_assembly`, public `nqGridEndLinN` (§5), public `NQEndLinInst.*` (§6). No `set_option maxHeartbeats`, no `sorry`/`admit`/`native_decide`/`axiom` (count 0 above).
3. Statement: `nqGridEndLinN` is the check-file pin copied by script into the theorem header (diff IDENTICAL) and `example : T2199_nqGridEndLinN := @nqGridEndLinN` compiles; no hypothesis added, nothing weakened.
4. Constants follow target 0 (`ε₀' = min ε₀ 1`, `ε₁ = εq = ε₀'/8`, `ε = min (ε₀'/(8C)) (1/2)`, `τ' = ε/2`, `D'' = C + k + 2 + (4k+2)/𝔠`, `D' = D''+1`, `τ_K = 1`, `D_Y = D_t = k+1`, `C_K = D₁ + 2C_P* + 6k + 20 + D''`, `C_P* = max_σ C_P`). Every inequality between them that the absorption lemmas and the regime facts use is proved once, in the private structure `NQEndArith` (`nqEnd_arith`), and used by the endpoint and by the instances.
5. he2 is new relative to RBM2D. `nqBudget_qvFar` contains `W^{2Cε}`, `W^{Cε+C}`, `W^{C+k}` against `W^{-D''}`, and `D''` has `C` but not `C/𝔠`, so bounding each positive power by `W ≤ N` first fails for large `C` (the rows of (a) (i.2) cover `C ≤ 20` only). `nqEnd_he2_bound` merges the `W`-powers into `W^e`, `e ≤ 0`, then uses `W ≥ N^𝔠`, with the common `N`-exponent `ξ = -(2k+4)`.
6. `Φc` enters only `nqLinExitTauN` and the `GoodSetN` membership used by `nonAlt_hA0clsN`, `nonAlt_hDclsN`, `subGaussStop_linN`; the right side comes from `budgetNonAltLinN`: `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k`, no `Φc`, no square. `STKbound` is internal: `stKbound_holds sz hd hκ hΛg hsize (Eventually.of_forall hE) hlam` with `Λg = 𝔡⁻¹`, `hlam` from `WO`.
7. Registry: `nqEndLin_assembly` is private because its binder `hY` mentions `YMomentBoundsN` (scratch copy with `private` removed: the registry replies `[RBM.Ind.YMomentBoundsN]`, above); with it private the pre-check exits 0. `Test/Axioms.lean` and `RBM3D.lean` are untouched.
8. Instances: `κ = 1` (so `κ' = min 1 (4/5)`; the preflight's `inst.py` used `κ = 1/10`), `k ∈ {2,3,4}` (`example`s), grid `KC C_K = max 1 ⌈N^{C_K}⌉`, `Δ > 0` by `window_nondegenerate`. `RangeCond (1/2) tInst` is `RBM.Green.rangeCond_mono` applied to the merged `GridEnvelopeNCheck.rangeCond_half`. `C = nqGood1C 3 3 10 κ'` stays abstract (`Classical.choose`; only `C > 0` is used), so each instance holds for the actual `C`. In `nqEndLin_instance` every deterministic premise of `nqGridEndLinN` is discharged and no hypothesis is left; the good-walk and initial hypotheses stay inside the conclusion (S3-12c). `assembly_instance` discharges every premise of `nqEndLin_assembly` at its own constants (`ε = 1/2`, `τ' = 1/4`, `D'' = 5`, `D' = 5+1`, `D_Y = 4`, `εq = 1/10`, `D₁ = 2`, `C_K = 100 + 2C_P`).
9. Section (a) was not edited and no `(a′)` is needed: nothing in it was contradicted. RBM2D HEAD (9e0f275) differs from the cited c9a24cf in the two ported files (stat above); every port is from c9a24cf, as the ticket says.

## (c) Verified Mathlib names (compiled in this file; signatures from `#check`)
```
Real.rpow_le_rpow_of_nonpos : 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_le_rpow_of_exponent_le : 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.rpow_le_rpow : 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
Real.rpow_add : 0 < x → ∀ y z, x ^ (y + z) = x ^ y * x ^ z
Real.rpow_add' : 0 ≤ x → y + z ≠ 0 → x ^ (y + z) = x ^ y * x ^ z
Real.rpow_mul : 0 ≤ x → ∀ y z, x ^ (y * z) = (x ^ y) ^ z
Real.rpow_natCast : ∀ x n, x ^ (n : ℝ) = x ^ n
Real.rpow_neg : 0 ≤ x → ∀ y, x ^ (-y) = (x ^ y)⁻¹
Real.rpow_neg_one : ∀ x, x ^ (-1) = x⁻¹
Real.rpow_pos_of_pos : 0 < x → ∀ y, 0 < x ^ y
Real.rpow_nonneg : 0 ≤ x → ∀ y, 0 ≤ x ^ y
Real.one_le_rpow : 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
Real.rpow_le_one_of_one_le_of_nonpos : 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Real.log_le_rpow_div : 0 ≤ x → 0 < ε → Real.log x ≤ x ^ ε / ε
Real.log_nonneg : 1 ≤ x → 0 ≤ Real.log x
Real.sqrt_le_sqrt : x ≤ y → √x ≤ √y
Real.sqrt_mul : 0 ≤ x → ∀ y, √(x * y) = √x * √y
Real.sqrt_eq_rpow : ∀ x, √x = x ^ (1 / 2)
Real.sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
tendsto_rpow_atTop : 0 < y → Tendsto (fun x => x ^ y) atTop atTop
Filter.Tendsto.eventually_ge_atTop : Tendsto f l atTop → ∀ c, ∀ᶠ x in l, c ≤ f x
Filter.eventually_all : [Finite ι] (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x
Filter.Eventually.exists : [f.NeBot] → (∀ᶠ x in f, p x) → ∃ x, p x
MeasureTheory.measureReal_iUnion_fintype_le : [Fintype β] ∀ f, μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p)
MeasureTheory.measureReal_empty : μ.real ∅ = 0
Fintype.card_subtype_le : Fintype.card {x // p x} ≤ Fintype.card α
one_add_mul_le_pow : -2 ≤ a → ∀ n, 1 + n * a ≤ (1 + a) ^ n
pow_le_one₀ : 0 ≤ a → a ≤ 1 → a ^ n ≤ 1;   one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n;   pow_le_pow_left₀ : 0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n
inv_le_one_of_one_le₀ : 1 ≤ a → a⁻¹ ≤ 1;   inv_anti₀ : 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹;   inv_mul_cancel₀ : a ≠ 0 → a⁻¹ * a = 1
div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c);   div_le_one : 0 < b → (a / b ≤ 1 ↔ a ≤ b);   mul_div_cancel₀ : b ≠ 0 → b * (a / b) = a
mul_le_of_le_one_right : 0 ≤ a → b ≤ 1 → a * b ≤ a;   le_mul_of_one_le_right : 0 ≤ a → 1 ≤ b → a ≤ a * b
one_div_le_one_div_of_le : 0 < a → a ≤ b → 1 / b ≤ 1 / a;   div_le_div_of_nonneg_right : a ≤ b → 0 ≤ c → a / c ≤ b / c
Nat.le_self_pow : n ≠ 0 → ∀ a, a ≤ a ^ n;   Nat.pow_le_pow_left : n ≤ m → ∀ i, n ^ i ≤ m ^ i;   Nat.le_mul_of_pos_right : 0 < m → n ≤ n * m
Nat.ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a;   Nat.le_ceil : a ≤ ⌈a⌉₊;   Nat.cast_sub : m ≤ n → ((n - m : ℕ) : R) = n - m
Finset.sup'_le : (∀ b ∈ s, f b ≤ a) → s.sup' H f ≤ a;   Finset.le_sup' : b ∈ s → f b ≤ s.sup' _ f
Set.compl_iInter : (⋂ i, s i)ᶜ = ⋃ i, (s i)ᶜ;   Set.mem_iInter : x ∈ ⋂ i, s i ↔ ∀ i, x ∈ s i
```
Verified absent: `RBM.Gauss.Sizes.rangeCond_mono` (the name is `RBM.Green.rangeCond_mono`); `measureReal_iUnion_fintype_le` unqualified (needs `open MeasureTheory` or the full name); `RBM.Gauss.Sizes.SizeTendsto.eventually_ge_atTop` (dot notation on `sz.SizeTendsto` reaches `Filter.Tendsto.eventually_ge_atTop` by unfolding).

## (d) Open issues and paper-delta candidates
Open issues (none blocks the merge):
- S3-12c still owes the good-event probability (`gridGoodN_holds` ∩ `nqLinGood_holds` at `Φc = N^{C₀}`), the initial event from `STLK s`, `map_pathH_eq`, and the net lift by `cont_core` with the deterministic floor `N^{ε₀}B_v^k ≤` right side (`Λ ≥ 1`).
- The eventual thresholds in `n` are those of (a) (i.3) and (ii) (the largest come from `4 ≤ W^ε` and `d W^{τ'} ≤ W^ε`: `log₁₀ N ≈ 274` at `C = 1` for `sz0`); they stay `∀ᶠ n`, never hypotheses.
- `nqEndLin_assembly` can be made public only after `YMomentBoundsN` is classified in `Test/Axioms.lean` (not writable here).
Paper-delta candidates (proposals; the dispatcher numbers them):
- T2199a: `lem:STOeq_NQ` is proved on the grid for one end time `v`, with `GoodSetN` at a free crude level `Φc` and `GoodLinN` at the deterministic levels `Φ₁ Φ₂ Φ₃`; right side `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k` (route (R), DECISIONS §62 (2)); the paper's (am;asoiuw) (`3_5:1143-1148`) is the `sup_u` form in terms of `Ξ̂`, `Ξ` (S3-12c).
- T2199b: explicit exponents and eventual thresholds for "`N` large enough" (`ε₀' = min ε₀ 1`, `ε₁ = εq = ε₀'/8`, `ε = min (ε₀'/(8C)) (1/2)`, `τ' = ε/2`, `D'' = C + k + 2 + (4k+2)/𝔠`, `D' = D''+1`, `C_K = D₁ + 2C_P* + 6k + 20 + D''`; constants not optimal, crude `W ≤ N` for the positive powers of `W`).
- T2199c: the collapsed window `v_n = s_n` (`Δ = 0`, `H_j = H_0`, `G = univ`; `hc_pos` of the assembly needs `s_n < v_n`).
- T2199d: premises of the endpoint: `W⁻¹ ≤ (1−t)/(1−s)` eventually (the window of EK-6 in `nonAlt_hkerN`) and `STCaseI` (`1−t ≥ g²/L²`, which gives `v ≤ 1−g²/L²`).
- T2199e: `STKbound` is not a premise (`stKbound_holds` from `3 ≤ d`, `N → ∞`, `|E| ≤ 2−κ`, `0 < g ≤ 𝔡⁻¹` from `WO`); the `Y`-moment constant is `C_P* = max_σ C_P(σ)` of `yMomentsUnifN`, fixed before the grid; the union over the non-alternating `σ` uses the failure exponent `D₁+1` per sign vector (`≤ 2^k` of them).
