Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 05:55:26 UTC 2026

Notation: `Bc = Bctl` (= W^{-d} Bparam, `Defs/Sizes.lean:214`), `T0 = BAflowT0`, `g0 = √T0·lam` (`FlowPins.lean:386`), `N = (WL)^d`, `A = (κ+1)/κ`. Files cited as seen by `sed`/`grep` in this stage; script `pre.py` in the scratchpad (`.../scratchpad/T2441/pre.py`).

### (i) Exponent / constant table (value | constraint | slack)
| # | quantity | value and where it comes from | constraint | slack |
|---|---|---|---|---|
| 1 | input = output exponent γ | 3/2 (`BATwistLoopLaw`, `TwistPins:95`); (p,q)=(2,2) in `BATwistSrc3` (`∀ p q ≥ 1`) | γ* = min(3/2, 2−1/(4p)−1/(2q)) = 3/2 | 13/8−3/2 = **1/8**; (p,q)=(1,2): 0 |
| 2 | Src3 exponent e | 4−1/(2p)−1/q = 13/4 | regime-(i) martingale integral needs e ≥ 2 (TP:165 writes e−2 ≥ 1: only the e ≥ 2 is used); martingale exponent e/2 = 13/8 ≥ 3/2 | 5/4 and 1/8 |
| 3 | drift (B̃₁, Ẽ^G̊: `Src1/2`, e=2) | ∫η_v⁻¹Bc_v² dv ≤ Bc_u²·log((1−s)/(1−u))/Im m (Bc increasing in v) | ≥ 3/2 | 1/2 |
| 4 | B̃₂ (`Src4`, γ=3/2) | γ+1/6 = 5/3; output `Bc^{3/2}(1+Bc^{1/6}Ξ)` | equal exponents, `log W`, `W^{2ε}` go into `≺`; regime (i) integral needs γ+1/6 ≥ 1 | 0 (output); 2/3 |
| 5 | 𝔠d (∃ in the frame) | min(1/100, 1/(30·Cd) [`TwistKer2:424`], 1/(2d), the five `Src` constants; `st5_conStInd_mono` `Step5Kit:101`, pattern `:286-304`) | `d·𝔠d < 1` (row 7), `𝔠d < 1/8` (row 12), Src constants | `𝔠d ≤ 1/100` alone does NOT give `d𝔠d<1` for d ≥ 100: the pin must put `1/(2d)` in the min (d=3: 1/6 vs 1/100) |
| 6 | log((1−s)/(1−τ)) | ≤ 𝔠d·log(1/Bc_τ) ≤ 𝔠d (d log W + log(1+𝔡⁻²)) (Bc ≥ W^{-d}/(1+lam²), lam ≤ 𝔡⁻¹ by `WO`) | ≤ C log W (C=1 for 𝔠d ≤ 1/(2d)) | script n=20: 0.55 vs log W = 18.7 |
| 7 | `BATwKerFar` side conditions | `u ≤ 1−g0²/L²`: 1−u ≥ 1−τ ≥ lam²/L² ≥ g0²/L² (`STCaseI`, g0 ≤ lam). `W⁻¹ ≤ (1−u)/(1−v)`: ≥ (1−τ)/(1−s) ≥ Bc_τ^{𝔠d} ≥ (W^d(1+𝔡⁻²))^{−𝔠d} | holds once `W^{1−d𝔠d} ≥ (1+𝔡⁻²)^{𝔠d}`: the power is `W^{d𝔠d} ≤ W^{1/2}` | 1/2 in the W-exponent (eventually) |
| 8 | F1 (g0 against lam) | (a) ℓ_v(g0) ≥ √T0·ℓ_v(lam) ≥ ℓ_v(lam)/√A (T0 ≥ κ/(κ+1): Im z ≤ 1, Im m ≥ κ); `zdistD ≤ d·zdistInf` (`zdistD_le_mul_zdistInf`, `Sizes:122`): ε' = ε + log(3d√A)/log W (**the factor d is not in the ticket**; merged `baTwKDecay_holds` `TwistKer:444-455` is already at the model scale in `zdistInf`). (b) T.10(d): (1−v)L² ≤ (1−s)L² ≤ lam² = g0²/T0 ≤ A·g0². (c) (c·x+a)/(c·x+b) ≤ c⁻¹(x+a)/(x+b) for c ≤ 1 gives κ_{v,u}(g0) ≤ A·κ_{v,u}(lam) | constants only | constants in (d,κ,ε,𝔡) |
| 9 | Bc comparability, regime (i) | 1 ≤ (g²+1−v)·B_{v,0} ≤ 1+(L²+1)/L^d ≤ 1+10/27 for L ≥ 3, d ≥ 3 (uses d ≥ 3) | B ≍ (g²+1−v)⁻¹ | script max 1.127 at L=8 (= bound) |
| 10 | regime (i) integrals, κ_{v,u} = (g²+1−v)/(g²+1−u) | ∫κη⁻¹B_v^e / (B_u^e log/Im m): drift (e=2), B̃₂ (5/3), martingale κ² (13/4) | ≤ 1·(const) | script [R]: 0.43–0.95 |
| 11 | regime (ii) bound (TP:169) | ∫η⁻¹B_v²dv ≤ (g⁻⁴ log((1−s)/(1−u)) + (L^d(1−u))⁻²/2)/Im m; B_u ≥ max(1/(2g²), (L^d(1−u))⁻¹) ⇒ ≤ (4 log+1/2)B_u²/Im m | Im m ≥ κ | script: 0.50 vs 29–37 |
| 12 | martingale weight (derived; simplifies TP) | `‖Ũ_{v,u}‖_{∞→∞} ≤ (1−v)/(1−u) ≤ (1−s)/(1−τ) ≤ Bc_τ^{−𝔠d}` (T.10(a), `STConStInd`), so `(Ũ⊗Ũ)∘EE(a,a) ≤ Bc_τ^{−2𝔠d}·max EE` (CS conjunct of `Src3`) in every case; martingale ≺ Bc^{13/8−𝔠d} | 13/8−𝔠d ≥ 3/2 | 1/8−𝔠d ≥ 0.115 (𝔠d ≤ 1/100). Decay (T.10(b)) is needed only for the `Z_s` term and B̃₂ (no loss allowed) and the drift in case B |  |
| 13 | grid budget (iv) | merged `C₀=11`, `CK_rem=6` (`TwistGridRem2:394`), `CK_tail=2D+20` (`TwistGridTail2:304`), `CK_wtail=3D+40` (`TwistGridWTail2:1234`): `CK=3D+40`. 1−τ ≥ 1−T0 = Im z/(Im m+Im z) ≥ N^{−1+ε}/2 (Im m(Im m+Im z) ≤ 1 from (self_m)); ‖MΘ_u‖ ≤ (1−u)⁻¹; weights ≤ 2N^{1−ε}+N^{𝔠d}c (Abel sum over j: Σ‖U_{j+1}−U_j‖ ≤ (τ−s)/(1−τ)) | error ≤ N^{12−CK/2} against floor Bc_τ^{3/2} ≥ c·N^{−3/2} (Bc ≥ W^{−d}/(1+𝔡⁻²) ≥ N⁻¹/(1+𝔡⁻²)); decision-4 term Δ·MΘ·Mart_k ≤ N^{1−CK+o(1)} | D=1: 12−43/2 = −19/2, slack 8; D=5: slack 14 |
| 14 | bootstrap form (1a (iii)) | **chosen: `≺` at a deterministic level** `Ξ : ℕ → ℝ`, `1 ≤ Ξ n`; hypothesis `PrecL μ (U := TimeIcc s t n × (Fin 2→Bool) × Zd×Zd×Zd) (‖twL2'−twK‖) (fun n _ _ => Ξ n * Bc n v^(3/2))` (`twSrc` shape, `TwistPins:249`); conclusion `PrecL μ (U := (Fin 2→Bool)×Zd×Zd×Zd) (‖twL2' τ−twK τ‖) (fun n _ _ => Bc n (τ n)^(3/2)*(1+Bc n (τ n)^(1/6)*Ξ n))`. | grid: `ST_grid_whp_of_sections` (`Step2Events:93-117`) takes per-section `Prec` of `F(seqHflow n tt ω)`, `Z(…)` with `F,Z` measurable functions of the matrix at ONE time: a deterministic `Ξ` fits (`precomp_param`), a pathwise `Ξ(ω)` (sup over `v` of the coupling) does not. `Src4`'s premise is `∀ ω`: feed it `Ξ'(n,ω) = N^τΞ_n` on the good event, the pathwise a-priori bound (`TwistKer_twL2_bounds` `TwistKer:1331`: `‖twL2'‖ ≤ η⁻²`) on the bad one (prob. ≤ N^{−D} by `badSetAt`/`StochDomAt`, `StochDomAt.lean:53-63`), then B̃₂ ≺ Ξ_n η⁻¹Bc^{5/3} deterministic | consequence for TL2e: Ξ_j is a deterministic sequence; iterate Ξ_{j+1}=N^{τ'}(1+Bc_t^{1/6}Ξ_j) from Ξ_0 = N^{C} (a-priori); contraction needs Bc_t ≤ W^{−2𝔡}+2N^{−ε} ≤ N^{−c} (`lam_sq_mul_pow_ge` `Sizes:193`, row 13), O(6C/c) rounds, each followed by TL2e's net |
| 15 | T.12'' (target 2) | σ0≠σ1, `t ≤ T0 < 1` (`BAt0_lt_one`), `BAReal` from `BAflow_real` (`GreenSchur:59`); row sums of Θ^{(+,−)}: `BATheta_row_sum_pm` (`KBase:381`); **(−,+) is `BATheta_swap` (`KBase:350`), not `BATheta_conj` (`:362`, which is (−,−) vs (+,+))**; M*M = (M−M*)/(2i Im m) and M M* the same (M−M* = M((M*)⁻¹−M⁻¹)M*, (M*)⁻¹−M⁻¹ = m−m̄ = 2i Im m); `BAMB_symm` (`Ward:83`) turns M^* into M̄; `eta` of `baFMz` = `etaOf (BAmF) t = (1−t)·Im m` (`FlowPins:328`, `GLoopFlow:58`) | identity exact | script [T]: ≤ 1e-15 relative |
| 16 | TL1 at τ ∈ [s,t] (case C) | `LWAvgLawgL` from `twSteps.1` (`STAvgUgL`, `Step2Gen:491`) with `K^{(1)} = PropSpin m = m` (`baKsol_one` `KInduct:77`, `Propagator/Pins:30`) restricted by `precomp_param`; `STLmaxgL` (`Carrier:87`) = `twSteps` conjunct 2 pointwise: **derivable, no missing premise** | `BATwistAvgProd_holds` `TwistAvgB:451` | zero mode: \|P Z\| ≤ 2(Nη)⁻¹ Bc ≤ (2/κ)Bc² (as (N(1−τ))⁻¹ ≤ Bc) |
| 17 | case table: case × merged input | (A) σ1=σ2, both regimes: `baEKSameRow_holds` `EKPins:568` (B) σ1≠σ2, `STCaseI`: `baTwKerFar_holds` `TwistKer:86`, `baTwKDecay_holds` `TwistKer:455`, `baTwistSrc5_holds` `TwistKer2:1364`, `baTwistSrc1/2/4` `TwistKer2:168/589/422`, `baTwistSrc3` `TwistQV:1385`. (C) σ1≠σ2, `STCaseII`: `baTwKerZero_holds` `TwistKer:256` at A=(κ+1)/κ (its norm is ∞→∞, `open scoped Matrix.Norms.Operator`), rows 15-16, `twWard_holds` `TwistPins:412`. Common: `BATwistDuhamel_holds` `TwistGrid2:143`, `BATwistHier_holds` `TwistGrid:855`, `BAuKer_eq_one_add` `EKPins:62`, `ST_model_le_path`/`ST_pathP_eq_seqP` (`Step2Events:566`, `Step2Core:400`) | each case needs its own `Src` constants in 𝔠d (row 5) | – |

### (ii) One concrete nondegenerate instance
Data: d=3, E=0 (Re z = 0 by λ→−λ on the even-L torus), (κ,ε,𝔡,𝔠)=(1/2,1/10,1/10,1/6) as `flow_sz0`.
- **I-A (`STCaseI`)**: `sz0` (L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^{−6}), `z = 6i/5 − m_w` (`zSeq`), s≡1/2, t≡2/3, 𝔠d=1/100, Ξ≡1; `STConStInd` is eventual (false at n=0, true for all n ≥ 8, thresholds not astronomical).
- **I-B (`STCaseII`)**: **no merged `BAFlow` datum has Case II** (sz0: lam²/L² ≤ 1.5e-5 against 1−t ≥ 0.3056; `GreenSchur_szF` lam=1/100, T0 ≤ 100/121; its sizes are `private`). Keeping `STCaseII sz0 s t` as an instance hypothesis would be a **False premise**. A mathematical datum: L≡4, W_n=n+1, lam≡5, z≡6i/5−m_w (`inst_BAFlow` pattern, `GreenSchur:495-560`), κ=1/4, ε=1/2, 𝔡=1/10 (lam ≤ 1/𝔡), s≡1/10, t≡1/5. Numbers below.
- **Target 2** at the ticket's `c₂=(1,0,0)`: Im M_{c₂c₁} = 0 (bipartite lattice, E=0), so both sides are 0 (degenerate, the identity is 0=0); use `c₂=(1,1,0)` (|rhs| = 2.06e-8 at I-A n=0, 1.74e-3 at I-B).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2441/pre.py`
```
[E] exact exponents: (p,q)=(2,2): e=4-1/(2p)-1/q=13/4, martingale e/2=13/8>=3/2 (slack 1/8; (p,q)=(1,2): e/2=3/2, slack 0); gamma*=3/2; B2: gamma+1/6=5/3 (needs >=1); drift 2 vs 3/2 (slack 1/2); regime-(i) martingale integral needs e>=2: True
[G] grid budget (merged C0=11, CK_rem=6, CK_tail=2D+20, CK_wtail=3D+40): weighted Rem error <= (2N^(1-eps)+c N^(1/100)) N^11 sqrt(Delta), sqrt(Delta)<=N^(-CK/2):
    D=1: CK=43, error exponent <= 12-CK/2=-19/2, target floor N^(-3/2): slack 8; decision-4 term Delta*N*Mart <= N^(1-CK+small)
    D=5: CK=55, error exponent <= 12-CK/2=-31/2, target floor N^(-3/2): slack 14; decision-4 term Delta*N*Mart <= N^(1-CK+small)
[A] I-A: sz0 (L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6), d=3, (k,e,dd,c)=(1/2,1/10,1/10,1/6), z=6i/5-m_w, s=1/2, t=2/3, cd=1/100, Xi=1
 n=0: L=4 W=32 N=2.10e+06 lam=1.56e-02 ImM=0.8325(>=k) ImZ=0.3675(in[N^-.9,1]) T0=0.6937(>=t) g0=1.30e-02 | CaseI lam^2/L^2=1.5e-05<=1/3 | Bctl_t^cd=0.9113<=2/3:False | 1/W=3.1e-02<=2/3 | WO W^-1.4=7.8e-03<=lam:True | Bctl_t^(3/2)(1+Bctl_t^(1/6))=1.09e-06 | log((1-s)/(1-t))=0.405, cd*log(1/Bctl)=0.09 vs log W=3.5
 n=8: L=36 W=1889568 N=3.15e+23 lam=2.94e-08 ImM=0.8333(>=k) ImZ=0.3667(in[N^-.9,1]) T0=0.6944(>=t) g0=2.45e-08 | CaseI lam^2/L^2=6.7e-19<=1/3 | Bctl_t^cd=0.6554<=2/3:True | 1/W=5.3e-07<=2/3 | WO W^-1.4=1.6e-09<=lam:True | Bctl_t^(3/2)(1+Bctl_t^(1/6))=2.97e-28 | log((1-s)/(1-t))=0.405, cd*log(1/Bctl)=0.42 vs log W=14.5
 n=20: L=84 W=130691232 N=1.32e+30 lam=1.82e-10 ImM=0.8333(>=k) ImZ=0.3667(in[N^-.9,1]) T0=0.6944(>=t) g0=1.52e-10 | CaseI lam^2/L^2=4.7e-24<=1/3 | Bctl_t^cd=0.5771<=2/3:True | 1/W=7.7e-09<=2/3 | WO W^-1.4=4.3e-12<=lam:True | Bctl_t^(3/2)(1+Bctl_t^(1/6))=1.56e-36 | log((1-s)/(1-t))=0.405, cd*log(1/Bctl)=0.55 vs log W=18.7
    ConStInd(cd=1/100) at (s,t)=(1/2,2/3) holds for all n>=8 (Bctl_n=c W_n^-3 decreasing); 1/T0<=(k+1)/k=3 at all three
    STCaseII on sz0 needs 1-s<=lam^2/L^2<=1.53e-05 but T0<=0.6944 for all n (1-t>=0.3056): no merged BAFlow datum has Case II (GreenSchur_szF: lam=1/100, T0<=100/121): a Case II instance on sz0 would have a False premise
[B] I-B (STCaseII datum, not merged): L=4, W_n=n+1, lam=5, z=6i/5-m_w, (k,e,dd,c)=(1/4,1/2,1/10,1/9), s=1/10, t=1/5, cd=1/100
 ImM=0.2666>=1/4:True ImZ=0.9334<=1:True T0=0.2221>=t:True (>=k/(k+1)=0.2:True) g0=2.3566 | CaseII 1-s=0.9<=lam^2/L^2=1.5625 | WO lam=5<=10 | ConStInd cd=1/100: (1-t)/(1-s)=0.8889, holds for n>=19 | W>=N^(1/9) for n>=1
[K] T.10 at the kernel (L=4, E=0, g0, m_F=i*yF; M=BAMB); norms ||.||_(inf->inf) as `open scoped Matrix.Norms.Operator`
 I-A n=0: (a) ||U_(s,t)||=1.5000 vs (1-s)/(1-t)=1.5000; (c) max||U^(++)||=1.0000; (b) C1 needed (R=Lam' ell_s, ell_s=1, Lam'=1,2, u<=1-g0^2/L^2) = 0.333
 I-B: (a) ||U_(s,t)||=1.1250 vs (1-s)/(1-t)=1.1250; (c) max||U^(++)||=1.0262; (d) A=(k+1)/k=5: (1-s)L^2=14.4<=A g0^2=27.8, max||QU||=2.0701
[T] T.12'' at the kernel: sum_a twK = (2i W^d eta)^-1 (M-M^H)_{c2c1}, eta=(1-t)Im m, c1=0; M^*M=(M-M^*)/(2i Im m)
 I-A n=0 c2=(1, 0, 0): |Im M_c2c1|=0.00e+00; |sum K-rhs|=(7.1e-22,2.8e-23), |rhs|=(3.71e-22,3.71e-22); Theta row-sum err 4e-15
 I-A n=0 c2=(1, 1, 0): |Im M_c2c1|=3.38e-04; |sum K-rhs|=(0.0e+00,1.7e-23), |rhs|=(2.06e-08,2.06e-08); Theta row-sum err 4e-15
 I-A n=0: |m-trM/L^3|=3e-16, max|M*M-(M-M*)/(2i Im m)|=9e-16, sum_b|M_ab|^2=1.0000000000
 I-B c2=(1, 0, 0): |Im M_c2c1|=0.00e+00; |sum K-rhs|=(4.3e-19,4.3e-19), |rhs|=(1.15e-18,1.15e-18); Theta row-sum err 4e-15
 I-B c2=(1, 1, 0): |Im M_c2c1|=1.11e-01; |sum K-rhs|=(1.7e-18,4.3e-19), |rhs|=(1.74e-03,1.74e-03); Theta row-sum err 4e-15
 I-B: |m-trM/L^3|=2e-16, max|M*M-(M-M*)/(2i Im m)|=9e-16, sum_b|M_ab|^2=1.0000000000
[R] integrals (L=8, B=Bparam, eta_v=(1-v)Im m, kappa_vu=(g^2+1-v)/(g^2+1-u)); (i) ratio=int/(B_u^e log((1-s)/(1-u))/Im m)
 (i) g=1.0, 1-u=0.0156>=g^2/L^2=0.0156: drift e=2:0.767  B2 e=5/3:0.814  mart e=13/4 (kappa^2):0.680  max_v (g^2+1-v)B_v=1.127<=1+(L^2+1)/L^d=1.127
 (i) g=0.2, 1-u=0.0100>=g^2/L^2=0.0006: drift e=2:0.485  B2 e=5/3:0.590  mart e=13/4 (kappa^2):0.426  max_v (g^2+1-v)B_v=1.010<=1+(L^2+1)/L^d=1.127
 (i) g=3.0, 1-u=0.2000>=g^2/L^2=0.1406: drift e=2:0.933  B2 e=5/3:0.946  mart e=13/4 (kappa^2):0.898  max_v (g^2+1-v)B_v=1.090<=1+(L^2+1)/L^d=1.127
 (ii) g=3.0, 1-s=0.1406<=g^2/L^2=0.1406: int eta^-1 B_v^2 dv/B_u^2 * Im m=0.51 <= 4 log((1-s)/(1-u))+1/2=29.49
 (ii) g=10.0, 1-s=1.0000<=g^2/L^2=1.5625: int eta^-1 B_v^2 dv/B_u^2 * Im m=0.50 <= 4 log((1-s)/(1-u))+1/2=37.34
```
Reading: I-A (n ≥ 8): Im m ≥ κ, Im z ∈ [N^{−0.9},1], s<t ≤ T0, `STCaseI`, `STConStInd`, W⁻¹ ≤ (1−t)/(1−s), `WO`, A ≥ 1/T0 hold at once; kernel (a) is sharp (1.5000 = (1−s)/(1−t)), (b) C₁ needed 0.33. I-B: `STCaseII`, T.10(d) with A=5 (1−s)L² = 14.4 ≤ A·g0² = 27.8, ‖QŨ‖ = 2.07; T.10(c) 1.03. External limit (TEAM §8 lesson 14): none (no external hypothesis; the Step-1…4 premises `twSteps` and `BATwistLoopLaw` at s stay hypotheses as pins of other gates).

### Verdicts
- **Target 1 `baTwistGridMart_holds`: PASS.** `baTwistGridAssemble_holds d C₀ hC₀ hR tail wtail` has type `BATwistGridMartAt d C₀`; `BATwistGridMart d` needs the wrapper `⟨C₀, hC₀, ·⟩` (`TwistGrid2:223`).
- **Target 2 `baTwistZeroMode_holds`: PASS.** Corrections to the ticket: (−,+) by `BATheta_swap`; instance `c₂ = (1,1,0)`.
- **Target 3 `BATwistStepFixed`, `_caseI`, `_caseII`: PASS** with: the `≺`-at-deterministic-`Ξ` form (row 14); `𝔠d` including `1/(2d)` (row 5); ε' with the factor d (row 8); martingale by T.10(a) (row 12); TL1 at τ from `twSteps` (row 16). The `STCaseII` instance needs the new datum I-B (a `BAFlow` instance for lam≡5, about 40 lines in `TwistStep2`), not `sz0`. No FAIL, no BLOCKED. Paper-delta candidates: none (the Lean-side forms are conventions, F1 as in T2413).

## (a″) Probe compile — Mon Oct 12 06:25:04 UTC 2026
Probe `RBM3D/Probe/T2441Pins.lean`: 332 lines, commit `f459c7f` on `t/T2441`, the only file of `git diff --stat main...t/T2441`; never merged. Section (a) is not edited and no (a′) is written: the 37 file:line citations of (a) and of the ticket were re-checked by script (scratchpad `T2441/cites.py`) and agree (the 3 first-hit flags of the script are docstring mentions or a range; the declaration lines are among its hits). Findings F1, F2 change a datum and a cost estimate of (a), not a verdict.

### Compile (script `final.sh`; scratch files are in the scratchpad `T2441/`, not in the repository)
```
Mon Oct 12 06:21:24 UTC 2026
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2441 && lake env lean RBM3D/Probe/T2441Pins.lean; echo "exit=$?"
BATwistStepFixed : ℕ → ({d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) → Prop
T2441_TL2e : Prop
BATwistGridMart : ℕ → Prop
BATwistZeroMode : ℕ → Prop
baTwistGridRem_holds : ∀ (d : ℕ), ∃ C₀, 0 ≤ C₀ ∧ BATwistGridRem d C₀
baTwistGridTail_holds : ∀ (d : ℕ), BATwistGridTail d
baTwistGridWTail_holds : ∀ (d : ℕ), BATwistGridWTail d
baTwistGridAssemble_holds : BATwistGridAssemble
BATwFrame : (d : ℕ) →
  ({d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) →
    ((sz : RBM.Gauss.Sizes d) → FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → (ℕ → ℝ) → Prop) → Prop
@BATwistLoopLaw : {d : ℕ} → {sz : RBM.Gauss.Sizes d} → FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → Prop
BATwistLoopStep : ℕ → ({d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) → Prop
exit=0
$ wc -l RBM3D/Probe/T2441Pins.lean; grep -c -E "sorry|admit|native_decide|axiom" RBM3D/Probe/T2441Pins.lean; git rev-parse --short HEAD; git status --short | wc -l
     332 RBM3D/Probe/T2441Pins.lean
0
f459c7f
       0
$ git diff --stat main...t/T2441
 RBM3D/Probe/T2441Pins.lean | 332 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 332 insertions(+)
```
Also: `lake env lean docs/tickets/checks/T2441-check.lean` in the worktree: exit 0, no `error` line. `grep -c "Step2Gen_\|STthetaOpg"` on the probe: 0. Name clash: `git grep -n -e BATwistStepFixed -e baTwistStepFixed -e T2441_ -e baTwistGridMart_holds -e baTwistZeroMode_holds main -- RBM3D RBM3D.lean` (main at `483a67f`): exit 1, no match; `git log --all --oneline -- 'RBM3D/BA/TwistStep*' | wc -l`: 0.

### (vi) The pin and the interface (`sed -n '41,50p;53,54p' RBM3D/Probe/T2441Pins.lean`)
```
def BATwistStepFixed (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  BATwFrame d R fun sz C μ s t =>
    BATwistLoopLaw C μ s → ∀ Ξ : ℕ → ℝ, (∀ n, 1 ≤ Ξ n) →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖twL2' C n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 - twK C n (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2‖)
        (fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ)) →
      ∀ τ : ℕ → ℝ, (∀ n, s n ≤ τ n) → (∀ n, τ n ≤ t n) →
        PrecL sz μ (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p ω => ‖twL2' C n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK C n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
          (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n))
def T2441_TL2e : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R
```
Decisions fixed by this text (they bound 1b):
1. The shape is the ticket's: TL2 at `s`, `∀ Ξ`, the bootstrap hypothesis, `∀ τ ∈ [s,t]`, `PrecL`; one statement for all four charges (`σ : Fin 2 → Bool` is in both index types); `R` free; `3 ≤ d`, `κ ε 𝔡 Cd`, `∃ 𝔠d ≤ 1/100` come from `BATwFrame`. `Ξ` carries `1 ≤ Ξ n` for all `n` (the premise of `BATwistSrc4`).
2. Bootstrap form (1a (iii), (a) row 14): the `≺` form at a deterministic level `Ξ : ℕ → ℝ` over `TimeIcc s t n × (Fin 2 → Bool) × Zd × Zd × Zd` (the index of `twSrc`). It is on `[s,t]`, not `[s,τ]`: the premise of `baTwistSrc4_holds` ranges over `[s,t]` (`TwistPins:269-272`), so the `Src` lemmas are used at `(s,t)` and the grid pins at `t := τ`. Consequence for TL2e: the iterates `Ξ_j` are deterministic sequences (plan (vii)).
3. Real exponents `(3/2 : ℝ)`, `(1/6 : ℝ)` as in `BATwistLoopLaw`; the level is T.11 (iv) at `γ = 3/2` and the martingale of T.11 (iii) at `(p, q) = (2, 2)` (exponent `13/8 ≥ 3/2`, (a) row 1).
4. `T2441_TL2e` is for all `d` and `R`; its instance at both regimes is probe lines 290-293.

### Instances (probe lines; every one compiles; `twSteps` and TL2 at `s` are other gates' pins and stay hypotheses)
| statement | datum | discharged at the datum | lines |
|---|---|---|---|
| target 2 `BATwistZeroMode 3` | `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`, `n = 0`, `σ = (false,true)`, `c₁ = 0`, `c₂ = (1,1,0) ≠ c₁` | every hypothesis (`c₂ ≠ 0` by `Fact`; (a) [T]: rhs 2.06e-8, the ticket's `(1,0,0)` is 0 = 0) | 79-89 |
| target 3, `STCaseI` | `sz0`, `s ≡ 1/2`, `t ≡ 2/3 ≤ T0` (`t0_sz0`) | frame, `STCaseI` (`lam²/L² ≤ 1/3`), `STConStInd` (`s1Setup_conStInd_const`), the bootstrap hypothesis at `Ξ_n = 32 N_n⁴` | 91-150 |
| target 3, `STCaseII` | new `T2441_szII` (lines 57-69), `s ≡ 0`, `t ≡ 1/2000` | frame with `BAFlow` (182-234), `t ≤ T0` (235-244), `STCaseII` (`1 ≤ 25/16`), `STConStInd` (`conStInd_const`), the bootstrap hypothesis at `Ξ_n = 2(2/κ)²N_n⁴` | 152-288 |
| interface | – | `T2441_TL2e` gives `BATwistLoopStep d STCaseI ∧ … d STCaseII` | 290-293 |
| emptiness | `sz0` | no `s_n < t_n ≤ T0_n` with `STCaseII sz0 s t` (`n = 0` suffices) | 294-308 |

### Findings
- **F1 (the `STCaseII` datum of (a), I-B).** The bound of `BASelf_subord` (`MFixedPoint:215`) is `Im m_w ≥ Im w/(‖w‖² + g²L^d)`, which is 7.493256e-04 at (a)'s datum (`w = 6i/5`, `g = 5`, `L = 4`, `d = 3`; `ev.py`; 6.249839e-04 at `Im w = 1.0006` below), not its `κ = 1/4` (true numerically, (a) [B]; not provable from the merged bound). The probe's datum: `L ≡ 4`, `W_n = n + 25`, `lam ≡ 5`, `w = (5003/5000) i` (`Im w > 1` is the hypothesis of `BASelf_subord`), `z ≡ w - m_w`, `(κ, ε, 𝔠, 𝔡) = (3/5000, 1/2, 1/9, 1/10)`: `Im m ≥ 6.2498e-4 ≥ κ`, `1/1000 ≤ 5003/5000 - 5000/5003 ≤ Im z ≤ 1` against `N^{-1/2} ≤ 1/1000` (`N_0 = 10⁶`), `T0 ≥ κ/(κ+1) = 5.996e-4 ≥ t = 5e-4`. The datum and its facts cost about 100 lines (57-69, 163-253), the `BAFlow` proof 53 of them (182-234): (a) estimated about 40. Time window `[0, 1/2000]`, `κ = 3/5000`: a witness, not a physical regime (constants in `(d, κ, ε, 𝔡)`, no smallness of `g`).
- **F2 (no merged `STCaseII` datum).** `grep -rnE ": BAFlow [A-Za-z_0-9.]+ [(0-9]" RBM3D` finds two concrete theorems, `flow_sz0` (`FlowPins:1214`) and `inst_BAFlow` (`GreenSchur:542`, datum `GreenSchur_szF`, private); `sz0` has no `STCaseII` window (compiled, 294-308); for `GreenSchur_szF` ((a) [A]: `lam = 1/100`, `T0 ≤ 100/121`; with `L = 4`, `lam²/L² = 6.25e-6`) this is not re-proved here.
- **F3 (privates).** `open private … from RBM3D.BA.TwistKer2` inside `namespace RBM.BA` works for the private lemmas of `TwistKer2` and `TwistGridTail` (probe line 73, used by the instances; scratch `priv.lean` for `TwistKer2_conU`, `TwistGridTail_measurable_twL2M`; the repository does the same at `TwistGridRem2:35`, `TwistGridTail:45-55`).
- **F4 (the bootstrap hypothesis is satisfiable).** At both data `‖Z_v‖ ≤ 2η⁻²`, `η⁻¹ ≤ (2/κ)N`, `B^{3/2} ≥ N⁻²` give the hypothesis at `Ξ_n = 2(2/κ)²N⁴` for every `n` and `ω` (`ST_prec_of_le_ev`): the pin's premises are consistent at concrete data, and TL2e's first round is the a priori one.
- **F5 (stop rule, TL1 at `τ`).** Scratch `T2441/tl1.lean` (58 lines, not part of the probe): from `twSteps C μ s t Cd`, `BAFlow`, `0 ≤ s`, `t ≤ T0` and any `τ ∈ [s,t]` it derives `LWAvgLawgL C μ τ` (`twSteps.1`'s `STAvgUgL` by `StochDomAt.precomp_param`, then `𝒦^{(1)} = m` eventually by `baKsol_one`, `BAflow_real`, `BAt0_lt_one`, `StochDomAt.of_subset`) and `STLmaxgL C μ τ` (`twSteps` conjunct 2 by `precomp_param`): `lake env lean` exit 0 (this confirms (a) row 16; no premise is missing from `BATwistLoopStep`).
- Not settled by the probe: the size of the grid-walk engine (viii).

### (vii) TL2e plan (proposal; nothing of it is proved here)
1. Frame: take `𝔠d` of `BATwistStepFixed d R` at the same `(κ, ε, 𝔡, Cd)`; `R sz s t`, `STConStInd`, `twSteps`, TL2 at `s` go unchanged to the pin; no regime is used.
2. Start: the a priori level of F4, `Ξ_0 = 2(2/κ)²N⁴`. Round `j`: the pin gives, for every sequence `τ ∈ [s,t]`, `Z_τ ≺ B_τ^{3/2}(1 + B_τ^{1/6}Ξ_j)`.
3. Net S2 (design §5, TP:171; at `μ`): `H_v = g₀Ψ + √v X` (`seqHflowBA`, `Gauss/BlockAnderson:83`; `seqHflow`, `FineModel:225`), so `‖G_v - G_{v'}‖ ≤ η_t⁻²(‖X‖|√v - √v'| + |z_v - z_{v'}|)` and `K̃` is Lipschitz in `v` with an `N^C` constant: `Z_v` moves by `≤ N^{-C'}` between net points of mesh `N^{-C''}`, `P_n ≤ N^C` points.
4. Per-`τ` → `TimeIcc`: let `τ*_n` be the net point of largest bad probability (a sequence in `[s,t]`, so the pin applies to it), union bound (`measure_biUnion_finset_le`) and the Lipschitz transfer: `Z ≺ Ξ_{j+1}B_v^{3/2}` on `TimeIcc s t`, `Ξ_{j+1} = 1 + B_t^{1/6}Ξ_j` (`B` increasing in time; `≺` absorbs the constants).
5. Contraction: `B_t ≤ W^{-2𝔡} + 2N^{-ε}` ((a) rows 13-14, `lam_sq_mul_pow_ge`, `Sizes:193`) gives `B_t^{1/6} ≤ N^{-c}`; after `J = O(1/c)` rounds `Ξ_J ≤ 2` eventually (each round has its own `∀ᶠ n`).
6. `BATwistLoopStep d R` for every `R`; `STCaseI`, `STCaseII` by instantiation (probe 290-293). T.12 (`δ`, `(p,q)` with `1/(4p) + 1/(2q) ≤ δ`) and T.13 (S3: `Σ_a` of the `M`-term `≤ C_M² W^{-d}`) are the other items of design §7 row TL2e.

### (viii) Predicted lines, merged privates
```
$ python3 -I ev.py   (landed = wc -l of the merged files; central = design §7 table, DECISIONS §242 for TL2a2-4)
row    files                               landed  central  landed/central
TL0    TwistPins                              962      620     1.55
TL1a   TwistAvgA+TwistAvgA2                  2313     1036     2.23
TL2a2  TwistGridRem+TwistGridRem2            1572     1380     1.14
TL2a3  TwistGridTail+TwistGridTail2          1950      915     2.13
TL2a4  TwistGridWTail+TwistGridWTail2        3156     1150     2.74
TL2b   TwistKer+TwistKer2                    3041     1478     2.06
TL2c   TwistQV                               1429      800     1.79
ratios sorted: [1.14, 1.55, 1.79, 2.06, 2.13, 2.23, 2.74]  median 2.06
TL2d central 1250: at min/median/max ratio -> 1424 / 2572 / 3430 lines in total (two files, stop line 2000 each)
```
Estimate, not a measurement. Assumptions: total = 1,250 × ratio; the 210 instance lines (probe 79-288) are fixed and sit in `TwistStep2`; the other lines split evenly (`TwistStep`: pin, T.12″, target 1, the grid-walk engine; `TwistStep2`: regime bookkeeping, cases (A)-(C), instances). Then `TwistStep` / `TwistStep2` = 607 / 817 (minimum ratio), 1,181 / 1,391 (median), 1,610 / 1,820 (maximum). The probe predicts no file above 1,800 at the median; at the maximum ratio `TwistStep2` is at 1,820 (flag). Moving the `STCaseII` datum and its `BAFlow` proof (≈ 100 lines, probe 57-69 and 163-253) to the head of `TwistStep` (the import order `TwistStep → TwistStep2` is kept) gives 1,710 / 1,720, so 1b should place it there; a third file would go by amend (DECISIONS §242 (3)).
Merged privates (all reachable by `open private`, F3; no `private` deletion and no amend predicted). Used by the probe: `TwistKer2_Z_crude` :1321, `TwistKer2_eta_inv_le` :708, `TwistKer2_Bctl_rpow_ge` :1342, `TwistKer2_eta_pos` :127. Further candidates for 1b: `TwistKer2_eta_eq` :123, `TwistKer2_Bctl_ge_inv` :234, `TwistKer2_conU` :281 (`Bctl_u^{𝔠d} ≤ (1-u)/(1-s)` for `u ≤ t`), `TwistKer2_hermitian` :565, `TwistKer2_carrier` :580; measurability `TwistGridTail_measurable_twChg` :856, `_twL2M` :865, `_twDerM` :872, `_twEEM` :886. Absent (new in 1b, for `ST_grid_whp_of_sections` / `ST_model_le_path`, which take `Measurable` families): measurability of `twL3M`, `twEGM`, `twB1M`, `twB2M` (`grep -rl "twB1M\|twB2M\|twEGM\|twL3M" RBM3D`: only `BA/TwistGrid.lean`; `grep -rn` of the same pattern piped to `grep -ic measurab`: 0).

### Paper-delta candidate and verdict of the probe step
- `T2441a`: the paper's `Ξ̃_u = sup_{v ≤ u} max |Z_v| B_v^{-γ_*}` (TP:171) is a random variable; the Lean pin takes a deterministic level `Ξ_n` and iterates it in TL2e (equivalent after the net; an interface convention, not a statement of the paper's theorems).
- Verdict: the probe compiles (exit 0), the pin and `T2441_TL2e` elaborate, both regimes have a compiled instance with only `twSteps` and TL2 at `s` as hypotheses; no obstruction found at the statement level (the size of the grid-walk engine is the open point, (viii)); no hypothesis added to a target, no signature changed.

## (a′) Preflight corrections — Mon Oct 12 10:43:26 UTC 2026
None. Section (a) is not edited; the decisions of (a″) were followed (the `≺` form at a deterministic `Ξ` over `TimeIcc s t`; `𝔠d` with `1/(2d)`; TL1 at `τ` from `twSteps`; the martingale weight by T.10 (a)).

## (b) Script output (stage 1b, final run of `final_verify2.sh`, scratchpad `T2441/`; stop line 2,000 per file)
```
$ date -u; git rev-parse --short HEAD; git log --oneline main..t/T2441 | wc -l; git status --short | wc -l
Mon Oct 12 10:42:20 UTC 2026
bc7ebc2
      24
       0
$ lake build RBM3D.BA.TwistStep RBM3D.BA.TwistStep2 | tail -1; <warnings naming TwistStep>
Build completed successfully (4059 jobs).
0
$ [RBM3D.lean + the 2 import lines, uncommitted, restored after] lake build | tail -1; grep 'axiom audit: '
Build completed successfully (4264 jobs). exit=0 
axiom audit: 12977 theorems, 4066 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ #print axioms RBM.BA.<target> (lake env lean)
'RBM.BA.BATwistStepFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistGridMart_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistZeroMode_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistStepFixed_caseI' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistStepFixed_caseII' depends on axioms: [propext, Classical.choice, Quot.sound]
all      116 new public declarations: 116 depend on exactly [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2441-check.lean; echo exit=$?; grep -c error
exit=0
0
$ for each new public name: git grep -w <name> main -- RBM3D RBM3D.lean
names checked:      116; clashes on main (30c6d7a): 0
$ cat both files | grep -c <RBM1D|RBM2D> / <sorry|admit|native_decide|axiom decl> / <Step2Gen_|STthetaOpg>
0 0 0
$ wc -l RBM3D/BA/TwistStep.lean RBM3D/BA/TwistStep2.lean   (stop line 2000 per file)
    1795 RBM3D/BA/TwistStep.lean
    1564 RBM3D/BA/TwistStep2.lean
$ git diff --stat main...t/T2441
 RBM3D/BA/TwistStep.lean    | 1795 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistStep2.lean   | 1564 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2441Pins.lean |  332 ++++++++
 3 files changed, 3691 insertions(+)
$ diff <(pin text, probe) <(pin text, RBM3D/BA/TwistStep.lean:59-68); echo exit=$?
exit=0 (      10 lines each)
$ grep -n the targets and the instances
59:def BATwistStepFixed (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
73:theorem baTwistGridMart_holds (d : ℕ) : BATwistGridMart d := by
113:theorem baTwistZeroMode_holds (d : ℕ) : BATwistZeroMode d := by
1037:theorem baTwistStepFixed_caseI (d : ℕ) : BATwistStepFixed d STCaseI := TwistStep2_pin d STCaseI (TwistStep2_ker_caseI d)
1330:theorem baTwistStepFixed_caseII (d : ℕ) : BATwistStepFixed d STCaseII := TwistStep2_pin d STCaseII (TwistStep2_ker_caseII d)
1341:def TwistStep2_szII : Sizes 3 where
1353:theorem TwistStep2_flowII : BAFlow TwistStep2_szII (3 / 5000) (1 / 2) (1 / 9) (1 / 10) TwistStep2_zII ∧ ∀
1441:example : True := by
1449:example : ∀ d, BATwistGridMart d := baTwistGridMart_holds
1452:example :
1459:example : (![1, 1, 0] : Zd 3 (sz0.L 0)) ≠ 0 := by
1463:example : ∀ d, BATwistZeroMode d := baTwistZeroMode_holds
1467:example {Cd : ℝ} (hC : 0 < Cd)
1509:example {Cd : ℝ} (hC : 0 < Cd)
```
Narrative (every item is in the files or the output above):
- **Files.** `TwistStep.lean`: pin :59, targets 1 :73 (three lines, §242 (2)) and 2 :113 (`(−,+)` by `BATheta_swap`), grid-walk bound `TwistStep_pathreal` :1026, six events `TwistStep_events_hp` :1622, core `TwistStep_det_n` :1369, back to the model `TwistStep_model_le` :1687, F1 `TwistStep_ellT_scale` :1717, (4.18) `TwistStep_Bparam_cmp` :1732, `TwistStep_ratio_le` :1754. `TwistStep2.lean`: assembly `TwistStep2_main` :386, `TwistStep2_pin` :635 from the regime input `TwistStep2_Ker` :597, kernels `kerA` :758, `kerC` :776, `kerB` :830, zero mode `TwistStep2_zero` :1269, regimes `ker_caseI` :1015, `ker_caseII` :1312, instances from :1341.
- **Bootstrap form (1a (iii)).** As in (a) row 14 and the probe: `≺` at a deterministic `Ξ : ℕ → ℝ`, `1 ≤ Ξ n`, over `TimeIcc s t`; the merged pin text equals the probe's (diff exit 0). It reaches the grid walk by `TwistStep_grid_whp` / `TwistStep_grid_zero` (wrappers of `ST_grid_whp_of_sections`, `ST_grid_whp_zero`); `B̃₂` by `TwistStep_src4_det` (the pathwise level of `BATwistSrc4` is `N^{τ/2} Ξ_n` on the good event and the a priori `TwistStep_zcrude` level off it).
- **Case table (1a (ii)).** Grid walk: `baTwistGrid_decomp` (clause (i)), `TwistStep_identity`/`_bound`/`_pathreal` (Abel summation, decision 4 by `TwistStep_theta_diff`), pins `baTwistGridRem_holds` and `baTwistGridWTail_holds` in `TwistStep2_main`; sources `baTwistSrc1..5_holds` in `TwistStep2_pin` (`𝔠d` = min of their five constants and `1/(2d)`, `st5_conStInd_mono`). (A) `σ₁ = σ₂`: `kerA` ← `baEKSameRow_holds`, used in both regimes. (B) `σ₁ ≠ σ₂`, `STCaseI`: `kerB` ← `baTwKerFar_holds` at `ε = 2ε'` (support: `zdistD_le_mul_zdistInf`, F1; `W⁻¹ ≤ (1−u)/(1−v)` from `STConStInd`, `d·𝔠d < 1`, `TwistStep2_Bctl_ge_W`; loss factor by `TwistStep_ratio_le`). (C) `σ₁ ≠ σ₂`, `STCaseII`: `kerC` ← `baTwKerZero_holds` at `A = (κ+1)/κ` for `Q = projMat`, and the zero mode: `TwistStep2_zero_sum` (`twWard_holds` at `G = Gres H ζ` and `baTwistZeroMode_holds`, the `M`-parts cancel), TL1 at `τ` (`TwistStep2_tl1`, `baTwistAvgProd_holds` from the parts `twSteps.1.2.1`, `twSteps.2.1`), `TwistStep2_zero_pt`.
- **Instances** (lines in the output): targets 1, 2 at `sz0`, `zSeq`, `flow_sz0`; target 3 at `STCaseI` on `sz0` (`s ≡ 1/2`, `t ≡ 2/3`) and at `STCaseII` on the new datum `TwistStep2_szII` (`TwistStep2_flowII`; `sz0` has no `STCaseII` window, `TwistStep2_no_caseII_sz0`), bootstrap hypothesis at `Ξ_n = 2(2/κ)²N_n⁴` (`TwistStep_zcrude`). `twSteps` and TL2 at `s` are hypotheses of the two examples (other gates' pins); everything else is discharged.
- **Audit finding.** The full build with the two root imports first failed the premise scan of `Test/Axioms.lean` on `TwistStep_Good` (a public `Prop` assumed by `TwistStep_det_n`, proved by no theorem) and `twSteps` (explicit hypothesis of two lemmas). Fixed in the files: `TwistStep_Good` is `private`; `TwistStep2_tl1`, `TwistStep2_zero` take the two parts of `twSteps` they use. No registry line added (ticket: Registry none). `RBM3D.lean` is not edited (the hub adds the two imports at merge); the full build above had them added temporarily.
- **Merged privates opened** by `open private` (all reachable, no `private` deletion, §153 (1), no amend): `TwistKer2_{Bctl_ge_inv, Wd_Ld_le, conU, eta_inv_le, Z_crude, Bctl_rpow_ge, hermitian, carrier}`, `TwistGridTail_measurable_{twChg, twL2M, twEEM}`, `TwistQV_cs_{weighted, diag}`, `TwistGrid_uKer_comm`, `TwistKer_Gres_{sub, conjTranspose}`, `TwistPins_sum_twist`, `TwistChain_{Off, trP_offset}`.
- **Size.** 3,359 lines in all against the central 1,250 (ratio 2.69): above the probe's median prediction (2,572), below its maximum-ratio one (3,430); both files are below the stop line.

## (c) Verified Mathlib names
`#check` in the final file context, 0 errors: `Finset.measurable_sup'`, `Finset.lt_sup'_iff`, `Finset.sup'_apply`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_le_one`, `Real.rpow_le_rpow_of_exponent_ge`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_inv_le_iff_of_pos`, `Real.inv_rpow`, `Real.mul_rpow`, `Real.one_le_rpow`, `div_le_div₀`, `inv_anti₀`, `mul_max_of_nonneg`, `one_le_mul_of_one_le_of_one_le`, `Complex.sub_conj`, `Complex.norm_conj`, `Matrix.linfty_opNorm_mulVec`, `Matrix.mulVec_mulVec`. Absent (checked): `Finset.measurable_sup'_apply`, `Real.sqrt_le_self`. In this Mathlib `add_le_add_right h` adds the constant on the left (`c + a ≤ c + b`).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: only `T2441a` of (a″) (deterministic `Ξ_n` instead of the random `Ξ̃_u` of TP:171); no other Lean/paper difference found.
- For TL2e (plan (vii) of (a″) unchanged): `T2441_TL2e` is in the probe only; the net (S2), the iteration of `Ξ_j` from the a priori level and `BATwistLoopStep` remain TL2e's.
- The `STCaseII` instance datum is a witness (`κ = 3/5000`, window `[0, 1/2000]`), not a physical regime ((a″) F1, F2); the straddling case (footnote 6) is in no TL row.
