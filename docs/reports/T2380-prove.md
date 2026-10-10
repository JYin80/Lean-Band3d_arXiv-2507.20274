Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 11:05:51 UTC 2026

Read at main 442d3aa (worktree T2380 = 442d3aa). No Lean written, no `lake` run. Scripts (not in the repository): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2380` (`conn.py`, `term.py`, `decay.py`, `pure.py`, `inst3d.py`; mirrors `mirror.py`, `mgraph.py`, `kode.py`, `k6.py` copied from T2376/T2374, which mirror `KCactus.lean`, `KLTree.lean`, `KLSumZeroWard.lean`). Notation: `M = BAMsigma d L (BAMB d L g E m)`, `Θ^{ss'} = BAThetaOf M t s s'`, `|x|` = `zdistD`, `D(δ) = KLmaxDist`, `slots 𝒮 = BAslot F` (`N = n+2|F|`, `BAslot_card`), edges `ℰ = ↥F ⊕ 𝒮` (`E = n+3|F|`: `|F|` chords `tΘ^{σ_iσ_j}`, `N` `M`-edges), `T(β) = Σ_{e∈ℰ} |β(c e) − β(q e)|` for `β : 𝒮 → Z_L^d`. `(Λ,κ)` as in `BAPropM`, `BAProp5s`; all constants below depend on `(d,Λ,κ)` (and `n`) only.

### (i) Statements (fixed here), exponent and constant table
| Lean name (namespace `RBM.BA`) | statement (mathematics) | consumers |
|---|---|---|
| defs `baPureB d Λ κ`, `baPureRate d Λ κ`; `baPure_edge` | `B = max(max(1, c₀⁻¹), C₅(1+Λ²))`, `r = min(min(c₀, log 2), c_s)`, `c₀ = BAct_rate d Λ κ`, `C₅ = BAp5s_C d Λ κ`, `c_s = BAp5s_rate d Λ κ` (`B ≥ 1`, `r > 0`). `3≤d, 0<Λ, 0<κ, 3≤L, 0<g≤Λ, BAReal d L g κ E m, 0≤t≤1 ⊢` (a) `‖M σ x y‖ ≤ B e^{−r|x−y|}` ∀σ,x,y (`Mbound_AO`/`Mbound_AO2`: branch `g<(2C_M)⁻¹`: `(C_M g)^k ≤ 2^{−k}`; else `c₀⁻¹e^{−c₀k}`; `M(−)=Mᴴ`); (b) `‖Θ^{ss}_{xy}‖ ≤ B e^{−r|x−y|}` and (c) `‖(t:ℂ)·Θ^{ss}_{xy}‖ ≤ B e^{−r|x−y|}` ∀s,x,y (`(prop:ThfadC_short)`: `‖Θ_{0a}‖ ≤ C₅(1_{a=0} + g²e^{−c_s|a|}) ≤ C₅(1+Λ²)e^{−c_s|a|}`, translation `x↦x+c` as `BAMsigma_shift`) | K07 §3–§5; K08b (entries) |
| `baSlot_path_le` | `KLIsTSP F, 2≤n ⊢ ∀β ∀s: |β s − β r₀| ≤ T(β)`, `r₀` = leaf slot `n−1` (node = root, `KLleafPar_root`); corollary `|β s − β t| ≤ 2T(β)` | K07 §3; K08b (weighted and `g²` sums) |
| `baSigmaTree_bound` (core, `hprod` interface as band `KLMolecule_tree_bound`, `KLMolecule.lean:209`) | `KLIsTSP F, 2≤n, d=k+2, 0<r, Γ≥0`, `hprod: ∀β consistent with δ (β(leaf v)=δ_v): ∏_e ‖E_e(β c e, β q e)‖ ≤ Γ e^{−rT(β)}` `⊢ ∀i,j: ‖BASigmaTree d L M t F σ δ‖ ≤ Γ · S₀^{N₀} · e^{−(r/4)|δ_i−δ_j|}`, `N₀ = n+2n²`, `S₀ = expC (d−2) (r/(4N₀))`; corollary with entrywise hypotheses (a),(c): `Γ = B^{E₀}`, `E₀ = n+3n²` | K07 §4; K08b (`Γ` with a `g²` factor) |
| `baSigmaPi_empty_bound` | same hypotheses on `M`, chords of `F ∈ KLTSPlong n σ ∅` short: `‖BASigmaPi d L n M t σ ∅ δ‖ ≤ \|TSP n\| · B^{E₀} S₀^{N₀} e^{−(r/4) D(δ)}` (every σ: `KLMolecule_same_charge`) | K08b |
| **`baSig_decay`** | `3≤d, 3≤n, 0<Λ, 0<κ`, ∀i: `3≤L i, 0<g i≤Λ, BAReal d (L i) (g i) κ (E i) (m i), 0≤t i≤1 ⊢ SigDecayAbs d n L (BASig d n L g E m t)` (`C = \|TSP n\|B^{E₀}S₀^{N₀}`, `c = r/4`; **every σ**, as `SigDecayAbs` demands; alternating is a special case) | K09b (`indStepAbs_of`, `KLIndStepA.lean:1050`), K08b |
| `baK_pure_eq`, **`baPure_loop`** | `3≤d, 3≤n, 0<Λ, 0<κ ⊢ ∃C>0 ∃c>0 ∀L≥3 ∀W ∀g∈(0,Λ] ∀E m, BAReal d L g κ E m, ∀t∈[0,1), ∀σ₀ ∀a: ‖BAKsol d L W M (PropSpin m) t (KLloopOf d L (const σ₀) a)‖ ≤ C · ((W:ℝ)^d)⁻¹^(n−1) · e^{−c D(a)}`; `baK_pure_eq`: for constant σ, `KLTSPlong n σ π = ∅` for `π≠∅`, so `K^{(n)} = (W^d)^{−(n−1)} K^{(∅)}` and `K^{(∅)}(a) = Σ_δ Σ^{(∅)}(δ) ∏_v Θ^{σ₀σ₀}(a_v,δ_v)` (`baK_eq_sum_Kpi`, `baKpi_eq_sum_SigmaPi`); `c = r/4`, `C = C_Σ (B S')^n`, `S' = expC (d−2) (r/2)`. No `W≥1`: `0⁻¹=0` | K12 (`BAKBoundAt`, pure σ), K08 |

Not targets: the `g²`-gain (`KLMolecule_selfW_bound_nc`) and `(D+1)^Q`-weighted slice sums are K08b; the core `hprod` interface lets K08b reuse the tree bound.

| quantity | value (instance below; `(d,Λ,κ)=(3,10,0.6814)`, `n=3,4`) | constraint | slack |
|---|---|---|---|
| `d`, `n` | 3; 3, 4 | `3≤d` (`BAPropM`, `BAProp5s`); `3≤n` (`baK_eq_sum_Kpi`), `2≤n` (path, cut lemmas) | 0; 0, 1 |
| `g, t` | `g=0.5`, `t=0.5` | `0<g≤Λ`; edges `0≤t≤1` (`baProp5s_of_real`), pure loop `t<1` (`baTreeRep`) | `g/Λ=0.05`; `1−t=0.5` |
| `C_M = 16d²/κ³` | 455.1 | branch `g<(2C_M)⁻¹ = 0.0011` or large | `g` is `455×` above: large branch |
| `c₀ = min(log(1+κ/(4dΛ)), κ/2)` | 5.662e-3 | `>0` | `log 2/c₀ = 122` |
| `B_M`, `r_M = min(c₀, log 2)` | 176.6; 5.662e-3 | `B_M≥1` | `≥ 1` |
| `A = 4(C_M/c₀)²`, `S_s = expC(d−2, c₀)`, `ε = κ²/4` | 2.58e10; 5.98e12; 0.1161 | `BAp5s_A, _S`, `BAoffDiag_scalar` | — |
| `c_s`, `C₅` | 2.47e-30; 1.98e26 | `>0` | observed `\|M\|` rate (`\|x−y\|` 1→4): 0.314 |
| `B_Θ = C₅(1+Λ²)`, `B` | 2.0e28 (`log10` 28.3); 2.0e28 | `B≥1`; entries `≤ B e^{−r\|x−y\|}` | observed `max\|entry\|e^{r\|x−y\|}/B = 3.5e-29` (output below) |
| `r = min(r_M, c_s)` | 2.47e-30 | `r>0` | positivity only is used downstream |
| `N₀ = n+2n²`, `E₀ = n+3n²` | 21, 30; 36, 52 | `N≤N₀`, `E≤E₀` (`\|F\| ≤ n²`) | true `max\|F\|=n−3`: `N=3,6`, `E=3,7` (`conn.py`) |
| `λ = r/(4N₀)`, `S₀ = expC(d−2, λ)` | `λ=2.9e-32`, `1.7e-32` | `2N₀λ·T ≤ (r/2)T` | 0 at `N=N₀` |
| `c = r/4` | 6.2e-31 | `r T ≥ (r/4)D + Σ_sλ\|δ_i−b_s\|`: factor 2 from `\|β s−β t\|≤2T`, factor 2 from the sum | observed `c ≥ 0.26` (decay.py), claimed `r_e/4 ≤ 0.164` |
| `C_Σ = \|TSP n\|B^{E₀}S₀^{N₀}` | `log10`: 3577 (n=3), 6183 (n=4) | finite | observed `C_obs = 0.33, 0.18` |
| `c_K = c`, `C_K = C_Σ(B S')^n` | `log10`: 4032 (n=3), 6790 (n=4); `W^{−d(n−1)} = 1.56e-2, 1.95e-3` at `W=2` | `r−c ≥ r/2` for `S'` | — |
The constants are explicit and finite but astronomically weak at `Λ=10` (`BAp5s_rate` = 2.5e-30, merged); consumers use only `∃C,c>0`, no hypothesis depends on them.

### (ii) One concrete nondegenerate instance, and the binding numerics
**Hypotheses** of all targets at once: `(d,L)=(3,4)`, `N=64`, `Λ=10`, `g=1/2` (`P.g0 ≤ 10` in Lean), `E=0.3`, `m` solving `BASelf` with `κ=Im m>0`, `t=1/2`, `W=2`, `n∈{3,4}`; no external hypothesis, so no limit computation owed (the `g²`/sum-zero clauses are K08). Lean (1b): flow point `P` of `(d,L)=(3,4)` (`MFixedPoint.lean:893`, `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`), `ι=Unit`, `L=4`, `t=1/2`, `n=3,4`: `baPure_edge` at entries `(0,(1,0,0))`; `baSigmaTree_bound` for `F=∅` (`n=3`) and `F={(0,2)}` (`n=4`, `σ=(+,+,+,+)` and `(+,+,−,+)`, labels distinct); `baSig_decay` (`SigDecayAbs 3 n (fun _ => 4) (BASig …)`); `baPure_loop` at `σ₀=+`, `W=2`, `a` of `n` distinct labels. `P` is a choice, so the script uses `g=1/2, E=0.3` (same `BAReal` shape), as T2376.
`cd $S; python3 inst3d.py` (tolerance: identities `≤1e-12`, inequalities exact):
```
hypotheses: d=3>=3, L=4>=3, N=64, 0<g=0.5<=Lambda=10, t=0.5 in [0,1), W=2, kappa:=Im m=0.681403>0, BASelf residual 2.3e-16, |m|=0.6881<=1; n in {3,4}>=3
C_M=16d^2/kappa^3=455.1, (2C_M)^-1=0.0011 <= g=0.5: large branch; c_M=min(log(1+kappa/(4 d Lambda)),kappa/2)=0.005662; A=4(C/c)^2=2.58e+10; S_s=expC(d-2,c_M)=5.98e+12; eps=kappa^2/4=0.1161
rate_s=min(c_M, eps^2 c_M/(2 A Lambda^2 S_s))=2.47e-30; C_5=1.98e+26; B_M=max(1,1/c_M)=176.6, r_M=min(c_M,log2)=0.005662; B_Theta=C_5(1+Lambda^2)=2e+28; B=2e+28 (log10 28.3), r=min(r_M,rate_s)=2.47e-30
edge bounds (a),(b),(c) at the data: max |entry| e^{r|x-y|} / B = {'M+': '3.45e-29', 'M-': '3.45e-29', 'tTh++': '2.04e-29', 'tTh--': '2.04e-29', 'Th++': '4.08e-29', 'Th--': '4.08e-29'} (<= 1 required)
observed |M+| profile by |x-y|_L: 6.88e-01 1.74e-01 9.13e-02 5.49e-02 6.77e-02 6.19e-02 2.61e-01 ; observed rate (|x-y| 1->4): 0.314  vs r = 2.47e-30
observed |t Th++| profile: 4.07e-01 4.82e-03 1.16e-03 3.31e-04 5.86e-04 4.07e-04 1.12e-02
Sigma^(0), n=3, sigma=+++ (pure +), |TSP|=1, 15 delta: nonzero 15/15, max|Sigma|=3.26e-01; C_obs at claimed c=r/4: 3.26e-01; log10 claimed C = 3577; sample D=0:3.3e-01 D=2:2.8e-03 D=4:2.0e-04 D=4:6.5e-04 D=5:3.1e-04
Sigma^(0), n=3, sigma=+-+ (alternating), |TSP|=1, 15 delta: nonzero 15/15, max|Sigma|=3.26e-01; C_obs at claimed c=r/4: 3.26e-01; log10 claimed C = 3577; sample D=0:3.3e-01 D=3:2.8e-04 D=4:3.1e-04 D=4:5.6e-04 D=5:3.1e-04
first stage n=3, a=(5, 23, 25): K^(0)(a) = 8.400090e-05-1.252616e-04j; sum_delta Sigma prod Theta = 8.400090e-05-1.252616e-04j; diff 2.5e-18
pure loop K^(0)(a), sigma=+++, n=3, 9 labels a: max|K|=1.33e-03, nonzero 9/9, C_obs at claimed c_K=r/4: 1.33e-03; log10 claimed C_K=4032; W^(-d(n-1)) = 1.562e-02
Sigma^(0), n=4, sigma=++++ (pure +), |TSP|=3, 15 delta: nonzero 15/15, max|Sigma|=1.40e-01; C_obs at claimed c=r/4: 1.40e-01; log10 claimed C = 6183; sample D=0:1.4e-01 D=4:4.0e-05 D=4:5.9e-05 D=4:6.4e-05 D=5:4.1e-05
Sigma^(0), n=4, sigma=+-+- (alternating), |TSP|=3, 15 delta: nonzero 15/15, max|Sigma|=1.39e-01; C_obs at claimed c=r/4: 1.39e-01; log10 claimed C = 6183; sample D=0:1.4e-01 D=3:2.3e-05 D=4:2.8e-05 D=4:8.6e-05 D=5:5.8e-05
Sigma^(0), n=4, sigma=++-+ (chord (0,2) long), |TSP|=3, 15 delta: nonzero 15/15, max|Sigma|=1.82e-01; C_obs at claimed c=r/4: 1.82e-01; log10 claimed C = 6183; sample D=0:1.8e-01 D=4:7.5e-06 D=4:5.2e-05 D=5:1.0e-05 D=5:2.1e-05
pure loop K^(0)(a), sigma=++++, n=4, 9 labels a: max|K|=5.32e-04, nonzero 9/9, C_obs at claimed c_K=r/4: 5.32e-04; log10 claimed C_K=6790; W^(-d(n-1)) = 1.953e-03
```
**Binding numerics, `n=3..6`, no ODE** (Σ and `K` are the full arrays over all `δ`, resp. `a`, on `Z_q`, the `d=1` circulant mirror of T2374/T2376; data BA-A `(g,E,t)=(.5,.3,.7)`, BA-B `(1.1,0,.6)`; `r_e` = 0.9 × tail rate of the slowest edge family fitted on `Z_80`, `B_obs` = max over the `Z_q` entries of `\|entry\|e^{r_e x}`; claimed `c = r_e/4`; `C_obs(c) = max_δ \|Σ\| e^{c D(δ)}`; `slope_obs` = regression slope of `log max_{D(δ)=k}\|Σ\|`, `k≥1`). `cd $S; python3 decay.py`:
```
BA-A n=3 q=24 (g,E,t)=(0.5,0.3,0.7) Im m=0.785 | edge rate r_e=0.9*tail=0.655 B_obs=1.35 | claimed c=r_e/4=0.164, log10 C=55 | #sigma=8: max C_obs(c)=4.92e-01 [+-+], min slope_obs=1.41 [++-], pure C_obs=4.92e-01 slope=1.41
BA-A n=4 q=16 (g,E,t)=(0.5,0.3,0.7) Im m=0.785 | edge rate r_e=0.9*tail=0.655 B_obs=1.35 | claimed c=r_e/4=0.164, log10 C=102 | #sigma=16: max C_obs(c)=3.88e-01 [++--], min slope_obs=1.34 [++--], pure C_obs=1.51e-01 slope=1.36, alternating C_obs=1.44e-01 slope=1.36
BA-A n=5 q=12 (g,E,t)=(0.5,0.3,0.7) Im m=0.785 | edge rate r_e=0.9*tail=0.655 B_obs=1.35 | claimed c=r_e/4=0.164, log10 C=167 | #sigma=3: max C_obs(c)=6.43e-02 [+-+-+], min slope_obs=1.25 [+++++], pure C_obs=4.47e-02 slope=1.25
BA-A n=6 q=12 (g,E,t)=(0.5,0.3,0.7) Im m=0.785 | edge rate r_e=0.9*tail=0.655 B_obs=1.35 | claimed c=r_e/4=0.164, log10 C=249 | #sigma=3: max C_obs(c)=5.29e-02 [++++++], min slope_obs=1.21 [+-+-+-], pure C_obs=5.29e-02 slope=1.21, alternating C_obs=2.36e-02 slope=1.21
BA-B n=3 q=24 (g,E,t)=(1.1,0.0,0.6) Im m=0.452 | edge rate r_e=0.9*tail=0.182 B_obs=1.00 | claimed c=r_e/4=0.045, log10 C=62 | #sigma=8: max C_obs(c)=9.23e-02 [+++], min slope_obs=0.36 [++-], pure C_obs=9.23e-02 slope=0.36
BA-B n=4 q=16 (g,E,t)=(1.1,0.0,0.6) Im m=0.474 | edge rate r_e=0.9*tail=0.182 B_obs=1.00 | claimed c=r_e/4=0.045, log10 C=116 | #sigma=16: max C_obs(c)=5.06e-02 [++--], min slope_obs=0.26 [+--+], pure C_obs=2.86e-02 slope=0.30, alternating C_obs=2.86e-02 slope=0.30
BA-B n=5 q=12 (g,E,t)=(1.1,0.0,0.6) Im m=0.505 | edge rate r_e=0.9*tail=0.182 B_obs=1.00 | claimed c=r_e/4=0.045, log10 C=187 | #sigma=3: max C_obs(c)=1.68e-02 [+-+-+], min slope_obs=0.27 [+++++], pure C_obs=1.48e-02 slope=0.27
BA-B n=6 q=12 (g,E,t)=(1.1,0.0,0.6) Im m=0.505 | edge rate r_e=0.9*tail=0.182 B_obs=1.00 | claimed c=r_e/4=0.045, log10 C=277 | #sigma=3: max C_obs(c)=9.54e-03 [++++++], min slope_obs=0.28 [+-+---], pure C_obs=9.54e-03 slope=0.31, alternating C_obs=8.05e-03 slope=0.29
```
Pure loops, `σ=(+,…,+)`, `K^{(∅)}(a)`: `cd $S; python3 pure.py` (`first-stage err` = `max|K − Σ_δ Σ^{(∅)} ∏Θ|`; `layers π≠∅` = nonempty layers of `KLTSPlong`):
```
BA-A n=3 q=24 sigma=+++ layers pi!=empty (nonempty): [] |TSP|=1 first-stage err=1.4e-16 max|K|=1.6e-01 | claimed c_K=r_e/4=0.164 log10C_K=57 | C_obs(c_K)=1.60e-01 slope_obs=1.51 | max|K| by D<=5: 0:2e-01 1:3e-02 2:6e-03 3:9e-04 4:2e-04 5:3e-05
BA-A n=4 q=16 sigma=++++ layers pi!=empty (nonempty): [] |TSP|=3 first-stage err=7.0e-17 max|K|=3.4e-02 | claimed c_K=r_e/4=0.164 log10C_K=106 | C_obs(c_K)=3.41e-02 slope_obs=1.43 | max|K| by D<=5: 0:3e-02 1:2e-02 2:3e-03 3:5e-04 4:8e-05 5:1e-05
BA-A n=5 q=12 sigma=+++++ layers pi!=empty (nonempty): [] |TSP|=11 first-stage err=3.5e-17 max|K|=8.2e-03 | claimed c_K=r_e/4=0.164 log10C_K=172 | C_obs(c_K)=8.22e-03 slope_obs=1.23 | max|K| by D<=5: 0:8e-03 1:6e-03 2:1e-03 3:2e-04 4:6e-05 5:2e-05
BA-A n=6 q=12 sigma=++++++ layers pi!=empty (nonempty): [] |TSP|=45 first-stage err=6.4e-17 max|K|=5.8e-03 | claimed c_K=r_e/4=0.164 log10C_K=254 | C_obs(c_K)=5.76e-03 slope_obs=1.15 | max|K| by D<=5: 0:6e-03 1:2e-03 2:7e-04 3:1e-04 4:3e-05 5:1e-05
BA-B n=3 q=24 sigma=+++ layers pi!=empty (nonempty): [] |TSP|=1 first-stage err=5.6e-17 max|K|=4.1e-02 | claimed c_K=r_e/4=0.045 log10C_K=66 | C_obs(c_K)=4.11e-02 slope_obs=0.38 | max|K| by D<=5: 0:4e-02 1:4e-02 2:3e-02 3:2e-02 4:1e-02 5:5e-03
BA-B n=4 q=16 sigma=++++ layers pi!=empty (nonempty): [] |TSP|=3 first-stage err=2.4e-17 max|K|=1.8e-02 | claimed c_K=r_e/4=0.045 log10C_K=121 | C_obs(c_K)=1.93e-02 slope_obs=0.33 | max|K| by D<=5: 0:7e-03 1:2e-02 2:2e-02 3:9e-03 4:6e-03 5:4e-03
BA-B n=5 q=12 sigma=+++++ layers pi!=empty (nonempty): [] |TSP|=11 first-stage err=1.0e-17 max|K|=8.1e-03 | claimed c_K=r_e/4=0.045 log10C_K=194 | C_obs(c_K)=8.44e-03 slope_obs=0.32 | max|K| by D<=5: 0:1e-03 1:8e-03 2:7e-03 3:4e-03 4:3e-03 5:2e-03
BA-B n=6 q=12 sigma=++++++ layers pi!=empty (nonempty): [] |TSP|=45 first-stage err=8.7e-18 max|K|=4.3e-03 | claimed c_K=r_e/4=0.045 log10C_K=285 | C_obs(c_K)=4.52e-03 slope_obs=0.36 | max|K| by D<=5: 0:2e-03 1:4e-03 2:3e-03 3:2e-03 4:1e-03 5:1e-03
```
Observed `slope_obs` ≥ claimed `c` in all 16 rows (0.26 ≥ 0.045, 1.21 ≥ 0.164); `C_obs` ≤ 0.49 against `log10` claimed `C` of 55..285: no prefactor or rate is contradicted; the claimed `C` is a proof artifact (`B^{E₀}S₀^{N₀}`). Slot graph and termwise chain: `cd $S; python3 conn.py` (connected: 1 component for all `F∈TSP n`, `n=3..8`; controls, max over `F`: `M`-edges alone leave up to `n−2` components, chords alone up to `2n−3`), `python3 term.py` (`(1)` `∏‖E_e‖ ≤ B^E e^{−rT}`, `(2)` `\|b_s−b_{r₀}\| ≤ T`, `D(δ) ≤ 2T`, `(3)` `e^{−rT} ≤ e^{−(r/4)D}∏_s e^{−λ\|δ_0−b_s\|}`, relative tol 1e-12):
```
n  |TSP|  max|F|  slots=n+2|F|  edges=n+3|F| (all F)  components(chords+M)  comp(M only, max over F)  comp(chords only, max over F)  min(T-maxdist) over 200 random beta
3 1 0 True max components 1 1 3 min T-D = 2  n-3 = 0  n^2 = 9
4 3 1 True max components 1 2 5 min T-D = 4  n-3 = 1  n^2 = 16
5 11 2 True max components 1 3 7 min T-D = 10  n-3 = 2  n^2 = 25
6 45 3 True max components 1 4 9 min T-D = 11  n-3 = 3  n^2 = 36
7 197 4 True max components 1 5 11 min T-D = 22  n-3 = 4  n^2 = 49
8 903 5 True max components 1 6 13 -  n-3 = 5  n^2 = 64
data Z_12 g=0.5 E=0.3 t=0.7: r=0.6551, B=1.3528
n=3: 1800 random (sigma, F in TSP, delta, b) cases; violations of (1),(2),(3): 0; max term/(B^E e^(-rT)) = 3.25e-01 (<=1); max e^(-rT)B^E/(RHS of (3)) = 1.00e+00 (<=1); min(T - max_s|b_s-b_r0|) = 0; root node of leaf n-1 for all F: True
n=4: 4200 random (sigma, F in TSP, delta, b) cases; violations of (1),(2),(3): 0; max term/(B^E e^(-rT)) = 1.89e-01 (<=1); max e^(-rT)B^E/(RHS of (3)) = 1.00e+00 (<=1); min(T - max_s|b_s-b_r0|) = 0; root node of leaf n-1 for all F: True
n=5: 8400 random (sigma, F in TSP, delta, b) cases; violations of (1),(2),(3): 0; max term/(B^E e^(-rT)) = 9.52e-02 (<=1); max e^(-rT)B^E/(RHS of (3)) = 3.20e-01 (<=1); min(T - max_s|b_s-b_r0|) = 1; root node of leaf n-1 for all F: True
n=6: 20100 random (sigma, F in TSP, delta, b) cases; violations of (1),(2),(3): 0; max term/(B^E e^(-rT)) = 6.66e-02 (<=1); max e^(-rT)B^E/(RHS of (3)) = 8.63e-02 (<=1); min(T - max_s|b_s-b_r0|) = 3; root node of leaf n-1 for all F: True
```
No indexing failure, no false identity or bound: no pin repair, no REQ.

### (iii) The written argument
**Edge bounds.** `(a)`: `BAPropM3_of_real` (`CombesThomas.lean:539`) gives `‖BAMB_{xy}‖ ≤ (C_M g)^{|x−y|}` for `g<(2C_M)⁻¹` (then `≤ 2^{−|x−y|}`) and `≤ c₀⁻¹e^{−c₀|x−y|}` otherwise; `M(−)=Mᴴ` has entries of the same modulus at `|y−x|=|x−y|`. `(b),(c)`: `baProp5s_of_real` (`Prop5Short.lean:608`, `t≤1`) bounds `Θ^{ss}_{0a}`; `Θ^{ss}_{xy}=Θ^{ss}_{0,y−x}` (a private copy of `KMolecule_theta_perm` with `e=x↦x+c`); `1_{a=0}≤e^{−c_s|a|}`, `g²≤Λ²`, `|t|≤1`.
**Reduction (the spanning tree), per `F` with `KLIsTSP F`, `2≤n`.** `BASigmaTree = Σ_{b:𝒮→Z_L^d} ∏_v 1[δ_v=b(leaf v)] ∏_{e∈ℰ} E_e(b c e, b q e)`. (P) `|β s − β r₀| ≤ T(β)`: within a node the `M`-edges form one cycle (`BAnextSlot_orbit`, `BAnextSlot_injective`): along the orbit from `s` to `t` with minimal exponent `k` the `k` edges are distinct, so `|β s−β t| ≤ Σ_{s'∈node}|β s'−β(next s')|`. Induct on the number of chords above the node `ν` (`KLMolecule_anc_step`, `KLMolecule.lean:86`): for `ν≠root`, `ν=J∈F`, `s` in `ν`: `|β s−β(in J)|` ≤ cycle sum of `ν`, `|β(in J)−β(out J)|` is the edge of `J`, `out J` lies in `KLnodePar F ν`; define `U(ν)` = (`M`-edges of nodes `μ ≥ ν`) + (chords `J' ≥ ν`); `U(ν) ≥ U(par ν) + cycle(ν) + chord(ν)` (the three index sets are disjoint, `¬KLArcLe (par ν) ν`), and `U ≤ T`. The paths used form a spanning tree rooted at `r₀`; all edges stay in the product. For consistent `β` (`β(leaf v)=δ_v`): `hprod` gives `∏‖E_e‖ ≤ Γe^{−rT}`; `T ≥ |δ_i−δ_j|/2`, `T ≥ |δ_i−β s|/2` (2T from the reference slot), so with `λ=r/(4N₀)`: `e^{−rT} ≤ e^{−(r/4)D}·e^{−(r/2)T}` and `(r/2)T ≥ 2N₀λT ≥ Σ_sλ|δ_i−β s|` (`N≤N₀`), i.e. `≤ e^{−(r/4)|δ_i−δ_j|}∏_s g(β s)`, `g(y)=e^{−λ|δ_i−y|}`. Summing over `b` (`Finset.prod_univ_sum`) `Σ_b∏_s g(b s) = (Σ_y g)^N ≤ S₀^{N₀}` (`sum_exp_decay_centre`, `PureLoop.lean:144`; `S₀≥1`). Inconsistent `b` contribute 0. Count: `N=n+2|F|` slots, `E=n+3|F|` edges per molecule, `|F| ≤ n²` (`card_le_univ`).
**Molecule.** `F∈KLTSPlong n σ ∅` has `σ_i=σ_j` on every chord (`KLMolecule_same_charge`), so `(c)` applies, `M`-edges any charge; sum over `≤ |TSP n|` trees. `baSig_decay` instantiates with the family hypotheses (∀i), constants independent of `i`.
**Pure loops.** `K^{(n)} = (W^d)^{−(n−1)} Σ_π K^{(π)}`; constant `σ` has `F_long=∅` for every `F`, so only `π=∅` (script: no nonempty layer). `K^{(∅)}(a)=Σ_δ Σ(δ)∏_vΘ^{σ₀σ₀}_{a_vδ_v}`; with `i,j` realising `D(a)` (`KLMolecule_exists_pair`): `D(δ) ≥ |a_i−a_j| − |a_i−δ_i| − |a_j−δ_j|`, so `e^{−cD(δ)} ≤ e^{−cD(a)}∏_v e^{c|a_v−δ_v|}`; with `c=r/4` and `‖Θ_{a_vδ_v}‖ ≤ B e^{−r|·|}`, each `Σ_{δ_v} B e^{−(3r/4)|a_v−δ_v|} ≤ B S'`. This is the paper's `A:654` (only `M`-edges and short edges), through the first stage and the molecule.

### (iv) Plan against the stop line `2000` (`wc -l RBM3D/BA/KPure.lean` at each section commit; estimate lo 1000 / central 1250 / hi 1700; ticket 750/1000/1700)
§0 header, imports (`BA.KMolecule, BA.CombesThomas, BA.Prop5Short, BA.KKernel, Loop.PureLoop, Loop.KLIndStepA`), `private` copies (`KPure_theta_shift`, `KPure_zdistD_tri`, `KPure_card_le`, `KPure_anc_step` from `KLMolecule.lean:86`): 60. §1 constants, entries, `baPure_edge`: 200 (≤ 260). §2 slot graph, cycle lemma, `baSlot_path_le`: 300 (≤ 560, the risk: new, no band twin; fallback = induction by `baCactus_cut`). §3 core tree bound + corollary (port of `KLMolecule.lean:209-327`, one label per slot): 260 (≤ 820). §4 `baSigmaPi_empty_bound`, `baSig_decay`: 130 (≤ 950). §5 `baK_pure_eq`, convolution, `baPure_loop`: 230 (≤ 1180). §6 instances at `P` (`n=3,4`): 90 (≤ 1270). Stop and report if `wc -l` exceeds 1700 before §5 is done. Registry pre-check (`import RBM3D`, `RBM3D.BA.KPure`, `#assert_rbm_axioms`) in 1b.

### Verdicts
- Edge-kernel bounds `baPure_edge`: PASS. Slot-graph path bound and spanning-tree reduction `baSlot_path_le`, `baSigmaTree_bound`, `baSigmaPi_empty_bound`: PASS.
- `(eq:molecule-decay)` as `SigDecayAbs d n L (BASig …)`, every σ, uniform over the family: PASS.
- Pure loops `baPure_loop` (constant σ, `W^{−d(n−1)}`, `e^{−cD(a)}`): PASS.
- Instances at `P`, `n=3,4`: PASS (all hypotheses hold at one nondegenerate datum; no external hypothesis).
- Paper-delta candidates: T2380a, `(eq:molecule-decay)` and `(res_pureKes)` state "some `c,C>0`": Lean fixes the dependence (`d,n,Λ,κ`; uniform in `L, g≤Λ, E, m, t, σ, δ`); T2380b, rate `r/4` (not optimal); T2380c, BA chord `tΘ^{σσ}` has no `−I` (unlike the band `Θ−1`): its `1_{x=y}` term is absorbed into the exponential bound.

### (a′) Preflight corrections — Sat Oct 10 12:02:06 UTC 2026
1. (ii) names the Lean instance of `baSigmaTree_bound` at `F={(0,2)}`, `σ=(+,+,−,+)`. For that `σ` the chord `(0,2)` is long (`σ_0=+`, `σ_2=−`), so `F` is not in the layer `π=∅` and the short-chord bound (c) does not cover it. The compiled instances use `F={(0,2)}` with `σ=(+,−,+,+)` (core theorem), `σ=(+,+,+,+)` (entrywise form), the star `F=∅` at `n=3`, and `baSigmaPi_empty_bound` at `σ=(+,+,+)` (`n=3`) and `σ=(+,−,+,−)` (`n=4`). No verdict of (a) changes.
2. (iii) proves the path bound (P) by an induction `U(ν)` over the chord ancestry. The 1b proves `baSlot_path_le` otherwise, for every pair of slots with factor one: a tree grown from a base slot, one slot and one edge at a time (`KPure_span_le`), and the closed sets of the slot graph are trivial (`KPure_slot_conn`). The reference-slot form and the `2T` form of (i) follow by weakening; the constants of (i) (`c=r/4`, `S₀`) stay valid, not tight. No verdict changes.

### (b) Script output (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2380`, branch `t/T2380`, last commit 88476fa; scripts are in the scratchpad `T2380/`, not in the repository)
**Build.**
```
$ cd ../RBM3D-wt/T2380; date -u; git log -1 --format="%h %s"; lake build RBM3D.BA.KPure 2>&1 | tail -2; lake build RBM3D.BA.KPure 2>&1 | grep -c "KPure.lean:[0-9]*:[0-9]*: \(warning\|error\)"
Sat Oct 10 11:57:02 UTC 2026
88476fa T2380: KPure K09b interface example (indStepAbs_of at BASig), section headings
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3753 jobs).
0
```
**Axioms** (all 13 public declarations of the statement block below) and hygiene.
```
$ lake env lean axioms.lean | grep -c 'depends on axioms'; ... | sed 's/.* axioms: //' | sort | uniq -c   (axioms.lean: import RBM3D.BA.KPure + 13 x #print axioms)
13
  13 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/BA/KPure.lean | wc -l
       0
```
**Target statements**, `extract_stmts.py` on `RBM3D/BA/KPure.lean` (whitespace-normalised, `[line]`):
```
[105] noncomputable def baPureB (d : ℕ) (Λ κ : ℝ) : ℝ
[110] noncomputable def baPureRate (d : ℕ) (Λ κ : ℝ) : ℝ
[113] theorem baPureB_one_le (d : ℕ) (Λ κ : ℝ) : 1 ≤ baPureB d Λ κ
[116] theorem baPureRate_pos {d : ℕ} (hd : 0 < d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : 0 < baPureRate d Λ κ
[205] theorem baPure_edge (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (∀ (σ : Bool) (x y : Zd d L), ‖BAMsigma d L (BAMB d L g (E : ℂ) m)
    σ x y‖ ≤ baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ)))) ∧ (∀ (s : Bool) (x y : Zd d L), ‖BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y‖ ≤ baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ *
    (zdistD d L (x - y) : ℝ)))) ∧ (∀ (s : Bool) (x y : Zd d L), ‖(t : ℂ) * BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t s s x y‖ ≤ baPureB d Λ κ * Real.exp (-(baPureRate d Λ κ * (zdistD d L (x - y) : ℝ))))
[377] theorem baSlot_path_le {d L : ℕ} [NeZero L] {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (β : BAslot F → Zd d L) (s t : BAslot F) : zdistD d L (β s - β t) ≤ ∑ e : ↥F ⊕ BAslot F, zdistD d L (β (BACactusValSrc F e) -
    β (BACactusValTgt F e))
[414] theorem baSigmaTree_bound (hd : 2 ≤ d) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (δ : Fin n → Zd d L) {r Γ : ℝ} (hr : 0 < r) (hΓ : 0 ≤ Γ) (hprod
    : ∀ β : BAslot F → Zd d L, (∀ v : Fin n, β (BAslotLeaf F v) = δ v) → ∏ e : ↥F ⊕ BAslot F, ‖BACactusValEdgeW M t F σ e (β (BACactusValSrc F e)) (β (BACactusValTgt F e))‖ ≤ Γ * Real.exp (-(r * ((∑ e : ↥F ⊕ BAslot F, zdistD d L (β
    (BACactusValSrc F e) - β (BACactusValTgt F e)) : ℕ) : ℝ)))) (i j : Fin n) : ‖BASigmaTree d L M t F σ δ‖ ≤ Γ * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) * Real.exp (-(r / 4 * (zdistD d L (δ i - δ j)
    : ℝ)))
[537] theorem baSigmaTree_bound_of_entries (hd : 2 ≤ d) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (δ : Fin n → Zd d L) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 <
    r) (hE : ∀ (e : ↥F ⊕ BAslot F) (x y : Zd d L), ‖BACactusValEdgeW M t F σ e x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ)))) (i j : Fin n) : ‖BASigmaTree d L M t F σ δ‖ ≤ B ^ (n + 3 * (n * n)) * (expC (d - 2) (r / (4 * ((n + 2
    * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) * Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ)))
[551] theorem baSigmaTree_bound_maxDist (hd : 2 ≤ d) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (δ : Fin n → Zd d L) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hE : ∀ (e : ↥F ⊕ BAslot F) (x y : Zd d L), ‖BACactusValEdgeW M t F σ e x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ)))) : ‖BASigmaTree d L M t F σ δ‖ ≤ B ^ (n + 3 * (n * n)) * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) :
    ℝ)))) ^ (n + 2 * (n * n)) * Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ)))
[589] theorem baSigmaPi_empty_bound (hd : 2 ≤ d) (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) (hM : ∀ (s : Bool) (x y : Zd d L), ‖M s x y‖ ≤ B * Real.exp (-(r *
    (zdistD d L (x - y) : ℝ)))) (hΘ : ∀ (s : Bool) (x y : Zd d L), ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * Real.exp (-(r * (zdistD d L (x - y) : ℝ)))) (δ : Fin n → Zd d L) : ‖BASigmaPi d L n M t σ ∅ δ‖ ≤ ((TSP n).card : ℝ) * (B ^ (n +
    3 * (n * n)) * (expC (d - 2) (r / (4 * ((n + 2 * (n * n) : ℕ) : ℝ)))) ^ (n + 2 * (n * n)) * Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))))
[632] theorem baSig_decay {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i) (hgΛ
    : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) : SigDecayAbs d n L (BASig d n L g E m t)
[670] theorem baK_pure_eq (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (σ₀ : Bool) (a
    : Fin n → Zd d L) : BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L (fun _ => σ₀) a) = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ δ : Fin n → Zd d L, BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t (fun
    _ => σ₀) ∅ δ * ∏ v, BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₀ σ₀ (a v) (δ v)
[813] theorem baPure_loop {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero
    L := ⟨by omega⟩ BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₀ : Bool) (a : Fin n → Zd d L), ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L (fun _ => σ₀) a)‖ ≤ C * (((W : ℝ) ^ d)⁻¹) ^ (n - 1)
    * Real.exp (-(c * (KLmaxDist d L a : ℝ)))
```
**Compiled nonempty instances**, `extract_inst.py` (namespace `KPureInst`, datum: flow point `P` of `(d,L)=(3,4)`, `Λ=10`, `κ=Im m₀`, `t=1/2`, `W=2`; each example truncated at 232 characters, full text `KPure.lean:844-1016`):
```
[857] private noncomputable abbrev M0 : Bool → Matrix (Zd 3 4) (Zd 3 4) ℂ := BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)
[859] private noncomputable abbrev tP : ℝ := 1 / 2
[861] private abbrev δ3 : Fin 3 → Zd 3 4 := ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]]
[863] private abbrev δ4 : Fin 4 → Zd 3 4 := ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]
[866] example : KLmaxDist 3 4 δ3 = 2 := by decide
[868] example : KLmaxDist 3 4 δ4 = 2 := by decide
[870] private abbrev F02 : Finset (Fin 4 × Fin 4) := {((0 : Fin 4), (2 : Fin 4))}
[872] private theorem F02_tsp : KLIsTSP F02 := KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)
[874] private theorem rate_pos : 0 < baPureRate 3 10 P.m0.im := baPureRate_pos (by norm_num) (by norm_num) P.real.1.1
[877] private theorem edge_P : (∀ (σ : Bool) (x y : Zd 3 4), ‖M0 σ x y‖ ≤ baPureB 3 10 P.m0.im * Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 (x - y) : ℝ)))) ∧ (∀ (s : Bool) (x y : Zd 3 4), ‖BAThetaOf M0 tP s s x y‖ ≤ baPureB 3 10...
[889] example : ‖M0 true 0 ![1, 0, 0]‖ ≤ baPureB 3 10 P.m0.im * Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) := edge_P.1 true 0 ![1, 0, 0]
[893] example : ‖BAThetaOf M0 tP false false 0 ![1, 0, 0]‖ ≤ baPureB 3 10 P.m0.im * Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) := edge_P.2.1 false 0 ![1, 0, 0]
[897] example : ‖(tP : ℂ) * BAThetaOf M0 tP true true 0 ![1, 0, 0]‖ ≤ baPureB 3 10 P.m0.im * Real.exp (-(baPureRate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ))) := edge_P.2.2 true 0 ![1, 0, 0]
[901] example : 1 ≤ baPureB 3 10 P.m0.im ∧ 0 < baPureRate 3 10 P.m0.im := ⟨baPureB_one_le 3 10 P.m0.im, rate_pos⟩
[905] example := baSlot_path_le (d := 3) (L := 4) F02_tsp (by norm_num) (fun s : BAslot F02 => (![((BAslotStart F02 s).val : ZMod 4), 0, 0] : Zd 3 4)) (BAslotLeaf F02 0) (BAslotLeaf F02 2)
[909] example := baSlot_path_le (d := 3) (L := 4) (F := (∅ : Finset (Fin 3 × Fin 3))) (KLisTSP_of_mem_TSP (empty_mem_TSP 3)) (by norm_num) (fun s => δ3 (BAslotStart _ s)) (BAslotLeaf _ 0) (BAslotLeaf _ 2)
[914] example := baSigmaTree_bound (d := 3) (L := 4) (n := 4) (F := F02) (by norm_num) F02_tsp (by norm_num) M0 tP ![true, false, true, true] δ4 rate_pos (pow_nonneg (by linarith [baPureB_one_le 3 10 P.m0.im]) _) (fun β _ => KPure_hpro...
[921] example : Fintype.card (↥F02 ⊕ BAslot F02) = 7 := by rw [Fintype.card_sum, Fintype.card_coe, BAslot_card] rfl
[926] example := baSigmaTree_bound_of_entries (d := 3) (L := 4) (n := 4) (F := F02) (by norm_num) F02_tsp (by norm_num) M0 tP ![true, true, true, true] δ4 (baPureB_one_le 3 10 P.m0.im) rate_pos (KPure_edge_entries M0 tP _ (by decide) e...
[932] example := baSigmaTree_bound_of_entries (d := 3) (L := 4) (n := 3) (F := (∅ : Finset (Fin 3 × Fin 3))) (by norm_num) (KLisTSP_of_mem_TSP (empty_mem_TSP 3)) (by norm_num) M0 tP ![true, true, true] δ3 (baPureB_one_le 3 10 P.m0.im) ...
[939] example := baSigmaTree_bound_maxDist (d := 3) (L := 4) (n := 4) (F := F02) (by norm_num) F02_tsp (by norm_num) M0 tP ![true, false, true, true] δ4 (baPureB_one_le 3 10 P.m0.im) rate_pos (KPure_edge_entries M0 tP _ (by decide) edg...
[946] example := baSigmaPi_empty_bound (d := 3) (L := 4) (n := 3) (by norm_num) (by norm_num) M0 tP ![true, true, true] (baPureB_one_le 3 10 P.m0.im) rate_pos edge_P.1 edge_P.2.2 δ3
[950] example := baSigmaPi_empty_bound (d := 3) (L := 4) (n := 4) (by norm_num) (by norm_num) M0 tP ![true, false, true, false] (baPureB_one_le 3 10 P.m0.im) rate_pos edge_P.1 edge_P.2.2 δ4
[955] example : SigDecayAbs 3 3 (fun _ : Unit => 4) (BASig 3 3 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP)) := baSig_decay (ι := Unit) (d := 3) (n := 3) (Λ := 10) (κ := P.m0.im) (by norm_num) (by no...
[963] example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => tP) () ![true, false, true, false] δ4‖ ≤ C * Real.exp (-(c * (KLmaxDist 3 4 δ4 : ℝ))) := let ⟨C, ...
[973] example := baK_pure_eq 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := tP) ⟨by norm_num, by norm_num⟩ (n := 3) (by norm_num) true δ3
[977] example := baK_pure_eq 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := tP) ⟨by norm_num, by norm_num⟩ (n := 4) (by norm_num) true δ4
[983] example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ‖BAKsol 3 4 2 M0 (PropSpin P.m0) tP (KLloopOf 3 4 (fun _ : Fin 3 => true) δ3)‖ ≤ C * ((((2 : ℕ) : ℝ) ^ 3)⁻¹) ^ (3 - 1) * Real.exp (-(c * (KLmaxDist 3 4 δ3 : ℝ))) := let ⟨C, hC, c, hc, H...
[990] example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ‖BAKsol 3 4 2 M0 (PropSpin P.m0) tP (KLloopOf 3 4 (fun _ : Fin 4 => true) δ4)‖ ≤ C * ((((2 : ℕ) : ℝ) ^ 3)⁻¹) ^ (4 - 1) * Real.exp (-(c * (KLmaxDist 3 4 δ4 : ℝ))) := let ⟨C, hC, c, hc, H...
[1000] example (TH : ∀ _ : Unit, Bool → Bool → Matrix (Zd 3 4) (Zd 3 4) ℂ) (hTH : IndStepTH 3 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => tP) TH) (hS : SigSumZeroAbs 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => tP) (BASig 3 4 (fu...
```
**Name clash, registry pre-check, check file, branch diff, sizes.**
```
$ grep -rnE 'baPureB|baPureRate|baPure_edge|baPure_loop|baSlot_path_le|baSigmaTree_bound|baSigmaPi_empty_bound|baSig_decay|baK_pure_eq|KPure_|KPureInst' RBM3D/RBM3D RBM3D/RBM3D.lean RBM3D-wt/T2381/RBM3D RBM3D-wt/T2378/RBM3D RBM3D-wt/T2379/RBM3D RBM1D/RBM1D RBM2D/RBM2D 2>/dev/null | wc -l
       0
$ git -C RBM3D grep -c -E 'baPureB|baPureRate|baPure_edge|baPure_loop|baSlot_path_le|baSigmaTree_bound|baSigmaPi_empty_bound|baSig_decay|baK_pure_eq|KPure_|KPureInst' main -- RBM3D RBM3D.lean | wc -l   # main = 306957f
       0
$ date -u; git log -1 --format=%h; printf 'import RBM3D\nimport RBM3D.BA.KPure\n#assert_rbm_axioms\n' > with.lean; (same without the KPure import) > without.lean; lake env lean with.lean > with.out; lake env lean without.lean > without.out; head -1 with.out without.out; diff with.out without.out | grep -c '^[0-9]'; diff with.out without.out | head -1
Sat Oct 10 11:59:26 UTC 2026
88476fa
with.lean exit 0
without.lean exit 0
axiom audit: 11012 theorems, 3223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
axiom audit: 11000 theorems, 3221 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
changed hunks (with vs without): 1, first hunk header: 1c1; premise-scan line (with): premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).; (without): premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
$ lake env lean docs/tickets/checks/T2380-check.lean 2>&1 | grep -c error
0
$ git diff --stat main...t/T2380
 RBM3D/BA/KPure.lean | 1016 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1016 insertions(+)
$ per commit: wc -l of RBM3D/BA/KPure.lean (git show <c>:...) and commit date
0619ad2      379 lines  2026-10-10T04:23:16-07:00 T2380: KPure sections 0-2 (edge bounds, spanning-tree path bound in the slot graph)
e5df01c      613 lines  2026-10-10T04:25:44-07:00 T2380: KPure sections 3-4 (tree bound, molecule bound, baSig_decay)
cfd0617      825 lines  2026-10-10T04:28:53-07:00 T2380: KPure section 5 (pure loop reduction and bound baPure_loop)
46116fb      986 lines  2026-10-10T04:32:32-07:00 T2380: KPure section 6 (compiled instances at the flow point), maxDist corollary, lint cleanup
ffb7515      997 lines  2026-10-10T04:36:44-07:00 T2380: KPure instances: edge count and pure-charge tree example
0650724      992 lines  2026-10-10T04:38:35-07:00 T2380: baSigmaPi_empty_bound in the KLmaxDist form of the design
8e59987      997 lines  2026-10-10T04:39:46-07:00 T2380: KPure instances: labels not collapsed (decide)
88476fa     1016 lines  2026-10-10T04:56:49-07:00 T2380: KPure K09b interface example (indStepAbs_of at BASig), section headings
```
**Ports.** No RBM1D or RBM2D text was used or copied (the name-clash `grep` above only scanned them; no diff-stat owed). Copies from merged RBM3D files, private with the stem `KPure_`: `KPure_theta_shift` ← `BA/KMolecule.lean:166` (at `e = Equiv.addRight c`); `KPure_anc_step` ← `Loop/KLMolecule.lean:86` (trimmed); `KPure_card_le` ← `:450`; `KPure_prod_const_exp` ← `:439` (any finite edge type); `KPure_zdistD_comm/tri` ← `:72-79`. `baSigmaTree_bound` follows `KLMolecule_tree_bound` (`:209`), `baSigmaPi_empty_bound` follows `KLmolecule_holds` (`:610`), with one label per slot.
**Narrative.**
1. All 13 public declarations above are proved, with the three standard axioms, and the file has no `sorry`, `admit`, `native_decide` or `axiom` (hygiene line above); it has 1016 lines in 8 commits (sizes above), far below the stop line 2000 and the internal 1700.
2. Layout: §0 helpers `:52`, §1 constants and `baPure_edge` `:101`, §2 slot graph and `baSlot_path_le` `:228`, §3 tree bound `:387`, §4 molecule bound and `baSig_decay` `:580`, §5 pure loops `:657`, §6 instances `:844`.
3. §1: (a) from `BAPropM3_of_real` (`CombesThomas.lean:539`), both branches (`(Cg)^k ≤ 2^{-k} ≤ e^{-rk}` for `g<(2C)⁻¹`, else `c₀⁻¹e^{-c₀k}`), `M(−)=Mᴴ` by `zdistD_neg`; (b), (c) from `baProp5s_of_real` (`Prop5Short.lean:608`) after the translation `x ↦ 0`, with `1_{a=0} ≤ e^{-c_s|a|}`, `g² ≤ Λ²`, `|t| ≤ 1`.
4. §2 (the one new argument): `KPure_span_le` is abstract: if every edge-closed vertex set containing one vertex is everything, then `ρ(f v, f s) ≤ Σ_e ρ(f c_e, f q_e)`; the proof grows a pair `(S, A)` (a crossing edge exists, is new, adds one vertex and one edge). `KPure_slot_conn` shows the closed sets of the slot graph are trivial: the `M`-edges of a node are one orbit of `BAnextSlot` (`BAnextSlot_orbit`), the chord `In J — Out J` reaches the parent node, strong induction on `|{e ∈ F : ν ⊆ e}|` (`KPure_anc_step`), the root node contains the leaf slot `n−1`.
5. §3: `baSigmaTree_bound` sums over slot labellings `b`; for `b` consistent with `δ`, `hprod` and `T(b) ≥ |δ_i−δ_j|`, `T(b) ≥ |δ_i−b s|` give `e^{-rT} ≤ e^{-(r/4)|δ_i−δ_j|} ∏_s e^{-λ|δ_i−b s|}`, `λ = r/(4N₀)`; inconsistent `b` vanish; `Σ_b ∏_s g(b s) = (Σ g)^N ≤ S₀^{N₀}` (`BAsum_exp_decay_le`, `Prop5Short.lean:251`; `S₀ ≥ 1`, `N = n+2|F| ≤ N₀`). The entrywise form uses `|ℰ| = |F| + (n+2|F|) ≤ n+3n²` (`BAslot_card`, `KCactus.lean:113`); `KLMolecule_exists_pair` (`KLMolecule.lean:584`) turns the pair form into `KLmaxDist` (`baSigmaTree_bound_maxDist`).
6. §4: `baSigmaPi_empty_bound`: in the layer `π=∅` every chord is short (`KLMolecule_same_charge`), `|KLTSPlong n σ ∅| ≤ |TSP n|`; `baSig_decay` instantiates it at each `i` with constants independent of `i`, every `σ`.
7. §5: for constant `σ`, `KLFlong F σ = ∅`, so only `π=∅` survives in `baK_eq_sum_Kpi` (K06), then `baKpi_eq_sum_SigmaPi`. `baPure_loop`: `‖Σ_δ‖ ≤ Σ_δ ‖Σ(δ)‖ ∏_v ‖Θ(a_v,δ_v)‖`, `max|a_i−a_j| ≤ max|δ_i−δ_j| + 2 Σ_v |a_v−δ_v|`, `Σ_δ ∏_v f_v(δ_v) = ∏_v Σ_x f_v(x)`, `Σ_x e^{-(r/2)|a_v−x|} ≤ expC (d−2) (r/2)`; `c = r/4`, `C = C_Σ (B S')^n`; `‖(W^d)⁻¹^{n−1}‖` by `norm_pow`, `norm_inv`, `Complex.norm_natCast`. No `1 ≤ W` is used.
8. Instances (all deterministic hypotheses discharged): edge bounds at `P`, `B ≥ 1`, `r > 0`; `baSlot_path_le` at `F={(0,2)}` (`n+2|F| = 6` slots, `n+3|F| = 7` edges: `Fintype.card (↥F02 ⊕ BAslot F02) = 7`) and at the star; the tree bounds (core with `hprod` discharged, entrywise, `KLmaxDist` form); `baSigmaPi_empty_bound` at `n=3,4`; `baSig_decay` (`SigDecayAbs` at `ι=Unit`, `n=3`, applied at `n=4`); `baK_pure_eq` and `baPure_loop` at `n=3,4`; the K09b interface (`indStepAbs_of` at `BASig` with `hD := baSig_decay`; `hTH` of K12 and `hS` of K08 stay hypotheses, other gates' pins). The labels `δ3`, `δ4` are not collapsed (`KLmaxDist = 2`, `decide`).
9. Merged inputs not used: `BAK_off_le`, `sum_exp_decay_conv`, `sum_exp_decay_centre`, `norm_sum_prod_le` (the lattice sum is `BAsum_exp_decay_le` in general `d`; the star bound has no role in the cactus route); the imports of `Loop.PureLoop` and `BA.KKernel` are kept as the ticket lists them. `baPropM_holds`, `baProp5s_holds` enter through their explicit-constant bodies `BAPropM3_of_real`, `baProp5s_of_real`, which fix `baPureB`, `baPureRate` as in (a).
10. Registry pre-check: `#assert_rbm_axioms` with and without `import RBM3D.BA.KPure` differs in one hunk (`1c1`: 11012 vs 11000 theorems, 3223 vs 3221 definitions, 0 axioms in `RBM`), the premise scan reads 113 in both: no new premise.
11. `main` moved from 442d3aa to 306957f (T2381 merged `BA/KInduct.lean`, `RBM3D.lean` +1 line); the `git grep` above finds none of the new names on it. The root import is added by the hub after the last `import` line of `RBM3D.lean`.

### (c) Verified Mathlib names used (`modof.lean`: `env.getModuleIdxFor?` of each name in the compiled environment: 112 names looked up, 112 resolved, 0 absent; the 104 lemma names are listed, 8 definitions and constructors are omitted: `Real.exp`, `Real.log`, `Finset.univ`, `Fintype.card`, `Set.Ico`, `Sum.inl`, `Sum.inr`, `Equiv.addRight`; grouped by namespace to keep the report within 300 lines; no name was invented)
```
Bool.*: false_eq_true
Complex.*: norm_natCast, norm_real
Equiv.*: coe_addRight
Finset.*: card_erase_of_mem, card_le_card, card_le_univ, card_lt_card, card_pos, card_univ, empty_mem_powerset, filter_subset, le_sup, mem_erase, mem_filter, mem_insert, mem_insert_of_mem, mem_insert_self,
  mem_singleton, mem_univ, mul_sum, prod_const, prod_eq_one, prod_eq_zero, prod_le_prod₀, prod_mul_distrib, prod_nonneg, prod_univ_sum, sdiff_subset_sdiff, single_le_sum, ssubset_iff_of_subset, subset_insert,
  subset_univ, sum_const, sum_eq_single, sum_eq_zero, sum_insert, sum_le_sum, sum_le_sum_of_subset, sum_neg_distrib, sum_nonneg
Fintype.*: card_coe, card_fin, card_sum, piFinset_univ
Function.*: iterate_succ_apply'
Matrix.*: conjTranspose_apply, inv_submatrix_equiv, nonsing_inv_eq_ringInverse, of_apply, one_apply, one_apply_eq, one_apply_ne, smul_apply, sub_apply, submatrix_apply
Nat.*: cast_nonneg, cast_sum, le_add_left, strong_induction_on
Real.*: exp_add, exp_le_exp, exp_log, exp_nat_mul, exp_neg, exp_pos, exp_sum, log_pos, norm_eq_abs
root.*: abs_of_nonneg, add_le_add, add_left_inj, le_max_left, le_max_right, le_mul_of_one_le_left, le_of_eq, le_refl, lt_div_iff₀, lt_min, min_le_left, min_le_right, mul_le_mul, mul_le_mul_of_nonneg_left,
  mul_le_mul_of_nonneg_right, mul_le_of_le_one_left, mul_nonneg, neg_mul, neg_sub, norm_inv, norm_mul, norm_nonneg, norm_pow, norm_prod, norm_star, norm_sum_le, norm_zero, nsmul_eq_mul, one_div, pow_le_pow_left₀,
  pow_le_pow_right₀, pow_nonneg, sub_add_cancel, sub_add_sub_cancel, zero_add
```

### (d) Open issues and paper-delta candidates
- No REQ, no pin repair, no obstruction. The only hypotheses left in an instance are `hTH`, `hS` of the K09b interface example (other gates' pins).
- Public declarations beyond the (i) table: `baPureB_one_le`, `baPureRate_pos` (the `B ≥ 1`, `r > 0` of the table), `baSigmaTree_bound_of_entries` (the table's corollary with entrywise hypotheses), `baSigmaTree_bound_maxDist` (the ticket's `e^{-c·maxdist}` form). `baSlot_path_le` is stronger than the table (every pair, factor one). `T(β)` is written inline (no public `def`).
- The constants are explicit and finite but weak at `Λ=10` ((a) table: `r = 2.47e-30`, from the merged `BAp5s_rate`); consumers use `∃ C, c` only. K08b reuses `baSigmaTree_bound` through `hprod`; K09b takes `baSig_decay` per index `i`, as the `hr` of `indStepAbs_of` (`Loop/KLIndStepB.lean:879`), and the interface example above compiles.
- T2380a (from (a)): `(eq:molecule-decay)` and `(res_pureKes)` state "some `c, C > 0`" (`c_n, C_n`); Lean fixes `c = r/4`, `C = C_Σ (B S')^n`, depending on `(d, n, Λ, κ)` only, uniform in `L ≥ 3`, `g ≤ Λ`, `E`, `m`, `t`, `σ`, `δ` (and `W`, `a` for the pure loop).
- T2380b (from (a)): the rate `r/4` is not optimal. T2380c (from (a)): the BA chord `tΘ^{(σσ)}` has no `−I` (unlike the band `Θ−1`); its `1_{x=y}` term is absorbed into `B = baPureB` (contains `C₅(1+Λ²)`).
- T2380d (1a-audit O1): `baPure_loop` and `baSig_decay` assume `3 ≤ n` (the range of `baK_eq_sum_Kpi`), while `lem_pureloop` (`A:643-647`) is stated for every `n`; in the proof of `ML:Kbound` the paper treats `n ∈ {1,2,3}` by the explicit formulas (`A:673`), which the 1a-audit assigns to K03/K12. `t ∈ [0,1)` is explicit in `baPure_loop` (the molecule bound holds on `t ∈ [0,1]`).
