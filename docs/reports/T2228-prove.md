Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 23:42:36 UTC 2026 (`date -u`; start 23:39:12)

Notation (ticket and `Defs/Sizes.lean:214`, `Defs/Params.lean:36`): `B = Bctl n u = W^{-d}((λ²+(1-u))⁻¹ + (L^d(1-u))⁻¹)` (`K=0`, `((0+1)^{d-2})⁻¹ = 1`), `N = (WL)^d`,
`R_u = (1-u)⁻¹ (N(1-u))⁻³`, `R' = N B⁴`. `Prec` = `StochDomAt` with the union over the index inside `P` (`StochDomAt.lean:61-63`).
Paper `6:63-79` (`eq:Exp(L-K)2`, `eq:ExpLWn=2_smalleta`) and `3_5:1634` (`deccA0`) read; the statements agree with the ticket's mathematics.

### (i) Exponent table
Budget used (one admissible choice, proved by hand below): every ingredient (`STLKU`, `STExpAvgU`, `stKbound_timeIcc`) at level `θ = τ/4`.

| item | value | constraint | slack |
|---|---|---|---|
| `𝔠_d` | `1/100` | `0 < 𝔠_d ≤ 1/100` (`STIngR6`); no input depends on it | `≤` tight (0); positivity `1/100` |
| regime (iv) | `1-u ≤ 1-s ≤ λ²/L^d` | gives `L^d(1-u) ≤ λ² ≤ λ²+(1-u)`, so `B ≤ 2(N(1-u))⁻¹` (constant `2`) | at `(szG,5/8)`: `1/64`; `B` ratio `0.9729` |
| `N B⁴ ≤ 16 R_u` | `16 = 2⁴` | `N·(N(1-u))⁻⁴ = (1-u)⁻¹(N(1-u))⁻³`, so `N B⁴ ≤ 16 N (N(1-u))⁻⁴ = 16 R_u` | ratio `NB⁴/(16R_u) = 0.896` (u=5/8), `0.445` (u=3/4) |
| floor `Kf` | `3` | `R' ≥ N^{-3}`: `B ≥ N⁻¹` (`expAvg_Bctl_ge`, `0 ≤ u < 1`), `R' = N B⁴ ≥ N·N⁻⁴` | equality at `B = N⁻¹` (exponent slack 0); `B ≥ N⁻¹` has ratio `5.19` at `szG,5/8` |
| envelope `Kenv` | `6` | `‖ℰ^{LK×LK}‖ ≤ N(η⁻²+(1-t)⁻¹)² ≤ 4N⁵`; `‖ℰ^{G̃}‖ ≤ 2N(η⁻¹+1)η⁻³ ≤ 4N⁵`; `‖X_B‖ ≤ 2N(η⁻¹+1)(η⁻³+NB²) ≤ 20N⁵` (uses `η⁻¹ ≤ N`, `(1-t)⁻¹ ≤ η⁻¹` (`Im m ≤ 1`), `‖𝒦^{(3)}‖ ≤ N B² ≤ 4N³` from `B ≤ 2(1-u)⁻¹ ≤ 2η⁻¹`) | `≤ N⁶` iff `N ≥ 20` (`N ≥ 4` for the first two); `N^6/20N^5 = N/20` |
| `η_u⁻¹ ≤ N` (`expAvg_eta_inv_le`, merged) | `u ≤ lemT z` | eventually: `N^ε ≥ 4/c₀`, `c₀ = √(2κ)/2` (`ExpAvg.lean:631-640`, `ExpEtermsA.lean:202-209`) | threshold `N ≥ 3.355e12` at `κ=ε=1/10` (eventual only; the inequality itself holds numerically at n=0 below) |
| first-moment level `D_p` | `Kenv+Kf+1 = 10` | `P(S_n) ≤ N^{-10}` ⇒ `Env·P(S_n) ≤ N^{6-10} = N⁻⁴ ≤ N⁻³ ≤ R'` | factor `N` in `N^{-4}` vs `N^{-3}` |
| union of 3 failure events | each at `D_p+1 = 11` | `3 N^{-11} ≤ N^{-10}` | `N ≥ 3` |
| pieces of `D_u` (θ=τ/4) | `LK: 2`, `A: 2`, `X_B: 3`, total `7` | `𝔼‖ℰ^{LK}‖ ≤ N^{2θ}R' + N⁻⁴ ≤ 2N^{2θ}R'`; `|A| ≤ 2 N·(N^θB²)(N^θB²)`; `|X_B| ≤ 2N^{2θ}R'` off-event, `𝔼 ≤ 3N^{2θ}R'` (uses `Σ_x|S_{xy}| = 1` (`sum_norm_SB_row`, `SB_transpose`, `3 ≤ L`), `card = L^d`, `W^dL^d = N`) | — |
| final absorption | `7·16 = 112` | `112 N^{τ/2} R_u ≤ N^τ R_u` iff `N^{τ/2} ≥ 112` | `τ=1`: `N ≥ 1.254e4`; `τ=1/2`: `1.574e8`; `τ=1/10`: `9.646e40` (eventual in `n`; ticket's `expDr_expect` condition `N^{τ/2} ≥ 2` is weaker) |
| decay level | `HighProbAt` at `D+7` | `Env P(G_nᶜ) ≤ N⁶ N^{-(D+7)} = N^{-(D+1)} ≤ W^{-(D+1)}` (`W ≤ N`) | factor `(N/W)^{D+1}` |
| decay constant | `4` | `|D_v(a)| ≤ 2(W^{-(D+1)} + N^{-(D+1)}) ≤ 4W^{-(D+1)} ≤ W^{-D}` iff `W ≥ 4` | `szG` has `W_n = n+4 ≥ 4`: slack 0 at `n=0`, `W=4` |
| decay `ε, D` | `stEtermDecay` at `(ε, D+1)`, `k=2`, `Cd = 0` | `ℓ¹`→`ℓ^∞` conversion inside the merged theorem; `STReg5I` not used | — |
| mollifier constants (§71) | none | neither pin quantifies over a mollifier | — |

`STExpAvgU`, `stKbound_timeIcc` (k=3 gives `Bctl²`), `STLKU` (k=1,2,3) enter only through `Bctl^k` at level `θ`; the three `STLKU` events are united by `of_subset_union`.
Regime used only through `1-u ≤ 1-s ≤ λ²/L^d` (`STReg5IV`, `Step5Pins.lean:63`); time range `0 ≤ s ≤ u ≤ t ≤ lemT z < 1`.

### (ii) One concrete nondegenerate instance: `(szG, zB, s=5/8, t=3/4)`, `d=3`, `L=4`, `W_n=n+4`, `λ=5`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `n=0`: `N=4096`
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2228/pf.py | grep -v "^D=[125] W=\(5\|32\)" | grep -v "^   \(slack\|N^\)"` (stdlib `cmath`; `msc` = root of `m²+zm+1` with `Im>0`)
```
N= 4096 lam^2/L^d= 25/64 = 0.390625
OK   regime(iv): 1-s <= lam^2/L^d  (3/8 <= 25/64)
zB: lemE=0.499984 lemT=0.983992 1-lemT=0.016008 Im m(E)=0.968248
OK   t=3/4 <= lemT zB, lemT zB>=31/32
OK   |E|<=|Re z|=1/2 <= 2-kappa=1.9
OK   locDomain: N^(-0.9)<=Im z=1/64<=1
max over u in [5/8,3/4]: B/(2/(N(1-u))) = 0.9729 (<=1); N B^4/R_u = 14.3352 (<=16)
u=0.625 B=1.2668e-03 2/(N(1-u))=1.3021e-03  N B^4=1.0549e-08 16R_u=1.1774e-08 floor N^-3=1.46e-11
u=0.750 B=1.5954e-03 2/(N(1-u))=1.9531e-03  N B^4=2.6534e-08 16R_u=5.9605e-08 floor N^-3=1.46e-11
szG,zB n=0 u=0.75: eta^-1=4.131e+00 (N=4.096e+03, eta^-1<=N: True) | EnvLK=1.818e+06 EnvG=2.964e+06 EnvXB=2.964e+06  N^6=4.722e+21
szG,zB n=0 u=lemT: eta^-1=6.452e+01 (...True) | EnvLK=7.312e+10 EnvG=1.441e+11 EnvXB=1.441e+11  N^6=4.722e+21
sz0 n=0: N= 2097152 Im z0=8.764e-06 lemT=0.999990949 1-lemT=9.051e-06 lam^2/L^3=3.815e-06
sz0,z0 n=0 u=lemT: eta^-1=1.141e+05 (...True) | EnvLK=3.555e+26 EnvG=7.110e+26 EnvXB=7.110e+26  N^6=8.507e+37
note: regime (iv) at sz0,z0,t=lemT fails (1-lemT=9.05e-06 > lam^2/L^3=3.81e-06), so no (iv) instance there
Thresholds: tau=1: N>=2^(2/tau)=4 ; N>=112^(2/tau)=1.254e+04 (szG first n=2, N_n=1.382e+04)
            tau=0.5: 1.600e+01 ; 1.574e+08 (first n=131) ; tau=0.1: 1.049e+06 ; 9.646e+40 (first n=11465513054278)
eta^-1<=N lemma threshold (kappa=eps=1/10): N>=(4/c0)^(1/eps)=3.355e+12
D=1 W=4 N=4096: 4W^-(D+1)=2.500e-01 <= W^-D=2.500e-01 : True ; N^-(D+1)<=W^-(D+1): True
D=2 W=4 N=4096: 4W^-(D+1)=6.250e-02 <= W^-D=6.250e-02 : True ; N^-(D+1)<=W^-(D+1): True
OK   W>=4 at szG n=0 (W=4): 4W^-(D+1)<=W^-D equality
OK   N>=20 at n=0 for 4N^5<=N^6,20N^5<=N^6
```
(Output lines `szG,zB … u=…` and `Thresholds` are shortened from the script's full lines; all `OK`, no `FAIL`; the `D=5`/`W=5,32` rows also print `True`.) Every deterministic hypothesis of both pins holds at this data: `3 ≤ d`, `0 ≤ s < t`, `t ≤ lemT zB` (`3/4 ≤ 0.984`), `STReg5IV` (`3/8 ≤ 25/64`, for every `n`, since `L, λ` are constant), `STFlow` (`|lemE| ≈ 0.5 ≤ 1.9`, `N^{-0.9} = 5.6e-4 ≤ 1/64`), `W ≥ 4`, `N ≥ 20`; `0 < λ = 5 ≤ 𝔡⁻¹ = 10`. The window `[5/8,3/4]` is not collapsed (`s < t`); `N = 4096`, not `0`. Decay uses no regime, so the same data serves it (`STReg5I` unused).

External hypotheses (stochastic premises of `STIngR6`/`STExpDriftLo`: `STLKU`, `STGdecayW … 0`, `STExpAvgU`; they stay hypotheses): concrete limit computation along `szG`, `n → ∞` (`W = n+4`, `N = (4W)³ → ∞`; `L, λ` fixed). Command: `python3 …/T2228/lim.py`
```
u=5/8 n=0: B/(2(N(1-u))^-1)=0.972906  NB^4/(16R_u)=0.895951  N*Bctl=5.188834e+00
u=5/8 n=1000000: B/(2(N(1-u))^-1)=0.972906  NB^4/(16R_u)=0.895951  N*Bctl=5.188834e+00
  exact n-independent limit: B N (1-u) = 1+64(1-u)/(26-u) = 1.9458128078817734
u=3/4 n=0: B/(2(N(1-u))^-1)=0.816832  NB^4/(16R_u)=0.445175  N*Bctl=6.534653e+00
u=3/4 n=1000000: B/(2(N(1-u))^-1)=0.816832  NB^4/(16R_u)=0.445175  N*Bctl=6.534653e+00
  exact n-independent limit: B N (1-u) = 1+64(1-u)/(26-u) = 1.6336633663366336
```
So along `szG` the control is `Bctl ≍ (N(1-u))⁻¹` with the explicit limit `B N (1-u) = 1 + 64(1-u)/(26-u) ≤ 2` (zero-mode regime), i.e. the premises `STLKU`, `STExpAvgU` are the averaged-local-law rates `(Nη)⁻¹`, `(Nη)^{-k}` at this scale, neither vacuous nor stronger than the floor `Bctl ≥ N⁻¹`; the ratios `B/(2/(N(1-u)))` and `NB⁴/(16R_u)` are `n`-independent (`< 1`), so the comparison with `R_u` closes for every `n`, not only at `n=0`.

### Verdicts
- `STExpDriftLo` (iv): **PASS**. Route closes: regime gives `B ≤ 2(N(1-u))⁻¹` and `N B⁴ ≤ 16R_u`; the three pieces sum to `≤ 7 N^{τ/2} N B⁴ ≤ 112 N^{τ/2} R_u ≤ N^τ R_u` for `N^{τ/2} ≥ 112`; envelope `N⁶` and floor `N^{-3}` with `D_p = 10` close; all hypotheses hold at the instance.
- `STExpDriftDecay`: **PASS**. `|D| ≤ 4W^{-(D+1)} ≤ W^{-D}` (`W ≥ 4`); `HighProbAt` level `D+7` against envelope `N⁶` and `W ≤ N` closes; holds in every regime (`STReg5I` unused); instance has `W = 4` at `n=0`, slack 0 (`W_n ≥ 4` for all `n`).
- Targets 0-1 (`expDrEGtLKM`, `expDrEGtK`, `expDr_Bctl_le_IV`, `expDr_envEGt`, `expDr_EGt_split`) and 2 (a)-(e): **PASS** mathematically (envelope, floor, split `𝓛^{(3)} = 𝒦^{(3)} + (𝓛-𝒦)^{(3)}`, `avg = (𝓛-𝒦)^{(1)}` since `𝒦^{(1)} = mSigma` (`KLK_one`, `KLTree.lean:206`); constants above). Target 4 instances: deterministic data of the instance above (`szG`, `n=0`, `u=3/4`: `1/4 ≤ 25/64`; `sz0`, `E=u=1/2`).
- No FAIL / BLOCKED: no step needs a hypothesis the pins lack; no `T2228a` candidate. Observation: ticket's "`1.06e-8`" for `N B⁴` at `u=5/8` prints as `1.0549e-08`; the inequality `≤ 16R_u = 1.1774e-08` holds.

## (b) Script output, stage 1b (first tool call `date -u` = Mon Oct  5 23:43:33 UTC 2026; report written Tue Oct  6 00:05:32 UTC 2026; commit `62288d9` on `t/T2228`)

### b.1 Build (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2228`)
```
$ date -u; lake build RBM3D.Induction.ExpEtermsB 2>&1 | grep -E "ExpEtermsB|Build completed|error"; echo "warnings/errors in ExpEtermsB.lean: $(lake build RBM3D.Induction.ExpEtermsB 2>&1 | grep -c 'ExpEtermsB.lean:')"
Tue Oct  6 00:03:06 UTC 2026
Build completed successfully (3854 jobs).
warnings/errors in ExpEtermsB.lean: 0
$ wc -l RBM3D/Induction/ExpEtermsB.lean; grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/ExpEtermsB.lean
1177 RBM3D/Induction/ExpEtermsB.lean
0
$ (time lake build)   # with a temporary uncommitted `import RBM3D.Induction.ExpEtermsB` in RBM3D.lean (removed afterwards); `date -u` before/after in the tool log: Tue Oct  6 00:01:06 UTC 2026 / Tue Oct  6 00:01:41 UTC 2026
info: RBM3D.lean:272:0: axiom audit: 6693 theorems, 2257 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 122 (borrowed 1, owed 89, structural 26, refuted 6).
Build completed successfully (4032 jobs).      [exit 0; 'error' lines in the output: 0]
```
### b.2 `#print axioms` (script `axioms_all.lean`: every public `theorem`/`noncomputable def` of the file, 14 targets + 14 instances)
```
Sizes.expDrEGtLKM' [propext, Classical.choice, Quot.sound]
Sizes.expDrEGtK' [propext, Classical.choice, Quot.sound]
Sizes.expDr_Bctl_le_IV' [propext, Classical.choice, Quot.sound]
Sizes.expDr_envEGt' [propext, Classical.choice, Quot.sound]
Sizes.expDr_EGt_split' [propext, Classical.choice, Quot.sound]
Sizes.expDr_env_poly' [propext, Classical.choice, Quot.sound]
Sizes.expDr_expect' [propext, Classical.choice, Quot.sound]
Sizes.expDr_LK_prec' [propext, Classical.choice, Quot.sound]
Sizes.expDr_EGtLK_prec' [propext, Classical.choice, Quot.sound]
Sizes.expDr_EGtK_prec' [propext, Classical.choice, Quot.sound]
Sizes.STExpDriftLoConcl_of_LKU' [propext, Classical.choice, Quot.sound]
Sizes.stExpDriftLo_holds' [propext, Classical.choice, Quot.sound]
Sizes.STExpDriftDecayConcl_of_GdecayW' [propext, Classical.choice, Quot.sound]
Sizes.stExpDriftDecay_holds' [propext, Classical.choice, Quot.sound]
all 28 public declarations (14 targets + 14 instances): standard-three count = 28, other = 0
```
### b.3 Target statements (script: declaration keyword to `:=`, from the file; the two vocabulary bodies equal the check file's: `rfl` examples in b.5)
```
theorem expDr_Bctl_le_IV {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1)
    (hreg : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d) :
    sz.Bctl n u ≤ 2 * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹
theorem expDr_envEGt {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖sz.STEGt n E u σ a ω‖ ≤
      2 * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ 3)
theorem expDr_EGt_split {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpEGt n E u σ a =
      expDrEGtK sz n E u σ a + ∫ ω, expDrEGtLKM sz n E u (sz.seqHflow n u ω) σ a ∂(sz.seqP)
theorem expDr_env_poly {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ),
      ‖sz.STELKLK n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖sz.STEGt n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) ∧
      ‖expDrEGtLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ)
theorem expDr_expect {d : ℕ} (sz : Sizes d) {V : ℕ → Type} (X : ∀ n, V n → sz.SeqΩ → ℂ) (R : ∀ n, V n → ℝ)
    {Kenv Kf : ℝ} (hsz : sz.SizeTendsto)
    (henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hfloor : ∀ᶠ n in atTop, ∀ v, ((sz.size n : ℕ) : ℝ) ^ (-Kf) ≤ R n v)
    (hprec : sz.Prec (U := V) (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v)) :
    sz.Prec (U := V) (fun n v _ => ‖∫ ω, X n v ω ∂(sz.seqP)‖) (fun n v _ => R n v)
theorem expDr_LK_prec {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (hLKU : STLKU sz E s t) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)
theorem expDr_EGtLK_prec {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (hLKU : STLKU sz E s t) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖expDrEGtLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)
theorem expDr_EGtK_prec {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (_hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hAvg : STExpAvgU sz (STflowE z) s t) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p _ => ‖expDrEGtK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)
theorem STExpDriftLoConcl_of_LKU {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5IV sz s t) (hLKU : STLKU sz (STflowE z) s t)
    (hAvg : STExpAvgU sz (STflowE z) s t) : STExpDriftLoConcl sz (STflowE z) s t
theorem stExpDriftLo_holds (d : ℕ) : STExpDriftLo d
theorem STExpDriftDecayConcl_of_GdecayW {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hGd : STGdecayW sz (STflowE z) s t 0) :
    STExpDriftDecayConcl sz (STflowE z) s t
theorem stExpDriftDecay_holds (d : ℕ) : STExpDriftDecay d
noncomputable def expDrEGtLKM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ
noncomputable def expDrEGtK {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) : ℂ
```
### b.4 Compiled nonempty instances (same file, `namespace RBM.Gauss.Step6Inst`; the six of the ticket's target 4 are shown, the other eight are listed)
```
theorem inst_expDriftLo_holds :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB
      (fun _ => 5 / 8) (fun _ => 3 / 4)
theorem inst_expDriftDecay_holds :
    InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
theorem inst_skeleton6IV_Lo :
    STExpDuhamelZ 3 → STExpIntIV 3 →
      InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
theorem inst_skeleton6I_Dec :
    LWtermEXP 3 → STExpDuhamelZ 3 → STExpDuhamelQ 3 → STExpWardI 3 → STExpIntI 3 →
      InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
theorem inst_expDr_Bctl_le_IV :
    szG.Bctl 0 (3 / 4) ≤ 2 * (((szG.size 0 : ℕ) : ℝ) * (1 - 3 / 4))⁻¹
theorem inst_expDr_envEGt :
    ∀ ω : sz0.SeqΩ,
      ‖sz0.STEGt 0 (1 / 2) (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0] ω‖ ≤
        2 * (((sz0.W 0 : ℕ) : ℝ) ^ 3 * ((sz0.L 0 : ℕ) : ℝ) ^ 3) *
          (((etaT (1 / 2) (1 / 2))⁻¹ + 1) * (etaT (1 / 2) (1 / 2))⁻¹ ^ 3)
all 14 (line:name): 1070:inst_expDriftLo_holds 1076:inst_expDriftDecay_holds 1081:inst_skeleton6IV_Lo 1089:inst_skeleton6I_Dec 1096:inst_expDr_Bctl_le_IV 1101:inst_expDr_envEGt 1110:inst_expDr_EGt_split 1118:inst_expDr_env_poly 1128:inst_expDr_expect 1142:inst_expDr_LK_prec 1149:inst_expDr_EGtLK_prec 1156:inst_expDr_EGtK_prec 1164:inst_STExpDriftLoConcl_of_LKU 1171:inst_STExpDriftDecayConcl_of_GdecayW 
```
Data: regime (iv) `szG`, `zB`, `[5/8, 3/4]` (`N = 4096` at `n = 0`); regime (i) `szB`, `zB`, `[7/8, 15/16]`; one-size lemmas at `sz0`, `n = 0`.  Discharged: `3 ≤ 3`, `|1/2| < 2`, `1/2 < 1`, `1 - 3/4 ≤ szG.lam 0 ^ 2 / (szG.L 0)^3` (`25/64`), all `STFlow`/time-range/regime hypotheses (`flow_zG`, `flow_zB`, `szB_flow_ht`, `szG_reg4`).  Left as hypotheses: `STLKU`, `STExpAvgU`, `STGdecayW … 0` and the premises inside `InstIng6Concl` (`STLK`, `STDecay`, `STExp2`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW`), other gates' pins `LWtermEXP`, `STExpDuhamelZ/Q`, `STExpWardI`, `STExpIntI`, `STExpIntIV`, and the `≺` input of `inst_expDr_expect`.
### b.5 Check-file equality (scratch files in the scratchpad: the check file's imports + `import RBM3D.Induction.ExpEtermsB` + sections 1-2 + `example : T2228Check.X := @X` for the 12 pins, `rfl` for the two defs, `example (d : ℕ) : STExpDriftLo d := stExpDriftLo_holds d` and the same for `STExpDriftDecay`; second file: the six section-3 statements as `example : <stmt> := @RBM.Gauss.Step6Inst.<name>`)
```
$ lake env lean check_eq.lean; lake env lean check_inst.lean     (script wrapper prints:)
check_eq exit 0; examples: 16; 'error' lines: 0
check_inst exit 0; examples: 6; output lines:        0
```
### b.6 Name clash, registry pre-check, diff
```
$ bash clash2.sh   (grep -rl --include='*.lean' <name> RBM3D RBM3D.lean, excluding the file itself)
other files per name: expDrEGtLKM=0 expDrEGtK=0 expDr_=0 STExpDriftLoConcl_of_LKU=0 stExpDriftLo_holds=0 STExpDriftDecayConcl_of_GdecayW=0 stExpDriftDecay_holds=0 inst_expDriftLo_holds=0 inst_expDriftDecay_holds=0 inst_skeleton6IV_Lo=0 inst_skeleton6I_Dec=0 inst_STExpDriftLoConcl_of_LKU=0 inst_STExpDriftDecayConcl_of_GdecayW=0
inst_expDr_* (incl. inst_expDr_Bctl_le_IV, _envEGt, _EGt_split, _env_poly, _expect, _LK_prec, _EGtLK_prec, _EGtK_prec): 0 other files
T2228Check / ExpEtermsB elsewhere in RBM3D/ and RBM3D.lean: 0 files
$ printf 'import RBM3D\nimport RBM3D.Induction.ExpEtermsB\n\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean     # after `lake build RBM3D.Test.Axioms`; exit 0 (tool log), 33 s
axiom audit: 6693 theorems, 2257 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 122 (borrowed 1, owed 89, structural 26, refuted 6).
registry: 2 borrowed + 140 owed + 83 structural + 7 refuted; 110 registered premise(s) car
'STExpDriftLo,' / 'STExpDriftDecay,' lines in the precheck output (owed ledger / carry-nothing list): 0
'unregistered' lines: 0
owed entries at merge-base 37289f6: 142; at HEAD 62288d9: 140
$ git diff --stat main...t/T2228; git diff main -- RBM3D/Induction/Step6Pins.lean | wc -l; git diff main...t/T2228 -- RBM3D/Test/Axioms.lean | grep '^-[^-]' | cut -c1-70
 RBM3D/Induction/ExpEtermsB.lean | 1177 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |    2 -
 2 files changed, 1177 insertions(+), 2 deletions(-)
0
-   `RBM.Gauss.Sizes.STExpDriftLo, -- `6:63-66`, `6:73-79` drift bound in regime (iv): S6-07; S6-01 (T2204, DECISIONS §67: owed)
-   `RBM.Gauss.Sizes.STExpDriftDecay, -- `3_5:1634` drift decay: S6-07; S6-01 (T2204, DECISIONS §67: owed)
```
Ports: no RBM1D/RBM2D file was opened, so there is no RBM1D/RBM2D diff-stat.  Copied from merged RBM3D files (last commits `git log -1 --format=%h -- <file>`): `expLK_first_moment` (`Induction/ExpEtermsA.lean:461`, `cd6fcba`) to `expDr_first_moment`; the column-sum argument of `expLK_window_le` (`:54-90`) to `expDr_hcol`, `expDr_bilin_le`; the arithmetic of `expLK_env_poly` (`:245`) to `expDr_env_poly`; `KLFinal_flowLam` (`Loop/KLFinal.lean:294`, `471b643`) to `expDr_flowLam`.  The RBM2D pointers in the module docstring (`MLExpDrift.lean` `:610`, `:717`, `:1092`, `:1230`, `c9a24cf`) are the ticket's/T2222's, not re-read.

### b.7 Narrative
1. `RBM3D/Induction/ExpEtermsB.lean`, 1177 lines (below the 1500-line fallback: no split): §0 vocabulary, §1 `expDr_Bctl_le_IV`, `expDr_envEGt` (+ private `expDr_hcol`, `expDr_bilin_le`, `expDr_cuts_le`), §2 `expDr_EGt_split`, §3 `expDr_env_poly`, §4 `expDr_expect`, `expDr_LK_prec`, `expDr_EGtLK_prec`, `expDr_EGtK_prec`, §5 `STExpDriftLoConcl_of_LKU`, `stExpDriftLo_holds`, §6 `STExpDriftDecayConcl_of_GdecayW`, `stExpDriftDecay_holds`, §7 instances.
2. Statements equal the check file's (b.5); no hypothesis added or removed, no merged signature changed (`Step6Pins.lean` diff is empty).  One binder is named `_hε` in `expDr_EGtK_prec` (unused there; the type is unchanged).  Eight instances beyond target 4 cover the other public theorems; section (a) was used unchanged, no (a′).
3. (iv): `D_u = 𝔼ℰ^{LK×LK} + A + 𝔼X_B`; `expDr_EGt_split` is `STLM = STKloop + STLKM` pointwise plus `integral_sub`/`integral_finsetSum`/`integral_mul_const` (`avg` and `ℰ^{G̃}` are bounded by `expDr_envEGt` and measurable by `walk_measurable_Lloop`).  `ℰ^{LK×LK}` uses `STLKU … 2`, `X_B` uses `STLKU … 1` and `… 3` (`StochDomAt.of_subset_union`, `τ' = τ/3`), `A` uses `STExpAvgU` and `stKbound_timeIcc … 3` through `st6_prec_det_iff`.
4. `expDr_expect` is applied twice with `Kenv = 6` (`expDr_env_poly`) and `Kf = 3` (private `expDr_floor`: `B ≥ N⁻¹`).  The assembly applies `st6_prec_det_iff` at `τ/2` to the three pieces, `N B⁴ ≤ 16 R_u` (`expDr_Bctl_le_IV`), and `48 ≤ N^{τ/2}` eventually, so `|D| ≤ N^τ R_u`.  The `112`/`τ/4` bookkeeping of (a) is not used (same truth, different constants).
5. `STReg5IV` enters only through `1-u ≤ 1-s ≤ λ²/L^d` in the call of `expDr_Bctl_le_IV`; the three random estimates use no regime.  `STReg5I` is unused in the decay pin.
6. Decay: `stDecayLoopU_of_step2 … 0`, then `stEtermDecay … 2` at `(ε', D+1)` for `STegt` and `STelklk` (bridges `STEGtM_eq_STegtM`, `STegtM_seqHflow`, `STELKLKM_eq_STelklkM`, `STelklkM_seqHflow`; `KLloopOf σ a = ⟨List.ofFn σ, List.ofFn a⟩` is by definition).  First moment with `HighProbAt` at `D+7`, envelope `N⁶`, `W ≤ N` (`expDr_W_le_size`): `|𝔼ℰ| ≤ 2 W^{-(D+1)}`; `|D_v(a)| ≤ 4 W^{-(D+1)} ≤ W^{-D}` for `W ≥ 4` (eventually, from `Bandwidth`, `N → ∞`).  `STEKDecay` closes with an eventually-empty failure set.
7. Premises used.  `stExpDriftLo_holds` (`𝔠_d = 1/100`): `STFlow`, `0 ≤ s`, `s < t` (as `≤`), `t ≤ lemT z`, `STReg5IV`, `STLKU`, `STExpAvgU`.  `stExpDriftDecay_holds` (`𝔠_d = 1/100`): `STFlow`, `0 ≤ s`, `s < t`, `t ≤ lemT z`, `STGdecayW … 0`.  The other `STIngR6` premises are unused (see the docstrings).
8. §29/§45 O2 lines: (1) `0 ≤ s ≤ u ≤ t ≤ lemT z < 1` (`st5_t_lt_one`), `1-u > 0` in every use; (2) as 5; (3) only `N = W^d L^d`, `W ≥ N^𝔠` (`Bandwidth`), `W ≤ N`; (4) hypotheses `∀ n`, conclusions `∀ᶠ n` (statements in b.3); (5) every input is uniform in `u` (`TimeIcc` inside `Prec` and `Whp`), no per-time clause, no grid lift; (6) `0 < lam n` only eventually (`expDr_flowLam`, for `stKbound_timeIcc`); (7) scale `sz.size n`; no mollifier constants.
9. Consumers: `stExpDriftLo_holds 3` and `stExpDriftDecay_holds 3` are accepted by the merged `inst_expDriftLo`, `inst_expDriftDecay`, `inst_skeleton6IV_avg`, `inst_skeleton6I'` (the instances `inst_expDriftLo_holds`, `inst_expDriftDecay_holds`, `inst_skeleton6IV_Lo`, `inst_skeleton6I_Dec` compile); `example (d : ℕ) : STExpDriftLo d := stExpDriftLo_holds d` and the Decay twin compile (b.5).
10. Registry: the two owed lines are deleted (142 to 140 entries); the file defines no public `Prop`, nothing was registered.  Merge note for the hub: T2224 deletes the two lines directly above in the same list; keep all four deleted; the root import `RBM3D.Induction.ExpEtermsB` is the hub's (my temporary root import was removed: `git status --short` shows only `RBM3D/Test/Axioms.lean` modified and the new file before the commit).

## (c) Verified Mathlib names (each compiled in `lake build RBM3D.Induction.ExpEtermsB`)
- `MeasureTheory.Integrable.of_bound` (`hf.aestronglyMeasurable C (Eventually.of_forall …)`, finite measure); `MeasureTheory.integrable_finsetSum`, `MeasureTheory.integral_finsetSum`; `Integrable.const_mul`, `.mul_const`, `.add`, `.sub`, `integrable_const`.
- `MeasureTheory.integral_add`, `integral_sub`, `integral_const`, `integral_const_mul`, `integral_mul_const`, `integral_mono_of_nonneg`, `integral_indicator_const`, `norm_integral_le_integral_norm`, `measure_toMeasurable`, `measurableSet_toMeasurable`, `subset_toMeasurable`, `measure_empty`.
- `Finset.measurable_sum`, `measurable_const`, `Measurable.mul_const`, `.sub_const`, `.add`, `.mul`; `Finset.sum_add_distrib`, `sum_comm`, `sum_const`, `card_univ`, `mul_sum`; `Matrix.transpose_apply`.
- `ENNReal.toReal_le_of_le_ofReal`; `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_natCast`, `Real.rpow_one`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`; `tendsto_rpow_atTop`; `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`; `Nat.le_self_pow`, `Nat.le_mul_of_pos_right`; `Complex.norm_natCast`, `Complex.im_le_norm`.
- Deprecated in this Mathlib (replaced): `integral_finset_sum`, `integrable_finset_sum` (aliases of `…finsetSum`, `since 2026-04-08`, `Bochner/Basic.lean:253`, `L1Space/Integrable.lean:455`); `Set.mem_setOf_eq` (warning: use `Set.mem_ofPred_eq`, from the tool log).

## (d) Open issues and paper-delta candidates
- No step needed a hypothesis a pin lacks: no primed successor, no `T2228a` in the sense of the ticket's last bullet; both merged pins are proved as stated.
- `T2228a` (candidate): `(deccA0)` for `D_u` (`STExpDriftDecay`, `3_5:1634`) holds in every regime; `STReg5I` is not used.
- `T2228b` (candidate; paper side as given by the ticket): `6:65`, `6:77` write `≺ W^d L^d (N|1-u|)^{-4}`; the Lean proof gets it from `B_{u,0} ≤ 2 (L^d(1-u))⁻¹` (regime (iv)), constant `2⁴ = 16`, and a factor `3` for the three drift pieces, absorbed in `N^{τ/2} ≥ 48`.
- `T2228c` (candidate; paper side as given by the ticket): `6:78` cites `(eq:bcal_k)` with `n = 3`; the Lean proof uses it uniformly in `u` (`stKbound_timeIcc`), and the (iv) bound of `ℰ^{LK×LK}` needs no regime (only its comparison with `R_u` does).
- `T2228d` (candidate; the TeX was not re-read in this stage): the Lean step `≺ → 𝔼` needs a polynomial envelope `N⁶` (`expDr_env_poly`) and a floor `R ≥ N^{-3}` (`B ≥ N⁻¹`); whether the paper states them at `6:65`, `6:77` was not checked here.
- Hub: add `import RBM3D.Induction.ExpEtermsB` to `RBM3D.lean` after the last `import` line; the registry deletion and the import are committed together (ticket merge note).
