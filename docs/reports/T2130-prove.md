Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 11:15:09 UTC 2026

Notation: `N = sz.size n = (WL)^d`, `g = sz.lam n`, `Bctl = W^{-d}B_{u,0}`, `STWB(u,r) = W^{-d}B_{u,r}`, `B_{u,K} = (g²+1-u)⁻¹(K+1)^{-(d-2)} + (L^d(1-u))⁻¹` (`Defs/Params.lean:36`). Merged inputs used: `ST_Bdata_holds` (`Induction/Step2Iterate.lean:1049`, pin `STBdata`, `Step2Events.lean:209`), `STBctl_mono` (`ScaleFacts.lean:74`), `ST_one_sub_lemT` (`Step2Iterate.lean:1014`).

### (i) Exponent table

| # | Quantity | Value | Constraint | Slack |
|---|---|---|---|---|
| 1 | `c` (size data) | `min(2𝔡𝔠, ε)/2` | `ST_Bdata_holds`, eventually in `n`, all `u ∈ [0, lemT z_n]`: `Bctl(u) ≤ N^{-c}` (from `(eq:WO)` `g ≥ W^{-d/2+𝔡}`, `W ≥ N^𝔠`, `Im z ≥ N^{-1+ε}`, `1-u ≥ 1-lemT z ≥ Im z/4`) | explicit |
| 2 | `cB` | `(𝔡⁻²+1)⁻¹` | `ST_Bdata_holds`: `cB W^{-d} ≤ Bctl(u)` (uses `g ≤ 𝔡⁻¹`, `0 ≤ u < 1`) | explicit |
| 3 | `ε₀` (fixed, flow regime) | `min(1, c·d/8)` | (a) `Bctl^{1/4} ≤ W^{-ε₀}`: `N^{-c} ≤ W^{-4ε₀}` since `W^d ≤ N` gives `W^{-4ε₀} ≥ N^{-4ε₀/d}`; needs `4ε₀ ≤ c d`. (b) window top `W^{-d/2} ≤ W^{-ε₀}` needs `ε₀ ≤ d/2` | (a) `c d/2` vs `c d` (factor 2); (b) `1 ≤ d/2 = 3/2` |
| 4 | `Ψ_u` (item 1) | `max(W^{-d/2}, Bctl(u)^{1/2})` | window `W^{-d/2} ≤ Ψ_u ≤ W^{-ε₀}`: lower trivial; upper `Bctl^{1/2} ≤ N^{-c/2} ≤ W^{-2ε₀} ≤ W^{-ε₀}` | `Ψ_u ≤ W^{-2ε₀}` if `ε₀ ≤ d/4`; here `W^{-d/2}` vs `W^{-ε₀}`: `d/2 - ε₀ ≥ 1` |
| 5 | why the `max` | `Bctl ≥ cB W^{-d}` with `cB < 1` | `Bctl^{1/2}` alone may be `< W^{-d/2}` (lower window fails) if `g` large; with the `max`, `Ψ_u² = max(W^{-d}, Bctl) ≤ cB⁻¹ Bctl = (𝔡⁻²+1) Bctl` | constant `𝔡⁻²+1` (a constant multiple of the paper's `Ψ_u = Bctl^{1/2}`: delta candidate `T2130a`, as T2040a) |
| 6 | item 1, part 1 | `‖G_u-M‖_max ≺ W^{-ε₀}` | from `STStep1Weak` (`≺ Bctl^{1/4}`, `Prec` at the section `u n ∈ [s n, t n]`: a sub-index of the union over `TimeIcc`) and row 3(a) | `N^{-c/4}` vs `W^{-ε₀} ≥ N^{-ε₀/d}`: any `τ < c/4 - ε₀/d` works; for `ε₀ = c d/8` this is `c/8`; at the instance `c/4 - ε₀/d = 1/60·(1/4) - 1/480 = 1/480` |
| 7 | item 1, part 2 | `max_{a,b}‖𝓛^{(2)}_{u,(-,+),(a,b)}‖ ≺ Ψ_u²` | `STL2decayPT` is `PrecPT` (union over `(a,b)` outside `P`): `‖𝓛^{(2)}‖ ≺ STWB(u,|a-b|) ≤ STWB(u,0) = Bctl` (`B_{u,K}` nonincreasing in `K`, `d ≥ 2`; `Bctl ≤ Ψ²`). `PrecPT → Prec` by a union bound over `L^{2d} ≤ N²` pairs: the pair `(τ, D)` of the statement becomes `(τ, D+2)` | `N^{-D'}·N² ≤ N^{-D}` for `D' = D+2`; no exponent lost |
| 8 | item 2 | `STStep2AvgPT` | `STGavLGEX` at `ε₀` (section `u`, `0 ≤ u n ≤ lemT`): `≺ Ψ_u² ≤ (𝔡⁻²+1) Bctl`; constant absorbed by `N^τ`; `Prec` over `a` → `PrecPT` over `(u,a)` by `perTimeOfStochDomAt` + `perTime_timeIcc_of_forall_seq` | constant `𝔡⁻²+1` |
| 9 | item 3, indicator | `1(Ω(u,ε₀))` removed | `Ω ⊇ E := {‖G-M‖_max ≤ N^τ Bctl^{1/4}}` eventually (row 3(a), `τ ≤ c/4-ε₀/d`), `P(E^c) ≤ N^{-D}` for all `D` (`Prec.whp` of `STStep1Weak`) | `τ_max = c/4 - ε₀/d` |
| 10 | item 3, diagonal and same block | `|G_xy-M_xy|² ≺ STWB(u,0)` | `GiiGEX` (`≺ max_{a,b} 𝓛^{(2)}`), then row 7 | `Bctl` exactly |
| 11 | `(+,−)` charge in `STgexRHS` | `𝓛_{(+,-),(a,b)} = 𝓛_{(-,+),(b,a)}` | trace cyclicity: `tr(G E_a G* E_b) = tr(G* E_b G E_a)`; then `STL2decayPT` at `(b,a)`, `zdistInf(b-a) = zdistInf(a-b)` | exact identity, constant 1 |
| 12 | neighbour sums | `|a'-a| ≤ 1`, `|b'-b| ≤ 1` (`L^∞`) | `|r'-r| ≤ 2` for `r = |a-b|`, `r' = |a'-b'|` (triangle inequality of `zdistInf`); `STWB(u,r') ≤ C_B STWB(u,r)`, `C_B = 3^{d-2}` (for `r' ≥ r`: `B` nonincreasing; for `r' ≥ r-2`: `(K+1)^{-(d-2)}` ratio `≤ ((r'+3)/(r'+1))^{d-2} ≤ 3^{d-2}`, equality at `r'=0, r=2`) | `C_B = 3` at `d = 3` (script: max `2.9985`) |
| 13 | number of terms | `2·(3^d)² = 1458` (`d=3`) | finitely many events (independent of `n`): union bound `1458 N^{-D'} ≤ N^{-D}` eventually | `D' = D+1` |
| 14 | `W^{-d}1_{|a-b|≤1}` vs `STWB` | `C_1 = 2^{d-2}(𝔡⁻²+1)` | for `r ≤ 1`: `B_{u,r} ≥ (g²+1)⁻¹ (r+1)^{-(d-2)} ≥ (𝔡⁻²+1)⁻¹ 2^{-(d-2)}`; the ticket's feared failure does not occur | `C_1 = 2.0005` at `g = 1/64`, `d = 3` (script: max `1/B_{u,1}` = `1.9399, 1.9922, 1.9990` at `n = 0, 1, 3`) |
| 15 | §29 (1) time | `0 ≤ s ≤ u ≤ t ≤ lemT z < 1` | `lemT_lt_one`; `Bparam` at `u < 1` (`|1-u| = 1-u`) | strict `< 1` |
| 16 | §29 (2),(3) | not used | no use of `ilambda > L` or of `L^d ≤ W^K`; only `N = (WL)^d` (`L^{2d} ≤ N²`, `W^d ≤ N`) | n/a |
| 17 | §29 (4) quantifiers | `∃ ε₀` fixed before `∀ᶠ n`; every size fact `∀ᶠ n` | `ST_Bdata_holds` is `∀ᶠ n`; the pins `STGbEXP*` are for every `ε₀ > 0` and every time sequence `0 ≤ t n ≤ lemT` (applied at `t := u`); `STInitialGT2`, `Prec` are `∀τ ∀D ∀ᶠ n` | no `∀ n` forced |
| 18 | §29 `Prec` vs `PrecPT` | hypotheses: `STStep1Weak` `Prec`, `STL2decayPT` `PrecPT`; conclusions: `STStep2LocalPT`, `STStep2AvgPT` `PrecPT` | chain `PrecPT(L2) → Prec (finite union, row 7) → GbEXP (Prec, one time sequence) → PrecPT` (`perTimeOfStochDomAt`, then `perTime_timeIcc_of_forall_seq`: statement per time `u ∈ TimeIcc` from the statement at every section) | the union over `x,y` (`N²`) is inside `P` for `GiiGEX/GijGEX`, then split to per-pair events with `N^{-D-2}` |
| 19 | the pin | `STLocalAvgOfL2 d` at `3 ≤ d` | needs `hd : 3 ≤ d` only through `stGbEXP_holds` (DECISIONS §36 (i)); `ST_Bdata_holds` needs `0 < d` | n/a |

Row 6/9 slack: `τ_max = c/4 - ε₀/d > 0` because `ε₀ ≤ c d/8` gives `ε₀/d ≤ c/8 < c/4`; the instance value is `0.0020833 = 1/480` (script line 1).

### (ii) One concrete nondegenerate instance

`d = 3`, merged flow instance `sz0`, `z0` (`Induction/Defs.lean:413`, `Defs/Sizes.lean:260`): `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`, `z0_n = 1/2 + i N^{-4/5}`; `𝔠 = 1/6`, `𝔡 = κ = ε = 1/10`; time range `u ∈ [0, lemT z0_n]` (`s = 0`, `t = lemT`, the widest). `msc` is the root of `m² + z m + 1 = 0` with `Im m > 0`, `|m| < 1`. All deterministic hypotheses of items 1-3 are checked below at `n = 0, 1, 3`; the stochastic hypotheses `STStep1Weak`, `STL2decayPT` are external (other gates' outputs).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2130/inst.py` (mpmath, 40 digits, 2001 times `u` per `n`):
```
c=0.01666666666666666666666666666666666666667 cB=0.009900990099009900990099009900990099009901 eps0=0.00625 tau_max=0.002083333333333333333333333333333333333333
window chain: 4*eps0=0.025 <= c*d=0.05 ; eps0<=d/2 : True

n=0 L=4 W=32 N=2097152 lam=1.562e-02 eta=8.764e-06 lemT=0.999990948752 1-lemT=9.051e-06
  Im z/(1+|z|)=5.843e-06 <= 1-lemT : True
  u in [0,lemT]: max Bctl=1.7321e-01 (at lemT), Bctl^(1/4)=0.6451, sqrt=0.4162 ; W^-eps0=0.978572 (eps0=0.00625) N^-c=0.7846
  min W^d*Bctl=1.01538 >= cB=0.00990 ; all window/Bdata checks at eps0: True
  at eps0=0.1: Bctl(lemT)^(1/4)=0.6451 <= W^-0.1=0.7071 : True ; W^{-d/2}=5.5243e-03 <= Psi=4.1619e-01
  max B_{u,r'}/B_{u,r} (|r-r'|<=2, r<=L/2=2) = 2.9104 <= 3^(d-2)=3 ; max 1/B_{u,1} = 1.9399 <= 2^(d-2)(g^2+1)=2.0005

n=1 L=8 W=1024 N=549755813888 lam=2.441e-04 eta=4.054e-10 lemT=0.999999999581 1-lemT=4.187e-10
  Im z/(1+|z|)=2.703e-10 <= 1-lemT : True
  u in [0,lemT]: max Bctl=1.9861e-02 (at lemT), Bctl^(1/4)=0.3754, sqrt=0.1409 ; W^-eps0=0.957603 (eps0=0.00625) N^-c=0.6373
  min W^d*Bctl=1.00195 >= cB=0.00990 ; all window/Bdata checks at eps0: True
  at eps0=0.1: Bctl(lemT)^(1/4)=0.3754 <= W^-0.1=0.5000 : True ; W^{-d/2}=3.0518e-05 <= Psi=1.4093e-01
  max B_{u,r'}/B_{u,r} (|r-r'|<=2, r<=L/2=4) = 2.9883 <= 3^(d-2)=3 ; max 1/B_{u,1} = 1.9922 <= 2^(d-2)(g^2+1)=2.0000

n=3 L=16 W=32768 N=144115188075855872 lam=3.815e-06 eta=1.875e-14 lemT=1.0 1-lemT=1.937e-14
  Im z/(1+|z|)=1.250e-14 <= 1-lemT : True
  u in [0,lemT]: max Bctl=2.3088e-03 (at lemT), Bctl^(1/4)=0.2192, sqrt=0.0481 ; W^-eps0=0.937084 (eps0=0.00625) N^-c=0.5176
  min W^d*Bctl=1.00024 >= cB=0.00990 ; all window/Bdata checks at eps0: True
  at eps0=0.1: Bctl(lemT)^(1/4)=0.2192 <= W^-0.1=0.3536 : True ; W^{-d/2}=1.6859e-07 <= Psi=4.8050e-02
  max B_{u,r'}/B_{u,r} (|r-r'|<=2, r<=L/2=8) = 2.9985 <= 3^(d-2)=3 ; max 1/B_{u,1} = 1.9990 <= 2^(d-2)(g^2+1)=2.0000

sup_r (r+1)/(r-1) for r>=2 = 3  (so C_B = 3^(d-2) = 3)
counts: neighbours 3^d=27 per index; terms of STgexRHS sum 2*(3^d)^2=1458 ; L^(2d) pairs at n=0: 4096 <= N^2=4398046511104
```
Reading: at `n = 0` the window `W^{-3/2} = 0.0055 ≤ Ψ_u = 0.416 ≤ W^{-ε₀}` holds even at the practical `ε₀ = 0.1` (`0.707`); the slack there at `u = lemT` is `Bctl^{1/4} = 0.645` vs `0.707`. The proved `ε₀ = 1/160` is conservative (`W^{-ε₀} = 0.9786`). Mixed-charge ratio `max B_{u,r'}/B_{u,r}` is below `3^{d-2} = 3` and tends to `3` as `n` grows (`L` grows, `r = 2, r' = 0`).

External-hypothesis limit (TEAM §8 lesson 14): the controls tend to zero along `sz0`, so `STStep1Weak` and `STL2decayPT` are nonvacuous: `Bctl(lemT)`: `0.1732, 0.01986, 0.002309` at `n = 0, 1, 3` (`≤ N^{-c}` with `N^{-c} → 0`, `c = 1/60`), hence `Bctl^{1/4} → 0` and `STWB(u,r) ≤ Bctl → 0` uniformly in `u ∈ [0, lemT]` (monotone `STBctl_mono`).

### Verdicts
- Item 1 (`STInitialGT2` at every time, `Ψ_u = max(W^{-d/2}, Bctl^{1/2})`, `ε₀ = min(1, c d/8)`, `c = min(2𝔡𝔠, ε)/2`): **PASS** (rows 3-7; window holds; `Ψ_u ≤ W^{-ε₀}` comes from `Bctl ≤ N^{-c}` for `t ≤ lemT z`, i.e. `1-u ≥ 1-lemT z ≥ Im z/4`).
- Item 2 (`STStep2AvgPT`): **PASS** (row 8; constant `𝔡⁻²+1`).
- Item 3 (`STStep2LocalPT`): **PASS** (rows 9-14; `STgexRHS` is `≤ C·STWB` with `C = 2(3^d)²·3^{d-2} + 2^{d-2}(𝔡⁻²+1)`, including the `W^{-d}1_{|a-b|≤1}` term; `(+,−)` reduces to `(−,+)` by trace cyclicity).
- Item 4 (`stLocalAvgOfL2_holds (hd : 3 ≤ d)`): **PASS** (items 2-3; row 19).
Paper-delta candidate: `T2130a` `Ψ_u = max(W^{-d/2}, Bctl^{1/2})` (paper `Bctl^{1/2}`; lower window needs `Bctl ≥ cB W^{-d}`, `cB = (𝔡⁻²+1)⁻¹ < 1`).

## (b) Script output (written Sun Oct  4 11:38:47 UTC 2026; branch t/T2130, last two commits 4a77b2b 27fa5b2: 4a77b2b is docstring-only on top of 27fa5b2)

### b.1 Build, warnings, forbidden tokens
$ lake build RBM3D.Induction.LocalAvg1 RBM3D.Induction.LocalAvg2 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3787 jobs).
$ lake env lean RBM3D/Induction/LocalAvg1.lean; echo exit=$?   (same for LocalAvg2.lean)  [no output = no warning]
LocalAvg1: exit=0 output_lines=0
LocalAvg2: exit=0 output_lines=0
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/LocalAvg[12].lean | wc -l
0

### b.2 `#print axioms` of every new public declaration (scratch file `import RBM3D.Induction.LocalAvg2` + 19 lines)
'stLocalPsi': [propext, Classical.choice, Quot.sound]
'localAvg1_stochDomAt_of_whp': [propext, Classical.choice, Quot.sound]
'localAvg1_domAt_of_le_const': [propext, Classical.choice, Quot.sound]
'localAvg1_perTime_of_stoch': [propext, Classical.choice, Quot.sound]
'localAvg1_STWB_le': [propext, Classical.choice, Quot.sound]
'localAvg1_STWB_ge': [propext, Classical.choice, Quot.sound]
'localAvg1_STWB_comp': [propext, Classical.choice, Quot.sound]
'localAvg1_rpow_half_sq': [propext, Classical.choice, Quot.sound]
'localAvg1_det': [propext, Classical.choice, Quot.sound]
'localAvg1_data': [propext, Classical.choice, Quot.sound]
'localAvg1_whp_L2': [propext, Classical.choice, Quot.sound]
'localAvg1_whp_omega': [propext, Classical.choice, Quot.sound]
'localAvg1_maxLoop2_le': [propext, Classical.choice, Quot.sound]
'stInitialGT2_of_L2decay': [propext, Classical.choice, Quot.sound]
'stStep2AvgPT_of_L2decay': [propext, Classical.choice, Quot.sound]
'localAvg2_rhs_le': [propext, Classical.choice, Quot.sound]
'localAvg2_entry_le': [propext, Classical.choice, Quot.sound]
'stStep2LocalPT_of_L2decay': [propext, Classical.choice, Quot.sound]
'stLocalAvgOfL2_holds': [propext, Classical.choice, Quot.sound]

### b.3 Target statements, extracted by script (`RBM3D/Induction/LocalAvg{1,2}.lean`)
RBM3D/Induction/LocalAvg1.lean:166
def stLocalPsi (sz : Sizes d) (u : ℕ → ℝ) (n : ℕ) : ℝ
RBM3D/Induction/LocalAvg1.lean:343
theorem stInitialGT2_of_L2decay (hd : 0 < d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {𝔠 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ lemT (z n))
    (hweak : STStep1Weak sz (STflowE z) s t) (hL2 : STL2decayPT sz (STflowE z) s t) :
    ∃ ε₀ CΨ : ℝ, 0 < ε₀ ∧ 0 < CΨ ∧ ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ stLocalPsi sz u n ∧
        stLocalPsi sz u n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧
        sz.Bctl n (u n) ≤ stLocalPsi sz u n ^ 2 ∧
        stLocalPsi sz u n ^ 2 ≤ CΨ * sz.Bctl n (u n)) ∧
      STInitialGT2 sz (STflowE z) u ε₀ (stLocalPsi sz u)
RBM3D/Induction/LocalAvg1.lean:406
theorem stStep2AvgPT_of_L2decay (hd : 3 ≤ d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {𝔠 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ lemT (z n))
    (hweak : STStep1Weak sz (STflowE z) s t) (hL2 : STL2decayPT sz (STflowE z) s t) :
    STStep2AvgPT sz (STflowE z) s t
RBM3D/Induction/LocalAvg2.lean:321
theorem stStep2LocalPT_of_L2decay (hd : 3 ≤ d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {𝔠 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ lemT (z n))
    (hweak : STStep1Weak sz (STflowE z) s t) (hL2 : STL2decayPT sz (STflowE z) s t) :
    STStep2LocalPT sz (STflowE z) s t
RBM3D/Induction/LocalAvg2.lean:394
theorem stLocalAvgOfL2_holds {d : ℕ} (hd : 3 ≤ d) : STLocalAvgOfL2 d

### b.4 The compiled nonempty instances (statements of the six `example`s, extracted; proofs are in the files)
-- LocalAvg1.lean:453
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    ∃ ε₀ CΨ : ℝ, 0 < ε₀ ∧ 0 < CΨ ∧
      (∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤
          stLocalPsi sz0 (fun _ => 1 / 32) n ∧
        stLocalPsi sz0 (fun _ => 1 / 32) n ≤ ((sz0.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
      STInitialGT2 sz0 (STflowE z0) (fun _ => 1 / 32) ε₀ (stLocalPsi sz0 (fun _ => 1 / 32))
-- LocalAvg1.lean:468
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    STStep2AvgPT sz0 (STflowE z0) sInst tInst
-- LocalAvg2.lean:413
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    STStep2LocalPT sz0 (STflowE z0) sInst tInst
-- LocalAvg2.lean:420
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    STStep2LocalPT sz0 (STflowE z0) sInst tInst ∧ STStep2AvgPT sz0 (STflowE z0) sInst tInst
-- LocalAvg2.lean:428
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3)
    (hOpt : STOptL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd)
-- LocalAvg2.lean:437
example {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hMart : STGridMart d)
    (hOpt : STOptL2 d) : STStep2 d

### b.5 Name-clash grep (new public names against the rest of `RBM3D/`, worktree = main + this commit)
$ for n in stLocalPsi stInitialGT2_of_L2decay stStep2AvgPT_of_L2decay stStep2LocalPT_of_L2decay stLocalAvgOfL2_holds localAvg1_ localAvg2_; do grep -rn --include='*.lean' "$n" RBM3D | grep -v 'RBM3D/Induction/LocalAvg[12].lean' | wc -l; done
stLocalPsi=0 stInitialGT2_of_L2decay=0 stStep2AvgPT_of_L2decay=0 stStep2LocalPT_of_L2decay=0 stLocalAvgOfL2_holds=0 localAvg1_=0 localAvg2_=0

### b.6 Registry pre-check and full build
The unmodified branch fails `lake build` at the root only (DECISIONS §20 blind spot: the root does not import the new modules, so `STLocalAvgOfL2` is unproved and, after the line removal, unregistered):
684:error: RBM3D.lean:176:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
685:  [RBM.Gauss.Sizes.STLocalAvgOfL2]
686:Classify each of them: borrowed from the literature, owed by this formalization, or a predicate that defines the objects under study.
687:Some required targets logged failures:
689:error: build failed
With the two imports temporarily added to RBM3D.lean after `import RBM3D.Green.GbEXP` (what the hub does at merge; reverted by `git checkout -- RBM3D.lean`, not committed), `lake build`, then the pre-check file:
683:info: RBM3D.lean:178:0: axiom audit: 3958 theorems, 1362 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
788:premises found by scanning: 73 (borrowed 1, owed 57, structural 15).
789:registry: 5 borrowed + 94 owed + 39 structural; 65 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
855:Build completed successfully (3879 jobs).
$ cat precheck.lean   # import RBM3D / import RBM3D.Induction.LocalAvg1 / import RBM3D.Induction.LocalAvg2 / #assert_rbm_axioms ; lake env lean precheck.lean > out; echo exit=$?
exit=0 (this run); lines containing 'error' in the output: 0
1:axiom audit: 3958 theorems, 1362 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
106:premises found by scanning: 73 (borrowed 1, owed 57, structural 15).
107:registry: 5 borrowed + 94 owed + 39 structural; 65 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,

### b.7 Diff scope and ports
$ git diff --stat main...t/T2130
 RBM3D/Induction/LocalAvg1.lean | 474 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/LocalAvg2.lean | 441 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |   1 -
 3 files changed, 915 insertions(+), 1 deletion(-)
Ports from RBM1D/RBM2D: none (RBM2D `Path/Step2Local.lean` not used). Copies inside RBM3D (private, `la2_` prefix): `Green/Pins.lean:494` (`loopFine_mp_eq_pm`), `:501` (`zdistInf_neg`), `:506` (`zdist_le_one`), `:523` (`card_ball_le`), `:1303` (`zdistInf_zero`); `Evolution/PropTInf.lean:43` (`zdistInf_add_le`); same statements with `L` generic.

### b.8 Narrative (no build history)
All three conclusions are `PrecPT` statements; each is reduced to time sections: `Green.perTime_timeIcc_of_forall_seq` (`Green/Pins.lean:243`) turns `PrecPT` over `TimeIcc s t × V` into `PerTimeDomAt` over `Unit × V` at every `u_n ∈ [s_n,t_n]`, which follows from `Prec` over `V` at the section (`localAvg1_perTime_of_stoch`). Hypotheses are those of `STLocalAvgOfL2` plus `3 ≤ d` (items 2-4); no other hypothesis was added and no merged statement changed.
- Size data (`localAvg1_data`, from `ST_Bdata_holds`, `Step2Iterate.lean:1049`; `cB = (𝔡⁻²+1)⁻¹` at `:1051`, `c = min(2𝔡𝔠, ε)/2` at `:1054`): eventually in `n`, for `0 ≤ u ≤ t_n ≤ lemT z_n`, `cB W^{-d} ≤ Bctl ≤ N^{-c}`. This is where `t ≤ lemT z` enters.
- Item 1 (`stInitialGT2_of_L2decay`, needs only `0 < d`): `ε₀ = min(1/2, d c/8)`, `CΨ = cB⁻¹ + 1`, `Ψ_u = max(W^{-d/2}, Bctl^{1/2})` (`stLocalPsi`). Window: `W^{-d/2} ≤ W^{-ε₀}` since `ε₀ ≤ 1/2 ≤ d/2`; `Bctl^{1/2} ≤ N^{-c/2} ≤ W^{-dc/2} ≤ W^{-ε₀}` (`ST_size_rpow_neg_le`: `N^{-c} ≤ W^{-dc}`). `Bctl ≤ Ψ² ≤ W^{-d} + Bctl ≤ CΨ Bctl`.
  Part 1: the weak law at `τ₀ = c/8` gives `‖G_u-M‖_max ≤ N^{c/8} Bctl^{1/4} ≤ N^{-c/8} ≤ W^{-ε₀}` w.h.p. (`localAvg1_whp_omega`, `localAvg1_det`). Part 2: `(eq:L2_decay)` at the section, union over the `≤ N²` pairs `(a,b)` (`Path.highProbAt_iInter`, `D ↦ D+2`), then `max_{a,b} 𝓛^{(2)} ≤ N^τ Bctl ≤ N^τ Ψ²` (`B_{u,K}` is non-increasing in `K`: `localAvg1_STWB_le`).
- Item 2: `(GavLGEX)` (`stGbEXP_holds`, third part) at `(u, ε₀, Ψ_u)` gives `≺ Ψ_u²`; `Ψ_u² ≤ CΨ Bctl` is absorbed by `N^{τ/2}` (`localAvg1_domAt_of_le_const`).
- Item 3: the indicator `1(Ω(u,ε₀))` is removed by the high-probability event `Ω` (item 1, part 1). At `τ > 0`, the events `Ω`, `(GijGEX)`, `(GiiGEX)` (from `Prec.whp` of `stGbEXP_holds` parts 2, 1, at `τ/3`) and `(eq:L2_decay)` at `τ/3` hold together w.h.p. (`HighProbAt.inter` three times). `(+,−)` reduces to `(−,+)` by trace cyclicity, `𝓛_{(+,-),(a,b)} = 𝓛_{(-,+),(b,a)}` (`Matrix.trace_mul_comm`, `la2_loop_pm`), and `|[b'-a']| = |[a'-b']|`.
  Neighbour sums: `|a'-a| ≤ 1, |b'-b| ≤ 1` give `|a-b| ≤ |a'-b'| + 2` (triangle inequality of `zdistInf`), and `B_{u,K'} ≤ 3^{d-2} B_{u,K}` for `K ≤ K'+2` (`localAvg1_STWB_comp`; script max `2.9985 < 3` at `d=3`, `n=3`, in the (a)(ii) output). Each charge has `≤ (3^d)²` terms. `W^{-d} 1_{|a-b|≤1} ≤ 2^{d-2} cB⁻¹ W^{-d} B_{u,|a-b|}` from `cB W^{-d} ≤ Bctl` and `B_{u,K} ≥ ((K+1)^{d-2})⁻¹ B_{u,0}` (`localAvg1_STWB_ge`): the ticket's feared failure does not occur. Total constant `C = 2·3^d·3^d·3^{d-2} + 2^{d-2} cB⁻¹` (`localAvg2_rhs_le`), absorbed once `C ≤ N^{τ/3}`. Diagonal entries: `(GiiGEX)` and `max_{a,b} ‖𝓛^{(2)}‖ ≤ X Bctl` (`localAvg1_maxLoop2_le`); `|[x]-[x]| = 0`.
- Item 4 (`stLocalAvgOfL2_holds`): the pair `(item 3, item 2)`. `3 ≤ d` is only `stGbEXP_holds`' (DECISIONS §36). Consumers of `STLocalAvgOfL2` (`grep`): `ST_step2_of_pins` (`Step2Iterate.lean:1393`), `ST_step2_of_pinsN` (`:1756`), `ST_step2_of_pins'` (`:1779`), `ST_step2_of_pinsN'` (`:1786`), `ST_step2_of_pinsLW'` (`:1793`), all concluding `STStep2 d := 3 ≤ d → …` (`Step2Defs.lean:599`). §36 (i) the merged input `stGbEXP_holds` is for `3 ≤ d`; (ii) the consumers sit under `3 ≤ d`; (iii) the last example of b.4 compiles `STStep2 d` for every `d` from `stLocalAvgOfL2_holds hd3`, and the fifth is the `d = 3` endpoint.
- Timeline from `date -u`: stage 1b started Sun Oct  4 11:16:11 UTC 2026; first commit 27fa5b2 made Sun Oct  4 11:34:08 UTC 2026 (checked by a `date -u` right after it); the docstring-only commit 4a77b2b was made between the `date -u` outputs Sun Oct  4 11:37:49 UTC 2026 and Sun Oct  4 11:38:37 UTC 2026, and b.6 was rerun on it.

## (c) Verified Mathlib names (each `#check`ed or compiled in these files)
`inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `inv_anti₀`, `le_inv_mul_iff₀`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_nonneg`, `Real.one_le_rpow`, `Real.sq_sqrt`, `Real.sqrt_eq_rpow`, `Finset.sum_le_card_nsmul`, `Finset.sum_pair`, `Finset.sup'_le`, `Finset.card_le_three`, `Finset.card_image_le`, `Fintype.card_piFinset`, `Matrix.trace_mul_comm`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `Set.mem_iInter`, `measure_mono`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
1. `T2130a`: the control of `(initialGT2)` is `Ψ_u = max(W^{-d/2}, (W^{-d}B_{u,0})^{1/2})`; the paper's `(W^{-d}B_{u,0})^{1/2}` satisfies the lower window `W^{-d/2} ≤ Ψ_u` only up to the constant `cB < 1` of `ST_Bdata_holds` (`cB W^{-d} ≤ W^{-d}B_{u,0}`); `Ψ_u² ≤ CΨ W^{-d}B_{u,0}` with `CΨ = cB⁻¹ + 1` (same device as T2040a/D93 per the ticket).
2. `T2130b`: `stLocalAvgOfL2_holds` and the items 2-3 carry `(hd : 3 ≤ d)` (DECISIONS §36, the standing rule after T2118b); the pin `STLocalAvgOfL2` itself is unchanged.
3. `T2130c`: `ε₀` is existential in the Lean statement of item 1 (depends on `d, 𝔠, 𝔡, ε` only through `c`), as the paper's "small constant `ε₀`" (T2015d reads it as every `ε₀ > 0` for `lem_GbEXP`; here one fixed value is used).
4. Registry (observation): after this commit the scan counts `STStep2LocalPT` and `STStep2AvgPT` as proved (the conditional theorems `stStep2LocalPT_of_L2decay`, `stStep2AvgPT_of_L2decay` conclude them), so their owed lines in `Test/Axioms.lean` now list under "carry nothing yet" (scratch `precheck.full` lines 60-61: one theorem rests on each; lines 131-132: listed among the premises carrying nothing). They were not touched (the ticket names only the `STLocalAvgOfL2` line); the dispatcher decides whether to remove them. They remain conditional on `STStep1Weak` (registered owed, S1-36) and `STL2decayPT` (concluded by `ST_L2_decay_pt`, `Step2Iterate.lean`).
5. Build note for the auditor and the hub: on the branch alone the root `lake build` fails (b.6, first block) because the line removal needs the root imports of the two new modules; with them (hub step 4) the full build and the pre-check pass (b.6). Add `import RBM3D.Induction.LocalAvg1` and `import RBM3D.Induction.LocalAvg2` after the last `import` line (`import RBM3D.Green.GbEXP` on this base).
6. Nothing in items 1-4 was false as stated; the preflight (a) needed no correction (its `ε₀ = min(1, cd/8)`, `CΨ` etc. are replaced by the equally valid `min(1/2, dc/8)`, `cB⁻¹+1`, no verdict changes; hence no `(a′)`).
