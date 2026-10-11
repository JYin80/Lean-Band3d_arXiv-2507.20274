Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 09:38:02 UTC 2026

Notation (d ≥ 3, BA reading of the ticket): `g = sz.lam n` (the BA coupling; `BAdom` is stated at `BAm d (sz.L n) (sz.lam n) (z n)`), `T0 = BAflowT0 = Im m/(Im m + Im z)` (`MFixedPoint:279`), `g₀ = BAflowLam0 = √T0·g ≤ g`, `m_F = BAmF = BAm d L g₀ E_n` (real axis), `η_u = (1-u) Im m_F`, `Ĥ = seqHflowBA`, `ζ = ztOf`, `Q = M^{(σσ')} = BAMss`, `Θ = BATheta`, `‖·‖_1`-distance `zdistD`, `r = zdistD(a-b)`. All `file:line` are in the worktree `RBM3D/` at commit 54ecfc4.

### (i) Exponent / constant table (each fact-block clause with its BA source; C1: constants in `(d, κ, 𝔡)` only)

| # | clause / quantity | value or BA source | constraint | slack |
|---|---|---|---|---|
| 1 | (A) `Admissible 𝔠 𝔡` | `BAFlow.1` (`FlowPins:389`) | none | exact |
| 2 | (R) `Ĥ` Hermitian | `λ₀Ψ_I + X`: `IsHermitian.add` of `smul` of `PsiI_isHermitian` and `seqHflow_isHermitian (sz.withLam 0)`; **only private copies exist** (`FlowPins:925`, `Step1Trivial:103`, `ConArg:310`, `GreenLocal:178`): one private `EMn2BA_`-copy | `λ₀ ∈ ℝ` (`Complex.conj_ofReal`) | exact |
| 3 | (R) `0 < Im ζ = η_u`, `0 ≤ u ≤ T0` | `ztOf_im` (`GLoopFlow:64`); `Im m_F ≥ κ > 0` from `BAflow_real` (`GreenSchur:59`), `u ≤ T0 < 1` (row 6); every `n` (`ba_G_data`, `GreenLDE:55`) | `(1-u) Im m_F > 0` | `(1-T0)·κ`, e.g. `0.3056·0.5` at the instance |
| 4 | (R) `C.L = loopFine (Ĥ, ζ)` | definitional: `BALloop` (`FlowPins:264`), `baFM` (`:322`) | none | exact |
| 5 | (S) `C.S n = SB d L g'` | `baFM.S = 1`; `sbKernel d L 0 = δ₀` (`Defs/Block:38`: `(1+2d·0²)⁻¹ = 1` at `x=0`, `0²·(…)=0` at `|x|₁=1`), so `SB d L 0 = circulant δ₀ = 1`; `g' := 0`; one lemma, no hypothesis | none | exact |
| 6 | (T) `T0 < 1`, all `n` | `BAt0_lt_one` (`MFixedPoint:285`), `Im z_n ≥ N^{-1+ε} > 0`, `Im m ≥ κ > 0` (`BAdom`, `MFixedPoint:435`) | `Im z, Im m > 0` | `1-T0 = Im z/(Im m+Im z)` |
| 7 | (E) `η_u ≤ 1-u` | `Im m_F ≤ ‖m_F‖ ≤ 1`, `BAm_norm_le_one` (`Ward:136`) at `BASelf` from `BAflow_real`; no window on `g`; `1-u > 0` | `‖m_F‖ ≤ 1` | `1-Im m_F ≥ 0` (`3.0e-11` at `n=3`; tight for `g→0`, where `m` is unimodular; `g=1`: `‖m‖=0.41`, slack `0.59`) |
| 8 | (B) lower `cB W^{-d} ≤ Bctl` | `Bctl = W^{-d}·Bparam d L (sz.lam n) u 0` (`Defs/Sizes:214`; reads `sz.lam n`, the BA `g`): `≥ W^{-d}(g²+1-u)⁻¹ ≥ W^{-d}(𝔡⁻²+1)⁻¹`; `cB = (𝔡⁻²+1)⁻¹ = 1/101` | `0 ≤ u`, `g ≤ 𝔡⁻¹` (`WO`, eventually) | `(g²+1)⁻¹/cB → 101` as `g→0` |
| 9 | (B) upper `Bctl ≤ N^{-c}` | `c = min(2𝔡𝔠, ε)/2 = 1/60`. `Bctl ≤ (W^d g²)⁻¹ + (N(1-u))⁻¹ ≤ N^{-2𝔡𝔠} + 2N^{-ε}` (`WO` lower, `Bandwidth`; `1-u ≥ 1-T0 ≥ Im z/2 ≥ N^{-1+ε}/2`, using `Im m ≤ ‖m‖ ≤ 1`, `Im z ≤ 1`) `≤ 3N^{-2c} ≤ N^{-c}` | `N^c ≥ 3` | `N^c/3 → ∞`; template `ST_Bdata_holds` (`Step2Iterate:1049`, band: replace `ST_flow_im_pos`, `ST_one_sub_lemT` by this) |
| 10 | `1-T0 ≥ N^{-1+ε/2}` (`RangeCond ε/2`, used by the unchanged proofs) | row 9 | `N^{ε/2} ≥ 2` | `N^{ε/2}/2` (`7.2/2` at `n=3`) |
| 11 | (HK) `(Kn2sol)` transfer | `K n t ![s,!s] ![x,x'] = W^{-d}(Θ Q)(x,x')` at `(g₀, E_n, m_F)`: `baKsol_two` (`KInduct:88`; `baKsolve` is a theorem, `KTreeRep:1699`; uniqueness `baK_unique` `KSolve:568`); needs `0 < g₀` (eventually, `BAflow_lam0_window` `GreenSchur:72`) and `BAReal` (`BAflow_real`, `κ ≤ Im m_F`) | `g₀ ≤ Λ := 𝔡⁻¹` eventually (`g₀ ≤ g ≤ 𝔡⁻¹`, `WO`) | exact |
| 12 | BAT-C2 constants | `(C₅,c₅) = baProp5_holds d 𝔡⁻¹ κ` (`Prop6Path:850`, all `σ₁σ₂`, rate `ellT L g t`); `c₀ = BAct_rate d 𝔡⁻¹ κ` (`CombesThomas:45`), `‖M^B_{ab}‖ ≤ c₀⁻¹e^{-c₀ r}` (`BAMB_decay_large` `:509`), `‖Q_{ab}‖ = ‖M^B_{ab}‖² = BAK_{ab}` (`KKernel:102`); `C = max(2C₅, c₀⁻²)`, `c = min(c₅/2, c₀)` | `Bparam d L g t K ≤ 2(1-t)⁻¹` (`Params:36`, `d ≥ 3`, `L ≥ 1`) | none (constants only) |
| 13 | `g` vs `g₀` (ticket (iii)) | `Bctl`, `emn2ExpEllStar` (`EMn2Exp1:176`), `ellT` all read `sz.lam n = g`; `BAKsol`, `BAProp5` read `g₀ = √T0·g`. `ellT L g t = min(max(g/√|1-t|,1),L)` is nondecreasing in `g`, so `ellT L g₀ t ≤ ellT L g t` and decay `e^{-c r/ellT(g₀)} ≤ e^{-c r/ellT(g)}`: the `g₀` bound is the stronger one. The prefactor `2(1-t)⁻¹` does not depend on `g`. A `g`-monotonicity lemma is **not in the tree** (`ellT_mono`, `Kernel/PropT:58`, is in `t`): one private lemma | `0 ≤ g₀ ≤ g` | none |
| 14 | (HK) far margin (limit computation of the external-looking hypothesis) | need `‖K‖ ≤ W^{-d}W^{-(D+d)}` from `r ≥ ℓ* = (log W)^{3/2}ℓ_t(g)`, `zdistInf ≤ zdistD` (`Sizes:117`), `ℓ_t ≥ 1` (`Params:39`): `C(1-t_n)⁻¹e^{-c(log W)^{3/2}} ≤ W^{-(D+d)}`, `(1-t_n)⁻¹ ≤ 2N^{1-ε} ≤ 2W^{(1-ε)/𝔠}` | `c(log W)^{3/2} ≥ log 2C + ((1-ε)/𝔠 + D + d) log W`; coefficient `9.4` at `(ε,𝔠,D,d) = (1/10,1/6,1,3)` | holds for `log W ≥ 89` (`c=1`), `354` (`c=½`), `8837` (`c=0.1`), `C=20` (`hk.py`) |
| 15 | far window nonempty at `sz0` (only to make (HK) non-vacuous) | `ℓ* ≤ ⌊L/2⌋` | `(5 log 2(n+1))^{3/2} ≤ 2(n+1)` | first at `n = 79` (`n = 49` fails) |
| 16 | `J` form, `τ` budget (unchanged from `T2404-prove.md` rows 1, 17: the proofs are model-free given the facts) | `3τ/10 < τ/2` | | slack exponent `τ/5` |

### (ii) One concrete nondegenerate instance (`d=3`)

Data: `sz0` (`Defs/Sizes:260`: `L=4(n+1)`, `W=(2(n+1))⁵`, `lam=(2(n+1))⁻⁶`), `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `z=zSeq`; `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` is the proved `flow_sz0` (`FlowPins:1214`; `Im z ∈ [11/30, 7/10]`, `Im m ≥ 4/5`, `t0_sz0`: `T0 ≥ 2/3`). Times `t ∈ [0, T0]`, `D=1`, `ε₀=1/20`, `Ψ=W⁻¹`, `ℓ ≤ (log W)^{10}ℓ_t`. The script recomputes `m_S = L⁻³ Σ_k (gλ_k - 6i/5)⁻¹` (`λ_k` the spectrum of `Ψ^{(B)}`), `z_S = 6i/5 - m_S`, `T0`, `E_n`, `g₀`, `m_F = m_S/√T0` (`BAzztE_data`) and checks the self-consistency residual of `m_F` at `(g₀, E_n)` independently.
```
$ python3 scratchpad/T2416/inst2.py
n=3 L=16 W=32768 N=e^39.5 T0=0.694444 Imz=0.366667 Imm=0.833333 1-ImmF=3.03e-11 ell*/(L/2)=4.19 ALL True []
n=10 L=44 W=5153632 N=e^57.7 T0=0.694444 Imz=0.366667 Imm=0.833333 1-ImmF=1.11e-16 ell*/(L/2)=2.76 ALL True []
n=40 L=164 W=3707398432 N=e^81.4 T0=0.694444 Imz=0.366667 Imm=0.833333 1-ImmF=3.66e-15 ell*/(L/2)=1.26 ALL True []
```
`ALL True` covers: `Admissible` (`WO`, `Bandwidth`, `L ≥ 3`), `BAdom`, `BASelf` residual `< 1e-12` and `Im m_F ≥ κ`, `T0 < 1`, `g₀ ≤ g`, `0 < η ≤ 1-u` and `Im ζ = η` at `u = 0, T0/2, T0` (rows 3, 7; float tolerance `1e-15` on the tight inequality, the exact one is `Im m_F ≤ ‖m_F‖ ≤ 1`), `cB W^{-d} ≤ Bctl ≤ N^{-1/60}` at the same `u` (rows 8, 9), `1-T0 ≥ N^{-1+ε/2}` (row 10), the `Ψ` window `W^{-3/2} ≤ Ψ ≤ W^{-ε₀}`, `ℓ` window. The far window `ℓ* ≤ L/2` is empty for `n ≤ 40` (last column `> 1`), so (HK) is non-vacuous only from `n = 79` (row 15):
```
$ python3 scratchpad/T2416/hk.py | head -6
linear coefficient of log W: 9.4 = (1-eps)/c + D + d  (eps=1/10, c=1/6, D=1, d=3)
c=1.0: margin>=0 from log W = 89.1  i.e. log10(n+1) = 7.44; margin at 2x that: 700.9
c=0.5: margin>=0 from log W = 354.2  i.e. log10(n+1) = 30.47; margin at 2x that: 2765.2
c=0.1: margin>=0 from log W = 8836.8  i.e. log10(n+1) = 767.25; margin at 2x that: 68820.8
n=49 L=200 logW=23.03 l*=110.5 L/2=100  far window nonempty: False
n=79 L=320 logW=25.38 l*=127.8 L/2=160  far window nonempty: True
```

BAT-C2 numerics (mixed pair `Q_{ab} = |M^B_{ab}|²`, `g` **not small**, `L=24`, `E=0.3`, `m` solved from `BASelf`; `ΘQ` by FFT; `ℓ = ellT L g t`; `Cmax` is `max_x(1-t)|ΘQ|e^{r/(10ℓ)}`):
```
$ python3 scratchpad/T2416/c2.py | awk 'NR==1 || $6=="0.00" || $6=="0.99"'
g    E    Imm   |m|   selfres  t     ell_t  rowsumK  sum|ThM|*(1-t)  Cmax=max_x |ThM|(1-t)e^{c0 r/ell}/ (c0=0.1)   c_emp=min_r -ln((1-t)|ThM|_r)*ell/r 
0.5 0.3 0.6631 0.6667 3.9e-16 0.00  1.000 1.000000000000 1.000000 0.4445 0.5249
0.5 0.3 0.6631 0.6667 3.9e-16 0.99  5.000 1.000000000000 1.000000 0.0091 1.4368
1.0 0.3 0.4092 0.4099 5.0e-16 0.00  1.000 1.000000000000 1.000000 0.1680 0.2325
1.0 0.3 0.4092 0.4099 5.0e-16 0.99 10.000 1.000000000000 1.000000 0.0022 2.6542
2.0 0.3 0.2003 0.2036 8.9e-16 0.00  2.000 1.000000000000 1.000000 0.0415 0.3133
2.0 0.3 0.2003 0.2036 8.9e-16 0.99 20.000 1.000000000000 1.000000 0.0005 5.0582
$ python3 scratchpad/T2416/c2.py | awk 'NR>1{ if ($9!="1.000000") bad++; if (m==0 || $11<m) m=$11 } END{print "rows",NR-1,"nonunit marginals",bad+0,"min c_emp",m}'
rows 12 nonunit marginals 0 min c_emp 0.2325
```
All 12 rows have `(1-t)Σ_b|ΘQ| = 1` (the marginal constant `1/(1-t)` is attained) and `c_emp > 0` (minimum `0.2325`); the self-consistency residual of `m` is `≤ 9e-16`.

**Statement of BAT-C2 (target 3), mathematics.** For `d ≥ 3`, `Λ, κ > 0` there are `C, c > 0` (depending on `d, Λ, κ`) such that for all `L ≥ 3`, `0 < g ≤ Λ`, `E`, `m` with `BAReal d L g κ E m`, `t ∈ [0,1)`, `σ₁, σ₂ ∈ {±}` (the mixed pair and all four), `a, b ∈ Z_L^d`:
(a) `Σ_b ‖(ΘQ)(a,b)‖ ≤ (1-t)⁻¹` and `Σ_a ‖(ΘQ)(a,b)‖ ≤ (1-t)⁻¹`; (b) `‖(ΘQ)(a,b)‖ ≤ C(1-t)⁻¹ exp(-c·zdistD(a-b)/ellT L g t)`.
Proof plan: (a) `Σ_c ‖Θ(a,c)‖ ≤ (1-t)⁻¹` from the resolvent identity `BATheta_resolvent` (`KBase:330`) and `Σ_b ‖Q_{cb}‖ = Σ_b BAK_{cb} = 1` (`BAK_row_sum` `KKernel:124`, `BAK_col_sum` `:128`); only private copies exist (`KStep:281`, `KWardIneq:189`), re-prove; then `Σ_b‖(ΘQ)(a,b)‖ ≤ Σ_c‖Θ(a,c)‖ Σ_b‖Q_{cb}‖`. (b) `r ≤ zdistD(a-c) + zdistD(c-b)` (`zdistD_add_le`, `Lattice:98`); case `zdistD(a-c) ≥ r/2`: `‖Θ(a,c)‖ = ‖Θ(0,c-a)‖ ≤ 2C₅(1-t)⁻¹e^{-c₅ r/(2ℓ)}` (`baP8_BATheta_shift` `Prop6Path:497`, row 12) times `Σ_c‖Q_{cb}‖ = 1`; case `zdistD(c-b) ≥ r/2`: `‖Q_{cb}‖ ≤ c₀⁻²e^{-c₀ r} ≤ c₀⁻²e^{-c₀ r/ℓ}` (`ℓ ≥ 1`) times `Σ_c‖Θ(a,c)‖ ≤ (1-t)⁻¹`. No `L^d` volume factor. `BAMfine_decay` (`GreenSchur:124`) is the fine-lattice form and is not needed (`K` lives on the coarse lattice); `baTheta_weighted_l1` (`GreenStab:251`) is same-sign only and is not used. `BAMB_ward_row` (`Ward:108`) enters only through `BAK_row_sum`.

**(HK) from BAT-C2 (target 4).** Row 11 gives `‖K‖ = W^{-d}‖(ΘQ)(x,x')‖` at `g₀`; (b) at `g₀` with `ellT L g₀ t ≤ ellT L g t` (row 13) and `ℓ* ≤ zdistInf ≤ zdistD` gives `W^{-d}·C(1-t_n)⁻¹e^{-c(log W)^{3/2}}`; row 14 closes it eventually.

### Verdicts
- Target 1 `baEMn2PolyFacts`: PASS (rows 1-5; two small lemmas owed inside the file: Hermitian copy, `SB d L 0 = 1`).
- Target 2 `baEMn2ExpFacts`: PASS (rows 6-10; `3 ≤ d` not needed; (B) is the BA twin of `ST_Bdata_holds`).
- Target 3 BAT-C2: PASS (statement above, constant `C` in `(d, 𝔡, κ)`, no `L^d`, no smallness of `g`, no scalar `m`).
- Target 4 `baEMn2ExpHK` (needs `3 ≤ d`): PASS (rows 11-15; `g` vs `g₀` is consistent, row 13).
- Target 5 BA pins (`baSTEMn2Poly` by `stEMn2PolygL_of`; `J` form by `stEMn2ExpJgL_of`; `Ĵ` form by `stEMn2ExpgL_of`): PASS. The "second estimate" of the paper's `lem: EMn2_N` is `(eq:MG_conclusion3)` (`3_5:437-440`, BA form `7_8:1999`), i.e. the `J`/`Ĵ` forms; `(eq:MG_conclusion2)` is the special case of the first estimate at `Ψ = (W^{-c₀}B_{t,|a-b|∧K})^{1/2}` and has no Lean form in `RBM3D/` (grep `MG_conclusion2`: 0 hits); not owed. The `J` form drops `J ≥ W^{-d}` and allows `ω`-dependent `J` (T2404a). The three L-pins stay premises of the pins.
- Target 6 T6-BA (`STContractM` at `H = seqHflowBA`, `z = ztOf`): PASS; `stContractM_holds d` (`Contract:1069`) is already for every Hermitian `H` and `Im z > 0`; the BA corollary needs only rows 2-3 and `NeZero (sz.L n)`, `NeZero (sz.W n)`.
- Target 7 C1: PASS (constants `(d, κ, 𝔡, Λ = 𝔡⁻¹)`; `κ ≤ Im m` is a datum; `‖m‖ ≤ 1` from Ward, uniform in `g`).
- Target 8 instances (`d=3`): PASS at `sz0`, `zSeq`, `flow_sz0`; fact blocks and (HK) are theorems there, the stochastic premises are hypotheses of the examples.

## (b) Script output — Sun Oct 11 10:03:35 UTC 2026
**Line count against the stop line (ticket: 1,800; one file ≤ 2,000).**
```
$ wc -l RBM3D/BA/EMn2BA.lean; git diff --numstat main...t/T2416; git log --oneline main..t/T2416 | cut -c1-7 | tr '\n' ' '; git status --short | wc -l
    1090 RBM3D/BA/EMn2BA.lean   (sections: Reading 54-132, Facts 136-282, Comp 291-450, HK 588-737, Pins 747-781, Contract 788-831, instances 845-1090)
1 0 RBM3D.lean;1090 0 RBM3D/BA/EMn2BA.lean;
4c09836 6ab73e1 0aa8926 eb76c2a  | uncommitted files:        0
```
**Build, check file, axioms.**
```
$ lake build RBM3D.BA.EMn2BA | tail -1
Build completed successfully (3825 jobs).
$ lake build  (full library; root `import RBM3D.BA.EMn2BA` added; ends in `#assert_rbm_axioms`)   started/ended: Sun Oct 11 09:59:16 UTC 2026;Sun Oct 11 09:59:58 UTC 2026;
lines containing 'error:': 0 | Build completed successfully (4226 jobs). exit 0 
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/EMn2BA.lean | wc -l  ->  0
$ lake env lean docs/tickets/checks/T2416-check.lean (branch worktree) ->  exit 0
$ lake env lean ax.lean (#print axioms of every public theorem/def of the file): 33 declarations, 33 with [propext, Classical.choice, Quot.sound], 0 others
```
**Clause table of (i) as finally used** (Lean line in `RBM3D/BA/EMn2BA.lean`; BA source file:line).
| clause | Lean | BA source |
|---|---|---|
| (A) `Admissible` | `baEMn2PolyFacts` :141 | `BAFlow.1` (`FlowPins:389`) |
| (R) `Hf` Hermitian | `EMn2BA_seqHflowBA_herm` :68 | `seqHflow_isHermitian`, `PsiI_isHermitian` (private copies `FlowPins:925`, `ConArg:311`) |
| (R) `0 < Im ζf = eta` | `baEMn2PolyFacts`, `EMn2BA_mF_data` :125 | `BAflow_real` (`GreenSchur:59`), `ztOf_im` (`GLoopFlow:64`) |
| (R) `C.L = loopFine` | `baEMn2PolyFacts` (`rfl`) | `BALloop` (`FlowPins:264`) |
| (S) `C.S = SB d L 0` | `EMn2BA_SB_zero` :77 | `baFM.S = 1` (`FlowPins:327`), `sbKernel` (`Defs/Block:38`) |
| (T) `T0 < 1` | `EMn2BA_T0_lt_one` :106 | `BAt0_lt_one` (`MFixedPoint:285`), `BAdom` |
| (E) `eta ≤ 1 - u` | `baEMn2ExpFacts` :160 | `BAm_norm_le_one` (`Ward:136`), `BAflow_real` |
| (B) `cB W^{-d} ≤ Bctl ≤ N^{-c}` | `baEMn2ExpFacts` :160, `EMn2BA_one_sub_T0` :111 | `WO`, `Bandwidth`, `BAdom`; twin of `ST_Bdata_holds` (`Step2Iterate:1049`); `Bctl` reads `sz.lam` (`Sizes:214`) |
| (HK) `𝒦^{(2)} = W^{-d}ΘQ` | `EMn2BA_K_two` :624 | `baKsol_two` (`KInduct:88`), `BAflow_real` |
| (HK) decay of `ΘQ` | `baComp_holds` :472 | `baProp5_holds` (`Prop6Path:850`), `BAMB_decay_large` (`CombesThomas:509`), `BAK_row_sum`/`BAK_col_sum` (`KKernel:124,128`), `BATheta_resolvent` (`KBase:330`) |
| (HK) `g₀ ≤ g`, far margin | `EMn2BA_ellT_mono_g` :591, `EMn2BA_arith` :597, `baEMn2ExpHK` :637 | `BAflow_lam0_window` (`GreenSchur:72`), `size_rpow_le_W_rpow` (`Defs/Sizes`) |
**Statement of BAT-C2's lemma, extracted by script** (`extract.py`: declaration text up to `:=`, whitespace collapsed).
```
EMn2BA:457 def BACompBound (d : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, (∀ a : Zd d L, ∑ b, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ (1 - t)⁻¹) ∧ (∀ b : Zd d L, ∑ a, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ (1 - t)⁻¹) ∧ ∀ a b : Zd d L, ‖(BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ C * (1 - t)⁻¹ * Real.exp (-c * (zdistD d L (a - b) : ℝ) / ellT L g t)
EMn2BA:472 theorem baComp_holds (d : ℕ) (Λ κ : ℝ) : BACompBound d Λ κ
```
**Targets, extracted by script** (T1, T2, T4, T5 three pins, T6).
```
EMn2BA:141 theorem baEMn2PolyFacts : emn2PolyFacts d BAFlow baFMz BAflowT0 baEMn2Hf baEMn2Zf
EMn2BA:160 theorem baEMn2ExpFacts : emn2ExpFacts d BAFlow baFMz BAflowT0 baEMn2Hf baEMn2Zf
EMn2BA:637 theorem baEMn2ExpHK (hd : 3 ≤ d) : emn2ExpHK d BAFlow baFMz BAflowT0
EMn2BA:753 theorem baSTEMn2Poly : STEMn2PolygL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
EMn2BA:760 def BAEMn2ExpJ : Prop := emn2ExpPrem d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 (fun sz z t ℓ D => ∀ J : ℕ → sz.SeqΩ → ℝ, (∀ n ω, 0 ≤ J n ω) → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun _ => Unit) (fun n _ ω => STJhatg (baFMz sz z) n D (ℓ n) (t n) ω) (fun n _ ω => J n ω) → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖STEEg (baFMz sz z) n (t n) p.1 p.2.1 p.2.2 ω‖) (fun n p ω => ((baFMz sz z).eta n (t n))⁻¹ * ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) + (J n ω) ^ 3) * (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2))
EMn2BA:773 theorem baSTEMn2ExpJ (hd : 3 ≤ d) : BAEMn2ExpJ d
EMn2BA:777 theorem baSTEMn2Exp (hd : 3 ≤ d) : STEMn2ExpgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
EMn2BA:814 theorem baSTContractM {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (m : ℂ) (E : ℝ) (hm : 0 < m.im) (hu : u < 1) : BAContractAt d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u ω) (ztOf m E u)
EMn2BA:823 theorem baSTContractM_flow {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) : BAContractAt d (sz.L n) (sz.W n) (baEMn2Hf sz z n u ω) (baEMn2Zf sz z n u)
```
**Compiled nonempty instances, `d = 3`** (`inst2.py`: file:line, statement head, proof term; data `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`; BAT-C2 at `MFixedPointInst.P`, `L = 4`, `Λ = 10`, `t = 1/2`; stochastic premises `hI`, `hA`, and the sample `ω`, are the free data).
```
EMn2BA:854 [: sz0.Admissible (1 / 6) (1 / 10) ∧ sz0.L 3 = 16 ∧ sz0.W 3 = 32768 ∧ (∀ ω : sz0.SeqΩ, (baEMn2Hf…] := by obtain ⟨hadm, hR, hS⟩ := baEMn2PolyFacts 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 obtain ⟨hH
EMn2BA:871 [: BAflowT0 sz0 zSeq 3 < 1 ∧ (baFMz sz0 zSeq).eta 3 (1 / 2) ≤ 1 - 1 / 2 ∧ (baFMz sz0 zSeq).eta 3…] := by obtain ⟨hT, hE, cB, c, hcB, hc, hB⟩ := (baEMn2ExpFacts 3).2 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq fl
EMn2BA:886 [: ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ σ : Bool × Bool, (∑ b, ‖(BATheta 3 4 P.g0 P.E P.m0 (1 / 2) σ.1 σ…] := by obtain ⟨C, hC, c, hc, H⟩ := baComp_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1 refine ⟨C, c, hC, hc, fun σ => ?_⟩ obtain ⟨h1, h2, h3⟩
EMn2BA:902 [: zdistD 3 4 (0 - ![2, 0, 0] : Zd 3 4) = 2…] := by decide
EMn2BA:968 [(D : ℝ) (hD : 0 < D) : ∃ n : ℕ, ∃ a b : Zd 3 (sz0.L n), a ≠ b ∧ emn2ExpEllStar sz0 n (1 / 2) ≤ …] := by have hHK := baEMn2ExpHK (by norm_num : 3 ≤ 3) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ 
EMn2BA:1024 [(hI : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 20) (f…] := baSTEMn2Poly 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun n => by norm_num) (
EMn2BA:1035 [(hI : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 20) (f…] := baSTEMn2Exp 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun n => b
EMn2BA:1053 [(hI : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 20) (f…] := baSTEMn2ExpJ 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun n => 
EMn2BA:1074 [(ω : sz0.SeqΩ) : ∑ x : Zd 3 (sz0.L 3), ‖loopL 3 (sz0.L 3) (sz0.W 3) (blockMat 3 (sz0.L 3) (sz0.…] := (baSTContractM_flow (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) sz0 flow_sz0 3 (by norm_num) (ha
EMn2BA:1086 [(ω : sz0.SeqΩ) : BAContractAt 3 (sz0.L 3) (sz0.W 3) (sz0.seqHflowBA (BAflowLam0 sz0 zSeq) 3 (1 …] := baSTContractM sz0 _ 3 (1 / 2) ω Complex.I 0 (by simp) (by norm_num)
```
**Name clashes, ports.**
```
$ git grep -n -w <each of the 33 new public names> main -- RBM3D docs/tickets/checks | wc -l  ->  0   (main at 88d1b63)
$ grep -c 'RBM1D\|RBM2D' RBM3D/BA/EMn2BA.lean  ->  0   (no port from RBM1D/RBM2D; no `git diff --stat` owed)
copies of private RBM3D lemmas, found by regex `copy of `X`, `file:line`` over the file: `KStep_row_of_resolvent` (BA/KStep.lean:279); `KWardIneq_col_of_resolvent` (BA/KWardIneq.lean:219); `kellStar_bparam_le` (Path/KellStar.lean:68); `kellStar_arith` (Path/KellStar.lean:89); twin of `ST_Bdata_holds` (`Induction/Step2Iterate.lean:1049`)
```
**Narrative.**
- One new file (1090 lines against the stop line 1,800) and the root import line; the commits listed above change only these two files (numstat above). The only importer is `RBM3D.lean` (`grep -rln RBM3D.BA.EMn2BA` over the worktree).
- T1/T2 (`baEMn2PolyFacts`, `baEMn2ExpFacts`): the fact blocks follow from `BAFlow` alone; no hypothesis was added (`baEMn2ExpFacts` carries no `0 < d`). (B) is the proof of `ST_Bdata_holds` with `ST_flow_im_pos`, `ST_one_sub_lemT` replaced by `EMn2BA_zim_pos` and `EMn2BA_one_sub_T0` (`1 - t₀ ≥ Im z/2`, from `Im m ≤ 1`, `Im z ≤ 1`); `cB = (𝔡⁻²+1)⁻¹`, `c = min(2𝔡𝔠, ε)/2`.
- T3 (BAT-C2): `BACompBound d Λ κ` has the shape of `BAProp5` (`3 ≤ d`, `0 < Λ`, `0 < κ`, constants before `L, g, E, m`); `baComp_holds` proves it for all four charge pairs. Marginals: right and left resolvent identities with `Σ|M^{(σσ')}| = Σ BAK = 1`. Decay: split of `Σ_c |Θ(a,c)||Q(c,b)|` at `|a-c| ≥ |a-b|/2` (`BAProp5`, `Bparam ≤ 2(1-t)⁻¹`) or `|c-b| ≥ |a-b|/2` (`|Q_{cb}| = |M^{(B)}_{cb}|²`, `BAMB_decay_large`, `ℓ_t ≥ 1`); `C = 2C₅ + c₀⁻²`, `c = min(c₅/2, c₀)`, depending on `(d, Λ, κ)` only. No `L^d` factor, no smallness of `g`, no scalar `m`.
- T4 (`baEMn2ExpHK`): `EMn2BA_K_two` is `baKsol_two` at `(g₀, E_n, m_F)`; BAT-C2 is used at `g₀ ≤ 𝔡⁻¹` (`BAflow_lam0_window`), and `ℓ_t(g₀) ≤ ℓ_t(g)` (`EMn2BA_ellT_mono_g`) turns the decay into the far field beyond `ℓ*_t(g)`. The amplitude is `(1-t_n)⁻¹ ≤ 2N ≤ 2W^{1/𝔠}`; the closing inequality is `EMn2BA_arith` (the exponent `(1-ε)/𝔠` of preflight row 14 is replaced by the weaker `1/𝔠`, so `ε` is not read; row 10 is not used).
- T5: the three pins are one-line applications of `stEMn2PolygL_of`, `stEMn2ExpJgL_of`, `stEMn2ExpgL_of` to the BA blocks; `STInitialGT2gL`, `STLWassmgL`, `STLWassmExpgL` stay premises of the pins. The second estimate of `lem:EMn2_N` (`3_5:437-440`) is the `J`/`Ĵ` pair; `(eq:MG_conclusion2)` has no Lean form in `RBM3D/` and is not owed (preflight verdict).
- T6: `BAContractAt` is the body of `STContractM`; `EMn2BA_contract_iff` is `Iff.rfl`; `baSTContractM` needs `0 < Im m`, `u < 1`; `baSTContractM_flow` is its form on `[0, t₀_n]`.
- Instances: the facts and the pins at `sz0`, `zSeq`, `flow_sz0`, `n = 3` (`L = 16`, `W = 32768`), `u = t ≡ 1/2 ≤ t₀` (`t0_sz0 : 2/3 ≤ t₀`). BAT-C2 at the flow point `P` (`P.g0_le : g₀ ≤ 10 = Λ`, `κ = Im m₀`). The (HK) instance is existential: it takes an `n` from the `∀ᶠ` together with `(log W)^{3/2} ≤ 2(n+1) = L/2` (`EMn2BAInst_far_ev`, from `isLittleO_rpow_exp_pos_mul_atTop`), the far pair `a = (2(n+1), 2(n+1), 2(n+1))`, `b = 0`, `a ≠ b`.
- Preflight section (a) was not edited and no `(a′)` is needed: no statement of (a) was found wrong.

## (c) Verified Mathlib names
- `#check @name` of the 89 Mathlib names the file uses (`grep -c '^#check'`; among them `Real.rpow_*`, `Real.log_*`, `Real.sqrt_*`, `Real.exp_*`, `Real.mul_rpow`, `Real.tendsto_log_atTop`, `Finset.sum_*`, `Matrix.mul_apply`, `ZMod.val_natCast`, `isLittleO_rpow_exp_pos_mul_atTop`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`, `tendsto_natCast_atTop_atTop`, `tendsto_atTop_add_const_right`, `inv_anti₀`, `div_le_div_iff_of_pos_right`, `le_div_iff₀`, `div_le_iff₀`, `norm_sum_le`, `pow_le_pow_left₀`, `one_le_pow₀`, `inv_le_one_of_one_le₀`, `le_mul_of_one_le_left`, `Matrix.IsHermitian.add`, `Matrix.conjTranspose_smul`): `lake env lean mathlib_check.lean` exit 0, 0 errors.
- Absent: a lemma `ellT L g₀ t ≤ ellT L g t` (monotone in the coupling): `git grep` of theorem names containing `ellT` on `main` lists only `ellT_mono` (`Kernel/PropT.lean:58`), `nqGood1_ellT_mono` (`Induction/NQGood1.lean:812`) and `scaleFacts_ellT_mono_ratio` (`Induction/ScaleFacts.lean:299`), all in the time argument; `EMn2BA_ellT_mono_g` is new.

## (d) Open issues and paper-delta candidates
- **T2416a** (Lean/paper): the paper's `(eq:kn2sol_decay)` (`7_8:2002`) is read at the coupling `g`; Lean proves BAT-C2 at the flow coupling `g₀ = √t₀ g ≤ g` and transfers to `ℓ*_t(g)` by `EMn2BA_ellT_mono_g`.
- **T2416b** (Lean/paper): the marginals of `Θ M^{(σσ')}` are `≤ (1-t)⁻¹` with constant exactly 1; the decay has explicit constants `(C, c)` in `(d, Λ, κ)`.
- **T2416c** (Lean/paper): the `J` form, the `Ĵ` form and (HK) carry `3 ≤ d` (T2118a); the `J` form drops `J ≥ W^{-d}` (T2404a); `(eq:MG_conclusion2)` has no Lean form.
- Open: stage L / BA-V must supply `STInitialGT2gL`, `STLWassmgL`, `STLWassmExpgL` at `baFMz`; the file is not in the certificate lane (no registry line, as the ticket says).
