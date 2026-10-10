Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 02:09:53 UTC 2026

Sources: `S:A`, `S:B` = RBM2D `Universality/GUEPhase/RandomLayerA.lean` (521 lines), `RandomLayerB.lean` (152 lines), RBM2D HEAD `9e0f275`; RBM3D main `010cad9` (T2356 `Eq729B` and T2361 `PathBounds` merged). Notation: `N = (W L)^d`, `x = 1 - t₁ = (1 - t₀) + ζ(t_n) t₀`, `ζ(t_n) ≤ t_n ≤ N^{-1+τ_U}` (`ouTStar`), `c_κ = √(κ(4-κ))/8` with `1 - t₀ = Im z/((Im m)+Im z) ≤ Im z/c_κ` (`zRange`, `im_msc_ge`, as `Eq729B.lean:1188-1189`), `N^τ ≤ W^{τ/𝔠}` (`Sizes.size_rpow_le_W_rpow`, `Defs/Sizes.lean:237`), `lam²W^d ≥ W^{2𝔡}` (`Sizes.lam_sq_mul_pow_ge`). Margin: `lemma28_quant` (`Defs/Semicircle.lean:359`) gives `|lemE z| ≤ 2 - κ` with the same κ, so the source's margin `κ/2` is not needed.

### (i) Exponent table (U3: the `τ_U` table of the rows S1–S6 at `d ≥ 3`)

Values at `𝔠 = 1/6`, `𝔡 = 1/10`, `d = 3`, `τ_U = ouTauMax 𝔠 𝔡 = min(𝔠/12, 𝔠𝔡/12, 1/100) = 1/720` (`ZeroModeProfile.lean:78`). `τ_D` = the loss of `h730`/`hscale`: `τ_U/2` at the LL scale, `τ_U` at the QUE scale. All rows are `∀ᶠ n` (thresholds in `N` or `W` only, from `Admissible`: `W ≥ N^𝔠`, `N → ∞`, `lam ≥ W^{-d/2+𝔡}`, `lam ≤ 𝔡⁻¹`).

| row | statement (3-d form) | constraint on `τ_U` | value / slack at `τ_U = 1/720` |
|---|---|---|---|
| S1 LL `r1` (→`h730`) | `t ≤ N^{-τ_D} η_LL/4`, `η_LL = N^{-1+2τ_U}` ⇔ `N^{τ_U-τ_D} ≥ 4` | none (`τ_D < τ_U`); fails at `τ_D = τ_U` | exponent `τ_U/2 = 1/1440`; sufficient form needs log10 N ≥ 867; exact ratio at `sz0` 0.99 → 0.06 |
| S2 LL `r2` (→`hscale`) | `4(Nη_LL)⁻¹ ≤ N^{-τ_D}` ⇔ `N^{2τ_U-τ_D} ≥ 4` | none (`τ_D < 2τ_U`) | exponent `3τ_U/2 = 1/480`; log10 N ≥ 289 |
| S3 LL `r3` (→`hell`) | `L^d(η_LL/c_κ + t) ≤ lam²`; via `lam²W^d ≥ W^{2𝔡}`, `N^{2τ_U} ≤ W^{2τ_U/𝔠}`: `(1/c_κ+1) W^{2τ_U/𝔠} ≤ W^{2𝔡}` | `τ_U < 𝔠𝔡` | `W`-exponents `1/60` vs `1/5`; `ouTauMax/𝔠𝔡 = 1/12` |
| S3' LL (new) `hell1` | `L^d x ≤ 1`: `(1/c_κ+1) N^{2τ_U}/W^d`, `2τ_U/𝔠 ≤ 1/6` (from `τ_U ≤ 𝔠/12`) | `τ_U < d𝔠/2` | `W`-exponent `1/60 - 3`; `ouTauMax/(d𝔠/2) = 1/180` |
| S4 QUE (→`h730`,`hscale`) | `Eq729B_claimA` (`Eq729B.lean:441`): `4N^{2τ_U} ≤ Nη_Q = W^{-𝔡/3} lam W^{d/2} ≥ W^{2𝔡/3}` | hypothesis `τ_U ≤ 𝔠𝔡/12` (binding row, equality at `ouTauMax`) | `N^{2τ_U} ≤ W^{1/60}`, `Nη_Q ≥ W^{1/15}`, spare `W^{𝔡/2} = W^{1/20} ≥ 4` |
| S5 QUE (→`hell`) | `Eq729B_hell_of_scales`: `2/c_κ ≤ W^{4𝔡/3}`, `2N^{τ_U} ≤ W^{2𝔡}` (inside `Eq729B_derived`, `:1125`) | `τ_U/𝔠 < 2𝔡` | `W`-exponents `1/120` vs `1/5`; spare `23𝔡/12 = 23/120` |
| S6 QUE (new) `hell1` | `L^d η_Q = lam W^{-d/2-𝔡/3}` (`Eq729B_Ld_mul_etaQ`, `:377`) `≤ 𝔡⁻¹ W^{-d/2-𝔡/3}`; `L^d ζ ≤ N^{τ_U}/W^d` | `τ_U ≤ 𝔠/12` | `W`-exponent `1/120 - 3` (second term), first term → 0 |
| S7 scale/domain | `η_LL ≤ 1`, `oull_of_pathBounds` needs `τ_U < 1/2`; `STFlow` `ε`: LL `ε = 2τ_U` (`N^{-1+ε} = η_LL`, all `n`), QUE `ε = 2𝔠𝔡/3 = 1/90` (`queDomain`, eventual) | `τ_U ≤ 1/2` | slack `359/720` |

Script (exponent arithmetic, `python3 exps.py`):
```
tau_U = ouTauMax = 1/720 ; c/12,c*dd/12,1/100 = 1/72 1/720 1/100
('S1 LL r1 h730: N^{tU-tD}>=4 (exp tU-tD)', Fraction(1, 1440), 'N-exponent >0')
('S2 LL r2 hscale: N^{2tU-tD}>=4 (exp 2tU-tD)', Fraction(1, 480), 'N-exponent >0')
('S3 LL hell: W-exp 2tU/c vs 2dd', (Fraction(1, 60), Fraction(1, 5)), '2tU/c < 2dd  <=> tU < c*dd')
("S3' LL hell1: W-exp 2tU/c - d", Fraction(-179, 60), '<0')
('S4 Q r1/claimA: W-exp of N^{2tU}=2tU/c vs N*eta_Q>=W^{2dd/3} ; spare W^{dd/2}>=4', (Fraction(1, 60), Fraction(1, 15), Fraction(1, 20)), '2tU/c <= 2dd/3 - dd/2 (design tU<=c*dd/12 gives dd/6)')
('S5 Q hell: tU/c vs 2dd ; spare 23dd/12', (Fraction(1, 120), Fraction(1, 5), Fraction(23, 120)), 'tU/c<=dd/12')
('S6 Q hell1: tU/c - d', Fraction(-359, 120), '<0 (uses c/12: tU/c<=1/12)')
('eta_LL<=1: tU <= 1/2; slack', Fraction(359, 720), '>0')
('locDomain eps_LL=2tU ; eps_Q=2*c*dd/3', (Fraction(1, 360), Fraction(1, 90)), 'eps>0')
('true limits: LL hell tU<c*dd ; Q claimA tU<c*dd/3 ; hell1 tU<d*c/2', (Fraction(1, 60), Fraction(1, 180), Fraction(1, 4)), 'ouTauMax is below all: ratios')
ratios ouTauMax/limit: 1/12 1/4 1/180
thresholds (sufficient-form constants): LL r1 log10N >= 866.9663875122658 ; LL r2 >= 288.98879583742195
```
**U3 verdict: no row needs `τ_U < ouTauMax`.** The only row at its limit is the hypothesis of `Eq729B_claimA` (merged, T2356); `𝔠/12` is used only by `hell1` (S3', S6), where any `τ_U < d𝔠/2` suffices. No pin change, no REQ.

**Statement points.**
* **(i) inputs replaced. PASS.** `UNMLOut d` (`Pins.lean:432`) at `STFlow sz κ ε 𝔠 𝔡 z` (`Induction/Defs.lean:286`: `Admissible ∧ ∀ n, locDomain κ ε n (z n)`) and times `0 ≤ t₁ ≤ lemT z` gives `STLK ∧ STLocalEntry` at `(STflowE z, t₁)` (= `lemE∘z`, defeq), the `hLK`, `hLoc` of `gueGrid_pathBounds` (`PathBounds.lean:550`) and `STExp2` for (7.47). LL: `z_n = E_n + iη_LL` is in `locDomain κ 2τ_U` for every `n`. QUE: `Eq729B_goodFlow_aux` (`:1274`) gives `z'` in `locDomain` for every `n` (equal to `E_n + iη_Q` eventually), `FlowData`, `|E'| ≤ 2-κ ∧ 0 ≤ t₁ ≤ t₀ < 1` for every `n`; `Eq729B_bridge` (`:1316`) gives `STExp2` and `Eq729B_eq747_of_inputs` (`:1221`) consumes it. `UNG1Row` has premises `ML, Loc, Que`; `Loc`, `Que` are unused (as the source's `G1Row` has only `P7Out`, `P7ExpOut`).
* **Translation of `RandomLayer_rows` (auditor line by line).** Source 8 conclusions ↦ `|lemE| ≤ 2-κ`, `0 ≤ t₁`, `t₁ ≤ t₀`, `t₀ < 1` (all `n`), `h730`, `hscale`, `hell : L^d(1-t₁) ≤ lam²` (source `L²(1-t₁) ≤ 1`), plus **new** `hell1 : L^d(1-t₁) ≤ 1` (T2361 F2: `Bounds_path` needs it; `hell` does not give it since `lam ≤ 𝔡⁻¹` only). The source's range conclusion `N^{-1+τ} ≤ 1-t₁` and its hypothesis `r5`, with the parameter `τ`, have no 3-d twin (`STFlow ε` replaces them). Hypotheses `r3` become `L^d(η/c_κ+t) ≤ lam²` and `≤ 1`. `RandomLayer_lem28`: items `0<Im z`, `|lemE| ≤ 2-κ`, `1/16 ≤ lemT < 1`, `etaT = √t₀ η ≥ η/4`, `1-t₀ ≤ η/c_κ` (source `η/4 ≤ 1-t₀` served only `r5`; a private `LLTransfer_lem28` has all items except `1-t₀ ≤ η/c_κ`).
* **`RandomLayer_rowsQ`.** `h730`, `hscale`, `hell` at `η_Q` are the merged `Eq729B_derived`; the 3-d `rowsQ` is only the new `hell1` (S6) (and, if kept, `r1`–`r3` stated at `η_Q`, S4–S5). **`RandomLayer_etaQ_pos/le_one`**: `ouEtaQ` carries `lam`, so `0 < η_Q` needs `0 < lam n` and `η_Q ≤ 1` holds only eventually (`queDomain`): no unconditional twin; `g1Row` does not need them. `etaLL_pos`, `etaLL_le_one` (`τ_U ≤ 1/2`, `N ≥ 1`) are unconditional.
* **(iii) U1: kind-generic producer `UNG1Rowk K P ML Loc Que`. PASS (not band-only), with this list of T inputs** (BA-C5's target list; band values in brackets): **T1** flow maps `flowE, flowT` and Lemma-2.8 facts at `0 < Im z ≤ 1`, `K.bulk sz κ (Re z) n` [`lemE`, `lemT`, `m = msc`; `lemma28_quant`, `zRange`, `im_msc_ge`]: `|flowE z| ≤ 2-κ`, `1/16 ≤ flowT z < 1`, `Im z_{t₀} = √t₀ Im z`, `1-t₀ ≤ Im z/c_κ`. **T2** PathBounds-type producer [`gueK_exists` `KPrim.lean:749` + `gueGrid_pathBounds`]: good data (all `n`), `h730`, `hscale`, `hell`, `hell1`, `hLK`, `hLoc` at `(E', t₁, t₀)` ⇒ `∃ Kt` with `hKinit`, `hK`, `hK2` and the path bounds `PB`. **T3** LL transfer [`oull_of_pathBounds` `LLTransfer.lean:443`]: `PB` at the LL flow ⇒ the moment bound of `UNOULLk`. **T4** Eq729B target-3 form [`Eq729B_eq747_of_inputs`]: `FlowData`, `hgood`, `STExp2 E' t₁`, `PB` ⇒ the body of `UNOUEq747k`, every `τ > 0` (band: rewriting `unPinsK_band_M`, `ouMatC_toC` as in `UNOUEq747k_band`). **T5** `ML ⇒ (STFlow ⇒ STLK ∧ STLocalEntry ∧ STExp2)` [`UNMLOut d`; BA `UNMLOutBA d`]. **T6** structural: for each `κ`, `K.bulk sz κ · n` is nonempty for all `n` or empty for all `n` (padding of an eventually-bulk `E` to a good sequence, as private `OUInterfaceK_pad`; band: `κ ≤ 2` / `κ > 2`). Proved generically here: rows S1–S6 (use only `Admissible` and T1), flow selection, quantifier and padding bookkeeping. Band-only (merged, supplied by T1–T5 at the band; BA must supply them in BA-C5): `msc`/`lemE`/`lemT`, GUE `gueK_exists`, `gueGrid_pathBounds`, `oull_of_pathBounds`, `Eq729B_eq747_of_eq729`, `goodFlow_aux`. `g1Row` is T2–T4 at `UNKind.band` plus `UNG1Rowk_band.1` (`OUInterfaceK.lean:392`); `g1Rowk_band` is its `.2`.

### (ii) One concrete nondegenerate instance

`d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `sz0.Admissible (1/6) (1/10)` (`sz0_admissible`, `:331`), `κ = 1/10`, `E_n = 0` (`lemE = 0`, `Im mE = 1`, `a = Im m = 2/(√(η²+4)+η)`, `t₀ = a²`, `1-t₀ = ηa`), `τ_U = ouTauMax = 1/720`, `t_n = ouTStar = N^{-1+τ_U}`, `ζ = 1-e^{-t_n}`, QUE `η_Q = W^{-1/30} lam W^{3/2}/N`, `N η_{t₀} = N(1-t₀)`, `Bparam(K=0)`: `Bctl = W^{-d}((lam²+x)⁻¹ + (L^d x)⁻¹)`. Window genuine: `0 < t₁ < t₀ < 1`, `η_LL ≈ 5e-7`, `t₀ - t₁ > 0` at every `n`. Hypotheses of the rows (`h𝔠`, `hd`, `hκ`, `hτU`, `hτUc` equality, `0 ≤ t ≤ ouTStar`) hold at all `n`; the exact hypothesis values of `gueGrid_pathBounds` / `Eq729B_eq747_of_inputs` (ratios, `≤ 1` required) are:
```
$ python3 inst2.py      (mpmath, 40 digits; script in scratchpad T2363/)
tauU=ouTauMax= 0.001388888888888889  1/c_k=12.810  d=3 kappa=1/10 c=1/6 dd=1/10 E=0 t=ouTStar(tauU) tauD: LL tauU/2, QUE tauU
ratios (<=1 required; NetaBctl<=2 required):  n | log10N | LL r1 h730 | LL r2 hscale | LL hell | LL hell1 | Q claimA | Q h730 | Q hscale | Q hell | Q hell1 | LL NetaBctl | Q NetaBctl
 0 | 6.3 | 0.99 | 0.97 | 0.258 | 6.29e-05 | 1.65 | 0.413 | 0.405 | 0.443 | 0.000108 | 1.26 | 1.44
 1 | 11.7 | 0.981 | 0.945 | 0.0331 | 1.97e-09 | 0.679 | 0.17 | 0.164 | 0.115 | 6.88e-09 | 1.03 | 1.12
 1e1 | 25.1 | 0.961 | 0.887 | 0.000212 | 1.65e-20 | 0.0762 | 0.019 | 0.0176 | 0.00589 | 4.58e-19 | 1 | 1.01
 1e6 | 114.3 | 0.833 | 0.578 | 4.4e-19 | 1.07e-94 | 3.3e-08 | 8.24e-09 | 5.72e-09 | 3.15e-11 | 7.69e-87 | 1 | 1
 1e50 | 906.3 | 0.235 | 0.0129 | 4.34e-149 | 0 | 1.13e-64 | 2.82e-65 | 1.55e-66 | 1.46e-84 | 0 | 1 | 1
largest grid n (0..59, 10^2..10^200) with row violated: {'LL r1 h730': None, 'LL r2 hscale': None, 'LL hell': None, 'LL hell1': None, 'Q claimA': 0, 'Q h730': None, 'Q hscale': None, 'Q hell': None, 'Q hell1': None, 'LL NetaBctl': None, 'Q NetaBctl': None}
```
All nine rows are `≤ 1` and both `N η_{t₁} Bctl(t₁)` are `≤ 2` at every grid `n` (integers 0–59, `10^2…10^200`), except the sufficient form `Eq729B_claimA` (`Q claimA`) at `n = 0` (1.65; exact `Q h730` there 0.413) — it holds from `n = 1`, and the `∀ᶠ` rows need no fixed `n`. The sufficient-form thresholds of S1, S2 (log10 N ≥ 867, 289) are not needed by the exact instance (ratios 0.99, 0.97 at `n = 0`).

**External hypotheses (`UNMLOut`; TEAM §8 lesson 14), limit computation.** `STLK` at `k = 1` is `‖L − m‖ ≺ Bctl(t₁)`, the consumer needs `(Nη_{t₁})⁻¹`, `η_{t₁} = x Im mE(E')`, `E' = 0`: `N η_{t₁} Bctl(t₁) = 1 + L^d x/(lam²+x)` (exact), printed in the last two columns: 1.26 / 1.44 at `n = 0`, 1.03 / 1.12 at `n = 1`, → 1 at `n = 10, 10^6, 10^50`, always `≤ 2` (`hell`: `L^d x ≤ lam²`): both sides have the same order, no loss of a power. `STLocalEntry` at `x = y`: `‖G_xx - m‖² ≺ Bctl ≈ (Nη_{t₁})⁻¹`, i.e. the local-law scale `(Nη)^{-1/2}` of `GUEPathBounds.localLaw` (`Grid.lean:97`).

### Verdicts
* **Target 1** (`RandomLayer_lem28`, `_rows`, `_rowsLL`, `_rowsQ`, `_eta*`): **PASS** (rows S1–S7; statements as the translation above; `rowsQ` reduced to `hell1`; `etaQ_*` conditional or dropped).
* **Target 2** (`g1Rowk_of_inputs`): **PASS** (hypotheses T1–T6 of (iii); kind-generic, not band-only).
* **Target 3** (`g1Row`, `g1Rowk_band`): **PASS** (T2–T4 discharged at the band by merged `gueK_exists`, `gueGrid_pathBounds` with the new `hell1`, `oull_of_pathBounds`, `Eq729B_eq747_of_inputs`, `Eq729B_goodFlow_aux`, `Eq729B_bridge`; `UNMLOut` stays the hypothesis `ML`).

## (a′) Preflight corrections — Sat Oct 10 02:56:34 UTC 2026
Section (a) is not edited; no verdict changes (all PASS). Differences between (a) and the built files:
1. (a)(iii) lists T1–T6; `g1Rowk_of_inputs` has one more input, T1′ `RandomLayerB_Dom`: a bulk energy with `Im z ∈ [N^{-1+ε}, 1]` lies in `𝐃_{κ,ε}` (`STFlow` carries `locDomain`; the kind's bulk is abstract). T2 is stated at `n₀ = 3` for both scales ((a) leaves `n₀` open).
2. (a)(i) S4–S5 ("inside `Eq729B_derived`"): `Eq729B_derived` is stated for `lemE`/`lemT` (`Eq729B_FlowData`) and the generic theorem needs the rows at abstract `fE`/`fT`; the QUE rows are `RandomLayer_rowsQ` (`r1..r4`, through the merged `Eq729B_claimA`, `Eq729B_h730_hscale_real`) with `RandomLayer_rows_flow`. `Eq729B_goodFlow`, `Eq729B_bridge` are not used: the modification of `z_n` at finitely many `n` is done generically in `RandomLayerB_eq747_seq`.
3. (a)(i) S3′: `RandomLayer_rowsLL` r4 uses `2τ_U ≤ 𝔠` (a cruder route than (a)'s `τ_U < d𝔠/2`), r3 uses `τ_U < 𝔠𝔡`; `RandomLayer_rowsQ` r4 uses `τ_U ≤ 𝔠`, r3 `τ_U ≤ 𝔠𝔡/12` (B8); all follow from `τ_U ≤ ouTauMax 𝔠 𝔡`.
4. (Repair, Sat Oct 10 04:01:27 UTC 2026; audit round 1 §4.) (a)(iii) ("PASS (not band-only)", "BA-C5's target list") and the Target 2 verdict line describe T1–T6 as kind-generic; at `d11d0a4` they were not: T5 `MLout` concluded the band `STLK`, `STLocalEntry`, `STExp2` along `STFlow`, T2 `Prod` took `STLK`, `STLocalEntry` as inputs, `RandomLayerB_KFam` (`STKloop`, `primRhsGUE`, `kTwoGUE`, `mSigma`, `sz.lam`) was fixed, T1′ `Dom` concluded `sz.locDomain`. At `f2adfa5` these are the parameters `Fl` (T1′, T5), `MO` (T5, T2, T4), `KF` (T2, T4) of `g1Rowk_of_inputs`, besides `fE`, `fT`, `PB` (B3). Still band-vocabulary: T1 uses the semicircle `etaT E t = (1-t) Im mE(E)` (`Loop/GLoop.lean:75`) and `|fE| ≤ 2 - κ`, and T2 receives `h730`, `hscale` in terms of the same `etaT` (`gueScale`, `GUEPhase/Grid.lean:84`). The preflight verdict PASS stands (U1: a band-only piece is not a FAIL); `g1Rowk_band`, `g1Row` are unchanged.

## (b) Script output — Sat Oct 10 02:56:34 UTC 2026 (stage 1b; outputs of the commands shown, run on commit d11d0a4 of branch t/T2363)
**B1 build, hygiene, size** (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2363`, branch `t/T2363`, commit `d11d0a4`; B1-B8 are outputs of the commands shown, run on this commit)
```
$ git log --format="%h" main..t/T2363 | paste -sd" " -; git status --short | wc -l | tr -d " "
d11d0a4 4955b29 8f2d543 / 0
$ lake build RBM3D.Universality.GUEPhase.RandomLayerA RBM3D.Universality.GUEPhase.RandomLayerB 2>&1 | grep "RandomLayer\|Build completed\|error"; for f in A B: lake env lean <file>   # no output = no warning
Build completed successfully (3837 jobs).
lake env lean A: exit=0
lake env lean B: exit=0
$ lake build 2>&1 | tail -1   # full library; RBM3D.lean does not import the modules yet (the hub adds the imports at merge)
Build completed successfully (4177 jobs).
$ grep -cE "sorry|admit|native_decide|^ *axiom " <A> <B>; wc -l <A> <B>   # A and B
0 0; 582 460
$ stop rule (ticket: stop line 1300, cut A|B at 750): wc -l of each file at each of its commits (git show <hash>:<file> | wc -l)
RandomLayerA.lean: 8f2d543 554; 4955b29 577; d11d0a4 582; 
RandomLayerB.lean: 4955b29 455; d11d0a4 460; 
$ git diff --stat main...t/T2363 | cat; git diff main...t/T2363 -- RBM3D/Test/Axioms.lean | grep "^[+-] " | cut -c1-96
 RBM3D/Test/Axioms.lean                        |   4 +-
 RBM3D/Universality/GUEPhase/RandomLayerA.lean | 582 ++++++++++++++++++++++++++
 RBM3D/Universality/GUEPhase/RandomLayerB.lean | 460 ++++++++++++++++++++
 3 files changed, 1044 insertions(+), 2 deletions(-)
-   `RBM.Univ.UNOULLk, -- (T2282, UN-51g: owed; owner UN-51 `RandomLayerB` `g1Rowk`; hypothesis 
-   `RBM.Univ.UNG1Rowk, -- (T2282, UN-51g: owed; owner UN-51 `RandomLayerA/B`; with `UNG2bRowk` 
+   `RBM.Univ.UNOULLk, -- (T2282, UN-51g: owed; owner band: UN-51 (`g1Rowk_band`); BA: BA-C5 (T 
+   `RBM.Univ.UNG1Rowk, -- (T2282, UN-51g: owed; owner band: UN-51 (`g1Rowk_band`); BA: BA-C5 (T
```

**B2 axioms** (re-run at `f2adfa5`, repair: `#print axioms` of the 40 public named declarations of the two files, listed by `decls.py`, scratch `ax2.lean`)
```
$ python3 decls.py <A> <B> > decls.txt; wc -l < decls.txt; (echo "import RBM3D.Universality.GUEPhase.RandomLayerB"; sed "s/^/#print axioms /" decls.txt) > ax2.lean; lake env lean ax2.lean > ax2.out 2>&1; echo exit=$?; sed -E "s/.*depends on axioms: //" ax2.out | sort | uniq -c
      40
exit=0
  40 [propext, Classical.choice, Quot.sound]
```

**B3 target statements** (`[B:n]` entries re-extracted at `f2adfa5` by `stmt.py`, repair; the three `inst_` lines of that run are in B4; `[A:n]` unchanged) (from the files by `stmt2.py`: keyword line to the first `:=`, whitespace collapsed; `[A:n]`, `[B:n]` = file and line; `variable {d : ℕ}`) **and the inputs of target 2** (`def3.py`: T1 `Flow`, T1′ `Dom`, T6 `Bulk`, T5 `MLout`, T2 `Prod`, T3 `LL`, T4 `Que`, loop family `KFam`)
```
[A:59] theorem RandomLayer_lem28 {κ e η : ℝ} (hκ : 0 < κ) (he : |e| ≤ 2 - κ) (hη0 : 0 < η) (hη1 : η ≤ 1) {z : ℂ} (hz : z = (e : ℂ) + (η : ℂ) * Complex.I) : 0 < z.im ∧ |lemE z| ≤ 2 - κ ∧ 1 / 16 ≤ lemT z ∧ lemT z < 1 ∧ etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η ∧ η / 4 ≤ etaT (lemE z) (lemT z) ∧ etaT (lemE z) (lemT z) ≤ η ∧ 1
  - lemT z ≤ η / (Real.sqrt (κ * (4 - κ)) / 8)
[A:151] theorem RandomLayer_rows (sz : Sizes d) {κ τD : ℝ} (hκ : 0 < κ) {e η t : ℕ → ℝ} (z : ℕ → ℂ) (hz : ∀ n, z n = (e n : ℂ) + (η n : ℂ) * Complex.I) (he : ∀ n, |e n| ≤ 2 - κ) (hη0 : ∀ n, 0 < η n) (hη1 : ∀ n, η n ≤ 1) (ht : ∀ n, 0 ≤ t n) (r1 : ∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-τD) * (η n / 4)) (r2 : ∀ᶠ n in atTop, 4 * (Nsz sz
  n * η n)⁻¹ ≤ Nsz sz n ^ (-τD)) (r3 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / (Real.sqrt (κ * (4 - κ)) / 8) + t n) ≤ sz.lam n ^ 2) (r4 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / (Real.sqrt (κ * (4 - κ)) / 8) + t n) ≤ 1) : (∀ n, |lemE (z n)| ≤ 2 - κ) ∧ (∀ n, 0 ≤ (1 - ouZeta (t n)) * lemT (z n)) ∧ (∀ n, (1 - ouZeta
  (t n)) * lemT (z n) ≤ lemT (z n)) ∧ (∀ n, lemT (z n) < 1) ∧ (∀ᶠ n in atTop, lemT (z n) - (1 - ouZeta (t n)) * lemT (z n) ≤ Nsz sz n ^ (-τD) * etaT (lemE (z n)) (lemT (z n))) ∧ (∀ᶠ n in atTop, (gueScale sz (fun n => lemE (z n)) n (lemT (z n)))⁻¹ ≤ Nsz sz n ^ (-τD)) ∧ (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t
  n)) * lemT (z n)) ≤ sz.lam n ^ 2) ∧ (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * lemT (z n)) ≤ 1)
[A:213] theorem RandomLayer_rowsLL (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 τU c : ℝ} (hA : sz.Admissible 𝔠 𝔡) (hτU : 0 < τU) (hτUc : τU ≤ ouTauMax 𝔠 𝔡) (hc : 0 < c) {t : ℕ → ℝ} (ht : ∀ n, t n ≤ ouTStar sz τU n) : (∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-(τU / 2)) * (ouEtaLL sz τU n / 4)) ∧ (∀ᶠ n in atTop, 4 * (Nsz sz n * ouEtaLL sz τU n)⁻¹ ≤
  Nsz sz n ^ (-(τU / 2))) ∧ (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaLL sz τU n / c + t n) ≤ sz.lam n ^ 2) ∧ (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaLL sz τU n / c + t n) ≤ 1)
[A:335] theorem RandomLayer_rowsQ (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 τU c : ℝ} (hA : sz.Admissible 𝔠 𝔡) (hτU : 0 < τU) (hτUc : τU ≤ ouTauMax 𝔠 𝔡) (hc : 0 < c) {t : ℕ → ℝ} (ht : ∀ n, t n ≤ ouTStar sz τU n) : (∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-τU) * (ouEtaQ sz 𝔡 n / 4)) ∧ (∀ᶠ n in atTop, 4 * (Nsz sz n * ouEtaQ sz 𝔡 n)⁻¹ ≤ Nsz sz n ^
  (-τU)) ∧ (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c + t n) ≤ sz.lam n ^ 2) ∧ (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c + t n) ≤ 1)
[A:478] theorem RandomLayer_etaLL_pos (sz : Sizes d) (τU : ℝ) (n : ℕ) : 0 < ouEtaLL sz τU n
[A:482] theorem RandomLayer_etaLL_le_one (sz : Sizes d) {τU : ℝ} (hτU : τU ≤ 1 / 2) (n : ℕ) : ouEtaLL sz τU n ≤ 1
[A:487] theorem RandomLayer_etaQ_pos (sz : Sizes d) (𝔡 : ℝ) {n : ℕ} (hlam : 0 < sz.lam n) : 0 < ouEtaQ sz 𝔡 n
[A:496] theorem RandomLayer_etaQ_le_one (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) : ∀ᶠ n in atTop, ouEtaQ sz 𝔡 n ≤ 1
[B:316] theorem g1Rowk_of_inputs (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) {ML Loc Que : Prop} (fE fT : ∀ d : ℕ, ∀ _ : Sizes d, ℕ → ℂ → ℝ) (Fl : ∀ d : ℕ, ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) (MO : ∀ d : ℕ, ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop) (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀
  n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) (hT1 : ∀ d, 3 ≤ d → RandomLayerB_Flow (K d) (fE d) (fT d)) (hT1' : ∀ d, 3 ≤ d → RandomLayerB_Dom (K d) (Fl d)) (hT6 : ∀ d, 3 ≤ d → RandomLayerB_Bulk (K d)) (hT2 : ∀ d, 3 ≤ d → RandomLayerB_Prod (fE d) (fT d) (MO d) (KF d) (PB d)) (hT3 : ∀ d, 3 ≤ d → RandomLayerB_LL (K d) (fE d) (fT
  d) (PB d)) (hT4 : ∀ d, 3 ≤ d → RandomLayerB_Que (K d) (P d) (fE d) (fT d) (MO d) (KF d) (PB d)) (hT5 : ML → ∀ d, 3 ≤ d → RandomLayerB_MLout (fT d) (Fl d) (MO d)) : UNG1Rowk K P ML Loc Que
[B:111] def RandomLayerB_Dom (K : UNKind d) (Fl : ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) : Prop := ∀ (𝔠 𝔡 κ ε : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < ε → ∀ E η : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → (∀ n, Nsz sz n ^ (-1 + ε) ≤ η n) → (∀ n, η n ≤ 1) → Fl sz κ ε 𝔠 𝔡 (fun n => (E n : ℂ) + (η n : ℂ) * Complex.I)
[B:123] def RandomLayerB_MLout (fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ) (Fl : ∀ _ : Sizes d, ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop) : Prop := ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), Fl sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ fT sz n (z n)) → MO sz z t
[B:132] def RandomLayerB_Prod (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ) (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop) (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop := ∀ (𝔠 𝔡 κ τD : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < τD → ∀ (z : ℕ → ℂ) (t1 : ℕ → ℝ), (∀ n,
  |fE sz n (z n)| ≤ 2 - κ) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ fT sz n (z n)) → (∀ n, fT sz n (z n) < 1) → (∀ᶠ n in atTop, fT sz n (z n) - t1 n ≤ Nsz sz n ^ (-τD) * etaT (fE sz n (z n)) (fT sz n (z n))) → (∀ᶠ n in atTop, (gueScale sz (fun n => fE sz n (z n)) n (fT sz n (z n)))⁻¹ ≤ Nsz sz n ^ (-τD)) → (∀ᶠ n in atTop, ((sz.L n : ℕ) :
  ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) → (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1) → MO sz z t1 → ∃ Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ, KF sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt ∧ PB sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt
[B:166] def RandomLayerB_Que (K : UNKind d) (P : UNOUProfile K) (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ) (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop) (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop := ∀ (𝔠 𝔡 κ τU : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < τU → τU
  ≤ ouTauMax 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ z : ℕ → ℂ, (∀ᶠ n in atTop, z n = (E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) → (∀ n, |fE sz n (z n)| ≤ 2 - κ ∧ 0 ≤ (1 - ouZeta (t n)) * fT sz n (z n) ∧ (1 - ouZeta (t n)) * fT sz n (z n) ≤ fT sz n (z n) ∧ fT sz n (z
  n) < 1) → ∀ Kt, KF sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => fT sz n (z n)) Kt → MO sz z (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) → PB sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => fT sz n (z n)) Kt → ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
  RandomLayerB_QueAt K P sz 𝔡 n (E n) (t n) τ
[B:367] def RandomLayerB_Flband (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop := STFlow sz κ ε 𝔠 𝔡 z
[B:371] def RandomLayerB_MOband (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) : Prop := sz.STLK (fun n => lemE (z n)) t ∧ sz.STLocalEntry (fun n => lemE (z n)) t ∧ sz.STExp2 (fun n => lemE (z n)) t
[B:454] theorem g1Rowk_band : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand
[B:468] theorem g1Row : UNG1Row
[B:63] def RandomLayerB_KFam (sz : Sizes d) (E' t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop := (∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E' n) (t1 n) σ a) ∧ (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
  I.length ≤ 4 * 3 → HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) ∧ (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)), Kt n s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E' n)) (t1 n) s σ₁ σ₂ a b)
[B:103] def RandomLayerB_Flow (K : UNKind d) (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ) : Prop := ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∀ (sz : Sizes d) (n : ℕ) (z : ℂ), K.bulk sz κ z.re n → 0 < z.im → z.im ≤ 1 → |fE sz n z| ≤ 2 - κ ∧ 1 / 16 ≤ fT sz n z ∧ fT sz n z < 1 ∧ etaT (fE sz n z) (fT sz n z) = Real.sqrt (fT sz n z) * z.im ∧ 1 - fT
  sz n z ≤ z.im / c
[B:117] def RandomLayerB_Bulk (K : UNKind d) : Prop := ∀ (sz : Sizes d) (κ : ℝ), (∀ n, ∃ e, K.bulk sz κ e n) ∨ ∀ n e, ¬ K.bulk sz κ e n
[B:151] def RandomLayerB_LL (K : UNKind d) (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ) (PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop := ∀ (𝔠 𝔡 κ τU : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < τU → τU < 1 / 2 → ∀ E t : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → (∀ n, 0 ≤ t n) →
  ∀ Kt, PB sz (fun n => fE sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) (fun n => (1 - ouZeta (t n)) * fT sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) (fun n => fT sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) Kt → ∀ δ : ℝ, 0 < δ → ∀ p : ℕ, ∀ᶠ n in atTop, RandomLayerB_LLAt K sz τU n (E
  n) (t n) δ p
```

**B4 compiled nonempty instances** (`d = 3`, `sz0 = SizesInst.sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `sz0.Admissible (1/6) (1/10)`, `κ = 1/10`, `τ_U = ouTauMax (1/6) (1/10) = 1/720` (`tau_eq`), `t_n = ouTStar sz0 τ_U n = N^{-1+τ_U} > 0`; every deterministic hypothesis discharged; `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (other gates) stay hypotheses of `inst_g1Row`, `inst_g1Rowk`, `inst_g1Rowk_of_inputs`)
```
$ grep -n "theorem inst_\|^example" <A> <B> | sed "s/theorem //" | cut -c1-34 | paste -sd";" -   (re-run at f2adfa5)
A.lean:528:inst_lem28 : ∃ z : ℂ, z;A.lean:537:inst_rowsLL :;A.lean:549:inst_rowsQ :;A.lean:562:example :=;A.lean:570:inst_etaLL : 0 < ouEtaL;A.lean:574:inst_etaQ : 0 < ouEtaQ ;B.lean:483:inst_g1Row (hML : ∀ d :;B.lean:489:inst_g1Rowk (hML : ∀ d ;B.lean:497:inst_g1Rowk_of_inputs (
$ sed -n "562,567p" RandomLayerA.lean   # RandomLayer_rows at the flow data of RandomLayer_lem28, z_n = i η_LL, E = 0
example :=
  RandomLayer_rows sz0 (κ := 1 / 10) (τD := ouTauMax (1 / 6) (1 / 10) / 2) (e := fun _ => 0)
    (η := ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10))) (t := ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)))
    (by norm_num) zLL (fun n => rfl) (fun n => by norm_num) (RandomLayer_etaLL_pos sz0 _)
    (RandomLayer_etaLL_le_one sz0 (by rw [tau_eq]; norm_num)) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    inst_rowsLL.1 inst_rowsLL.2.1 inst_rowsLL.2.2.1 inst_rowsLL.2.2.2
$ python3 stmt.py <B> inst_g1Row inst_g1Rowk inst_g1Rowk_of_inputs   # at f2adfa5; inst_g1Rowk_of_inputs applies g1Rowk_of_inputs at the explicit band data (fE = lemE, fT = lemT, Fl, MO, KF, PB of the band, T1-T6 by the RandomLayerB_*_band lemmas)
[B:483] theorem inst_g1Row (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) : UNOULL sz0 (ouTauMax (1 / 6) (1 / 10)) ∧ UNOUEq747 sz0 (1 / 10) (ouTauMax (1 / 6) (1 / 10))
[B:489] theorem inst_g1Rowk (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) : UNOULLk (UNKind.band 3) sz0 (ouTauMax (1 / 6) (1 / 10)) ∧ UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (ouTauMax (1 / 6) (1 / 10))
[B:497] theorem inst_g1Rowk_of_inputs (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) : UNOULLk (UNKind.band 3) sz0 (ouTauMax (1 / 6) (1 / 10)) ∧ UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (ouTauMax (1 / 6) (1 / 10))
```

**B5 translation table RBM2D -> RBM3D** (port of RBM2D `RandomLayerA.lean` (521 lines) and `RandomLayerB.lean` (152 lines); `table.py` prints source line and target line; the auditor reads each row against the files)
```
RandomLayer_lem28  RandomLayerA:83  ->  RandomLayer_lem28@59  [k -> kappa; margin kappa kept; 'eta/4 <= 1-t0' dropped (served r5); new: etaT = sqrt(t0)*eta, 1-t0 <= eta/c_kappa, c_kappa = sqrt(kappa(4-kappa))/8]
RandomLayer_rows  RandomLayerA:139  ->  RandomLayer_rows@151  [8 conclusions -> 8 (|lemE|<=2-k, 0<=t1, t1<=t0, t0<1, h730, hscale, hell = L^d(1-t1)<=lam^2) + new hell1; range conclusion and r5 dropped; r3: L^d(eta/c_k+t)<=lam^2; new r4: <=1; abstract form RandomLayer_rows_flow]
RandomLayer_rowsLL  RandomLayerA:339  ->  RandomLayer_rowsLL@213  [r1,r2,r3,r5 -> r1,r2,r3,r4 at eta_LL, tau_D = tU/2; r3 needs tU < c*dd, r4 needs 2*tU <= c, 3 <= d]
RandomLayer_rowsQ  RandomLayerA:414  ->  RandomLayer_rowsQ@335  [r1,r2,r3,r5 at W^{2/3}/N -> r1..r4 at eta_Q = W^{-dd/3} lam W^{d/2}/N, tau_D = tU; needs tU <= c*dd/12 (claimA, r3), tU <= c (r4), 3 <= d]
RandomLayer_etaLL_pos  RandomLayerA:256  ->  RandomLayer_etaLL_pos@478  [d.size -> Nsz sz n]
RandomLayer_etaLL_le_one  RandomLayerA:260  ->  RandomLayer_etaLL_le_one@482  [same, tU <= 1/2]
RandomLayer_etaQ_pos  RandomLayerA:264  ->  RandomLayer_etaQ_pos@487  [eta_Q carries lam: hypothesis 0 < lam n]
RandomLayer_etaQ_le_one  RandomLayerA:271  ->  RandomLayer_etaQ_le_one@496  [eventually (queDomain at E = 0, kappa = 2), Admissible]
RandomLayer_L_sq_le  RandomLayerA:233  ->  RandomLayer_Ld_mul_rpow@177  [L^2 <= N^{1-2c} -> L^d N^{-1+a} = N^a/W^d (private)]
RandomLayer_rpow_mul_eq  RandomLayerA:211  ->  RandomLayer_rpow_mul_eq@197  [private, unchanged]
RandomLayerB_oull_seq  RandomLayerB:58  ->  RandomLayerB_oull_seq@191  [P7Out -> hT5 (STLK, STLocalEntry); kind-generic; n0 = 3 (source 2); rows from rowsLL + rows_flow]
RandomLayerB_eq747_seq  RandomLayerB:96  ->  RandomLayerB_eq747_seq@226  [P7Out, P7ExpOut -> hT5 (+ STExp2); z_n modified at finitely many n (STFlow at every n); n0 = 3]
g1Row  RandomLayerB:142  ->  g1Row@430  [G1Row -> UNG1Row (UNMLOut only; Loc, Que unused) = UNG1Rowk_band.1 of g1Rowk_band; + kind-generic g1Rowk_of_inputs]
RandomLayer_lemT_pos ... (56,66,215,221,201,207,228)  ->  merged/inline: lemT_pos, zt_im_lemma28, Nsz_pos, Sizes.one_le_size, hsz.eventually, tendsto_rpow_atTop, Nsz = W^d L^d
RandomLayer_size_mul_etaQ ... (288,295,305,319)  ->  merged: Eq729B_claimA, Sizes.size_rpow_le_W_rpow, Eq729B_h730_hscale_real, Eq729B_Ld_mul_etaQ (eta_Q = W^{2/3}/N -> W^{-dd/3} lam W^{d/2}/N)
```

**B6 registry pre-check** (scratch `reg.lean` = `import RBM3D` + `import ...RandomLayerA` + `import ...RandomLayerB` + `#assert_rbm_axioms`; `reg_base.lean` = the same without the two imports; neither is committed)
```
$ lake env lean reg.lean > reg.out 2>&1; echo "exit=$?"; head -1 reg.out; grep -c error reg.out; lake env lean reg_base.lean > reg_base.out 2>&1; echo "exit=$?"; head -1 reg_base.out
exit=0
axiom audit: 10753 theorems, 3159 definitions, 0 axioms in `RBM` (compiler-generated decla
0
exit=0
axiom audit: 10727 theorems, 3148 definitions, 0 axioms in `RBM` (compiler-generated decla
$ ledger counts (theorems resting on each premise), reg_base.out -> reg.out
UNOULLk 6->7; UNG1Rowk 7->9; UNMLOut 29->33; UNLocAvgBand 42->45; UNQueBand 22->25; 
$ for f in reg_base reg; do grep -o "premises found by scanning: [0-9]* (borrowed [0-9]*, owed [0-9]*\|[0-9]* registered premise(s) carry nothing yet" $f.out | paste -sd";" -; done; diff <(carry-nothing list of reg_base.out) <(same of reg.out) | grep "^>"
premises found by scanning: 133 (borrowed 1, owed 71;124 registered premise(s) carry nothing yet
premises found by scanning: 132 (borrowed 1, owed 70;125 registered premise(s) carry nothing yet
> RBM.Univ.UNG1Rowk
```

**B7 name clash and port citation**
```
$ git rev-parse --short main; git merge-base main t/T2363 | cut -c1-7
c06b2d7 010cad9
$ for n in <37 new public names + RandomLayerInst RandomLayerBInst>; do git grep -nwE "(theorem|def|lemma|abbrev|structure|namespace) +([A-Za-z0-9_.]*\.)?$n" main -- RBM3D RBM3D.lean; done | wc -l
0
$ for n in <same>; do git grep -nw $n main -- RBM3D RBM3D.lean; done | cut -c1-120   # any mention on main
main:RBM3D/Universality/ZeroModeProfile.lean:125:/-- **Row `UNG1Row`** (UN-51, `RandomLayerB` `g1Row`): the two layer pi
main:RBM3D/Universality/Pins.lean:430:`(E', t) ↔ (z, t ≤ lemT z)` is `RBM2D/Universality/GUEPhase/RandomLayerA.lean`, `R
$ cd /Users/junyin/Lean_proof/RBM3D; git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/RandomLayer{A,B}.lean | wc -l; wc -l ../RBM2D/RBM2D/Universality/GUEPhase/RandomLayer{A,B}.lean
9e0f275
0
 521 RandomLayerA.lean; 152 RandomLayerB.lean; 673 total
```

**B8 the `τ_U` table (U3)**: the constraints on `τ_U` used by the rows of `RandomLayerA.lean`; `ouTauMax_slack` (`ZeroModeProfile.lean:536`) gives them from `τ_U ≤ ouTauMax 𝔠 𝔡`
```
$ grep -n "ouTauMax_slack\|hτ12 :\|hτc𝔡\|h12c\|h12𝔡" RandomLayerA.lean | cut -c1-100; sed -n "537p" ZeroModeProfile.lean
221:  obtain ⟨h12c, -, hτc𝔡, -⟩ := ouTauMax_slack h𝔠 h𝔡 hτUc
314:    (hτU : 0 ≤ τU) (hτ12 : τU ≤ 𝔠 * 𝔡 / 12) (hNW : Nsz sz n ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
343:  obtain ⟨h12c, h12𝔡, -, -⟩ := ouTauMax_slack h𝔠 h𝔡 hτUc
344:  have hτ12 : τU ≤ 𝔠 * 𝔡 / 12 := by linarith
    12 * τU ≤ 𝔠 ∧ 12 * τU ≤ 𝔠 * 𝔡 ∧ τU < 𝔠 * 𝔡 ∧ 3 * τU / 2 < 2 * (𝔠 * 𝔡) / 3 := by
```

**Narrative** (every number is in B1–B8 or in the files)
1. Delivered: `RandomLayerA.lean` (582 lines) and `RandomLayerB.lean` (460 lines), commits `8f2d543 4955b29 d11d0a4`; 1042 lines against the stop line 1300, A below the cut 750 at each commit (B1). Both modules and the full library build, `lake env lean` prints nothing, the 37 public declarations use only the three standard axioms (B2), the registry pre-check exits 0 (B6), `git diff main...t/T2363` is the two new files and the two comment lines of `Test/Axioms.lean` (B1), no name clash (B7). The 37 are the 11 targets, `RandomLayer_rows_flow`, 11 definitions, 7 band-discharge lemmas and 7 instances.
2. Target 1 (A): `RandomLayer_lem28` adds `η_{t₀} = √t₀ η` and `1 - t₀ ≤ η/c_κ`, `c_κ = √(κ(4-κ))/8`; `RandomLayer_rows_flow` assembles `r1..r4` at any scale with abstract flow data (Lemma 2.8 facts as hypotheses), `RandomLayer_rows` is its form with `z_n = e_n + iη_n`, `lemE`, `lemT` (the source's shape); `RandomLayer_rowsLL` (`η_LL`, `τ_D = τ_U/2`) and `RandomLayer_rowsQ` (`η_Q`, `τ_D = τ_U`) prove `r1..r4`; the four `eta` lemmas (B5, B3).
3. U3 (B8): the rows use `τ_U < 𝔠𝔡` and `2τ_U ≤ 𝔠` (LL), `τ_U ≤ 𝔠𝔡/12` (claimA) and `τ_U ≤ 𝔠` (QUE), all given by `ouTauMax_slack`; no row needs `τ_U < ouTauMax`: no pin change (`ouTauMax'`, `UNG1Row'`), no REQ.
4. Target 2 (U1; repaired at `f2adfa5`, audit round 1 §4): `g1Rowk_of_inputs` takes the kind's vocabulary as parameters — flow maps `fE`, `fT`, flow domain `Fl`, `G`-loop outputs `MO`, primitive family `KF`, path bounds `PB` — and seven `Prop` inputs of the file (B3): T1 `Flow` (Lemma 2.8 facts of `fE`, `fT`), T1′ `Dom` (bulk energy, `Im z ∈ [N^{-1+ε}, 1]` ⇒ `Fl`), T6 `Bulk`, T5 `MLout` (`ML` ⇒ `MO sz z t` along `Fl`), T2 `Prod` (rows and `MO` ⇒ `∃ Kt, KF ∧ PB`), T3 `LL`, T4 `Que` (`KF`, `MO`, `PB` ⇒ body of `UNOUEq747k`). Still fixed in the inputs: the semicircle `etaT` in T1 and in the rows handed to T2, and `|fE| ≤ 2 - κ` ((a′) 4). Proved generically: the rows at both scales, the flow selection (`z_n = E_n + iη'_n` with `η'_n = η_Q` where `η_Q ∈ [N^{-1+ε}, 1]`, else `N^{-1+ε}`, `ε = min(𝔠(𝔡 - 𝔡/3), 1)`; equal to `η_Q` eventually), `Fl` and `MO` along it, the padding of an arbitrary energy sequence to a bulk sequence (T6), the quantifiers.
5. Target 3: `g1Rowk_band` is `g1Rowk_of_inputs` at `UNKind.band`, `UNOUProfile.band`, `fE = lemE`, `fT = lemT`, `PB = GUEPathBounds (gueGridK sz 3) 3`; T1 by `RandomLayer_lem28`, T1′ and T6 directly (`κ ≤ 2` or `κ > 2`), T2 by `gueK_exists`, `Sizes.stKbound_holds`, `gueGrid_pathBounds`, T3 by `oull_of_pathBounds`, T4 by `Eq729B_eq747_of_inputs`, T5 by `UNMLOut`: the lines 329–414 of `RandomLayerB.lean` (seven public lemmas `RandomLayerB_*_band`, public so that the registry scan counts the inputs as proved). `g1Row := UNG1Rowk_band.1 g1Rowk_band`; `UNLocAvgBand`, `UNQueBand` are unused.
6. For BA-C5 (repaired at `f2adfa5`): a BA twin chooses `fE`, `fT`, `Fl`, `MO`, `KF`, `PB` at `UNKind.ba` and proves the seven inputs there; T1 must hold in the semicircle `etaT` form ((a′) 4). The band choices are `RandomLayerB_Flband` (`Fl = STFlow`), `RandomLayerB_MOband` (`STLK ∧ STLocalEntry ∧ STExp2` at `lemE ∘ z`), `RandomLayerB_KFam`, `RandomLayerB_PBband`, discharged by the seven `RandomLayerB_*_band` lemmas (`RandomLayerB.lean:343-451` at `f2adfa5`).
7. Deviations from the ticket text: `Eq729B_goodFlow`, `Eq729B_bridge` are not used ((a′) 2); `n₀ = 3` at both scales (source: 2 at LL); `RandomLayer_rows` has the source's form and an abstract twin.
8. Registry (B6): the two owner comments are edited (comment text only); the scan then counts `UNG1Rowk` as proved at the band (it leaves "found by scanning" and enters "registered, carries nothing yet"); the ledgers of `UNOULLk`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand` grow by the theorems that assume them. Not done: `UNG1Rowk` at `UNKind.ba` (BA-C5 inputs, BA-N2 instance).

## (c) Verified Mathlib names (all elaborate; `#check` output, signatures abbreviated)
```
$ grep -ohE "\b(Real|Complex|Filter|Nat|Set)\.[A-Za-z_₀0-9']+" <A> <B> | sort -u, plus root names by hand (42 in all) > mn2.txt; (echo "import ...RandomLayerA"; echo "open Filter"; sed "s/^/#check @/" mn2.txt) > mn.lean; lake env lean mn.lean > mn.out 2>&1; echo exit=$?
exit=0  names=42  errors=0
@Real.le_sqrt : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → (x ≤ √y ↔ x ^ 2 ≤ y)
@Real.rpow_add_one : ∀ {x : ℝ}, x ≠ 0 → ∀ (y : ℝ), x ^ (y + 1) = x ^ y * x
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.sqrt_le_one : ∀ {x : ℝ}, √x ≤ 1 ↔ x ≤ 1
@tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Tendsto (fun x => x ^ y) atTop atTop
```
Names verified absent: none needed (no name was invented; all used names elaborate).

## (d) Open issues and paper-delta candidates
Paper-delta candidates (Lean/paper or Lean/RBM2D statement differences):
* `T2363a`: the row `hell1 : L^d(1-t₁) ≤ 1` is proved at both scales (`r4` of `RandomLayer_rowsLL`, `RandomLayer_rowsQ`); it is not in the paper (`(eq:WO)` gives only `lam ≤ 𝔡⁻¹`, so `hell` does not imply it); extends T2361b.
* `T2363b`: `g1Rowk_of_inputs` is generic in the kind's vocabulary `fE`, `fT`, `Fl`, `MO`, `KF`, `PB` with seven inputs (B3); T1 and the rows handed to T2 keep the semicircle `etaT E t = (1-t) Im mE(E)` (`Loop/GLoop.lean:75`) and `|fE| ≤ 2 - κ`, i.e. they are band-vocabulary ((a′) 4). At the band there is one statement, `g1Row`. No paper statement corresponds to T1–T6; they are interfaces for BA-C5.
* `T2363c`: `STFlow` needs `locDomain` at every `n` and `η_Q ≤ 1` holds eventually, so the flow `z_n = E_n + iη_Q` is modified at finitely many `n` (narrative 4); `≺` is unaffected (as T2356).
* `T2363d`: `UNG1Rowk`'s `Loc`, `Que` are unused (the source's `G1Row` had only `P7Out`, `P7ExpOut`); of the five conclusions of `UNMLOut` only `STLK`, `STLocalEntry`, `STExp2` are consumed.
* `T2363e`: not ported from RBM2D: the energy margin `κ/2`, the range exponent `τ = 𝔠/3`, the hypothesis `r5`; the QUE scale is `η_Q = W^{-𝔡/3} lam W^{d/2}/N` (RBM2D `W^{2/3}/N`); `n₀ = 3` at the LL scale (RBM2D 2).
Open: (1) `UNG1Rowk` at `UNKind.ba`: BA-C5 (inputs T1–T6) and BA-N2 (instance). (2) `RandomLayerB_Prod` supplies loops of length ≤ 12 only (`n₀ = 3`). (3) The registry ledgers grow (B6); no registry change is requested beyond the two comments of the ticket. (4) T1 and the rows handed to T2 use the semicircle `etaT` and `|fE| ≤ 2 - κ`; whether the BA flow (`BAflowT0`, `BAflowEs`, `BA/FlowPins.lean:537-540`) satisfies them, or `etaT` must become a parameter, is open for BA-C5.

## Repair (audit round 1, repairer model: claude-opus-5-5) — Sat Oct 10 04:01:27 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2363`, branch `t/T2363`, repair commit `f2adfa5` (only `RandomLayerB.lean` changed). B2–B4 above re-run at `f2adfa5`; B1, B5–B8 are the outputs at `d11d0a4`, superseded where they differ by:
```
$ git log --format="%h" main..t/T2363 | paste -sd" " -; git status --short | wc -l | tr -d " "; git diff --stat d11d0a4 f2adfa5 | tail -1
f2adfa5 d11d0a4 4955b29 8f2d543
0
 1 file changed, 140 insertions(+), 86 deletions(-)
$ git diff --stat main...t/T2363 | cat
 RBM3D/Test/Axioms.lean                        |   4 +-
 RBM3D/Universality/GUEPhase/RandomLayerA.lean | 582 ++++++++++++++++++++++++++
 RBM3D/Universality/GUEPhase/RandomLayerB.lean | 514 +++++++++++++++++++++++
 3 files changed, 1098 insertions(+), 2 deletions(-)
$ wc -l RandomLayerA.lean RandomLayerB.lean | paste -sd";" -   # stop line 1300
     582 RandomLayerA.lean;     514 RandomLayerB.lean;    1096 total
$ grep -nE "sorry|admit|native_decide|^ *axiom " <A> <B> | wc -l
       0
$ lake build RBM3D.Universality.GUEPhase.RandomLayerA RBM3D.Universality.GUEPhase.RandomLayerB 2>&1 | grep -E "^error|RandomLayer|Build completed|failed"; lake env lean <B>; echo exit=$?
✔ [3837/3837] Built RBM3D.Universality.GUEPhase.RandomLayerB (6.9s)
Build completed successfully (3837 jobs).
exit=0
$ lake build 2>&1 | tail -1
Build completed successfully (4177 jobs).
$ lake env lean reg.lean > reg.out 2>&1; echo "exit=$?"; head -1 reg.out | cut -c1-90; grep -c error reg.out; grep -o "<scan counts>" reg.out | paste -sd";" -   # reg.lean = import RBM3D + both modules + #assert_rbm_axioms
exit=0
axiom audit: 10754 theorems, 3161 definitions, 0 axioms in `RBM` (compiler-generated decla
0
premises found by scanning: 132 (borrowed 1, owed 70;125 registered premise(s) carry nothing yet
$ lake env lean ax.lean > ax.out 2>&1; echo exit=$?; grep -c "" ax.out; grep g1Rowk_of_inputs ax.out   # ax.lean: two pin checks, then 10 #print axioms
#   example : RBM.Univ.UNG1Row := g1Row;   example : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d, UNMLOut d) UNLocAvgBand UNQueBand := g1Rowk_band
exit=0
10
'RBM.Univ.GUEPhase.g1Rowk_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.RandomLayerBInst.inst_g1Rowk_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
$ for n in RandomLayerB_Flband RandomLayerB_MOband inst_g1Rowk_of_inputs; do git grep -nw $n main -- RBM3D RBM3D.lean; done | wc -l   # main = 9b94993
       0
```
Narrative: target 2 repaired as audit §4 item 1 (first branch): `Fl`, `MO`, `KF` are parameters of `g1Rowk_of_inputs` and of `RandomLayerB_Dom`, `RandomLayerB_MLout`, `RandomLayerB_Prod`, `RandomLayerB_Que`; the band instantiation is `RandomLayerB_Flband`, `RandomLayerB_MOband` (new public defs), `RandomLayerB_KFam`, `RandomLayerB_PBband`. `g1Rowk_band`, `g1Row` keep their statements (the two pin checks above elaborate); `inst_g1Row`, `inst_g1Rowk` kept; new compiled instance `inst_g1Rowk_of_inputs` (B4). Target 1 (`RandomLayerA.lean`) and `Test/Axioms.lean` are unchanged. Report: (a′) 4, B2–B4, narrative 4 and 6, T2363b, open issue (4).
